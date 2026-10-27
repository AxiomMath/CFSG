module

public import CFSG.Combinatorics.HexagonUniqueDuality
public import CFSG.Combinatorics.HexagonAutomorphismBound
public import CFSG.GroupTheory.PerfectSmallOvergroup
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineHexagon

public section

namespace CFSG.Wreathed.FourPointUnitaryRecognition

open CFSG.Assembly.LowTwoRank CFSG.LinearGroups.UnitaryThreeOverNine
  CFSG.Combinatorics.HexagonStabilizerFaithful

theorem colour_relation {V V' : Type*} {Δ : SimpleGraph V} {Δ' : SimpleGraph V'}
    {col : Δ.Coloring Bool} {col' : Δ'.Coloring Bool} {ε₁ ε₂ : Bool} {ψ : Δ ≃g Δ'}
    (h1 : ψ '' {v | col v = ε₁} = {v | col' v = ε₂})
    (h2 : ψ '' {v | col v = !ε₁} = {v | col' v = !ε₂}) (v : V) :
    col' (ψ v) = xor (xor (col v) ε₁) ε₂ := by
  rcases Bool.eq_false_or_eq_true (xor (col v) ε₁) with h | h
  · have hv : col v = !ε₁ := by revert h; cases col v <;> cases ε₁ <;> decide
    have : ψ v ∈ {v | col' v = !ε₂} := h2 ▸ Set.mem_image_of_mem ψ hv
    rw [this, h]
    cases ε₂ <;> rfl
  · have hv : col v = ε₁ := by revert h; cases col v <;> cases ε₁ <;> decide
    have : ψ v ∈ {v | col' v = ε₂} := h1 ▸ Set.mem_image_of_mem ψ hv
    rw [this, h]
    cases ε₂ <;> rfl

theorem incColoring_incAction {F : Type} [Field F] (hF : Nat.card F = 9) (k : StatedSU 3 3 F)
    (w : NonisoLine F ⊕ HexLine F) : incColoring F (incAction hF k w) = incColoring F w := by
  rcases w with p | T <;> rfl

theorem finite_iso {V : Type*} [Finite V] (Δ : SimpleGraph V) : Finite (Δ ≃g Δ) :=
  Finite.of_injective (fun f : Δ ≃g Δ => f.toEquiv) fun _ _ h =>
    RelIso.ext fun x => congrFun (congrArg (fun e : V ≃ V => (e : V → V)) h) x

theorem nonempty_mulEquiv_statedSU_of_hexagon_action {G : Type*} [Group G] [Finite G]
    [Group.IsPerfect G] (hG : Nat.card G = 6048) {V : Type*} [Fintype V] (Δ : SimpleGraph V)
    [DecidableRel Δ.Adj] (hcard : Fintype.card V = 126) (hconn : Δ.Connected)
    (hdeg : ∀ v, Δ.degree v = 3) (col : Δ.Coloring Bool)
    (hcyc : ∀ (v : V) (c : Δ.Walk v v), c.IsCycle → 12 ≤ c.length)
    (ρ : G →* (Δ ≃g Δ)) (hρ : Function.Injective ρ) (hρcol : ∀ g v, col (ρ g v) = col v)
    {F : Type} [Field F] (hF : Nat.card F = 9) : Nonempty (G ≃* StatedSU 3 3 F) := by
  classical
  have := finite_nonisoLine hF
  have := finite_hexLine hF
  have : Fintype (NonisoLine F ⊕ HexLine F) := Fintype.ofFinite _
  have hcardF : Fintype.card (NonisoLine F ⊕ HexLine F) = 126 := by
    rw [← Nat.card_eq_fintype_card, card_incGraph_vertices hF]
  obtain ⟨hconnF, -⟩ := hexagon_facts hF
  have hdegF : ∀ v, (incGraph F).degree v = 3 := fun v => by
    rw [degree_eq_ncard, ncard_neighborSet hF]
  have hcycF : ∀ (v : NonisoLine F ⊕ HexLine F) (c : (incGraph F).Walk v v), c.IsCycle →
      12 ≤ c.length := fun v c hc => twelve_le_length hF c hc
  obtain ⟨ε₁, ε₂, ψ, h1, h2⟩ :=
    CFSG.Combinatorics.HexagonUniqueDuality.order_two_generalized_hexagons_unique_up_to_duality
      Δ hcard hconn hdeg col hcyc (incGraph F) hcardF hconnF hdegF (incColoring F) hcycF
  have hψ := colour_relation h1 h2
  have hΩ :=
    (CFSG.Combinatorics.HexagonAutomorphismBound.order_two_generalized_hexagon_automorphism_bound
      Δ hcard hconn hdeg col hcyc).2
  have := finite_iso Δ
  let ρ' : G →* partAut Δ col := ρ.codRestrict (partAut Δ col) fun g => mem_partAut.mpr (hρcol g)
  have hρ' : Function.Injective ρ' := fun g g' h => hρ (congrArg Subtype.val h)
  let κ := incAction hF
  let σ₀ : StatedSU 3 3 F →* (Δ ≃g Δ) :=
    { toFun := fun k => (ψ.trans (κ k)).trans ψ.symm
      map_one' := RelIso.ext fun v => by
        show ψ.symm (κ 1 (ψ v)) = v
        rw [map_one, RelIso.one_apply, RelIso.symm_apply_apply]
      map_mul' := fun k k' => RelIso.ext fun v => by
        show ψ.symm (κ (k * k') (ψ v)) = ψ.symm (κ k (ψ (ψ.symm (κ k' (ψ v)))))
        rw [map_mul, RelIso.mul_apply, RelIso.apply_symm_apply] }
  have hσ₀ : ∀ k v, σ₀ k v = ψ.symm (κ k (ψ v)) := fun k v => rfl
  have hσcol : ∀ k, σ₀ k ∈ partAut Δ col := fun k => mem_partAut.mpr fun v => by
    have hu := hψ (σ₀ k v)
    rw [hσ₀, RelIso.apply_symm_apply, incColoring_incAction, hψ v] at hu
    rw [hσ₀]
    generalize col (ψ.symm (κ k (ψ v))) = b at hu ⊢
    generalize col v = b' at hu ⊢
    revert hu
    cases b <;> cases b' <;> cases ε₁ <;> cases ε₂ <;> decide
  let σ : StatedSU 3 3 F →* partAut Δ col := σ₀.codRestrict (partAut Δ col) hσcol
  have hσ : Function.Injective σ := by
    intro k k' h
    have h' : σ₀ k = σ₀ k' := congrArg Subtype.val h
    apply incAction_injective hF
    refine RelIso.ext fun w => ?_
    have := DFunLike.congr_fun h' (ψ.symm w)
    rw [hσ₀, hσ₀, RelIso.apply_symm_apply] at this
    exact ψ.symm.injective this
  have : Group.IsPerfect (StatedSU 3 3 F) := isPerfect_statedSU_three_three hF
  have : Finite (StatedSU 3 3 F) :=
    Nat.finite_of_card_ne_zero (by rw [card_statedSU hF]; norm_num)
  obtain ⟨-, -, f, -, -⟩ := perfect_equal_order_embeddings_in_small_common_overgroup 6048
    (by norm_num) hG (card_statedSU hF) ρ' σ hρ' hσ (by omega)
  exact ⟨f⟩

end CFSG.Wreathed.FourPointUnitaryRecognition
