module

public import CFSG.ClassicalInvolution.Q3.Q3TWY29
public import CFSG.ClassicalInvolution.Q3.Q3TWY30
public import CFSG.ClassicalInvolution.Q3.Q3TY35

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TWY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.Timmesfeld
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.WeakCT
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local macro "nd_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes3.DAdj, edgeD]; done)
    | (simp [DNodes3.DAdj, edgeD]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)


section Orth

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}
  {M : Subgroup G}

theorem not_scalar_five3 (c : TCtx3 .POmegaOdd (0 + 5) Ω K z) {β : Subgroup G} {t : G}
    (ht : IsClassicalMember3 β t) (htz : t * z * t⁻¹ = z) (nd : DNodes3 (0 + 5) Ω M)
    (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β)
    {Rz : ℕ → Subgroup (modelUniv .POmegaOdd (0 + 5) 3 1 Nat.prime_three).K}
    {RzM : Subgroup (modelUniv .POmegaOdd (0 + 5) 3 1 Nat.prime_three).K}
    (hch : LayerChain3 c nd Rz RzM)
    {α : spinGroup (quadOdd (0 + 5) 𝔽₃) ≃* spinGroup (quadOdd (0 + 5) 𝔽₃)}
    (hαθ : ∀ y, c.d.ψ (α y) = locAut c.hΩ.conjInvariant htz (c.d.ψ y))
    {g₀ : (Fin (0 + 5) ⊕ Fin (0 + 5) ⊕ Unit → 𝔽₃) ≃ₗ[𝔽₃]
      (Fin (0 + 5) ⊕ Fin (0 + 5) ⊕ Unit → 𝔽₃)}
    (hg₀O : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd (0 + 5) 𝔽₃))
    (hconj : ∀ y v, spinAction (quadOdd (0 + 5) 𝔽₃) (α y) (g₀ v) =
      g₀ (spinAction (quadOdd (0 + 5) 𝔽₃) y v))
    {i0 : (Fin (0 + 5) ⊕ Fin (0 + 5) ⊕ Unit → 𝔽₃) ≃ₗ[𝔽₃]
      (Fin (0 + 5) ⊕ Fin (0 + 5) ⊕ Unit → 𝔽₃)}
    (hL : IsFundamental (quadOdd (0 + 5) 𝔽₃) ((Rz 2).map (spinAction (quadOdd (0 + 5) 𝔽₃))) i0) :
    ¬ ∃ ε : 𝔽₃, ε * ε = 1 ∧ ∀ x ∈ negSpace i0, g₀ x = ε • x := by
  classical
  rintro ⟨ε, hε, hx⟩
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  have : Invertible (2 : 𝔽₃) := invertibleOfNonzero h2
  obtain ⟨F, hFL, hFi⟩ := hL
  have hxF : ∀ w ∈ F.span, g₀ w = ε • w := fun w hw =>
    hx w (by rw [hFi, negSpace_La_neg_one h2]; exact hw)
  have hcomm : ∀ r ∈ Rz 2, g₀ * spinAction (quadOdd (0 + 5) 𝔽₃) r =
      spinAction (quadOdd (0 + 5) 𝔽₃) r * g₀ := by
    intro r hr
    have hmem : spinAction (quadOdd (0 + 5) 𝔽₃) r ∈
        (Rz 2).map (spinAction (quadOdd (0 + 5) 𝔽₃)) := ⟨r, hr, rfl⟩
    rw [hFL] at hmem
    obtain ⟨A, hA⟩ := hmem
    rw [← hA]
    exact commutes_La_of_scalar F hg₀O hε hxF A
  have hfix : ∀ r ∈ Rz 2, locAut c.hΩ.conjInvariant htz (c.d.ψ r) = c.d.ψ r :=
    fixed_of_commute3 c.d.ψ α (locAut c.hΩ.conjInvariant htz) hαθ
      (spinAction (quadOdd (0 + 5) 𝔽₃)) (ker_spinAction_le_center _) c.hY.cop
      (fun y => LinearEquiv.ext fun v => hconj y v) (c.hY.pow3 _ (hch.fund 2 (by omega) (by omega)))
      hcomm
  obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj (a := ⟨2, by omega⟩) (b := ⟨1, by omega⟩) (by nd_idx)
  rw [h1] at hW₁
  have hJt : conjSub t (nd.J ⟨2, by omega⟩) = nd.J ⟨2, by omega⟩ :=
    conjSub_eq_of_standardPair h2 hW₁ ht.mem ht.orderOf_eq_two
  obtain ⟨x₁, hx₁J, hx₁1, hx₁p, hx₁inv⟩ :=
    TWS7.exists_inverted_unipotent (p := 3) h2 hW₁ ht.mem ht.orderOf_eq_two
  obtain ⟨-, x₀, hx₀J, hx₀1, hx₀p, hx₀α⟩ := unip_data_odd3 c htz
    (node_mem_z3 c nd h0 (a := 2) (by omega) (by omega)) (hch.fund 2 (by omega) (by omega))
    (hch.img 2 (by omega) (by omega)) hJt hx₁J hx₁1 hx₁p hx₁inv hαθ
  let θ : spinGroup (quadOdd (0 + 5) 𝔽₃) →* locQuot Ω z := c.d.ψ
  have hαθ' : ∀ y, θ (α y) = locAut c.hΩ.conjInvariant htz (θ y) := hαθ
  have h3 : θ x₀ = (θ x₀)⁻¹ := by
    have h4 : locAut c.hΩ.conjInvariant htz (θ x₀) = θ x₀ := hfix x₀ hx₀J
    rw [← hαθ' x₀, hx₀α, map_inv] at h4
    exact h4.symm
  have hsq : x₀ * x₀ = 1 := by
    have hker : x₀ * x₀ ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul]
      nth_rewrite 1 [h3]
      exact inv_mul_cancel _
    exact c.hY.central _ (hch.fund 2 (by omega) (by omega)) _ ((Rz 2).mul_mem hx₀J hx₀J)
      (c.d.ker_le hker)
  apply hx₀1
  calc x₀ = x₀ * (x₀ * x₀) := by rw [hsq, mul_one]
    _ = x₀ ^ 3 := (pow_three x₀).symm
    _ = 1 := hx₀p

theorem orth_bridge3 {u : ℕ} (c : TCtx3 .POmegaOdd (u + 5) Ω K z) {β : Subgroup G} {t : G}
    (ht : IsClassicalMember3 β t) (htz : t * z * t⁻¹ = z) (nd : DNodes3 (u + 5) Ω M)
    (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β)
    {Rz : ℕ → Subgroup (modelUniv .POmegaOdd (u + 5) 3 1 Nat.prime_three).K}
    {RzM : Subgroup (modelUniv .POmegaOdd (u + 5) 3 1 Nat.prime_three).K}
    (hch : LayerChain3 c nd Rz RzM)
    {α : spinGroup (quadOdd (u + 5) 𝔽₃) ≃* spinGroup (quadOdd (u + 5) 𝔽₃)}
    (hαθ : ∀ y, c.d.ψ (α y) = locAut c.hΩ.conjInvariant htz (c.d.ψ y))
    {g₀ : (Fin (u + 5) ⊕ Fin (u + 5) ⊕ Unit → 𝔽₃) ≃ₗ[𝔽₃] (Fin (u + 5) ⊕ Fin (u + 5) ⊕ Unit → 𝔽₃)}
    (hg₀O : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd (u + 5) 𝔽₃)) (hg₀2 : g₀ * g₀ = 1)
    (hconj : ∀ y v, spinAction (quadOdd (u + 5) 𝔽₃) (α y) (g₀ v) =
      g₀ (spinAction (quadOdd (u + 5) 𝔽₃) y v))
    {pr : ℕ → HypPair (quadOdd (u + 5) 𝔽₃)}
    (horth : ∀ a b, a < u + 1 + 1 → b < u + 1 + 1 → a ≠ b → (pr a).Orth (pr b))
    {i : ℕ → (Fin (u + 5) ⊕ Fin (u + 5) ⊕ Unit → 𝔽₃) ≃ₗ[𝔽₃]
      (Fin (u + 5) ⊕ Fin (u + 5) ⊕ Unit → 𝔽₃)}
    (hL : ∀ a ≤ u + 1, IsFundamental (quadOdd (u + 5) 𝔽₃)
      ((Rz (a + 2)).map (spinAction (quadOdd (u + 5) 𝔽₃))) (i a))
    (nL : ∀ a ≤ u + 1, negSpace (i a) = hypPlane (pr a) ⊔ hypPlane (pr (a + 1)))
    {S : Subgroup ((Fin (u + 5) ⊕ Fin (u + 5) ⊕ Unit → 𝔽₃) ≃ₗ[𝔽₃]
      (Fin (u + 5) ⊕ Fin (u + 5) ⊕ Unit → 𝔽₃))}
    {s' : (Fin (u + 5) ⊕ Fin (u + 5) ⊕ Unit → 𝔽₃) ≃ₗ[𝔽₃]
      (Fin (u + 5) ⊕ Fin (u + 5) ⊕ Unit → 𝔽₃)}
    (hS : IsFundamental (quadOdd (u + 5) 𝔽₃) S s')
    (hc : ∀ a < u + 1, Commutes S ((Rz (a + 2)).map (spinAction (quadOdd (u + 5) 𝔽₃))))
    (fS : ∀ l ∈ S, g₀ * l = l * g₀) :
    ∀ a < u + 1, ∀ x ∈ negSpace s', ∀ y ∈ negSpace (i a), polar (quadOdd (u + 5) 𝔽₃) x y = 0 := by
  have hodd : Odd (Nat.card 𝔽₃) := odd_gf3
  by_cases hu : 1 ≤ u
  · exact orth_of_commutes_chain3 hodd (s := u + 1) (by omega) horth
      (L := fun a => (Rz (a + 2)).map (spinAction (quadOdd (u + 5) 𝔽₃))) hL nL hS hc
  · obtain rfl : u = 0 := by omega
    intro a ha
    obtain rfl : a = 0 := by omega
    exact orth_of_commutes_nonscalar3 hodd (hL 0 (by omega)) hS (hc 0 (by omega)) hg₀O hg₀2 fS
      (not_scalar_five3 c ht htz nd h0 h1 hch hαθ hg₀O hconj (hL 0 (by omega)))

end Orth

end CFSG.ClassicalInvolution.Q3.Q3TWY
