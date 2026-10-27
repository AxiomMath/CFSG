module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5OneAltQ
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5OneTrans

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS Equiv.Perm.OnCycleFactors
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))} {s : X}

theorem card_fixedPoints_eq_fixCount {m : ℕ} (σ : Perm (Fin m)) :
    Nat.card (Function.fixedPoints σ) = fixCount σ := by
  classical
  unfold fixCount
  rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  rfl

@[expose] noncomputable def Sec5S.psi (hS : Sec5S X n z Z S s) (hn : 8 ≤ n) {B : Subgroup X}
    (hB : Sec5Comp X n (centralizer ({s} : Set X)) B) (M : AhatModel X n B) {A : Subgroup X}
    (hA : Sec5Comp X n (normalizer (Z : Set X)) A) : ↥(hGrp s A) →* Perm (Fin n) :=
  (pAct hn hB M).comp (Subgroup.inclusion (hS.hGrp_le_normComps hA))

theorem Sec5S.odd_card_ker_psi (hS : Sec5S X n z Z S s) (hn : 8 ≤ n) {B : Subgroup X}
    (hB : Sec5Comp X n (centralizer ({s} : Set X)) B) (M : AhatModel X n B) {A : Subgroup X}
    (hA : Sec5Comp X n (normalizer (Z : Set X)) A) :
    Odd (Nat.card (hS.psi hn hB M hA).ker) := by
  have hodd := hS.odd_card_hGrp_inf_ker hn hB M hA
  let g : (hS.psi hn hB M hA).ker →*
      ↥((hGrp s A).subgroupOf (normComps X n s) ⊓ (pAct hn hB M).ker) :=
    { toFun := fun t => ⟨⟨(t.1 : X), hS.hGrp_le_normComps hA t.1.2⟩, ⟨t.1.2, t.2⟩⟩
      map_one' := rfl
      map_mul' := fun a b => rfl }
  have hg : Function.Injective g := fun a b h => by
    have h1 := congrArg (fun w => (((w : ↥(normComps X n s)) : X))) (congrArg Subtype.val h)
    apply Subtype.ext
    apply Subtype.ext
    exact h1
  exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_injective g hg)

theorem Sec5S.large_false (hF : Solomon75Frac53) (hN : Solomon75NoSwap)
    (hS : Sec5S X n z Z S s) (hn12 : 12 ≤ n) {A₁ A₂ : Subgroup X}
    (hA₁ : Sec5Comp X n (normalizer (Z : Set X)) A₁)
    (hA₂ : Sec5Comp X n (normalizer (Z : Set X)) A₂) (hne : A₁ ≠ A₂) : False := by
  classical
  have hn : 8 ≤ n := by omega
  obtain ⟨B, hB, -⟩ := hS.data.exists_comp_centralizer hS.inv
  set M : AhatModel X n B := AhatModel.ofCover hB.2 with hM
  set N : Subgroup X := normalizer (Z : Set X) with hNdef
  set G : Subgroup X := normComps X n s ⊓ N with hG
  let p : ↥(normComps X n s) →* Perm (Fin n) := pAct hn hB M
  let p₀ : ↥G →* Perm (Fin n) := p.comp (Subgroup.inclusion inf_le_left)
  let Q : Subgroup (Perm (Fin n)) := p₀.range
  obtain ⟨z₁, hz₁Z, hz₁A, hz₁1⟩ := hS.data.exists_mem_Z_inf hA₁
  have hz₁2 : z₁ * z₁ = 1 := hS.data.Z_sq_eq_one hz₁Z
  have hz₁s : z₁ * s = s * z₁ := hS.comm_of_mem_Z hA₁ hz₁Z hz₁A hz₁1
  have hz₁inv : z₁ ∈ invsOf s A₁ := ⟨hz₁A, hz₁1, hz₁2, hz₁s⟩
  have hz₁N : z₁ ∈ normComps X n s := hS.hGrp_le_normComps hA₁ (subset_hGrp hz₁inv)
  let ζ : Perm (Fin n) := p ⟨z₁, hz₁N⟩
  have hζ2 : ζ * ζ = 1 := by
    have : (⟨z₁, hz₁N⟩ : ↥(normComps X n s)) * ⟨z₁, hz₁N⟩ = 1 := Subtype.ext hz₁2
    show p ⟨z₁, hz₁N⟩ * p ⟨z₁, hz₁N⟩ = 1
    rw [← map_mul, this, map_one]
  have hζfix : fixCount ζ ≤ 3 := hS.fixCount_pAct_le hF hN hn hB M hA₁ hz₁Z hz₁A hz₁1 hz₁N
  let U : Subgroup (Perm (Fin n)) := Q ⊓ Subgroup.centralizer ({ζ} : Set (Perm (Fin n)))
  let Φ : ↥U →* Perm ζ.cycleFactorsFinset :=
    (toPermHom ζ).comp (Subgroup.inclusion inf_le_right)
  have hΦ : Group.IsSolvable Φ.ker := by
    have hsolv : Group.IsSolvable ↥(toPermHom ζ).ker :=
      solvable_ker_toPermHom ζ (by rw [card_fixedPoints_eq_fixCount]; omega)
    let g : Φ.ker →* ↥(toPermHom ζ).ker :=
      ⟨⟨fun t => ⟨Subgroup.inclusion inf_le_right t.1, t.2⟩, rfl⟩, fun a b => rfl⟩
    have hg : Function.Injective g := fun a b h => by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun w : ↥(toPermHom ζ).ker =>
        ((w : ↥(centralizer ({ζ} : Set (Perm (Fin n))))) : Perm (Fin n))) h
    exact Group.isSolvable_of_isSolvable_injective hg
  let Y : Subgroup ↥G := (oddCoreOf N).subgroupOf G
  have hYn : Y.Normal := ⟨fun a ha g => by
    show ((g * a * g⁻¹ : ↥G) : X) ∈ oddCoreOf N
    have hg : (g : X) ∈ N := g.2.2
    have h1 : (a : X) ∈ oddCoreOf N := ha
    have := (Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreOf N hg) (a : X)).1 h1
    simpa using this⟩
  let Lp : Subgroup (Perm (Fin n)) := Y.map p₀
  have hLodd : Odd (Nat.card Lp) := by
    have hYle : Y.map G.subtype ≤ oddCoreOf N := by
      rintro _ ⟨y, hy, rfl⟩
      exact hy
    have h0 : Nat.card (Y.map G.subtype) = Nat.card Y :=
      Subgroup.card_map_of_injective G.subtype_injective
    have h1 : Nat.card Y ∣ Nat.card (oddCoreOf N) := by
      rw [← h0]
      exact Subgroup.card_dvd_of_le hYle
    exact Odd.of_dvd_nat (odd_card_oddCoreOf N) ((Subgroup.card_map_dvd Y p₀).trans h1)
  have hLn : ∀ u ∈ U, ∀ l ∈ Lp, u * l * u⁻¹ ∈ Lp := by
    rintro u ⟨⟨γ, rfl⟩, -⟩ _ ⟨y, hy, rfl⟩
    refine ⟨γ * y * γ⁻¹, hYn.conj_mem y hy γ, ?_⟩
    simp [map_mul, map_inv]
  have hVG : ∀ (A : Subgroup X), Sec5Comp X n N A → ∀ t : ↥(hGrp s A), (t : X) ∈ G :=
    fun A hA t => ⟨hS.hGrp_le_normComps hA t.2, hA.isPCompIn.1 (hGrp_le s A t.2).1⟩
  have hU : ∀ (A : Subgroup X) (hA : Sec5Comp X n N A) (t : ↥(hGrp s A)),
      hS.psi hn hB M hA t ∈ U := by
    intro A hA t
    have hmem : hS.psi hn hB M hA t ∈ Subgroup.centralizer ({ζ} : Set (Perm (Fin n))) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hAD : A ≤ K0 X n N := le_sSup hA
      have hcomm' : z₁ * (t : X) = (t : X) * z₁ :=
        hS.data.Z_le_center_K0 hz₁Z (hAD (hGrp_le s A t.2).1)
      show p ⟨t.1, hS.hGrp_le_normComps hA t.2⟩ * p ⟨z₁, hz₁N⟩ =
        p ⟨z₁, hz₁N⟩ * p ⟨t.1, hS.hGrp_le_normComps hA t.2⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hcomm'.symm
    exact ⟨⟨⟨t.1, hVG A hA t⟩, rfl⟩, hmem⟩
  have hcommLp : ∀ (a : ↥(hGrp s A₁)) (b : ↥(hGrp s A₂)),
      ⁅hS.psi hn hB M hA₁ a, hS.psi hn hB M hA₂ b⁆ ∈ Lp := by
    intro a b
    let a' : ↥G := ⟨a.1, hVG A₁ hA₁ a⟩
    let b' : ↥G := ⟨b.1, hVG A₂ hA₂ b⟩
    refine ⟨⁅a', b'⁆, ?_, map_commutatorElement p₀ a' b'⟩
    show ((⁅a', b'⁆ : ↥G) : X) ∈ oddCoreOf N
    have ha : (a : X) ∈ A₁ := (hGrp_le s A₁ a.2).1
    have hb : (b : X) ∈ A₂ := (hGrp_le s A₂ b.2).1
    have := commutator_mem_oddCoreOf_of_ne hA₁.isPCompIn hA₂.isPCompIn hne ha hb
    simpa [commutatorElement_def] using this
  obtain ⟨k₁, C₁, hF₁, hD₁, π₁, h5₁, hc₁, hkn₁, hnk₁, hπ₁⟩ := hS.exists_alt_quot hn12 hA₁
  obtain ⟨k₂, C₂, hF₂, hD₂, π₂, h5₂, hc₂, hkn₂, hnk₂, hπ₂⟩ := hS.exists_alt_quot hn12 hA₂
  obtain ⟨kζ, hkζ⟩ := exists_support_card_of_mul_self hζ2
  have hcβ : Fintype.card ζ.cycleFactorsFinset = kζ :=
    AhatData.card_cycleFactorsFinset_of_involution hζ2 hkζ
  have hkζn : 2 * kζ ≤ n := by
    have := Finset.card_le_univ ζ.support
    simpa [hkζ] using this
  have hcount := card_alt_mul_le_factorial U Φ hΦ Lp hLn hLodd (hS.psi hn hB M hA₁)
    (hS.psi hn hB M hA₂) (hU A₁ hA₁) (hU A₂ hA₂) hcommLp (by omega) (by omega) π₁ π₂ hπ₁ hπ₂
    (hS.odd_card_ker_psi hn hB M hA₁) (hS.odd_card_ker_psi hn hB M hA₂)
  rw [hc₁, hc₂, hcβ] at hcount
  rcases le_total k₂ k₁ with h | h
  · exact false_of_alt_counts h5₂ h (by omega) hcount
  · rw [mul_comm] at hcount
    exact false_of_alt_counts h5₁ h (by omega) hcount

end CFSG.OddStandard.Solomon75
