module

public import CFSG.ClassicalInvolution.Asc77.AscC25W12
public import CFSG.ClassicalInvolution.Asc77.AscC25W15

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25W

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

namespace Sp

variable {F : Type} [Field F]

theorem psp4_map_inv_eq (h2 : (2 : F) ≠ 0) {Y : Type} [Group Y] (ψ : StatedSp 2 F →* Y)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F)) {L : Subgroup (StatedSp 2 F)}
    {j : StatedSp 2 F} (hL : IsLongRootSp2 L j) {z : Y} (hzL : IsUniqueInvolution (L.map ψ) z) :
    ψ j = z := by
  have hcen : Subgroup.center (StatedSp 2 F) = spScalars 2 F :=
    CFSG.LieType.Universal.Symplectic.center_eq 2 F
  have hjL : j ∈ L := (hL.isClassicalSL2 h2).mem
  have hj2 : j * j = 1 := by
    have := pow_orderOf_eq_one j
    rwa [(hL.isClassicalSL2 h2).orderOf_eq_two, pow_two] at this
  have hmem : ψ j ∈ L.map ψ := Subgroup.mem_map_of_mem ψ hjL
  have hψj2 : ψ j * ψ j = 1 := by rw [← map_mul, hj2, map_one]
  rcases hzL.unique (ψ j) hmem hψj2 with h | h
  · exfalso
    have hjk : j ∈ ψ.ker := h
    have hjc := hker hjk
    rw [hcen] at hjc
    obtain ⟨c, hc⟩ := scalar_of_mem_spScalars hjc
    obtain ⟨k, g, -, hjg⟩ := hL
    rw [hjg] at hc
    exact longInv_conj_not_scalar h2 k g ⟨c, hc⟩
  · exact h

theorem psp4_model_cent [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) {Y : Type} [Group Y]
    (ψ : StatedSp 2 F →* Y) (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F))
    (hsurj : Function.Surjective ψ) {R R' : Subgroup (StatedSp 2 F)} {i i' : StatedSp 2 F}
    (hR : IsLongRootSp2 R i) (hR' : IsLongRootSp2 R' i') (hne : R.map ψ ≠ R'.map ψ) {z' : Y}
    (hz : IsUniqueInvolution (R.map ψ) z') (hz' : IsUniqueInvolution (R'.map ψ) z')
    (β : MulAut Y) (hβ : ∀ y ∈ R.map ψ, β y = y) (hβ' : ∀ y ∈ R'.map ψ, β y = y) :
    β = 1 ∨ ∀ y, β y = z' * y * z'⁻¹ := by
  have hk := ker_eq_spScalars h2 ψ hker hR hR' hne hz hz'
  have hψi := psp4_map_inv_eq h2 ψ hker hR hz
  have hψi' := psp4_map_inv_eq h2 ψ hker hR' hz'
  have hcen : Subgroup.center (StatedSp 2 F) = spScalars 2 F :=
    CFSG.LieType.Universal.Symplectic.center_eq 2 F
  set e := projEquiv ψ hsurj hk with he
  let β' : MulAut (StatedProj (StatedSp 2 F)) := e.trans (β.trans e.symm)
  have hβ'e : ∀ y, e (β' (e.symm y)) = β y := fun y => by simp [β']
  have he_proj : ∀ x, e (proj 2 F x) = ψ x := fun x => projEquiv_proj ψ hsurj hk x
  have hiR : i ∈ R := (hR.isClassicalSL2 h2).mem
  have hi'R' : i' ∈ R' := (hR'.isClassicalSL2 h2).mem
  have hi2 : i * i = 1 := by
    have := pow_orderOf_eq_one i
    rwa [(hR.isClassicalSL2 h2).orderOf_eq_two, pow_two] at this
  have hi'2 : i' * i' = 1 := by
    have := pow_orderOf_eq_one i'
    rwa [(hR'.isClassicalSL2 h2).orderOf_eq_two, pow_two] at this
  have hi1 : i ≠ 1 := by
    intro h
    have := (hR.isClassicalSL2 h2).orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  have hi'1 : i' ≠ 1 := by
    intro h
    have := (hR'.isClassicalSL2 h2).orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  have hc : i' * i⁻¹ ∈ Subgroup.center (StatedSp 2 F) := by
    rw [hcen, ← hk]
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψi, hψi', mul_inv_cancel]
  have hRne : R ≠ R' := fun h => hne (by rw [h])
  have hβR : ∀ r ∈ R, β' (proj 2 F r) = proj 2 F r := by
    intro r hr
    have h1 : β (ψ r) = ψ r := hβ _ (Subgroup.mem_map_of_mem ψ hr)
    have h2' : β' (proj 2 F r) = e.symm (β (e (proj 2 F r))) := rfl
    rw [h2', he_proj, h1]
    exact e.symm_apply_eq.mpr (he_proj r).symm
  have hβR' : ∀ r ∈ R', β' (proj 2 F r) = proj 2 F r := by
    intro r hr
    have h1 : β (ψ r) = ψ r := hβ' _ (Subgroup.mem_map_of_mem ψ hr)
    have h2' : β' (proj 2 F r) = e.symm (β (e (proj 2 F r))) := rfl
    rw [h2', he_proj, h1]
    exact e.symm_apply_eq.mpr (he_proj r).symm
  rcases psp4_cent h2 h4 ⟨i, hR⟩ ⟨i', hR'⟩ hRne hiR hi2 hi1 hi'R' hi'2 hi'1 hc β' hβR hβR' with
    h | h
  · left
    ext y
    rw [← hβ'e y, h]
    simp
  · right
    intro y
    have hconj : e (proj 2 F i * e.symm y * (proj 2 F i)⁻¹) = z' * y * z'⁻¹ := by
      rw [map_mul, map_mul, map_inv, he_proj, MulEquiv.apply_symm_apply, hψi]
    rw [← hβ'e y, h, MulAut.conj_apply]
    exact hconj

end Sp

section ModelFact

variable (p f : ℕ) [Fact p.Prime]

@[expose] def Cent5 : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (D : LieSystemData p f Y Φ)
    (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    D.card = 1 → (∃ i : Fin D.card, IsOrthTag 5 true (D.tag i) (D.rank i)) →
    TwinSect0 Φ A A' z' a₀ b₀ →
    ∀ β : Y ≃* Y, (∀ x ∈ A, β x = x) → (∀ x ∈ A', β x = x) →
      β = 1 ∨ ∀ y : Y, β y = z' * y * z'⁻¹

end ModelFact

variable {p f : ℕ} [Fact p.Prime]


theorem cent5_of_hom (hp2 : p ≠ 2) {Y : Type} [Group Y] (t : StatedLieTag) (k e : ℕ)
    (hadm : StatedLieAdmissible t k p e) (ψ : (modelUniv t k p e Fact.out).K →* Y)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K)
    (hsurj : Function.Surjective ψ) (ht : t = .PSp) (hk : k = 2) (hq : 5 ≤ p ^ e)
    {R R' : Subgroup (modelUniv t k p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    (hR' : R' ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    (hne : R.map ψ ≠ R'.map ψ) {z' : Y} (hz : IsUniqueInvolution (R.map ψ) z')
    (hz' : IsUniqueInvolution (R'.map ψ) z') (β : MulAut Y)
    (hβ : ∀ y ∈ R.map ψ, β y = y) (hβ' : ∀ y ∈ R'.map ψ, β y = y) :
    β = 1 ∨ ∀ y, β y = z' * y * z'⁻¹ := by
  subst ht hk
  have he : e ≠ 0 := by
    rintro rfl
    simp at hq
  have h2 := two_ne_zero_gf (p := p) e hp2
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e he]
    omega
  obtain ⟨P, hP, hRP⟩ := (mem_fundamentalSubgroups_PSp_iff hadm R).mp hR
  obtain ⟨P', hP', hRP'⟩ := (mem_fundamentalSubgroups_PSp_iff hadm R').mp hR'
  obtain ⟨i, hi⟩ := (exists_isLongRootSp2_iff h2 R).mpr ⟨P, hP, hRP⟩
  obtain ⟨i', hi'⟩ := (exists_isLongRootSp2_iff h2 R').mpr ⟨P', hP', hRP'⟩
  exact Sp.psp4_model_cent h2 h4 ψ hker hsurj hi hi' hne hz hz' β hβ hβ'

theorem cent5_proved : Cent5 p f := by
  intro hp2 hq Y _ _ Φ D A A' z' a₀ b₀ hD1 hi htw β hA hA'
  obtain ⟨i, hi⟩ := hi
  have hsub : Subsingleton (Fin D.card) := by
    rw [hD1]
    infer_instance
  have hsurj : ∀ j : Fin D.card, Function.Surjective (D.hom j) := by
    intro j
    rw [← MonoidHom.range_eq_top]
    have hall : ∀ l : Fin D.card, (D.hom l).range ≤ (D.hom j).range := by
      intro l
      rw [Subsingleton.elim l j]
    refine eq_top_iff.mpr ?_
    rw [← D.generate]
    exact iSup_le hall
  have hcase : ∀ j : Fin D.card, D.tag j = .PSp ∧ D.rank j = 2 := by
    intro j
    rw [Subsingleton.elim j i]
    simp only [IsOrthTag] at hi
    rcases hi with ⟨-, ht, hn⟩ | ⟨h6, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ | ⟨h8, -⟩
    · exact ⟨ht, hn⟩
    all_goals omega
  have hexp : ∀ j : Fin D.card, D.exp j = f := by
    intro j
    rcases D.exp_eq j with h | ⟨hT, -⟩
    · exact h
    · rw [(hcase j).1] at hT
      exact absurd hT (by decide)
  obtain ⟨i₁, R, hR, hAR⟩ := D.fundamental A htw.hA
  obtain ⟨i₂, R', hR', hAR'⟩ := D.fundamental A' htw.hA'
  have h₂₁ : i₂ = i₁ := Subsingleton.elim _ _
  subst h₂₁
  have hq' : 5 ≤ p ^ D.exp i₂ := by rw [hexp i₂]; exact hq
  have hz : IsUniqueInvolution (R.map (D.hom i₂)) z' := by
    rw [← hAR]
    exact htw.hzA
  have hz' : IsUniqueInvolution (R'.map (D.hom i₂)) z' := by
    rw [← hAR']
    exact htw.hzA'
  have hne : R.map (D.hom i₂) ≠ R'.map (D.hom i₂) := by
    rw [← hAR, ← hAR']
    exact htw.ne
  exact cent5_of_hom hp2 (D.tag i₂) (D.rank i₂) (D.exp i₂) (D.admissible i₂) (D.hom i₂)
    (D.ker_le_center i₂) (hsurj i₂) (hcase i₂).1 (hcase i₂).2 hq' hR hR' hne hz hz' β
    (by rw [← hAR]; exact hA) (by rw [← hAR']; exact hA')

end CFSG.ClassicalInvolution.Asc77.C25W
