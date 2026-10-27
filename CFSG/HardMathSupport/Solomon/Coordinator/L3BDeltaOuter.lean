module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.DiagOuter
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BTorusDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Matrix
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Coordinator
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCLinearSubfield
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.HardMathSupport.Lang.UnitaryAutomorphisms (higher_linear_prime_semilinear_field_descent')
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL (mem_semilinearAutGroup_of_odd)

theorem three_dvd_card_projectiveSL (E : Type) [Field E] [Finite E] :
    3 ∣ Nat.card (projectiveSL 3 E) := by
  let σ : Equiv.Perm (Fin 3) := finRotate 3
  have hdet : ((permGL E σ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).det = 1 := by
    rw [coe_permGL, Matrix.det_permutation]
    have : Equiv.Perm.sign σ⁻¹ = 1 := by
      rw [map_inv]
      have := sign_finRotate 2
      simp [σ]
    simp [this]
  let g : Matrix.SpecialLinearGroup (Fin 3) E := ⟨(permGL E σ : GL (Fin 3) E), hdet⟩
  have hg3 : g ^ 3 = 1 := by
    have h1 : (permGL E σ) ^ 3 = 1 := by
      rw [← map_pow]
      have : σ ^ 3 = 1 := by decide
      rw [this, map_one]
    have hcoe : Matrix.SpecialLinearGroup.toGL g = permGL E σ := Units.ext rfl
    refine Matrix.SpecialLinearGroup.toGL_injective ?_
    rw [map_pow, map_one, hcoe]
    exact h1
  have hx3 : (proj 3 E g) ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
  have hx1 : proj 3 E g ≠ 1 := by
    intro h
    rw [proj_eq_one_iff] at h
    obtain ⟨c, -, hc⟩ := h
    have h10 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 1 0) hc
    simp [g, coe_permGL, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, σ] at h10
  have hord : orderOf (proj 3 E g) = 3 := orderOf_eq_prime hx3 hx1
  have := orderOf_dvd_natCard (proj 3 E g)
  rwa [hord] at this

variable {F : Type} [Field F] [Finite F]

theorem localDeltaIn_eq_bot_of_conj_fieldAut_three {σ : F ≃+* F} (hσ : orderOf σ = 3)
    {H D : Subgroup (MulAut (projectiveSL 3 F))} (hH : innerAut (projectiveSL 3 F) ≤ H)
    {x : MulAut (projectiveSL 3 F)} (hx : x ∈ D) (h : MulAut (projectiveSL 3 F))
    (hxh : x = h * fieldAut 3 F σ * h⁻¹) : localDeltaIn 3 H D = ⊥ := by
  set k := semilinearFixedSubfield σ with hkdef
  have hk : ∀ c, c ∈ k ↔ σ c = c := fun c => RingHom.mem_eqLocusField
  have hinj := CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (k := F)
    (le_refl 3)
  have hx1 : x ≠ 1 := by
    rintro rfl
    have h1 : fieldAut 3 F σ = 1 := by
      calc fieldAut 3 F σ = h⁻¹ * (h * fieldAut 3 F σ * h⁻¹) * h := by group
        _ = 1 := by rw [← hxh, mul_one, inv_mul_cancel]
    have h2 : σ = 1 := fieldAut_injective (le_refl 3) (by rw [h1, map_one])
    rw [h2, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  have hk3 : 3 ≤ 3 := le_rfl
  refine localDeltaIn_eq_bot_of_conj_normal_quasisimple_fixSub Nat.prime_three hinj hH hx hx1 h
    (fieldAut 3 F σ) hxh (linearSubfieldInclusion 3 k).range ?_ ?_
    (isQuasisimple_range_linearSubfieldInclusion hk3 k) ?_ ?_
  · rintro _ ⟨y, rfl⟩
    exact fieldAut_linearSubfieldInclusion (fun c hc => (hk c).1 hc) y
  · intro a ha t ht
    exact conj_mem_range_linearSubfieldInclusion σ ha ht
  · rw [← Nat.card_congr (MonoidHom.ofInjective (linearSubfieldInclusion_injective
      (by omega) k)).toEquiv]
    have : Finite k := inferInstance
    exact three_dvd_card_projectiveSL k
  · intro g hg hfix
    have hmem : g ∈ fixingSubgroup (MulAut (projectiveSL 3 F))
        ((linearSubfieldInclusion 3 k).range : Set (projectiveSL 3 F)) :=
      (mem_fixingSubgroup_iff _).2 fun y hy => hfix y hy
    rw [fixingSubgroup_range_linearSubfieldInclusion hk hk3] at hmem
    have hdvd : orderOf g ∣ 3 := by
      have h3 : orderOf (fieldAut 3 F σ) = 3 := by rw [orderOf_fieldAut hk3 σ]; exact hσ
      have := orderOf_dvd_of_mem_zpowers hmem
      rwa [h3] at this
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hg.symm hdvd)

theorem localDeltaIn_eq_bot_of_mem_semilinear_not_linear_three
    {H D : Subgroup (MulAut (projectiveSL 3 F))} (hH : innerAut (projectiveSL 3 F) ≤ H)
    {x : MulAut (projectiveSL 3 F)} (hx : x ∈ D) (hxE : x ∈ semilinearAutGroup 3 F)
    (hxD : x ∉ linearAutGroup 3 F) (hxp : x ^ 3 = 1) : localDeltaIn 3 H D = ⊥ := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨f, hℓ, hcard⟩ := FiniteField.card F (ringChar F)
  have hx1 : x ≠ 1 := fun h => hxD (h ▸ (linearAutGroup 3 F).one_mem)
  have hFc : Nat.card F = ringChar F ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨hpf, σ, hσ, ⟨h, -, hxh⟩, hk⟩ := higher_linear_prime_semilinear_field_descent' hℓ
    f.pos (le_refl 3) hFc Nat.prime_three x hxE hxD (orderOf_eq_prime hxp hx1)
  exact localDeltaIn_eq_bot_of_conj_fieldAut_three hσ hH hx h hxh

theorem localDeltaIn_eq_bot_of_not_le_linearAutGroup_three {D : Subgroup (MulAut (projectiveSL 3 F))}
    (hD : IsElemAbelian 3 D) (hDl : ¬ D ≤ linearAutGroup 3 F)
    {H : Subgroup (MulAut (projectiveSL 3 F))} (hH : innerAut (projectiveSL 3 F) ≤ H) :
    localDeltaIn 3 H D = ⊥ := by
  obtain ⟨x, hx, hxl⟩ := IsConcreteLE.not_le_iff_exists.1 hDl
  have hxp := hD.2 x hx
  have hxE : x ∈ semilinearAutGroup 3 F := by
    refine mem_semilinearAutGroup_of_odd (le_refl 3) ?_
    rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hxp) with h | h
    · rw [h]; exact odd_one
    · rw [h]; decide
  exact localDeltaIn_eq_bot_of_mem_semilinear_not_linear_three hH hx hxE hxl hxp

end CFSG.HardMathSupport.Solomon.Coordinator
