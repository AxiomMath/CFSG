module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BFieldCentral
public import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
import CFSG.LieType.Universal.SpecialLinear

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.GLS.IVK Matrix
open scoped commutatorElement

section PSL

variable {F : Type} [Field F] (σ : F ≃+* F)

@[expose] noncomputable def l3bT : Subgroup (projectiveSL 3 F) :=
  ((proj 3 F).comp (SpecialLinearGroup.map (n := Fin 3) (fixedField σ).subtype)).range

theorem l3bT_le_fix : l3bT σ ≤ l3bFix (fieldAut 3 F σ) := by
  rintro _ ⟨A₀, rfl⟩
  show fieldAut 3 F σ (proj 3 F _) = proj 3 F _
  rw [fieldAut_proj]
  congr 1
  ext i j
  exact fixedField_apply σ _

theorem exists_scalar_of_mem_fix {d : projectiveSL 3 F} (hd : d ∈ l3bFix (fieldAut 3 F σ)) :
    ∃ A : SpecialLinearGroup (Fin 3) F, proj 3 F A = d ∧
      ∃ s ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F),
        SpecialLinearGroup.map σ.toRingHom A = A * s := by
  obtain ⟨A, rfl⟩ := proj_surjective 3 F d
  refine ⟨A, rfl, A⁻¹ * SpecialLinearGroup.map σ.toRingHom A, ?_, by group⟩
  have h : fieldAut 3 F σ (proj 3 F A) = proj 3 F A := hd
  rw [fieldAut_proj, proj_eq_proj_iff] at h
  have h' := (Subgroup.center (SpecialLinearGroup (Fin 3) F)).inv_mem
    ((scalars_eq_center 3 F) ▸ h)
  simpa using h'

theorem mem_l3bT_of_fixed {A : SpecialLinearGroup (Fin 3) F}
    (hA : SpecialLinearGroup.map σ.toRingHom A = A) : proj 3 F A ∈ l3bT σ := by
  obtain ⟨A₀, rfl⟩ := CFSG.RankThree.PartTwo.KFacts.exists_sl_map_subtype_eq hA
  exact ⟨A₀, rfl⟩

theorem commutator_fix_le_l3bT : ⁅l3bFix (fieldAut 3 F σ), l3bFix (fieldAut 3 F σ)⁆ ≤ l3bT σ := by
  rw [Subgroup.commutator_le]
  intro d₁ h₁ d₂ h₂
  obtain ⟨A₁, rfl, s₁, hs₁, e₁⟩ := exists_scalar_of_mem_fix σ h₁
  obtain ⟨A₂, rfl, s₂, hs₂, e₂⟩ := exists_scalar_of_mem_fix σ h₂
  rw [← map_commutatorElement]
  apply mem_l3bT_of_fixed
  rw [map_commutatorElement, e₁, e₂]
  exact l3bf_commutator_central_mul hs₁ hs₂

theorem cube_fix_mem_l3bT {d : projectiveSL 3 F} (hd : d ∈ l3bFix (fieldAut 3 F σ)) :
    d ^ 3 ∈ l3bT σ := by
  obtain ⟨A, rfl, s, hs, e⟩ := exists_scalar_of_mem_fix σ hd
  rw [← map_pow]
  apply mem_l3bT_of_fixed
  have hs3 : s ^ 3 = 1 := by
    obtain ⟨r, hr, hrs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hs
    apply Subtype.ext
    have hr' : r ^ 3 = 1 := by simpa using hr
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hrs, ← map_pow, hr', map_one]
    rfl
  have hc : Commute A s := Subgroup.mem_center_iff.1 hs A
  rw [map_pow, e, hc.mul_pow, hs3, mul_one]

@[expose] noncomputable def l3bG : SpecialLinearGroup (Fin 3) (fixedField σ) →* projectiveSL 3 F :=
  (proj 3 F).comp (SpecialLinearGroup.map (n := Fin 3) (fixedField σ).subtype)

theorem l3bT_eq_map : l3bT σ = (⊤ : Subgroup (SpecialLinearGroup (Fin 3) (fixedField σ))).map
    (l3bG σ) := by
  rw [l3bT, ← MonoidHom.range_eq_map]
  rfl

theorem l3bT_perfect : ⁅l3bT σ, l3bT σ⁆ = l3bT σ := by
  have hperf : commutator (SpecialLinearGroup (Fin 3) (fixedField σ)) = ⊤ :=
    (Group.isPerfect_def (G := SpecialLinearGroup (Fin 3) (fixedField σ))).1
      (CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl)
  rw [l3bT_eq_map, ← Subgroup.map_commutator, ← commutator_def, hperf]

theorem commutator_fix_eq : ⁅l3bFix (fieldAut 3 F σ), l3bFix (fieldAut 3 F σ)⁆ = l3bT σ := by
  refine le_antisymm (commutator_fix_le_l3bT σ) ?_
  calc l3bT σ = ⁅l3bT σ, l3bT σ⁆ := (l3bT_perfect σ).symm
    _ ≤ _ := Subgroup.commutator_mono (l3bT_le_fix σ) (l3bT_le_fix σ)

theorem ker_l3bG : (l3bG σ).ker = Subgroup.center (SpecialLinearGroup (Fin 3) (fixedField σ)) := by
  ext x
  constructor
  · intro hx
    have h1 : SpecialLinearGroup.map (n := Fin 3) (fixedField σ).subtype x ∈ scalars 3 F :=
      proj_eq_one_iff.1 hx
    obtain ⟨c, hc, hxc⟩ := mem_scalars.1 h1
    have hxij : ∀ i j, (((x : Matrix (Fin 3) (Fin 3) (fixedField σ)) i j : fixedField σ) : F) =
        (scalar (Fin 3) (c : F)) i j := fun i j => by
      rw [← hxc]; rfl
    have hc3 : (c : F) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
    have hdiag : ∀ i, (((x : Matrix (Fin 3) (Fin 3) (fixedField σ)) i i : fixedField σ) : F) = c := by
      intro i
      have := hxij i i
      simpa [scalar_apply, diagonal_apply_eq] using this
    refine Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨(x : Matrix (Fin 3) (Fin 3) (fixedField σ)) 0 0, ?_, ?_⟩
    · apply Subtype.ext
      rw [Fintype.card_fin, SubmonoidClass.coe_pow, hdiag 0, hc3]
      rfl
    · ext i j
      by_cases h : i = j
      · subst h
        simp [scalar_apply, diagonal_apply_eq, hdiag]
      · simp [scalar_apply, diagonal_apply_ne _ h, hxij i j]
  · intro hx
    obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hx
    rw [MonoidHom.mem_ker]
    show proj 3 F (SpecialLinearGroup.map (n := Fin 3) (fixedField σ).subtype x) = 1
    rw [proj_eq_one_iff, scalars_eq_center]
    refine Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨(r : F), ?_, ?_⟩
    · have : r ^ 3 = 1 := by simpa using hr
      have h2 := congrArg (fun t : fixedField σ => (t : F)) this
      simpa using h2
    · rw [Matrix.SpecialLinearGroup.map_apply_coe, ← hrx]
      ext i j
      simp only [scalar_apply, diagonal_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
      split_ifs <;> simp

@[expose] noncomputable def l3bTEquiv :
    (SpecialLinearGroup (Fin 3) (fixedField σ) ⧸ Subgroup.center (SpecialLinearGroup (Fin 3) (fixedField σ))) ≃*
      ↥(l3bT σ) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_l3bG σ).symm).trans
    (QuotientGroup.quotientKerEquivRange (l3bG σ))

theorem l3bT_quasisimple_data :
    IsSimpleGroup ↥(l3bT σ) ∧ ∃ a b : ↥(l3bT σ), a * b ≠ b * a := by
  obtain ⟨-, hsimple, a, b, hab⟩ :=
    CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 (fixedField σ) le_rfl
  have E := l3bTEquiv σ
  refine ⟨E.symm.isSimpleGroup, E a, E b, fun h => hab (E.injective ?_)⟩
  rw [map_mul, map_mul]
  exact h

@[expose] def l3bCyc (K : Type) [Field K] : SpecialLinearGroup (Fin 3) K :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by simp [Matrix.det_fin_three]⟩

theorem l3bCyc_pow_three (K : Type) [Field K] : l3bCyc K ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [l3bCyc, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem l3bCyc_not_mem_center (K : Type) [Field K] :
    l3bCyc K ∉ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
  intro h
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 h
  have := congrFun (congrFun hr 0) 2
  simp [l3bCyc, scalar_apply] at this

theorem three_dvd_card_l3bT : 3 ∣ Nat.card ↥(l3bT σ) := by
  have hne : l3bG σ (l3bCyc (fixedField σ)) ≠ 1 := by
    intro h
    have : l3bCyc (fixedField σ) ∈ (l3bG σ).ker := h
    rw [ker_l3bG] at this
    exact l3bCyc_not_mem_center _ this
  have hpow : l3bG σ (l3bCyc (fixedField σ)) ^ 3 = 1 := by
    rw [← map_pow, l3bCyc_pow_three, map_one]
  have hx : l3bG σ (l3bCyc (fixedField σ)) ∈ l3bT σ := ⟨_, rfl⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho : orderOf (⟨_, hx⟩ : ↥(l3bT σ)) = 3 :=
    orderOf_eq_prime (Subtype.ext hpow) (fun h => hne (congrArg Subtype.val h))
  have := orderOf_dvd_natCard (⟨_, hx⟩ : ↥(l3bT σ))
  rwa [ho] at this

theorem l3bf_fixData_psl : L3BFixData (fieldAut 3 F σ) := by
  have hq := l3bT_quasisimple_data σ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [commutator_fix_eq]; exact hq.1
  · rw [commutator_fix_eq]; exact hq.2
  · rw [commutator_fix_eq]; exact three_dvd_card_l3bT σ
  · intro d hd
    rw [commutator_fix_eq]
    exact cube_fix_mem_l3bT σ hd

end PSL

end CFSG.HardMathSupport.Solomon.Coordinator
