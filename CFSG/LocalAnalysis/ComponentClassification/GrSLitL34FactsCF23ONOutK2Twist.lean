module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutK2
public import CFSG.Sporadic.ONOddCore.OuterQuot
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public noncomputable section

namespace CFSG.ComponentClassification.SolMax.ONOut

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Sporadic.ONOddCore CFSG.ONSchreier
open CFSG.ComponentClassification.PSL3Four (frob)

abbrev S3 : Type := projectiveSL 3 PSL3Four.F4

@[expose] def IsGF (ψ : MulAut S3) : Prop :=
  ∃ A : GL (Fin 3) PSL3Four.F4, ψ = conjAut 3 PSL3Four.F4 A * dualAut 3 PSL3Four.F4 ∨
    ψ = conjAut 3 PSL3Four.F4 A * fieldAut 3 PSL3Four.F4 frob

theorem frob_mul_frob : frob * frob = 1 :=
  RingEquiv.ext fun x => frob.left_inv x

theorem frob_ne_one : frob ≠ 1 := by
  intro h
  have := congrArg (fun σ : PSL3Four.F4 ≃+* PSL3Four.F4 => σ PSL3Four.F4.ω) h
  simp only [PSL3Four.frob_apply] at this
  revert this
  decide

theorem dual_sq : dualAut 3 PSL3Four.F4 * dualAut 3 PSL3Four.F4 = 1 :=
  (standard_automorphism_transport (n := 3) (K := PSL3Four.F4)).2.2.2.1

theorem field_sq : fieldAut 3 PSL3Four.F4 frob * fieldAut 3 PSL3Four.F4 frob = 1 := by
  rw [← map_mul, frob_mul_frob, map_one]

theorem dual_not_mem : dualAut 3 PSL3Four.F4 ∉ linearAutGroup 3 PSL3Four.F4 := fun h =>
  ProjectivePlane.dualAut_not_mem_semilinearAutGroup (le_refl 3)
    (linearAutGroup_le_semilinearAutGroup h)

theorem field_not_mem : fieldAut 3 PSL3Four.F4 frob ∉ linearAutGroup 3 PSL3Four.F4 := fun h =>
  frob_ne_one ((CFSG.RankThree.PartTwo.KFacts.fieldAut_mem_linearAutGroup_iff (le_refl 3)).1 h)

theorem reduce_df {G : Type*} [Group G] {d f : G} (hd : d * d = 1) (hf : f * f = 1)
    (hdf : d * f = f * d) {e₁ e₂ e₃ : G} (h₁ : e₁ = d ∨ e₁ = f) (h₂ : e₂ = d ∨ e₂ = f)
    (h₃ : e₃ = d ∨ e₃ = f) : e₃ * (e₁ * e₂)⁻¹ = d ∨ e₃ * (e₁ * e₂)⁻¹ = f := by
  have hd' : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  have hf' : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf
  have c1 : d * (d * d)⁻¹ = d := by rw [hd, inv_one, mul_one]
  have c2 : f * (d * d)⁻¹ = f := by rw [hd, inv_one, mul_one]
  have c3 : d * (f * f)⁻¹ = d := by rw [hf, inv_one, mul_one]
  have c4 : f * (f * f)⁻¹ = f := by rw [hf, inv_one, mul_one]
  have c5 : d * (d * f)⁻¹ = f := by
    rw [mul_inv_rev, hd', hf', ← mul_assoc, hdf, mul_assoc, hd, mul_one]
  have c6 : f * (d * f)⁻¹ = d := by rw [mul_inv_rev, hd', hf', ← mul_assoc, hf, one_mul]
  have c7 : d * (f * d)⁻¹ = f := by rw [mul_inv_rev, hd', hf', ← mul_assoc, hd, one_mul]
  have c8 : f * (f * d)⁻¹ = d := by
    rw [mul_inv_rev, hd', hf', ← mul_assoc, ← hdf, mul_assoc, hf, mul_one]
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> rcases h₃ with rfl | rfl
  · exact Or.inl c1
  · exact Or.inr c2
  · exact Or.inr c5
  · exact Or.inl c6
  · exact Or.inr c7
  · exact Or.inl c8
  · exact Or.inl c3
  · exact Or.inr c4

theorem swap_conj {ε : MulAut S3}
    (hε : ε = dualAut 3 PSL3Four.F4 ∨ ε = fieldAut 3 PSL3Four.F4 frob)
    (A : GL (Fin 3) PSL3Four.F4) :
    ∃ A' : GL (Fin 3) PSL3Four.F4, ε * conjAut 3 PSL3Four.F4 A = conjAut 3 PSL3Four.F4 A' * ε := by
  rcases hε with rfl | rfl
  · exact ⟨_, dualAut_mul_conjAut A⟩
  · exact ⟨_, fieldAut_mul_conjAut frob A⟩

theorem not_isGF_mul {ψ₁ ψ₂ : MulAut S3} (h₁ : IsGF ψ₁) (h₂ : IsGF ψ₂) : ¬ IsGF (ψ₁ * ψ₂) := by
  set d := dualAut 3 PSL3Four.F4
  set f := fieldAut 3 PSL3Four.F4 frob
  have hdf : d * f = f * d := dualAut_mul_fieldAut frob
  have key : ∀ (A₁ A₂ A₃ : GL (Fin 3) PSL3Four.F4) (e₁ e₂ e₃ : MulAut S3),
      (e₁ = d ∨ e₁ = f) → (e₂ = d ∨ e₂ = f) → (e₃ = d ∨ e₃ = f) →
      conjAut 3 PSL3Four.F4 A₃ * e₃ ≠
        conjAut 3 PSL3Four.F4 A₁ * e₁ * (conjAut 3 PSL3Four.F4 A₂ * e₂) := by
    intro A₁ A₂ A₃ e₁ e₂ e₃ h₁ h₂ h₃ heq
    obtain ⟨A₂', hA₂'⟩ := swap_conj h₁ A₂
    have h4 : conjAut 3 PSL3Four.F4 A₃ * e₃ =
        conjAut 3 PSL3Four.F4 A₁ * conjAut 3 PSL3Four.F4 A₂' * (e₁ * e₂) := by
      rw [heq, mul_assoc (conjAut 3 PSL3Four.F4 A₁), ← mul_assoc e₁, hA₂']
      group
    have hmem : e₃ * (e₁ * e₂)⁻¹ ∈ linearAutGroup 3 PSL3Four.F4 := by
      have e5 : e₃ * (e₁ * e₂)⁻¹ = (conjAut 3 PSL3Four.F4 A₃)⁻¹ *
          (conjAut 3 PSL3Four.F4 A₁ * conjAut 3 PSL3Four.F4 A₂') := by
        rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, h4, mul_inv_cancel_right]
      rw [e5]
      exact mul_mem (inv_mem (conjAut_mem_linearAutGroup A₃))
        (mul_mem (conjAut_mem_linearAutGroup A₁) (conjAut_mem_linearAutGroup A₂'))
    rcases reduce_df dual_sq field_sq hdf h₁ h₂ h₃ with h | h
    · exact dual_not_mem (h ▸ hmem)
    · exact field_not_mem (h ▸ hmem)
  rintro ⟨A₃, h₃⟩
  obtain ⟨A₁, h₁⟩ := h₁
  obtain ⟨A₂, h₂⟩ := h₂
  have pick : ∀ {ψ : MulAut S3} {A : GL (Fin 3) PSL3Four.F4},
      (ψ = conjAut 3 PSL3Four.F4 A * d ∨ ψ = conjAut 3 PSL3Four.F4 A * f) →
        ∃ e, (e = d ∨ e = f) ∧ ψ = conjAut 3 PSL3Four.F4 A * e := by
    rintro ψ A (h | h)
    · exact ⟨d, Or.inl rfl, h⟩
    · exact ⟨f, Or.inr rfl, h⟩
  obtain ⟨e₁, he₁, rfl⟩ := pick h₁
  obtain ⟨e₂, he₂, rfl⟩ := pick h₂
  obtain ⟨e₃, he₃, h₃'⟩ := pick h₃
  exact key A₁ A₂ A₃ e₁ e₂ e₃ he₁ he₂ he₃ h₃'.symm

@[expose] def resL
    (γ : MulAut Pv)
    (hL : ∀ x : Pv, ((γ x : Pv) : Equiv.Perm (Fin N)) ∈ onL ↔ (x : Equiv.Perm (Fin N)) ∈ onL)
    (a : onL) : onL :=
  ⟨γ ⟨a, onM_le (onL_le_M a.2)⟩, (hL _).2 a.2⟩

theorem exists_isGF
    {γ : MulAut Pv}
    (hγ : γ ∉ (MulAut.conj : Pv →* MulAut Pv).range) (hz : γ zP = zP) :
    ∃ hL : ∀ x : Pv, ((γ x : Pv) : Equiv.Perm (Fin N)) ∈ onL ↔ (x : Equiv.Perm (Fin N)) ∈ onL,
      ∃ ψ : MulAut S3, IsGF ψ ∧ ∀ a : onL, lToS (resL γ hL a) = ψ (lToS a) := by
  obtain ⟨-, -, h⟩ := ctuc_on_outer_local_quotient_is_graph_or_field
  obtain ⟨-, hL, -, A, hA⟩ := h γ hγ hz
  refine ⟨hL, ?_⟩
  rcases hA with hA | hA
  · exact ⟨_, ⟨A, Or.inl rfl⟩, fun a => hA a (resL γ hL a) rfl⟩
  · exact ⟨_, ⟨A, Or.inr rfl⟩, fun a => hA a (resL γ hL a) rfl⟩

theorem outer_mul_outer_inner
    {γ₁ γ₂ : MulAut Pv}
    (h₁ : γ₁ ∉ (MulAut.conj : Pv →* MulAut Pv).range)
    (h₂ : γ₂ ∉ (MulAut.conj : Pv →* MulAut Pv).range) (hz₁ : γ₁ zP = zP) (hz₂ : γ₂ zP = zP) :
    γ₁ * γ₂ ∈ (MulAut.conj : Pv →* MulAut Pv).range := by
  by_contra h₃
  obtain ⟨-, hsurj, -⟩ := ctuc_on_outer_local_quotient_is_graph_or_field
  obtain ⟨hL₁, ψ₁, hψ₁, e₁⟩ := exists_isGF h₁ hz₁
  obtain ⟨hL₂, ψ₂, hψ₂, e₂⟩ := exists_isGF h₂ hz₂
  obtain ⟨hL₃, ψ₃, hψ₃, e₃⟩ := exists_isGF h₃ (by rw [MulAut.mul_apply, hz₂, hz₁])
  have hcomp : ∀ a : onL, resL (γ₁ * γ₂) hL₃ a = resL γ₁ hL₁ (resL γ₂ hL₂ a) := fun a =>
    Subtype.ext rfl
  have hψ : ψ₃ = ψ₁ * ψ₂ := by
    refine MulEquiv.ext fun s => ?_
    obtain ⟨a, rfl⟩ := hsurj s
    rw [← e₃, hcomp, e₁, e₂]
    rfl
  exact not_isGF_mul hψ₁ hψ₂ (hψ ▸ hψ₃)

theorem outer_fix_eq
    {α : MulAut Pv} (hα : α ∉ (MulAut.conj : Pv →* MulAut Pv).range) (hz : α zP = zP) :
    ∃ m : Pv, m * zP = zP * m ∧ α = MulAut.conj m * sigmaPv := by
  obtain ⟨m, hm⟩ := outer_mul_outer_inner hα sigmaPv_not_inner hz sigmaPv_zP
  refine ⟨m, ?_, ?_⟩
  · have h := congrArg (fun φ : MulAut Pv => φ zP) hm
    simp only [MulAut.conj_apply, MulAut.mul_apply, sigmaPv_zP, hz] at h
    calc m * zP = m * zP * m⁻¹ * m := by group
      _ = zP * m := by rw [h]
  · calc α = α * (sigmaPv * sigmaPv) := by rw [sigmaPv_sq, mul_one]
      _ = MulAut.conj m * sigmaPv := by rw [← mul_assoc, hm]

end CFSG.ComponentClassification.SolMax.ONOut
