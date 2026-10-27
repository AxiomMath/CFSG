module

public import CFSG.LargeExtraspecial.DW2ModSec
public import CFSG.LargeExtraspecial.DW2ModSixA
public import CFSG.LargeExtraspecial.DW2ModTv

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Module Submodule
open CFSG.ComponentClassification.OutcomeLocal (IsF2Transvection tv tv_apply tv_ext
  isF2Transvection_iff exists_apply_eq_one tv_mul_tv_center tv_mul_tv_axis)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Y : Subgroup (V ≃ₗ[ZMod 2] V)} {D : Set (V ≃ₗ[ZMod 2] V)} {A B C : Submodule (ZMod 2) V}
  (hB : IsInv Y B) (hC : IsInv Y C) (hAB : A ≤ B) (hBC : B ≤ C)

omit [FiniteDimensional (ZMod 2) V] in
theorem secHom_mk' (y : Y) {c : V} (hc : c ∈ C) :
    ((secHom B C Y hB hC y : LinearMap.GeneralLinearGroup (ZMod 2) (Sec B C)) :
      Sec B C →ₗ[ZMod 2] Sec B C) (secMk B C ⟨c, hc⟩) =
      secMk B C ⟨(y : V ≃ₗ[ZMod 2] V) c, hC y y.2 c hc⟩ :=
  secHom_apply_mk hB hC y ⟨c, hc⟩

include hAB hBC in
theorem exists_lift {y : Y} (hrk : secRank (y : V ≃ₗ[ZMod 2] V) A C ≤ 1)
    {φ : Dual (ZMod 2) (Sec B C)} {c : Sec B C} (hφc : φ c = 0) (hφ : φ ≠ 0) (hc0 : c ≠ 0)
    (hy : secHom B C Y hB hC y = tv φ c hφc) :
    ∃ a, ∃ ha : a ∈ C, secMk B C ⟨a, ha⟩ = c ∧
      ∀ v (hv : v ∈ C), (y : V ≃ₗ[ZMod 2] V) v - v - φ (secMk B C ⟨v, hv⟩) • a ∈ A := by
  obtain ⟨x, hx⟩ := exists_apply_eq_one hφ
  obtain ⟨⟨v₀, hv₀⟩, rfl⟩ := secMk_surjective B C x
  set a := (y : V ≃ₗ[ZMod 2] V) v₀ - v₀ with ha_def
  have haC : a ∈ C := sub_mem (hC y y.2 v₀ hv₀) hv₀
  have hπ : ∀ v (hv : v ∈ C), secMk B C ⟨(y : V ≃ₗ[ZMod 2] V) v - v,
      sub_mem (hC y y.2 v hv) hv⟩ = φ (secMk B C ⟨v, hv⟩) • c := by
    intro v hv
    have h1 := secHom_mk' hB hC y hv
    rw [hy, tv_apply] at h1
    have e : (⟨(y : V ≃ₗ[ZMod 2] V) v - v, sub_mem (hC y y.2 v hv) hv⟩ : C) =
        ⟨(y : V ≃ₗ[ZMod 2] V) v, hC y y.2 v hv⟩ - ⟨v, hv⟩ := rfl
    rw [e, map_sub, ← h1]
    abel
  have hac : secMk B C ⟨a, haC⟩ = c := by
    rw [hπ v₀ hv₀, hx, one_smul]
  have haA : a ∉ A := fun h => hc0 (by rw [← hac]; exact secMk_eq_zero_iff.mpr (hAB h))
  have hspan : ∀ v ∈ C, (y : V ≃ₗ[ZMod 2] V) v - v ∈ A ⊔ (ZMod 2 ∙ a) := by
    intro v hv
    have hle : (C.map ((y : V →ₗ[ZMod 2] V) - 1) ⊔ A) = A ⊔ (ZMod 2 ∙ a) := by
      refine (Submodule.eq_of_le_of_finrank_le (sup_le le_sup_right ?_) ?_).symm
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact Submodule.mem_sup_left ⟨v₀, hv₀, by rw [sub_one_apply]⟩
      · have h1 : finrank (ZMod 2) ↥(C.map ((y : V →ₗ[ZMod 2] V) - 1) ⊔ A) ≤
            finrank (ZMod 2) A + 1 := by
          unfold secRank at hrk
          omega
        have h2 : finrank (ZMod 2) (A ⊔ ZMod 2 ∙ a : Submodule (ZMod 2) V) =
            finrank (ZMod 2) A + 1 := finrank_sup_span_singleton haA
        omega
    have : (y : V ≃ₗ[ZMod 2] V) v - v ∈ C.map ((y : V →ₗ[ZMod 2] V) - 1) ⊔ A :=
      Submodule.mem_sup_left ⟨v, hv, by rw [sub_one_apply]⟩
    rwa [hle] at this
  refine ⟨a, haC, hac, fun v hv => ?_⟩
  obtain ⟨α, hα, b, hb, hαb⟩ := Submodule.mem_sup.mp (hspan v hv)
  obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hb
  have hμ : μ = φ (secMk B C ⟨v, hv⟩) := by
    have h1 := hπ v hv
    have e : (⟨(y : V ≃ₗ[ZMod 2] V) v - v, sub_mem (hC y y.2 v hv) hv⟩ : C) =
        ⟨α, (hAB.trans hBC) hα⟩ + μ • ⟨a, haC⟩ := Subtype.ext hαb.symm
    rw [e, map_add, map_smul, hac, secMk_eq_zero_iff.mpr (hAB hα), zero_add] at h1
    exact smul_left_injective (ZMod 2) hc0 h1
  rw [← hαb, ← hμ, add_sub_cancel_right]
  exact hα

omit [FiniteDimensional (ZMod 2) V] in
include hAB in
theorem not_mem_of_lift {a : V} (ha : a ∈ C) {c : Sec B C} (hc0 : c ≠ 0)
    (hac : secMk B C ⟨a, ha⟩ = c) : a ∉ A :=
  fun h => hc0 (by rw [← hac]; exact secMk_eq_zero_iff.mpr (hAB h))

theorem finrank_sup_pair {a a' : V} (ha : a ∉ A) (ha' : a' ∉ A) (haa' : a - a' ∉ A) :
    finrank (ZMod 2) (A ⊔ (ZMod 2 ∙ a) ⊔ (ZMod 2 ∙ a') : Submodule (ZMod 2) V) =
      finrank (ZMod 2) A + 2 := by
  have h1 : finrank (ZMod 2) (A ⊔ ZMod 2 ∙ a : Submodule (ZMod 2) V) = finrank (ZMod 2) A + 1 :=
    finrank_sup_span_singleton ha
  have ha'' : a' ∉ A ⊔ ZMod 2 ∙ a := by
    intro h
    obtain ⟨α, hα, b, hb, hαb⟩ := Submodule.mem_sup.mp h
    obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hb
    rcases zmod2_cases μ with rfl | rfl
    · rw [zero_smul, add_zero] at hαb
      exact ha' (hαb ▸ hα)
    · rw [one_smul] at hαb
      apply haa'
      have : a - a' = -α := by rw [← hαb]; abel
      rw [this]
      exact neg_mem hα
  rw [finrank_sup_span_singleton ha'', h1]

section Main

variable (hinj : Function.Injective (secHom B C Y hB hC))
  (hrk : ∀ y : Y, (y : V ≃ₗ[ZMod 2] V) ∈ D → secRank (y : V ≃ₗ[ZMod 2] V) A C ≤ 1)
  (hcl : ∀ y : Y, IsF2Transvection (secHom B C Y hB hC y) → (y : V ≃ₗ[ZMod 2] V) ∈ D)

omit [FiniteDimensional (ZMod 2) V] in
theorem apply_secMk_of_tv {y' : Y} {φ φ' : Dual (ZMod 2) (Sec B C)} {c' : Sec B C}
    (hφ'c' : φ' c' = 0) (hy' : secHom B C Y hB hC y' = tv φ' c' hφ'c') (hφc' : φ c' = 0) {v : V}
    (hv : v ∈ C) : φ (secMk B C ⟨(y' : V ≃ₗ[ZMod 2] V) v, hC y' y'.2 v hv⟩) =
      φ (secMk B C ⟨v, hv⟩) := by
  rw [← secHom_mk' hB hC y' hv, hy', tv_apply, map_add, map_smul, hφc', smul_zero, add_zero]

include hAB hinj hrk hcl in
theorem sub_mem_of_center_eq {y y' : Y}
    {φ φ' : Dual (ZMod 2) (Sec B C)} {c : Sec B C} (hφc : φ c = 0) (hφ'c : φ' c = 0)
    (hφ : φ ≠ 0) (hφ' : φ' ≠ 0) (hc0 : c ≠ 0) (hy : secHom B C Y hB hC y = tv φ c hφc)
    (hy' : secHom B C Y hB hC y' = tv φ' c hφ'c) {a a' : V} (ha : a ∈ C) (ha' : a' ∈ C)
    (hac : secMk B C ⟨a, ha⟩ = c) (ha'c : secMk B C ⟨a', ha'⟩ = c)
    (hka : ∀ v (hv : v ∈ C), (y : V ≃ₗ[ZMod 2] V) v - v - φ (secMk B C ⟨v, hv⟩) • a ∈ A)
    (hka' : ∀ v (hv : v ∈ C), (y' : V ≃ₗ[ZMod 2] V) v - v - φ' (secMk B C ⟨v, hv⟩) • a' ∈ A) :
    a - a' ∈ A := by
  by_cases hφφ : φ = φ'
  ·
    subst hφφ
    have hyy : y = y' := hinj (hy.trans hy'.symm)
    subst hyy
    obtain ⟨x, hx⟩ := exists_apply_eq_one hφ
    obtain ⟨⟨v, hv⟩, rfl⟩ := secMk_surjective B C x
    have h1 := hka v hv
    have h2 := hka' v hv
    rw [hx, one_smul] at h1 h2
    have : a - a' = ((y : V ≃ₗ[ZMod 2] V) v - v - a') - ((y : V ≃ₗ[ZMod 2] V) v - v - a) := by
      abel
    rw [this]
    exact sub_mem h2 h1
  by_contra haa
  have h1 : φ + φ' ≠ 0 := fun h => hφφ (by
    have := congrArg (· + φ') h
    simpa [add_assoc, add_self_zmod2] using this)
  have hyy' : secHom B C Y hB hC (y * y') = tv (φ + φ') c (by
      rw [LinearMap.add_apply, hφc, hφ'c, add_zero]) := by
    rw [map_mul, hy, hy', tv_mul_tv_center]
  have hD : ((y * y' : Y) : V ≃ₗ[ZMod 2] V) ∈ D := by
    refine hcl _ ?_
    rw [hyy']
    exact (isF2Transvection_iff _).mpr ⟨_, _, _, h1, hc0, rfl⟩
  have hrk2 := hrk _ hD
  have hkey : ∀ v (hv : v ∈ C), ((y * y' : Y) : V ≃ₗ[ZMod 2] V) v - v -
      (φ (secMk B C ⟨v, hv⟩) • a + φ' (secMk B C ⟨v, hv⟩) • a') ∈ A := by
    intro v hv
    have k1 := hka _ (hC y' y'.2 v hv)
    have k2 := hka' v hv
    rw [apply_secMk_of_tv hB hC hφ'c hy' hφc hv] at k1
    have e : ((y * y' : Y) : V ≃ₗ[ZMod 2] V) v - v - (φ (secMk B C ⟨v, hv⟩) • a +
        φ' (secMk B C ⟨v, hv⟩) • a') = ((y : V ≃ₗ[ZMod 2] V) ((y' : V ≃ₗ[ZMod 2] V) v) -
        (y' : V ≃ₗ[ZMod 2] V) v - φ (secMk B C ⟨v, hv⟩) • a) +
        ((y' : V ≃ₗ[ZMod 2] V) v - v - φ' (secMk B C ⟨v, hv⟩) • a') := by
      change (y : V ≃ₗ[ZMod 2] V) ((y' : V ≃ₗ[ZMod 2] V) v) - v - _ = _
      abel
    rw [e]
    exact add_mem k1 k2
  obtain ⟨x₁, hx₁, hx₁'⟩ := exists_apply_eq_one_apply_eq_zero hφ hφφ
  obtain ⟨x₂, hx₂, hx₂'⟩ := exists_apply_eq_one_apply_eq_zero hφ' (Ne.symm hφφ)
  obtain ⟨⟨v₁, hv₁⟩, rfl⟩ := secMk_surjective B C x₁
  obtain ⟨⟨v₂, hv₂⟩, rfl⟩ := secMk_surjective B C x₂
  have hmem : ∀ v ∈ C, ((y * y' : Y) : V ≃ₗ[ZMod 2] V) v - v ∈
      C.map ((((y * y' : Y) : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) - 1) ⊔ A :=
    fun v hv => Submodule.mem_sup_left ⟨v, hv, by rw [sub_one_apply]⟩
  have hA' : A ≤ C.map ((((y * y' : Y) : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) - 1) ⊔ A :=
    le_sup_right
  have hamem : a ∈ C.map ((((y * y' : Y) : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) - 1) ⊔ A := by
    have := hkey v₁ hv₁
    rw [hx₁, hx₁', one_smul, zero_smul, add_zero] at this
    have e : a = (((y * y' : Y) : V ≃ₗ[ZMod 2] V) v₁ - v₁) -
        (((y * y' : Y) : V ≃ₗ[ZMod 2] V) v₁ - v₁ - a) := by abel
    rw [e]
    exact sub_mem (hmem v₁ hv₁) (hA' this)
  have ha'mem : a' ∈ C.map ((((y * y' : Y) : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) - 1) ⊔ A := by
    have := hkey v₂ hv₂
    rw [hx₂, hx₂', one_smul, zero_smul, zero_add] at this
    have e : a' = (((y * y' : Y) : V ≃ₗ[ZMod 2] V) v₂ - v₂) -
        (((y * y' : Y) : V ≃ₗ[ZMod 2] V) v₂ - v₂ - a') := by abel
    rw [e]
    exact sub_mem (hmem v₂ hv₂) (hA' this)
  have hle : A ⊔ (ZMod 2 ∙ a) ⊔ (ZMod 2 ∙ a') ≤
      C.map ((((y * y' : Y) : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) - 1) ⊔ A := by
    refine sup_le (sup_le hA' ?_) ?_
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hamem
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact ha'mem
  have h2 := Submodule.finrank_mono hle
  rw [finrank_sup_pair (not_mem_of_lift hAB ha hc0 hac) (not_mem_of_lift hAB ha' hc0 ha'c) haa]
    at h2
  unfold secRank at hrk2
  omega

omit [FiniteDimensional (ZMod 2) V] in
include hcl in
theorem lift_mul_of_axis_eq {y y' : Y} {φ : Dual (ZMod 2) (Sec B C)} {c c' : Sec B C}
    (hφc : φ c = 0) (hφc' : φ c' = 0) (hφ : φ ≠ 0) (hcc' : c ≠ c')
    (hy : secHom B C Y hB hC y = tv φ c hφc) (hy' : secHom B C Y hB hC y' = tv φ c' hφc')
    {a a' : V}
    (hka : ∀ v (hv : v ∈ C), (y : V ≃ₗ[ZMod 2] V) v - v - φ (secMk B C ⟨v, hv⟩) • a ∈ A)
    (hka' : ∀ v (hv : v ∈ C), (y' : V ≃ₗ[ZMod 2] V) v - v - φ (secMk B C ⟨v, hv⟩) • a' ∈ A) :
    ∃ h : φ (c + c') = 0, secHom B C Y hB hC (y * y') = tv φ (c + c') h ∧
      ((y * y' : Y) : V ≃ₗ[ZMod 2] V) ∈ D ∧
      ∀ v (hv : v ∈ C), ((y * y' : Y) : V ≃ₗ[ZMod 2] V) v - v -
        φ (secMk B C ⟨v, hv⟩) • (a + a') ∈ A := by
  have h0 : φ (c + c') = 0 := by rw [map_add, hφc, hφc', add_zero]
  have hcc0 : c + c' ≠ 0 := fun h => hcc' (by
    have := congrArg (· + c') h
    simpa [add_assoc, add_self_zmod2] using this)
  have hyy' : secHom B C Y hB hC (y * y') = tv φ (c + c') h0 := by
    rw [map_mul, hy, hy', tv_mul_tv_axis]
  have hD : ((y * y' : Y) : V ≃ₗ[ZMod 2] V) ∈ D := by
    refine hcl _ ?_
    rw [hyy']
    exact (isF2Transvection_iff _).mpr ⟨_, _, _, hφ, hcc0, rfl⟩
  refine ⟨h0, hyy', hD, fun v hv => ?_⟩
  have k1 := hka _ (hC y' y'.2 v hv)
  have k2 := hka' v hv
  rw [apply_secMk_of_tv hB hC hφc' hy' hφc' hv] at k1
  have e : ((y * y' : Y) : V ≃ₗ[ZMod 2] V) v - v - φ (secMk B C ⟨v, hv⟩) • (a + a') =
      ((y : V ≃ₗ[ZMod 2] V) ((y' : V ≃ₗ[ZMod 2] V) v) - (y' : V ≃ₗ[ZMod 2] V) v -
        φ (secMk B C ⟨v, hv⟩) • a) +
        ((y' : V ≃ₗ[ZMod 2] V) v - v - φ (secMk B C ⟨v, hv⟩) • a') := by
    change (y : V ≃ₗ[ZMod 2] V) ((y' : V ≃ₗ[ZMod 2] V) v) - v - _ = _
    rw [smul_add]
    abel
  rw [e]
  exact add_mem k1 k2

include hAB hBC hinj hrk hcl in
theorem finrank_commSub_sup_le (hgen : Y = Subgroup.closure D)
    (htv : ∀ y : Y, (y : V ≃ₗ[ZMod 2] V) ∈ D → IsF2Transvection (secHom B C Y hB hC y))
    (hsurj : ∀ τ : LinearMap.GeneralLinearGroup (ZMod 2) (Sec B C), IsF2Transvection τ →
      ∃ y : Y, (y : V ≃ₗ[ZMod 2] V) ∈ D ∧ secHom B C Y hB hC y = τ)
    (hdim : 3 ≤ finrank (ZMod 2) (Sec B C)) :
    finrank (ZMod 2) (commSub Y C ⊔ A : Submodule (ZMod 2) V) ≤
      finrank (ZMod 2) A + finrank (ZMod 2) (Sec B C) := by
  classical
  have hax : ∀ c c' : Sec B C, ∃ φ : Dual (ZMod 2) (Sec B C), φ ≠ 0 ∧ φ c = 0 ∧ φ c' = 0 := by
    intro c c'
    set Wc : Subspace (ZMod 2) (Sec B C) := Submodule.span (ZMod 2) {c, c'}
    have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq Wc
    have h2 : finrank (ZMod 2) Wc ≤ 2 := by
      have : finrank (ZMod 2) Wc ≤ ({c, c'} : Set (Sec B C)).toFinset.card :=
        finrank_span_le_card _
      have h3 : ({c, c'} : Set (Sec B C)).toFinset.card ≤ 2 := by
        rw [Set.toFinset_insert, Set.toFinset_singleton]
        exact Finset.card_insert_le _ _
      omega
    have hne : Wc.dualAnnihilator ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at h1
      omega
    obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨φ, hφ0, ?_, ?_⟩
    · exact (Submodule.mem_dualAnnihilator φ).mp hφ c (Submodule.subset_span (by simp))
    · exact (Submodule.mem_dualAnnihilator φ).mp hφ c' (Submodule.subset_span (by simp))
  have hdata : ∀ c : Sec B C, c ≠ 0 → ∃ (φ : Dual (ZMod 2) (Sec B C)) (hφc : φ c = 0) (y : Y),
      φ ≠ 0 ∧ (y : V ≃ₗ[ZMod 2] V) ∈ D ∧ secHom B C Y hB hC y = tv φ c hφc ∧
      ∃ a, ∃ ha : a ∈ C, secMk B C ⟨a, ha⟩ = c ∧
        ∀ v (hv : v ∈ C), (y : V ≃ₗ[ZMod 2] V) v - v - φ (secMk B C ⟨v, hv⟩) • a ∈ A := by
    intro c hc0
    obtain ⟨φ, hφ0, hφc, -⟩ := hax c c
    obtain ⟨y, hyD, hy⟩ := hsurj _ ((isF2Transvection_iff _).mpr ⟨φ, c, hφc, hφ0, hc0, rfl⟩)
    exact ⟨φ, hφc, y, hφ0, hyD, hy, exists_lift hB hC hAB hBC (hrk y hyD) hφc hφ0 hc0 hy⟩
  choose φF hφF yF hφF0 hyFD hyF aF haF haFc hkF using hdata
  have huniq : ∀ (c : Sec B C) (hc0 : c ≠ 0) (φ : Dual (ZMod 2) (Sec B C)) (hφc : φ c = 0)
      (y : Y), φ ≠ 0 → (y : V ≃ₗ[ZMod 2] V) ∈ D → secHom B C Y hB hC y = tv φ c hφc →
      ∀ a (ha : a ∈ C), secMk B C ⟨a, ha⟩ = c →
        (∀ v (hv : v ∈ C), (y : V ≃ₗ[ZMod 2] V) v - v - φ (secMk B C ⟨v, hv⟩) • a ∈ A) →
        A.mkQ a = A.mkQ (aF c hc0) := by
    intro c hc0 φ hφc y hφ0 hyD hy a ha hac hka
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact sub_mem_of_center_eq hB hC hAB hinj hrk hcl hφc (hφF c hc0) hφ0
      (hφF0 c hc0) hc0 hy (hyF c hc0) ha (haF c hc0) hac (haFc c hc0) hka (hkF c hc0)
  let Lf : Sec B C → V ⧸ A := fun c => if hc : c = 0 then 0 else A.mkQ (aF c hc)
  have hLf : ∀ c (hc0 : c ≠ 0), Lf c = A.mkQ (aF c hc0) := fun c hc0 => by
    simp only [Lf, hc0, ↓reduceDIte]
  have hadd : ∀ c c', Lf (c + c') = Lf c + Lf c' := by
    intro c c'
    by_cases hc : c = 0
    · simp [Lf, hc]
    by_cases hc' : c' = 0
    · simp [Lf, hc']
    by_cases hcc : c = c'
    · subst hcc
      rw [add_self_zmod2, add_self_zmod2]
      simp [Lf]
    have hcc0 : c + c' ≠ 0 := fun h => hcc (by
      have := congrArg (· + c') h
      simpa [add_assoc, add_self_zmod2] using this)
    obtain ⟨φ, hφ0, hφc, hφc'⟩ := hax c c'
    obtain ⟨y, hyD, hy⟩ := hsurj _ ((isF2Transvection_iff _).mpr ⟨φ, c, hφc, hφ0, hc, rfl⟩)
    obtain ⟨y', hyD', hy'⟩ := hsurj _ ((isF2Transvection_iff _).mpr ⟨φ, c', hφc', hφ0, hc', rfl⟩)
    obtain ⟨a, ha, hac, hka⟩ := exists_lift hB hC hAB hBC (hrk y hyD) hφc hφ0 hc hy
    obtain ⟨a', ha', ha'c, hka'⟩ := exists_lift hB hC hAB hBC (hrk y' hyD') hφc' hφ0 hc' hy'
    obtain ⟨h0, hyy', hD, hk⟩ := lift_mul_of_axis_eq hB hC hcl hφc hφc' hφ0 hcc hy hy' hka hka'
    have hsum : secMk B C ⟨a + a', add_mem ha ha'⟩ = c + c' := by
      rw [show (⟨a + a', add_mem ha ha'⟩ : C) = ⟨a, ha⟩ + ⟨a', ha'⟩ from rfl, map_add, hac, ha'c]
    rw [hLf _ hcc0, hLf _ hc, hLf _ hc',
      ← huniq _ hcc0 φ h0 _ hφ0 hD hyy' _ (add_mem ha ha') hsum hk,
      ← huniq _ hc φ hφc y hφ0 hyD hy a ha hac hka,
      ← huniq _ hc' φ hφc' y' hφ0 hyD' hy' a' ha' ha'c hka', map_add]
  let L : Sec B C →ₗ[ZMod 2] V ⧸ A :=
    { toFun := Lf
      map_add' := hadd
      map_smul' := fun μ c => by
        rw [RingHom.id_apply]
        rcases zmod2_cases μ with rfl | rfl
        · rw [zero_smul, zero_smul]
          simp [Lf]
        · rw [one_smul, one_smul] }
  set T := (LinearMap.range L).comap A.mkQ with hT
  have hAT : A ≤ T := fun a ha => by
    rw [hT, Submodule.mem_comap, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero A).mpr ha]
    exact zero_mem _
  have hcomm : commSub Y C ≤ T := by
    rw [commSub_le_iff]
    refine forall_sub_mem_of_forall hgen hC fun d hd v hv => ?_
    have hdY : d ∈ Y := hgen ▸ Subgroup.subset_closure hd
    obtain ⟨φ, c, hφc, hφ0, hc0, hτ⟩ := (isF2Transvection_iff _).mp (htv ⟨d, hdY⟩ hd)
    obtain ⟨a, ha, hac, hka⟩ := exists_lift hB hC hAB hBC (hrk ⟨d, hdY⟩ hd) hφc hφ0 hc0 hτ
    have haT : a ∈ T := by
      rw [hT, Submodule.mem_comap, huniq c hc0 φ hφc ⟨d, hdY⟩ hφ0 hd hτ a ha hac hka, ← hLf c hc0]
      exact ⟨c, rfl⟩
    have e : d v - v = (d v - v - φ (secMk B C ⟨v, hv⟩) • a) + φ (secMk B C ⟨v, hv⟩) • a := by
      abel
    rw [e]
    exact add_mem (hAT (hka v hv)) (Submodule.smul_mem _ _ haT)
  have hle : commSub Y C ⊔ A ≤ T := sup_le hcomm hAT
  have hTdim : finrank (ZMod 2) T = finrank (ZMod 2) A + finrank (ZMod 2) (LinearMap.range L) := by
    set ψ : T →ₗ[ZMod 2] V ⧸ A := A.mkQ ∘ₗ T.subtype
    have hr : LinearMap.range ψ = LinearMap.range L := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨t, rfl⟩
        exact t.2
      · intro x hx
        obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective A x
        exact ⟨⟨v, hx⟩, rfl⟩
    have hk : LinearMap.ker ψ = A.comap T.subtype := by
      ext t
      rw [LinearMap.mem_ker, Submodule.mem_comap]
      exact Submodule.Quotient.mk_eq_zero A
    have h1 := LinearMap.finrank_range_add_finrank_ker ψ
    rw [hr, hk, (Submodule.comapSubtypeEquivOfLe hAT).finrank_eq] at h1
    omega
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.finrank_range_le L
  omega

end Main

end CFSG.LargeExtraspecial.DW
