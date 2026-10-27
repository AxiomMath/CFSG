module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFact
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParamTorus
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandard
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

section Matrix

variable {K F : Type*} [Field K] [Field F]

theorem specialLinear_map_slConjugation {m : ℕ} (ι : K →+* F) (D : GL (Fin m) K)
    (x : SpecialLinearGroup (Fin m) K) :
    SpecialLinearGroup.map ι (slConjugation m K D x) =
      slConjugation m F (GeneralLinearGroup.map ι D) (SpecialLinearGroup.map ι x) := by
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe, LinearFlag.coe_slConjugation,
    LinearFlag.coe_slConjugation, SpecialLinearGroup.map_apply_coe, map_mul, map_mul,
    ← Matrix.GeneralLinearGroup.map_inv]
  rfl

theorem generalLinear_map_diagGL {m : ℕ} (ι : K →+* F) (c : Fin m → Kˣ) :
    GeneralLinearGroup.map ι (TauCeti.diagGL c) =
      TauCeti.diagGL (fun i => Units.map (ι : K →* F) (c i)) := by
  apply Units.ext
  ext i j
  rw [GeneralLinearGroup.map_apply, TauCeti.diagGL_coe, TauCeti.diagGL_coe]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [Matrix.diagonal_apply_ne _ hij]

end Matrix

section Embed

variable {Y : Type*} [Group Y] {K : Type*} [Field K]

theorem exists_projectiveSL_embedding_of_hom {m : ℕ} (hm : 3 ≤ m)
    (φ : SpecialLinearGroup (Fin m) K →* Y) (hne : φ.range ≠ ⊥) (hZ : center φ.range = ⊥)
    {Kc : Subgroup Y} (hDK : φ.range ≤ Kc) :
    ∃ ε : LinearFlag.projectiveSL m K →* Kc, Function.Injective ε ∧
      ε.range = φ.range.subgroupOf Kc ∧ ∀ x, (ε (LinearFlag.proj m K x) : Y) = φ x := by
  have hker : φ.ker = center (SpecialLinearGroup (Fin m) K) := by
    refine le_antisymm (LieType.CurtisTits.ker_le_center_of_isQuasisimple
      (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup hm) ?_) ?_
    · by_contra h
      push Not at h
      apply hne
      rw [eq_bot_iff]
      rintro _ ⟨x, rfl⟩
      exact (mem_bot).mpr (h x)
    · intro z hz
      have hzc : (⟨φ z, z, rfl⟩ : φ.range) ∈ center φ.range := by
        rw [mem_center_iff]
        rintro ⟨_, x, rfl⟩
        apply Subtype.ext
        change φ x * φ z = φ z * φ x
        rw [← map_mul, ← map_mul, (mem_center_iff.mp hz x)]
      rw [hZ, mem_bot] at hzc
      exact congrArg Subtype.val hzc
  have hsc : LinearFlag.scalars m K ≤ φ.ker := by
    rw [hker, LinearFlag.scalars_eq_center]
  set ε₀ := QuotientGroup.lift (LinearFlag.scalars m K) φ hsc with hε₀
  have hε₀app : ∀ x, ε₀ (LinearFlag.proj m K x) = φ x := fun x => QuotientGroup.lift_mk' _ hsc x
  have hmem : ∀ y, ε₀ y ∈ Kc := by
    intro y
    obtain ⟨x, rfl⟩ := LinearFlag.proj_surjective m K y
    rw [hε₀app]
    exact hDK ⟨x, rfl⟩
  refine ⟨ε₀.codRestrict Kc hmem, ?_, ?_, fun x => hε₀app x⟩
  · rw [injective_iff_map_eq_one]
    intro y hy
    obtain ⟨x, rfl⟩ := LinearFlag.proj_surjective m K y
    have h1 : φ x = 1 := by
      rw [← hε₀app]
      exact congrArg Subtype.val hy
    have h2 : x ∈ φ.ker := h1
    rw [hker] at h2
    rw [LinearFlag.proj_eq_one_iff, LinearFlag.scalars_eq_center]
    exact h2
  · ext ⟨k, hk⟩
    rw [mem_subgroupOf, MonoidHom.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := LinearFlag.proj_surjective m K y
      have h1 : φ x = k := by
        rw [← hε₀app]
        exact congrArg Subtype.val hy
      exact ⟨x, h1⟩
    · rintro ⟨x, hx⟩
      exact ⟨LinearFlag.proj m K x, Subtype.ext (by
        change ε₀ (LinearFlag.proj m K x) = k
        rw [hε₀app, hx])⟩

end Embed

section Torus

variable {K F : Type} [Field K] [Field F] [Finite F]

theorem proj_apply_eq_conjAut_of_odd {m : ℕ} (hm : 3 ≤ m) (ι : K →+* F) {σ : F ≃+* F}
    (hσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {E : Type*} [Group E]
    (p : E →* LinearFlag.projectiveSL m F) (hp : Function.Surjective p)
    (hpker : p.ker ≤ center E) (δ : SpecialLinearGroup (Fin m) K →* E)
    (hδ : ∀ x, p (δ x) = LinearFlag.proj m F (SpecialLinearGroup.map ι x))
    (D : GL (Fin m) K) (γ : MulAut E) (hγ : ∀ x, γ (δ x) = δ (slConjugation m K D x))
    {r : ℕ} (hr : Odd r) (hγr : γ ^ r = 1) (hDr : D ^ r = 1) (y : E) :
    p (γ y) = LinearFlag.conjAut m F (GeneralLinearGroup.map ι D) (p y) := by
  have hker : p.ker = center E :=
    LinearPilot.ker_eq_center_of_surjective_of_center_eq_bot hp hpker
      (CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot hm)
  set γb := LinearPilot.descendCenterMulAut p hp hker γ with hγb
  set β := LinearFlag.conjAut m F (GeneralLinearGroup.map ι D) with hβ
  have hagree : ∀ x : SpecialLinearGroup (Fin m) K,
      γb (LinearFlag.proj m F (SpecialLinearGroup.map ι x)) =
        β (LinearFlag.proj m F (SpecialLinearGroup.map ι x)) := by
    intro x
    conv_lhs => rw [← hδ x]
    rw [hγb, LinearPilot.descendCenterMulAut_apply, hγ, hδ, specialLinear_map_slConjugation, hβ,
      LinearFlag.conjAut_proj]
  have hk : ∀ x, x ∈ ι.fieldRange ↔ σ x = x := fun x => by
    rw [RingHom.mem_fieldRange, hfix x, Set.mem_range]
  have hmem : β⁻¹ * γb ∈ zpowers (LinearFlag.fieldAut m F σ) := by
    rw [← CFSG.RankThree.PartOne.fixingSubgroup_range_linearSubfieldInclusion hk hm,
      mem_fixingSubgroup_iff]
    intro z hz
    obtain ⟨x, rfl⟩ := LinearPilot.exists_proj_map_eq_of_mem_range ι hz
    rw [MulAut.smul_def, MulAut.mul_apply, hagree x, ← MulAut.mul_apply, inv_mul_cancel,
      MulAut.one_apply]
  set β' := β⁻¹ * γb with hβ'
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hmem
  have hf2 : LinearFlag.fieldAut m F σ ^ 2 = 1 := by rw [sq, ← map_mul, hσ, map_one]
  have hβ'2 : β' ^ 2 = 1 := by
    rw [← hj, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hf2,
      _root_.one_zpow]
  have hσD : GeneralLinearGroup.map (σ : F →+* F) (GeneralLinearGroup.map ι D) =
      GeneralLinearGroup.map ι D := by
    apply Units.ext
    ext a b
    rw [GeneralLinearGroup.map_apply, GeneralLinearGroup.map_apply]
    exact (hfix _).2 ⟨_, rfl⟩
  have hcomm : Commute β (LinearFlag.fieldAut m F σ) := by
    have h := LinearFlag.fieldAut_mul_conjAut σ (GeneralLinearGroup.map ι D)
    rw [hσD] at h
    exact h.symm
  have hcomm' : Commute β β' := hj ▸ hcomm.zpow_right j
  have hγbr : γb ^ r = 1 := by rw [hγb, ← map_pow, hγr, map_one]
  have hβr : β ^ r = 1 := by rw [hβ, ← map_pow, ← map_pow, hDr, map_one, map_one]
  have hγβ : γb = β * β' := by rw [hβ', mul_inv_cancel_left]
  have hβ'r : β' ^ r = 1 := by
    have h := hcomm'.mul_pow r
    rw [← hγβ, hγbr, hβr, one_mul] at h
    exact h.symm
  have hβ'1 : β' = 1 := by
    obtain ⟨s, hs⟩ := hr
    rw [hs, pow_succ, pow_mul, hβ'2, one_pow, one_mul] at hβ'r
    exact hβ'r
  rw [← LinearPilot.descendCenterMulAut_apply p hp hker γ y, ← hγb, hγβ, hβ'1, mul_one]

end Torus

section Param

variable {G : Type*} [Group G] {K F : Type} [Field K] [Finite K] [CharP K 2] [Field F] [Finite F]

theorem exists_slParam_of_proj {m : ℕ} (hm : 3 ≤ m) (hF : 5 ≤ Nat.card F) (ι : K →+* F)
    {σ : F ≃+* F} (hσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    {E : Subgroup G} (hEperf : ⁅E, E⁆ = E) (p : E →* LinearFlag.projectiveSL m F)
    (hp : Function.Surjective p) (hpker : p.ker ≤ center E)
    (δ : SpecialLinearGroup (Fin m) K →* G) (hδE : ∀ x, δ x ∈ E)
    (h1 : ∀ x, p ⟨δ x, hδE x⟩ = LinearFlag.proj m F (SpecialLinearGroup.map ι x))
    {t : G} (ht : t ∈ normalizer (E : Set G))
    (h3 : ∀ y, p (E.normalizerMonoidHom ⟨t, ht⟩ y) = LinearFlag.fieldAut m F σ (p y))
    (g : (Fin m → Kˣ) → G) (hgN : ∀ c, g c ∈ normalizer (E : Set G))
    (hgδ : ∀ c x, g c * δ x * (g c)⁻¹ = δ (slConjugation m K (TauCeti.diagGL c) x))
    (hgr : ∀ c, g c ^ Nat.card Kˣ = 1) :
    ∃ Φ : SpecialLinearGroup (Fin m) F →* G, Φ.range = E ∧
      Φ.ker ≤ center (SpecialLinearGroup (Fin m) F) ∧
      (∀ x, Φ (SpecialLinearGroup.map ι x) = δ x) ∧
      (∀ c x, Φ (slConjugation m F (TauCeti.diagGL (liftParam ι c)) x) = g c * Φ x * (g c)⁻¹) ∧
      (∀ x, t * Φ x * t⁻¹ = Φ (SpecialLinearGroup.map σ.toRingHom x)) := by
  have : Group.IsPerfect E := Subgroup.isPerfect_iff.mpr hEperf
  have : Group.IsPerfect (SpecialLinearGroup (Fin m) K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le hm
  have : Group.IsPerfect (SpecialLinearGroup (Fin m) F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le hm
  obtain ⟨Φ₀, hΦ₀, hsurj, hker⟩ :=
    LinearPilot.exists_surjective_lift_of_ker_le_center hm hF hp hpker
  set δ' : SpecialLinearGroup (Fin m) K →* E := δ.codRestrict E hδE with hδ'
  have h1' : ∀ x, p (δ' x) = LinearFlag.proj m F (SpecialLinearGroup.map ι x) := h1
  have hN1 : Φ₀.comp (SpecialLinearGroup.map ι) = δ' :=
    LinearPilot.eq_of_comp_eq_of_ker_le_center hpker fun x => by
      rw [MonoidHom.comp_apply, hΦ₀]
      exact (h1' x).symm
  have hN3 : (E.normalizerMonoidHom ⟨t, ht⟩).toMonoidHom.comp Φ₀ =
      Φ₀.comp (SpecialLinearGroup.map σ.toRingHom) :=
    LinearPilot.eq_of_comp_eq_of_ker_le_center hpker fun x => by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h3, hΦ₀, hΦ₀,
        LinearFlag.fieldAut_proj]
  have hrodd : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units]
    exact LinearPilot.odd_natCard_sub_one
  have hN2 : ∀ c, (E.normalizerMonoidHom ⟨g c, hgN c⟩).toMonoidHom.comp Φ₀ =
      Φ₀.comp (slConjugation m F (TauCeti.diagGL (liftParam ι c))).toMonoidHom := fun c => by
    have hγ : ∀ x, E.normalizerMonoidHom ⟨g c, hgN c⟩ (δ' x) =
        δ' (slConjugation m K (TauCeti.diagGL c) x) := fun x => Subtype.ext (hgδ c x)
    have hγr : (E.normalizerMonoidHom ⟨g c, hgN c⟩) ^ Nat.card Kˣ = 1 := by
      rw [← map_pow]
      have : (⟨g c, hgN c⟩ : normalizer (E : Set G)) ^ Nat.card Kˣ = 1 :=
        Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hgr c)
      rw [this, map_one]
    have hDr : (TauCeti.diagGL c) ^ Nat.card Kˣ = 1 := by
      rw [← map_pow]
      have : c ^ Nat.card Kˣ = 1 := funext fun i => pow_card_eq_one'
      rw [this, map_one]
    refine LinearPilot.eq_of_comp_eq_of_ker_le_center hpker fun x => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.coe_toMonoidHom, proj_apply_eq_conjAut_of_odd hm ι hσ hfix p hp hpker δ' h1'
        (TauCeti.diagGL c) _ hγ hrodd hγr hDr, hΦ₀, hΦ₀, generalLinear_map_diagGL,
      LinearFlag.conjAut_proj]
    rfl
  refine ⟨E.subtype.comp Φ₀, ?_, ?_, fun x => ?_, fun c x => ?_, fun x => ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hsurj, ← MonoidHom.range_eq_map,
      range_subtype]
  · intro x hx
    exact hker (Subtype.ext hx)
  · exact congrArg Subtype.val (DFunLike.congr_fun hN1 x)
  · exact (congrArg Subtype.val (DFunLike.congr_fun (hN2 c) x)).symm
  · exact congrArg Subtype.val (DFunLike.congr_fun hN3 x)

end Param

end CFSG.SeitzReduction.SymplecticPilot
