module

public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.LieType.Ree.LargeReeInvolutionIntermediateOddCore
public import CFSG.LieType.Ree.LargeReeInvolutionComponentFree
public import CFSG.Sporadic.Schreier.TitsInter
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocleBasic
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalSocleSelector
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalComponentFree
public import CFSG.Sporadic.Schreier.TitsComponent

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Subgroup CFSG.Blueprint CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem le_ker_of_isPerfect_of_isSolvable {G Q : Type*} [Group G] [Group Q]
    [Group.IsSolvable Q] (K : Subgroup G) [Group.IsPerfect K] (f : G →* Q) : K ≤ f.ker := by
  have : Group.IsPerfect (f.comp K.subtype).range := Group.IsPerfect.range _
  have : Subsingleton (f.comp K.subtype).range := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isSolvable (f.comp K.subtype).range inferInstance
  intro k hk
  have h1 : (⟨f k, ⟨k, hk⟩, rfl⟩ : (f.comp K.subtype).range) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val h1

theorem socle_action_facts {A : Type} [Group A] {W : Subgroup A} [W.Normal] [IsSimpleGroup W]
    (hWnab : ∃ x y : W, x * y ≠ y * x) (hCW : centralizer (W : Set A) = ⊥) {a : A}
    (haW : a ∈ W) (ha : orderOf a = 2) {T : Type} [Group T] (φ : W ≃* T) :
    ∃ ρ : A →* MulAut T, Function.Injective ρ ∧
      (∀ (x : A) (w : W) (hw : x * w * x⁻¹ ∈ W), ρ x (φ w) = φ ⟨_, hw⟩) ∧
      (∀ ρ' : A →* MulAut T,
        (∀ (x : A) (w : W) (hw : x * w * x⁻¹ ∈ W), ρ' x (φ w) = φ ⟨_, hw⟩) → ρ' = ρ) ∧
      W.map ρ = OuterAutomorphisms.inner T ∧ orderOf (φ ⟨a, haW⟩) = 2 ∧
      ρ a = MulAut.conj (φ ⟨a, haW⟩) ∧
      (centralizer ({a} : Set A)).map ρ = ρ.range ⊓ centralizer {MulAut.conj (φ ⟨a, haW⟩)} ∧
      ((centralizer ({a} : Set A)).subgroupOf W).map φ.toMonoidHom =
        centralizer {φ ⟨a, haW⟩} ∧
      (W ⊓ centralizer ({a} : Set A)).map ρ = (centralizer {φ ⟨a, haW⟩}).map MulAut.conj ∧
      ((QuotientGroup.mk' (OuterAutomorphisms.inner T)).comp ρ).ker = W := by
  have hZ : center T = ⊥ := by
    have : IsSimpleGroup T := φ.symm.isSimpleGroup
    refine OutcomeLocal.center_eq_bot_of_isSimpleGroup ?_
    obtain ⟨x, y, hxy⟩ := hWnab
    exact ⟨φ x, φ y, fun h => hxy (φ.injective (by rw [map_mul, map_mul, h]))⟩
  obtain ⟨ρ, hinj, hρW, huniq, hρapp⟩ := OutcomeLocal.socle_extension hCW φ hZ
  have happ : ∀ (x : A) (w : W) (hw : x * w * x⁻¹ ∈ W), ρ x (φ w) = φ ⟨_, hw⟩ :=
    fun x w _ => (hρapp x w).trans (congrArg φ (Subtype.ext rfl))
  have hWρ : W.map ρ = (MulAut.conj : T →* MulAut T).range := OutcomeLocal.map_eq_range_conj φ hρW
  have hz2 : orderOf (φ ⟨a, haW⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, ← ha]
    exact (orderOf_injective W.subtype W.subtype_injective ⟨a, haW⟩).symm
  have hρa : ρ a = MulAut.conj (φ ⟨a, haW⟩) := hρW ⟨a, haW⟩
  have hφC : ((centralizer ({a} : Set A)).subgroupOf W).map φ.toMonoidHom =
      centralizer {φ ⟨a, haW⟩} := by
    ext y
    simp only [mem_map, mem_subgroupOf, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg φ (Subtype.ext hw)
    · intro hy
      refine ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩
      have h1 := congrArg φ.symm hy
      rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at h1
      exact congrArg Subtype.val h1
  refine ⟨ρ, hinj, happ, fun ρ' hρ' => huniq ρ' fun w => ?_, hWρ, hz2, hρa, ?_, hφC, ?_, ?_⟩
  · ext y
    obtain ⟨v, rfl⟩ := φ.surjective y
    rw [hρ' w v (mul_mem (mul_mem w.2 v.2) (inv_mem w.2)), MulAut.conj_apply, ← map_inv,
      ← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext rfl)
  · rw [SymmetricLocal.map_centralizer_singleton_of_injective ρ hinj a, hρa]
  · ext χ
    constructor
    · rintro ⟨x, ⟨hxW, hxa⟩, rfl⟩
      refine ⟨φ ⟨x, hxW⟩, ?_, (hρW ⟨x, hxW⟩).symm⟩
      rw [← hφC]
      exact ⟨⟨x, hxW⟩, hxa, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      rw [← hφC] at hy
      obtain ⟨w, hw, rfl⟩ := hy
      exact ⟨w, ⟨w.2, hw⟩, hρW w⟩
  · have hinner : OuterAutomorphisms.inner T = (MulAut.conj : T →* MulAut T).range := rfl
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hinner, ← hWρ,
      comap_map_eq_self_of_injective hinj]

theorem simple_generalized_fitting_large_Ree_Tits_involution_centralizers_component_free
    {A : Type} [Group A] [Finite A] {W : Subgroup A} (hW : CFSG.generalizedFitting A = W)
    (hWs : IsSimpleGroup W) (hWnab : ∃ x y : W, x * y ≠ y * x) {a : A} (ha : orderOf a = 2)
    {t : Assembly.LowTwoRank.StatedLieTag} (ht : t = .twistedF4 ∨ t = .Tits) {p₀ e : ℕ}
    (hmod : ReeTitsModel W t p₀ e) :
    ∃ haW : a ∈ W,
      (∀ L : Subgroup A, ¬ Assembly.IsComponentOf L (centralizer ({a} : Set A))) ∧
      CFSG.layer (centralizer ({a} : Set A)) = ⊥ ∧
      (t = .twistedF4 → p₀ = 2 ∧ (∃ m : ℕ, 1 ≤ m ∧ e = 2 * m + 1) ∧
        ∀ (m : ℕ) (K : Type) [Field K] [Finite K] [CharP K F4.prime], e = 2 * m + 1 →
          Nat.card K = p₀ ^ e →
          Nonempty (W ≃* DerivedCentralQuotient (reeFixedGroup .F4 K reeF4Perm
            fun i => if i ∈ reeF4Long then p₀ ^ m else p₀ ^ (m + 1))) →
          Nonempty (W ≃* F4.reeGamma K m)) ∧
      (t = .Tits → p₀ = 2 ∧ e = 1 ∧ Nonempty (W ≃* Sporadic.Schreier.Tits.titsD)) ∧
      ∀ (T : Type) [Group T] (φ : W ≃* T), ∃ ρ : A →* MulAut T, Function.Injective ρ ∧
        (∀ (x : A) (w : W) (hw : x * w * x⁻¹ ∈ W), ρ x (φ w) = φ ⟨_, hw⟩) ∧
        (∀ ρ' : A →* MulAut T,
          (∀ (x : A) (w : W) (hw : x * w * x⁻¹ ∈ W), ρ' x (φ w) = φ ⟨_, hw⟩) → ρ' = ρ) ∧
        W.map ρ = OuterAutomorphisms.inner T ∧ orderOf (φ ⟨a, haW⟩) = 2 ∧
        ρ a = MulAut.conj (φ ⟨a, haW⟩) ∧
        (centralizer ({a} : Set A)).map ρ = ρ.range ⊓ centralizer {MulAut.conj (φ ⟨a, haW⟩)} ∧
        ((centralizer ({a} : Set A)).subgroupOf W).map φ.toMonoidHom =
          centralizer {φ ⟨a, haW⟩} ∧
        (W ⊓ centralizer ({a} : Set A)).map ρ = (centralizer {φ ⟨a, haW⟩}).map MulAut.conj ∧
        ((QuotientGroup.mk' (OuterAutomorphisms.inner T)).comp ρ).ker = W ∧
        Group.IsSolvable ((QuotientGroup.mk' (OuterAutomorphisms.inner T)).comp ρ).range := by
  classical
  have hWn : W.Normal := by
    rw [← hW, CFSG.generalizedFitting_eq_componentClassification]
    exact ComponentClassification.GeneralizedFitting.normal A
  have hZW : center W = ⊥ := OutcomeLocal.center_eq_bot_of_isSimpleGroup hWnab
  have hCW : centralizer (W : Set A) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxW : x ∈ W := by
      rw [← hW]
      exact CFSG.centralizer_generalizedFitting_le A (by rw [hW]; exact hx)
    have hxZ : (⟨x, hxW⟩ : W) ∈ center W := mem_center_iff.mpr fun y =>
      Subtype.ext (mem_centralizer_iff.mp hx y y.2)
    rw [hZW, mem_bot] at hxZ
    exact mem_bot.mpr (congrArg Subtype.val hxZ)
  have hF4 : t = .twistedF4 → p₀ = 2 ∧ (∃ m : ℕ, 1 ≤ m ∧ e = 2 * m + 1) ∧
      ∀ (m : ℕ) (K : Type) [Field K] [Finite K] [CharP K F4.prime], e = 2 * m + 1 →
        Nat.card K = p₀ ^ e →
        Nonempty (W ≃* DerivedCentralQuotient (reeFixedGroup .F4 K reeF4Perm
          fun i => if i ∈ reeF4Long then p₀ ^ m else p₀ ^ (m + 1))) →
        Nonempty (W ≃* F4.reeGamma K m) := by
    rintro rfl
    obtain ⟨-, -, -, hp, hm, hiso⟩ := large_Ree_model_Schreier _ p₀ e hmod
    exact ⟨hp, hm, hiso⟩
  have hTits : t = .Tits → p₀ = 2 ∧ e = 1 ∧ Nonempty (W ≃* Sporadic.Schreier.Tits.titsD) := by
    rintro rfl
    exact ⟨hmod.1.2.2.2.1, hmod.1.2.2.2.2, Sporadic.Schreier.Tits.titsModelEquiv _ p₀ e hmod⟩
  obtain ⟨T₀, _, ⟨φ₀⟩, hInn, hfree, hOut⟩ : ∃ (T₀ : Type) (_ : Group T₀),
      Nonempty (W ≃* T₀) ∧
      (∀ Y : Subgroup (MulAut T₀), OuterAutomorphisms.inner T₀ ≤ Y → ∀ u ∈ Y, orderOf u = 2 →
        u ∈ OuterAutomorphisms.inner T₀) ∧
      (∀ z : T₀, orderOf z = 2 → ∀ B : Subgroup (centralizer ({z} : Set T₀)),
        ¬ CFSG.IsComponent B) ∧
      Group.IsSolvable (Outer W) := by
    rcases ht with rfl | rfl
    · obtain ⟨-, -, hsolv, hp, ⟨m, hm, hem⟩, hiso⟩ := large_Ree_model_Schreier _ p₀ e hmod
      subst hp
      obtain ⟨-, a', hfa, K, _, _, hK, hw⟩ := hmod
      have hc : CharP K F4.prime :=
        LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
          (by omega) hK
      have hK' : Nat.card K = 2 ^ (2 * a' + 1) := by rw [hK, hfa]
      have ha' : 1 ≤ a' := by omega
      exact ⟨F4.reeGamma K a', inferInstance, hiso a' K hfa hK hw,
        fun Y hY u hu hu2 =>
          ((LargeReeInvolution.large_Ree_all_intermediate_involution_centralizers_odd_core_free
            a' ha' K hK').1 Y hY u hu hu2).1,
        (LargeReeInvolution.large_Ree_involution_centralizers_component_free a' ha' K hK').1,
        hsolv⟩
    · exact ⟨Sporadic.Schreier.Tits.titsD, inferInstance,
        Sporadic.Schreier.Tits.titsModelEquiv _ p₀ e hmod,
        fun Y hY u hu hu2 =>
          (Sporadic.Schreier.Tits.CTUC_Tits_all_intermediate_involution_centralizers_odd_core_free
            Y hY u hu hu2).1,
        Sporadic.Schreier.Tits.titsD_involution_centralizer_component_free,
        (Sporadic.Schreier.Tits.AT_Tits_model_Schreier _ p₀ e hmod).2⟩
  have hZ₀ : center T₀ = ⊥ := by
    have : IsSimpleGroup T₀ := φ₀.symm.isSimpleGroup
    refine OutcomeLocal.center_eq_bot_of_isSimpleGroup ?_
    obtain ⟨x, y, hxy⟩ := hWnab
    exact ⟨φ₀ x, φ₀ y, fun h => hxy (φ₀.injective (by rw [map_mul, map_mul, h]))⟩
  obtain ⟨ρ₀, hinj₀, hρW₀, -, -⟩ := OutcomeLocal.socle_extension hCW φ₀ hZ₀
  have hWρ₀ : W.map ρ₀ = (MulAut.conj : T₀ →* MulAut T₀).range :=
    OutcomeLocal.map_eq_range_conj φ₀ hρW₀
  have hle₀ : (MulAut.conj : T₀ →* MulAut T₀).range ≤ ρ₀.range := hWρ₀ ▸ map_le_range ρ₀ W
  have haW : a ∈ W := by
    have ha2 : orderOf (ρ₀ a) = 2 := by rw [orderOf_injective ρ₀ hinj₀ a, ha]
    have h1 : ρ₀ a ∈ (MulAut.conj : T₀ →* MulAut T₀).range :=
      hInn ρ₀.range hle₀ (ρ₀ a) ⟨a, rfl⟩ ha2
    rw [← hWρ₀] at h1
    obtain ⟨w, hw, hwa⟩ := h1
    rwa [← hinj₀ hwa]
  have hOut₀ : Group.IsSolvable (Outer T₀) :=
    (LocalAnalysis.ComponentInitial.outer_isomorphism φ₀).2.mp hOut
  have hker₀ : ((QuotientGroup.mk' (OuterAutomorphisms.inner T₀)).comp ρ₀).ker = W := by
    have hinner : OuterAutomorphisms.inner T₀ = (MulAut.conj : T₀ →* MulAut T₀).range := rfl
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hinner, ← hWρ₀,
      comap_map_eq_self_of_injective hinj₀]
  have hnocomp : ∀ L : Subgroup A, ¬ Assembly.IsComponentOf L (centralizer ({a} : Set A)) := by
    intro L hL
    have : Group.IsPerfect L := ⟨hL.2.2.1⟩
    have hLW : L ≤ W :=
      hker₀ ▸ le_ker_of_isPerfect_of_isSolvable L
        ((QuotientGroup.mk' (OuterAutomorphisms.inner T₀)).comp ρ₀)
    have hLCW : Assembly.IsComponentOf L (W ⊓ centralizer {a}) :=
      LocalAnalysis.ComponentInitial.isComponentOf_of_le hL (le_inf hLW hL.1) inf_le_right
    have hconj := OutcomeLocal.conj_injective_of_center_eq_bot hZ₀
    have hz2 : orderOf (φ₀ ⟨a, haW⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, ← ha]
      exact (orderOf_injective W.subtype W.subtype_injective ⟨a, haW⟩).symm
    have hCAimg := SymmetricLocal.map_centralizer_singleton_of_injective ρ₀ hinj₀ a
    have hCWimg : (W ⊓ centralizer {a}).map ρ₀ =
        (MulAut.conj : T₀ →* MulAut T₀).range ⊓ centralizer {ρ₀ a} := by
      rw [map_inf_eq _ _ _ hinj₀, hWρ₀, hCAimg, ← inf_assoc, inf_eq_left.mpr hle₀]
    have hL₁ : Assembly.IsComponentOf (L.map ρ₀)
        ((MulAut.conj : T₀ →* MulAut T₀).range ⊓ centralizer {MulAut.conj (φ₀ ⟨a, haW⟩)}) := by
      have := SymmetricLocal.isComponentOf_map_of_injective ρ₀ hinj₀ hLCW
      rw [hCWimg, hρW₀ ⟨a, haW⟩] at this
      exact this
    exact UnbalancingLocal.ComponentFree.no_component_of_mulEquiv
      (UnbalancingLocal.ComponentFree.centralizerRangeEquiv hconj (φ₀ ⟨a, haW⟩)).symm
      (hfree _ hz2) _
      ((LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hL₁.1).mp hL₁)
  have hlayer : CFSG.layer (centralizer ({a} : Set A)) = ⊥ := by
    refine sSup_eq_bot.mpr fun K hK => ?_
    exfalso
    exact hnocomp (K.map (centralizer ({a} : Set A)).subtype)
      ((LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
        (map_subtype_le K)).mpr (by
          have h : (K.map (centralizer ({a} : Set A)).subtype).subgroupOf
              (centralizer ({a} : Set A)) = K :=
            comap_map_eq_self_of_injective (centralizer ({a} : Set A)).subtype_injective K
          rw [h]
          exact hK))
  refine ⟨haW, hnocomp, hlayer, hF4, hTits, fun T _ φ => ?_⟩
  obtain ⟨ρ, hinj, happ, huniq, hWρ, hz2, hρa, hCA, hφC, hCW', hker⟩ :=
    socle_action_facts hWnab hCW haW ha φ
  have hOutT : Group.IsSolvable (Outer T) :=
    (LocalAnalysis.ComponentInitial.outer_isomorphism φ).2.mp hOut
  exact ⟨ρ, hinj, happ, huniq, hWρ, hz2, hρa, hCA, hφC, hCW', hker, inferInstance⟩

end CFSG.ComponentClassification.UnbalancedCorr
