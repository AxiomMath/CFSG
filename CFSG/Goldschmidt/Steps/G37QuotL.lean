module

import CFSG.Goldschmidt.Steps.Completion
import CFSG.Goldschmidt.Steps.G36Setup
public import CFSG.Goldschmidt.Steps.G37CoreTypeII
public import CFSG.Goldschmidt.Steps.G37Quot

public section

namespace CFSG.Goldschmidt.G37

open CFSG.GorensteinWalter
open CFSG.Open (goldschmidtOddCore goldschmidtLayer)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H : Subgroup G}

omit [Finite G] in
theorem mem_centralizer_goldschmidtOddCore_iff (x : H) :
    x ∈ Subgroup.centralizer (goldschmidtOddCore H : Set H) ↔
      (x : G) ∈ Subgroup.centralizer (oddCoreOf H : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · rintro h _ ⟨o, ho, rfl⟩
    exact congrArg Subtype.val (h o ho)
  · intro h o ho
    exact Subtype.ext (h (o : G) ⟨o, ho, rfl⟩)

omit [Finite G] in
theorem nonempty_centerQuotientEquiv_barOf {K : Subgroup G} (hKH : K ≤ H)
    (hKp : Group.IsPerfect K) (hKO : K ≤ Subgroup.centralizer (oddCoreOf H : Set G)) :
    Nonempty (K ⧸ Subgroup.center K ≃* barOf H K ⧸ Subgroup.center (barOf H K)) := by
  let e : K.subgroupOf H ≃* K := Subgroup.subgroupOfEquivOfLe hKH
  have hP : Group.IsPerfect (K.subgroupOf H) := by
    have := hKp
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let f := (QuotientGroup.mk' (goldschmidtOddCore H)).subgroupMap (K.subgroupOf H)
  have hker : f.ker ≤ Subgroup.center (K.subgroupOf H) := by
    intro x hx
    have h1 : QuotientGroup.mk' (goldschmidtOddCore H) (x : H) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have h2 : (x : H) ∈ goldschmidtOddCore H := (QuotientGroup.eq_one_iff _).mp h1
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact ((Subgroup.mem_centralizer_iff.mp (hKO y.2)) _ ⟨_, h2, rfl⟩).symm
  obtain ⟨φ⟩ := nonempty_centerQuotientEquiv hP f
    ((QuotientGroup.mk' (goldschmidtOddCore H)).subgroupMap_surjective _) hker
  exact ⟨(CFSG.Goldschmidt.SStarTransport.quotientCenterEquiv e.symm).trans φ⟩

omit [Finite G] in
theorem isGoldL2_of_barOf {K : Subgroup G} (hKH : K ≤ H) (hKp : Group.IsPerfect K)
    (hKO : K ≤ Subgroup.centralizer (oddCoreOf H : Set G)) (h : IsGoldL2 (barOf H K)) :
    IsGoldL2 K := by
  obtain ⟨φ⟩ := nonempty_centerQuotientEquiv_barOf hKH hKp hKO
  exact isTypeL2Odd_of_mulEquiv φ.symm h

theorem isGoldJR_of_barOf {K : Subgroup G} (hKH : K ≤ H) (hKp : Group.IsPerfect K)
    (hKO : K ≤ Subgroup.centralizer (oddCoreOf H : Set G)) (h : IsGoldJR (barOf H K)) :
    IsGoldJR K := by
  obtain ⟨φ⟩ := nonempty_centerQuotientEquiv_barOf hKH hKp hKO
  exact CFSG.Walter.IsTypeJR.of_mulEquiv φ.symm h

omit [Finite G] in
theorem exists_isComponentOf_of_le_barOf {Lb : Subgroup (H ⧸ goldschmidtOddCore H)}
    (hLb : IsComponentOf Lb ⊤)
    (hcov : Lb ≤ barOf H (H ⊓ Subgroup.centralizer (oddCoreOf H : Set G))) :
    ∃ L : Subgroup G, IsComponentOf L H ∧ barOf H L = Lb ∧
      ∀ K : Subgroup G, K ≤ H → K ≤ Subgroup.centralizer (oddCoreOf H : Set G) →
        Group.IsPerfect K → barOf H K ≤ Lb → K ≤ L := by
  set π := QuotientGroup.mk' (goldschmidtOddCore H) with hπ
  set C : Subgroup H := Subgroup.centralizer (goldschmidtOddCore H : Set H) with hC
  set D : Subgroup H := Lb.comap π ⊓ C with hD
  set L' : Subgroup H := ⁅D, D⁆ with hL'
  have hDmap : D.map π = Lb := by
    apply le_antisymm
    · exact (Subgroup.map_mono inf_le_left).trans (Subgroup.map_comap_le _ _)
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := hcov hy
      exact ⟨x, Subgroup.mem_inf.mpr ⟨hy,
        (mem_centralizer_goldschmidtOddCore_iff x).mpr (Subgroup.mem_inf.mp hx).2⟩, rfl⟩
  let f : D →* Lb := (π.comp D.subtype).codRestrict Lb (fun x => (Subgroup.mem_inf.mp x.2).1)
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [← hDmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : f.ker ≤ Subgroup.center D := by
    intro x hx
    have h1 : π (x : H) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have h2 : (x : H) ∈ goldschmidtOddCore H := (QuotientGroup.eq_one_iff _).mp h1
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp y.2).2) _ h2).symm
  have hLbq : CFSG.IsQuasisimple Lb := ⟨Group.isPerfect_def.mpr hLb.2.2.2.1, hLb.2.2.2.2,
    CFSG.Walter.IsQuasisimple.exists_mul_ne_mul hLb.2.2⟩
  have hDq := CFSG.LocalCores.quasisimple_central_extension_derived_of_surjective f hf hker hLbq
  have hL'q : GorensteinWalter.IsQuasisimple L' := by
    have h1 := CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((commutator D).equivMapOfInjective D.subtype D.subtype_injective) hDq
    rw [Subgroup.map_subtype_commutator] at h1
    exact ⟨CFSG.LocalCores.isQuasisimple_nontrivial h1, Group.isPerfect_def.mp h1.1, h1.2.1⟩
  have hL'D : L' ≤ D := commutator_self_le D
  have hDsn : D.IsSubnormal :=
    ((CFSG.Walter.isSubnormal_of_isComponentOf hLb).comap π).inf
      (Subgroup.normal_centralizer (H := goldschmidtOddCore H)).isSubnormal
  have hL'sn : L'.IsSubnormal := Subgroup.IsSubnormal.trans hL'D
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hL'D).mpr
      (Subgroup.normalizer_commutator_ge_left D D)).isSubnormal hDsn
  have hL'sub : (L'.map H.subtype).subgroupOf H = L' :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hLbp : ⁅Lb, Lb⁆ = Lb := Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hLb.2.2.2.1)
  refine ⟨L'.map H.subtype, ⟨Subgroup.map_subtype_le _, hL'sub.symm ▸ hL'sn,
    CFSG.Walter.isQuasisimple_of_mulEquiv' (L'.equivMapOfInjective H.subtype
      H.subtype_injective) hL'q⟩, ?_, ?_⟩
  · rw [barOf, hL'sub, hL', Subgroup.map_commutator, hDmap, hLbp]
  · intro K hKH hKO hKp hKLb
    have hKD : K.subgroupOf H ≤ D := fun x hx =>
      Subgroup.mem_inf.mpr ⟨hKLb ⟨x, hx, rfl⟩, (mem_centralizer_goldschmidtOddCore_iff x).mpr
        (hKO hx)⟩
    have hKp' : ⁅K.subgroupOf H, K.subgroupOf H⁆ = K.subgroupOf H := by
      rw [← subgroupOf_commutator hKH hKH, Subgroup.isPerfect_iff.mp hKp]
    have h1 : K.subgroupOf H ≤ L' := hKp' ▸ Subgroup.commutator_mono hKD hKD
    have h2 := Subgroup.map_mono (f := H.subtype) h1
    rwa [Subgroup.map_subgroupOf_eq_of_le hKH] at h2

omit [Finite G] in
theorem preOf_centralizer_barOf {L : Subgroup G} (hLH : L ≤ H) (hLp : Group.IsPerfect L)
    (hLO : L ≤ Subgroup.centralizer (oddCoreOf H : Set G)) :
    preOf H (Subgroup.centralizer (barOf H L : Set (H ⧸ goldschmidtOddCore H))) =
      H ⊓ Subgroup.centralizer (L : Set G) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
    have h1 := commutator_le_oddCoreOf_of_mk_mem_centralizer hLH x.2 hx
    have h2 : ⁅⁅L, Subgroup.zpowers (x : G)⁆, L⁆ = ⊥ := by
      rw [Subgroup.commutator_comm L, eq_bot_iff]
      calc ⁅⁅Subgroup.zpowers (x : G), L⁆, L⁆ ≤ ⁅oddCoreOf H, L⁆ :=
            Subgroup.commutator_mono h1 le_rfl
        _ = ⊥ := by
            rw [Subgroup.commutator_comm]
            exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hLO
        _ ≤ ⊥ := le_rfl
    have h4 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.LocalCores.perfect_double_commutator hLp h2)
    rw [Subgroup.mem_centralizer_iff]
    intro ℓ hℓ
    exact (Subgroup.mem_centralizer_iff.mp (h4 hℓ) (x : G) (Subgroup.mem_zpowers _)).symm
  · intro y hy
    obtain ⟨hyH, hyC⟩ := Subgroup.mem_inf.mp hy
    refine ⟨⟨y, hyH⟩, ?_, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_comap]
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨ℓ, hℓ, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hyC _ hℓ

theorem barOf_inf_le {A L : Subgroup G} (hA : IsPGroup 2 A) (hLH : L ≤ H)
    (hLO : L ≤ Subgroup.centralizer (oddCoreOf H : Set G)) :
    barOf H A ⊓ barOf H L ≤ barOf H (A ⊓ L) := by
  rintro _ ⟨⟨x, hx, rfl⟩, hxL⟩
  have hxLO : (x : G) ∈ L ⊔ oddCoreOf H := by
    rw [← preOf_barOf' hLH]
    exact ⟨x, hxL, rfl⟩
  obtain ⟨k, hk⟩ := hA ⟨x, hx⟩
  have hk' : (x : G) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hxL' : (x : G) ∈ L := CFSG.Goldschmidt.mem_of_mem_sup_of_odd
    (Completion.odd_card_oddCoreOf H)
    (fun l hl o ho => (Subgroup.mem_centralizer_iff.mp (hLO hl) o ho).symm) hxLO hk'
  exact ⟨x, ⟨hx, hxL'⟩, rfl⟩

theorem le_centralizer_oddCoreOf_of_isComponentOf {L : Subgroup G} (hL : IsComponentOf L H) :
    L ≤ Subgroup.centralizer (oddCoreOf H : Set G) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.Walter.isComponentOf_commutator_eq_bot_of_isSolvable hL
      (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Completion.odd_card_oddCoreOf H)) (Subgroup.map_subtype_le _)
      (Completion.le_normalizer_oddCoreOf H))

end CFSG.Goldschmidt.G37
