module

public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents
public import CFSG.LocalAnalysis.ComponentInitial.BlockSylowOrder
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBLocalB
public import CFSG.LocalAnalysis.ComponentInitial.KProperSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalMaximalComponent
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification

section TwoComponents

variable {X : Type*} [Group X] [Finite X]

theorem isSolvable_pPrimeCore_two : Group.IsSolvable (CFSG.pPrimeCore 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card)

theorem isPComponent_two_of_isComponent {K : Subgroup X} (hK : CFSG.IsComponent K) :
    CFSG.IsPComponent 2 K :=
  (solvable_prime_core_ordinary_components 2 Nat.prime_two isSolvable_pPrimeCore_two).1 K hK

theorem pLayer_two_eq_top_of_isQuasisimple (hX : CFSG.IsQuasisimple X) : CFSG.pLayer X 2 = ⊤ := by
  have htop : CFSG.IsComponent (⊤ : Subgroup X) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hX, Subgroup.IsSubnormal.top⟩
  exact eq_top_iff.2 (le_sSup (isPComponent_two_of_isComponent htop))

end TwoComponents

variable {G : Type*} [Group G]

theorem isTwoPComponent_of_isComponentOf [Finite G] {Q C : Subgroup G}
    (hQ : CFSG.Assembly.IsComponentOf Q C) :
    CFSG.Assembly.ComponentType.IsTwoPComponent (Q.subgroupOf C) :=
  (isTwoPComponent_iff_isPComponent _).2
    (isPComponent_two_of_isComponent ((isComponentOf_iff_isComponent_subgroupOf hQ.1).1 hQ))

theorem gsFixedLayer_eq_of_le_centralizer [Finite G] {J : Subgroup G} {t : G}
    (hJ : CFSG.Assembly.IsQuasisimple J) (hJt : J ≤ centralizer ({t} : Set G)) :
    UnbalancedGS.gsFixedLayer J t = J := by
  unfold UnbalancedGS.gsFixedLayer
  rw [inf_eq_left.mpr hJt, pLayer_two_eq_top_of_isQuasisimple
    ((AssemblyBPredicates.isQuasisimple_iff_native J).1 hJ), ← MonoidHom.range_eq_map,
    range_subtype]

theorem pLayer_map_eq_of_commutator_eq [Finite G] {C J : Subgroup G} (hJC : J ≤ C)
    (hcomm : ⁅C, C⁆ = J) (hJ : CFSG.Assembly.IsQuasisimple J) :
    (CFSG.pLayer C 2).map C.subtype = J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap, CFSG.pLayer]
    refine sSup_le fun P hP => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have hperf : Group.IsPerfect P :=
      ((PrimeComponentLift.prime_component_minimal_perfect_lift 2).2 P hP).1
    have hPle : P ≤ commutator C := by
      rw [← Subgroup.isPerfect_iff.mp hperf, _root_.commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    calc P.map C.subtype ≤ (commutator C).map C.subtype := Subgroup.map_mono hPle
      _ = ⁅C, C⁆ := Subgroup.map_subtype_commutator C
      _ = J := hcomm
  · have hnormal : (J.subgroupOf C).Normal := by
      have h : J.subgroupOf C = commutator C := by
        rw [← hcomm, ← Subgroup.map_subtype_commutator, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
      rw [h]
      infer_instance
    have hcomp : CFSG.IsComponent (J.subgroupOf C) :=
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJC).symm
        ((AssemblyBPredicates.isQuasisimple_iff_native J).1 hJ), hnormal.isSubnormal⟩
    calc J = (J.subgroupOf C).map C.subtype := (Subgroup.map_subgroupOf_eq_of_le hJC).symm
      _ ≤ (CFSG.pLayer C 2).map C.subtype :=
        Subgroup.map_mono (le_sSup (isPComponent_two_of_isComponent hcomp))

theorem exists_component_centralizer_of_pumpUp {C : CFSG.Assembly.GroupProp}
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hpump : KProperOrdinaryLocalBPumpUp C) {G : Type} [Group G] [Finite G]
    (hK : CFSG.Assembly.KProper C G)
    (hB : CFSG.Assembly.ComponentType.LocalBProperty G) {a b : G} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hab : a * b = b * a) {J : Subgroup G}
    (hJ : CFSG.Assembly.IsComponentOf J (centralizer ({a} : Set G)))
    (hJb : J ≤ centralizer ({b} : Set G)) :
    ∃ L : Subgroup G, CFSG.Assembly.IsComponentOf L (centralizer ({b} : Set G)) ∧
      ((conjSub a⁻¹ L = L ∧ J ≤ L) ∨
        (conjSub a⁻¹ L ≠ L ∧ (J : Set G) = {g | ∃ x ∈ L, x * (a⁻¹ * x * a) = g})) := by
  set H := centralizer ({b} : Set G) with hHdef
  have haH : a ∈ H := Subgroup.mem_centralizer_singleton_iff.2 hab
  set a' : H := ⟨a, haH⟩ with ha'def
  have ha' : orderOf a' = 2 := by rw [Subgroup.orderOf_mk]; exact ha
  have hKH : CFSG.Assembly.KProper C H := kProper_subgroup hC hK H
  have hloc : ∀ Q : Subgroup H, CFSG.Assembly.ComponentType.IsTwoPComponent Q →
      CFSG.Assembly.IsComponentOf Q ⊤ :=
    fun Q hQ => AssemblyBLocalB.ordinary_at_involution hB b hb Q hQ
  have hJ' : CFSG.Assembly.IsComponentOf (J.subgroupOf H) (centralizer ({a'} : Set H)) := by
    have h1 : CFSG.Assembly.IsComponentOf J (H ⊓ centralizer ({a} : Set G)) :=
      isComponentOf_of_le hJ (le_inf hJb hJ.1) inf_le_right
    rw [← map_subtype_centralizer_singleton H a', ← Subgroup.map_subgroupOf_eq_of_le hJb] at h1
    exact (isComponentOf_map_iff H.subtype_injective).1 h1
  obtain ⟨-, L', hL', hcase⟩ := hpump H hKH hloc a' ha' (J.subgroupOf H) hJ'
  have hLmap : CFSG.Assembly.IsComponentOf (L'.map H.subtype) H := by
    have h2 := (isComponentOf_map_iff H.subtype_injective).2
      ((AssemblyBPredicates.isComponentOf_top_iff_native L').2 hL')
    rwa [← MonoidHom.range_eq_map, range_subtype] at h2
  have hconj : (conjSub a'⁻¹ L').map H.subtype = conjSub a⁻¹ (L'.map H.subtype) :=
    map_subtype_conjSub H a'⁻¹ L'
  refine ⟨L'.map H.subtype, hLmap, ?_⟩
  rcases hcase with ⟨hinv, hJL⟩ | ⟨hne, hset, -, -⟩
  · refine Or.inl ⟨by rw [← hconj, hinv], ?_⟩
    calc J = (J.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hJb).symm
      _ ≤ L'.map H.subtype := Subgroup.map_mono (hJL.1.trans inf_le_left)
  · refine Or.inr ⟨fun h => hne (Subgroup.map_injective H.subtype_injective (hconj.trans h)), ?_⟩
    ext g
    constructor
    · intro hg
      have hmem : (⟨g, hJb hg⟩ : H) ∈ ((J.subgroupOf H : Subgroup H) : Set H) := hg
      rw [hset] at hmem
      obtain ⟨x, hx, hxg⟩ := hmem
      exact ⟨x, ⟨x, hx, rfl⟩, congrArg Subtype.val hxg⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      have hmem : x * (a'⁻¹ * x * a') ∈ ((J.subgroupOf H : Subgroup H) : Set H) := by
        rw [hset]
        exact ⟨x, hx, rfl⟩
      exact hmem

theorem eq_of_le_of_index_center_le [Finite G] {J L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hJL : J ≤ L)
    (hle : (center L).index ≤ (center J).index) : L = J := by
  have : Group.IsPerfect L := ⟨hL.1⟩
  by_contra hne
  exact absurd hle (not_le.2 (index_center_lt_of_lt (lt_of_le_of_ne hJL (Ne.symm hne))))

theorem diagonal_data_of_swapped [Finite G] {a b : G} (ha : orderOf a = 2)
    (hab : a * b = b * a) {J L : Subgroup G}
    (hL : CFSG.Assembly.IsComponentOf L (centralizer ({b} : Set G))) (hLa : conjSub a⁻¹ L ≠ L)
    (hset : (J : Set G) = {g | ∃ x ∈ L, x * (a⁻¹ * x * a) = g}) :
    (∃ δ : L →* J, (∀ x : L, (δ x : G) = x * (a⁻¹ * x * a)) ∧
      Function.Surjective δ ∧ δ.ker ≤ center L) ∧
      Nonempty (J ⧸ center J ≃* L ⧸ center L) ∧
      ⁅(L ⊔ conjSub a⁻¹ L) ⊓ centralizer ({a} : Set G),
        (L ⊔ conjSub a⁻¹ L) ⊓ centralizer ({a} : Set G)⁆ = J ∧
      J ≤ (L ⊔ conjSub a⁻¹ L) ⊓ centralizer ({a} : Set G) ∧ CFSG.Assembly.IsQuasisimple J := by
  have haH : a⁻¹ ∈ centralizer ({b} : Set G) :=
    inv_mem (Subgroup.mem_centralizer_singleton_iff.2 hab)
  have hAB : ⁅L, conjSub a⁻¹ L⁆ = ⊥ :=
    (isComponentOf_eq_or_commute hL (isComponentOf_conjSub_of_mem hL haH)).resolve_left
      fun h => hLa h.symm
  obtain ⟨hΔset, hΔC, hsurj, hker, -, hΔq, -, -, hder, -, -, hiso⟩ :=
    swapped_quasisimple_fixed_central_product ha hL.2.2 hAB
  have hΔJ : (swapDiag hAB).range = J := SetLike.ext' (hΔset.trans hset.symm)
  refine ⟨⟨(MulEquiv.subgroupCongr hΔJ).toMonoidHom.comp (swapDiag hAB).rangeRestrict,
    fun x => rfl, (MulEquiv.subgroupCongr hΔJ).surjective.comp hsurj, fun x hx => hker ?_⟩,
    hΔJ ▸ hiso, hder.trans hΔJ, hΔJ ▸ hΔC, hΔJ ▸ hΔq⟩
  rw [MonoidHom.mem_ker] at hx ⊢
  exact (MulEquiv.subgroupCongr hΔJ).injective (hx.trans (map_one _).symm)

theorem gsCorr_of_fixed_layer [Finite G] {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : a * b = b * a) {J L : Subgroup G}
    (hJ : CFSG.Assembly.IsComponentOf J (centralizer ({a} : Set G)))
    (hJp : CFSG.Assembly.ComponentType.IsTwoPComponent (J.subgroupOf (centralizer ({a} : Set G))))
    (hJb : J ≤ centralizer ({b} : Set G))
    (hL : CFSG.Assembly.IsComponentOf L (centralizer ({b} : Set G)))
    (hlayer : UnbalancedGS.gsFixedLayer (L ⊔ conjugate L a) a = J) :
    UnbalancedGS.GSCorr a J b L := by
  have hbJ : b ∈ centralizer (J : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun j hj => (Subgroup.mem_centralizer_singleton_iff.1 (hJb hj))
  refine ⟨ha, hb, hab, hJ.1, (isTwoPComponent_iff_isPComponent _).1 hJp, hL.1,
    (isTwoPComponent_iff_isPComponent _).1 (isTwoPComponent_of_isComponentOf hL),
    centralizer_le_normalizer _ hbJ, fun j hj => ?_, ?_⟩
  · have hjb : j * b = b * j := Subgroup.mem_centralizer_iff.1 hbJ j hj
    rw [show j⁻¹ * b⁻¹ * j * b = 1 by
      rw [mul_assoc, mul_assoc, ← mul_assoc b⁻¹, show b⁻¹ * j * b = j by
        rw [mul_assoc, hjb, ← mul_assoc, inv_mul_cancel, one_mul], inv_mul_cancel]]
    exact one_mem _
  · rw [gsFixedLayer_eq_of_le_centralizer hJ.2.2 hJb, hlayer]

theorem exists_correspondence_of_commuting_involution {C : CFSG.Assembly.GroupProp}
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hpump : KProperOrdinaryLocalBPumpUp C) {G : Type} [Group G] [Finite G]
    (hK : CFSG.Assembly.KProper C G) (hB : CFSG.Assembly.ComponentType.LocalBProperty G)
    {a : G} (ha : orderOf a = 2) {J : Subgroup G}
    (hJ : CFSG.Assembly.IsComponentOf J (centralizer ({a} : Set G)))
    (hJp : CFSG.Assembly.ComponentType.IsTwoPComponent (J.subgroupOf (centralizer ({a} : Set G))))
    (hmax : ∀ t : G, orderOf t = 2 → ∀ Q : Subgroup G,
      CFSG.Assembly.IsComponentOf Q (centralizer ({t} : Set G)) →
        (center Q).index ≤ (center J).index)
    {b : G} (hb : orderOf b = 2) (hab : a * b = b * a) (hJb : J ≤ centralizer ({b} : Set G)) :
    ∃ L : Subgroup G, CFSG.Assembly.IsComponentOf L (centralizer ({b} : Set G)) ∧
      CFSG.Assembly.ComponentType.IsTwoPComponent (L.subgroupOf (centralizer ({b} : Set G))) ∧
      UnbalancedGS.GSCorr a J b L ∧
      (L = J ∨
        (conjSub a⁻¹ L ≠ L ∧ (J : Set G) = {g | ∃ x ∈ L, x * (a⁻¹ * x * a) = g} ∧
          (∃ δ : L →* J, (∀ x : L, (δ x : G) = x * (a⁻¹ * x * a)) ∧
            Function.Surjective δ ∧ δ.ker ≤ center L) ∧
          Nonempty (J ⧸ center J ≃* L ⧸ center L) ∧
          ⁅(L ⊔ conjSub a⁻¹ L) ⊓ centralizer ({a} : Set G),
            (L ⊔ conjSub a⁻¹ L) ⊓ centralizer ({a} : Set G)⁆ = J)) := by
  obtain ⟨L, hL, hcase⟩ :=
    exists_component_centralizer_of_pumpUp hC hpump hK hB ha hb hab hJ hJb
  refine ⟨L, hL, isTwoPComponent_of_isComponentOf hL, ?_⟩
  rcases hcase with ⟨-, hJL⟩ | ⟨hLa, hset⟩
  · have hLJ : L = J := eq_of_le_of_index_center_le hL.2.2 hJL (hmax b hb L hL)
    subst hLJ
    have hconjJ : conjugate L a = L := by
      have haN : a⁻¹ ∈ normalizer (L : Set G) := centralizer_le_normalizer _ (inv_mem
        (Subgroup.mem_centralizer_iff.2 fun j hj =>
          Subgroup.mem_centralizer_singleton_iff.1 (hJ.1 hj)))
      exact conjSub_eq_of_mem_normalizer haN
    refine ⟨gsCorr_of_fixed_layer ha hb hab hJ hJp hJb hL ?_, Or.inl rfl⟩
    rw [hconjJ, sup_idem]
    exact gsFixedLayer_eq_of_le_centralizer hJ.2.2 hJ.1
  · obtain ⟨hδ, hiso, hder, hJC, hJq⟩ := diagonal_data_of_swapped ha hab hL hLa hset
    refine ⟨gsCorr_of_fixed_layer ha hb hab hJ hJp hJb hL ?_,
      Or.inr ⟨hLa, hset, hδ, hiso, hder⟩⟩
    exact pLayer_map_eq_of_commutator_eq hJC hder hJq

theorem local_B_maximal_component_commuting_involution_propagation {C : CFSG.Assembly.GroupProp}
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hpump : KProperOrdinaryLocalBPumpUp C) {G : Type} [Group G] [Finite G]
    (hK : CFSG.Assembly.KProper C G) (hcomp : CFSG.Assembly.IsComponentType G)
    (hB : CFSG.Assembly.ComponentType.LocalBProperty G) :
    ∃ a : G, orderOf a = 2 ∧ ∃ J : Subgroup G,
      CFSG.Assembly.ComponentType.IsTwoPComponent (J.subgroupOf (centralizer ({a} : Set G))) ∧
      CFSG.Assembly.IsComponentOf J (centralizer ({a} : Set G)) ∧
      CFSG.Open.fusionMaximalComponent J ∧
      (∀ t : G, orderOf t = 2 → ∀ Q : Subgroup G,
        CFSG.Assembly.IsComponentOf Q (centralizer ({t} : Set G)) →
          (center Q).index ≤ (center J).index) ∧
      (∀ b : G, orderOf b = 2 → a * b = b * a → J ≤ centralizer ({b} : Set G) →
        ∃ L : Subgroup G, CFSG.Assembly.IsComponentOf L (centralizer ({b} : Set G)) ∧
          CFSG.Assembly.ComponentType.IsTwoPComponent (L.subgroupOf (centralizer ({b} : Set G))) ∧
          UnbalancedGS.GSCorr a J b L ∧
          (L = J ∨
            (conjSub a⁻¹ L ≠ L ∧ (J : Set G) = {g | ∃ x ∈ L, x * (a⁻¹ * x * a) = g} ∧
              (∃ δ : L →* J, (∀ x : L, (δ x : G) = x * (a⁻¹ * x * a)) ∧
                Function.Surjective δ ∧ δ.ker ≤ center L) ∧
              Nonempty (J ⧸ center J ≃* L ⧸ center L) ∧
              ⁅(L ⊔ conjSub a⁻¹ L) ⊓ centralizer ({a} : Set G),
                (L ⊔ conjSub a⁻¹ L) ⊓ centralizer ({a} : Set G)⁆ = J))) ∧
      ∀ b : G, orderOf b = 2 → a * b = b * a → J ≤ centralizer ({b} : Set G) →
        ∀ L : Subgroup G, CFSG.Assembly.IsComponentOf L (centralizer ({b} : Set G)) →
          conjSub a⁻¹ L = L → J ≤ L → L = J := by
  obtain ⟨a, ha, J, hJle, hJp, hJ, hJmax, hbound, -⟩ :=
    UnbalancingLocal.local_B_maximal_correspondence_component_existence hcomp hB
  have hJp' : CFSG.Assembly.ComponentType.IsTwoPComponent
      (J.subgroupOf (centralizer ({a} : Set G))) :=
    (isTwoPComponent_iff_isPComponent _).2 hJp
  have hZJ := (UnbalancingLocal.pComponent_vertex hB ha hJle hJp).2.2
  have hmax : ∀ t : G, orderOf t = 2 → ∀ Q : Subgroup G,
      CFSG.Assembly.IsComponentOf Q (centralizer ({t} : Set G)) →
        (center Q).index ≤ (center J).index := by
    intro t ht Q hQ
    have hQp : CFSG.IsPComponent 2 (Q.subgroupOf (centralizer ({t} : Set G))) :=
      isPComponent_two_of_isComponent ((isComponentOf_iff_isComponent_subgroupOf hQ.1).1 hQ)
    have h1 := hbound t ht Q hQ.1 hQp
    rwa [(UnbalancingLocal.pComponent_vertex hB ht hQ.1 hQp).2.2, hZJ] at h1
  exact ⟨a, ha, J, hJp', hJ, hJmax, hmax, fun b hb hab hJb =>
    exists_correspondence_of_commuting_involution hC hpump hK hB ha hJ hJp' hmax hb hab hJb,
    fun b hb _ _ L hL _ hJL => eq_of_le_of_index_center_le hL.2.2 hJL (hmax b hb L hL)⟩

end CFSG.LocalAnalysis.ComponentInitial
