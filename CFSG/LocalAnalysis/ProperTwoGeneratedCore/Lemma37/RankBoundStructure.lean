module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBenderCaseTwo
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBasicsFixedSet
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBenderComponent
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ComponentNumberRestrictionsEven
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineCanonicalRank

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.BenderSuzuki

structure RankBoundHyp (X : Type) [Group X] [Finite X] (t : X) : Prop where
  core : pPrimeCore 2 X = ⊥
  central : t ∈ Subgroup.center X
  order : orderOf t = 2
  layer_ne_bot : layer X ≠ ⊥
  unique : ∀ y ∈ generalizedFitting X, orderOf y = 2 → y = t

theorem orderOf_dvd_two_of_mem_center_quaternion {T : Type*} [Group T] {m : ℕ} (hm : 2 ≤ m)
    (e : T ≃* QuaternionGroup m) {x : T} (hx : x ∈ Subgroup.center T) : orderOf x ∣ 2 := by
  have hc : e x ∈ Subgroup.center (QuaternionGroup m) := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hx g']
  rw [← MulEquiv.orderOf_eq e]
  apply orderOf_dvd_of_pow_eq_one
  rcases ((CFSG.GroupTheory.quaternion_centralizers hm).2.2.1 (e x)).mp hc with h0 | h1
  · rw [h0, ← QuaternionGroup.one_def, one_pow]
  · rw [h1, pow_two, QuaternionGroup.a_mul_a, ← Nat.cast_add, ← two_mul, ZMod.natCast_self,
      ← QuaternionGroup.one_def]

variable {X : Type} [Group X] [Finite X] {t : X}

theorem two_dvd_card_of_isComponent {L : Subgroup X} (hL : CFSG.IsComponent L) :
    2 ∣ Nat.card L := by
  by_contra hodd
  have hsolv : Group.IsSolvable L :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd))
  have : Group.IsPerfect L := hL.1.1
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.1.2.1
  have : Nontrivial L := (QuotientGroup.mk'_surjective (Subgroup.center L)).nontrivial
  exact Group.IsPerfect.not_isSolvable L hsolv

namespace RankBoundHyp

variable (h : RankBoundHyp X t)
include h

theorem eq_of_mem_component {L : Subgroup X} (hL : CFSG.IsComponent L) {y : X} (hy : y ∈ L)
    (hy2 : orderOf y = 2) : y = t :=
  h.unique y (Subgroup.mem_sup_right (Assembly.component_le_layer hL hy)) hy2

theorem mem_component {L : Subgroup X} (hL : CFSG.IsComponent L) : t ∈ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 (two_dvd_card_of_isComponent hL)
  rw [← h.eq_of_mem_component hL y.2 (by rwa [Subgroup.orderOf_coe])]
  exact y.2

theorem component_eq {L L' : Subgroup X} (hL : CFSG.IsComponent L)
    (hL' : CFSG.IsComponent L') : L = L' := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 L) := inferInstance
  obtain ⟨T'⟩ : Nonempty (Sylow 2 L') := inferInstance
  have h2 := distinct_even_component_sylow_join_rank L L'
    ((CFSG.isComponent_iff_open L).mp hL) ((CFSG.isComponent_iff_open L').mp hL') hne
    (even_iff_two_dvd.mpr (two_dvd_card_of_isComponent hL))
    (even_iff_two_dvd.mpr (two_dvd_card_of_isComponent hL')) T T'
  have hle : (T : Subgroup L).map L.subtype ⊔ (T' : Subgroup L').map L'.subtype ≤
      generalizedFitting X :=
    sup_le
      ((Subgroup.map_subtype_le _).trans ((Assembly.component_le_layer hL).trans le_sup_right))
      ((Subgroup.map_subtype_le _).trans ((Assembly.component_le_layer hL').trans le_sup_right))
  have h1 := Assembly.pRank_two_le_one_of_forall_involution_eq h.order fun y hy hy2 =>
    h.unique y (hle hy) hy2
  omega

theorem exists_component : ∃ J : Subgroup X, CFSG.IsComponent J := by
  by_contra hno
  push Not at hno
  exact h.layer_ne_bot (le_bot_iff.mp (sSup_le fun J hJ => absurd hJ (hno J)))

theorem layer_eq {J : Subgroup X} (hJ : CFSG.IsComponent J) : layer X = J :=
  le_antisymm (sSup_le fun _ hL => (h.component_eq hL hJ).le) (Assembly.component_le_layer hJ)

theorem component_normal {J : Subgroup X} (hJ : CFSG.IsComponent J) : J.Normal := by
  rw [← h.layer_eq hJ, CFSG.layer_eq_componentClassification]
  exact CFSG.ComponentClassification.Layer.normal X

theorem sylow_quaternion {J : Subgroup X} (hJ : CFSG.IsComponent J) (T : Sylow 2 J) :
    ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((T : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2))) := by
  have hrank : CFSG.Open.pRank 2 J ≤ 1 :=
    Assembly.pRank_two_le_one_of_forall_involution_eq h.order fun y hy hy2 =>
      h.eq_of_mem_component hJ hy hy2
  rw [CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 2 (by decide)] at hrank
  have hnot := LocalCriterionClassFreeAffine.not_twoRankAtLeastTwo_of_twoRank_le_one hrank
  rcases sylowTwo_cyclic_or_quaternion_of_not_twoRank hnot T with hcyc | hquat
  · exact absurd hcyc (Assembly.not_isCyclic_sylow_two_of_commutator_eq_top
      hJ.1.1.commutator_eq_top (two_dvd_card_of_isComponent hJ) T)
  · exact hquat

theorem exists_mem_component_orderOf_eq_four {J : Subgroup X} (hJ : CFSG.IsComponent J) :
    ∃ a ∈ J, orderOf a = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 J) := inferInstance
  obtain ⟨r, -, ⟨e⟩⟩ := h.sylow_quaternion hJ T
  have : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
  refine ⟨((e.symm (QuaternionGroup.xa 0) : T) : J), ((e.symm (QuaternionGroup.xa 0) : T) : J).2,
    ?_⟩
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, MulEquiv.orderOf_eq,
    QuaternionGroup.orderOf_xa]

theorem fitting_commute {J : Subgroup X} (hJ : CFSG.IsComponent J) {b : X}
    (hb : b ∈ fittingSubgroup X) {a : X} (ha : a ∈ J) : a * b = b * a := by
  have hc := CFSG.ComponentClassification.GeneralizedFitting.fitting_layer_commute X
  rw [← CFSG.layer_eq_componentClassification, h.layer_eq hJ] at hc
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc hb)
    a ha

theorem fitting_orderOf_ne_four {J : Subgroup X} (hJ : CFSG.IsComponent J) {c : X}
    (hc : c ∈ fittingSubgroup X) : orderOf c ≠ 4 := by
  intro hc4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJstar : ∀ x ∈ J, x ∈ generalizedFitting X := fun x hx =>
    Subgroup.mem_sup_right (Assembly.component_le_layer hJ hx)
  by_cases hcJ : c ∈ J
  · have hcard : Nat.card (Subgroup.zpowers (⟨c, hcJ⟩ : J)) = 2 ^ 2 := by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, hc4]
      norm_num
    obtain ⟨T, hT⟩ := (IsPGroup.of_card hcard).exists_le_sylow
    obtain ⟨r, hr, ⟨e⟩⟩ := h.sylow_quaternion hJ T
    have hcT : (⟨c, hcJ⟩ : J) ∈ (T : Subgroup J) := hT (Subgroup.mem_zpowers _)
    have hcen : (⟨⟨c, hcJ⟩, hcT⟩ : (T : Subgroup J)) ∈ Subgroup.center (T : Subgroup J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subtype.ext (h.fitting_commute hJ hc ((g : J).2)))
    have hm : 2 ≤ 2 ^ (r - 2) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 := orderOf_dvd_two_of_mem_center_quaternion hm e hcen
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hc4] at h2
    norm_num at h2
  · obtain ⟨a, haJ, ha4⟩ := h.exists_mem_component_orderOf_eq_four hJ
    have hsq : ∀ x : X, orderOf x = 4 → orderOf (x ^ 2) = 2 := fun x hx => by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [hx]; norm_num), hx]
    have ha2 : a ^ 2 = t := h.eq_of_mem_component hJ (J.pow_mem haJ 2) (hsq a ha4)
    have hc2 : c ^ 2 = t :=
      h.unique _ (Subgroup.mem_sup_left ((fittingSubgroup X).pow_mem hc 2)) (hsq c hc4)
    have hac : (a * c) ^ 2 = 1 := by
      rw [Commute.mul_pow (h.fitting_commute hJ hc haJ), ha2, hc2, ← pow_two, ← h.order,
        pow_orderOf_eq_one]
    have hac1 : a * c ≠ 1 := fun h1 => hcJ (by
      rw [eq_inv_of_mul_eq_one_right h1]
      exact J.inv_mem haJ)
    have hact := h.unique (a * c) ((generalizedFitting X).mul_mem (hJstar a haJ)
      (Subgroup.mem_sup_left hc)) (orderOf_eq_prime hac hac1)
    apply hcJ
    have hca : c = a⁻¹ * t := by rw [← hact, inv_mul_cancel_left]
    rw [hca]
    exact J.mul_mem (J.inv_mem haJ) (h.mem_component hJ)

theorem fittingSubgroup_le {J : Subgroup X} (hJ : CFSG.IsComponent J) :
    fittingSubgroup X ≤ Subgroup.zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (fittingSubgroup X) :=
    CFSG.isPGroup_of_nilpotent_normal _ inferInstance inferInstance h.core
  intro b hb
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h2) ⟨b, hb⟩
  rw [Subgroup.orderOf_mk] at hk
  rcases k with _ | _ | k
  · rw [pow_zero, orderOf_eq_one_iff] at hk
    rw [hk]
    exact Subgroup.one_mem _
  · rw [pow_one] at hk
    rw [h.unique b (Subgroup.mem_sup_left hb) hk]
    exact Subgroup.mem_zpowers t
  · exfalso
    apply h.fitting_orderOf_ne_four hJ ((fittingSubgroup X).pow_mem hb (2 ^ k))
    have h4 : 2 ^ (k + 1 + 1) = 2 ^ k * 4 := by ring
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero)
      (by rw [hk]; exact pow_dvd_pow 2 (by omega)), hk, h4,
      Nat.mul_div_cancel_left _ (by positivity)]

theorem generalizedFitting_eq {J : Subgroup X} (hJ : CFSG.IsComponent J) :
    generalizedFitting X = J := by
  apply le_antisymm
  · exact sup_le ((h.fittingSubgroup_le hJ).trans
      (Subgroup.zpowers_le.mpr (h.mem_component hJ))) (h.layer_eq hJ).le
  · rw [← h.layer_eq hJ]
    exact le_sup_right

theorem centralizer_le {J : Subgroup X} (hJ : CFSG.IsComponent J) :
    Subgroup.centralizer (J : Set X) ≤ J := by
  have hC := CFSG.centralizer_generalizedFitting_le X
  rwa [h.generalizedFitting_eq hJ] at hC

end RankBoundHyp

end CFSG.ProperTwoGeneratedCore.Lemma37
