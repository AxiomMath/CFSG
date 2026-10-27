module

public import CFSG.ClassicalInvolution.Q3.Q3TNMain

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.LocalCores
open CFSG.ComponentClassification
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y]

theorem odd_card_inf_of_not_mem {L : Subgroup Y} {z : Y} (hz : IsClassicalMember3 L z)
    {N : Subgroup Y} (hzN : z ∉ N) : Odd (Nat.card (L ⊓ N : Subgroup Y)) := by
  by_contra hev
  have h2 : 2 ∣ Nat.card (L ⊓ N : Subgroup Y) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hw' : orderOf (w : Y) = 2 := by rw [Subgroup.orderOf_coe]; exact hw
  exact hzN (hz.eq_of_orderOf_eq_two w.2.1 hw' ▸ w.2.2)

theorem isClassicalMember3_map_centralizer (hO : classicalInvolutionOddCore Y = ⊥) {z : Y}
    {L : Subgroup Y} (hz : IsClassicalMember3 L z) {T : Subgroup Y} [T.Normal]
    (hT : IsComponentOf T ⊤) (hTL : T ⊔ L = ⊤)
    (hTz : ¬ T ≤ Subgroup.centralizer ({z} : Set Y)) :
    IsClassicalMember3 (L.map (QuotientGroup.mk' (Subgroup.centralizer (T : Set Y))))
      (QuotientGroup.mk' (Subgroup.centralizer (T : Set Y)) z) := by
  set D := Subgroup.centralizer (T : Set Y) with hD
  set π := QuotientGroup.mk' D with hπ
  have hzD : z ∉ D := fun h => hTz fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp h t ht)
  have hcenD : Subgroup.center Y ≤ D := fun c hc =>
    Subgroup.mem_centralizer_iff.mpr fun t _ => (Subgroup.mem_center_iff.mp hc t)
  refine ⟨?_, Subgroup.mem_map_of_mem _ hz.mem, ?_, ?_⟩
  · have h1 : π z ≠ 1 := fun h => hzD ((QuotientGroup.eq_one_iff z).mp h)
    have h2 : π z ^ 2 = 1 := by rw [← map_pow, hz.sq_eq_one, map_one]
    exact orderOf_eq_prime h2 h1
  · set π' := QuotientGroup.mk' (Subgroup.center Y) with hπ'
    set Ct : Subgroup Y := (Subgroup.centralizer ({π' z} : Set (Y ⧸ Subgroup.center Y))).comap π'
      with hCt
    have hCC : Subgroup.centralizer ({z} : Set Y) ≤ Ct := fun c hc => by
      rw [hCt, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.mp hc]
    have hsub : IsSubnormal L Ct :=
      isSubnormal_trans hz.subnormal
        (IsSubnormal.step hCC (centralizer_subgroupOf_normal_comap_center z)
          (IsSubnormal.refl Ct))
    have hP : (Subgroup.centralizer ({π z} : Set (Y ⧸ D))).comap π = Ct := by
      ext y
      simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, hCt]
      constructor
      · intro h
        have hy : y ∈ T ⊔ L := hTL ▸ Subgroup.mem_top y
        obtain ⟨t, ht, l, hl, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
        have hlz : l * z = z * l := hz.commute_involution hl
        have hcomm : ⁅t, z⁆ ∈ Subgroup.center Y := by
          refine inf_centralizer_le_center hO hz hT hTL hTz ⟨?_, ?_⟩
          · have h1 := T.mul_mem ht ((inferInstance : T.Normal).conj_mem _ (T.inv_mem ht) z)
            rw [commutatorElement_def]
            simpa [mul_assoc] using h1
          · have h' : π t * π l * π z = π z * (π t * π l) := by rw [← map_mul]; exact h
            have hlz' : π l * π z = π z * π l := by rw [← map_mul, ← map_mul, hlz]
            have htz : π t * π z = π z * π t := by
              apply mul_right_cancel (b := π l)
              calc π t * π z * π l = π t * (π z * π l) := mul_assoc _ _ _
                _ = π t * π l * π z := by rw [← hlz', ← mul_assoc]
                _ = π z * π t * π l := by rw [h', ← mul_assoc]
            have hq : π ⁅t, z⁆ = 1 := by
              rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
              exact htz
            exact (QuotientGroup.eq_one_iff _).mp hq
        have h1 : π' t * π' z = π' z * π' t := by
          rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
          exact (QuotientGroup.eq_one_iff _).mpr hcomm
        have h2 : π' l * π' z = π' z * π' l := by rw [← map_mul, ← map_mul, hlz]
        rw [map_mul, mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
      · intro h
        have h0 : π' ⁅y, z⁆ = 1 := by
          rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
          exact h
        have h1 : ⁅y, z⁆ ∈ Subgroup.center Y := (QuotientGroup.eq_one_iff _).mp h0
        have h2 : π ⁅y, z⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr (hcenD h1)
        rwa [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    have := Components.chain_map π (hP ▸ hsub)
    rwa [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at this
  · obtain ⟨e⟩ := hz.nonempty_equiv
    have hker : Odd (Nat.card (π.subgroupMap L).ker) := by
      have hinj : Nat.card (π.subgroupMap L).ker = Nat.card (L ⊓ D : Subgroup Y) := by
        refine Nat.card_congr ⟨fun x => ⟨x.1.1, x.1.2, ?_⟩, fun x => ⟨⟨x.1, x.2.1⟩, ?_⟩,
          fun _ => rfl, fun _ => rfl⟩
        · have := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
          exact (QuotientGroup.eq_one_iff _).mp this
        · exact MonoidHom.mem_ker.mpr (Subtype.ext ((QuotientGroup.eq_one_iff _).mpr x.2.2))
      rw [hinj]
      exact odd_card_inf_of_not_mem hz hzD
    exact ⟨(OddKernel.coreQuotientEquiv (π.subgroupMap L) (MonoidHom.subgroupMap_surjective _ L)
      hker).symm.trans e⟩

theorem centralizer_map_eq_bot (hO : classicalInvolutionOddCore Y = ⊥) {z : Y} {L : Subgroup Y}
    (hz : IsClassicalMember3 L z) {T : Subgroup Y} [T.Normal] (hT : IsComponentOf T ⊤)
    (hTL : T ⊔ L = ⊤) (hTz : ¬ T ≤ Subgroup.centralizer ({z} : Set Y)) :
    Subgroup.centralizer (T.map (QuotientGroup.mk' (Subgroup.centralizer (T : Set Y))) :
      Set (Y ⧸ Subgroup.centralizer (T : Set Y))) = ⊥ := by
  set D := Subgroup.centralizer (T : Set Y) with hD
  set π := QuotientGroup.mk' D with hπ
  refine eq_bot_iff.mpr fun w hw => ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective D w
  have hyc : y ∈ D := by
    refine mem_centralizer_of_commutator_mem_center hT fun t ht => ?_
    refine inf_centralizer_le_center hO hz hT hTL hTz ⟨?_, ?_⟩
    · have h1 := T.mul_mem ht ((inferInstance : T.Normal).conj_mem _ (T.inv_mem ht) y)
      rw [commutatorElement_def]
      simpa [mul_assoc] using h1
    · have h1 : π t * π y = π y * π t := Subgroup.mem_centralizer_iff.mp hw (π t) ⟨t, ht, rfl⟩
      have h2 : π ⁅t, y⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact h1
      exact (QuotientGroup.eq_one_iff _).mp h2
  exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff y).mpr hyc)

omit [Finite Y] in
theorem isComponentOf_map_centralizer {T : Subgroup Y} [T.Normal] (hT : IsComponentOf T ⊤) :
    IsComponentOf (T.map (QuotientGroup.mk' (Subgroup.centralizer (T : Set Y)))) ⊤ := by
  refine LocalComponents.image hT _ (QuotientGroup.mk'_surjective _) fun hle => ?_
  rw [QuotientGroup.ker_mk'] at hle
  exact not_forall_commute_of_isComponent hT fun x hx a ha =>
    Subgroup.mem_centralizer_iff.mp (hle hx) a ha

theorem oddCore_quotient_centralizer_eq_bot (hO : classicalInvolutionOddCore Y = ⊥) {z : Y}
    {L : Subgroup Y} (hz : IsClassicalMember3 L z) {T : Subgroup Y} [T.Normal]
    (hT : IsComponentOf T ⊤) (hTL : T ⊔ L = ⊤) (hTz : ¬ T ≤ Subgroup.centralizer ({z} : Set Y)) :
    classicalInvolutionOddCore (Y ⧸ Subgroup.centralizer (T : Set Y)) = ⊥ := by
  have hT' := isComponentOf_map_centralizer hT
  rcases LocalComponents.normal_contains_or_commutes _
      (classicalInvolutionOddCore (Y ⧸ Subgroup.centralizer (T : Set Y))) hT' with h | h
  · exfalso
    apply Q3B.not_isSolvable_of_isComponentOf hT'
    refine CFSG.FeitThompson.isSolvable_of_odd_natCard _
      ((OddCore.odd_card (Y ⧸ Subgroup.centralizer (T : Set Y))).of_dvd_nat ?_)
    exact Subgroup.card_dvd_of_le h
  · rw [eq_bot_iff, ← centralizer_map_eq_bot hO hz hT hTL hTz,
      ← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact h

end CFSG.ClassicalInvolution.Q3.Q3T
