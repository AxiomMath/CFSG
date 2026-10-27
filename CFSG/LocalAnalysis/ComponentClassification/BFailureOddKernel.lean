module

public import CFSG.LocalAnalysis.ComponentClassification.BFailureOddLowerImage
public import CFSG.LocalAnalysis.ComponentClassification.CentralTwoBInclusion
public import CFSG.GroupTheory.CoprimeQuotientNormalizer

public section

namespace CFSG.ComponentClassification.BFailureOdd

open CFSG CFSG.ComponentClassification.CatalogueBPrimeJoin

theorem exists_pComponent_not_le_of_not_badTwo_le {G : Type*} [Group G] {H B : Subgroup G}
    (h : ¬ (badTwoComponentSubgroup H).map H.subtype ≤ B) :
    ∃ L : Subgroup H, IsPComponent 2 L ∧ ¬ IsQuasisimple L ∧ ¬ L.map H.subtype ≤ B := by
  by_contra hcon
  apply h
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  by_contra hLB
  exact hcon ⟨L, hL.1, hL.2, hLB⟩

theorem le_of_isPerfect_of_le_sup {G : Type*} [Group G] {L B N : Subgroup G} [B.Normal]
    [Group.IsPerfect L] [Group.IsSolvable N] (hL : L ≤ B ⊔ N) : L ≤ B := by
  let φ := QuotientGroup.mk' B
  have hLN : L.map φ ≤ N.map φ := by
    have h := Subgroup.map_mono (f := φ) hL
    rwa [Subgroup.map_sup, (Subgroup.map_eq_bot_iff B).2 (QuotientGroup.ker_mk' B).ge,
      bot_sup_eq] at h
  have : Group.IsSolvable (N.map φ) := Group.isSolvable_of_surjective (φ.subgroupMap_surjective N)
  have : Group.IsSolvable (L.map φ) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLN)
  have : Group.IsPerfect (L.map φ) := Group.IsPerfect.map φ
  by_contra hne
  have hmap : L.map φ ≠ ⊥ := by
    intro h
    apply hne
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  have : Nontrivial (L.map φ) := (Subgroup.nontrivial_iff_ne_bot _).2 hmap
  exact Group.IsPerfect.not_isSolvable (L.map φ) inferInstance

theorem B_failure_solvable_odd_kernel_quasisimple_image {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hNsolv : Group.IsSolvable N) (hNodd : Odd (Nat.card N))
    (hB : CentralTwoBInclusion.Property (G ⧸ N)) {S : Subgroup G} (hS : S ≠ ⊥)
    (hS2 : IsPGroup 2 S)
    (hSB : ¬ (TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G))).map
        (Subgroup.normalizer (S : Set G)).subtype ≤ TwoComponents.badSubgroup G) :
    ∃ L : Subgroup G, L ≤ Subgroup.normalizer (S : Set G) ∧
      CFSG.IsPComponent 2 (L.subgroupOf (Subgroup.normalizer (S : Set G))) ∧
      ¬ CFSG.IsQuasisimple L ∧ ¬ L ≤ TwoComponents.badSubgroup G ∧
      L.map (QuotientGroup.mk' N) ≤
        Subgroup.normalizer ((S.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) ∧
      CFSG.IsComponent ((L.map (QuotientGroup.mk' N)).subgroupOf
        (Subgroup.normalizer ((S.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) :
          Set (G ⧸ N)))) ∧
      Group.IsPerfect L ∧ L ⊓ N ≠ ⊥ ∧ Group.IsSolvable (L ⊓ N : Subgroup G) ∧
      Odd (Nat.card (L ⊓ N : Subgroup G)) ∧ ((L ⊓ N).subgroupOf L).Normal ∧
      ¬ (L ⊓ N).subgroupOf L ≤ Subgroup.center L ∧
      (∃ e : L ⧸ N.subgroupOf L ≃* L.map (QuotientGroup.mk' N),
        ∀ l : L, (e l : G ⧸ N) = QuotientGroup.mk' N l) ∧
      CFSG.IsQuasisimple (L.map (QuotientGroup.mk' N)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN2 : ¬ 2 ∣ Nat.card N := by
    obtain ⟨m, hm⟩ := hNodd
    omega
  set H := Subgroup.normalizer (S : Set G) with hHdef
  set π := QuotientGroup.mk' N with hπdef
  set Ĥ := Subgroup.normalizer ((S.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N)) with hĤdef
  rw [badSubgroup_eq_badTwoComponentSubgroup, badSubgroup_eq_badTwoComponentSubgroup] at hSB
  obtain ⟨L', hL'c, hL'q, hL'B⟩ := exists_pComponent_not_le_of_not_badTwo_le hSB
  set L := L'.map H.subtype with hLdef
  have hLH : L ≤ H := Subgroup.map_subtype_le L'
  have hLL' : L.subgroupOf H = L' :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective L'
  let eL : L' ≃* L := L'.equivMapOfInjective H.subtype H.subtype_injective
  have hLperf : Group.IsPerfect L := by
    have := CatalogueBHeldSmallCore.pComponent_perfect 2 L' hL'c
    exact Group.IsPerfect.ofSurjective (f := eL.toMonoidHom) eL.surjective
  have hLq : ¬ IsQuasisimple L := fun hq =>
    hL'q ((LocalAnalysis.ComponentInitial.isQuasisimple_congr eL).2 hq)
  have hLB : ¬ L ≤ TwoComponents.badSubgroup G := by
    rw [badSubgroup_eq_badTwoComponentSubgroup]
    exact hL'B
  have hHmap : H.map π = Ĥ := GroupTheory.normal_coprime_quotient_normalizer 2 N hN2 S hS2
  have hLĤ : L.map π ≤ Ĥ := hHmap ▸ Subgroup.map_mono hLH
  let f : H →* Ĥ := (MulEquiv.subgroupCongr hHmap).toMonoidHom.comp (π.subgroupMap H)
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr hHmap).surjective.comp (π.subgroupMap_surjective H)
  have hfker : ¬ 2 ∣ Nat.card f.ker := by
    have hle : f.ker.map H.subtype ≤ N := by
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hx
      have h1 : ((f x : Ĥ) : G ⧸ N) = 1 := by
        rw [hx]
        rfl
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hdvd : Nat.card f.ker ∣ Nat.card N := by
      rw [← Subgroup.card_map_of_injective H.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    exact fun h2 => hN2 (h2.trans hdvd)
  have hL'f : IsPComponent 2 (L'.map f) :=
    (prime_complement_quotient_p_component_bijection f hf hfker).1.mapsTo hL'c
  have hmapeq : L'.map f = (L.map π).subgroupOf Ĥ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x : G), ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨l, ⟨x, hx, rfl⟩, hly⟩
      exact ⟨x, hx, Subtype.ext hly⟩
  have hπLc : IsPComponent 2 ((L.map π).subgroupOf Ĥ) := by
    rw [← hmapeq]
    exact hL'f
  have hSπ : S.map π ≠ ⊥ := by
    intro hbot
    rw [Subgroup.map_eq_bot_iff, hπdef, QuotientGroup.ker_mk'] at hbot
    obtain ⟨n, hn⟩ := hS2.exists_card_eq
    have hdvd : Nat.card S ∣ Nat.card N := Subgroup.card_dvd_of_le hbot
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, Subgroup.card_eq_one] at hn
      exact hS hn
    have h2 : 2 ∣ Nat.card S := by
      rw [hn]
      exact dvd_pow_self 2 hn0
    exact hN2 (h2.trans hdvd)
  have hπLq : IsQuasisimple (L.map π) := by
    by_contra hnq
    apply hLB
    have hnq' : ¬ IsQuasisimple ((L.map π).subgroupOf Ĥ) := fun hq =>
      hnq ((LocalAnalysis.ComponentInitial.isQuasisimple_congr
        (Subgroup.subgroupOfEquivOfLe hLĤ)).1 hq)
    have h1 : (L.map π).subgroupOf Ĥ ≤ badTwoComponentSubgroup Ĥ := le_sSup ⟨hπLc, hnq'⟩
    have h2 : L.map π ≤ (badTwoComponentSubgroup Ĥ).map Ĥ.subtype := by
      have h := Subgroup.map_mono (f := Ĥ.subtype) h1
      rwa [Subgroup.subgroupOf_map_subtype, inf_of_le_left hLĤ] at h
    have h3 := hB (S.map π) hSπ (hS2.map π)
    rw [badSubgroup_eq_badTwoComponentSubgroup, badSubgroup_eq_badTwoComponentSubgroup] at h3
    have h4 := odd_quotient_bad_subgroup_lower_image π (QuotientGroup.mk'_surjective N)
      (by rwa [hπdef, QuotientGroup.ker_mk'])
    rw [badSubgroup_eq_badTwoComponentSubgroup, badSubgroup_eq_badTwoComponentSubgroup] at h4
    have h5 : L.map π ≤ (badTwoComponentSubgroup G).map π := h2.trans (h3.trans h4)
    have h6 : L ≤ badTwoComponentSubgroup G ⊔ N := by
      rw [Subgroup.map_le_iff_le_comap, Subgroup.comap_map_eq, hπdef, QuotientGroup.ker_mk'] at h5
      exact h5
    have : (badTwoComponentSubgroup G).Characteristic :=
      (bad_two_component_characteristic_perfect (G := G)).1
    rw [badSubgroup_eq_badTwoComponentSubgroup]
    exact le_of_isPerfect_of_le_sup h6
  have hπLcomp : IsComponent ((L.map π).subgroupOf Ĥ) := by
    refine ⟨(LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hLĤ)).2 hπLq, ?_⟩
    obtain ⟨K, -, hsub, -, -⟩ := hπLc
    exact hsub
  let ψ : L →* L.map π := π.subgroupMap L
  have hψ : Function.Surjective ψ := π.subgroupMap_surjective L
  have hψker : N.subgroupOf L = ψ.ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro hx
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).2 hx)
    · intro hx
      exact (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val hx)
  let e : L ⧸ N.subgroupOf L ≃* L.map π := QuotientGroup.liftEquiv (N.subgroupOf L) hψ hψker
  have he : ∀ l : L, (e l : G ⧸ N) = π l := fun l => rfl
  have hP : IsQuasisimple (L ⧸ N.subgroupOf L) :=
    (LocalAnalysis.ComponentInitial.isQuasisimple_congr e).2 hπLq
  have hAcenter : ¬ N.subgroupOf L ≤ Subgroup.center L := by
    intro hc
    have hq := LocalAnalysis.ComponentInitial.quasisimple_central_extension_derived hc hP
    rw [hLperf.commutator_eq_top] at hq
    exact hLq ((LocalAnalysis.ComponentInitial.isQuasisimple_congr Subgroup.topEquiv).1 hq)
  have hAeq : (L ⊓ N).subgroupOf L = N.subgroupOf L := Subgroup.inf_subgroupOf_left N L
  have hAne : L ⊓ N ≠ ⊥ := by
    intro hbot
    apply hAcenter
    intro x hx
    have hxA : (x : G) ∈ L ⊓ N := ⟨x.2, hx⟩
    rw [hbot, Subgroup.mem_bot] at hxA
    have hx1 : x = 1 := Subtype.ext hxA
    rw [hx1]
    exact Subgroup.one_mem _
  have hAsolv : Group.IsSolvable (L ⊓ N : Subgroup G) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_right)
  have hAodd : Odd (Nat.card (L ⊓ N : Subgroup G)) :=
    hNodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hAnormal : ((L ⊓ N).subgroupOf L).Normal := by
    rw [hAeq]
    infer_instance
  have hAcenter' : ¬ (L ⊓ N).subgroupOf L ≤ Subgroup.center L := by
    rw [hAeq]
    exact hAcenter
  refine ⟨L, hLH, ?_, hLq, hLB, hLĤ, hπLcomp, hLperf, hAne, hAsolv, hAodd, hAnormal, hAcenter',
    ⟨e, he⟩, hπLq⟩
  rw [hLL']
  exact hL'c

end CFSG.ComponentClassification.BFailureOdd
