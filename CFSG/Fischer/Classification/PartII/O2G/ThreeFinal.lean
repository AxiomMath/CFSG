module

public import CFSG.Fischer.Classification.PartII.O2G.ThreeRel
public import CFSG.Fischer.Classification.PartII.O2Input

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer LocalU O2Twin O2G

theorem o2_twin_le_four {G : Type} [Group G] {D : Set G} (hH : Hyp G D)
    (hna : NonabelianCommutator G) {d : G} (hd : d ∈ D)
    (h2 : HasNormalPSubgroup 2 (LocalQuotient D d)) {a : G} (ha : a ∈ LocalClass D d) :
    {b | LocalU.IsTwin (LocalClass D d) a b}.ncard ≤ 4 := by
  have hP := hH.pair
  have hZ := hH.center
  have hS := hH.simple
  have := Pair.finite hP
  change (twinClass (LocalClass D d) a).ncard ≤ 4
  obtain ⟨c, hc, hca⟩ := Pair.exists_not_commute_of_mem_localClass hP hZ hS hd ha
  obtain ⟨x, y, hxy, hne⟩ := exists_isTwin_ne hP hZ hS hna hd h2
  have hev := even_ncard_twinClass hP hZ hS hd hxy hne ha
  have hpos : 0 < (twinClass (LocalClass D d) a).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 ⟨a, self_mem_twinClass ha⟩
  have h1 : 1 < (twinClass (LocalClass D d) a).ncard := by
    obtain ⟨m, hm⟩ := hev
    omega
  obtain ⟨a', ha', hne'⟩ := Set.exists_ne_of_one_lt_ncard h1 a
  exact ncard_twinClass_le_four hP hZ hS hd ha hc (fun e => hca e.symm)
    (eq_empty_of_sprod_eq_one hP hZ hS hd ha ha' hne')

theorem o2_O2 {G : Type} [Group G] {D : Set G} (hH : Hyp G D) (hna : NonabelianCommutator G)
    (hs : ¬ IsSymplecticType D) {d : G} (hd : d ∈ D)
    (h2 : HasNormalPSubgroup 2 (LocalQuotient D d)) {a : G} (ha : a ∈ LocalClass D d) :
    (twinClass (LocalClass D d) a).ncard = 4 := by
  rcases o2_four_or_sixteen_le hH hna hs hd h2 ha with h | h
  · exact h
  · have := o2_twin_le_four hH hna hd h2 ha
    change (twinClass (LocalClass D d) a).ncard ≤ 4 at this
    change 16 ≤ (twinClass (LocalClass D d) a).ncard at h
    omega

theorem o2TwinFourInput : O2TwinFourInput :=
  fun _ _ _ _ hH hna hs _ hd _ h2 _ ha => o2_O2 hH hna hs hd h2 ha

end CFSG.Fischer.Classification
