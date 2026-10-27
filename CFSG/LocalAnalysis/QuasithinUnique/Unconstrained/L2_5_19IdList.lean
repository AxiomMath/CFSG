module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma116
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19MinSwap

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section List

variable {G : Type} [Group G] [Finite G]

theorem exists_lemma115Hyp (hq : QTKECore G) {u : G} (hu1 : u ≠ 1) (hu2 : u * u = 1) :
    ∃ (S M : Subgroup G) (z : G), Lemma115Hyp (Subgroup.centralizer ({u} : Set G)) S M z := by
  set H : Subgroup G := Subgroup.centralizer ({u} : Set G) with hH
  have hord : orderOf u = 2 := orderOf_eq_prime (by rw [← sq] at hu2; exact hu2) hu1
  have hB : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  have hB1 : Subgroup.zpowers u ≠ ⊥ := fun h => hu1 (Subgroup.zpowers_eq_bot.mp h)
  have hBH : Subgroup.zpowers u ⊔ Subgroup.centralizer (Subgroup.zpowers u : Set G) ≤ H := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · refine Subgroup.centralizer_le ?_
      simp only [Set.singleton_subset_iff, SetLike.mem_coe]
      exact Subgroup.mem_zpowers u
  have hHB : H ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
    rw [normalizer_zpowers_eq_centralizer hu2]
  obtain ⟨S, hS⟩ := exists_isSylowTwoOf H
  obtain ⟨T, hST, hT⟩ := exists_isSylowTwoOf_of_le (le_top : S ≤ ⊤) hS.isPGroup
  have huS : u ∈ S := by
    have h1 : Subgroup.zpowers u ≤ pCoreOf 2 H := by
      refine le_pCoreOf_of_le_normalizer ?_ ?_ hB
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
      · exact hHB
    exact EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS (h1 (Subgroup.mem_zpowers u))
  have hTbot : T ≠ ⊥ := fun h => hu1 (by
    have : u ∈ T := hST huS
    rw [h] at this
    exact Subgroup.mem_bot.mp this)
  have hZne : centerOf T ≠ ⊥ := by
    have : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).mpr hTbot
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hTp : IsPGroup 2 ↥T := hT.isPGroup
    have := hTp.center_nontrivial
    obtain ⟨c, hc1⟩ := exists_ne (1 : Subgroup.center ↥T)
    intro hbot
    apply hc1
    have hcmem : ((c : ↥T) : G) ∈ centerOf T :=
      ⟨(c : ↥T).2, Subgroup.mem_centralizer_iff.mpr fun y hy =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2 ⟨y, hy⟩)⟩
    rw [hbot, Subgroup.mem_bot] at hcmem
    exact Subtype.ext (Subtype.ext hcmem)
  obtain ⟨z, hzZ, hz1, hz2⟩ :=
    exists_involution_of_isPGroup_ne_bot (hT.isPGroup.to_le inf_le_left) hZne
  have hz2' : z * z = 1 := by rwa [sq] at hz2
  have hzord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hloc : IsTwoLocal (Subgroup.centralizer ({z} : Set G)) :=
    ⟨Subgroup.zpowers z, fun h => hz1 (Subgroup.zpowers_eq_bot.mp h),
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzord]; norm_num),
      (normalizer_zpowers_eq_centralizer hz2').symm⟩
  obtain ⟨M, hzM, hmax⟩ := Finite.exists_le_maximal hloc
  have hM : CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal M :=
    ⟨hmax.prop, fun K hK hMK => (hmax.eq_of_le hK hMK).symm⟩
  exact ⟨S, M, z, lemma116 hq.2.1 hB hB1 hBH hHB hS hT hST hzZ.1 hzZ.2 hz1 hz2 hM hzM⟩

theorem exists_lemma115Cases (hlist : Lemma115_3_List) (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hq : QTKECore G) {u : G} (hu1 : u ≠ 1)
    (hu2 : u * u = 1) {L : Subgroup G} (hL : IsComponentIn L (Subgroup.centralizer ({u} : Set G))) :
    ∃ z : G, Lemma115Cases L z := by
  obtain ⟨S, M, z, h⟩ := exists_lemma115Hyp hq hu1 hu2
  exact ⟨z, hlist G hsimple hnonab hq _ S M z h L hL⟩

end List

end CFSG.QuasithinUnique.Id2519
