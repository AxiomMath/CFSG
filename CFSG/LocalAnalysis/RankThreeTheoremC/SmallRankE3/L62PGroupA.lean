module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralPerfectLifts
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {H : Type} [Group H] [Finite H]

private lemma l62_orderOf_z {z : H} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) : orderOf z = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime hz3 hz1

private lemma l62_zpowers_eq {y c : H} (hy : y ^ 3 = 1) (hc : c ^ 3 = 1)
    (hy1 : y ≠ 1) (hc1 : c ≠ 1) (h : y ∈ zpowers c) : zpowers y = zpowers c := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact Subgroup.eq_of_le_of_card_ge (zpowers_le.2 h) (by
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hy hy1, orderOf_eq_prime hc hc1])

theorem l62_z_mem_of_normal {S : Subgroup H} (hS : IsPGroup 3 S) {z : H} (hz1 : z ≠ 1)
    (hz3 : z ^ 3 = 1)
    (hgen : ∀ w ∈ S, (∀ g ∈ S, g * w = w * g) → w ^ 3 = 1 → w ∈ zpowers z)
    {N : Subgroup H} (hNS : N ≤ S) (hN : ∀ g ∈ S, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hne : N ≠ ⊥) :
    z ∈ N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsNilpotent ↥S := hS.isNilpotent
  have hnorm : (N.subgroupOf S).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hN g g.2 n hn⟩
  have hHne : N.subgroupOf S ≠ ⊥ := by
    obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    intro hbot
    apply ht1
    have hmem : (⟨t, hNS t.2⟩ : ↥S) ∈ N.subgroupOf S := t.2
    rw [hbot, Subgroup.mem_bot] at hmem
    have h2 : ((⟨t, hNS t.2⟩ : ↥S) : H) = ((1 : ↥S) : H) := congrArg Subtype.val hmem
    exact Subtype.ext h2
  have hW : N.subgroupOf S ⊓ Subgroup.center ↥S ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hHne
  set W : Subgroup ↥S := N.subgroupOf S ⊓ Subgroup.center ↥S
  have hWp : IsPGroup 3 W := hS.to_subgroup W
  haveI : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).2 hW
  obtain ⟨m, hm, hmcard⟩ := hWp.nontrivial_iff_card.mp inferInstance
  have hdvdW : 3 ∣ Nat.card W := hmcard ▸ dvd_pow_self 3 hm.ne'
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := W) 3 hdvdW
  set u : H := ((w : ↥S) : H)
  have hu_ord : orderOf u = 3 :=
    (Subgroup.orderOf_coe _).trans ((Subgroup.orderOf_coe _).trans hw)
  have hup : u ^ 3 = 1 := by
    rw [← hu_ord]
    exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hu_ord
    exact Nat.prime_three.one_lt.ne hu_ord
  have huC : ∀ g ∈ S, g * u = u * g := fun g hg =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp w.2.2 ⟨g, hg⟩)
  have hmem : u ∈ zpowers z := hgen u (w : ↥S).2 huC hup
  have heq : zpowers u = zpowers z := l62_zpowers_eq hup hz3 hu1 hz1 hmem
  have hzu : z ∈ zpowers u := by
    rw [heq]
    exact mem_zpowers z
  have huN : u ∈ N := w.2.1
  exact zpowers_le.mpr huN hzu

theorem l62_comm_mem_zpowers {S : Subgroup H} (hS : IsPGroup 3 S) {z : H} (hzS : z ∈ S)
    (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) (hzc : ∀ g ∈ S, g * z = z * g)
    (hgen : ∀ w ∈ S, (∀ g ∈ S, g * w = w * g) → w ^ 3 = 1 → w ∈ zpowers z)
    {U : Subgroup H} (hUS : U ≤ S) (hUn : ∀ g ∈ S, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hUc : Nat.card U = 3 ^ 2) :
    ∀ g ∈ S, ∀ u ∈ U, g * u * g⁻¹ * u⁻¹ ∈ zpowers z := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU1 : U ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hUc
    have : 1 < 3 ^ 2 := by norm_num
    omega
  have hzU : z ∈ U := l62_z_mem_of_normal hS hz1 hz3 hgen hUS hUn hU1
  have hzcard : Nat.card (zpowers z) = 3 := by
    rw [Nat.card_zpowers, l62_orderOf_z hz3 hz1]
  have hAU : zpowers z ≤ U := zpowers_le.mpr hzU
  haveI hAn : ((zpowers z).subgroupOf S).Normal := by
    refine Subgroup.normal_of_le_center ?_
    intro a ha
    rw [Subgroup.mem_subgroupOf, mem_zpowers_iff] at ha
    obtain ⟨n, hn⟩ := ha
    rw [Subgroup.mem_center_iff]
    intro t
    apply Subtype.ext
    show (t : H) * (a : H) = (a : H) * t
    rw [← hn]
    exact (Commute.zpow_right (show Commute (t : H) z from hzc t t.2) n).eq
  haveI hCn : (U.subgroupOf S).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hUn g g.2 n hn⟩
  have hAC : (zpowers z).subgroupOf S < U.subgroupOf S := by
    refine lt_of_le_of_ne (fun a ha => hAU ha) fun heq => ?_
    have h1 : Nat.card ((zpowers z).subgroupOf S) = Nat.card U := by
      rw [heq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUS).toEquiv
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hAU.trans hUS)).toEquiv, hzcard, hUc] at h1
    have : 3 < 3 ^ 2 := by norm_num
    omega
  obtain ⟨b, -, -, -, B, -, hAB, hBC, -, -, hcomm⟩ :=
    CFSG.SectionRank.Ccomm.exists_central_extension hS hAC
  have hBeq : B = U.subgroupOf S := by
    refine Subgroup.eq_of_le_of_card_ge hBC ?_
    have hcardC : Nat.card (U.subgroupOf S) = 3 ^ 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUS).toEquiv, hUc]
    obtain ⟨j, hj⟩ := (hS.to_subgroup B).exists_card_eq
    have hlt : Nat.card ((zpowers z).subgroupOf S) < Nat.card B :=
      Subgroup.card_lt_of_lt hAB
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hAU.trans hUS)).toEquiv, hzcard, hj] at hlt
    have hj2 : 2 ≤ j := by
      by_contra hj'
      have hj1 : j ≤ 1 := by omega
      have h2 : 3 ^ j ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj1
      rw [pow_one] at h2
      omega
    rw [hcardC, hj]
    exact Nat.pow_le_pow_right (by norm_num) hj2
  intro g hg u hu
  have hmem : (⟨u, hUS hu⟩ : ↥S) ∈ B := by
    rw [hBeq]
    exact hu
  have h1 := hcomm _ hmem ⟨g, hg⟩
  rw [Subgroup.mem_subgroupOf] at h1
  have h2 : g * u * g⁻¹ * u⁻¹ = (u * g * u⁻¹ * g⁻¹)⁻¹ := by group
  rw [h2]
  exact (zpowers z).inv_mem (by simpa [commutatorElement_def] using h1)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
