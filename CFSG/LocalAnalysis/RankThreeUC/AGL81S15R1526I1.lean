module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Open.LocalVocabulary
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open Subgroup KFactsPair

section Row28SylowPair

variable {X : Type} [Group X] [Finite X]

theorem exists_sylow_central_pair_aux1 {H : Subgroup X} (hH : IsPGroup 3 H) {x : X} (hx : x ∈ H) :
    ∃ k : ℕ, orderOf x = 3 ^ k := by
  obtain ⟨k, hk⟩ := hH ⟨x, hx⟩
  have hdvd : orderOf (⟨x, hx⟩ : ↥H) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  exact ⟨j, by rw [← Subgroup.orderOf_mk x hx]; exact hj⟩

theorem exists_sylow_central_pair_aux2 {Q Q' K : Subgroup X}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q K) (hQ' : CFSG.ABGLocalTools.IsSylowOf 3 Q' K) :
    ∃ k ∈ K, Q' = conjSub k Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := hQ.exists_sylow_eq_subgroupOf
  obtain ⟨S', hS'⟩ := hQ'.exists_sylow_eq_subgroupOf
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥K) S S'
  have key : ∀ a ∈ (S : Subgroup ↥K), g * a * g⁻¹ ∈ (S' : Subgroup ↥K) := by
    intro a ha
    rw [← hg, Sylow.smul_def]
    exact ⟨a, ha, rfl⟩
  have hle : conjSub (g : X) Q ≤ Q' := by
    rintro _ ⟨q, hq, rfl⟩
    have hq' : (⟨q, hQ.le hq⟩ : ↥K) ∈ (S : Subgroup ↥K) := by
      rw [hS]; exact Subgroup.mem_subgroupOf.mpr hq
    have h2 := key _ hq'
    rw [hS'] at h2
    simpa [MulAut.conj_apply] using Subgroup.mem_subgroupOf.mp h2
  have hcard : Nat.card Q' ≤ Nat.card (conjSub (g : X) Q) := by
    rw [hQ'.card_eq, conjSub, Subgroup.card_map_of_injective (MulAut.conj (g : X)).injective,
      hQ.card_eq]
  exact ⟨g, g.2, (Subgroup.eq_of_le_of_card_ge hle hcard).symm⟩

theorem exists_sylow_central_pair_aux3 {P N : Subgroup X} (hP : IsPGroup 3 P) (hNP : N ≤ P)
    (hN : N ≠ ⊥) (hnorm : ∀ y ∈ P, ∀ n ∈ N, y * n * y⁻¹ ∈ N) :
    ∃ b ∈ N, orderOf b = 3 ∧ ∀ y ∈ P, b * y = y * b := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsNilpotent ↥P := hP.isNilpotent
  haveI hNn : (N.subgroupOf P).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hnorm g g.2 n hn⟩
  have hN' : N.subgroupOf P ≠ ⊥ := by
    intro h
    apply hN
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hNP hx⟩ : ↥P) ∈ N.subgroupOf P := Subgroup.mem_subgroupOf.mpr hx
    rw [h, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
  obtain ⟨⟨c, hc⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hN')
  obtain ⟨hcN, hcZ⟩ := Subgroup.mem_inf.mp hc
  have hcN' : (c : X) ∈ N := Subgroup.mem_subgroupOf.mp hcN
  have hc1' : (c : X) ≠ 1 := fun h => hc1 (Subtype.ext (Subtype.ext h))
  obtain ⟨k, hk⟩ := exists_sylow_central_pair_aux1 hP c.2
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hc1' (orderOf_eq_one_iff.mp (by simpa using hk))
  have hdvd : 3 ∣ orderOf (c : X) := by
    rw [hk]; exact dvd_pow_self 3 hk0
  refine ⟨(c : X) ^ (orderOf (c : X) / 3), N.pow_mem hcN' _, ?_, fun y hy => ?_⟩
  · exact orderOf_pow_orderOf_div (by rw [hk]; positivity) hdvd
  · have hcomm : (⟨y, hy⟩ : ↥P) * c = c * ⟨y, hy⟩ :=
      (Subgroup.mem_center_iff.mp hcZ ⟨y, hy⟩)
    have h2 : Commute (c : X) y := (congrArg Subtype.val hcomm).symm
    exact Commute.pow_left h2 _

theorem exists_sylow_central_pair_aux4 {P A : Subgroup X} (hP : IsPGroup 3 P) (hAP : A ≤ P)
    (hA3 : Nat.card A = 3) (hnorm : ∀ y ∈ P, ∀ a ∈ A, y * a * y⁻¹ ∈ A) :
    ∀ a ∈ A, ∀ y ∈ P, a * y = y * a := by
  have hA0 : A ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hA3
    omega
  obtain ⟨b, hbA, hb3, hbc⟩ := exists_sylow_central_pair_aux3 hP hAP hA0 hnorm
  have heq : Subgroup.zpowers b = A :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbA)
      (by rw [Nat.card_zpowers, hb3, hA3])
  intro a ha y hy
  rw [← heq] at ha
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  exact Commute.zpow_left (hbc y hy) n

theorem exists_sylow_central_pair_aux5 {H : Subgroup X} (hH : Nat.card H = 3) {x : X}
    (hx : x ∈ H) : x ^ 3 = 1 := by
  have h := pow_card_eq_one' (G := ↥H) (x := (⟨x, hx⟩ : ↥H))
  rw [hH] at h
  simpa using congrArg Subtype.val h

end Row28SylowPair

end CFSG.LocalAnalysis.RankThreeUC.S15
