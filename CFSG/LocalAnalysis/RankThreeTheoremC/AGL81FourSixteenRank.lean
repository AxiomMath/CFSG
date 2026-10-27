module

import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81FourSixteenPGroup
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.FourSixteen

open CFSG.Open Subgroup

variable {Y : Type*} [Group Y] [Finite Y] {p : ℕ} [hp : Fact p.Prime]

private theorem sylow_inf_ne_bot (P : Sylow p Y) {K : Subgroup Y} [K.Normal]
    (hKp : p ∣ Nat.card K) : (P : Subgroup Y) ⊓ K ≠ ⊥ := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hKp
  have hxp : IsPGroup p (zpowers (x : Y)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx, pow_one]
  obtain ⟨T, hT⟩ := hxp.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Y P T
  have hxg := hT (mem_zpowers (x : Y))
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxg
  have hxg' : g⁻¹ * (x : Y) * g ∈ (P : Subgroup Y) := by
    simpa [MulAut.smul_def, mul_assoc] using hxg
  intro hbot
  have hK : g⁻¹ * (x : Y) * g ∈ K := by simpa using ‹K.Normal›.conj_mem (x : Y) x.2 g⁻¹
  have h1 : g⁻¹ * (x : Y) * g ∈ (P : Subgroup Y) ⊓ K := ⟨hxg', hK⟩
  rw [hbot, Subgroup.mem_bot] at h1
  have h2 : (x : Y) = 1 := by
    have := congrArg (fun y => g * y * g⁻¹) h1
    simpa [mul_assoc] using this
  rw [show x = 1 from Subtype.ext h2, orderOf_one] at hx
  exact hp.out.one_lt.ne hx

private theorem inf_centralizer_ne_bot' {S S₀ : Subgroup Y} (hSp : IsPGroup p S) (hS₀S : S₀ ≤ S)
    (hn : S ≤ normalizer (S₀ : Set Y)) (hS₀1 : S₀ ≠ ⊥) :
    S₀ ⊓ centralizer (S : Set Y) ≠ ⊥ := by
  have : Group.IsNilpotent S := hSp.isNilpotent
  have hN : (S₀.subgroupOf S).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have := (mem_normalizer_iff.mp (hn g.2) x).mp hx
    simpa [mem_subgroupOf] using this
  have hne : S₀.subgroupOf S ≠ ⊥ := by
    intro h
    apply hS₀1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hS₀S hx⟩ : S) ∈ S₀.subgroupOf S := hx
    rw [h, mem_bot] at this
    simpa using congrArg Subtype.val this
  obtain ⟨z, hz1⟩ := (ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  intro hbot
  apply hz1
  have hzS₀ : ((z : S) : Y) ∈ S₀ := (mem_inf.1 z.2).1
  have hzc : ((z : S) : Y) ∈ centralizer (S : Set Y) := by
    rw [mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp (mem_inf.1 z.2).2 ⟨y, hy⟩)
  have : ((z : S) : Y) ∈ S₀ ⊓ centralizer (S : Set Y) := ⟨hzS₀, hzc⟩
  rw [hbot, mem_bot] at this
  exact Subtype.ext (Subtype.ext this)

private theorem le_normalizer_inf (P : Subgroup Y) (K : Subgroup Y) [K.Normal] :
    P ≤ normalizer ((P ⊓ K : Subgroup Y) : Set Y) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨P.mul_mem (P.mul_mem hg h1) (P.inv_mem hg), ‹K.Normal›.conj_mem h h2 g⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := P.mul_mem (P.mul_mem (P.inv_mem hg) h1) hg
      simpa [mul_assoc] using this
    · have := ‹K.Normal›.conj_mem _ h2 g⁻¹
      simpa [mul_assoc] using this

private theorem exists_orderOf_eq {X : Subgroup Y} (hX : IsPGroup p X) (h : X ≠ ⊥) :
    ∃ z ∈ X, orderOf z = p := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hX
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact h (Subgroup.eq_bot_of_card_eq X (by simpa using hk))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p (hk ▸ dvd_pow_self p hk0)
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe, hx]⟩

theorem three_le_pRank_centralizer_of_heis (hp2 : p ≠ 2) {N C : Subgroup Y} [N.Normal]
    [C.Normal] (hpN : p ∣ Nat.card N) (hNC : ¬ p ∣ Nat.card (N ⊓ C : Subgroup Y))
    (hrk : 3 ≤ Open.pRank p (⊤ : Subgroup Y))
    (hheis : ∀ E : Subgroup Y, Nat.card E = p ^ 3 → (∀ e ∈ E, e ^ p = 1) →
      (∃ a ∈ E, ∃ b ∈ E, a * b ≠ b * a) → E ⊓ C ≠ ⊥)
    {D : Subgroup Y} (hD : IsElemAbelian p D) (hDc : Nat.card D = p ^ 2) :
    3 ≤ Open.pRank p (centralizer (D : Set Y)) := by
  have hp1 := hp.out.one_lt
  have hDp : IsPGroup p D := IsPGroup.of_card hDc
  obtain ⟨P, hDP⟩ := hDp.exists_le_sylow
  have hPr : Open.pRank p (P : Subgroup Y) = Open.pRank p (⊤ : Subgroup Y) :=
    (CFSG.SectionRank.pRank_sylow P).1
  have hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb => by
    simpa using congrArg Subtype.val (hD.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  by_cases hPC : (P : Subgroup Y) ⊓ C = ⊥
  ·
    obtain ⟨A, hAP, hA, hAc⟩ := CFSG.SectionRank.exists_pRank hp1 (P : Subgroup Y)
    have hAD : A ≤ centralizer (D : Set Y) := by
      intro a ha
      rw [mem_centralizer_iff]
      intro d hd
      by_contra hne
      obtain ⟨E, hEP, hEc, hEe, hEn⟩ := exists_heis_of_not_commute hp2 P.isPGroup' (hDP hd)
        (hAP ha) (hD.2 d hd) (hA.2 a ha) hne
      refine hheis E hEc hEe hEn (eq_bot_iff.2 fun g hg => ?_)
      rw [← hPC]
      exact ⟨hEP hg.1, hg.2⟩
    calc 3 ≤ Open.pRank p (P : Subgroup Y) := hPr ▸ hrk
      _ ≤ Open.pRank p (centralizer (D : Set Y)) := CFSG.SectionRank.le_pRank hp1 hAD hA hAc
  have hPN : (P : Subgroup Y) ⊓ N ≠ ⊥ := sylow_inf_ne_bot P hpN
  have hcen : ∀ (K : Subgroup Y) [K.Normal], (P : Subgroup Y) ⊓ K ≠ ⊥ →
      ∃ z ∈ K, z ∈ centralizer ((P : Subgroup Y) : Set Y) ∧ orderOf z = p := by
    intro K _ hK
    have h1 := inf_centralizer_ne_bot' P.isPGroup' inf_le_left (le_normalizer_inf _ K) hK
    obtain ⟨z, hz, hzp⟩ := exists_orderOf_eq (P.isPGroup'.to_le (inf_le_left.trans inf_le_left))
      h1
    exact ⟨z, hz.1.2, hz.2, hzp⟩
  obtain ⟨z₁, hz₁C, hz₁P, hz₁p⟩ := hcen C hPC
  obtain ⟨z₂, hz₂N, hz₂P, hz₂p⟩ := hcen N hPN
  have hz₂ : z₂ ∉ zpowers z₁ := by
    intro h
    have hz₂C : z₂ ∈ C := (zpowers_le.2 hz₁C) h
    exact hNC (hz₂p ▸ Subgroup.orderOf_dvd_natCard _ ⟨hz₂N, hz₂C⟩)
  by_cases hzD : z₁ ∈ D ∧ z₂ ∈ D
  ·
    set H := D ⊓ centralizer ((P : Subgroup Y) : Set Y)
    have hlt : zpowers z₁ < H := by
      refine lt_of_le_of_ne (zpowers_le.2 ⟨hzD.1, hz₁P⟩) fun h => hz₂ ?_
      rw [h]
      exact ⟨hzD.2, hz₂P⟩
    have hc1 := Subgroup.card_lt_of_lt hlt
    rw [Nat.card_zpowers, hz₁p] at hc1
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 (hDp.to_le (inf_le_left : H ≤ D))
    have hdvd : Nat.card H ∣ p ^ 2 := hDc ▸ Subgroup.card_dvd_of_le inf_le_left
    rw [hj] at hdvd hc1
    have hj2 : j ≤ 2 := (Nat.pow_dvd_pow_iff_le_right hp1).1 hdvd
    have hj1 : 1 < j := (Nat.pow_lt_pow_iff_right hp1).1 (by simpa using hc1)
    have hHD : H = D := Subgroup.eq_of_le_of_card_ge inf_le_left (by
      rw [hDc, hj, show j = 2 by omega])
    have hPD : (P : Subgroup Y) ≤ centralizer (D : Set Y) := by
      intro g hg
      rw [mem_centralizer_iff]
      intro d hd
      rw [← hHD] at hd
      exact ((mem_centralizer_iff.1 hd.2) g hg).symm
    calc 3 ≤ Open.pRank p (P : Subgroup Y) := hPr ▸ hrk
      _ ≤ Open.pRank p (centralizer (D : Set Y)) := CFSG.SectionRank.pRank_mono hp1 hPD
  obtain ⟨z, hzP, hzp, hzD'⟩ : ∃ z, z ∈ centralizer ((P : Subgroup Y) : Set Y) ∧
      orderOf z = p ∧ z ∉ D := by
    by_cases h1 : z₁ ∈ D
    · exact ⟨z₂, hz₂P, hz₂p, fun h2 => hzD ⟨h1, h2⟩⟩
    · exact ⟨z₁, hz₁P, hz₁p, h1⟩
  have hzd : ∀ d ∈ D, d * z = z * d := fun d hd => (mem_centralizer_iff.1 hzP d (hDP hd))
  set s : Set Y := (D : Set Y) ∪ {z}
  have hcomm : s.Pairwise Commute := by
    rintro a (ha | rfl) b (hb | rfl) -
    · exact hDcomm a ha b hb
    · exact hzd a ha
    · exact (hzd b hb).symm
    · exact Commute.refl _
  have hexp : ∀ a ∈ s, a ^ p = 1 := by
    rintro a (ha | rfl)
    · exact hD.2 a ha
    · rw [← hzp, pow_orderOf_eq_one]
  set D' := closure s
  have hD'e : IsElemAbelian p D' :=
    ⟨isMulCommutative_closure hcomm, fun x hx => pow_eq_one_of_mem_closure hcomm hexp hx⟩
  have hD'C : D' ≤ centralizer (D : Set Y) := by
    rw [closure_le]
    rintro a (ha | rfl)
    · exact mem_centralizer_iff.2 fun d hd => hDcomm d hd a ha
    · exact mem_centralizer_iff.2 fun d hd => hzd d hd
  have hDD' : D < D' := by
    refine lt_of_le_of_ne (fun d hd => subset_closure (Or.inl hd)) fun h => hzD' ?_
    rw [h]
    exact subset_closure (Or.inr rfl)
  have hD'p : IsPGroup p D' := fun x => ⟨1, Subtype.ext (by simpa using hD'e.2 _ x.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hD'p
  have hlt := Subgroup.card_lt_of_lt hDD'
  rw [hDc, hk] at hlt
  have hk3 : 3 ≤ k := by
    have := (Nat.pow_lt_pow_iff_right hp1).1 hlt
    omega
  exact hk3.trans (CFSG.SectionRank.le_pRank hp1 hD'C hD'e hk)

end CFSG.LocalAnalysis.RankThreeTheoremC.FourSixteen
