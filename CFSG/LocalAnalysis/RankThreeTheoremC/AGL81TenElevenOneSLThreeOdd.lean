module

import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81FourSixteenPGroup
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27

open CFSG.Open Subgroup

@[expose] def KFactLThreeOddAutRank : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), L.Normal → ∀ n : ℕ, Odd n →
    Nonempty (↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) →
    ∀ Q : Subgroup Y, IsPGroup 3 Q → Q ⊓ centralizer (L : Set Y) = ⊥ → Open.pRank 3 Q ≤ 2

theorem center_eq_bot_of_odd {n : ℕ} (hn : Odd n) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn0 : n ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hn)
  refine eq_bot_iff.2 fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr
  set u := Units.mk0 r hr0
  have hu3 : u ^ 3 = 1 := Units.ext (by simp [u, hr])
  have hcard : Nat.card (GaloisField 2 n)ˣ = 2 ^ n - 1 := by
    rw [Nat.card_units, GaloisField.card 2 n hn0]
  have h3 : ¬ 3 ∣ 2 ^ n - 1 := by
    obtain ⟨k, rfl⟩ := hn
    intro h
    have h1 : (2 ^ (2 * k + 1) : ℕ) % 3 = 2 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    have h2 : 1 ≤ 2 ^ (2 * k + 1) := Nat.one_le_two_pow
    generalize 2 ^ (2 * k + 1) = m at h h1 h2
    omega
  have hu1 : u = 1 := by
    have hdvd := orderOf_dvd_of_pow_eq_one hu3
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
    · exact orderOf_eq_one_iff.1 h1
    · exact absurd (hcard ▸ h1 ▸ orderOf_dvd_natCard u) h3
  have hr1 : r = 1 := by
    have := congrArg Units.val hu1
    simpa [u] using this
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]

variable {Y : Type*} [Group Y] [Finite Y] {p : ℕ} [hp : Fact p.Prime]

theorem sylow_inf_ne_bot_of_dvd (P : Sylow p Y) {K : Subgroup Y} [K.Normal]
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

theorem exists_mem_centralizer_sylow_of_inf_ne_bot (P : Sylow p Y) (K : Subgroup Y) [K.Normal]
    (hK : (P : Subgroup Y) ⊓ K ≠ ⊥) :
    ∃ z ∈ K, z ∈ centralizer ((P : Subgroup Y) : Set Y) ∧ orderOf z = p := by
  set S₀ := (P : Subgroup Y) ⊓ K
  have hSp : IsPGroup p (P : Subgroup Y) := P.isPGroup'
  have : Group.IsNilpotent (P : Subgroup Y) := hSp.isNilpotent
  have hN : (S₀.subgroupOf P).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hx' : (x : Y) ∈ S₀ := hx
    refine ⟨P.mul_mem (P.mul_mem g.2 x.2) (P.inv_mem g.2), ?_⟩
    exact ‹K.Normal›.conj_mem _ hx'.2 g
  have hne : S₀.subgroupOf P ≠ ⊥ := by
    intro h
    apply hK
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.1⟩ : (P : Subgroup Y)) ∈ S₀.subgroupOf P := hx
    rw [h, mem_bot] at this
    simpa using congrArg Subtype.val this
  have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  set Z₀ := (S₀.subgroupOf P ⊓ center (P : Subgroup Y)).map (P : Subgroup Y).subtype
  have hZ₀p : IsPGroup p Z₀ := (hSp.to_subgroup _).map _
  have hZ₀ : Z₀ ≠ ⊥ := by
    rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hZ₀p
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hZ₀ (Subgroup.eq_bot_of_card_eq Z₀ (by simpa using hk))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p (hk ▸ dvd_pow_self p hk0)
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 x.2
  refine ⟨(x : Y), ?_, ?_, by rw [Subgroup.orderOf_coe, hx]⟩
  · rw [← hyx]
    exact (mem_subgroupOf.1 hy.1).2
  · rw [mem_centralizer_iff]
    intro g hg
    rw [← hyx]
    exact congrArg Subtype.val (mem_center_iff.mp hy.2 ⟨g, hg⟩)

theorem three_le_pRank_centralizer_of_inf_ne_bot {N C : Subgroup Y} [N.Normal] [C.Normal]
    (hpN : p ∣ Nat.card N) (hNC : N ⊓ C = ⊥) (hrk : 3 ≤ Open.pRank p (⊤ : Subgroup Y))
    (hPC : ∀ P : Sylow p Y, (P : Subgroup Y) ⊓ C ≠ ⊥)
    {D : Subgroup Y} (hD : IsElemAbelian p D) (hDc : Nat.card D = p ^ 2) :
    3 ≤ Open.pRank p (centralizer (D : Set Y)) := by
  have hp1 := hp.out.one_lt
  have hDp : IsPGroup p D := IsPGroup.of_card hDc
  obtain ⟨P, hDP⟩ := hDp.exists_le_sylow
  have hPr : Open.pRank p (P : Subgroup Y) = Open.pRank p (⊤ : Subgroup Y) :=
    (CFSG.SectionRank.pRank_sylow P).1
  have hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb => by
    simpa using congrArg Subtype.val (hD.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨z₁, hz₁C, hz₁P, hz₁p⟩ := exists_mem_centralizer_sylow_of_inf_ne_bot P C (hPC P)
  obtain ⟨z₂, hz₂N, hz₂P, hz₂p⟩ :=
    exists_mem_centralizer_sylow_of_inf_ne_bot P N (sylow_inf_ne_bot_of_dvd P hpN)
  have hz₂ : z₂ ∉ zpowers z₁ := by
    intro h
    have hz₂C : z₂ ∈ C := (zpowers_le.2 hz₁C) h
    have : z₂ ∈ N ⊓ C := ⟨hz₂N, hz₂C⟩
    rw [hNC, mem_bot] at this
    rw [this, orderOf_one] at hz₂p
    exact hp1.ne hz₂p
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
    ⟨isMulCommutative_closure hcomm, fun x hx =>
      FourSixteen.pow_eq_one_of_mem_closure hcomm hexp hx⟩
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

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27
