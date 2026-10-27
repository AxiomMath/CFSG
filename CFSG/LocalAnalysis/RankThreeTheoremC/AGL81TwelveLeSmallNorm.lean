module

public import CFSG.HardMathSupport.Curtis.Proving.SmallOvergroupOrder
public import CFSG.Quasithin.Background.FLcSL
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrSmall

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe.Small

open CFSG.Open CFSG.QuasithinUnique CFSG.HardMathSupport.Curtis.Proving
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

theorem center_quotient_eq_bot {Q : Type} [Group Q] (hQ : Open.IsQuasisimple Q) :
    Subgroup.center (Q ⧸ Subgroup.center Q) = ⊥ := by
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  obtain ⟨a, b, hab⟩ :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q hQ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.center (Q ⧸ Subgroup.center Q)) with h | h
  · exact h
  · exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm hab

theorem eq_one_of_normalizer_le {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    {j : ℕ} (hA : Nat.card (MulAut X) = 2 ^ j * Nat.card X) {S : Subgroup X} (hS : IsPGroup 2 S)
    (hN : Subgroup.normalizer (S : Set X) ≤ S) {σ : MulAut X} (hσ : σ ^ 3 = 1)
    (hSσ : ∀ s ∈ S, σ s ∈ S) : σ = 1 := by
  have hodd : Odd (orderOf σ) :=
    Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hσ)
  obtain ⟨x, hx⟩ : ∃ x : X, MulAut.conj x = σ :=
    ParabIrr.mem_inner_of_odd_two_pow hZ hA hodd
  have hxN : x ∈ Subgroup.normalizer (S : Set X) := by
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have h := hSσ n hn
    rw [← hx, MulAut.conj_apply] at h
    exact h
  have hxS : x ∈ S := hN hxN
  obtain ⟨k, hk⟩ := hS ⟨x, hxS⟩
  have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hx3 : x ^ 3 = 1 := by
    refine ParabComm.conj_injective_of_center hZ ?_
    rw [map_pow, hx, hσ, map_one]
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have hord : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hx3) (orderOf_dvd_of_pow_eq_one hxk)
  rw [orderOf_eq_one_iff] at hord
  rw [← hx, hord, map_one]

theorem relIndex_dvd_three_of_card_dvd {X : Type} [Group X] {T P : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) (hTP : T ≤ P) (h : Nat.card P ∣ 96) : T.relIndex P ∣ 3 := by
  have hodd : ¬ 2 ∣ T.relIndex P := by
    intro h2
    apply hT.2.2
    have h' := Subgroup.relIndex_mul_relIndex T P ⊤ hTP le_top
    change 2 ∣ T.relIndex ⊤
    rw [← h']
    exact Dvd.dvd.mul_right h2 _
  have hdvd : T.relIndex P ∣ 2 ^ 5 * 3 :=
    (Subgroup.relIndex_dvd_card T P).trans (by simpa using h)
  have hcop : Nat.Coprime (T.relIndex P) (2 ^ 5) :=
    Nat.Coprime.pow_right 5 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).symm
  exact hcop.dvd_of_dvd_mul_left hdvd

theorem normalizer_le_of_relIndex_dvd_three {X : Type} [Group X] {T P : Subgroup X}
    (hidx : T.relIndex P ∣ 3) (hNP : Subgroup.normalizer (T : Set X) ≤ P)
    (hnn : ¬ P ≤ Subgroup.normalizer (T : Set X)) : Subgroup.normalizer (T : Set X) ≤ T := by
  have hmul := Subgroup.relIndex_mul_relIndex T (Subgroup.normalizer (T : Set X)) P
    Subgroup.le_normalizer hNP
  have hb : (Subgroup.normalizer (T : Set X)).relIndex P ≠ 1 := fun h1 =>
    hnn (Subgroup.relIndex_eq_one.mp h1)
  have hbdvd : (Subgroup.normalizer (T : Set X)).relIndex P ∣ 3 :=
    (Dvd.intro_left _ hmul).trans hidx
  have hb3 : (Subgroup.normalizer (T : Set X)).relIndex P = 3 :=
    ((Nat.dvd_prime Nat.prime_three).mp hbdvd).resolve_left hb
  have h3 : T.relIndex (Subgroup.normalizer (T : Set X)) * 3 ∣ 1 * 3 := by
    rw [hb3] at hmul
    rw [hmul, one_mul]
    exact hidx
  exact Subgroup.relIndex_eq_one.mp
    (Nat.dvd_one.mp (Nat.dvd_of_mul_dvd_mul_right (by norm_num) h3))

theorem normalizer_map_le_of_overgroup96 {Q : Type} [Group Q] [Finite Q]
    (hZ : Odd (Nat.card (Subgroup.center Q))) (h96 : OvergroupOrder96 (Q ⧸ Subgroup.center Q))
    {T P : Subgroup Q} (hT : IsSylowTwoOf T ⊤) (hTP : T ≤ P) (hP : P ≠ ⊤)
    (hNP : Subgroup.normalizer (T : Set Q) ≤ P) (hnn : ¬ P ≤ Subgroup.normalizer (T : Set Q)) :
    Subgroup.normalizer (T.map (QuotientGroup.mk' (Subgroup.center Q)) :
        Set (Q ⧸ Subgroup.center Q)) ≤ T.map (QuotientGroup.mk' (Subgroup.center Q)) := by
  set π := QuotientGroup.mk' (Subgroup.center Q) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hZr : Nat.Coprime (Nat.card (Subgroup.center Q)) 2 := Nat.coprime_two_right.mpr hZ
  have hN := CFSG.LieType.BorelTits.normalizer_eq_comap_normalizer_map (Subgroup.center Q)
    le_rfl hZr hT.2.1
  have hTb : IsSylowTwoOf (T.map π) ⊤ :=
    CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective hT π hπs
  have hZP : Subgroup.center Q ≤ P := fun z hz => hNP (Subgroup.center_le_normalizer _ hz)
  have hPb : P.map π ≠ ⊤ := by
    intro htop
    apply hP
    have hker : π.ker ≤ P := by
      rw [hπ, QuotientGroup.ker_mk']
      exact hZP
    rw [← Subgroup.comap_map_eq_self hker, htop, Subgroup.comap_top]
  have hTbPb : T.map π ≤ P.map π := Subgroup.map_mono hTP
  refine normalizer_le_of_relIndex_dvd_three
    (relIndex_dvd_three_of_card_dvd hTb hTbPb (h96 _ _ hTb hTbPb hPb)) ?_ ?_
  · intro x hx
    obtain ⟨q, rfl⟩ := hπs x
    have hq : q ∈ Subgroup.normalizer (T : Set Q) := by
      rw [hN]
      exact hx
    exact ⟨q, hNP hq, rfl⟩
  · intro h
    apply hnn
    intro p hp
    rw [hN]
    exact h ⟨p, hp, rfl⟩

theorem normalizer_map_le_of_equiv_slt {Q : Type} [Group Q] [Finite Q] {n : ℕ} (hn : 1 ≤ n)
    (e : Q ⧸ Subgroup.center Q ≃* CFSG.Quasithin.FLc.SLt n) {T : Subgroup Q}
    (hT : IsSylowTwoOf T ⊤) :
    Subgroup.normalizer (T.map (QuotientGroup.mk' (Subgroup.center Q)) :
        Set (Q ⧸ Subgroup.center Q)) ≤ T.map (QuotientGroup.mk' (Subgroup.center Q)) := by
  have hTb : IsSylowTwoOf (T.map (QuotientGroup.mk' (Subgroup.center Q))) ⊤ :=
    CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective hT _ (QuotientGroup.mk'_surjective _)
  have hidx : ¬ 2 ∣ (T.map (QuotientGroup.mk' (Subgroup.center Q))).index := by
    have h := hTb.2.2
    rwa [show ((T.map (QuotientGroup.mk' (Subgroup.center Q))).subgroupOf ⊤).index =
      (T.map (QuotientGroup.mk' (Subgroup.center Q))).index from
        Subgroup.relIndex_top_right _] at h
  let S : Sylow 2 (Q ⧸ Subgroup.center Q) := hTb.2.1.toSylow hidx
  exact (CFSG.Quasithin.FLc.normalizer_eq_of_sylow_equiv hn e S).le

theorem centralizes_of_normalizer_le {A : Type} [Group A] [Finite A] {Y T : Subgroup A}
    (hY : Open.IsQuasisimple ↥Y) (hT : IsSylowTwoOf T Y) {β : A} (hβ3 : β ^ 3 = 1)
    (hβY : β ∈ Subgroup.normalizer (Y : Set A)) (hβT : ∀ t ∈ T, β * t * β⁻¹ ∈ T) {j : ℕ}
    (hA : Nat.card (MulAut (↥Y ⧸ Subgroup.center ↥Y)) =
      2 ^ j * Nat.card (↥Y ⧸ Subgroup.center ↥Y))
    (hN : Subgroup.normalizer ((T.subgroupOf Y).map (QuotientGroup.mk' (Subgroup.center ↥Y)) :
        Set (↥Y ⧸ Subgroup.center ↥Y)) ≤
      (T.subgroupOf Y).map (QuotientGroup.mk' (Subgroup.center ↥Y))) :
    ∀ y ∈ Y, β * y = y * β := by
  have hZ := center_quotient_eq_bot hY
  have hS2 : IsPGroup 2 ((T.subgroupOf Y).map (QuotientGroup.mk' (Subgroup.center ↥Y))) :=
    (hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm).map _
  have hc3 : (⟨β, hβY⟩ : ↥(Subgroup.normalizer (Y : Set A))) ^ 3 = 1 :=
    Subtype.ext (by simpa using hβ3)
  have hσ3 : ParabIrr.quotAutN Y ⟨β, hβY⟩ ^ 3 = 1 := by
    rw [← map_pow, hc3, map_one]
  have hσ : ParabIrr.quotAutN Y ⟨β, hβY⟩ = 1 := by
    refine eq_one_of_normalizer_le hZ hA hS2 hN hσ3 ?_
    rintro _ ⟨t, ht, rfl⟩
    have h1 : (ParabIrr.quotAutN Y ⟨β, hβY⟩) (QuotientGroup.mk' (Subgroup.center ↥Y) t) =
        QuotientGroup.mk' (Subgroup.center ↥Y) (Y.normalizerMonoidHom ⟨β, hβY⟩ t) :=
      CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk _ _
    rw [h1]
    have h2 : Y.normalizerMonoidHom ⟨β, hβY⟩ t ∈ T.subgroupOf Y := by
      rw [Subgroup.mem_subgroupOf, Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact hβT t (Subgroup.mem_subgroupOf.mp ht)
    exact ⟨_, h2, rfl⟩
  exact ParabIrr.centralizes_of_quotAutN_eq_one hY hσ

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe.Small
