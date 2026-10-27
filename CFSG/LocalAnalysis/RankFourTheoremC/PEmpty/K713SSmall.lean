module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SBasic
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SAbelian
public import CFSG.LocalAnalysis.GL83PartI.I713.Extension
import CFSG.Goldschmidt.Steps.Sec82PGroup
import CFSG.GH74.Uniqueness.SU.SU1Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms Subgroup
open scoped commutatorElement

theorem isPerfect_of_simple_nonabelian' {K : Type*} [Group K] [IsSimpleGroup K]
    (hnonab : ∃ a b : K, a * b ≠ b * a) : _root_.commutator K = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator K) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    apply hab
    have hmem : ⁅a, b⁆ ∈ _root_.commutator K :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rwa [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  · exact h

theorem commutator_inner_eq {K : Type*} [Group K] [IsSimpleGroup K]
    (hnonab : ∃ a b : K, a * b ≠ b * a) : ⁅inner K, inner K⁆ = inner K := by
  have h := Subgroup.map_commutator (H₁ := (⊤ : Subgroup K)) (H₂ := (⊤ : Subgroup K))
    (f := (MulAut.conj : K →* MulAut K))
  have htop : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = (⊤ : Subgroup K) := by
    rw [← _root_.commutator_def]
    exact isPerfect_of_simple_nonabelian' hnonab
  rw [htop] at h
  have hmap : (⊤ : Subgroup K).map (MulAut.conj : K →* MulAut K) = inner K := by
    rw [ComponentClassification.OuterAutomorphisms.inner, MonoidHom.range_eq_map]
  rw [hmap] at h
  exact h.symm

theorem mem_of_pow_mem_of_pow_eq_one {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {N : Subgroup G}
    {y : G} (hy : y ^ p = 1) {i : ℤ} (hi : y ^ i ∈ N) (hpi : ¬ (p : ℤ) ∣ i) : y ∈ N := by
  have hcop : IsCoprime i (p : ℤ) := by
    have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    exact ((Prime.coprime_iff_not_dvd hpp).mpr hpi).symm.symm.symm
  obtain ⟨a, b, hab⟩ := hcop
  have : y = (y ^ i) ^ a * (y ^ (p : ℤ)) ^ b := by
    rw [← zpow_mul, ← zpow_mul, ← zpow_add]
    nth_rewrite 1 [← zpow_one y]
    congr 1
    linarith
  rw [this, zpow_natCast, hy, one_zpow, mul_one]
  exact N.zpow_mem hi a

theorem outLift_of_card_outer_lt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type*} [Group K]
    [Finite K] [IsSimpleGroup K] (hnonab : ∃ a b : K, a * b ≠ b * a)
    (hrank : pRank p (⊤ : Subgroup K) ≤ 1) (hOut : Nat.card (Outer K) < p ^ 2) :
    OutLift p K := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ : Subgroup.center K = ⊥ := GL83.I713.center_eq_bot_of_simple hnonab
  obtain ⟨S⟩ : Nonempty (Sylow p (MulAut K)) := inferInstance
  refine outLift_of_split hp S ?_
  set N : Subgroup (MulAut K) := inner K with hN
  by_cases hSN : (S : Subgroup (MulAut K)) ≤ N
  · exact ⟨⊥, bot_le, bot_inf_eq _, by rw [inf_eq_left.2 hSN, sup_bot_eq]⟩
  have hd : ((S : Subgroup (MulAut K)) ⊓ N).relIndex S = p := by
    have h1 : ((S : Subgroup (MulAut K)) ⊓ N).relIndex S = N.relIndex S :=
      inf_relIndex_left _ _
    have h2 : N.relIndex (S ⊔ N) = N.relIndex S := relIndex_sup_right _ _
    have h3 : N.relIndex (S ⊔ N) ∣ Nat.card (Outer K) := by
      have := relIndex_mul_index (le_sup_right : N ≤ (S : Subgroup (MulAut K)) ⊔ N)
      exact Dvd.intro _ this
    have h4 : N.relIndex S ∣ Nat.card (S : Subgroup (MulAut K)) :=
      Dvd.intro _ (relIndex_mul_card N (S : Subgroup (MulAut K)))
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 S.isPGroup'
    rw [hm] at h4
    obtain ⟨j, hj, hjd⟩ := (Nat.dvd_prime_pow hp).1 h4
    rw [h1]
    have hne1 : N.relIndex S ≠ 1 := fun h => hSN (relIndex_eq_one.1 h)
    have hlt : N.relIndex S < p ^ 2 :=
      lt_of_le_of_lt (Nat.le_of_dvd Nat.card_pos (h2 ▸ h3)) hOut
    rw [hjd] at hne1 hlt ⊢
    have hj1 : j ≠ 0 := fun h => hne1 (by rw [h, pow_zero])
    have hj2 : j < 2 := (Nat.pow_lt_pow_iff_right hp.one_lt).1 hlt
    obtain rfl : j = 1 := by omega
    exact pow_one p
  by_cases hSab : ∀ x y : (S : Subgroup (MulAut K)), x * y = y * x
  · exact exists_complement_of_abelian_sylow_amb S hSab N (commutator_inner_eq hnonab)
  have hSnc : ¬ IsCyclic (S : Subgroup (MulAut K)) := fun hc =>
    hSab fun x y => IsMulCommutative.is_comm.comm x y
  obtain ⟨V, hVS, -, hVcard, hVexp, hVcomm⟩ :=
    CFSG.Goldschmidt.Sec82.exists_normal_plane_le_of_le hp hp2
      (T := (S : Subgroup (MulAut K))) (R := (S : Subgroup (MulAut K))) S.isPGroup' le_rfl
      Subgroup.le_normalizer hSnc
  have hVN : ¬ V ≤ N := by
    intro hVN
    have hV : IsElemAbelian p V :=
      (CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_iff).2 ⟨hVcomm, hVexp⟩
    have h2 := CFSG.SectionRank.le_pRank hp.one_lt hVN hV hVcard
    have hinn : pRank p N = pRank p (⊤ : Subgroup K) := by
      rw [hN, CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (GL83.I713.innerEquiv K hZ)]
    omega
  obtain ⟨y, hyV, hyN⟩ := Set.not_subset.1 hVN
  have hyS : y ∈ (S : Subgroup (MulAut K)) := hVS hyV
  have hyp : y ^ p = 1 := hVexp y hyV
  refine ⟨zpowers y, zpowers_le.2 hyS, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxR, hxN⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hxR
    by_cases hpi : (p : ℤ) ∣ i
    · obtain ⟨k, rfl⟩ := hpi
      rw [zpow_mul, zpow_natCast, hyp, one_zpow]
      exact one_mem _
    · exact absurd (mem_of_pow_mem_of_pow_eq_one hp hyp hxN hpi) hyN
  · set P : Subgroup (MulAut K) := (S : Subgroup (MulAut K)) ⊓ N with hP
    have hPR : P ⊔ zpowers y ≤ (S : Subgroup (MulAut K)) :=
      sup_le inf_le_left (zpowers_le.2 hyS)
    have hyP : y ∉ P := fun h => hyN h.2
    have h1 := relIndex_mul_relIndex P (P ⊔ zpowers y) S le_sup_left hPR
    rw [hd] at h1
    have ha : P.relIndex (P ⊔ zpowers y) ≠ 1 := fun h =>
      hyP (relIndex_eq_one.1 h (mem_sup_right (mem_zpowers y)))
    have hb : (P ⊔ zpowers y).relIndex S = 1 := by
      rcases (Nat.prime_mul_iff.1 (h1 ▸ hp)) with ⟨_, hb1⟩ | ⟨_, ha1⟩
      · exact hb1
      · exact absurd ha1 ha
    exact le_antisymm hPR (relIndex_eq_one.1 hb)

theorem liftClause_of_card_outer_le_six {K : Type*} [Group K] [Finite K] [IsSimpleGroup K]
    (hnonab : ∃ a b : K, a * b ≠ b * a) (h : Nat.card (Outer K) ≤ 6) : LiftClause K := by
  intro p hp hp2 hrank
  refine outLift_of_card_outer_lt hp hp2 hnonab hrank (lt_of_le_of_lt h ?_)
  have h3 : 3 ≤ p := by
    have := hp.two_le
    omega
  nlinarith

theorem liftClause_of_card_outer_le_four {K : Type*} [Group K] [Finite K] [IsSimpleGroup K]
    (hnonab : ∃ a b : K, a * b ≠ b * a) (h : Nat.card (Outer K) ≤ 4) : LiftClause K :=
  liftClause_of_card_outer_le_six hnonab (h.trans (by norm_num))

theorem liftClause_of_not_dvd {K : Type*} [Group K] [Finite K]
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 1 →
      ¬ p ∣ Nat.card (Outer K)) :
    LiftClause K :=
  fun p hp hp2 hr => outLift_of_not_dvd (h p hp hp2 hr)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S
