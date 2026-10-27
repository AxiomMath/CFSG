module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporAssemble
public import CFSG.HardMathSupport.Solomon.Proving.Fi22AutTables
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.PlaneKill

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Timmesfeld.ComponentBalance

@[expose] def SporPair (name : TauCeti.SporadicName) (p : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ K B : Subgroup X,
    I271Hyp p K B → I271Norm p K B → I271SporType K name →
      ¬ (IsFiTwentyTwo ↥K ∧ p = 5) → ¬ (IsHatON ↥K ∧ p = 3) →
        I271CaseA p K B ∨ IsStronglyBalancedIn p B K

theorem i271SporGen_iff : I271SporGen ↔ ∀ name p, SporPair name p :=
  ⟨fun h name p X _ _ hX K B hH hN hS hF hO => h X hX p K B hH hN name hS hF hO,
    fun h X _ _ hX p K B hH hN name hS hF hO => h name p X hX K B hH hN hS hF hO⟩

@[expose] def SporGenTable (name : TauCeti.SporadicName) (p : ℕ) : Prop :=
  SporadicOnePair name p ∨ B3SporRestPair name p

section S0

variable {X : Type} [Group X] [Finite X]

theorem card_image_autOrderIn {B K : Subgroup X} (hperf : commutator ↥K = ⊤) :
    Nat.card (((B ⊓ Subgroup.normalizer (K : Set X)).subgroupOf
        (Subgroup.normalizer (K : Set X))).map
      (i271Act K (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K)))) = autOrderIn B K := by
  rw [← Subgroup.relIndex_ker, ker_i271Act hperf (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K)),
    Subgroup.relIndex_subgroupOf (inf_le_right : B ⊓ Subgroup.normalizer (K : Set X) ≤
      Subgroup.normalizer (K : Set X))]
  rfl

theorem p_sq_dvd_card_of_norm (hOut : SporadicOuterLeTwo) {p : ℕ} {K B : Subgroup X}
    {name : TauCeti.SporadicName} (hH : I271Hyp p K B) (hN : I271Norm p K B)
    (hS : I271SporType K name) :
    p ^ 2 ∣ Nat.card (TauCeti.CFSGIndex.sporadic name).Group := by
  obtain ⟨e⟩ := hS
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hH.core hH.comp
  have hperf : commutator ↥K = ⊤ := hq.1
  have hsimple : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  have hnab : ∃ a b : ↥K ⧸ Subgroup.center ↥K, a * b ≠ b * a :=
    exists_noncomm_of_isQuasisimple hq
  have hcen : Subgroup.center (↥K ⧸ Subgroup.center ↥K) = ⊥ :=
    Solomon.Proving.fi22_center_eq_bot hnab
  have hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (↥K ⧸ Subgroup.center ↥K)) ≤ 2 := hOut _ hsimple hnab name ⟨e⟩
  have hmul := Solomon.Proving.fi22_card_mulAut hcen
  have hcard : Nat.card (↥K ⧸ Subgroup.center ↥K) =
      Nat.card (TauCeti.CFSGIndex.sporadic name).Group := Nat.card_congr e.toEquiv
  have hp := hH.prime
  have hBel : IsElemAbelian p B := hH.scp.2.1
  obtain ⟨r, hr⟩ := exists_pow_autOrderIn hp hBel hN.1
  have hr2 : 2 ≤ r := by
    have h2 := hN.2
    rw [hr] at h2
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h2
  have hdvdAut : p ^ r ∣ Nat.card (MulAut (↥K ⧸ Subgroup.center ↥K)) := by
    rw [← hr, ← card_image_autOrderIn (B := B) hperf]
    exact Subgroup.card_subgroup_dvd_card _
  have hOutpos : 0 < Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (↥K ⧸ Subgroup.center ↥K)) := Nat.card_pos
  have hc12 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (↥K ⧸ Subgroup.center ↥K)) = 1 ∨ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (↥K ⧸ Subgroup.center ↥K)) = 2 := by omega
  have hcop : Nat.Coprime (p ^ r) (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (↥K ⧸ Subgroup.center ↥K))) := by
    apply Nat.Coprime.pow_left
    rcases hc12 with h | h
    · rw [h]; exact Nat.coprime_one_right _
    · rw [h]
      exact (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd =>
        hH.odd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd)
  rw [hmul] at hdvdAut
  have h1 : p ^ r ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := hcop.dvd_of_dvd_mul_right hdvdAut
  rw [hcard] at h1
  exact (pow_dvd_pow p hr2).trans h1

end S0

theorem sporPair_of_not_sq_dvd (hOut : SporadicOuterLeTwo) (name : TauCeti.SporadicName) (p : ℕ)
    (h : ¬ p ^ 2 ∣ Nat.card (TauCeti.CFSGIndex.sporadic name).Group) : SporPair name p := by
  intro X _ _ _ K B hH hN hS _ _
  exact absurd (p_sq_dvd_card_of_norm hOut hH hN hS) h


theorem center_eq_bot_of_five_le
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    {X : Type} [Group X] [Finite X] {p : ℕ} {K B : Subgroup X} {name : TauCeti.SporadicName}
    (hH : I271Hyp p K B) (hp5 : 5 ≤ p) (hS : I271SporType K name) :
    Subgroup.center ↥K = ⊥ := by
  obtain ⟨e⟩ := hS
  have hp := hH.prime
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hH.core hH.comp
  have hZ : IsPGroup p (Subgroup.center ↥K) :=
    i271h_center_isPGroup hp (i271h_primeCore_eq_bot hH.core hH.comp)
  have hd : Nat.card (Subgroup.center ↥K) ∣ 12 :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.card_center_dvd_twelve hSpM hq name e
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hZ
  rw [hn] at hd
  apply Subgroup.eq_bot_of_card_eq
  rw [hn]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0, pow_zero]
  · exfalso
    have hpd : p ∣ 12 := (dvd_pow_self p hpos.ne').trans hd
    have h12 : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
    rw [h12] at hpd
    rcases (Nat.Prime.dvd_mul hp).1 hpd with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) ((Nat.Prime.dvd_of_dvd_pow hp h2))
      omega
    · have := Nat.le_of_dvd (by norm_num) h3
      omega

theorem sporPair_Fi22_five
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers) :
    SporPair .Fi22 5 := by
  intro X _ _ hX K B hH hN hS hF5 hON
  exfalso
  have hcen := center_eq_bot_of_five_le hSpM hH (le_refl 5) hS
  obtain ⟨e⟩ := hS
  apply hF5
  refine ⟨⟨?_⟩, rfl⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm.trans e

@[expose] def SporPlaneKill (name : TauCeti.SporadicName) (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group) → AutRankLe2 p S ∧ PlaneKill p S

theorem sporPair_of_planeKill {name : TauCeti.SporadicName} {p : ℕ}
    (h : SporPlaneKill name p) : SporPair name p := by
  intro X _ _ _ K B hH hN hS _ _
  obtain ⟨e⟩ := hS
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hH.core hH.comp
  obtain ⟨hR, hP⟩ := h (↥K ⧸ Subgroup.center ↥K) hq.2 (exists_noncomm_of_isQuasisimple hq) ⟨e⟩
  exact conclusion_of_planeKill hH hN hR hP

structure SporGenPairs : Prop where
  m11_3 : SporPair .M11 3
  m12_3 : SporPair .M12 3
  m22_3 : SporPair .M22 3
  m23_3 : SporPair .M23 3
  m24_3 : SporPair .M24 3
  j2_3 : SporPair .J2 3
  j4_3 : SporPair .J4 3
  hs_3 : SporPair .HS 3
  ru_3 : SporPair .Ru 3
  he_3 : SporPair .He 3
  j3_3 : SporPair .J3 3
  mcl_3 : SporPair .McL 3
  suz_3 : SporPair .Suz 3
  on_3 : SporPair .ONan 3
  co3_3 : SporPair .Co3 3
  co2_3 : SporPair .Co2 3
  co1_3 : SporPair .Co1 3
  fi22_3 : SporPair .Fi22 3
  fi23_3 : SporPair .Fi23 3
  fi24_3 : SporPair .Fi24Prime 3
  hn_3 : SporPair .HN 3
  ly_3 : SporPair .Ly 3
  th_3 : SporPair .Th 3
  b_3 : SporPair .B 3
  m_3 : SporPair .M 3
  co1_5 : SporPair .Co1 5
  hn_5 : SporPair .HN 5
  ly_5 : SporPair .Ly 5
  b_5 : SporPair .B 5
  m_5 : SporPair .M 5
  j2_5 : SporPair .J2 5
  hs_5 : SporPair .HS 5
  mcl_5 : SporPair .McL 5
  suz_5 : SporPair .Suz 5
  he_5 : SporPair .He 5
  ru_5 : SporPair .Ru 5
  co2_5 : SporPair .Co2 5
  co3_5 : SporPair .Co3 5
  fi23_5 : SporPair .Fi23 5
  fi24_5 : SporPair .Fi24Prime 5
  th_5 : SporPair .Th 5
  m_7 : SporPair .M 7
  he_7 : SporPair .He 7
  on_7 : SporPair .ONan 7
  co1_7 : SporPair .Co1 7
  fi24_7 : SporPair .Fi24Prime 7
  th_7 : SporPair .Th 7
  b_7 : SporPair .B 7
  j4_11 : SporPair .J4 11
  m_11 : SporPair .M 11
  m_13 : SporPair .M 13

theorem SporGenPairs.apply (h : SporGenPairs) (hF : SporPair .Fi22 5) :
    ∀ name p, SporGenTable name p → SporPair name p := by
  intro name p tab
  rcases tab with h1 | h2
  · unfold SporadicOnePair at h1
    rcases h1 with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl
      exacts [h.j3_3, h.mcl_3, h.suz_3, h.on_3, h.co3_3, h.co2_3, h.co1_3, h.fi22_3, h.fi23_3,
        h.fi24_3, h.hn_3, h.ly_3, h.th_3, h.b_3, h.m_3]
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl
      exacts [h.co1_5, h.hn_5, h.ly_5, h.b_5, h.m_5]
    · rw [hn]
      exact h.m_7
  · unfold B3SporRestPair at h2
    rcases h2 with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [h.m11_3, h.m12_3, h.m22_3, h.m23_3, h.m24_3, h.j2_3, h.j4_3, h.hs_3, h.ru_3, h.he_3]
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [h.j2_5, h.hs_5, h.mcl_5, h.suz_5, h.he_5, h.ru_5, h.co2_5, h.co3_5, hF, h.fi23_5,
        h.fi24_5, h.th_5]
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [h.he_7, h.on_7, h.co1_7, h.fi24_7, h.th_7, h.b_7]
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl
      exacts [h.j4_11, h.m_11]
    · rw [hn]
      exact h.m_13

theorem i271SporGen_of_pairs (hOut : SporadicOuterLeTwo) (hTab : SporadicP2Table)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (h : SporGenPairs) : I271SporGen := by
  rw [i271SporGen_iff]
  intro name p
  by_cases hsq : p ^ 2 ∣ Nat.card (TauCeti.CFSGIndex.sporadic name).Group
  · by_cases hpr : p.Prime ∧ p ≠ 2
    · exact h.apply (sporPair_Fi22_five hSpM) name p (hTab name p hpr.1 hpr.2 hsq)
    · intro X _ _ _ K B hH
      exact absurd ⟨hH.prime, hH.odd⟩ hpr
  · exact sporPair_of_not_sq_dvd hOut name p hsq

end CFSG.HardMathSupport.Dickson.I271
