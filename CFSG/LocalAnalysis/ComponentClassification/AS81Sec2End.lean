module

public import CFSG.LargeExtraspecial.S12T36Core
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Z

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup Module QuadraticMap CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.RankThree.OrthogonalInvolutions
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four
open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

namespace Sec2

variable {G : Type} [Group G]

theorem le_normalizer_map_subtype {K : Subgroup G} {P : Subgroup K} (hP : P.Normal) :
    K ≤ normalizer ((P.map K.subtype : Subgroup G) : Set G) := by
  intro c hc
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨c, hc⟩ * w * ⟨c, hc⟩⁻¹, hP.conj_mem w hw _, rfl⟩
  · rintro ⟨w, hw, hwx⟩
    refine ⟨⟨c, hc⟩⁻¹ * w * ⟨c, hc⟩, ?_, ?_⟩
    · have := hP.conj_mem w hw ⟨c, hc⟩⁻¹
      rwa [inv_inv] at this
    · change c⁻¹ * (w : G) * c = x
      rw [show (w : G) = c * x * c⁻¹ from hwx]
      group

variable [Finite G] [IsSimpleGroup G]

theorem Mbar_map_eq_of_dvd (S : LargeExtraspecial.Setting G) (hn : 3 ≤ S.width) {V' : Type*}
    [AddCommGroup V'] [Module (ZMod 2) V'] [FiniteDimensional (ZMod 2) V']
    {q' : QuadraticForm (ZMod 2) V'} (hq' : (polarBilin q').Nondegenerate)
    (hV' : finrank (ZMod 2) V' = 2 * S.width) (h : Nat.card (omegaGroup q' hq') ∣ Nat.card S.Mbar) :
    S.Mbar.map S.O.subtype = timmesfeldOmega S.q := by
  have hfinQ : finrank (ZMod 2) S.Qt = 2 * S.width := S.finrank_Qt_eq_two_mul_width
  have : Nontrivial S.Qt := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have hOQ : Nat.card S.O = 2 * Nat.card (omegaGroup S.q S.q_nondegenerate) :=
    LargeExtraspecial.S12DW.card_orthogonalGroup_eq S.q_nondegenerate
  have hMO : Nat.card S.Mbar ∣ 2 * Nat.card (omegaGroup S.q S.q_nondegenerate) := by
    rw [← hOQ]
    exact Subgroup.card_subgroup_dvd_card S.Mbar
  have hΩ := LargeExtraspecial.S12T36.card_omegaGroup_eq_of_dvd_two_mul S.q_nondegenerate hq'
    (by omega) hfinQ hV' (h.trans hMO)
  rw [hΩ] at h
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := hMO
  have hpos : 0 < Nat.card (omegaGroup S.q S.q_nondegenerate) := Nat.card_pos
  have hab : a * b = 2 := by
    refine (Nat.eq_of_mul_eq_mul_left hpos ?_).symm
    rw [← mul_assoc, ← ha, ← hb, mul_comm]
  rcases (Nat.dvd_prime Nat.prime_two).mp ⟨b, hab.symm⟩ with h1 | h2
  ·
    rw [h1, mul_one] at ha
    have hidx : S.Mbar.index = 2 := by
      have h1 := Subgroup.card_mul_index S.Mbar
      rw [ha, hOQ] at h1
      exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans (mul_comm _ _))
    have : S.Mbar.Normal := Subgroup.normal_of_index_eq_two hidx
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcardq : Nat.card (S.O ⧸ S.Mbar) = 2 := by
      rw [← Subgroup.index_eq_card]
      exact hidx
    have : IsCyclic (S.O ⧸ S.Mbar) := isCyclic_of_prime_card hcardq
    have hcomm : _root_.commutator S.O ≤ S.Mbar :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp IsCyclic.isMulCommutative
    rw [CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_subgroupOf
      S.q_nondegenerate (by omega)] at hcomm
    have hle : omegaGroup S.q S.q_nondegenerate ≤ S.Mbar.map S.O.subtype := fun g hg =>
      ⟨⟨g, omegaGroup_le S.q S.q_nondegenerate hg⟩, hcomm hg, rfl⟩
    have hcard : Nat.card (S.Mbar.map S.O.subtype) = Nat.card S.Mbar :=
      (Nat.card_congr (S.Mbar.equivMapOfInjective S.O.subtype S.O.subtype_injective).toEquiv).symm
    rw [LargeExtraspecial.s12_timmesfeldOmega_eq S.q S.q_nondegenerate]
    exact (Subgroup.eq_of_le_of_card_ge hle (hcard.trans ha).le).symm
  ·
    exfalso
    refine S.Mbar_ne_top hn (Subgroup.eq_top_of_card_eq _ ?_)
    rw [ha, hOQ, h2, mul_comm]

end Sec2

namespace Sec2Data

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F T₀ : Subgroup G}
  {u y : G}

theorem rankTwoX_eq_top (h212 : Step212) (hD : Sec2Data G A R g E F T₀ u y)
    (htop : rankTwoX A ⊔ R = ⊤) : rankTwoX A = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := hD.setting.frame
  have hR2 : IsPGroup 2 R := hF.sylowR.isPGroup
  have hodd : ∀ x : G, Odd (orderOf x) → x ∈ rankTwoX A := by
    intro x hx
    have hxs : x ∈ ((rankTwoX A ⊔ R : Subgroup G) : Set G) := by
      rw [htop]
      exact mem_top x
    rw [Subgroup.normal_mul] at hxs
    obtain ⟨a, ha, r, hr, rfl⟩ := hxs
    obtain ⟨k, hk⟩ := hR2 ⟨r, hr⟩
    have hk' : r ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h1 : (QuotientGroup.mk (a * r) : G ⧸ rankTwoX A) = QuotientGroup.mk r := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff a).mpr ha, one_mul]
    have h2 : orderOf (QuotientGroup.mk (a * r) : G ⧸ rankTwoX A) ∣ 2 ^ k := by
      rw [h1]
      exact orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one])
    have h3 : orderOf (QuotientGroup.mk (a * r) : G ⧸ rankTwoX A) ∣ orderOf (a * r) :=
      orderOf_map_dvd (QuotientGroup.mk' (rankTwoX A)) (a * r)
    have h4 : Nat.Coprime (2 ^ k) (orderOf (a * r)) := Nat.Coprime.pow_left _
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hx.not_two_dvd_nat)
    have h5 := Nat.dvd_gcd h2 h3
    rw [h4] at h5
    exact (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h5))
  have hK : sec2K E ≤ rankTwoX A := by
    unfold sec2K oUpperTwo
    rw [closure_le]
    exact fun x hx => hodd x hx.2
  have hPST := ((h212 G A R g E F hD.setting).2 T₀ hD.le hD.sylow).2.1
  have hRX : R ≤ rankTwoX A :=
    ((hF.R_le_F.trans le_sup_left).trans le_sup_right).trans (hPST.trans (inf_le_right.trans hK))
  exact (sup_eq_left.mpr hRX).symm.trans htop

theorem exists_centerIn_eq (h24 : Step24) (h212 : Step212) (hD : Sec2Data G A R g E F T₀ u y) :
    ∃ z : G, orderOf z = 2 ∧ centerIn (sec2T E T₀) = zpowers z := by
  have hS := hD.setting
  have hZ4 := (h24 G A R g E F hS).1
  obtain ⟨-, -, -, hZ2, hZne, -⟩ := (h212 G A R g E F hS).2 T₀ hD.le hD.sylow
  have hT2 : IsPGroup 2 (sec2T E T₀) := hD.sylow.isPGroup.to_le inf_le_left
  have hle : centerIn (sec2T E T₀) ≤ sec2Z A E F := by
    rw [← hZ2, Sec2.centerIn_eq_map]
    refine map_mono ?_
    rw [← Subgroup.upperCentralSeries_one]
    exact Subgroup.upperCentralSeries_mono _ (by norm_num)
  have hne : centerIn (sec2T E T₀) ≠ ⊥ := by
    have hT1 : sec2T E T₀ ≠ ⊥ := by
      intro h
      have hZ : sec2Z A E F ≤ ⊥ := by
        rw [← h, ← hZ2]
        exact map_subtype_le _
      rw [le_bot_iff] at hZ
      rw [hZ, card_bot] at hZ4
      norm_num at hZ4
    have h := Sec2.inf_centerIn_ne_bot hT2 le_rfl le_normalizer hT1
    rwa [inf_eq_right.mpr (show centerIn (sec2T E T₀) ≤ sec2T E T₀ from inf_le_left)] at h
  have hcard : Nat.card (centerIn (sec2T E T₀)) = 2 := by
    have hdvd : Nat.card (centerIn (sec2T E T₀)) ∣ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hZ4]
      exact Subgroup.card_dvd_of_le hle
    have h1 : Nat.card (centerIn (sec2T E T₀)) ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
    have h4 : Nat.card (centerIn (sec2T E T₀)) ≠ 4 := fun h =>
      hZne (Subgroup.eq_of_le_of_card_ge hle (by rw [h, hZ4]))
    obtain ⟨i, hi, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · exact absurd hn h1
    · exact hn
    · exact absurd hn h4
  obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzo : orderOf z = 2 := by
    have hdvd : orderOf z ∣ 2 := hcard ▸ Subgroup.orderOf_dvd_natCard _ hz
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1'
    · exact h
  refine ⟨z, hzo, (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hz) ?_).symm⟩
  rw [hcard, Nat.card_zpowers, hzo]

end Sec2Data

end CFSG.ComponentClassification.AS81
