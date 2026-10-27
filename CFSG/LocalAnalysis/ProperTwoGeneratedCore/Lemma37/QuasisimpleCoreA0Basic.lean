module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreA0BasicBW
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBasicsRooting

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}
  {N : Subgroup J}

theorem FourGen.exists_involution_not_mem_fourGroup (hz : FourGen Q z) (h : Setting J Q B) :
    ∃ t ∈ (Q : Subgroup J), t * t = 1 ∧ t ∉ fourGroup z := by
  have hsimple := h.simple
  set π := QuotientGroup.mk' (Subgroup.center J) with hπ
  let S : Sylow 2 (J ⧸ Subgroup.center J) := Q.mapSurjective (QuotientGroup.mk'_surjective _)
  have hS : (S : Subgroup (J ⧸ Subgroup.center J)) = (Q : Subgroup J).map π :=
    Sylow.coe_mapSurjective _ _
  have hnonab : ∃ a b : J ⧸ Subgroup.center J, a * b ≠ b * a := by
    by_contra hall
    push Not at hall
    have hZ : Subgroup.center J = ⊤ := by
      rw [eq_top_iff, ← h.perfect.commutator_eq_top, commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [commutatorElement_def, ← commute_mk_iff]
      exact hall _ _
    obtain ⟨g, hg⟩ := exists_ne (1 : J ⧸ Subgroup.center J)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    exact hg ((QuotientGroup.eq_one_iff x).mpr (hZ ▸ Subgroup.mem_top x))
  have hzc : IsCentralInvolution (S : Subgroup (J ⧸ Subgroup.center J)) (π z) := by
    refine ⟨hS ▸ Subgroup.mem_map_of_mem π hz.mem, orderOf_eq_prime ?_ hz.mk_ne_one, ?_⟩
    · rw [pow_two, ← map_mul, hz.mul_self, map_one]
    · intro s hs
      rw [hS] at hs
      obtain ⟨q, hq, rfl⟩ := hs
      exact (commute_mk_iff q z).mpr (hz.comm_mem_center q hq)
  obtain ⟨g, hgS, hgne⟩ := centralInvolution_exists_conj_mem_ne hsimple hnonab hzc
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
  have hπt : π (k⁻¹ * z * k) = (k : J ⧸ Subgroup.center J)⁻¹ * π z * k := by
    rw [map_mul, map_mul, map_inv]
    rfl
  refine ⟨k⁻¹ * z * k, ?_, ?_, fun hV => ?_⟩
  · rw [hS] at hgS
    obtain ⟨q, hq, hqt⟩ := hgS
    have hζ : q⁻¹ * (k⁻¹ * z * k) ∈ Subgroup.center J := by
      rw [← QuotientGroup.eq_one_iff]
      change π (q⁻¹ * (k⁻¹ * z * k)) = 1
      rw [map_mul, map_inv, hπt, ← hqt, inv_mul_cancel]
    have h1 := (Q : Subgroup J).mul_mem hq (h.center_le_sylow hζ)
    rwa [mul_inv_cancel_left] at h1
  · calc k⁻¹ * z * k * (k⁻¹ * z * k) = k⁻¹ * (z * z) * k := by group
      _ = 1 := by rw [hz.mul_self, mul_one, inv_mul_cancel]
  · have hne : π (k⁻¹ * z * k) ≠ π z := by rw [hπt]; exact hgne
    have hzz : k * (k⁻¹ * z * k) * k⁻¹ = z := by group
    rcases (hz.mem_fourGroup_iff h).mp hV with h1 | h1 | h1 | h1
    · apply hz.mk_ne_one
      rw [← hzz, h1, mul_one, mul_inv_cancel, QuotientGroup.mk_one]
    · apply hz.ne_centralElt h
      rw [← hzz, h1, Setting.conj_eq_of_mem_center h.centralElt_mem_center]
    · exact hne (by rw [h1])
    · apply hne
      have he : π (centralElt J) = 1 := (QuotientGroup.eq_one_iff _).mpr h.centralElt_mem_center
      rw [h1, map_mul, he, one_mul]

structure A0Config (Q : Sylow 2 J) (B : Subgroup J) (z u : J) (N : Subgroup J) : Prop where
  setting : Setting J Q B
  fourGen : FourGen Q z
  mem : u ∈ (Q : Subgroup J)
  sq : u * u = centralElt J
  comm : u * z = z * u
  rank : CFSG.Open.pRank 2 (quasiNormalizer u) ≤ 2
  le_quasiNormalizer : N ≤ quasiNormalizer u
  quasiNormalizer_le : quasiNormalizer u ≤ Subgroup.normalizer (N : Set J)
  odd : Odd (Nat.card N)
  not_le : ¬ N ≤ B
  sylow_le : (Q : Subgroup J) ≤ quasiNormalizer u

namespace A0Config

theorem mem_quasiNormalizer (hc : A0Config Q B z u N) {q : J} (hq : q ∈ (Q : Subgroup J)) :
    q ∈ quasiNormalizer u :=
  hc.sylow_le hq

theorem mem_normalizer (hc : A0Config Q B z u N) {q : J} (hq : q ∈ (Q : Subgroup J)) :
    q ∈ Subgroup.normalizer (N : Set J) :=
  hc.quasiNormalizer_le (hc.sylow_le hq)

theorem mem_core (hc : A0Config Q B z u N) : u ∈ B :=
  hc.setting.sylow_le hc.mem

theorem twoRank_eq_two (hc : A0Config Q B z u N) : twoRank J = 2 := by
  have h1 := CFSG.SectionRank.pRank_mono (p := 2) (by decide) hc.sylow_le
  rw [sylow_two_rank_eq Q] at h1
  have h2 := hc.setting.rank
  have h3 := hc.rank
  omega

theorem mul_comm_of_mem (hc : A0Config Q B z u N) {o : J} (ho : o ∈ N) : o * u = u * o :=
  hc.setting.mul_comm_of_odd (odd_orderOf_of_mem hc.odd ho)
    ((hc.setting.mem_normalizer_zpowers_iff hc.sq).mp (hc.le_quasiNormalizer ho))

theorem mul_mul_self (hc : A0Config Q B z u N) : u * z * (u * z) = centralElt J := by
  calc u * z * (u * z) = u * (z * u) * z := by group
    _ = u * u * (z * z) := by rw [← hc.comm]; group
    _ = centralElt J := by rw [hc.sq, hc.fourGen.mul_self, mul_one]

theorem conj_eq_of_not_mem (hc : A0Config Q B z u N) {t : J} (htQ : t ∈ (Q : Subgroup J))
    (ht : t * t = 1) (htV : t ∉ fourGroup z) : t * z * t⁻¹ = centralElt J * z :=
  (hc.fourGen.conj_eq hc.setting htQ).resolve_left fun h1 => by
    have htz : t * z = z * t := by
      calc t * z = t * z * t⁻¹ * t := by group
        _ = z * t := by rw [h1]
    have h3 := hc.fourGen.three_le_pRank hc.setting
      (hc.setting.centralElt_mem_quasiNormalizer u) (hc.mem_quasiNormalizer hc.fourGen.mem)
      (hc.mem_quasiNormalizer htQ) ht htz htV
    have h2 := hc.rank
    omega

theorem not_mem_center_of_not_mem (hc : A0Config Q B z u N) {t : J}
    (htQ : t ∈ (Q : Subgroup J)) (ht : t * t = 1) (htV : t ∉ fourGroup z) :
    t ∉ Subgroup.center J ∧ t * z ∉ Subgroup.center J ∧
      t * z * t⁻¹ * z⁻¹ ∈ Subgroup.center J := by
  have h := hc.setting
  have hz := hc.fourGen
  refine ⟨fun htZ => htV ?_, fun htzZ => htV ?_, ?_⟩
  · rcases h.mem_center_iff.mp htZ with h1 | h1 <;> rw [h1]
    · exact (fourGroup z).one_mem
    · exact centralElt_mem_fourGroup z
  · have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz.mul_self
    rcases h.mem_center_iff.mp htzZ with h1 | h1
    · rw [mul_eq_one_iff_eq_inv.mp h1, hzinv]
      exact mem_fourGroup z
    · rw [show t = t * z * z⁻¹ by group, h1, hzinv]
      exact (fourGroup z).mul_mem (centralElt_mem_fourGroup z) (mem_fourGroup z)
  · rw [hc.conj_eq_of_not_mem htQ ht htV, mul_inv_cancel_right]
    exact h.centralElt_mem_center

theorem conj_self_eq_of_not_mem (hc : A0Config Q B z u N) {t : J}
    (htQ : t ∈ (Q : Subgroup J)) (ht : t * t = 1) (htV : t ∉ fourGroup z) :
    t * u * t⁻¹ = centralElt J * u := by
  have h := hc.setting
  have hz := hc.fourGen
  obtain ⟨htZ, htzZ, htzc⟩ := hc.not_mem_center_of_not_mem htQ ht htV
  refine (h.conj_eq_of_mem_quasiNormalizer hc.sq (hc.mem_quasiNormalizer htQ)).resolve_left
    fun h1 => ?_
  have htu : t * u = u * t := by
    calc t * u = t * u * t⁻¹ * t := by group
      _ = u * t := by rw [h1]
  have hcomm : t * z * u = u * (t * z) := by
    calc t * z * u = t * (u * z) := by rw [mul_assoc, hc.comm]
      _ = u * (t * z) := by rw [← mul_assoc, htu, mul_assoc]
  have key := h.eq_of_commute_of_odd hc.mem_core hc.sq hc.le_quasiNormalizer
    hc.quasiNormalizer_le hc.odd hc.not_le (h.sylow_le htQ) (hz.mem_of_setting h)
    (hc.mem_quasiNormalizer htQ) (hc.mem_quasiNormalizer hz.mem) ht hz.mul_self htZ
    hz.not_mem_center htzc htzZ hcomm
  have htzz : t * z * z = z * (t * z) := by
    rcases key with h2 | h2 <;> rw [h2]
    · exact hc.comm
    · rw [mul_assoc, hc.comm, ← mul_assoc, (h.commute_centralElt z).eq.symm, mul_assoc]
  have h3 : t = z * t * z := by
    calc t = t * z * z := by rw [mul_assoc, hz.mul_self, mul_one]
      _ = z * t * z := by rw [htzz]; group
  have h4 : t * z * t⁻¹ = z := by
    calc t * z * t⁻¹ = (z * t * z) * z * t⁻¹ := by rw [← h3]
      _ = z * t * (z * z) * t⁻¹ := by group
      _ = z := by rw [hz.mul_self, mul_one, mul_inv_cancel_right]
  rw [hc.conj_eq_of_not_mem htQ ht htV] at h4
  exact h.centralElt_ne_one (mul_eq_right.mp h4)

theorem conj_mul_eq_of_not_mem (hc : A0Config Q B z u N) {t : J}
    (htQ : t ∈ (Q : Subgroup J)) (ht : t * t = 1) (htV : t ∉ fourGroup z) :
    t * (u * z) * t⁻¹ = u * z := by
  rw [show t * (u * z) * t⁻¹ = (t * u * t⁻¹) * (t * z * t⁻¹) by group,
    hc.conj_self_eq_of_not_mem htQ ht htV, hc.conj_eq_of_not_mem htQ ht htV,
    hc.setting.central_mul_central]

end A0Config

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
