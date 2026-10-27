module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1OddCoresNorm
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1OddCoresG1Props
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1Generation
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentZGen

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Assembly.Dichotomy

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
  (htype : ∀ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)),
    s ∉ (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
      CaseC3.Genuine (Subgroup.center J) s)
include d htype

theorem centralizer_forty_le_normalizer :
    Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40} ≤ Subgroup.normalizer
      (oddCoreSpan (e1WBar (Subgroup.center J) u m y x) : Set (J ⧸ Subgroup.center J)) := by
  have hb := d.caseC3BCD
  set W := oddCoreSpan (e1WBar (Subgroup.center J) u m y x) with hW
  set N := Subgroup.normalizer (W : Set (J ⧸ Subgroup.center J)) with hN
  obtain ⟨τ, hτN, hτE, hτa, hτK, hτfpf, hτ3⟩ := d.exists_tau_e1NBar htype
  have hτW : τ ∈ N := by
    have h := normalizer_le_oddCoreSpan_normalizer _ (hb.mem_normalizer_e1GBar hτN hτfpf hτ3)
    rwa [d.oddCoreSpan_e1GBar htype hτN hτfpf hτ3] at h
  have hSW : (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)) ≤ N :=
    hb.map_le_normalizer_e1WBar.trans (normalizer_le_oddCoreSpan_normalizer _)
  have hCW : Subgroup.centralizer (e1EBar (Subgroup.center J) u m y x :
      Set (J ⧸ Subgroup.center J)) ≤ N := fun c hc =>
    d.centralizer_self_le_normalizer htype (Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hc _ d.mem_e1EBar_gens.1).symm)
  have hzW : caseC3Word (Subgroup.center J) u m y x 40 ∈ e1WBar (Subgroup.center J) u m y x :=
    hb.caseC3Word_mem_e1WBar_iff.mpr (by decide)
  have hz1 : caseC3Word (Subgroup.center J) u m y x 40 ≠ 1 := by
    rw [Ne, hb.caseC3Word_eq_one_iff]
    decide
  intro g hg
  obtain ⟨o, ho, n, hn, rfl⟩ := d.exists_mul_mem_pPrimeCore_normalizer htype hg
  obtain ⟨k, -, s, hs, c, hc, rfl⟩ := d.exists_eq_pow_mul_of_mem_e1NBar htype hτN hτE hτa hτK hn
  have hoW : o ∈ N := Subgroup.le_normalizer (involutionOddCore_le_span _ hzW hz1 (by
    rw [involutionOddCore_eq_map_pPrimeCore]
    exact ho))
  exact N.mul_mem hoW (N.mul_mem (N.mul_mem (N.pow_mem hτW k) (hSW hs)) (hCW hc))

theorem normalizer_oddCoreSpan_e1WBar_eq_top :
    Subgroup.normalizer
    (oddCoreSpan (e1WBar (Subgroup.center J) u m y x) : Set (J ⧸ Subgroup.center J)) = ⊤ := by
  rw [eq_top_iff, ← d.centralizer_sup_centralizer_eq_top htype]
  exact sup_le (d.centralizer_forty_le_normalizer htype) (d.centralizer_self_le_normalizer htype)

theorem oddCoreSpan_e1WBar_eq_bot :
    oddCoreSpan (e1WBar (Subgroup.center J) u m y x) = ⊥ := by
  have hb := d.caseC3BCD
  have : IsSimpleGroup (J ⧸ Subgroup.center J) := d.setting.simple
  have hn := Subgroup.normalizer_eq_top_iff.mp (d.normalizer_oddCoreSpan_e1WBar_eq_top htype)
  refine hn.eq_bot_or_eq_top.resolve_right fun htop => ?_
  have hodd := (d.oddCoreSpanCompleted_e1WBar htype).2.1
  have h2 : orderOf (caseC3Word (Subgroup.center J) u m y x 40) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hb.forty_mul_self)
      (by rw [Ne, hb.caseC3Word_eq_one_iff]; decide)
  have hmem : caseC3Word (Subgroup.center J) u m y x 40 ∈
      oddCoreSpan (e1WBar (Subgroup.center J) u m y x) := by
    rw [htop]
    exact Subgroup.mem_top _
  have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
  rw [h2] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem involutionOddCore_eq_bot_of_mem_e1WBar
    {a : J ⧸ Subgroup.center J}
    (ha : a ∈ e1WBar (Subgroup.center J) u m y x) (ha1 : a ≠ 1) : involutionOddCore a = ⊥ :=
  eq_bot_iff.mpr ((involutionOddCore_le_span _ ha ha1).trans
    (d.oddCoreSpan_e1WBar_eq_bot htype).le)

theorem involutionOddCore_eq_bot
    {t : J ⧸ Subgroup.center J} (htt : t * t = 1) (ht1 : t ≠ 1) :
    involutionOddCore t = ⊥ := by
  have hb := d.caseC3BCD
  have hconj : ∀ {a c : J ⧸ Subgroup.center J}, involutionOddCore a = ⊥ →
      involutionOddCore (c * a * c⁻¹) = ⊥ := fun {a c} h => by
    rw [← MulAut.conj_apply, ← involutionOddCore_map, h, Subgroup.map_bot]
  by_cases hg : CaseC3.Genuine (Subgroup.center J) t
  · obtain ⟨c, rfl⟩ := isConj_iff.mp (d.isConj_forty_of_genuine htype htt ht1 hg)
    exact hconj (d.involutionOddCore_eq_bot_of_mem_e1WBar htype
      (hb.caseC3Word_mem_e1WBar_iff.mpr (by decide))
      (by rw [Ne, hb.caseC3Word_eq_one_iff]; decide))
  · obtain ⟨c, rfl⟩ := isConj_iff.mp (d.isConj_self_of_not_genuine htype htt ht1 hg)
    rw [← CaseC3BCD.caseC3Word_thirtytwo (Z := Subgroup.center J) (m := m) (y := y) (x := x)]
    exact hconj (d.involutionOddCore_eq_bot_of_mem_e1WBar htype
      (hb.caseC3Word_mem_e1WBar_iff.mpr (by decide))
      (by rw [Ne, hb.caseC3Word_eq_one_iff]; decide))

theorem pPrimeCore_centralizer_eq_bot
    {t : J ⧸ Subgroup.center J} (htt : t * t = 1)
    (ht1 : t ≠ 1) : CFSG.pPrimeCore 2 (Subgroup.centralizer {t}) = ⊥ := by
  have h := d.involutionOddCore_eq_bot htype htt ht1
  rw [involutionOddCore_eq_map_pPrimeCore] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h

omit htype in
theorem self_ne_one : (u : J ⧸ Subgroup.center J) ≠ 1 := by
  rw [← CaseC3BCD.caseC3Word_thirtytwo (Z := Subgroup.center J) (m := m) (y := y) (x := x), Ne,
    d.caseC3BCD.caseC3Word_eq_one_iff]
  decide

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
