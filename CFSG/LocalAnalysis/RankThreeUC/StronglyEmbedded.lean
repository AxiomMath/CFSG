module

public import CFSG.LocalAnalysis.RankThreeUC.WitnessGen
public import CFSG.RankThree.PartOne.S12.InputsSec15
import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalPairGeometry
import CFSG.RankThree.PartOne.CTP.StrongPGlue

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.ABGLocalTools (IsSylowOf exists_isSylowOf isSylowOf_of_card)

variable {G : Type} [Group G] [Finite G]

private theorem isSylowOf_of_normalizer_le {p : ℕ} [Fact p.Prime] {S E M : Subgroup G}
    (hSE : IsSylowOf p S E) (hEM : E ≤ M) (hN : normalizer (S : Set G) ≤ E) :
    IsSylowOf p S M := by
  obtain ⟨Q, hQ⟩ := (hSE.isPGroup.comap_subtype (K := M)).exists_le_sylow
  obtain ⟨T, hT, hST⟩ : ∃ T : Subgroup G, IsSylowOf p T M ∧ S ≤ T :=
    ⟨(Q : Subgroup M).map M.subtype, ⟨Q, rfl⟩, fun x hx => ⟨⟨x, hEM (hSE.le hx)⟩, hQ hx, rfl⟩⟩
  by_cases hTS : S = T
  · exact hTS ▸ hT
  · exfalso
    have hgrow := pGroup_proper_subgroup_lt_internal_normalizer p Fact.out T S hT.isPGroup
      (lt_of_le_of_ne hST hTS)
    have heq : T ⊓ normalizer (S : Set G) = S :=
      hSE.eq_of_le (le_inf hST le_normalizer) (inf_le_right.trans hN) hT.isPGroup.to_inf_left
    exact hgrow.ne heq.symm

private theorem exists_mem_map_conj_eq_of_isSylowOf {p : ℕ} [Fact p.Prime] {A B M : Subgroup G}
    (hA : IsSylowOf p A M) (hB : IsSylowOf p B M) :
    ∃ m ∈ M, A.map (MulAut.conj m).toMonoidHom = B := by
  obtain ⟨QA, rfl⟩ := hA
  obtain ⟨QB, rfl⟩ := hB
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M QA QB
  refine ⟨m, m.2, ?_⟩
  rw [← hm, sylow_conjugate_eq_map, Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem one_le_pRank_of_isPGroup_of_ne_bot {p : ℕ} [Fact p.Prime] {Q : Subgroup G}
    (hQ : IsPGroup p Q) (hne : Q ≠ ⊥) : 1 ≤ CFSG.Open.pRank p Q := by
  have hdvd : p ∣ Nat.card Q :=
    hQ.card_eq_or_dvd.resolve_left fun h => hne (Subgroup.card_eq_one.mp h)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hx' : orderOf (x : G) = p := (Subgroup.orderOf_coe x).trans hx
  unfold CFSG.Open.pRank
  refine le_csSup (pRank_set_bddAbove p (Fact.out : p.Prime).one_lt Q)
    ⟨Subgroup.zpowers (x : G), Subgroup.zpowers_le.mpr x.2, ⟨inferInstance, fun y hy => ?_⟩, ?_⟩
  · obtain ⟨i, rfl⟩ := hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx', pow_orderOf_eq_one,
      one_zpow]
  · rw [Nat.card_zpowers, hx', pow_one]

private theorem ne_bot_of_one_le_pRank {p : ℕ} (hp : 1 < p) {Q : Subgroup G}
    (hQ : 1 ≤ CFSG.Open.pRank p Q) : Q ≠ ⊥ := by
  rintro rfl
  obtain ⟨E, hE, -, hcard⟩ := pRank_attained p ⊥ hQ
  rw [le_bot_iff.mp hE, Subgroup.card_bot] at hcard
  exact (Nat.one_lt_pow (by omega) hp).ne' hcard.symm

theorem isStronglyPEmbedded_of_normalizer_le {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ≠ ⊤) (hpM : p ∣ Nat.card M)
    (h : ∀ Q : Subgroup G, Q ≠ ⊥ → IsPGroup p Q → Q ≤ M → normalizer (Q : Set G) ≤ M) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded p M := by
  refine ⟨hM, hpM, fun g hg hdvd => hg ?_⟩
  obtain ⟨S, hSD⟩ := exists_isSylowOf p (M ⊓ M.map (MulAut.conj g).toMonoidHom)
  have hSM : S ≤ M := hSD.le.trans inf_le_left
  have hSMg : S ≤ M.map (MulAut.conj g).toMonoidHom := hSD.le.trans inf_le_right
  have hS1 : S ≠ ⊥ := by
    rintro rfl
    have hpos := (Fact.out : p.Prime).factorization_pos_of_dvd Nat.card_pos.ne' hdvd
    have hcard := hSD.card_eq
    rw [Subgroup.card_bot] at hcard
    exact (Nat.one_lt_pow hpos.ne' (Fact.out : p.Prime).one_lt).ne' hcard.symm
  have hN : normalizer (S : Set G) ≤ M := h S hS1 hSD.isPGroup hSM
  have hS'M : S.map (MulAut.conj g⁻¹).toMonoidHom ≤ M := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hSMg hs
    simpa [MulAut.conj_apply, mul_assoc] using hy
  have hN' : normalizer ((S.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G) ≤ M :=
    h _ ((Subgroup.map_eq_bot_iff_of_injective S (MulAut.conj g⁻¹).injective).not.mpr hS1)
      (hSD.isPGroup.map _) hS'M
  have hNg : normalizer (S : Set G) ≤ M.map (MulAut.conj g).toMonoidHom := by
    intro x hx
    have hx' : (MulAut.conj g⁻¹).toMonoidHom x ∈
        normalizer ((S.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G) := by
      rw [← map_equiv_normalizer_eq S (MulAut.conj g⁻¹)]
      exact mem_map_of_mem _ hx
    exact ⟨_, hN' hx', by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  have hSM' : IsSylowOf p S M := isSylowOf_of_normalizer_le hSD inf_le_left (le_inf hN hNg)
  have hS'M' : IsSylowOf p (S.map (MulAut.conj g⁻¹).toMonoidHom) M := by
    refine isSylowOf_of_card hS'M ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hSM'.card_eq]
  obtain ⟨m, hmM, hm⟩ := exists_mem_map_conj_eq_of_isSylowOf hS'M' hSM'
  have hc : m * g⁻¹ ∈ normalizer (S : Set G) := by
    have : S.map (MulAut.conj (m * g⁻¹)).toMonoidHom = S := by
      rw [← conjugate_map_mul S m g⁻¹]
      exact hm
    exact mem_normalizer_iff_map_conj_eq.mpr this
  have hg' : g⁻¹ ∈ M := by simpa using M.mul_mem (M.inv_mem hmM) (hN hc)
  exact inv_mem_iff.mp hg'

theorem normalizer_le_of_gamma_one_le {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M : Subgroup G}
    (hPM : (P : Subgroup G) ≤ M) (hΓ : rankThreeGamma 1 p (P : Subgroup G) ≤ M)
    {Q : Subgroup G} (hQ : Q ≠ ⊥) (hQp : IsPGroup p Q) (hQM : Q ≤ M) :
    normalizer (Q : Set G) ≤ M := by
  obtain ⟨m, hm⟩ := pGroup_conjugate_into_sylow_within_overgroup p Fact.out P M hPM Q hQp hQM
  have h1 : 1 ≤ CFSG.Open.pRank p (Q.map (MulAut.conj (m : G)).toMonoidHom) := by
    rw [← pRank_eq_of_subgroup_equiv p (Fact.out : p.Prime).one_lt Q _
      (Q.equivMapOfInjective (MulAut.conj (m : G)).toMonoidHom (MulAut.conj (m : G)).injective)]
    exact one_le_pRank_of_isPGroup_of_ne_bot hQp hQ
  have hN := (gamma_normalizer_le 1 p (P : Subgroup G) _ hm h1).trans hΓ
  intro x hx
  have hx' : (MulAut.conj (m : G)) x ∈ M := hN (by
    rw [← map_equiv_normalizer_eq Q (MulAut.conj (m : G))]
    exact mem_map_of_mem _ hx)
  simpa [MulAut.conj_apply, mul_assoc] using M.mul_mem (M.mul_mem (M.inv_mem m.2) hx') m.2

theorem gamma_one_le_iff_isStronglyPEmbedded {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M : Subgroup G} (hPM : (P : Subgroup G) ≤ M) (hM : M ≠ ⊤) (hP : (P : Subgroup G) ≠ ⊥) :
    rankThreeGamma 1 p (P : Subgroup G) ≤ M ↔
      CFSG.RankThree.PartOne.IsStronglyPEmbedded p M := by
  refine ⟨fun hΓ => isStronglyPEmbedded_of_normalizer_le hM ?_
    fun Q hQ hQp hQM => normalizer_le_of_gamma_one_le hPM hΓ hQ hQp hQM, fun hY => ?_⟩
  · exact (P.isPGroup'.card_eq_or_dvd.resolve_left fun h =>
      hP (Subgroup.card_eq_one.mp h)).trans (Subgroup.card_dvd_of_le hPM)
  · refine (gamma_le_iff 1 p (P : Subgroup G) M).mpr fun Q hQP hQ1 => ?_
    exact hY.normalizer_le (ne_bot_of_one_le_pRank (Fact.out : p.Prime).one_lt hQ1)
      (P.isPGroup'.to_le hQP) (hQP.trans hPM)

theorem IsWitnessGen.gamma_one_le_iff (hS : CFSG.LocalAnalysis.AGL81TheoremCD.StandingGen G)
    {p : ℕ} {P : Sylow p G} (hp : IsWitnessPrime p P) {M : Subgroup G}
    (hw : IsWitnessGen p P M) :
    rankThreeGamma 1 p (P : Subgroup G) ≤ M ↔
      CFSG.RankThree.PartOne.IsStronglyPEmbedded p M := by
  have : Fact p.Prime := ⟨hp.prime⟩
  have := hS.simple
  have hP : (P : Subgroup G) ≠ ⊥ := ne_bot_of_one_le_pRank (Fact.out : p.Prime).one_lt
    (by have := hp.rank; omega)
  exact gamma_one_le_iff_isStronglyPEmbedded (hw.sylow_le hp)
    (twoLocal_ne_top hS.nonab M hw.maxLocal.1) hP

theorem IsWitness.gamma_one_le_iff (hS : Standing G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M : Subgroup G} (hw : IsWitness p P M) :
    rankThreeGamma 1 p (P : Subgroup G) ≤ M ↔
      CFSG.RankThree.PartOne.IsStronglyPEmbedded p M :=
  IsWitnessGen.gamma_one_le_iff hS.toGen (IsWitnessPrime.of_mem_sigmaA hS hp P) hw.toGen

end CFSG.LocalAnalysis.RankThreeUC
