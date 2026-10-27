module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.CaseI
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.CaseII
import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.PerfectLe
import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.WeakClosed
import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerBalance
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.MSide

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding
open CFSG.LocalAnalysis.RankThreeTheoremC

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem map_mk_layer_n [Fact p.Prime] {N : Subgroup G} (hp5 : 5 ≤ p) {n : ℕ} (hn : 2 ≤ n)
    {L U : Subgroup G} (hLN : L ≤ N) (e : L ≃* PSL(2, GaloisField p n)) (hUL : IsSylowOf p U L)
    (hU : Nat.card U = p ^ n) :
    primeComplementCore (G := N) p ⊓ L.subgroupOf N = ⊥ ∧
      Nonempty ((L.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)) ≃*
        PSL(2, GaloisField p n)) ∧
      IsSylowOf p ((U.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)))
        ((L.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p))) := by
  have hK : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n (by omega)
  have : IsSimpleGroup PSL(2, GaloisField p n) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [hK]
      exact (show 4 ≤ p by omega).trans (Nat.le_self_pow (by omega) p))
  let eL : L.subgroupOf N ≃* PSL(2, GaloisField p n) :=
    (Subgroup.subgroupOfEquivOfLe hLN).trans e
  have hpL : p ∣ Nat.card (L.subgroupOf N) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLN).toEquiv]
    refine dvd_trans ?_ (Subgroup.card_dvd_of_le hUL.le)
    rw [hU]
    exact dvd_pow_self p (by omega)
  have hinj := inf_eq_bot_of_coprime_of_isSimpleGroup Fact.out _ (primeComplementCore_coprime p)
    eL.isSimpleGroup hpL
  obtain ⟨e₁⟩ := nonempty_mulEquiv_map_mk_of_inf_eq_bot _ hinj
  exact ⟨hinj, ⟨e₁.symm.trans eL⟩, isSylowOf_map_mk_of_inf_eq_bot hLN hUL hinj⟩

omit [Finite G] in
theorem fr_coprime_card_map_subgroupOf {Y : Type*} [Group Y] {N W : Subgroup G} (hWN : W ≤ N)
    (hW : Nat.Coprime p (Nat.card W)) (f : N →* Y) :
    Nat.Coprime p (Nat.card ((W.subgroupOf N).map f)) :=
  Nat.Coprime.coprime_dvd_right ((Subgroup.card_map_dvd _ f).trans
    (dvd_of_eq (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWN).toEquiv))) hW

theorem fr_pRank_sylow_le [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x) {n : ℕ}
    (hUel : CFSG.Open.IsElemAbelian p (frU P x)) (hUcard : Nat.card (frU P x) = p ^ n) :
    CFSG.Open.pRank p (P : Subgroup G) ≤ n + 1 := by
  have hp : p.Prime := Fact.out
  have hxp : Nat.card (zpowers x) = p := by
    rw [Nat.card_zpowers]
    exact hl.point.elem.2.1
  refine CFSG.SectionRank.pRank_le hp.one_lt fun E hEP hE => ?_
  have hdec : ∀ e : E, ∃ a : (frU P x) × (zpowers x), (e : G) = (a.1 : G) * (a.2 : G) := by
    intro e
    obtain ⟨t, ht, z, hz, hez⟩ := fr_P_decomp hG hl (hEP e.2)
    have hcomm : t * z = z * t := by
      have := congrArg Subtype.val (hl.abel.is_comm.comm (⟨t, ht.1⟩ : (P : Subgroup G))
        ⟨z, hz.1⟩)
      exact this
    have hep : (e : G) ^ p = 1 := hE.2 _ e.2
    have htp : t ^ p = 1 := hUel.2 t ht
    have hzp : z ^ p = 1 := by
      have h1 : (t * z) ^ p = t ^ p * z ^ p := (Commute.mul_pow (show Commute t z from hcomm) p)
      rw [← hez, hep, htp, one_mul] at h1
      exact h1.symm
    have hzx : z ∈ zpowers x := by
      have hord : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzp
      rcases (Nat.dvd_prime hp).1 hord with h1 | h1
      · rw [orderOf_eq_one_iff.mp h1]
        exact one_mem _
      · have hA : zpowers z = zpowers x := by
          refine fr_Z0_unique hl (zpowers_le.mpr hz) ?_
          rw [Nat.card_zpowers, h1]
        rw [← hA]
        exact mem_zpowers z
    exact ⟨(⟨t, ht⟩, ⟨z, hzx⟩), hez⟩
  choose ι hι using hdec
  have hinj : Function.Injective ι := fun a b hab => Subtype.ext (by rw [hι a, hι b, hab])
  have h := Nat.card_le_card_of_injective ι hinj
  rw [Nat.card_prod, hUcard, hxp] at h
  rwa [← pow_succ] at h

theorem fr_caseI_N [Fact p.Prime] (hK : FrobKFacts) (hG : FrobGlobal G) (hl : FrobLocal p P M x)
    {N : Subgroup G} (hNtop : N ≠ ⊤) (hLN : layerOf x ≤ N)
    (hSyl : IsSylowOf p (frU P x) N) {W : Subgroup G} (hWp : Nat.Coprime p (Nat.card W))
    (hWN : W ≤ N) (hUW : frU P x ≤ normalizer (W : Set G)) :
    W ≤ CFSG.Open.GLBPrimeCore p N := by
  have hp : p.Prime := Fact.out
  have hp5 := hl.p5
  set O : Subgroup N := primeComplementCore (G := N) p
  obtain ⟨n, hn3, ⟨e⟩, hUL, hUe, hUc⟩ := fr_layer_rank hG hl
  have hUN : frU P x ≤ N := hUL.le.trans hLN
  have hOM : O ≤ (N ⊓ M).subgroupOf N :=
    primeComplementCore_le_subgroupOf_inf_of_coprime hp hUN fun _ hX hXN =>
      fr_coprime_le hG hl ((Nat.Prime.coprime_iff_not_dvd hp).mpr hX) hXN
  obtain ⟨-, ⟨eL⟩, hUL'⟩ := map_mk_layer_n hp5 (by omega) hLN e hUL hUc
  exact le_rankThreePrimeCore_of_map_mk_eq_bot hWN (frobCaseI_holds hK.kc hK.schreier hp5 hn3
    (primeComplementCore_quotient_eq_bot p)
    ((catalogSimpleSections_of_isKProper hG.kProper N hNtop).quotient O) eL hUL'
    (isSylowOf_top_map_mk hSyl) (map_mk_inf_ne_top hOM fun h => hl.not_le (hLN.trans h))
    (fun _ hDU hD1 => normalizer_le_map_mk_inf hp hOM hUN hUL.isPGroup
      (fun _ hD hD1 => fr_normalizer_le hG hl hD hD1) hDU hD1)
    (not_map_mk_le_map_mk_inf hOM hLN hl.not_le)
    (fr_coprime_card_map_subgroupOf hWN hWp _) (map_subgroupOf_le_normalizer_map hUW _))

theorem fr_caseIIHyp [Fact p.Prime] (hK : FrobKFacts) (hG : FrobGlobal G) (hl : FrobLocal p P M x)
    {N : Subgroup G} (hNtop : N ≠ ⊤) (hLN : layerOf x ≤ N) (hxN : x ∈ N) :
    ∃ n : ℕ, FrobCaseIIHyp p n
      (((layerOf x).subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)))
      (((frU P x).subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)))
      (QuotientGroup.mk' (primeComplementCore (G := N) p) ⟨x, hxN⟩) := by
  have hp : p.Prime := Fact.out
  have hp5 := hl.p5
  set O : Subgroup N := primeComplementCore (G := N) p
  obtain ⟨n, hn3, ⟨e⟩, hUL, hUe, hUc⟩ := fr_layer_rank hG hl
  obtain ⟨-, ⟨eL⟩, hUL'⟩ := map_mk_layer_n hp5 (by omega) hLN e hUL hUc
  have hxo : orderOf (⟨x, hxN⟩ : N) = p := by
    rw [Subgroup.orderOf_mk]
    exact hl.point.elem.2.1
  have hxo' : orderOf (QuotientGroup.mk' O ⟨x, hxN⟩) = p :=
    orderOf_mk_of_coprime hp O (primeComplementCore_coprime p) hxo
  have hab := isMulCommutative_sylow_quotient (N := N) fun _ hQ => fr_pGroup_abelian hl _ hQ
  refine ⟨n, hp5, hn3, primeComplementCore_quotient_eq_bot p,
    (catalogSimpleSections_of_isKProper hG.kProper N hNtop).quotient O, ⟨eL⟩, hUL',
    pRank_top_quotient_le hp fun Q _ => ?_, hab,
    fun h => by
      rw [h, orderOf_one] at hxo'
      exact hp.one_lt.ne hxo',
    by simpa only [hxo'] using pow_orderOf_eq_one (QuotientGroup.mk' O ⟨x, hxN⟩),
    mk_mem_centralizer_map (fr_x_mem_Z0 hl).2,
    centralizer_mk_le_normalizer_map hp hxo (fr_layer_normal_in_centralizer x),
    perfect_le_map_mk hp hxo fun _ hJ hJp => fr_perfect_le hG hl _ hJ hJp,
    weaklyClosed_map_mk hxo hab fun Q hxQ g hg => fr_weakly_closed hl Q hxQ g hg⟩
  exact (pRank_le_pRank_sylow hp P Q).trans (fr_pRank_sylow_le hG hl hUe hUc)

theorem fr_caseII_N [Fact p.Prime] (hK : FrobKFacts) (hG : FrobGlobal G) (hl : FrobLocal p P M x)
    {N : Subgroup G} (hNtop : N ≠ ⊤) (hLN : layerOf x ≤ N) (hxN : x ∈ N) {W : Subgroup G}
    (hWp : Nat.Coprime p (Nat.card W)) (hWN : W ≤ N) (hUW : frU P x ≤ normalizer (W : Set G)) :
    ∀ w ∈ W, ∀ l ∈ layerOf x, w⁻¹ * (l⁻¹ * w * l) ∈ CFSG.Open.GLBPrimeCore p N := by
  obtain ⟨n, h⟩ := fr_caseIIHyp hK hG hl hNtop hLN hxN
  exact commutator_mem_rankThreePrimeCore hWN hLN (frobCaseII_holds hK.schreier hK.weak hK.inner h
    (fr_coprime_card_map_subgroupOf hWN hWp _) (map_subgroupOf_le_normalizer_map hUW _))

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
