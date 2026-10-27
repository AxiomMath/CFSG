module

public import CFSG.LocalAnalysis.AGLEmbedding.LemmaJStar
public import CFSG.LocalAnalysis.AGLEmbeddingD2.TheoremZ

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section N1
variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M R X : Subgroup G}

@[expose] def D1JCompetitorsOn (C : Subgroup G → Prop) (R X : Subgroup G) : Prop :=
  ∀ H : Subgroup G, C H → ∀ H' : Subgroup G, GLBIsMaxTwoLocal H' →
    nclIn H X ≤ H' → R ≤ H' → C H' ∧ nclIn H X ≤ nclIn H' X

theorem D1JConfig.toAGL {H : Subgroup G} (h : D1JConfig p P M H R X) :
    CFSG.AGLEmbeddingD2.AGLJConfig p M H R X :=
  ⟨h.phaseThree.toPair, h.le_R, h.ne_bot, h.normal_sup, h.commutator_le, h.centralizer_le⟩

theorem false_of_competitorsOn {C : Subgroup G → Prop}
    (hC : ∀ H, C H → D1JConfig p P M H R X) (hcomp : D1JCompetitorsOn C R X)
    {H : Subgroup G} (h : C H) (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) : False :=
  CFSG.AGLEmbeddingD2.false_of_agljCompetitorsOn (fun H' h' => (hC H' h').toAGL) hcomp h hCGT
    (hD2 G (hC H h).phaseThree.glob)

end N1

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open scoped commutatorElement

namespace AGLPair

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R : Subgroup G}

theorem false_of_unique_over' (h : AGLPair p M H R) {X X' J : Subgroup G}
    (hXR : X ≤ R) (hX'R : X' ≤ R)
    (hXQ : ((X ⊔ pCoreOf 2 M).subgroupOf M).Normal)
    (hNX : ⁅GLBPrimeCore p H, X⁆ ≤ pCoreOf 2 M)
    (hCX : (H ⊓ M) ⊓ Subgroup.centralizer (X : Set G) ≤ X' ⊔ GLBPrimeCore p H)
    (hNJ : ⁅GLBPrimeCore p H, J⁆ ≤ pCoreOf 2 H)
    (huniq : ∀ H' : Subgroup G, GLBIsMaxTwoLocal H' → J ≤ H' → R ≤ H' → H' = H)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : NoXBlockFor G) : False := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hp2 : p.Coprime 2 := (Nat.coprime_primes h.prime Nat.prime_two).mpr h.ne_two
  have hX : IsPGroup p X := h.isPGroup_R.to_le hXR
  have hX' : IsPGroup p X' := h.isPGroup_R.to_le hX'R
  have hXM : X ≤ M := hXR.trans h.le_M
  have hSN : pCoreOf 2 H ≤ GLBPrimeCore p H := h.twoCore_le_primeCore
  have hQS : pCoreOf 2 M ≤ pCoreOf 2 H := h.twoCore_M_le
  have hQM : pCoreOf 2 M ≤ M := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M
  have hMQ : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M
  have hQcop : p.Coprime (Nat.card (pCoreOf 2 M)) := by
    obtain ⟨k, hk⟩ :=
      IsPGroup.iff_card.mp (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
    exact hk ▸ hp2.pow_right k
  have hMXQ : M ≤ Subgroup.normalizer ((X ⊔ pCoreOf 2 M : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hXM hQM)).mp hXQ
  obtain ⟨T, hTN, hT2, hTidx, hRT, hST⟩ := h.exists_sylowTwo_primeCore
  have hT1 : T ≠ ⊥ := fun hbot => CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_pCoreOf_ne_bot H
    h.maxTwoLocal_H.1 (le_bot_iff.mp (hbot ▸ hST))
  have hJT : J ≤ Subgroup.normalizer (T : Set G) := by
    refine le_normalizer_of_forall_mul_mul_inv_mem fun j hj t ht => ?_
    have hc := hNJ (Subgroup.commutator_mem_commutator ((GLBPrimeCore p H).inv_mem (hTN ht)) hj)
    rw [commutatorElement_def, inv_inv] at hc
    have e : j * t * j⁻¹ = t * (t⁻¹ * j * t * j⁻¹) := by group
    rw [e]
    exact T.mul_mem ht (hST hc)
  refine h.false_of_normal_inf_le_sup (D := pCoreOf 2 M ⊔ (M ⊓ Subgroup.centralizer (X : Set G)))
    hX' (hX'R.trans h.le_H) hTN hT2 hTidx hT1
    (fun C hCT hC hchar => normalizer_le_of_forall_maxTwoLocal_eq hT2 hJT hRT huniq hCT hC hchar)
    (sup_le hQM inf_le_left) (le_normalizer_sup_inf_centralizer hX hQcop hXM hQM hMQ hMXQ)
    le_sup_left (fun n hn => mem_sup_inf_centralizer_of_commutator_mem hX hQcop hXM hQM hMQ hMXQ
      (h.primeCore_le hn) fun x hx => ?_) ?_ hCGT hD2
  · have hc := hNX (Subgroup.commutator_mem_commutator hn hx)
    rwa [commutatorElement_def] at hc
  · rintro d ⟨hd, hdH⟩
    obtain ⟨q, hq, c, hc, rfl⟩ := exists_mul_of_mem_sup_inf_centralizer hMQ hd
    have hqN : q ∈ GLBPrimeCore p H := hSN (hQS hq)
    have hcH : c ∈ H := by
      have e : c = q⁻¹ * (q * c) := by group
      rw [e]
      exact H.mul_mem (H.inv_mem (glbPrimeCore_le p H hqN)) hdH
    exact (X' ⊔ GLBPrimeCore p H).mul_mem (Subgroup.mem_sup_right hqN) (hCX ⟨⟨hcH, hc.1⟩, hc.2⟩)

end AGLPair

end CFSG.AGLEmbeddingD2

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

namespace D1PhaseThree

section N1b
variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem false_of_unique_over' (h : D1PhaseThree p P M H R) {X X' J : Subgroup G}
    (hXR : X ≤ R) (hX'R : X' ≤ R)
    (hXQ : ((X ⊔ pCoreOf 2 M).subgroupOf M).Normal)
    (hNX : ⁅GLBPrimeCore p H, X⁆ ≤ pCoreOf 2 M)
    (hCX : (H ⊓ M) ⊓ Subgroup.centralizer (X : Set G) ≤ X' ⊔ GLBPrimeCore p H)
    (hNJ : ⁅GLBPrimeCore p H, J⁆ ≤ pCoreOf 2 H)
    (huniq : ∀ H' : Subgroup G, GLBIsMaxTwoLocal H' → J ≤ H' → R ≤ H' → H' = H)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) : False :=
  h.toPair.false_of_unique_over' hXR hX'R hXQ hNX hCX hNJ huniq hCGT (hD2 G h.glob)

end N1b

end D1PhaseThree

end CFSG.AGLEmbedding
