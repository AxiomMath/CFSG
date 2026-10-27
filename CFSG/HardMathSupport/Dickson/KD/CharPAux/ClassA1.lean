module

public import CFSG.HardMathSupport.Dickson.KD.CharPAux.ClassA
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreA1
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der69
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Prop67
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieCore
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentral
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec2Statements
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.Proving.LBLayerConj
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.HardMathSupport.Dickson.KD

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.GorensteinWalter
  CFSG.HardMathSupport.Timmesfeld.DefChar

theorem frame_projectiveSL_two {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hK : IsOddPrimePower (Nat.card K)) (hKc : 3 < Nat.card K) (hp2 : p ≠ 2)
    (y : projectiveSL 2 K) (hy : orderOf y = p) : Frame p y := by
  obtain ⟨N, hN, hN0, hy0⟩ := exists_nilpotent_of_orderOf_eq (p := p) y hy
  have hne : Nontrivial (Fin 2 → K) := inferInstance
  refine ⟨∅, modelT 2 K N, ?_, ?_, ?_, ?_, ?_⟩
  · rintro q (hq | hq)
    · exact hq.elim
    rw [hy0]
    exact model_h1 hN q (Or.inr hq)
  · intro s q hs hq
    rw [hy0] at hs
    exact model_hT hN s q hs hq
  · intro s q _ hq
    exact hq.elim
  · intro s0 hα hfix
    set α : MulAut (projectiveSL 2 K) := MulAut.conj s0 with hαdef
    let ι : PSL2 K ≃* projectiveSL 2 K := LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 K
    have hcop : (orderOf (MulAut.congr ι.symm α)).Coprime p := by
      rw [MulEquiv.orderOf_eq (MulAut.congr ι.symm) α]
      exact Nat.Coprime.coprime_dvd_left (orderOf_map_dvd MulAut.conj s0) hα
    have h1 : MulAut.congr ι.symm α = 1 := by
      refine uniq_psl2 hK hKc hp2 hN hN0 _ hcop ?_
      intro s t hs
      have hmem : proj 2 K s ∈ ((∅ : Set (projectiveSL 2 K)) ∪ modelT 2 K N) :=
        Or.inr ⟨s, t, hs, rfl⟩
      have h2 := hfix _ hmem
      show ι.symm (α (ι (QuotientGroup.mk s))) = QuotientGroup.mk s
      have h3 : ι (QuotientGroup.mk s) = proj 2 K s := rfl
      rw [h3, h2]
      rfl
    exact (MulAut.congr ι.symm).injective (by rw [h1, map_one])
  · refine isPGroup_closure_of_subset_map slRep_injective (isNilpotent_toLin' hN) (proj 2 K) ?_
    rintro q (hq | ⟨s, t, hs, rfl⟩)
    · exact hq.elim
    · exact ⟨_, uni_mem_flagSub hs, rfl⟩

theorem kdCharPAt_A_one (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A 1 q).Valid)
    {p : ℕ} (hp2 : p ≠ 2) (hpq : p = q.p) :
    KDCharPAt p (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  subst hpq
  have hlin : CFSG.AGLEmbedding.IsLinTwoIndex q.p q.exponent ⟨.A 1 q, hv⟩ := ⟨q, rfl, rfl, rfl⟩
  obtain ⟨e1⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hlin
  let ι : PSL2 (GaloisField q.p q.exponent) ≃* projectiveSL 2 (GaloisField q.p q.exponent) :=
    LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 _
  let E : (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group ≃*
      projectiveSL 2 (GaloisField q.p q.exponent) := e1.trans ι
  have hKq : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  have hodd : IsOddPrimePower (Nat.card (GaloisField q.p q.exponent)) :=
    ⟨q.p, q.exponent, q.prime_p, q.prime_p.odd_of_ne_two hp2, q.exponent_pos, hKq⟩
  have h4 : 4 ≤ q.p ^ q.exponent := by
    have := hv
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff] at this
    simpa [TauCeti.PrimePower.card_def] using this.1.2 rfl
  have hKc : 3 < Nat.card (GaloisField q.p q.exponent) := by rw [hKq]; omega
  haveI : NeZero q.exponent := ⟨q.exponent_pos.ne'⟩
  have hfs : ∃ s : Finset (GaloisField q.p q.exponent), s.card = 4 := by
    haveI : Fintype (GaloisField q.p q.exponent) := Fintype.ofFinite _
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset
      (GaloisField q.p q.exponent))) (n := 4) (by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
    exact ⟨t, ht⟩
  exact kdCharPAt_of_frame E (center_projectiveSL_eq_bot_of_simple (by omega) (Or.inr hfs))
    fun y hy => frame_projectiveSL_two hodd hKc hp2 y hy

end CFSG.HardMathSupport.Dickson.KD
