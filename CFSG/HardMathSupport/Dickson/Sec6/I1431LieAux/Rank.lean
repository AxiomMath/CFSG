module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Z3Cube
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagPSLn
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Split

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.PartTwo.KFacts
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCLinPlane CFSG.RankThree.PartOne.Sec66T
  CFSG.ComponentClassification.RankTwoClassical
open CFSG.HardMathSupport.Dickson.Sec6.I923

@[expose] def NoE27 (P : Type) [Group P] : Prop :=
  ¬ ∃ E : Subgroup P, IsElemAbelian 3 E ∧ Nat.card E = 27

@[expose] def NoE27At (Fam : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (P : Type) [Group P] [Finite P] (t : StatedLieTag) (n p f : ℕ),
    StatedLieAdmissible t n p f → t ≠ .Tits → Fam t n p f → LieModel P t n p f → NoE27 P

@[expose] def OutDerived3At (Fam : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (P : Type) [Group P] [Finite P] (t : StatedLieTag) (n p f : ℕ),
    StatedLieAdmissible t n p f → t ≠ .Tits → Fam t n p f → LieModel P t n p f →
    ∀ τ ∈ innAutDerived P, τ ^ 3 = 1 → IsInnerAut τ

theorem OutDerived3At.mono {Fam Fam' : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (hle : ∀ t n p f, Fam' t n p f → Fam t n p f) (h : OutDerived3At Fam) : OutDerived3At Fam' :=
  fun P _ _ t n p f hadm ht hF hm => h P t n p f hadm ht (hle t n p f hF) hm

theorem Y1431NoCfgAt.of_noE27 (h0 : L2CentreThree) {Fam : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (hOut : OutDerived3At Fam) (hrk : NoE27At Fam) : Y1431NoCfgAt Fam := by
  intro Y _ _ Â ξ J q c t n p f hadm ht hF hm q0 hq0 hqq
  have hin := c.mem_innerAut_of_outDerived (MulEquiv.refl _)
    (fun _ => hOut (Y ⧸ Subgroup.center Y) t n p f hadm ht hF hm)
  obtain ⟨E, hE, hcard⟩ := c.exists_elemAbelian_27 h0 hin
  exact hrk (Y ⧸ Subgroup.center Y) t n p f hadm ht hF hm ⟨E, hE, hcard⟩

theorem outDerived3_pslGood : OutDerived3At FamPslGood := by
  intro P _ _ t n p f hadm ht hF hm τ hτ hτ3
  obtain ⟨rfl, hn3, hcop⟩ := hF
  have hC : StatedClassicalModel P .PSL n p f :=
    (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  rw [← hK] at hcop
  let e : P ≃* projectiveSL n K := e0.trans (statedProjEquiv n K)
  have h1 : MulAut.congr e τ ∈ innAutDerived (projectiveSL n K) :=
    (mem_innAutDerived_congr e).2 hτ
  have h2 := innAutDerived_le_linearAutGroup hn3 h1
  have h3 : (MulAut.congr e τ) ^ 3 = 1 := by rw [← map_pow, hτ3, map_one]
  exact (isInnerAut_congr e τ).1 (inner_of_mem_linearAut_of_pow_eq_one hn3 hcop h2 h3)

end CFSG.HardMathSupport.Dickson.Sec6.I1431
