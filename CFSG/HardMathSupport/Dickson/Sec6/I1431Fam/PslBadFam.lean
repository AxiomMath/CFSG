module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadMain
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagPSLn
public import CFSG.RankThree.PartTwo.Sec4.Item413AutGen
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Outer
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

@[expose] def FamPslBadThree : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t n p f => FamPslBad t n p f ∧ n = 3

theorem y1431_noCfg_pslBadThree (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    Y1431NoCfgAt FamPslBadThree := by
  intro Y _ _ Â ξ J q c t n p f hadm ht hF hm q0 hq0 hqq
  obtain ⟨⟨rfl, hn3, hnc⟩, rfl⟩ := hF
  have hC : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL 3 p f :=
    (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  let e : (Y ⧸ Subgroup.center Y) ≃* projectiveSL 3 K := e0.trans (statedProjEquiv 3 K)
  have cS := c.descend e
  have hp : p.Prime := hadm.1
  have h3 : 3 ∣ p ^ f - 1 := by
    by_contra h
    apply hnc
    have : Nat.gcd 3 (p ^ f - 1) = 1 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h
    rw [this]
    exact Nat.coprime_one_right 3
  have hp3 : p ≠ 3 := by
    rintro rfl
    have h1 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by have := hadm.2.1; omega)
    have h2 : 0 < 3 ^ f := pow_pos (by norm_num) f
    omega
  have hpk : (3 : K) ≠ 0 := CFSG.RankThree.PartTwo.Sec4.three_ne_zero_of_card hp hp3 hK
  have hA : ∀ a ∈ Â.map (descendHom e), a ∈ linearAutGroup 3 K := by
    rintro _ ⟨a', ha', rfl⟩
    have h1 : MulAut.congr e (centerDescend Y a') ∈ innAutDerived (projectiveSL 3 K) :=
      (mem_innAutDerived_congr e).2 (centerDescend_mem_innAutDerived (c.mem_innAutDerived ha'))
    exact innAutDerived_le_linearAutGroup (by norm_num) h1
  exact s1431_false_psl_bad_three hpk hO cS (ten_le_of_cube hq0 hqq) hA

end CFSG.HardMathSupport.Dickson.Sec6.I1431
