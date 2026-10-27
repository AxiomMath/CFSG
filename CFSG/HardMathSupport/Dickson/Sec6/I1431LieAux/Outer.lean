module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Defs
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Split
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.PartTwo.KFacts
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Dickson.Sec6.I923 (NoL2Layer FamOK noL2_of_conj_descent)

theorem d4Vocab_innDiag_le (Y : Type) [Group Y] : d4Vocab.innDiag Y ≤ innAutDerived Y := by
  intro e he
  simp only [d4Vocab] at he
  split_ifs at he with hd
  · exact innerAut_le_innAutDerived Y he
  · exact he

theorem Y1431Cfg.mem_innAutDerived {Y : Type} [Group Y] [Finite Y] {Â : Subgroup (MulAut Y)}
    {ξ : MulAut Y} {J : Subgroup Y} {q : ℕ} (c : Y1431Cfg d4Vocab Y Â ξ J q) {e : MulAut Y}
    (he : e ∈ Â) : e ∈ innAutDerived Y :=
  d4Vocab_innDiag_le Y (c.inn e he)

theorem Y1431Cfg.pow_three {V : InndiagVocab} {Y : Type} [Group Y] [Finite Y]
    {Â : Subgroup (MulAut Y)} {ξ : MulAut Y} {J : Subgroup Y} {q : ℕ}
    (c : Y1431Cfg V Y Â ξ J q) : ξ ^ 3 = 1 :=
  c.elemAbelian.2 ξ c.mem

theorem ten_le_of_cube {q q0 : ℕ} (hq0 : 4 ≤ q0) (hqq : q = q0 ^ 3) : 10 ≤ q := by
  have : 4 ^ 3 ≤ q0 ^ 3 := Nat.pow_le_pow_left hq0 3
  omega

theorem centerDescend_mem_innAutDerived {Y : Type*} [Group Y] {α : MulAut Y}
    (h : α ∈ innAutDerived Y) :
    centerDescend Y α ∈ innAutDerived (Y ⧸ Subgroup.center Y) := by
  have hle : innAutDerived Y ≤ (innAutDerived (Y ⧸ Subgroup.center Y)).comap (centerDescend Y) := by
    refine sup_le ?_ ?_
    · rintro _ ⟨g, rfl⟩
      rw [Subgroup.mem_comap, CFSG.HardMathSupport.Solomon.Coordinator.centerDescend_conj]
      exact innerAut_le_innAutDerived _ ⟨_, rfl⟩
    · rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_comap, map_commutatorElement]
      exact commutator_le_innAutDerived _ (by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  exact hle h

theorem noL2_of_famOK_outer {Y P : Type} [Group Y] [Finite Y] [Group P]
    (e : (Y ⧸ Subgroup.center Y) ≃* P) (hP : FamOK P) {α : MulAut Y} (h3 : α ^ 3 = 1)
    (hout : ¬ IsInnerAut (MulAut.congr e (centerDescend Y α))) {J : Subgroup Y}
    (hJ : GLAPComponent 3 (Lemma510Ns.fixSub α) J) {r : ℕ} (hr : 10 ≤ r) :
    ¬ IsTypeL2 r (barOf 3 J) := by
  have hψ3 : (MulAut.congr e (centerDescend Y α)) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, h3, map_one, map_one]
  obtain ⟨γ, f, hγ, hf⟩ := hP _ hψ3 hout
  exact CFSG.HardMathSupport.Dickson.Sec6.I923.noL2_of_conj_descent e α rfl hγ hf hJ hr

theorem Y1431Cfg.inner_of_famOK {V : InndiagVocab} {Y : Type} [Group Y] [Finite Y]
    {Â : Subgroup (MulAut Y)} {ξ : MulAut Y} {J : Subgroup Y} {q q0 : ℕ}
    (c : Y1431Cfg V Y Â ξ J q) (hq0 : 4 ≤ q0) (hqq : q = q0 ^ 3) {P : Type} [Group P]
    (e : (Y ⧸ Subgroup.center Y) ≃* P) (hP : FamOK P) :
    IsInnerAut (MulAut.congr e (centerDescend Y ξ)) := by
  by_contra hout
  exact noL2_of_famOK_outer e hP c.pow_three hout c.comp (ten_le_of_cube hq0 hqq) c.typeL2

end CFSG.HardMathSupport.Dickson.Sec6.I1431
