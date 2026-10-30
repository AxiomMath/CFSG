module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddTop

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.Yardstones.Md42047359a2a

private theorem lc3_lieIndexChar_eq (d : TauCeti.LieTypeIndex) :
    lieIndexChar d = d.characteristic := by
  cases d <;> simp [lieIndexChar]

private theorem lc3_fixSubgroup_one {K : Type} [Group K] :
    fixSubgroup (1 : MulAut K) = ⊤ := by
  ext x
  rw [mem_fixSubgroup]
  simp

private theorem lc3_five_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : 5 ≤ p := by
  have h2 := hp.two_le
  by_contra hlt
  push Not at hlt
  interval_cases p <;> first | exact absurd rfl hp2 | exact absurd rfl hp3 | norm_num at hp

section ChevDownThree

set_option linter.unusedSectionVars false

theorem kdChevDownQ_three_of_lieComp (h : LieComp.LieComp) (q : ℕ) : KDChevDownQ 3 q := by
  intro S _ _ hS hna hchev α hα I hI
  by_cases hα1 : α = 1
  · subst hα1
    rw [lc3_fixSubgroup_one] at hI
    obtain ⟨e⟩ := chevQ_pSimple_top_equiv Nat.prime_three hna hI
    exact chev_isChevSimple_of_mulEquiv e hchev
  · have hA : KDAmbSolv 3 := kdAmbSolv_holds Nat.prime_three (by norm_num) u42_fixSubgroup_solvable
    have hInner : KDChevInner 3 :=
      kdChevInner_of Nat.prime_three (by norm_num)
        (kdCharP_of_lieQConstrainedInner Nat.prime_three
          (CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.lieQConstrainedInner_odd
            Nat.prime_three (by norm_num))) hA
    rcases hchev with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
    · cases i with
      | cyclic r hr => exact (show False from hi).elim
      | alternating n hn => exact (show False from hi).elim
      | sporadic s => exact (show False from hi).elim
      | lie d =>
        have hd : d.1.characteristic = q := hi
        have hC := (h S hS hna d ⟨e⟩ α hα I hI).1.chev
        rw [lc3_lieIndexChar_eq, hd] at hC
        exact hC
    · exact (kdAmbDownQ_holds (q := q) Nat.prime_three (by norm_num) hInner hA)
        S i hi ⟨e⟩ α hα hα1 I hI

end ChevDownThree

section ChevClosureThree

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

theorem chevClosureQAt_three_of_lieComp (h : LieComp.LieComp) : ChevClosureQAt G 3 :=
  chevClosureQAt_of_kdChevDownQ CFSG.LocalAnalysis.GLTheoremA.input18_3_4_holds
    (fun q _ => kdChevDownQ_three_of_lieComp h q)

theorem chevClosureQAt_of_lieComp_lieComps (h3 : LieComp.LieComp)
    (h5 : ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ F, LieComp.LieCompsOn p F)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ChevClosureQAt G p := by
  by_cases hp3 : p = 3
  · subst hp3
    exact chevClosureQAt_three_of_lieComp h3
  · exact chevClosureQAt_of_lieComps (h5 p hp (lc3_five_le hp hp2 hp3))
      (CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.lieQConstrainedInner_odd hp hp2)

end ChevClosureThree

end CFSG.LocalAnalysis.GLTheoremA
