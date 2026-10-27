module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YD4Gen
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Witness46

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YD4

open CFSG.Open

theorem descend_simple {Q S T : Type} [Group Q] [Group S] [Group T] [IsSimpleGroup T]
    (hTnc : ¬ ∀ a b : T, a * b = b * a) (π : Q →* S)
    (hker : ∀ x, π x = 1 → x ∈ Subgroup.center Q) {X : Subgroup Q} (f : ↥X →* T)
    (hf : Function.Surjective f) :
    ∃ φ : (π.comp X.subtype).range →* T, Function.Surjective φ ∧
      ∀ x : ↥X, φ ((π.comp X.subtype).rangeRestrict x) = f x := by
  have hZT : Subgroup.center T = ⊥ := center_eq_bot_of_simple_of_not_comm hTnc
  have hk : (π.comp X.subtype).ker ≤ f.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have h1 : π (x : Q) = 1 := hx
    have h2 : (x : Q) ∈ Subgroup.center Q := hker _ h1
    have : f x ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨y, rfl⟩ := hf s
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_center_iff.1 h2 y)
    rw [hZT, Subgroup.mem_bot] at this
    exact this
  obtain ⟨φ, hφ⟩ := exists_descend (π.comp X.subtype) f hk
  refine ⟨φ, ?_, hφ⟩
  intro t
  obtain ⟨x, rfl⟩ := hf t
  exact ⟨_, hφ x⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YD4

end
