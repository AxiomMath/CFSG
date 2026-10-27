module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Base
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdEven
public import CFSG.LocalAnalysis.ComponentClassification.OddSelector

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup Assembly.LowTwoRank LocalAnalysis.ComponentInitial.LinearFlag

theorem exists_ne_comm_of_center_eq_bot {X : Type*} [Group X] [Nontrivial X]
    (h : center X = ⊥) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have ht : center X = ⊤ := eq_top_iff.mpr fun x _ => mem_center_iff.mpr fun g => hc g x
  rw [h] at ht
  exact bot_ne_top ht

theorem psl4 : CF23InnerFusionFor fun Y _ =>
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel Y .PSL 4 p f := by
  intro G _ _ N hN hC hY α J hα hJN hJα hJ hstd hsmall hZ hexc
  obtain ⟨p, f, hp, hp2, hf, hm⟩ := hY
  exfalso
  apply hexc
  have := hN
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := RestrictedStd.statedClassicalModel_of_lieModel_PSL hm
  let φ' : ↥N ≃* projectiveSL 4 K := φ.trans (SymmetricLocal.statedProjEquivProjectiveSL 4 K)
  have : IsSimpleGroup (projectiveSL 4 K) :=
    OutcomeLocal.isSimpleGroup_projectiveSL (k := K) (by norm_num)
  have hs : IsSimpleGroup ↥N := φ'.isSimpleGroup
  have hnab : ∃ x y : ↥N, x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ :=
      exists_ne_comm_of_center_eq_bot (OddSelector.center_projectiveSL_eq_bot (k := K)
        (by norm_num : 3 ≤ 4))
    exact ⟨φ'.symm a, φ'.symm b, fun h => hab (by simpa using congrArg φ' h)⟩
  have hJc : Assembly.IsComponentOf J (centralizer ({α} : Set G)) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hJα).2 hJ
  obtain ⟨p', f', hp'2, hsrc⟩ : ∃ p' f' : ℕ, p' ≠ 2 ∧
      (StatedClassicalModel (↥J ⧸ center ↥J) .PSL 2 p' f' ∨
        Nonempty (↥J ⧸ center ↥J ≃* alternatingGroup (Fin 7)) ∨
        StatedClassicalModel (↥J ⧸ center ↥J) .PSL 3 2 2) := by
    rcases hsmall with ⟨p', f', -, hp'2, -, -, hm'⟩ | h7
    · exact ⟨p', f', hp'2, Or.inl (RestrictedStd.statedClassicalModel_of_lieModel_PSL hm')⟩
    · exact ⟨3, 1, by decide, Or.inr (Or.inl h7)⟩
  obtain ⟨-, -, -, -, -, hpp, hff, -, hJm, -⟩ :=
    OddSelector.faithful_odd_higher_linear_socle_selector_core hs hnab hC hα hJN hJc hstd hp'2
      hsrc (fun _ => Or.inr hZ) (le_refl 4) hp hp2 hf hK φ'
  rw [hpp, hff] at hJm
  exact Or.inr (Or.inl ⟨p, f, hp, hp2, hf, Or.inl ⟨by decide, hJm⟩, Or.inl hm⟩)

end CFSG.ComponentClassification.GSThmB.CF23I
