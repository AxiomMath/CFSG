module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269R3
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269R4
public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Bridge
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

namespace I269R

theorem exists_noncomm_of_simple_not_prime {S : Type} [Group S] [IsSimpleGroup S]
    (hc : ¬ (Nat.card S).Prime) : ∃ a b : S, a * b ≠ b * a := by
  by_contra h
  simp only [not_exists, ne_eq, not_not] at h
  letI : CommGroup S := { ‹Group S› with mul_comm := fun a b => h a b }
  exact hc ((CommGroup.is_simple_iff_prime_card (α := S)).1 ‹IsSimpleGroup S›)

theorem center_eq_bot_of_simple {T : Type} [Group T] [IsSimpleGroup T]
    (hnc : ∃ a b : T, a * b ≠ b * a) : Subgroup.center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    have ha : a ∈ Subgroup.center T := by rw [h]; trivial
    exact (Subgroup.mem_center_iff.1 ha b).symm

end I269R

section Certs


theorem e9Solv_d4two (S : Type) [Group S] (h : catalogIs S S9.isD4two) : E9Solv S := by
  obtain ⟨q, hv, hq, ⟨e₀⟩⟩ := CatB.lieIndex_isD4two h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq.trans (by norm_num))
  have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD 4 q hv e₀
  rw [h1, h2] at hmodel
  have hcard : Nat.card S = 2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7 := by
    have := (CFSG.Timmesfeld.card_statedClassicalModel_two hmodel).2.2.2.1 rfl
    rw [this]
    decide +kernel
  haveI : Finite S := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨-, hsimp⟩ :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaPlus S 4 2 1 hmodel
  have hZ : Subgroup.center S = ⊥ :=
    I269R.center_eq_bot_of_simple (I269R.exists_noncomm_of_simple_not_prime
      (by rw [hcard]; norm_num))
  obtain ⟨eS⟩ := CatB.bridge_d4two h
  let e1 : S ≃* StatedProj (StatedOmega (StatedQuadPlus 4 (ZMod 2))) :=
    eS.trans (CatB.statedProjZMod2Equiv (StatedOmega (StatedQuadPlus 4 (ZMod 2)))).symm
  let eO : StatedProj (StatedOmega (StatedQuadPlus 4 (ZMod 2))) ≃* I269R.OG :=
    CFSG.HardMathSupport.Curtis.Coordinator.projEquivElementary (ZMod 2) (by simp) (n := 4)
      (by norm_num)
  obtain ⟨eA⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup (ZMod 2)
  refine I269R.e9Solv_of_props hZ hcard ?_ ?_ ?_ ?_
  · exact I269R.noThreeSeven_orth.of_mulEquiv (e1.trans eO)
  · exact I269R.noNineFive_orth.of_mulEquiv (e1.trans eO)
  · exact I269R.innerPair_adjoint.of_mulEquiv (e1.trans eA)
  · exact I269R.outerNoFive_adjoint.of_mulEquiv (e1.trans eA)

end Certs

end CFSG.LocalAnalysis.GLTheoremA

end
