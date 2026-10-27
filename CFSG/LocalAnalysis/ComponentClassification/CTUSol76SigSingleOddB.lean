module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleChar2
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleB

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.Assembly.LowTwoRank

theorem fixedSubgroup_conj_eq_centralizer {T : Type} [Group T] (y : T) :
    FixedCommutingProduct.fixedSubgroup (MulAut.conj y) = centralizer ({y} : Set T) := by
  ext g
  change MulAut.conj y g = g ↔ _
  rw [MulAut.conj_apply, mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem twoComponentsQuasisimpleAt_of_fixed {T : Type} [Group T] [Finite T]
    (hZ : center T = ⊥) (h : CatLeaf.FixedTwoComponentsQuasisimple T) :
    TwoComponentsQuasisimpleAt T := by
  intro y hy2 K hK
  have hyy : y * y = 1 := by rw [← sq, ← hy2, pow_orderOf_eq_one]
  have hα2 : MulAut.conj y * MulAut.conj y = 1 := by
    rw [← map_mul, hyy, map_one]
  have hα1 : MulAut.conj y ≠ 1 := by
    intro h1
    have hyZ : y ∈ center T := by
      rw [mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut T => φ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    rw [hZ, mem_bot] at hyZ
    rw [hyZ, orderOf_one] at hy2
    norm_num at hy2
  have heq := fixedSubgroup_conj_eq_centralizer y
  have hKF : K ≤ FixedCommutingProduct.fixedSubgroup (MulAut.conj y) := heq ▸ hK.1
  have hKp : IsPComponent 2 (K.subgroupOf (FixedCommutingProduct.fixedSubgroup (MulAut.conj y))) :=
    heq ▸ hK.2
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hKF)
    (h (MulAut.conj y) hα2 hα1 _ hKp)

theorem oddLieType_of_oddClassicalRep {S : Type} [Group S] (h : OddClassicalRep S) :
    Blueprint.OddLieType S := by
  obtain ⟨t, n, p, f, hp2, hm⟩ := h
  refine ⟨t, n, p, f, hm.1.1, hp2, hm.1, Or.inl ⟨?_, hm⟩⟩
  cases t
  all_goals first
    | exact (hm.2 : False).elim
    | simp [Blueprint.classicalTags]

theorem oddLieType_of_oddExceptionalRep {S : Type} [Group S] (h : OddExceptionalRep S) :
    Blueprint.OddLieType S := by
  rcases h with ⟨t, p, f, hp2, ht, hm⟩ | ⟨p, f, hm⟩
  · exact ⟨t, 0, p, f, hm.1.1, hp2, hm.1, Or.inr (Or.inl ⟨rfl, ht, hm⟩)⟩
  · have hp3 : p = 3 := hm.1.2.2.2.1
    refine ⟨.twistedG2, 0, p, f, hm.1.1, by omega, hm.1, Or.inr (Or.inr (Or.inl ⟨rfl, ?_, hm⟩))⟩
    simp [Blueprint.reeTitsTags]

section Certified


theorem twoComponentsQuasisimpleAt_of_oddLieType {T : Type} [Group T] [Finite T]
    (hT : IsSimpleGroup T) (hna : ∃ a b : T, a * b ≠ b * a) (h : Blueprint.OddLieType T) :
    TwoComponentsQuasisimpleAt T :=
  twoComponentsQuasisimpleAt_of_fixed (FooteLit.center_eq_bot_of_isSimpleGroup hna)
    (CatLeaf.fixedTwoComponentsQuasisimple_of_oddLieType hna h)

theorem singleComponentQuasisimpleAt_classical_of_clean
    (h : SingleComponentCleanAt (fun S _ => OddClassicalRep S)) :
    SingleComponentQuasisimpleAt (fun S _ => OddClassicalRep S) :=
  singleComponentQuasisimpleAt_of_clean
    (fun _ _ _ hT hna hP => twoComponentsQuasisimpleAt_of_oddLieType hT hna
      (oddLieType_of_oddClassicalRep hP)) h

theorem singleComponentQuasisimpleAt_exceptional_of_clean
    (h : SingleComponentCleanAt (fun S _ => OddExceptionalRep S)) :
    SingleComponentQuasisimpleAt (fun S _ => OddExceptionalRep S) :=
  singleComponentQuasisimpleAt_of_clean
    (fun _ _ _ hT hna hP => twoComponentsQuasisimpleAt_of_oddLieType hT hna
      (oddLieType_of_oddExceptionalRep hP)) h

end Certified

end CFSG.ComponentClassification.Sol76.Sig
