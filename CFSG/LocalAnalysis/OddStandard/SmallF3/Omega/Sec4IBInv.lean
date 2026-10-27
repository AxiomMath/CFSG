module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBSpin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma sec4ISgn_eq_neg_one_of_ne_zero {u : ZMod 2} (hu : u ≠ 0) :
    sec4ISgn u = -1 := by
  revert u
  decide

private lemma sec4IT_mem_commSp_iff (fr : Sec4IFrame Q) (s : Fin 7 → ZMod 2) (v : V) :
    v ∈ commSp (sec4IT fr s) ↔ ∀ i, s i = 0 → fr.b.repr v i = 0 := by
  rw [mem_commSp_iff (sec4IT_mul_self fr s)]
  constructor
  · intro hv i hi
    have h := congrArg (fun w => fr.b.repr w i) hv
    simp only [map_neg] at h
    rw [sec4IT_repr] at h
    rw [hi, sec4ISgn_zero] at h
    have hx : fr.b.repr v i = -fr.b.repr v i := by simpa using h
    have h2 : (2 : ZMod 3) * fr.b.repr v i = 0 := by
      rw [two_mul]
      exact eq_neg_iff_add_eq_zero.mp hx
    exact (mul_eq_zero.mp h2).resolve_left (by decide)
  · intro hv
    apply fr.b.ext_elem
    intro i
    rw [sec4IT_repr, map_neg]
    by_cases hi : s i = 0
    · have hx : (fr.b.repr v) i = 0 := hv i hi
      rw [hi, sec4ISgn_zero, Units.val_one, one_mul]
      rw [Finsupp.neg_apply, hx, neg_zero]
    · rw [sec4ISgn_eq_neg_one_of_ne_zero hi]
      simp

theorem sec4IT_invDim (fr : Sec4IFrame Q) (s : Fin 7 → ZMod 2) :
    invDim (sec4IT fr s) = vecWeight s := by
  have hspan : commSp (sec4IT fr s) =
      Submodule.span (ZMod 3) (fr.b '' {i : Fin 7 | s i ≠ 0}) := by
    apply le_antisymm
    · intro v hv
      rw [Module.Basis.mem_span_image]
      intro i hi
      by_contra hsi
      have h0 : fr.b.repr v i = 0 :=
        (sec4IT_mem_commSp_iff fr s v).mp hv i (not_not.mp hsi)
      exact (Finsupp.mem_support_iff.mp (by simpa using hi)) h0
    · rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact (sec4IT_mem_commSp_iff fr s (fr.b i)).mpr fun j hj => by
        rw [Module.Basis.repr_self, Finsupp.single_apply]
        split_ifs with hji
        · exact absurd (show s i = 0 from hji.symm ▸ hj) hi
        · rfl
  rw [invDim, hspan, Set.image_eq_range]
  have hb : LinearIndependent (ZMod 3)
      (fun i : {j : Fin 7 // s j ≠ 0} => fr.b (i : Fin 7)) :=
    fr.b.linearIndependent.comp (fun i : {j : Fin 7 // s j ≠ 0} => (i : Fin 7))
      Subtype.val_injective
  exact (finrank_span_eq_card hb).trans (by rw [Fintype.card_subtype]; rfl)

theorem sec4IT_invType (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q) {s : Fin 7 → ZMod 2}
    (hs : IsEvenVec s) : invType (sec4IT fr s) = (vecWeight s, (-1) ^ (vecWeight s / 2)) := by
  have ht : sec4IT fr s ∈ omegaGroup hQ := by
    change sec4IMono fr 1 s ∈ omegaGroup hQ
    exact (sec4IMono_mem_omegaGroup_iff hQ fr 1 s).mpr ⟨by simp, hs⟩
  have htype := (involution_mem_omegaGroup_iff hQ (sec4IT_mul_self fr s)).mp ht
  simp only [invType]
  rw [htype.2, sec4IT_invDim fr s]

end CFSG.OddStandard.SmallF3.Omega
