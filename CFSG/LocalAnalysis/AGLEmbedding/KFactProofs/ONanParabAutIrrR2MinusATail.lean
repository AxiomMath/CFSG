module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailUnipotentGroup
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailSubspaceCount
public import CFSG.RankThree.PartOne.AUTSL.FrobPair

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.RankThree.PartOne.AUTSL
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

section Tail

variable {K : Type} [Field K] (b c : K)

@[expose] def tailA (a : Fin 2 → K) : Fin 2 → K := ![a 0 ^ 2 + c * a 1 ^ 2, b * a 1 ^ 2]

end Tail

section Iso

variable {K : Type} [Field K] (n : ℕ) (hn : 1 ≤ n) (b c : K)

@[expose] noncomputable def mnIso :
    (quadTail (n - 1) (minusTailForm K b c)).IsometryEquiv (coordinateQuadMinus n K hn b c) :=
  (minusTailIsometry n K b c).trans (coordinateMinusIsometry n K hn b c)

theorem mnIso_apply (v : (Fin (n - 1) ⊕ Fin (n - 1) → K) × (Fin 2 → K)) (k : Fin (2 * n)) :
    mnIso n hn b c v k =
      tailModelEquiv (n - 1) K (Fin 2) v ((minusIndexEquiv n hn).symm k) := rfl

theorem mnIso_inl (v : (Fin (n - 1) ⊕ Fin (n - 1) → K) × (Fin 2 → K)) (i : Fin (n - 1)) :
    mnIso n hn b c v (minusIndexEquiv n hn (.inl i)) = v.1 (.inl i) := by
  rw [mnIso_apply, Equiv.symm_apply_apply]
  rfl

theorem mnIso_inr (v : (Fin (n - 1) ⊕ Fin (n - 1) → K) × (Fin 2 → K)) (i : Fin (n - 1)) :
    mnIso n hn b c v (minusIndexEquiv n hn (.inr (.inl i))) = v.1 (.inr i) := by
  rw [mnIso_apply, Equiv.symm_apply_apply]
  rfl

theorem mnIso_tail (v : (Fin (n - 1) ⊕ Fin (n - 1) → K) × (Fin 2 → K)) (j : Fin 2) :
    mnIso n hn b c v (minusIndexEquiv n hn (.inr (.inr j))) = v.2 j := by
  rw [mnIso_apply, Equiv.symm_apply_apply]
  rfl

end Iso

section Frob

variable {K : Type} [Field K] [Finite K] [CharP K 2] (n : ℕ) (hn : 1 ≤ n) (b c : K) (hb : b ≠ 0)

@[expose] noncomputable def mnFrob :
    ((Fin (n - 1) ⊕ Fin (n - 1) → K) × (Fin 2 → K)) ≃+
      ((Fin (n - 1) ⊕ Fin (n - 1) → K) × (Fin 2 → K)) :=
  (mnIso n hn b c).toLinearEquiv.toAddEquiv.trans
    ((coordinateSemilinearMap (frobElt n hn b c hb)).trans
      (mnIso n hn b c).symm.toLinearEquiv.toAddEquiv)

theorem mnIso_mnFrob (v : (Fin (n - 1) ⊕ Fin (n - 1) → K) × (Fin 2 → K)) :
    mnIso n hn b c (mnFrob n hn b c hb v) =
      coordinateSemilinearMap (frobElt n hn b c hb) (mnIso n hn b c v) := by
  change (mnIso n hn b c).toLinearEquiv ((mnIso n hn b c).symm.toLinearEquiv
    (coordinateSemilinearMap (frobElt n hn b c hb) (mnIso n hn b c v))) = _
  exact (mnIso n hn b c).toLinearEquiv.apply_symm_apply _

theorem mnFrob_fst (v : (Fin (n - 1) ⊕ Fin (n - 1) → K) × (Fin 2 → K))
    (s : Fin (n - 1) ⊕ Fin (n - 1)) : (mnFrob n hn b c hb v).1 s = v.1 s ^ 2 := by
  have h := mnIso_mnFrob n hn b c hb v
  rw [frobElt_apply] at h
  rcases s with i | i
  · have h1 := congrFun h (minusIndexEquiv n hn (.inl i))
    rw [mnIso_inl, tailLin_other n hn b c _ (tailZero_ne_inl n hn i) (tailOne_ne_inl n hn i),
      mnIso_inl] at h1
    exact h1
  · have h1 := congrFun h (minusIndexEquiv n hn (.inr (.inl i)))
    rw [mnIso_inr, tailLin_other n hn b c _ (tailZero_ne_inr n hn i) (tailOne_ne_inr n hn i),
      mnIso_inr] at h1
    exact h1

theorem mnFrob_snd (v : (Fin (n - 1) ⊕ Fin (n - 1) → K) × (Fin 2 → K)) :
    (mnFrob n hn b c hb v).2 = tailA b c v.2 := by
  have h := mnIso_mnFrob n hn b c hb v
  rw [frobElt_apply] at h
  funext j
  fin_cases j
  · have h1 := congrFun h (minusIndexEquiv n hn (.inr (.inr 0)))
    have h2 : minusIndexEquiv n hn (.inr (.inr 0)) = tailZero n hn := rfl
    have h3 : minusIndexEquiv n hn (.inr (.inr 1)) = tailOne n hn := rfl
    rw [mnIso_tail, h2, tailLin_zero, ← h2, ← h3, mnIso_tail, mnIso_tail] at h1
    exact h1
  · have h1 := congrFun h (minusIndexEquiv n hn (.inr (.inr 1)))
    have h3 : minusIndexEquiv n hn (.inr (.inr 1)) = tailOne n hn := rfl
    rw [mnIso_tail, h3, tailLin_one, ← h3, mnIso_tail] at h1
    exact h1

theorem mnFrob_hypVec (u : Fin (n - 1) ⊕ Fin (n - 1)) :
    mnFrob n hn b c hb (hypVec K (Fin 2 → K) u) = hypVec K (Fin 2 → K) u := by
  refine Prod.ext (funext fun s => ?_) ?_
  · rw [mnFrob_fst]
    by_cases h : s = u
    · simp [hypVec, h]
    · simp [hypVec, h]
  · rw [mnFrob_snd]
    funext j
    fin_cases j <;> simp [hypVec, tailA]

theorem mnFrob_inr (a : Fin 2 → K) :
    mnFrob n hn b c hb ((0 : Fin (n - 1) ⊕ Fin (n - 1) → K), a) = (0, tailA b c a) := by
  refine Prod.ext (funext fun s => ?_) ?_
  · rw [mnFrob_fst]
    simp
  · rw [mnFrob_snd]

include hn hb in
theorem tailA_eq_zero_iff (a : Fin 2 → K) : tailA b c a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have h1 : mnFrob n hn b c hb ((0 : Fin (n - 1) ⊕ Fin (n - 1) → K), a) =
        mnFrob n hn b c hb 0 := by
      rw [mnFrob_inr, map_zero]
      exact Prod.ext rfl h
    have := congrArg Prod.snd ((mnFrob n hn b c hb).injective h1)
    exact this
  · rintro rfl
    funext j
    fin_cases j <;> simp [tailA]

include hn hb in
theorem tailA_surjective (a : Fin 2 → K) : ∃ a' : Fin 2 → K, tailA b c a' = a := by
  obtain ⟨v, hv⟩ := (mnFrob n hn b c hb).surjective ((0 : Fin (n - 1) ⊕ Fin (n - 1) → K), a)
  have h1 : v.1 = 0 := by
    funext s
    have := congrArg (fun w => w.1 s) hv
    simp only [mnFrob_fst, Pi.zero_apply] at this
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  refine ⟨v.2, ?_⟩
  have := congrArg Prod.snd hv
  rw [mnFrob_snd] at this
  exact this

theorem mem_tailFlag_mnFrob_iff (k : ℕ) (v : (Fin (n - 1) ⊕ Fin (n - 1) → K) × (Fin 2 → K)) :
    mnFrob n hn b c hb v ∈ tailFlag K (Fin 2 → K) (n - 1) k ↔
      v ∈ tailFlag K (Fin 2 → K) (n - 1) k := by
  rw [mem_tailFlag_iff, mem_tailFlag_iff, mem_flag_iff_coord, mem_flag_iff_coord, mnFrob_snd,
    tailA_eq_zero_iff n hn b c hb]
  simp only [mnFrob_fst, pow_eq_zero_iff two_ne_zero]

end Frob

section Conj

variable {K : Type} [Field K] [Finite K] [CharP K 2] (n : ℕ) (hn : 1 ≤ n) (b c : K) (hb : b ≠ 0)

theorem mnStabDiag_fst_of_rel {g g' : ((Fin (n - 1) ⊕ Fin (n - 1) → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin (n - 1) ⊕ Fin (n - 1) → K) × (Fin 2 → K))}
    (h : ∀ y, g' (mnFrob n hn b c hb y) = mnFrob n hn b c hb (g y)) (i : Fin (n - 1)) :
    (stabDiag g').1 i = (stabDiag g).1 i ^ 2 := by
  change (g' (hypVec K (Fin 2 → K) (.inl i))).1 (.inl i) =
    ((g (hypVec K (Fin 2 → K) (.inl i))).1 (.inl i)) ^ 2
  have h1 := h (hypVec K (Fin 2 → K) (.inl i))
  rw [mnFrob_hypVec] at h1
  rw [h1, mnFrob_fst]

theorem mnStabDiag_snd_of_rel {g g' : ((Fin (n - 1) ⊕ Fin (n - 1) → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin (n - 1) ⊕ Fin (n - 1) → K) × (Fin 2 → K))}
    (h : ∀ y, g' (mnFrob n hn b c hb y) = mnFrob n hn b c hb (g y)) (a : Fin 2 → K) :
    (stabDiag g').2 (tailA b c a) = tailA b c ((stabDiag g).2 a) := by
  change (g' (0, tailA b c a)).2 = tailA b c (g (0, a)).2
  have h1 := h (0, a)
  rw [mnFrob_inr] at h1
  rw [h1, mnFrob_snd]

theorem mnMapTailFlag_of_rel {g g' : ((Fin (n - 1) ⊕ Fin (n - 1) → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin (n - 1) ⊕ Fin (n - 1) → K) × (Fin 2 → K))}
    (h : ∀ y, g' (mnFrob n hn b c hb y) = mnFrob n hn b c hb (g y)) {k : ℕ}
    (hg : (tailFlag K (Fin 2 → K) (n - 1) k).map
      (g : ((Fin (n - 1) ⊕ Fin (n - 1) → K) × (Fin 2 → K)) →ₗ[K] _) =
        tailFlag K (Fin 2 → K) (n - 1) k) :
    (tailFlag K (Fin 2 → K) (n - 1) k).map
      (g' : ((Fin (n - 1) ⊕ Fin (n - 1) → K) × (Fin 2 → K)) →ₗ[K] _) =
        tailFlag K (Fin 2 → K) (n - 1) k := by
  have hiff : ∀ y, y ∈ tailFlag K (Fin 2 → K) (n - 1) k ↔
      g y ∈ tailFlag K (Fin 2 → K) (n - 1) k := by
    intro y
    constructor
    · intro hy
      rw [← hg]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← hg] at hy
      obtain ⟨w, hw, hwy⟩ := hy
      have : w = y := g.injective hwy
      rwa [this] at hw
  have hiff' : ∀ y', y' ∈ tailFlag K (Fin 2 → K) (n - 1) k ↔
      g' y' ∈ tailFlag K (Fin 2 → K) (n - 1) k := by
    intro y'
    obtain ⟨y, rfl⟩ := (mnFrob n hn b c hb).surjective y'
    rw [h, mem_tailFlag_mnFrob_iff n hn b c hb, mem_tailFlag_mnFrob_iff n hn b c hb]
    exact hiff y
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    exact (hiff' w).1 hw
  · intro v hv
    refine ⟨g'.symm v, (hiff' _).2 (by simpa using hv), by simp⟩

end Conj

end CFSG.AGLEmbedding.ParabAutIrr
