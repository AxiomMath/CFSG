module

public import CFSG.HardMathSupport.Dickson.KD.CharPAux.Frame
public import CFSG.HardMathSupport.Dickson.KD.CharPAux.FlagGroup

public section

namespace CFSG.HardMathSupport.Dickson.KD

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.HardMathSupport.Timmesfeld.DefChar.Orth

section A

variable {n : ℕ} {K : Type} [Field K]

@[expose] def slRep (n : ℕ) (K : Type*) [Field K] :
    Matrix.SpecialLinearGroup (Fin n) K →* Module.End K (Fin n → K) where
  toFun s := Matrix.toLin' (s : Matrix (Fin n) (Fin n) K)
  map_one' := by
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.toLin'_one]
    rfl
  map_mul' a b := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.toLin'_mul, Module.End.mul_eq_comp]

theorem slRep_injective : Function.Injective (slRep n K) := fun a b h =>
  Subtype.ext (Matrix.toLin'.injective h)

theorem mem_Wsp_iff {N : Matrix (Fin n) (Fin n) K} {x : Fin n → K} :
    x ∈ Wsp N ↔ x ∈ LinearMap.ker (Matrix.toLin' N) ⊓ LinearMap.range (Matrix.toLin' N) := by
  rw [Matrix.toLin'_apply']
  rfl

theorem tvSL_mem_flagSub {N : Matrix (Fin n) (Fin n) K} {w ψ : Fin n → K} (h : ψ ⬝ᵥ w = 0)
    (hw : w ∈ Wsp N) (hψ : ψ ∈ Fsp N) :
    tvSL w ψ h ∈ flagSub (slRep n K) (Matrix.toLin' N) := by
  show InFlag (Matrix.toLin' N) (Matrix.toLin' ((tvSL w ψ h : Matrix.SpecialLinearGroup (Fin n) K) :
    Matrix (Fin n) (Fin n) K))
  rw [coe_tvSL, map_add, Matrix.toLin'_one]
  refine inFlag_one_add ?_ ?_ ?_
  · rw [toLin'_mul_eq, toLin'_mul_eq, zN_eq_zero hψ, Nz_eq_zero hw]
  · intro x _
    rw [Matrix.toLin'_apply, vecMulVec_mulVec]
    simp only [op_smul_eq_smul]
    exact Submodule.smul_mem _ _ (mem_Wsp_iff.1 hw)
  · intro x hx
    rw [Matrix.toLin'_apply, vecMulVec_mulVec, dot_eq_zero_of_mem (mem_Wsp_iff.2 hx) hψ]
    simp

theorem uni_mem_flagSub {N : Matrix (Fin n) (Fin n) K} {s : Matrix.SpecialLinearGroup (Fin n) K}
    {t : K} (hs : (s : Matrix (Fin n) (Fin n) K) = 1 + t • N) :
    s ∈ flagSub (slRep n K) (Matrix.toLin' N) := by
  show InFlag (Matrix.toLin' N) (Matrix.toLin' (s : Matrix (Fin n) (Fin n) K))
  rw [hs, map_add, Matrix.toLin'_one, map_smul]
  refine inFlag_one_add ?_ ?_ ?_
  · rw [smul_mul_assoc, mul_smul_comm]
  · intro x hx
    rw [LinearMap.smul_apply, LinearMap.mem_ker.1 hx, smul_zero]
    exact Submodule.zero_mem _
  · intro x hx
    rw [LinearMap.smul_apply, LinearMap.mem_ker.1 hx.1, smul_zero]

theorem frame_projectiveSL [NeZero n] {p : ℕ} [Fact p.Prime] [CharP K p] [Finite K] (hp2 : p ≠ 2)
    (hn : 3 ≤ n) (y : projectiveSL n K) (hy : orderOf y = p) : Frame p y := by
  obtain ⟨N, hN, hN0, hy0⟩ := exists_nilpotent_of_orderOf_eq (p := p) y hy
  have hne : Nontrivial (Fin n → K) := by
    haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_neZero n⟩⟩
    infer_instance
  refine ⟨modelGen n K N, modelT n K N, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    rw [hy0]
    exact model_h1 hN q hq
  · intro s q hs hq
    rw [hy0] at hs
    exact model_hT hN s q hs hq
  · intro s q hs hq
    rw [hy0] at hs
    exact model_hGen hN s q hs hq
  · intro s hs hfix
    exact model_huniq hN hp2 hn hN0 _
      (Nat.Coprime.coprime_dvd_left (orderOf_map_dvd MulAut.conj s) hs) hfix
  · refine isPGroup_closure_of_subset_map slRep_injective (isNilpotent_toLin' hN) (proj n K) ?_
    rintro q (⟨w, ψ, h, hw, hψ, rfl⟩ | ⟨s, t, hs, rfl⟩)
    · exact ⟨_, tvSL_mem_flagSub h hw hψ, rfl⟩
    · exact ⟨_, uni_mem_flagSub hs, rfl⟩

theorem center_projectiveSL_eq_bot_of_simple (hn : 2 ≤ n)
    (h : 3 ≤ n ∨ ∃ s : Finset K, s.card = 4) : Subgroup.center (projectiveSL n K) = ⊥ := by
  have hsimple : IsSimpleGroup (projectiveSL n K) := by
    have := (CFSG.LinearGroups.linear_projective_simple (K := K) (n := n) hn h).2.1
    exact (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K).symm.isSimpleGroup
  have hperf : Group.IsPerfect (projectiveSL n K) := by
    have := CFSG.LinearGroups.linear_projective_perfect (K := K) (n := n) hn h
    exact Group.IsPerfect.ofSurjective
      (f := (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K).toMonoidHom)
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K).surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (projectiveSL n K)) with h | h
  · exact h
  · exfalso
    have h1 := (commutator_eq_bot_iff_center_eq_top (projectiveSL n K)).2 h
    rw [Group.IsPerfect.commutator_eq_top] at h1
    exact top_ne_bot h1

theorem kdCharPAt_A (q : TauCeti.PrimePower) (r : ℕ) (hv : (TauCeti.LieTypeIndex.A r q).Valid)
    (hr : 2 ≤ r) {p : ℕ} (hp2 : p ≠ 2) (hpq : p = q.p) :
    KDCharPAt p (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  subst hpq
  let e : (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group ≃*
      projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _)
  have hn : 3 ≤ r + 1 := by omega
  haveI : NeZero (r + 1) := ⟨by omega⟩
  haveI : NeZero q.exponent := ⟨q.exponent_pos.ne'⟩
  exact kdCharPAt_of_frame e (center_projectiveSL_eq_bot_of_simple (by omega) (Or.inl hn))
    fun y hy => frame_projectiveSL hp2 hn y hy

end A

end CFSG.HardMathSupport.Dickson.KD
