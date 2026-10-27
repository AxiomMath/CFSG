module

public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.CertCases
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

@[expose] def negIter (τ : List ℤ) (j : ℕ) : List ℤ :=
  (fun v => lmulVec Tag.E7.rank negWList v)^[j] τ

@[expose] def SpanGen (τ : List ℤ) (X : List (List ℤ)) : Prop :=
  ∀ α ∈ X, ∃ i ∈ List.range 6, ∃ j ∈ List.range 6, ∃ s₁ ∈ [(-1 : ℤ), 0, 1],
    ∃ s₂ ∈ [(-1 : ℤ), 0, 1],
      α = vadd Tag.E7.rank (vsmul Tag.E7.rank s₁ (negIter τ i))
        (vsmul Tag.E7.rank s₂ (negIter τ j))

instance (τ : List ℤ) (X : List (List ℤ)) : Decidable (SpanGen τ X) := by
  unfold SpanGen
  infer_instance

@[expose] def e7CompA (c : E7T3Cert) : List (List ℤ) :=
  (e7StdRoots (e7T3Nodes 0)).map (lmulVec Tag.E7.rank (e7wl c.w))

@[expose] def e7CompB (c : E7T3Cert) : List (List ℤ) :=
  (e7StdRoots (e7T3Nodes 1)).map (lmulVec Tag.E7.rank (e7wl c.w))

theorem cert_cases01 : ∀ c ∈ e7T3Certs, c.comps.map E7T3Comp.kind = [0, 1] →
    sigma0 ∈ c.rootList →
    c.Good ∧ sigma0 ∈ e7CompB c ∧ SpanGen sigma0 (e7CompB c) ∧
      ∃ τ ∈ e7CompA c, SpanGen τ (e7CompA c) := by
  decide +kernel

theorem toVec_negIter (τ : List ℤ) (j : ℕ) :
    toVec Tag.E7.rank (negIter τ j) =
      ((((-1 : ℤ) • e7T3W) ^ j) *ᵥ toVec Tag.E7.rank τ) := by
  induction j with
  | zero => simp [negIter]
  | succ j ih =>
    have h : negIter τ (j + 1) = lmulVec Tag.E7.rank negWList (negIter τ j) := by
      simp only [negIter, Function.iterate_succ_apply']
    have hm : toMat Tag.E7.rank negWList = (-1 : ℤ) • e7T3W := by
      rw [negWList, e7T3W_eq]
      ext i j
      simp [toMat, lsmul, lofFn, lget]
    rw [h, toVec_lmulVec, hm, pow_succ', ← Matrix.mulVec_mulVec, ih]

theorem rootChar_kill_of_spanGen {L : Type} [Field L] {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {be : Fin Tag.E7.rank → Lˣ}
    (hbe : be ∈ fixedCharTuples ((-1 : ℤ) • e7T3W) Fr) {τ : List ℤ} {X : List (List ℤ)}
    (hX : SpanGen τ X) (hτ : rootChar be (toVec Tag.E7.rank τ) = 1) :
    ∀ α ∈ X, rootChar be (toVec Tag.E7.rank α) = 1 := by
  intro α hα
  obtain ⟨i, -, j, -, s₁, -, s₂, -, rfl⟩ := hX α hα
  have hk : ∀ m : ℕ, rootChar be (toVec Tag.E7.rank (negIter τ m)) = 1 := fun m => by
    rw [toVec_negIter, rootChar_pow_mulVec_of_mem_fixedCharTuples hFr hbe m, hτ, one_pow]
  rw [toVec_vadd, toVec_vsmul, toVec_vsmul, rootChar_add, rootChar_zsmul, rootChar_zsmul, hk, hk,
    one_zpow, one_zpow, one_mul]

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
