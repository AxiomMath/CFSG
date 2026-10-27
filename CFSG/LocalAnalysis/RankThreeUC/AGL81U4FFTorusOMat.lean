module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OModelT

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open

variable {F : Type} [Field F] [Finite F] {b c : F}

noncomputable abbrev NormOne (M : NormModel F b c) : Subgroup M.Eˣ := rootsOfUnity (Nat.card F + 1) M.E

@[expose] noncomputable def torusO (M : NormModel F b c) :
    (Fin 3 → ↥(NormOne M)) →* ↥(StatedOmega (StatedQuadMinus 3 F b c)) :=
  ((M.τ).comp
    (⟨⟨fun a => (a 0, a 1, a 2), rfl⟩, fun _ _ => rfl⟩ :
      (Fin 3 → ↥(NormOne M)) →* ↥(NormOne M) × ↥(NormOne M) × ↥(NormOne M))).codRestrict _
    fun a => M.τ_mem _

private theorem torusO_coe (M : NormModel F b c) (a : Fin 3 → ↥(NormOne M)) :
    ((torusO M a : ↥(StatedOmega (StatedQuadMinus 3 F b c))) :
      GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) = M.τ (a 0, a 1, a 2) := rfl

theorem torusO_apply (M : NormModel F b c) (a : Fin 3 → ↥(NormOne M)) (x : OW F) :
    M.T ((((torusO M a : ↥(StatedOmega (StatedQuadMinus 3 F b c))) :
      GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
      Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x) =
      fun i => (((a i : ↥(NormOne M)) : M.Eˣ) : M.E) * M.T x i := by
  rw [torusO_coe, M.τ_apply]
  funext i
  fin_cases i <;> rfl

theorem torusO_injective (M : NormModel F b c) : Function.Injective (torusO M) := by
  intro a a' h
  have h1 : ((torusO M a : ↥(StatedOmega (StatedQuadMinus 3 F b c))) :
      GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) =
      ((torusO M a' : ↥(StatedOmega (StatedQuadMinus 3 F b c))) :
      GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :=
    congrArg Subtype.val h
  rw [torusO_coe, torusO_coe] at h1
  have h2 := M.τ_injective h1
  simp only [Prod.mk.injEq] at h2
  obtain ⟨h0, h1', h2'⟩ := h2
  funext i
  fin_cases i
  · exact h0
  · exact h1'
  · exact h2'

theorem normOne_pow (M : NormModel F b c) (a : Fin 3 → ↥(NormOne M)) :
    a ^ (Nat.card F + 1) = 1 := by
  funext i
  rw [Pi.pow_apply, Pi.one_apply]
  apply Subtype.ext
  exact (mem_rootsOfUnity _ _).mp (a i).2

@[expose] noncomputable def kerEval (M : NormModel F b c) (i : Fin 3) : Subgroup (Fin 3 → ↥(NormOne M)) :=
  (Pi.evalMonoidHom (fun _ : Fin 3 => ↥(NormOne M)) i).ker

theorem mem_kerEval (M : NormModel F b c) {i : Fin 3} {a : Fin 3 → ↥(NormOne M)} :
    a ∈ kerEval M i ↔ a i = 1 := Iff.rfl

theorem kerEval_sup (M : NormModel F b c) {i j : Fin 3} (hij : i ≠ j) :
    kerEval M i ⊔ kerEval M j = ⊤ := by
  rw [eq_top_iff]
  intro a _
  have hb' : (Pi.mulSingle i (a i) : Fin 3 → ↥(NormOne M)) ∈ kerEval M j := by
    rw [mem_kerEval, Pi.mulSingle_eq_of_ne hij.symm]
  have hb : a * (Pi.mulSingle i (a i) : Fin 3 → ↥(NormOne M))⁻¹ ∈ kerEval M i := by
    rw [mem_kerEval, Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same, mul_inv_cancel]
  have h := Subgroup.mul_mem_sup hb hb'
  rwa [inv_mul_cancel_right] at h

private theorem subRight_one_pow_apply (k : ℕ) (x : Fin 3) :
    ((Equiv.subRight (1 : Fin 3)) ^ k) x = x - k • (1 : Fin 3) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, Equiv.subRight_apply, ih, succ_nsmul]
    abel

private theorem sigma_mul_torusO (M : NormModel F b c) (a : Fin 3 → ↥(NormOne M)) :
    M.σ * ((torusO M a : ↥(StatedOmega (StatedQuadMinus 3 F b c))) :
      GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) =
      ((torusO M (fun k => a (k + 1)) : ↥(StatedOmega (StatedQuadMinus 3 F b c))) :
      GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) * M.σ := by
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  apply M.T.injective
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Units.val_mul, Units.val_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, M.σ_apply, torusO_apply, torusO_apply,
    M.σ_apply]

theorem exists_permO (M : NormModel F b c) :
    ∃ (P : ↥(StatedOmega (StatedQuadMinus 3 F b c))) (π : Equiv.Perm (Fin 3)),
      (∀ i j : Fin 3, ∃ k : ℕ, (π ^ k) i = j) ∧
      ∀ a : Fin 3 → ↥(NormOne M), ∃ a' : Fin 3 → ↥(NormOne M),
        (∀ i, a' (π i) = a i) ∧ P * torusO M a * P⁻¹ = torusO M a' := by
  refine ⟨⟨M.σ, M.σ_mem⟩, Equiv.subRight (1 : Fin 3), ?_, ?_⟩
  · have key : ∀ i j : Fin 3, i - (i - j).val • (1 : Fin 3) = j := by decide
    intro i j
    refine ⟨(i - j).val, ?_⟩
    rw [subRight_one_pow_apply]
    exact key i j
  · intro a
    refine ⟨fun k => a (k + 1), fun i => ?_, ?_⟩
    · simp
    · rw [mul_inv_eq_iff_eq_mul]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact sigma_mul_torusO M a

theorem exists_mem_torusO_head (M : NormModel F b c) {ω : M.E} (hω : ω ^ (Nat.card F + 1) = 1)
    (hω1 : ω ≠ 1) :
    ∃ a₀ : Fin 3 → ↥(NormOne M), a₀ ≠ 1 ∧ (((a₀ 0 : ↥(NormOne M)) : M.Eˣ) : M.E) = ω := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω
  have hu : Units.mk0 ω hω0 ∈ rootsOfUnity (Nat.card F + 1) M.E :=
    (mem_rootsOfUnity _ _).mpr (Units.ext (by simpa using hω))
  refine ⟨Pi.mulSingle 0 (⟨Units.mk0 ω hω0, hu⟩ : ↥(NormOne M)), ?_, ?_⟩
  · intro h
    have h0 := congrFun h 0
    rw [Pi.mulSingle_eq_same, Pi.one_apply] at h0
    apply hω1
    have h1 := congrArg (fun u : ↥(NormOne M) => ((u : M.Eˣ) : M.E)) h0
    simpa using h1
  · simp

end CFSG.LocalAnalysis.RankThreeUC
