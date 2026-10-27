module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aIrred

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open scoped MatrixGroups Matrix

open CFSG.QuasithinUnique.Setup.X7

section Coordinates

variable {F : Type*} [Field F] [CharP F 2] [Fintype F] (k : Type*) [Field k] [Algebra F k]
  [CharP k 2] {f : ℕ}

theorem triangular_highest_vector_coordinates (hF : Fintype.card F = 2 ^ f) :
    Function.Bijective (lowerUniEquiv F) ∧
      Nat.card (lowerUni F) = Nat.card F ^ 3 ∧ Nat.card (upperUni F) = Nat.card F ^ 3 ∧
      IsPGroup 2 (lowerUni F) ∧ IsPGroup 2 (upperUni F) ∧
      ((wJ : SL(3, F)) * wJ = 1 ∧
        Subgroup.map (MulAut.conj (wJ : SL(3, F))).toMonoidHom (lowerUni F) = upperUni F) ∧
      (∀ (i : ℕ) (x y z : F) (j : Fin 3),
        natRep k i (u3 x y z) j 0 = frK k i (![1, x, y] j)) ∧
      (∀ (i : ℕ) (x y z : F) (j : Fin 3),
        dualRep k i (u3 x y z) j 2 = frK k i (![y + x * z, z, 1] j)) ∧
      (∀ (i : ℕ) (x y z : F) (j : Fin 8),
        adjRep k i (u3 x y z) j 0 = frK k i
          (![1, x, y, z, y + x * z, x * y + x ^ 2 * z, y * z, y ^ 2 + x * y * z] j)) ∧
      (∀ a b : Fin f → Bool, ∀ g ∈ upperUni F,
        (tensorRep (F := F) k a b g).mulVec (hw k a b) = hw k a b) ∧
      (∀ (i : ℕ) (r t : Fˣ) (j : Fin 3),
        natRep k i (dT r t) j 0 = if j = 0 then frK k i (r : F) else 0) ∧
      (∀ (i : ℕ) (r t : Fˣ) (j : Fin 3),
        dualRep k i (dT r t) j 2 = if j = 2 then frK k i ((r * t : Fˣ) : F) else 0) ∧
      (∀ (i : ℕ) (r t : Fˣ) (j : Fin 8),
        adjRep k i (dT r t) j 0 =
          if j = 0 then frK k i ((r : F) * ((r * t : Fˣ) : F)) else 0) := by
  have hcard : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  refine ⟨(lowerUniEquiv F).bijective, card_lowerUni, card_upperUni, isPGroup_lowerUni hcard,
    isPGroup_upperUni hcard, ⟨wJ_mul_self, ?_⟩, fun i x y z j => natRep_u3_col k i x y z j,
    fun i x y z j => dualRep_u3_col k i x y z j, fun i x y z j => adjRep_u3_col' k i x y z j,
    ?_, fun i r t j => natRep_dT_col k i r t j, fun i r t j => dualRep_dT_col k i r t j,
    fun i r t j => adjRep_dT_col k i r t j⟩
  · ext g
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact wJ_conj_lowerUni hu
    · intro hg
      obtain ⟨x, y, z, rfl⟩ := mem_upperUni.mp hg
      refine ⟨u3 x y z, mem_lowerUni.mpr ⟨x, y, z, rfl⟩, ?_⟩
      show (wJ : SL(3, F)) * u3 x y z * (wJ : SL(3, F))⁻¹ = up3 x y z
      rw [wJ_inv, wJ_u3_wJ]
  · intro a b g hg
    obtain ⟨x, y, z, rfl⟩ := mem_upperUni.mp hg
    exact tensorRep_up3_fixed k a b x y z

end Coordinates

section Duality

variable {F : Type*} [Field F] [CharP F 2] [Fintype F] (k : Type*) [Field k] [Algebra F k]
  [CharP k 2] {f : ℕ}

@[expose] def frobPow (F : Type*) [Field F] [CharP F 2] : ℕ → (SL(3, F) →* SL(3, F))
  | 0 => MonoidHom.id _
  | r + 1 => (frobSL F).comp (frobPow F r)

omit [Fintype F] in
theorem frobSL_coe (h : SL(3, F)) :
    ((frobSL F h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (h : Matrix (Fin 3) (Fin 3) F).map (fun x => x ^ 2) := by
  ext i j
  simp [frobSL, Matrix.SpecialLinearGroup.map_apply_coe, frobenius_def]

omit [Fintype F] in
theorem frobSL_tauSL (g : SL(3, F)) : frobSL F (tauSL F g) = tauSL F (frobSL F g) := by
  apply Subtype.ext
  rw [frobSL_coe, tauSL_coe, tauSL_coe, trInvMat, trInvMat, ← map_inv, frobSL_coe,
    Matrix.transpose_map]

omit [Fintype F] in
theorem frobSL_iterate_coe (n : ℕ) (g : SL(3, F)) :
    (((frobSL F)^[n] g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) F).map (fun x => x ^ 2 ^ n) := by
  induction n generalizing g with
  | zero => ext i j; simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', frobSL_coe, ih]
    ext i j
    simp only [Matrix.map_apply]
    rw [← pow_mul, pow_succ]

theorem frobSL_iterate_card (hF : Fintype.card F = 2 ^ f) (g : SL(3, F)) :
    (frobSL F)^[f] g = g := by
  apply Subtype.ext
  rw [frobSL_iterate_coe]
  ext i j
  simp only [Matrix.map_apply]
  rw [← hF, FiniteField.pow_card]

theorem tensorRep_comp_frobPow (hF : Fintype.card F = 2 ^ f) (r : ℕ) :
    ∀ a b : Fin f → Bool,
      ∃ (P : Matrix (TIdx f ((shiftBits f)^[r] a) ((shiftBits f)^[r] b)) (TIdx f a b) k)
        (Q : Matrix (TIdx f a b) (TIdx f ((shiftBits f)^[r] a) ((shiftBits f)^[r] b)) k),
        MatIso ((tensorRep (F := F) k a b).comp (frobPow F r))
          (tensorRep k ((shiftBits f)^[r] a) ((shiftBits f)^[r] b)) P Q := by
  induction r with
  | zero =>
    intro a b
    exact ⟨_, _, MatIso.refl (tensorRep (F := F) k a b)⟩
  | succ r ih =>
    intro a b
    obtain ⟨P₁, Q₁, h₁⟩ := tensorRep_comp_frob k hF a b
    obtain ⟨P₂, Q₂, h₂⟩ := ih (shiftBits f a) (shiftBits f b)
    have h3 := (h₁.comp (frobPow F r)).trans h₂
    exact ⟨_, _, by
      rw [frobPow, ← MonoidHom.comp_assoc]
      exact h3⟩

theorem duality_and_automorphism_transport (hF : Fintype.card F = 2 ^ f) :
    (∀ g : SL(3, F), frobSL F (tauSL F g) = tauSL F (frobSL F g)) ∧
      (∀ g : SL(3, F), (frobSL F)^[f] g = g) ∧ (∀ g : SL(3, F), tauSL F (tauSL F g) = g) ∧
      (∀ a b : Fin f → Bool, ∃ (P : Matrix (TIdx f b a) (TIdx f a b) k)
        (Q : Matrix (TIdx f a b) (TIdx f b a) k),
          MatIso (dualMat (tensorRep (F := F) k a b)) (tensorRep k b a) P Q) ∧
      (∀ a b : Fin f → Bool, ∃ (P : Matrix (TIdx f (shiftBits f a) (shiftBits f b)) (TIdx f a b) k)
        (Q : Matrix (TIdx f a b) (TIdx f (shiftBits f a) (shiftBits f b)) k),
          MatIso ((tensorRep (F := F) k a b).comp (frobSL F))
            (tensorRep k (shiftBits f a) (shiftBits f b)) P Q) ∧
      (∀ a b : Fin f → Bool, ∃ (P : Matrix (TIdx f b a) (TIdx f a b) k)
        (Q : Matrix (TIdx f a b) (TIdx f b a) k),
          MatIso ((tensorRep (F := F) k a b).comp (tauSL F)) (tensorRep k b a) P Q) ∧
      (∀ (r : ℕ) (a b : Fin f → Bool),
        ∃ (P : Matrix (TIdx f ((shiftBits f)^[r] a) ((shiftBits f)^[r] b)) (TIdx f a b) k)
          (Q : Matrix (TIdx f a b) (TIdx f ((shiftBits f)^[r] a) ((shiftBits f)^[r] b)) k),
          MatIso ((tensorRep (F := F) k a b).comp (frobPow F r))
            (tensorRep k ((shiftBits f)^[r] a) ((shiftBits f)^[r] b)) P Q) ∧
      (∀ (r : ℕ) (a b : Fin f → Bool),
        ∃ (P : Matrix (TIdx f ((shiftBits f)^[r] b) ((shiftBits f)^[r] a)) (TIdx f a b) k)
          (Q : Matrix (TIdx f a b) (TIdx f ((shiftBits f)^[r] b) ((shiftBits f)^[r] a)) k),
          MatIso (((tensorRep (F := F) k a b).comp (tauSL F)).comp (frobPow F r))
            (tensorRep k ((shiftBits f)^[r] b) ((shiftBits f)^[r] a)) P Q) ∧
      (∀ (i : ℕ) (g : SL(3, F)),
        gram k * (adjRep k i g⁻¹)ᵀ = adjRep k i g * gram k) := by
  refine ⟨frobSL_tauSL, frobSL_iterate_card hF, tauSL_tauSL,
    fun a b => ⟨_, _, tensorRep_dual_iso k a b⟩, fun a b => tensorRep_comp_frob k hF a b,
    fun a b => ⟨_, _, tensorRep_comp_tau k a b⟩, fun r a b => tensorRep_comp_frobPow k hF r a b,
    fun r a b => ?_, fun i g => gram_adjRep_dual k i g⟩
  obtain ⟨P₁, Q₁, h₁⟩ := (⟨_, _, tensorRep_comp_tau k a b⟩ :
    ∃ (P : Matrix (TIdx f b a) (TIdx f a b) k) (Q : Matrix (TIdx f a b) (TIdx f b a) k),
      MatIso ((tensorRep (F := F) k a b).comp (tauSL F)) (tensorRep k b a) P Q)
  obtain ⟨P₂, Q₂, h₂⟩ := tensorRep_comp_frobPow k hF r b a
  exact ⟨_, _, (h₁.comp (frobPow F r)).trans h₂⟩

end Duality

section Orbits

variable {F : Type*} [Field F] [CharP F 2] [Fintype F] (k : Type*) [Field k] [Algebra F k]
  [CharP k 2] {f : ℕ}

theorem full_trace_zero_tensor (hF : Fintype.card F = 2 ^ f) :
    Module.finrank k (TIdx f (ones f) (ones f) → k) = Nat.card F ^ 3 ∧
      ∑ g : lowerUni F, ((tensorRep (F := F) k (ones f) (ones f) (g : SL(3, F))).mulVec
        (hw k (ones f) (ones f))) (w7 f) = 1 ∧
      (∃ b : Module.Basis (lowerUni F) k (TIdx f (ones f) (ones f) → k), ∀ u : lowerUni F,
        b u = (tensorRep (F := F) k (ones f) (ones f) (u : SL(3, F))).mulVec
          (hw k (ones f) (ones f))) ∧
      (∃ b : Module.Basis (TIdx f (ones f) (ones f)) k (lowerUni F → k),
        ∀ (x : TIdx f (ones f) (ones f)) (u : lowerUni F),
          b x u = ((tensorRep (F := F) k (ones f) (ones f) (u : SL(3, F))).mulVec
            (hw k (ones f) (ones f))) x) ∧
      fixedSub (matRep (tensorRep (F := F) k (ones f) (ones f))) (upperUni F) =
        Submodule.span k {hw k (ones f) (ones f)} ∧
      (matRep (tensorRep (F := F) k (ones f) (ones f))).IsIrreducible := by
  have hq : Fintype.card (TIdx f (ones f) (ones f)) = Fintype.card F ^ 3 := by
    rw [card_TIdx_ones, hF, ← pow_mul, mul_comm, pow_mul]
    norm_num
  refine ⟨?_, norm_coeff_full k hF, fullOrbit_basis k hF, ?_,
    (tensorRep_fixed_irreducible k hF (ones f) (ones f)).1,
    (tensorRep_fixed_irreducible k hF (ones f) (ones f)).2⟩
  · rw [Module.finrank_fintype_fun_eq_card, hq, Nat.card_eq_fintype_card]
  · have : Nonempty (TIdx f (ones f) (ones f)) := ⟨w7 f⟩
    refine ⟨basisOfLinearIndependentOfCardEqFinrank (fullCoords_li k hF) ?_, fun x u => ?_⟩
    · rw [Module.finrank_fintype_fun_eq_card, card_lowerUni_eq, hq]
    · rw [coe_basisOfLinearIndependentOfCardEqFinrank]

theorem fundamental_tensor_orbits_and_fixed_characters (hF : Fintype.card F = 2 ^ f)
    (a b : Fin f → Bool) :
    Submodule.span k (Set.range fun u : lowerUni F =>
        matRep (tensorRep (F := F) k a b) (u : SL(3, F)) (hw k a b)) = ⊤ ∧
      fixedSub (matRep (tensorRep (F := F) k a b)) (upperUni F) = Submodule.span k {hw k a b} ∧
      (matRep (tensorRep (F := F) k a b)).IsIrreducible ∧
      Module.finrank k (TIdx f a b → k) = 3 ^ cntS a b * 8 ^ cntH a b ∧
      ∀ r t : Fˣ, (tensorRep (F := F) k a b (dT r t)).mulVec (hw k a b) =
        (algebraMap F k (r : F) ^ (mBits a + mBits b) * algebraMap F k (t : F) ^ mBits b) •
          hw k a b := by
  refine ⟨mixed_span k hF a b, (tensorRep_fixed_irreducible k hF a b).1,
    (tensorRep_fixed_irreducible k hF a b).2, ?_, fun r t => tensorRep_dT_hw k a b r t⟩
  rw [Module.finrank_fintype_fun_eq_card]
  exact card_TIdx_eq a b

end Orbits

end CFSG.QuasithinUnique.Setup.X7a
