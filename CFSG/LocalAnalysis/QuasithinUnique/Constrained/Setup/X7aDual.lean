module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aTensor
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aGram
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Iso

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open scoped MatrixGroups Matrix

open CFSG.QuasithinUnique.Setup.X7

section Dual

variable {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [CharP k 2]

@[expose] def locIso : (a b : Bool) → Matrix (Fin (locDim b a)) (Fin (locDim a b)) k
  | false, false => (1 : Matrix (Fin 1) (Fin 1) k)
  | true, false => (1 : Matrix (Fin 3) (Fin 3) k)
  | false, true => (1 : Matrix (Fin 3) (Fin 3) k)
  | true, true => gram k

theorem locIso_mul_locIso (a b : Bool) : locIso k a b * locIso k b a = 1 := by
  cases a <;> cases b
  · exact Matrix.one_mul (1 : Matrix (Fin 1) (Fin 1) k)
  · exact Matrix.one_mul (1 : Matrix (Fin 3) (Fin 3) k)
  · exact Matrix.one_mul (1 : Matrix (Fin 3) (Fin 3) k)
  · exact gram_mul_self k

omit [CharP k 2] in
theorem dual_iso_ff_aux : (1 : Matrix (Fin 1) (Fin 1) k) * (1 : Matrix (Fin 1) (Fin 1) k)ᵀ =
    (1 : Matrix (Fin 1) (Fin 1) k) * 1 := by
  simp

theorem dual_iso_ft_aux (i : ℕ) (g : SL(3, F)) :
    (1 : Matrix (Fin 3) (Fin 3) k) * (dualRep k i g⁻¹)ᵀ = natRep k i g * 1 := by
  rw [Matrix.one_mul, Matrix.mul_one, dualRep_apply, inv_inv, Matrix.transpose_transpose]
  rfl

theorem dual_iso_tf_aux (i : ℕ) (g : SL(3, F)) :
    (1 : Matrix (Fin 3) (Fin 3) k) * (natRep k i g⁻¹)ᵀ = dualRep k i g * 1 := by
  rw [Matrix.one_mul, Matrix.mul_one]
  rfl

theorem locRep_dual_iso (a b : Bool) (i : ℕ) (g : SL(3, F)) :
    locIso k a b * (locRep k a b i g⁻¹)ᵀ = locRep k b a i g * locIso k a b := by
  cases a <;> cases b
  · exact dual_iso_ff_aux k
  · exact dual_iso_ft_aux k i g
  · exact dual_iso_tf_aux k i g
  · exact gram_adjRep_dual k i g

variable {f : ℕ}

theorem tensorRep_dual_iso (a b : Fin f → Bool) :
    MatIso (dualMat (tensorRep (F := F) k a b)) (tensorRep k b a)
      (kron (fun i => locIso k (a i) (b i))) (kron (fun i => locIso k (b i) (a i))) := by
  refine ⟨?_, ?_, fun g => ?_⟩
  · rw [← kron_mul]
    simp_rw [locIso_mul_locIso]
    exact kron_one
  · rw [← kron_mul]
    simp_rw [locIso_mul_locIso]
    exact kron_one
  · rw [dualMat_apply]
    change kron (fun i => locIso k (a i) (b i)) *
      (kron (fun i => locRep k (a i) (b i) (i : ℕ) g⁻¹))ᵀ =
        kron (fun i => locRep k (b i) (a i) (i : ℕ) g) * kron (fun i => locIso k (a i) (b i))
    rw [kron_transpose, ← kron_mul, ← kron_mul]
    congr 1
    funext i
    exact locRep_dual_iso k (a i) (b i) (i : ℕ) g

end Dual

section Frobenius

variable {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [CharP k 2]

@[expose] def frobSL (F : Type*) [Field F] [CharP F 2] : SL(3, F) →* SL(3, F) :=
  Matrix.SpecialLinearGroup.map (iterateFrobenius F 2 1)

theorem twistMat_frobSL [CharP F 2] (i : ℕ) (g : SL(3, F)) :
    twistMat k i (frobSL F g) = twistMat k (i + 1) g := by
  ext a b
  simp only [twistMat_apply, frK_apply, frobSL, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply, iterateFrobenius_def, map_pow, ← pow_mul,
    pow_succ]
  congr 1

theorem natRep_frobSL [CharP F 2] (i : ℕ) (g : SL(3, F)) :
    natRep k i (frobSL F g) = natRep k (i + 1) g :=
  twistMat_frobSL k i g

theorem dualRep_frobSL [CharP F 2] (i : ℕ) (g : SL(3, F)) :
    dualRep k i (frobSL F g) = dualRep k (i + 1) g := by
  rw [dualRep_apply, dualRep_apply, ← map_inv, twistMat_frobSL]

theorem adjRep_frobSL [CharP F 2] (i : ℕ) (g : SL(3, F)) :
    adjRep k i (frobSL F g) = adjRep k (i + 1) g := by
  ext r s
  rw [adjRep_apply, adjRep_apply, conjMat, conjMat, ← map_inv, twistMat_frobSL, twistMat_frobSL]

theorem locRep_frobSL [CharP F 2] (a b : Bool) (i : ℕ) (g : SL(3, F)) :
    locRep k a b i (frobSL F g) = locRep k a b (i + 1) g := by
  cases a <;> cases b
  · rfl
  · exact dualRep_frobSL k i g
  · exact natRep_frobSL k i g
  · exact adjRep_frobSL k i g

section Periodic

variable [Fintype F] {f : ℕ}

theorem frK_add_card (hF : Fintype.card F = 2 ^ f) (i : ℕ) (x : F) :
    frK k (i + f) x = frK k i x := by
  rw [frK_apply, frK_apply, pow_add, mul_comm, pow_mul, ← map_pow, ← hF, FiniteField.pow_card]

theorem twistMat_add_mul_card (hF : Fintype.card F = 2 ^ f) (j n : ℕ) (g : SL(3, F)) :
    twistMat k (j + f * n) g = twistMat k j g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc]
    ext a b
    simp only [twistMat_apply]
    rw [frK_add_card k hF]
    exact congrFun (congrFun ih a) b

theorem twistMat_mod (hF : Fintype.card F = 2 ^ f) (i : ℕ) (g : SL(3, F)) :
    twistMat k i g = twistMat k (i % f) g := by
  conv_lhs => rw [← Nat.mod_add_div i f]
  exact twistMat_add_mul_card k hF _ _ g

theorem locRep_mod (hF : Fintype.card F = 2 ^ f) (a b : Bool) (i : ℕ) (g : SL(3, F)) :
    locRep k a b i g = locRep k a b (i % f) g := by
  cases a <;> cases b
  · rfl
  · show dualRep k i g = dualRep k (i % f) g
    rw [dualRep_apply, dualRep_apply, twistMat_mod k hF i, twistMat_mod k hF (i % f)]
  · exact twistMat_mod k hF i g
  · show adjRep k i g = adjRep k (i % f) g
    ext r s
    rw [adjRep_apply, adjRep_apply, conjMat, conjMat, twistMat_mod k hF i g,
      twistMat_mod k hF i g⁻¹, twistMat_mod k hF (i % f) g, twistMat_mod k hF (i % f) g⁻¹]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem tensorRepGen_congr_mod (hF : Fintype.card F = 2 ^ f) (τ : ι → Bool × Bool) {e e' : ι → ℕ}
    (h : ∀ i, e i % f = e' i % f) : tensorRepGen (F := F) k τ e = tensorRepGen k τ e' := by
  ext g : 1
  show kron _ = kron _
  congr 1
  funext i
  rw [locRep_mod k hF _ _ (e i) g, locRep_mod k hF _ _ (e' i) g, h i]

omit [Fintype F] in
theorem tensorRepGen_reindex {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (σ : ι ≃ ι')
    (τ : ι → Bool × Bool) (e : ι → ℕ) :
    MatIso (tensorRepGen (F := F) k τ e) (tensorRepGen k (τ ∘ σ.symm) (e ∘ σ.symm))
      (permMat k (Equiv.piCongrLeft' (fun i => Fin (locDim (τ i).1 (τ i).2)) σ))
      (permMat k (Equiv.piCongrLeft' (fun i => Fin (locDim (τ i).1 (τ i).2)) σ).symm) := by
  refine matIso_of_reindex _ (fun g x' x => ?_)
  show kron _ (Equiv.piCongrLeft' _ σ x') (Equiv.piCongrLeft' _ σ x) = kron _ x' x
  simp only [kron_apply, Equiv.piCongrLeft'_apply]
  exact Equiv.prod_comp σ.symm (fun i => locRep k (τ i).1 (τ i).2 (e i) g (x' i) (x i))

@[expose] def shiftBits (f : ℕ) (a : Fin f → Bool) : Fin f → Bool :=
  fun j => a ((finRotate f).symm j)

omit [Field F] [Fintype F] [CharP k 2] in
theorem rotate_exp (f : ℕ) (j : Fin f) : (((finRotate f).symm j : Fin f) : ℕ) + 1 ≡ (j : ℕ) [MOD f] := by
  obtain ⟨i, rfl⟩ : ∃ i, j = finRotate f i :=
    ⟨(finRotate f).symm j, (Equiv.apply_symm_apply _ _).symm⟩
  rw [Equiv.symm_apply_apply]
  cases f with
  | zero => exact i.elim0
  | succ n =>
    rw [coe_finRotate]
    split_ifs with h
    · subst h
      simp [Nat.ModEq]
    · rfl

theorem tensorRep_comp_frob [CharP F 2] (hF : Fintype.card F = 2 ^ f) (a b : Fin f → Bool) :
    ∃ (P : Matrix (TIdx f (shiftBits f a) (shiftBits f b)) (TIdx f a b) k)
      (Q : Matrix (TIdx f a b) (TIdx f (shiftBits f a) (shiftBits f b)) k),
      MatIso ((tensorRep (F := F) k a b).comp (frobSL F))
        (tensorRep k (shiftBits f a) (shiftBits f b)) P Q := by
  have h1 : (tensorRep (F := F) k a b).comp (frobSL F) =
      tensorRepGen k (fun i : Fin f => (a i, b i)) (fun i => (i : ℕ) + 1) := by
    ext g : 1
    show kron _ = kron _
    congr 1
    funext i
    exact locRep_frobSL k _ _ (i : ℕ) g
  have h2 : tensorRepGen (F := F) k ((fun i : Fin f => (a i, b i)) ∘ (finRotate f).symm)
      ((fun i : Fin f => (i : ℕ) + 1) ∘ (finRotate f).symm) =
      tensorRep k (shiftBits f a) (shiftBits f b) :=
    tensorRepGen_congr_mod k hF _ (fun j => rotate_exp f j)
  have h3 := tensorRepGen_reindex (F := F) k (finRotate f) (fun i : Fin f => (a i, b i))
    (fun i => (i : ℕ) + 1)
  rw [h2] at h3
  rw [h1]
  exact ⟨_, _, h3⟩
end Periodic

end Frobenius

section Graph

variable {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [CharP k 2]

@[expose] def trInvMat (g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F :=
  ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ

theorem trInvMat_mul (g h : SL(3, F)) : trInvMat (g * h) = trInvMat g * trInvMat h := by
  unfold trInvMat
  rw [mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]

theorem trInvMat_one : trInvMat (1 : SL(3, F)) = 1 := by
  unfold trInvMat
  rw [inv_one, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]

theorem det_trInvMat (g : SL(3, F)) : (trInvMat g).det = 1 := by
  rw [trInvMat, Matrix.det_transpose]
  exact (g⁻¹).2

@[expose] def tauFun (g : SL(3, F)) : SL(3, F) := ⟨trInvMat g, det_trInvMat g⟩

theorem tauFun_coe (g : SL(3, F)) :
    ((tauFun g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = trInvMat g := rfl

theorem tauFun_mul (g h : SL(3, F)) : tauFun (g * h) = tauFun g * tauFun h :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, tauFun_coe, tauFun_coe, tauFun_coe]
    exact trInvMat_mul g h)

theorem tauFun_one : tauFun (1 : SL(3, F)) = 1 :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_one, tauFun_coe]
    exact trInvMat_one)

@[expose] def tauSL (F : Type*) [Field F] : SL(3, F) →* SL(3, F) where
  toFun := tauFun
  map_one' := tauFun_one
  map_mul' := tauFun_mul

theorem tauSL_coe (g : SL(3, F)) :
    ((tauSL F g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = trInvMat g := rfl

theorem tauSL_tauSL (g : SL(3, F)) : tauSL F (tauSL F g) = g :=
  Subtype.ext (by
    rw [tauSL_coe, trInvMat, ← map_inv, tauSL_coe, trInvMat, inv_inv, Matrix.transpose_transpose])

theorem twistMat_tauSL (i : ℕ) (g : SL(3, F)) :
    twistMat k i (tauSL F g) = (twistMat k i g⁻¹)ᵀ := by
  ext a b
  simp only [twistMat_apply, tauSL_coe, trInvMat, Matrix.transpose_apply]

theorem natRep_tauSL (i : ℕ) (g : SL(3, F)) : natRep k i (tauSL F g) = dualRep k i g :=
  twistMat_tauSL k i g

theorem dualRep_tauSL (i : ℕ) (g : SL(3, F)) : dualRep k i (tauSL F g) = natRep k i g := by
  rw [dualRep_apply, ← map_inv, twistMat_tauSL, inv_inv, Matrix.transpose_transpose]
  rfl

@[expose] def permT : Matrix (Fin 8) (Fin 8) k :=
  Matrix.of fun r s => co ((Xm (Pi.single s 1) : Matrix (Fin 3) (Fin 3) k)ᵀ) r

omit [CharP k 2] in
theorem permT_mulVec (c : Fin 8 → k) :
    (permT k).mulVec c = co ((Xm c : Matrix (Fin 3) (Fin 3) k)ᵀ) := by
  have h1 : (Xm c : Matrix (Fin 3) (Fin 3) k)ᵀ =
      ∑ s, c s • (Xm (Pi.single s (1 : k)) : Matrix (Fin 3) (Fin 3) k)ᵀ := by
    rw [Xm_eq_sum k c, Matrix.transpose_sum]
    simp [Matrix.transpose_smul]
  have h2 : co ((Xm c : Matrix (Fin 3) (Fin 3) k)ᵀ) =
      ∑ s, c s • co ((Xm (Pi.single s (1 : k)) : Matrix (Fin 3) (Fin 3) k)ᵀ) := by
    rw [h1]
    calc co (∑ s, c s • (Xm (Pi.single s (1 : k)) : Matrix (Fin 3) (Fin 3) k)ᵀ)
        = coL k (∑ s, c s • (Xm (Pi.single s (1 : k)) : Matrix (Fin 3) (Fin 3) k)ᵀ) := rfl
      _ = ∑ s, c s • co ((Xm (Pi.single s (1 : k)) : Matrix (Fin 3) (Fin 3) k)ᵀ) := by
        rw [map_sum]
        simp only [map_smul, coL_apply]
  rw [h2]
  funext r
  simp [Matrix.mulVec, dotProduct, permT, Finset.sum_apply, mul_comm]

theorem permT_mul_self : permT k * permT k = 1 := by
  have h : ∀ c, (permT k * permT k).mulVec c = c := by
    intro c
    rw [← Matrix.mulVec_mulVec, permT_mulVec, permT_mulVec,
      Xm_co k (by rw [Matrix.trace_transpose]; exact trace_Xm k c), Matrix.transpose_transpose,
      co_Xm]
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun c => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h, Matrix.one_mulVec]

theorem adjRep_mulVec (i : ℕ) (g : SL(3, F)) (c : Fin 8 → k) :
    (adjRep k i g).mulVec c = co (conjMat k i g (Xm c)) := by
  have : (adjRep k i g).mulVec c = adjEnd k i g c :=
    LinearMap.toMatrix'_mulVec (adjEnd k i g) c
  rw [this, adjEnd_apply]

theorem conjMat_tauSL_transpose (i : ℕ) (g : SL(3, F)) (Y : Matrix (Fin 3) (Fin 3) k) :
    conjMat k i (tauSL F g) Yᵀ = (conjMat k i g Y)ᵀ := by
  rw [conjMat, conjMat, twistMat_tauSL, ← map_inv, twistMat_tauSL, inv_inv]
  simp only [Matrix.transpose_mul, mul_assoc]

theorem permT_adjRep (i : ℕ) (g : SL(3, F)) :
    permT k * adjRep k i g = adjRep k i (tauSL F g) * permT k := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun c => ?_
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
  rw [adjRep_mulVec, permT_mulVec, permT_mulVec, adjRep_mulVec,
    Xm_co k (by rw [trace_conjMat, trace_Xm]),
    Xm_co k (by rw [Matrix.trace_transpose]; exact trace_Xm k c), conjMat_tauSL_transpose]

@[expose] def locIsoTau : (a b : Bool) → Matrix (Fin (locDim b a)) (Fin (locDim a b)) k
  | false, false => (1 : Matrix (Fin 1) (Fin 1) k)
  | true, false => (1 : Matrix (Fin 3) (Fin 3) k)
  | false, true => (1 : Matrix (Fin 3) (Fin 3) k)
  | true, true => permT k

theorem locIsoTau_mul (a b : Bool) : locIsoTau k a b * locIsoTau k b a = 1 := by
  cases a <;> cases b
  · exact Matrix.one_mul (1 : Matrix (Fin 1) (Fin 1) k)
  · exact Matrix.one_mul (1 : Matrix (Fin 3) (Fin 3) k)
  · exact Matrix.one_mul (1 : Matrix (Fin 3) (Fin 3) k)
  · exact permT_mul_self k

omit [CharP k 2] in
theorem tau_iso_ff_aux : (1 : Matrix (Fin 1) (Fin 1) k) * 1 = 1 * 1 := rfl

theorem tau_iso_ft_aux (i : ℕ) (g : SL(3, F)) :
    (1 : Matrix (Fin 3) (Fin 3) k) * dualRep k i (tauSL F g) = natRep k i g * 1 := by
  rw [Matrix.one_mul, Matrix.mul_one, dualRep_tauSL]

theorem tau_iso_tf_aux (i : ℕ) (g : SL(3, F)) :
    (1 : Matrix (Fin 3) (Fin 3) k) * natRep k i (tauSL F g) = dualRep k i g * 1 := by
  rw [Matrix.one_mul, Matrix.mul_one, natRep_tauSL]

theorem locRep_tau (a b : Bool) (i : ℕ) (g : SL(3, F)) :
    locIsoTau k a b * locRep k a b i (tauSL F g) = locRep k b a i g * locIsoTau k a b := by
  cases a <;> cases b
  · exact tau_iso_ff_aux k
  · exact tau_iso_ft_aux k i g
  · exact tau_iso_tf_aux k i g
  · have := permT_adjRep k i (tauSL F g)
    rw [tauSL_tauSL] at this
    exact this

variable {f : ℕ}

theorem tensorRep_comp_tau (a b : Fin f → Bool) :
    MatIso ((tensorRep (F := F) k a b).comp (tauSL F)) (tensorRep k b a)
      (kron (fun i => locIsoTau k (a i) (b i))) (kron (fun i => locIsoTau k (b i) (a i))) := by
  refine ⟨?_, ?_, fun g => ?_⟩
  · rw [← kron_mul]
    simp_rw [locIsoTau_mul]
    exact kron_one
  · rw [← kron_mul]
    simp_rw [locIsoTau_mul]
    exact kron_one
  · change kron (fun i => locIsoTau k (a i) (b i)) *
      kron (fun i => locRep k (a i) (b i) (i : ℕ) (tauSL F g)) =
        kron (fun i => locRep k (b i) (a i) (i : ℕ) g) * kron (fun i => locIsoTau k (a i) (b i))
    rw [← kron_mul, ← kron_mul]
    congr 1
    funext i
    exact locRep_tau k (a i) (b i) (i : ℕ) g

end Graph

end CFSG.QuasithinUnique.Setup.X7a
