module

public import CFSG.LieType.Chevalley.E6GraphInvolutionLinear

public noncomputable section

namespace CFSG.LieType.Chevalley.E6GraphInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LieType.Chevalley.E6GraphLevi
open Matrix

section Descent

variable {K : Type} [Field K]

@[expose] def semiT (σ : K →+* K) (B : Matrix (Fin 6) (Fin 6) K) (v : Fin 6 → K) : Fin 6 → K :=
  B *ᵥ fun i => σ (v i)

@[expose] def hermJ (σ : K →+* K) (v w : Fin 6 → K) : K :=
  (fun i => σ (v i)) ⬝ᵥ (antiId K *ᵥ w)

variable {σ : K →+* K}

theorem map_mulVec_fun (M : Matrix (Fin 6) (Fin 6) K) (v : Fin 6 → K) :
    (fun i => σ ((M *ᵥ v) i)) = M.map σ *ᵥ fun i => σ (v i) :=
  funext fun i => RingHom.map_mulVec σ M v i

theorem semiT_add (B : Matrix (Fin 6) (Fin 6) K) (v w : Fin 6 → K) :
    semiT σ B (v + w) = semiT σ B v + semiT σ B w := by
  rw [semiT, semiT, semiT, ← mulVec_add]
  congr 1
  funext i
  simp

theorem semiT_smul (B : Matrix (Fin 6) (Fin 6) K) (c : K) (v : Fin 6 → K) :
    semiT σ B (c • v) = σ c • semiT σ B v := by
  rw [semiT, semiT, ← mulVec_smul]
  congr 1
  funext i
  simp

theorem semiT_semiT (hσσ : ∀ c, σ (σ c) = c) {B : Matrix (Fin 6) (Fin 6) K}
    (hBB : B * B.map σ = 1) (v : Fin 6 → K) : semiT σ B (semiT σ B v) = v := by
  rw [semiT, semiT, map_mulVec_fun, mulVec_mulVec, hBB, one_mulVec]
  funext i
  exact hσσ _

theorem span_fixed_eq_top (h2 : (2 : K) = 0) (hσσ : ∀ c, σ (σ c) = c)
    {B : Matrix (Fin 6) (Fin 6) K} (hBB : B * B.map σ = 1) {e : K} (he : e + σ e = 1) :
    Submodule.span K {v : Fin 6 → K | semiT σ B v = v} = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  have h1 : v + semiT σ B v ∈ {v : Fin 6 → K | semiT σ B v = v} := by
    show semiT σ B (v + semiT σ B v) = v + semiT σ B v
    rw [semiT_add, semiT_semiT hσσ hBB, add_comm]
  have h1' : σ e • v + e • semiT σ B v ∈ {v : Fin 6 → K | semiT σ B v = v} := by
    show semiT σ B (σ e • v + e • semiT σ B v) = σ e • v + e • semiT σ B v
    rw [semiT_add, semiT_smul, semiT_smul, semiT_semiT hσσ hBB, hσσ, add_comm]
  have hv : v = e • (v + semiT σ B v) + (σ e • v + e • semiT σ B v) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-v i) * he - semiT σ B v i * e * h2
  rw [hv]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span h1))
    (Submodule.subset_span h1')

theorem exists_fixed_matrix (h2 : (2 : K) = 0) (hσσ : ∀ c, σ (σ c) = c)
    {B : Matrix (Fin 6) (Fin 6) K} (hBB : B * B.map σ = 1) (he : ∃ e, e + σ e = 1) :
    ∃ H : GL (Fin 6) K, B * (H : Matrix (Fin 6) (Fin 6) K).map σ = H := by
  obtain ⟨e, he⟩ := he
  obtain ⟨s, hsW, hspan, hli⟩ := exists_linearIndependent K {v : Fin 6 → K | semiT σ B v = v}
  have htop : ⊤ ≤ Submodule.span K (Set.range ((↑) : s → Fin 6 → K)) := by
    rw [Subtype.range_coe, hspan, span_fixed_eq_top h2 hσσ hBB he]
  set b := Module.Basis.mk hli htop
  set b' := b.reindex (b.indexEquiv (Pi.basisFun K (Fin 6)))
  have hfix : ∀ j, semiT σ B (b' j) = b' j := fun j => by
    rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
    exact hsW (Subtype.mem _)
  refine ⟨⟨(Pi.basisFun K (Fin 6)).toMatrix b', b'.toMatrix (Pi.basisFun K (Fin 6)),
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩,
    ?_⟩
  ext i j
  have := congrFun (hfix j) i
  simp only [semiT, Matrix.mulVec, dotProduct] at this
  simp only [Matrix.mul_apply, Matrix.map_apply, Module.Basis.toMatrix_apply,
    Pi.basisFun_repr]
  exact this

theorem map_map_eq_self (hσσ : ∀ c, σ (σ c) = c) (M : Matrix (Fin 6) (Fin 6) K) :
    (M.map σ).map σ = M := by
  ext i j
  exact hσσ _

theorem gram_map_eq_and_transpose (hσσ : ∀ c, σ (σ c) = c) {B H : Matrix (Fin 6) (Fin 6) K}
    (hBU : (B.map σ)ᵀ * antiId K * B = antiId K) (hBB : B * B.map σ = 1)
    (hH : B * H.map σ = H) :
    ((H.map σ)ᵀ * antiId K * H).map σ = (H.map σ)ᵀ * antiId K * H ∧
      ((H.map σ)ᵀ * antiId K * H)ᵀ = (H.map σ)ᵀ * antiId K * H := by
  have hBBm : B.map σ * B = 1 := mul_eq_one_comm.1 hBB
  have hHm : H.map σ = B.map σ * H := by
    have := congrArg (fun M : Matrix (Fin 6) (Fin 6) K => M.map σ) hH
    simp only [Matrix.map_mul, map_map_eq_self hσσ] at this
    exact this.symm
  have hJ : (B.map σ)ᵀ * antiId K = antiId K * B.map σ := by
    calc (B.map σ)ᵀ * antiId K = (B.map σ)ᵀ * antiId K * (B * B.map σ) := by
          rw [hBB, Matrix.mul_one]
      _ = antiId K * B.map σ := by rw [← Matrix.mul_assoc, hBU]
  have hfix : ((H.map σ)ᵀ * antiId K * H).map σ = (H.map σ)ᵀ * antiId K * H := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, map_map_eq_self hσσ, antiId_map,
      hHm, Matrix.transpose_mul]
    calc Hᵀ * antiId K * (B.map σ * H) = Hᵀ * (antiId K * B.map σ) * H := by
          simp only [Matrix.mul_assoc]
      _ = Hᵀ * ((B.map σ)ᵀ * antiId K) * H := by rw [hJ]
      _ = Hᵀ * (B.map σ)ᵀ * antiId K * H := by simp only [Matrix.mul_assoc]
  refine ⟨hfix, ?_⟩
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, antiId_transpose,
    ← Matrix.mul_assoc]
  conv_rhs => rw [← hfix]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, map_map_eq_self hσσ, antiId_map]

end Descent

section Fixed

variable {k K : Type} [Field k] [Field K] [Algebra k K] [Finite k] {σ : K →+* K}

theorem fixed_algebraMap' (hσk : ∀ c, σ c = c ^ Nat.card k) (a : k) :
    σ (algebraMap k K a) = algebraMap k K a := by
  have : Fintype k := Fintype.ofFinite k
  rw [hσk, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem exists_map_eq_of_map_eq (hσk : ∀ c, σ c = c ^ Nat.card k)
    {G : Matrix (Fin 6) (Fin 6) K} (hG : G.map σ = G) :
    ∃ M : Matrix (Fin 6) (Fin 6) k, M.map (algebraMap k K) = G := by
  have h : ∀ i j, ∃ a : k, algebraMap k K a = G i j := fun i j =>
    mem_range_algebraMap_of_pow_card_eq (by rw [← hσk]; exact congrFun (congrFun hG i) j)
  choose M hM using h
  exact ⟨Matrix.of M, by ext i j; exact hM i j⟩

theorem exists_comp_eq_of_fixed (hσk : ∀ c, σ c = c ^ Nat.card k) {u : Fin 6 → K}
    (hu : (fun i => σ (u i)) = u) : ∃ v : Fin 6 → k, (fun i => algebraMap k K (v i)) = u := by
  have h : ∀ i, ∃ a : k, algebraMap k K a = u i := fun i =>
    mem_range_algebraMap_of_pow_card_eq (by rw [← hσk]; exact congrFun hu i)
  choose v hv using h
  exact ⟨v, funext hv⟩

end Fixed


section Normal

variable {k K : Type} [Field k] [Field K] [Algebra k K] [Finite k] {σ : K →+* K}

@[expose] def AltType (σ : K →+* K) (B : Matrix (Fin 6) (Fin 6) K) : Prop :=
  ∀ w, semiT σ B w = w → hermJ σ w w = 0

theorem dotProduct_mulVec_left (M : Matrix (Fin 6) (Fin 6) K) (x y : Fin 6 → K) :
    (M *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (Mᵀ *ᵥ y) := by
  rw [← vecMul_transpose, ← dotProduct_mulVec]

theorem semiT_mulVec_algebraMap (hσk : ∀ c, σ c = c ^ Nat.card k)
    {B H : Matrix (Fin 6) (Fin 6) K} (hH : B * H.map σ = H) (v : Fin 6 → k) :
    semiT σ B (H *ᵥ fun i => algebraMap k K (v i)) = H *ᵥ fun i => algebraMap k K (v i) := by
  rw [semiT, map_mulVec_fun, mulVec_mulVec, hH]
  congr 1
  funext i
  exact fixed_algebraMap' hσk _

theorem hermJ_mulVec_algebraMap (hσk : ∀ c, σ c = c ^ Nat.card k)
    {H : Matrix (Fin 6) (Fin 6) K} {M : Matrix (Fin 6) (Fin 6) k}
    (hM : M.map (algebraMap k K) = (H.map σ)ᵀ * antiId K * H) (v w : Fin 6 → k) :
    hermJ σ (H *ᵥ fun i => algebraMap k K (v i)) (H *ᵥ fun i => algebraMap k K (w i)) =
      algebraMap k K (v ⬝ᵥ (M *ᵥ w)) := by
  have hv : (fun i => σ (algebraMap k K (v i))) = fun i => algebraMap k K (v i) :=
    funext fun i => fixed_algebraMap' hσk _
  rw [hermJ, map_mulVec_fun, hv, dotProduct_mulVec_left, mulVec_mulVec, mulVec_mulVec, ← hM,
    RingHom.map_dotProduct]
  congr 1
  funext i
  exact (RingHom.map_mulVec _ M w i).symm

theorem exists_eq_mulVec_of_fixed (hσk : ∀ c, σ c = c ^ Nat.card k)
    {B : Matrix (Fin 6) (Fin 6) K} {H : GL (Fin 6) K}
    (hH : B * (H : Matrix (Fin 6) (Fin 6) K).map σ = H) {w : Fin 6 → K}
    (hw : semiT σ B w = w) :
    ∃ v : Fin 6 → k, w = (H : Matrix (Fin 6) (Fin 6) K) *ᵥ fun i => algebraMap k K (v i) := by
  set u := ((H⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w with hu
  have hHH : (H : Matrix (Fin 6) (Fin 6) K) * ((H⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hHH' : ((H⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * (H : Matrix (Fin 6) (Fin 6) K) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hwu : w = (H : Matrix (Fin 6) (Fin 6) K) *ᵥ u := by
    rw [hu, mulVec_mulVec, hHH, one_mulVec]
  have hfix : (fun i => σ (u i)) = u := by
    have h1 : semiT σ B w = (H : Matrix (Fin 6) (Fin 6) K) *ᵥ fun i => σ (u i) := by
      rw [semiT, hwu, map_mulVec_fun, mulVec_mulVec, hH]
    rw [hw] at h1
    have h2 := congrArg (fun x => ((H⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ x) h1
    simp only [mulVec_mulVec, hHH', one_mulVec] at h2
    rw [hu]
    exact h2.symm
  obtain ⟨v, hv⟩ := exists_comp_eq_of_fixed hσk hfix
  exact ⟨v, by rw [hwu, ← hv]⟩

theorem altType_iff (hσk : ∀ c, σ c = c ^ Nat.card k) {B : Matrix (Fin 6) (Fin 6) K}
    {H : GL (Fin 6) K} (hH : B * (H : Matrix (Fin 6) (Fin 6) K).map σ = H)
    {M : Matrix (Fin 6) (Fin 6) k}
    (hM : M.map (algebraMap k K) =
      ((H : Matrix (Fin 6) (Fin 6) K).map σ)ᵀ * antiId K * H) :
    AltType σ B ↔ ∀ v : Fin 6 → k, v ⬝ᵥ (M *ᵥ v) = 0 := by
  constructor
  · intro halt v
    have := halt _ (semiT_mulVec_algebraMap hσk hH v)
    rw [hermJ_mulVec_algebraMap hσk hM] at this
    exact (algebraMap k K).injective (by rw [this, map_zero])
  · intro halt w hw
    obtain ⟨v, rfl⟩ := exists_eq_mulVec_of_fixed hσk hH hw
    rw [hermJ_mulVec_algebraMap hσk hM, halt, map_zero]

theorem det_antiId_eq_one (h2 : (2 : K) = 0) : (antiId K).det = 1 :=
  eq_one_of_mul_self_eq_one_of_two_eq_zero h2 det_antiId_sq

end Normal

section Basis

variable {k K : Type} [Field k] [Field K] [Algebra k K] [Finite k] {σ : K →+* K}

omit [Finite k] in
theorem one_not_alternating :
    ¬ ∀ v : Fin 6 → k, v ⬝ᵥ (((1 : GL (Fin 6) k) : Matrix (Fin 6) (Fin 6) k) *ᵥ v) = 0 := by
  intro h
  have h0 := h (Pi.single 0 1)
  rw [Units.val_one, one_mulVec, single_dotProduct, one_mul, Pi.single_eq_same] at h0
  exact one_ne_zero h0

theorem exists_fixed_normal_basis (h2 : (2 : K) = 0) (hσσ : ∀ c, σ (σ c) = c)
    (hσk : ∀ c, σ c = c ^ Nat.card k) (he : ∃ e, e + σ e = 1) {B : Matrix (Fin 6) (Fin 6) K}
    (hBU : (B.map σ)ᵀ * antiId K * B = antiId K) (hBB : B * B.map σ = 1) (hBdet : B.det = 1) :
    ∃ H : Matrix (Fin 6) (Fin 6) K, H.det = 1 ∧ B * H.map σ = H ∧
      ((AltType σ B ∧ (H.map σ)ᵀ * antiId K * H = antiId K) ∨
        (¬ AltType σ B ∧ (H.map σ)ᵀ * antiId K * H = 1)) := by
  have hk2 : (2 : k) = 0 := (algebraMap k K).injective (by rw [map_ofNat, map_zero]; exact h2)
  have : CharP k 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hk2
  obtain ⟨H₀, hH₀⟩ := exists_fixed_matrix h2 hσσ hBB he
  obtain ⟨hGfix, hGsym⟩ := gram_map_eq_and_transpose hσσ hBU hBB hH₀
  obtain ⟨M, hM⟩ := exists_map_eq_of_map_eq hσk hGfix
  have hMsym : Mᵀ = M := Matrix.map_injective (algebraMap k K).injective (by
    show Mᵀ.map (algebraMap k K) = M.map (algebraMap k K)
    rw [Matrix.transpose_map, hM, hGsym])
  have hH₀d : (H₀ : Matrix (Fin 6) (Fin 6) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp H₀.isUnit).ne_zero
  have hdetG : (((H₀ : Matrix (Fin 6) (Fin 6) K).map σ)ᵀ * antiId K * H₀).det ≠ 0 := by
    rw [det_mul, det_mul, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      det_antiId_eq_one h2, mul_one]
    exact mul_ne_zero ((map_ne_zero σ).2 hH₀d) hH₀d
  have hMdet : M.det ≠ 0 := by
    intro h
    apply hdetG
    rw [← hM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
  set MGL : GL (Fin 6) k := Matrix.nonsingInvUnit M (isUnit_iff_ne_zero.2 hMdet) with hMGL
  have hMGLc : (MGL : Matrix (Fin 6) (Fin 6) k) = M := rfl
  have htype := altType_iff hσk hH₀ hM
  have key : ∀ C D : GL (Fin 6) k,
      (D : Matrix (Fin 6) (Fin 6) k) * M * (D : Matrix (Fin 6) (Fin 6) k)ᵀ = C →
      (C : Matrix (Fin 6) (Fin 6) k).det = 1 →
      ∃ H : Matrix (Fin 6) (Fin 6) K, H.det = 1 ∧ B * H.map σ = H ∧
        (H.map σ)ᵀ * antiId K * H = (C : Matrix (Fin 6) (Fin 6) k).map (algebraMap k K) := by
    intro C D hD hC
    set Q : Matrix (Fin 6) (Fin 6) K := ((D : Matrix (Fin 6) (Fin 6) k)ᵀ).map (algebraMap k K)
      with hQ
    have hQσ : Q.map σ = Q := by
      ext i j
      exact fixed_algebraMap' hσk _
    set H := (H₀ : Matrix (Fin 6) (Fin 6) K) * Q with hHdef
    have hBH : B * H.map σ = H := by rw [Matrix.map_mul, hQσ, ← Matrix.mul_assoc, hH₀]
    have hQt : Qᵀ = (D : Matrix (Fin 6) (Fin 6) k).map (algebraMap k K) := by
      rw [hQ, Matrix.transpose_map, Matrix.transpose_transpose]
    have hGram : (H.map σ)ᵀ * antiId K * H =
        (C : Matrix (Fin 6) (Fin 6) k).map (algebraMap k K) := by
      rw [Matrix.map_mul, hQσ, Matrix.transpose_mul]
      calc Qᵀ * ((H₀ : Matrix (Fin 6) (Fin 6) K).map σ)ᵀ * antiId K *
            ((H₀ : Matrix (Fin 6) (Fin 6) K) * Q) =
            Qᵀ * (((H₀ : Matrix (Fin 6) (Fin 6) K).map σ)ᵀ * antiId K * H₀) * Q := by
            simp only [Matrix.mul_assoc]
        _ = ((D : Matrix (Fin 6) (Fin 6) k) * M *
              (D : Matrix (Fin 6) (Fin 6) k)ᵀ).map (algebraMap k K) := by
            rw [← hM, hQt, hQ, Matrix.map_mul, Matrix.map_mul]
        _ = _ := by rw [hD]
    refine ⟨H, ?_, hBH, hGram⟩
    have e1 := congrArg Matrix.det hBH
    rw [det_mul, hBdet, one_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at e1
    have e2 := congrArg Matrix.det hGram
    rw [det_mul, det_mul, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      det_antiId_eq_one h2, mul_one, e1, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hC,
      map_one] at e2
    exact eq_one_of_mul_self_eq_one_of_two_eq_zero h2 e2
  by_cases halt : AltType σ B
  · obtain ⟨D, hD⟩ := exists_congruence_of_alternating_iff MGL (antiIdGL k) hMsym antiId_transpose
      (iff_of_true (htype.1 halt) (antiId_alternating hk2))
    obtain ⟨H, hdet, hBH, hG⟩ := key (antiIdGL k) D hD (det_antiId_eq_one hk2)
    exact ⟨H, hdet, hBH, Or.inl ⟨halt, by rw [hG, coe_antiIdGL, antiId_map]⟩⟩
  · obtain ⟨D, hD⟩ := exists_congruence_of_alternating_iff MGL 1 hMsym (by simp)
      (iff_of_false (fun h => halt (htype.2 h)) one_not_alternating)
    obtain ⟨H, hdet, hBH, hG⟩ := key 1 D hD (by simp)
    refine ⟨H, hdet, hBH, Or.inr ⟨halt, ?_⟩⟩
    rw [hG, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

end Basis

section Conj

variable {k K : Type} [Field k] [Field K] [Algebra k K] [Finite k] {σ : K →+* K}

theorem coe_mul_map_eq_one {B : SpecialLinearGroup (Fin 6) K}
    (hBB : B * Matrix.SpecialLinearGroup.map σ B = 1) :
    (B : Matrix (Fin 6) (Fin 6) K) * (B : Matrix (Fin 6) (Fin 6) K).map σ = 1 := by
  have := congrArg (fun C : SpecialLinearGroup (Fin 6) K => (C : Matrix (Fin 6) (Fin 6) K)) hBB
  simpa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] using this

theorem exists_unitary_conj (h2 : (2 : K) = 0) (hσσ : ∀ c, σ (σ c) = c)
    (hσk : ∀ c, σ c = c ^ Nat.card k) (he : ∃ e, e + σ e = 1)
    {B B' : SpecialLinearGroup (Fin 6) K} (hB : B ∈ unitarySL σ) (hB' : B' ∈ unitarySL σ)
    (hBB : B * Matrix.SpecialLinearGroup.map σ B = 1)
    (hBB' : B' * Matrix.SpecialLinearGroup.map σ B' = 1)
    (htype : AltType σ (B : Matrix (Fin 6) (Fin 6) K) ↔
      AltType σ (B' : Matrix (Fin 6) (Fin 6) K)) :
    ∃ D ∈ unitarySL σ, D * B * Matrix.SpecialLinearGroup.map σ D⁻¹ = B' := by
  obtain ⟨H, hHdet, hBH, hHG⟩ := exists_fixed_normal_basis (k := k) h2 hσσ hσk he
    (mem_unitarySL_iff.1 hB) (coe_mul_map_eq_one hBB) B.2
  obtain ⟨H', hH'det, hBH', hH'G⟩ := exists_fixed_normal_basis (k := k) h2 hσσ hσk he
    (mem_unitarySL_iff.1 hB') (coe_mul_map_eq_one hBB') B'.2
  have hG : (H.map σ)ᵀ * antiId K * H = (H'.map σ)ᵀ * antiId K * H' := by
    rcases hHG with ⟨ha, hg⟩ | ⟨ha, hg⟩ <;> rcases hH'G with ⟨ha', hg'⟩ | ⟨ha', hg'⟩
    · rw [hg, hg']
    · exact absurd (htype.1 ha) ha'
    · exact absurd (htype.2 ha') ha
    · rw [hg, hg']
  set Hs : SpecialLinearGroup (Fin 6) K := ⟨H, hHdet⟩
  set Hs' : SpecialLinearGroup (Fin 6) K := ⟨H', hH'det⟩
  have hBHs : B * Matrix.SpecialLinearGroup.map σ Hs = Hs := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply]
    exact hBH)
  have hBHs' : B' * Matrix.SpecialLinearGroup.map σ Hs' = Hs' := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply]
    exact hBH')
  refine ⟨Hs' * Hs⁻¹, ?_, ?_⟩
  · rw [mem_unitarySL_iff]
    set N := ((Hs⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
    have hHN : H * N = 1 := by
      change (Hs : Matrix (Fin 6) (Fin 6) K) * N = 1
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    rw [Matrix.SpecialLinearGroup.coe_mul]
    change ((H' * N).map σ)ᵀ * antiId K * (H' * N) = antiId K
    calc ((H' * N).map σ)ᵀ * antiId K * (H' * N) =
          (N.map σ)ᵀ * ((H'.map σ)ᵀ * antiId K * H') * N := by
          rw [Matrix.map_mul, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = ((H * N).map σ)ᵀ * antiId K * (H * N) := by
          rw [← hG, Matrix.map_mul, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = antiId K := by
          rw [hHN, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one,
            Matrix.one_mul, Matrix.mul_one]
  · have e : B' = Hs' * (Matrix.SpecialLinearGroup.map σ Hs')⁻¹ :=
      eq_mul_inv_of_mul_eq hBHs'
    calc Hs' * Hs⁻¹ * B * Matrix.SpecialLinearGroup.map σ (Hs' * Hs⁻¹)⁻¹ =
          Hs' * Hs⁻¹ * (B * Matrix.SpecialLinearGroup.map σ Hs) *
            (Matrix.SpecialLinearGroup.map σ Hs')⁻¹ := by
          rw [_root_.mul_inv_rev, inv_inv, map_mul, map_inv]
          group
      _ = Hs' * (Matrix.SpecialLinearGroup.map σ Hs')⁻¹ := by
          rw [hBHs]
          group
      _ = B' := e.symm

end Conj

section Reps

variable {K : Type} [Field K] {σ : K →+* K}

theorem sq_mul_diagramMap_of_mem
    (h2 : (2 : K) = 0) {B : SpecialLinearGroup (Fin 6) K}
    (hB : B ∈ unitarySL σ) :
    (realize h2 B * diagramMap TwistTag.E6 K) ^ 2 =
      realize h2 (B * Matrix.SpecialLinearGroup.map σ B) := by
  have hPP := diagramMap_E6_mul_self (K := K)
  have hPinv : (diagramMap TwistTag.E6 K)⁻¹ = diagramMap TwistTag.E6 K :=
    (eq_inv_of_mul_eq_one_left hPP).symm
  rw [map_mul, ← diagramMap_conj_realize_of_mem_unitarySL h2 hB, sq, hPinv]
  calc realize h2 B * diagramMap TwistTag.E6 K * (realize h2 B * diagramMap TwistTag.E6 K) =
        realize h2 B * (diagramMap TwistTag.E6 K * realize h2 B * diagramMap TwistTag.E6 K) *
          (diagramMap TwistTag.E6 K * diagramMap TwistTag.E6 K) := by
        rw [hPP, mul_one]
        group
    _ = _ := by rw [hPP, mul_one]

theorem mul_map_eq_one_of_sq_eq_one
    (h2 : (2 : K) = 0) (hσσ : ∀ c, σ (σ c) = c)
    {B : SpecialLinearGroup (Fin 6) K} (hB : B ∈ unitarySL σ)
    (hsq : (realize h2 B * diagramMap TwistTag.E6 K) ^ 2 = 1) :
    B * Matrix.SpecialLinearGroup.map σ B = 1 := by
  rw [sq_mul_diagramMap_of_mem h2 hB, ← MonoidHom.mem_ker] at hsq
  obtain ⟨l, hl3, hl⟩ := (mem_ker_realize h2 _).1 hsq
  set Z := B * Matrix.SpecialLinearGroup.map σ B with hZ
  have hZU : Z ∈ unitarySL σ := mul_mem hB (map_mem_unitarySL hσσ hB)
  have hU := mem_unitarySL_iff.1 hZU
  rw [hl] at hU
  have hn : σ l * l = 1 := by
    have e1 : ((Matrix.scalar (Fin 6) l).map σ)ᵀ * antiId K * Matrix.scalar (Fin 6) l =
        (σ l * l) • antiId K := by
      rw [Matrix.scalar_apply, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose,
        ← Matrix.smul_eq_diagonal_mul, Matrix.smul_mul, ← Matrix.smul_eq_mul_diagonal, smul_smul]
    rw [e1] at hU
    have e := congrFun (congrFun hU 0) 5
    simp only [Matrix.smul_apply, smul_eq_mul, antiId, Matrix.of_apply] at e
    have h5 : (5 : Fin 6) = Fin.rev 0 := rfl
    rw [ite_eq_left h5, mul_one] at e
    exact e
  have hZσ : Matrix.SpecialLinearGroup.map σ Z = Z := by
    have hc : Z * B = B * Z := Subtype.ext (by
      show (Z : Matrix (Fin 6) (Fin 6) K) * (B : Matrix (Fin 6) (Fin 6) K) =
        (B : Matrix (Fin 6) (Fin 6) K) * (Z : Matrix (Fin 6) (Fin 6) K)
      rw [hl]
      exact (Matrix.scalar_commute l (fun r => Commute.all l r)
        (B : Matrix (Fin 6) (Fin 6) K)).eq)
    calc Matrix.SpecialLinearGroup.map σ Z =
          Matrix.SpecialLinearGroup.map σ B * B := by
          rw [hZ, map_mul, map_map_of_involutive hσσ]
      _ = B⁻¹ * (Z * B) := by rw [hZ]; group
      _ = Z := by rw [hc]; group
  have hfix : σ l = l := by
    have e := congrArg (fun C : SpecialLinearGroup (Fin 6) K => (C : Matrix (Fin 6) (Fin 6) K) 0 0)
      hZσ
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      hl, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at e
    exact e
  have hl1 : l = 1 := by
    rw [hfix] at hn
    calc l = l * (l * l) := by rw [hn, mul_one]
      _ = l ^ 3 := by ring
      _ = 1 := hl3
  apply Subtype.ext
  rw [hl, hl1, map_one, Matrix.SpecialLinearGroup.coe_one]

@[expose] def uSU (K : Type) [Field K] : SpecialLinearGroup (Fin 6) K :=
  SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 5 by decide) 1

theorem map_uSU : Matrix.SpecialLinearGroup.map σ (uSU K) = uSU K := by
  rw [uSU, map_transvection, map_one]

theorem uSU_mem (h2 : (2 : K) = 0) : uSU K ∈ unitarySL σ := by
  rw [mem_unitarySL_iff_unitaryTwist]
  change graphSL K (Matrix.SpecialLinearGroup.map σ (uSU K)) = uSU K
  rw [map_uSU, uSU, graphSL_transvection h2]

theorem uSU_mul_map (h2 : (2 : K) = 0) : uSU K * Matrix.SpecialLinearGroup.map σ (uSU K) = 1 := by
  rw [map_uSU]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  change Matrix.transvection (0 : Fin 6) 5 (1 : K) * Matrix.transvection 0 5 1 = 1
  have hE : (Matrix.single (0 : Fin 6) (5 : Fin 6) (1 : K) : Matrix (Fin 6) (Fin 6) K) *
      Matrix.single (0 : Fin 6) (5 : Fin 6) (1 : K) = 0 :=
    Matrix.single_mul_single_of_ne (1 : K) (0 : Fin 6) 5 0 (by decide) (1 : K)
  rw [Matrix.transvection, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul,
    Matrix.one_mul, Matrix.mul_one, hE, add_zero, add_assoc,
    ← two_smul K (Matrix.single (0 : Fin 6) 5 (1 : K)), h2, zero_smul, add_zero]

theorem one_mul_map_self : (1 : SpecialLinearGroup (Fin 6) K) *
    Matrix.SpecialLinearGroup.map σ 1 = 1 := by
  rw [map_one, mul_one]

theorem altType_one (h2 : (2 : K) = 0) :
    AltType σ ((1 : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
  intro w hw
  rw [semiT, Matrix.SpecialLinearGroup.coe_one, one_mulVec] at hw
  rw [hermJ, hw]
  exact antiId_alternating h2 w

theorem not_altType_uSU (h2 : (2 : K) = 0) {c : K}
    (hc : c + σ c = 1) : ¬ AltType σ (uSU K : Matrix (Fin 6) (Fin 6) K) := by
  intro halt
  set w : Fin 6 → K := c • Pi.single 0 1 + Pi.single 5 1 with hw
  have hw0 : w 0 = c := by simp [hw]
  have hw5 : w 5 = 1 := by simp [hw]
  have hwi : ∀ i, i ≠ 0 → i ≠ 5 → w i = 0 := fun i h0 h5 => by
    simp [hw, Pi.single_eq_of_ne h0, Pi.single_eq_of_ne h5]
  have hfix : semiT σ (uSU K : Matrix (Fin 6) (Fin 6) K) w = w := by
    funext i
    change (Matrix.transvection (0 : Fin 6) 5 (1 : K) *ᵥ fun j => σ (w j)) i = w i
    rw [Matrix.transvection, Matrix.add_mulVec, one_mulVec, Pi.add_apply, Matrix.single_mulVec]
    by_cases h0 : i = 0
    · subst h0
      rw [Function.update_self, hw0, hw5, map_one, one_mul]
      linear_combination hc + (1 - c) * h2
    · rw [Function.update_of_ne h0, Pi.zero_apply, add_zero]
      by_cases h5 : i = 5
      · subst h5
        rw [hw5, map_one]
      · rw [hwi i h0 h5, map_zero]
  have h1 := halt w hfix
  rw [hermJ] at h1
  simp only [dotProduct, antiId_mulVec, Fin.sum_univ_six] at h1
  have r0 : Fin.rev (0 : Fin 6) = 5 := rfl
  have r1 : Fin.rev (1 : Fin 6) = 4 := rfl
  have r2 : Fin.rev (2 : Fin 6) = 3 := rfl
  have r3 : Fin.rev (3 : Fin 6) = 2 := rfl
  have r4 : Fin.rev (4 : Fin 6) = 1 := rfl
  have r5 : Fin.rev (5 : Fin 6) = 0 := rfl
  rw [r0, r1, r2, r3, r4, r5, hw0, hw5, hwi 1 (by decide) (by decide),
    hwi 2 (by decide) (by decide), hwi 3 (by decide) (by decide),
    hwi 4 (by decide) (by decide), map_zero, map_one] at h1
  have : (1 : K) = 0 := by linear_combination h1 - hc
  exact one_ne_zero this

end Reps

section Main

variable {K : Type} [Field K] {σ : K →+* K}

theorem conj_realize_mul_diagramMap_of_mem
    (h2 : (2 : K) = 0)
    {D : SpecialLinearGroup (Fin 6) K} (hD : D ∈ unitarySL σ) (B : SpecialLinearGroup (Fin 6) K) :
    realize h2 D * (realize h2 B * diagramMap TwistTag.E6 K) * (realize h2 D)⁻¹ =
      realize h2 (D * B * Matrix.SpecialLinearGroup.map σ D⁻¹) * diagramMap TwistTag.E6 K := by
  have hP := diagramMap_conj_realize_of_mem_unitarySL h2 (inv_mem hD)
  rw [map_inv] at hP
  calc realize h2 D * (realize h2 B * diagramMap TwistTag.E6 K) * (realize h2 D)⁻¹ =
        realize h2 D * realize h2 B *
          (diagramMap TwistTag.E6 K * (realize h2 D)⁻¹ * (diagramMap TwistTag.E6 K)⁻¹) *
            diagramMap TwistTag.E6 K := by group
    _ = _ := by rw [hP, map_mul, map_mul]

end Main

theorem _root_.CFSG.LieType.Chevalley.even_E6_graph_unitary_Levi_involution_forms
    (f : ℕ)
    (hf : 1 ≤ f) (k K : Type) [Field k] [Field K] [Algebra k K] (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ∀ ℓ ∈ subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ,
      (ℓ * diagramMap TwistTag.E6 K) ^ 2 = 1 →
      ((∃ D ∈ unitarySL σ,
          realize (two_eq_zero_of_card_sq hf hK) D ∈
            subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ ∧
          realize (two_eq_zero_of_card_sq hf hK) D * (ℓ * diagramMap TwistTag.E6 K) *
            (realize (two_eq_zero_of_card_sq hf hK) D)⁻¹ = diagramMap TwistTag.E6 K) ∨
        ∃ D ∈ unitarySL σ,
          realize (two_eq_zero_of_card_sq hf hK) D ∈
            subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ ∧
          realize (two_eq_zero_of_card_sq hf hK) D * (ℓ * diagramMap TwistTag.E6 K) *
            (realize (two_eq_zero_of_card_sq hf hK) D)⁻¹ =
              pinnedX TwistTag.E6.tag K sRoot 1 * diagramMap TwistTag.E6 K) ∧
      ((∃ x ∈ subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ,
          x * (ℓ * diagramMap TwistTag.E6 K) * x⁻¹ =
            pinnedX TwistTag.E6.tag K sRoot 1 * diagramMap TwistTag.E6 K) →
        ∃ g ∈ graphFixedRootGroup TwistTag.E6 K σ,
          (thetaRootGroup (algebraMap k K)).map (MulAut.conj g).toMonoidHom ≤
              subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ ∧
            ¬ IsPGroup 2 ↥((thetaRootGroup (algebraMap k K)).map (MulAut.conj g).toMonoidHom ⊔
              ((thetaRootGroup (algebraMap k K)).map (MulAut.conj g).toMonoidHom).map
                (MulAut.conj (ℓ * diagramMap TwistTag.E6 K)).toMonoidHom)) := by
  intro ℓ hℓ hsq
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hK2
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    rw [hσ, hσ]
    exact CFSG.LieType.Simplicity.pow_pow_card_sq hK c
  have hσk : ∀ c, σ c = c ^ Nat.card k := fun c => by rw [hk]; exact hσ c
  obtain ⟨e, he⟩ : ∃ e, e + σ e = 1 := by
    obtain ⟨e, he⟩ := (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution
      (p := 2) (f := f) hK).trace_surj 1 (map_one _)
    refine ⟨e, ?_⟩
    rwa [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← hσ] at he
  obtain ⟨hLC, -, -⟩ := subsystemGroup_inf_eq_map_realize hK hσ hK2
  have hXC := thetaRankOneGroup_le_graphFixedRootGroup (k := k) hK2 hσk
  refine ⟨?_, ?_⟩
  · have hℓ' := hℓ
    rw [hLC] at hℓ'
    obtain ⟨B, hB, rfl⟩ := hℓ'
    have hBB := mul_map_eq_one_of_sq_eq_one hK2 hσσ hB hsq
    have hmem : ∀ D ∈ unitarySL σ, realize hK2 D ∈
        subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ :=
      fun D hD => by
        rw [hLC]
        exact ⟨D, hD, rfl⟩
    by_cases halt : AltType σ (B : Matrix (Fin 6) (Fin 6) K)
    · obtain ⟨D, hD, hDB⟩ := exists_unitary_conj (k := k) hK2 hσσ hσk ⟨e, he⟩ hB
        (one_mem _) hBB one_mul_map_self (iff_of_true halt (altType_one hK2))
      refine Or.inl ⟨D, hD, hmem D hD, ?_⟩
      rw [conj_realize_mul_diagramMap_of_mem hK2 hD, hDB, map_one, one_mul]
    · obtain ⟨D, hD, hDB⟩ := exists_unitary_conj (k := k) hK2 hσσ hσk ⟨e, he⟩ hB
        (uSU_mem hK2) hBB (uSU_mul_map hK2) (iff_of_false halt (not_altType_uSU hK2 he))
      refine Or.inr ⟨D, hD, hmem D hD, ?_⟩
      rw [conj_realize_mul_diagramMap_of_mem hK2 hD, hDB, uSU, realize_transvection_zero_five]
  · rintro ⟨x, hx, hxj⟩
    have hwC : wordElt K negSWord ∈ graphFixedRootGroup TwistTag.E6 K σ :=
      wordElt_mem_graphFixedRootGroup hK2 weylTwist_negSWord
    refine ⟨x⁻¹ * wordElt K negSWord, mul_mem (inv_mem (Subgroup.mem_inf.1 hx).2) hwC, ?_,
      detector_of_conj hK2 (algebraMap k K) hxj⟩
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_thetaRootGroup _).1 hr
    have hθ : pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K c) ∈
        graphFixedRootGroup TwistTag.E6 K σ :=
      hXC (Subgroup.mem_sup_left ((mem_thetaRootGroup _).2 ⟨c, rfl⟩))
    have hs : pinnedX TwistTag.E6.tag K (-sRoot) (algebraMap k K c) ∈
        subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ := by
      refine Subgroup.mem_inf.2 ⟨pinnedX_negS_mem_subsystemGroup hK2 _, ?_⟩
      rw [← wordElt_negSWord_conj hK2]
      exact mul_mem (mul_mem hwC hθ) (inv_mem hwC)
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      show x⁻¹ * wordElt K negSWord * pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K c) *
        (x⁻¹ * wordElt K negSWord)⁻¹ = x⁻¹ * (wordElt K negSWord *
          pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K c) *
            (wordElt K negSWord)⁻¹) * x⁻¹⁻¹ by group, wordElt_negSWord_conj hK2, inv_inv]
    exact mul_mem (mul_mem (inv_mem hx) hs) hx

end CFSG.LieType.Chevalley.E6GraphInvolution
