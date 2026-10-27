module

public import CFSG.GH74.Generic.S1.FrameNormUni
public import CFSG.RankThree.PartOne.KC.CommonEigenbasis

public section

namespace CFSG.GH74.Generic.S1.SymDiagUni

open Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary

variable {F : Type} [Field F]

theorem trace_ne_zero_of_refl (hchar : ringChar F ≠ 2) {ρ : GL (Fin 4) F} (hρ : ρ * ρ = 1)
    (hdet : (ρ : Matrix (Fin 4) (Fin 4) F).det = -1) :
    Matrix.trace (ρ : Matrix (Fin 4) (Fin 4) F) ≠ 0 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
  obtain ⟨ρ', P, hρ', hP, -⟩ := exists_refl_conj hchar hρ hdet
  have htr : Matrix.trace (ρ' : Matrix (Fin 4) (Fin 4) F) = 2 := by
    have h1 : Matrix.trace ((P⁻¹ * ρ' * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 2 := by
      rw [hP]
      change Matrix.trace (reflDiagMat F 3) = 2
      simp [Matrix.trace, reflDiagMat, Fin.sum_univ_four]
      norm_num
    rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.one_mul] at h1
    exact h1
  rcases hρ' with rfl | rfl
  · rw [htr]; exact h2
  · rw [Units.val_neg, Matrix.trace_neg] at htr
    intro h0
    rw [h0, neg_zero] at htr
    exact h2 htr.symm

theorem commute_of_smul_comm {A B : Matrix (Fin 4) (Fin 4) F} (hB : B * B = 1)
    (htr : Matrix.trace A ≠ 0) {c : F} (hc : A * B = c • (B * A)) : A * B = B * A := by
  have h1 : A = c • (B * A * B) := by
    calc A = A * (B * B) := by rw [hB, Matrix.mul_one]
      _ = (A * B) * B := (Matrix.mul_assoc _ _ _).symm
      _ = c • (B * A) * B := by rw [hc]
      _ = c • (B * A * B) := by rw [Matrix.smul_mul]
  have h2 : Matrix.trace A = c * Matrix.trace A := by
    conv_lhs => rw [h1]
    rw [Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm (B * A) B, ← Matrix.mul_assoc, hB,
      Matrix.one_mul]
  have h3 : (1 - c) * Matrix.trace A = 0 := by linear_combination h2
  have h4 : c = 1 := by
    have := (mul_eq_zero.1 h3).resolve_right htr
    linear_combination -this
  rw [h4, one_smul] at hc
  exact hc

theorem det_eq_prod_of_eigen {R : Matrix (Fin 4) (Fin 4) F} (b : Basis (Fin 4) F (Fin 4 → F))
    (μ : Fin 4 → F) (hb : ∀ k, R *ᵥ b k = μ k • b k) : R.det = ∏ k, μ k := by
  have h1 : LinearMap.toMatrix b b (Matrix.toLin' R) = Matrix.diagonal μ := by
    ext a c
    rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply, hb c, map_smul, Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_apply, Matrix.diagonal_apply]
    by_cases hac : a = c
    · subst hac
      simp
    · simp [hac, Ne.symm hac]
  rw [← LinearMap.det_toLin' R, ← LinearMap.det_toMatrix b, h1, Matrix.det_diagonal]

theorem pattern_of_prod (h2 : (2 : F) ≠ 0) (a : Fin 4 → F) (ha : ∀ k, a k = 1 ∨ a k = -1)
    (hprod : ∏ k, a k = -1) :
    ∃ (ε : F) (i : Fin 4), (ε = 1 ∨ ε = -1) ∧ ∀ k, ε * a k = if k = i then -1 else 1 := by
  rw [Fin.prod_univ_four] at hprod
  rcases ha 0 with h0 | h0 <;> rcases ha 1 with h1 | h1 <;> rcases ha 2 with h2' | h2' <;>
    rcases ha 3 with h3 | h3 <;> rw [h0, h1, h2', h3] at hprod <;>
    first
    | exact absurd (by linear_combination hprod : (2 : F) = 0) h2
    | (refine ⟨1, 0, Or.inl rfl, fun k => ?_⟩; fin_cases k <;> simp [h0, h1, h2', h3]; done)
    | (refine ⟨1, 1, Or.inl rfl, fun k => ?_⟩; fin_cases k <;> simp [h0, h1, h2', h3]; done)
    | (refine ⟨1, 2, Or.inl rfl, fun k => ?_⟩; fin_cases k <;> simp [h0, h1, h2', h3]; done)
    | (refine ⟨1, 3, Or.inl rfl, fun k => ?_⟩; fin_cases k <;> simp [h0, h1, h2', h3]; done)
    | (refine ⟨-1, 0, Or.inr rfl, fun k => ?_⟩; fin_cases k <;> simp [h0, h1, h2', h3]; done)
    | (refine ⟨-1, 1, Or.inr rfl, fun k => ?_⟩; fin_cases k <;> simp [h0, h1, h2', h3]; done)
    | (refine ⟨-1, 2, Or.inr rfl, fun k => ?_⟩; fin_cases k <;> simp [h0, h1, h2', h3]; done)
    | (refine ⟨-1, 3, Or.inr rfl, fun k => ?_⟩; fin_cases k <;> simp [h0, h1, h2', h3])

theorem exists_common_eigenbasis (hchar : ringChar F ≠ 2) (R : Fin 4 → Matrix (Fin 4) (Fin 4) F)
    (hR2 : ∀ j, R j * R j = 1) (hcomm : ∀ j k, R j * R k = R k * R j) :
    ∃ (b : Basis (Fin 4) F (Fin 4 → F)) (μ : Fin 4 → Fin 4 → F), ∀ j k, R j *ᵥ b k = μ j k • b k := by
  have : CharP F (ringChar F) := ringChar.charP F
  have hζ : IsPrimitiveRoot (-1 : F) 2 := IsPrimitiveRoot.neg_one (ringChar F) hchar
  let f : Fin 4 → Module.End F (Fin 4 → F) := fun j => Matrix.toLinAlgEquiv' (R j)
  have hf_comm : ∀ i j, Commute (f i) (f j) := fun i j => by
    show f i * f j = f j * f i
    simp only [f, ← map_mul, hcomm i j]
  have hf_pow : ∀ i, f i ^ 2 = 1 := fun i => by
    have h1 : f i ^ 2 = Matrix.toLinAlgEquiv' (R i ^ 2) :=
      (map_pow Matrix.toLinAlgEquiv' (R i) 2).symm
    rw [h1, pow_two, hR2 i, map_one]
  obtain ⟨b₀, μ₀, hb₀⟩ :=
    CFSG.RankThree.PartOne.exists_basis_common_eigenvectors_of_pow_eq_one hζ f hf_comm hf_pow
  let e : Fin 4 ≃ Fin (finrank F (Fin 4 → F)) := finCongr (Module.finrank_fin_fun F).symm
  refine ⟨b₀.reindex e.symm, fun j k => μ₀ j (e k), fun j k => ?_⟩
  have := hb₀ j (e k)
  simpa [f, Basis.reindex_apply] using this

theorem exists_pattern (hchar : ringChar F ≠ 2) (ρ : Fin 4 → GL (Fin 4) F)
    (hρ2 : ∀ j, ρ j * ρ j = 1)
    (hdet : ∀ j, ((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = -1)
    (hcomm : ∀ j k, ∃ c : F, ((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((ρ k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      c • (((ρ k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        ((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)))
    (hne : ∀ j k, j ≠ k → ∀ c : F, ((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) ≠
      c • ((ρ k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) :
    ∃ (b : Basis (Fin 4) F (Fin 4 → F)) (ε : Fin 4 → F) (π : Fin 4 → Fin 4),
      (∀ j, ε j = 1 ∨ ε j = -1) ∧ Function.Injective π ∧
      ∀ j k, ((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ b k =
        (ε j * if k = π j then -1 else 1) • b k := by
  classical
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
  set R : Fin 4 → Matrix (Fin 4) (Fin 4) F := fun j => ((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
    with hR
  have hRR : ∀ j, R j * R j = 1 := fun j => by
    rw [hR]; dsimp only; rw [← Units.val_mul, hρ2 j, Units.val_one]
  have hc : ∀ j k, R j * R k = R k * R j := fun j k => by
    obtain ⟨c, hc⟩ := hcomm j k
    exact commute_of_smul_comm (hRR k) (trace_ne_zero_of_refl hchar (hρ2 j) (hdet j)) hc
  obtain ⟨b, μ, hb⟩ := exists_common_eigenbasis hchar R hRR hc
  have hμ : ∀ j k, μ j k = 1 ∨ μ j k = -1 := by
    intro j k
    have h1 : R j *ᵥ (R j *ᵥ b k) = b k := by
      rw [Matrix.mulVec_mulVec, hRR j, Matrix.one_mulVec]
    rw [hb j k, Matrix.mulVec_smul, hb j k, smul_smul] at h1
    have h3 : (μ j k * μ j k - 1) • b k = 0 := by
      rw [sub_smul, h1, one_smul, sub_self]
    have h4 := (smul_eq_zero.1 h3).resolve_right (b.ne_zero k)
    exact mul_self_eq_one_iff.1 (sub_eq_zero.1 h4)
  have hprod : ∀ j, ∏ k, μ j k = -1 := fun j => by
    rw [← det_eq_prod_of_eigen b (μ j) (hb j)]
    exact hdet j
  have hpat : ∀ j, ∃ (ε : F) (i : Fin 4), (ε = 1 ∨ ε = -1) ∧
      ∀ k, ε * μ j k = if k = i then -1 else 1 := fun j =>
    pattern_of_prod h2 (μ j) (hμ j) (hprod j)
  choose ε π hε hεπ using hpat
  have hεε : ∀ j, ε j * ε j = 1 := fun j => mul_self_eq_one_iff.2 (hε j)
  have hev : ∀ j k, R j *ᵥ b k = (ε j * if k = π j then -1 else 1) • b k := by
    intro j k
    rw [← hεπ j k, ← mul_assoc, hεε j, one_mul]
    exact hb j k
  refine ⟨b, ε, π, hε, ?_, hev⟩
  intro j k hjk
  by_contra hne'
  have hjk' : j ≠ k := fun e => hne' e
  have hlin : Matrix.toLin' (ε j • R j) = Matrix.toLin' (ε k • R k) := by
    apply b.ext
    intro l
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.smul_mulVec, hb j l,
      hb k l, smul_smul, smul_smul, hεπ j l, hεπ k l, hjk]
  have hmat : ε j • R j = ε k • R k := Matrix.toLin'.injective hlin
  have hRj : R j = (ε j * ε k) • R k := by
    calc R j = (ε j * ε j) • R j := by rw [hεε j, one_smul]
      _ = ε j • (ε j • R j) := by rw [smul_smul]
      _ = ε j • (ε k • R k) := by rw [hmat]
      _ = (ε j * ε k) • R k := by rw [smul_smul]
  exact hne j k hjk' (ε j * ε k) hRj


theorem exists_unitary_frame_matrix {p f : ℕ} (h : UnitaryFieldData p f F) (hp2 : p ≠ 2)
    (R : Fin 4 → Matrix (Fin 4) (Fin 4) F)
    (hunit : ∀ j, conjTr (FrameUni.frameBar h) (R j) * R j = 1)
    (b : Basis (Fin 4) F (Fin 4 → F)) (ε : Fin 4 → F) (π : Fin 4 → Fin 4)
    (hε : ∀ j, ε j = 1 ∨ ε j = -1) (hπ : Function.Injective π)
    (hev : ∀ j k, R j *ᵥ b k = (ε j * if k = π j then -1 else 1) • b k) :
    ∃ P : Matrix (Fin 4) (Fin 4) F, conjTr (FrameUni.frameBar h) P * P = 1 ∧
      ∀ j, conjTr (FrameUni.frameBar h) P * R j * P = ε j • reflDiagMat F j := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP F p := h.charP
  have hchar : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
  set σ := FrameUni.frameBar h with hσ
  have hσσ : ∀ c, σ (σ c) = c := h.bar_bar
  have hσε : ∀ k, σ (ε k) = ε k := fun k => by rcases hε k with he | he <;> simp [he]
  have hεε : ∀ k, ε k * ε k = 1 := fun k => mul_self_eq_one_iff.2 (hε k)
  have hπs : Function.Surjective π := Finite.injective_iff_surjective.1 hπ
  have hperp : ∀ k l, k ≠ l → herm σ (b (π k)) (b (π l)) = 0 := by
    intro k l hkl
    have hπkl : π l ≠ π k := fun e => hkl (hπ e).symm
    have h1 := herm_mulVec σ (R k) (b (π k)) (b (π l))
    rw [hunit k, one_mulVec, hev k (π k), hev k (π l)] at h1
    simp only [ite_true, hπkl, ite_false, herm_smul_left, herm_smul_right] at h1
    have e1 : σ (ε k * -1) = -ε k := by rw [map_mul, hσε, map_neg, map_one, mul_neg_one]
    rw [e1] at h1
    have h3 : (2 : F) * herm σ (b (π k)) (b (π l)) = 0 := by
      linear_combination (-1 : F) * h1 - herm σ (b (π k)) (b (π l)) * hεε k
    exact (mul_eq_zero.1 h3).resolve_left h2
  have hnz : ∀ k, herm σ (b (π k)) (b (π k)) ≠ 0 := by
    intro k hk
    have hall : ∀ m, herm σ (b (π k)) (b m) = 0 := by
      intro m
      obtain ⟨l, rfl⟩ := hπs m
      by_cases hkl : k = l
      · subst hkl; exact hk
      · exact hperp k l hkl
    have hz : hermL σ (b (π k)) = 0 := b.ext fun m => by simpa using hall m
    have hz' : b (π k) = 0 := eq_zero_of_herm σ fun y => by
      have := LinearMap.congr_fun hz y
      simpa using this
    exact b.ne_zero _ hz'
  have hfix : ∀ k, h.bar (herm σ (b (π k)) (b (π k))) = herm σ (b (π k)) (b (π k)) :=
    fun k => herm_self_fixed σ hσσ _
  have hsc : ∀ k, ∃ c : F, herm σ (c • b (π k)) (c • b (π k)) = 1 := by
    intro k
    obtain ⟨c, hc⟩ := h.normHom_surjective ⟨(herm σ (b (π k)) (b (π k)))⁻¹, by
      rw [UnitaryFieldData.mem_fixedField, map_inv₀, hfix k]⟩
    refine ⟨c, ?_⟩
    have hc' : h.bar c * c = (herm σ (b (π k)) (b (π k)))⁻¹ := by
      have := congrArg Subtype.val hc
      rw [UnitaryFieldData.coe_normHom, UnitaryFieldData.norm] at this
      rw [mul_comm, this]
    rw [herm_smul_left, herm_smul_right, ← mul_assoc]
    change h.bar c * c * herm σ (b (π k)) (b (π k)) = 1
    rw [hc', inv_mul_cancel₀ (hnz k)]
  choose c hc using hsc
  let w : Fin 4 → (Fin 4 → F) := fun k => c k • b (π k)
  have hw : ∀ k l, herm σ (w k) (w l) = if k = l then 1 else 0 := by
    intro k l
    by_cases hkl : k = l
    · subst hkl
      calc herm σ (w k) (w k) = 1 := hc k
        _ = if k = k then 1 else 0 := by simp
    · calc herm σ (w k) (w l) = 0 := by
            change herm σ (c k • b (π k)) (c l • b (π l)) = 0
            rw [herm_smul_left, herm_smul_right, hperp k l hkl, mul_zero, mul_zero]
        _ = if k = l then 1 else 0 := by simp [hkl]
  let P : Matrix (Fin 4) (Fin 4) F := Matrix.of fun i k => w k i
  have hP : conjTr σ P * P = 1 := by
    ext a b'
    have : (conjTr σ P * P) a b' = herm σ (w a) (w b') := by
      simp [conjTr, Matrix.mul_apply, herm, P]
    rw [this, hw, Matrix.one_apply]
  have hRw : ∀ j k, R j *ᵥ w k = (ε j * if k = j then -1 else 1) • w k := by
    intro j k
    change R j *ᵥ (c k • b (π k)) = _
    rw [Matrix.mulVec_smul, hev j (π k)]
    simp only [hπ.eq_iff]
    rw [smul_comm]
  have hRP : ∀ j, R j * P = P * Matrix.diagonal (fun k => ε j * if k = j then -1 else 1) := by
    intro j
    ext i k
    have h1 : (R j * P) i k = (R j *ᵥ w k) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, P]
    rw [h1, hRw j k, Matrix.mul_diagonal, Pi.smul_apply, smul_eq_mul, mul_comm]
    rfl
  refine ⟨P, hP, fun j => ?_⟩
  rw [Matrix.mul_assoc, hRP j, ← Matrix.mul_assoc, hP, Matrix.one_mul]
  ext a b'
  by_cases hab : a = b'
  · subst hab; simp [reflDiagMat]
  · simp [reflDiagMat, hab]

end CFSG.GH74.Generic.S1.SymDiagUni

namespace CFSG.GH74.Generic.S1

open Matrix CFSG.LieType.Universal.Unitary

theorem exists_diag_frame_uni {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2)
    (hq : q % 4 = 1) (ρ : Fin 4 → GL (Fin 4) F) (hρ2 : ∀ j, ρ j * ρ j = 1)
    (hdet : ∀ j, ((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = -1)
    (hunit : ∀ j, (((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map (fun x : F => x ^ q))ᵀ *
      ((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1)
    (hcomm : ∀ j k, ∃ c : F, ((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((ρ k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      c • (((ρ k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        ((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)))
    (hne : ∀ j k, j ≠ k → ∀ c : F, ((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) ≠
      c • ((ρ k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) :
    ∃ (P : GL (Fin 4) F) (ε : Fin 4 → F), (∀ j, ε j = 1 ∨ ε j = -1) ∧
      (((P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map (fun x : F => x ^ q))ᵀ *
        ((P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 ∧
      ∀ j, ((P⁻¹ * ρ j * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        ε j • ((reflDiag F j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  obtain ⟨p, f, h, rfl, hp2⟩ := FrameUni.exists_unitaryFieldData hF hq
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP F p := h.charP
  have hchar : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  obtain ⟨b, ε, π, hε, hπ, hev⟩ := SymDiagUni.exists_pattern hchar ρ hρ2 hdet hcomm hne
  have hunit' : ∀ j, conjTr (FrameUni.frameBar h) ((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := hunit
  obtain ⟨P, hP, hPj⟩ := SymDiagUni.exists_unitary_frame_matrix h hp2
    (fun j => ((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) hunit' b ε π hε hπ hev
  have hPP : P * conjTr (FrameUni.frameBar h) P = 1 := mul_eq_one_comm.1 hP
  let Pg : GL (Fin 4) F := ⟨P, conjTr (FrameUni.frameBar h) P, hPP, hP⟩
  refine ⟨Pg, ε, hε, hP, fun j => ?_⟩
  have hinv : ((Pg⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = conjTr (FrameUni.frameBar h) P :=
    rfl
  rw [Units.val_mul, Units.val_mul, hinv]
  exact hPj j

end CFSG.GH74.Generic.S1
