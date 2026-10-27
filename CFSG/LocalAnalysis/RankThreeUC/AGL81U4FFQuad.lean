module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFLinAlg
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFDescent
public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary Matrix

section Adjoint

variable {F : Type} [Field F]

theorem qd_herm_mulVec_left {n : ℕ} (σ : F ≃+* F) (A : Matrix (Fin n) (Fin n) F)
    (x y : Fin n → F) :
    herm σ (A *ᵥ x) y = herm σ x (conjTr σ A *ᵥ y) := by
  simp only [herm, mulVec, dotProduct, conjTr, transpose_apply, map_apply, map_sum, map_mul,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem qd_conjTr_smul {n : ℕ} (σ : F ≃+* F) (c : F) (A : Matrix (Fin n) (Fin n) F) :
    conjTr σ (c • A) = σ c • conjTr σ A := by
  ext i j
  simp [conjTr]

theorem qd_conjTr_conjTr {n : ℕ} (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c)
    (A : Matrix (Fin n) (Fin n) F) : conjTr σ (conjTr σ A) = A := by
  ext i j
  simp [conjTr, hσ]

theorem qd_conjTr_eq_self {n : ℕ} (σ : F ≃+* F) {M : Matrix (Fin n) (Fin n) F}
    (h1 : conjTr σ M * M = 1) (h2 : M * M = 1) : conjTr σ M = M := by
  calc conjTr σ M = conjTr σ M * (M * M) := by rw [h2, mul_one]
    _ = (conjTr σ M * M) * M := by rw [mul_assoc]
    _ = M := by rw [h1, one_mul]

theorem mem_sesqPerp_iff {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}
    {W : Submodule K (Fin n → K)} {x : Fin n → K} :
    x ∈ sesqPerp σ W ↔ ∀ w ∈ W, herm σ w x = 0 :=
  Iff.rfl

@[expose] def qdAdj {n : ℕ} (σ : F ≃+* F) (φ : (Fin n → F) →ₗ[F] (Fin n → F)) :
    (Fin n → F) →ₗ[F] (Fin n → F) :=
  Matrix.toLin' (conjTr σ (LinearMap.toMatrix' φ))

theorem qdAdj_apply {n : ℕ} (σ : F ≃+* F) (φ : (Fin n → F) →ₗ[F] (Fin n → F)) (y : Fin n → F) :
    qdAdj σ φ y = conjTr σ (LinearMap.toMatrix' φ) *ᵥ y := by
  rw [qdAdj, Matrix.toLin'_apply]

theorem qdAdj_add {n : ℕ} (σ : F ≃+* F) (φ ψ : (Fin n → F) →ₗ[F] (Fin n → F)) :
    qdAdj σ (φ + ψ) = qdAdj σ φ + qdAdj σ ψ := by
  simp only [qdAdj, map_add, conjTr_add]

theorem qdAdj_smul {n : ℕ} (σ : F ≃+* F) (c : F) (φ : (Fin n → F) →ₗ[F] (Fin n → F)) :
    qdAdj σ (c • φ) = σ c • qdAdj σ φ := by
  simp only [qdAdj, map_smul, qd_conjTr_smul]

theorem qdAdj_qdAdj {n : ℕ} (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c)
    (φ : (Fin n → F) →ₗ[F] (Fin n → F)) : qdAdj σ (qdAdj σ φ) = φ := by
  simp only [qdAdj, LinearMap.toMatrix'_toLin', qd_conjTr_conjTr σ hσ, Matrix.toLin'_toMatrix']

theorem qdAdj_herm {n : ℕ} (σ : F ≃+* F) (φ : (Fin n → F) →ₗ[F] (Fin n → F)) (x y : Fin n → F) :
    herm σ (φ x) y = herm σ x (qdAdj σ φ y) := by
  rw [← LinearMap.toMatrix'_mulVec φ x, qdAdj_apply, qd_herm_mulVec_left]

theorem qdAdj_toLin {n : ℕ} (σ : F ≃+* F) (M : Matrix (Fin n) (Fin n) F) :
    qdAdj σ (Matrix.toLin' M) = Matrix.toLin' (conjTr σ M) := by
  simp only [qdAdj, LinearMap.toMatrix'_toLin']

@[expose] def qdEnd {n : ℕ} (C I : Submodule F (Fin n → F)) :
    Submodule F ((Fin n → F) →ₗ[F] (Fin n → F)) where
  carrier := {φ | (∀ x ∈ C, φ x = 0) ∧ ∀ x, φ x ∈ I}
  add_mem' := by
    rintro φ ψ ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨fun x hx => by simp [h1 x hx, h3 x hx], fun x => I.add_mem (h2 x) (h4 x)⟩
  zero_mem' := ⟨fun x _ => rfl, fun x => I.zero_mem⟩
  smul_mem' := by
    rintro c φ ⟨h1, h2⟩
    exact ⟨fun x hx => by simp [h1 x hx], fun x => I.smul_mem c (h2 x)⟩

theorem mem_qdEnd {n : ℕ} {C I : Submodule F (Fin n → F)} {φ : (Fin n → F) →ₗ[F] (Fin n → F)} :
    φ ∈ qdEnd C I ↔ (∀ x ∈ C, φ x = 0) ∧ ∀ x, φ x ∈ I :=
  Iff.rfl

@[expose] def qdImage (B : Subgroup (GL (Fin 4) F)) : Submodule F (Fin 4 → F) :=
  Submodule.span F {w | ∃ b ∈ B, ∃ x : Fin 4 → F, w = ((b : Matrix (Fin 4) (Fin 4) F) - 1) *ᵥ x}

theorem qd_sub_mulVec_mem {B : Subgroup (GL (Fin 4) F)} {b : GL (Fin 4) F} (hb : b ∈ B)
    (y : Fin 4 → F) : ((b : Matrix (Fin 4) (Fin 4) F) - 1) *ᵥ y ∈ qdImage B := by
  unfold qdImage
  exact Submodule.subset_span ⟨b, hb, y, rfl⟩

end Adjoint

section Counting

theorem qd_finrank_sesqPerp_add {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {n : ℕ}
    (W : Submodule K (Fin n → K)) :
    Module.finrank K (sesqPerp σ W) + Module.finrank K W = n := by
  have h := card_sesqPerp_mul_card σ W
  rw [Module.natCard_eq_pow_finrank (K := K) (V := sesqPerp σ W),
    Module.natCard_eq_pow_finrank (K := K) (V := W), ← pow_add] at h
  have hK : 2 ≤ Nat.card K := Finite.one_lt_card
  exact Nat.pow_right_injective hK h

theorem qd_sesqPerp_sesqPerp {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hσ : ∀ c, σ (σ c) = c) {n : ℕ} (W : Submodule K (Fin n → K)) :
    sesqPerp σ (sesqPerp σ W) = W := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · intro w hw
    rw [mem_sesqPerp_iff]
    intro c hc
    exact herm_eq_zero_comm σ hσ ((mem_sesqPerp_iff.mp hc) w hw)
  · have h1 := qd_finrank_sesqPerp_add σ (sesqPerp σ W)
    have h2 := qd_finrank_sesqPerp_add σ W
    omega

end Counting

section Quad

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem qd_conjTr_of_mem {n : ℕ} {b : GL (Fin n) F} (hb : b ∈ SUid σ n) (hbb : b * b = 1) :
    conjTr σ (b : Matrix (Fin n) (Fin n) F) = (b : Matrix (Fin n) (Fin n) F) := by
  apply qd_conjTr_eq_self σ
  · exact (mem_SUid.mp hb).2
  · rw [← Units.val_mul, hbb, Units.val_one]

theorem qd_conjTr_sub_one {n : ℕ} {b : GL (Fin n) F} (hb : b ∈ SUid σ n) (hbb : b * b = 1) :
    conjTr σ ((b : Matrix (Fin n) (Fin n) F) - 1) = (b : Matrix (Fin n) (Fin n) F) - 1 := by
  rw [conjTr_sub, conjTr_one, qd_conjTr_of_mem hb hbb]

theorem qd_herm_sub_one_left {n : ℕ} {b : GL (Fin n) F} (hb : b ∈ SUid σ n) (hbb : b * b = 1)
    (y x : Fin n → F) :
    herm σ (((b : Matrix (Fin n) (Fin n) F) - 1) *ᵥ y) x =
      herm σ y (((b : Matrix (Fin n) (Fin n) F) - 1) *ᵥ x) := by
  rw [qd_herm_mulVec_left, qd_conjTr_sub_one hb hbb]

theorem qd_image_fix {B : Subgroup (GL (Fin 4) F)}
    (hquad : ∀ b ∈ B, ∀ b' ∈ B,
      ((b : Matrix (Fin 4) (Fin 4) F) - 1) * ((b' : Matrix (Fin 4) (Fin 4) F) - 1) = 0)
    {w : Fin 4 → F} (hw : w ∈ qdImage B) :
    ∀ b ∈ B, ((b : Matrix (Fin 4) (Fin 4) F) - 1) *ᵥ w = 0 := by
  unfold qdImage at hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b', hb', x, rfl⟩ := hw
    intro b hb
    rw [Matrix.mulVec_mulVec, hquad b hb b' hb', Matrix.zero_mulVec]
  | zero => intro b _; rw [Matrix.mulVec_zero]
  | add w w' _ _ h1 h2 => intro b hb; rw [Matrix.mulVec_add, h1 b hb, h2 b hb, add_zero]
  | smul c w _ h1 => intro b hb; rw [Matrix.mulVec_smul, h1 b hb, smul_zero]

theorem qd_mem_sesqPerp_image_iff (hσ : IsUnitaryInvolution σ) {B : Subgroup (GL (Fin 4) F)}
    (hBU : B ≤ SUid σ 4) (hinv : ∀ b ∈ B, b * b = 1) (x : Fin 4 → F) :
    x ∈ sesqPerp σ (qdImage B) ↔ ∀ b ∈ B, (b : Matrix (Fin 4) (Fin 4) F) *ᵥ x = x := by
  rw [mem_sesqPerp_iff]
  constructor
  · intro hx b hb
    have h0 : ((b : Matrix (Fin 4) (Fin 4) F) - 1) *ᵥ x = 0 := by
      apply eq_zero_of_herm σ
      intro y
      rw [qd_herm_mulVec_left, qd_conjTr_sub_one (hBU hb) (hinv b hb)]
      exact herm_eq_zero_comm σ hσ.invol (hx _ (qd_sub_mulVec_mem hb y))
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h0
    exact sub_eq_zero.mp h0
  · intro hfix w hw
    unfold qdImage at hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨b, hb, y, rfl⟩ := hw
      have h0 : ((b : Matrix (Fin 4) (Fin 4) F) - 1) *ᵥ x = 0 := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, hfix b hb, sub_self]
      rw [qd_herm_sub_one_left (hBU hb) (hinv b hb), h0, herm_zero_right]
    | zero => rw [herm_zero_left]
    | add w w' _ _ h1 h2 => rw [herm_add_left, h1, h2, add_zero]
    | smul c w _ h1 => rw [herm_smul_left, h1, mul_zero]

end Quad

section Descent

variable {F : Type} [Field F]

theorem qd_natCard_qdEnd [Finite F] {n : ℕ} (C I : Submodule F (Fin n → F)) :
    Nat.card ↥(qdEnd C I) = Nat.card F ^ ((n - Module.finrank F C) * Module.finrank F I) := by
  have h := card_linearMaps_vanishing_into (K := F) (N := Fin n → F) C I
  rw [Module.finrank_fin_fun] at h
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun φ => mem_qdEnd)

theorem qd_adj_mem {n : ℕ} (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c) {C I : Submodule F (Fin n → F)}
    (hC : C = sesqPerp σ I) (hI : I = sesqPerp σ C) {φ : (Fin n → F) →ₗ[F] (Fin n → F)}
    (hφ : φ ∈ qdEnd C I) : qdAdj σ φ ∈ qdEnd C I := by
  rw [mem_qdEnd] at hφ ⊢
  obtain ⟨h1, h2⟩ := hφ
  constructor
  · intro x hx
    have hxI : x ∈ sesqPerp σ I := by rw [← hC]; exact hx
    apply eq_zero_of_herm σ
    intro y
    rw [qdAdj_herm σ (qdAdj σ φ) x y, qdAdj_qdAdj σ hσ φ]
    exact herm_eq_zero_comm σ hσ (mem_sesqPerp_iff.mp hxI (φ y) (h2 y))
  · intro y
    rw [hI, mem_sesqPerp_iff]
    intro c hc
    rw [← qdAdj_herm σ φ c y, h1 c hc, herm_zero_left]

@[expose] def qdAdjE {n : ℕ} (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c) {C I : Submodule F (Fin n → F)}
    (hC : C = sesqPerp σ I) (hI : I = sesqPerp σ C) : ↥(qdEnd C I) ≃+ ↥(qdEnd C I) where
  toFun x := ⟨qdAdj σ x.1, qd_adj_mem σ hσ hC hI x.2⟩
  invFun x := ⟨qdAdj σ x.1, qd_adj_mem σ hσ hC hI x.2⟩
  left_inv x := Subtype.ext (qdAdj_qdAdj σ hσ x.1)
  right_inv x := Subtype.ext (qdAdj_qdAdj σ hσ x.1)
  map_add' x y := Subtype.ext (qdAdj_add σ x.1 y.1)

end Descent

theorem su4_quadratic_card_le {F : Type} [Field F] [Finite F] [CharP F 2] (σ : F ≃+* F)
    (hσ : IsUnitaryInvolution σ) (B : Subgroup (GL (Fin 4) F)) (hBU : B ≤ SUid σ 4)
    (hinv : ∀ b ∈ B, b * b = 1)
    (hquad : ∀ b ∈ B, ∀ b' ∈ B,
      ((b : Matrix (Fin 4) (Fin 4) F) - 1) * ((b' : Matrix (Fin 4) (Fin 4) F) - 1) = 0) :
    ∃ r : ℕ, r ≤ 2 ∧
      Nat.card {x : Fin 4 → F // ∀ b ∈ B, (b : Matrix (Fin 4) (Fin 4) F) *ᵥ x = x} =
        Nat.card F ^ (4 - r) ∧ Nat.card B ^ 2 ≤ Nat.card F ^ (r ^ 2) := by
  set I : Submodule F (Fin 4 → F) := qdImage B
  set C : Submodule F (Fin 4 → F) := sesqPerp σ I
  have hC : C = sesqPerp σ I := rfl
  have hI : I = sesqPerp σ C := (qd_sesqPerp_sesqPerp hσ.invol I).symm
  have hfix : ∀ x, x ∈ C ↔ ∀ b ∈ B, (b : Matrix (Fin 4) (Fin 4) F) *ᵥ x = x :=
    fun x => qd_mem_sesqPerp_image_iff hσ hBU hinv x
  have hIC : I ≤ C := by
    intro w hw
    rw [hfix]
    intro b hb
    have h0 := qd_image_fix hquad hw b hb
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h0
    exact sub_eq_zero.mp h0
  have hsum : Module.finrank F C + Module.finrank F I = 4 := qd_finrank_sesqPerp_add σ I
  have hle : Module.finrank F I ≤ Module.finrank F C := Submodule.finrank_mono hIC
  have hr2 : Module.finrank F I ≤ 2 := by omega
  refine ⟨Module.finrank F I, hr2, ?_, ?_⟩
  · have e : {x : Fin 4 → F // ∀ b ∈ B, (b : Matrix (Fin 4) (Fin 4) F) *ᵥ x = x} ≃ ↥C :=
      Equiv.subtypeEquivRight fun x => (hfix x).symm
    rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := F) (V := C)]
    congr 1
    omega
  ·
    have hEcard : Nat.card ↥(qdEnd C I) =
        Nat.card F ^ (Module.finrank F I * Module.finrank F I) := by
      rw [qd_natCard_qdEnd C I, show 4 - Module.finrank F C = Module.finrank F I by omega]
    have hEfin : Finite ↥(qdEnd C I) := by
      apply Nat.finite_of_card_ne_zero
      rw [hEcard]
      exact pow_ne_zero _ (Nat.card_pos (α := F)).ne'
    haveI := hEfin
    let s : ↥(qdEnd C I) ≃+ ↥(qdEnd C I) := qdAdjE σ hσ.invol hC hI
    have hs : ∀ (c : F) (x : ↥(qdEnd C I)), s (c • x) = σ c • s x :=
      fun c x => Subtype.ext (qdAdj_smul σ c x.1)
    have hss : ∀ x, s (s x) = x := fun x => Subtype.ext (qdAdj_qdAdj σ hσ.invol x.1)
    have hdesc := card_fix_sq_of_semilinear_involution (K := F) (C := ↥(qdEnd C I))
      σ.toRingHom hσ.invol hσ.exists_ne s hs hss
    have hmem : ∀ b ∈ B, Matrix.toLin' ((b : Matrix (Fin 4) (Fin 4) F) - 1) ∈ qdEnd C I := by
      intro b hb
      rw [mem_qdEnd]
      refine ⟨fun x hx => ?_, fun x => ?_⟩
      · rw [Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, (hfix x).mp hx b hb,
          sub_self]
      · rw [Matrix.toLin'_apply]
        exact qd_sub_mulVec_mem hb x
    let f : ↥B → {x : ↥(qdEnd C I) // s x = x} := fun b =>
      ⟨⟨Matrix.toLin' ((b.1 : Matrix (Fin 4) (Fin 4) F) - 1), hmem b.1 b.2⟩, by
        apply Subtype.ext
        show qdAdj σ (Matrix.toLin' ((b.1 : Matrix (Fin 4) (Fin 4) F) - 1)) =
          Matrix.toLin' ((b.1 : Matrix (Fin 4) (Fin 4) F) - 1)
        rw [qdAdj_toLin, qd_conjTr_sub_one (hBU b.2) (hinv b.1 b.2)]⟩
    have hf : Function.Injective f := by
      intro b b' h
      have h1 : Matrix.toLin' ((b.1 : Matrix (Fin 4) (Fin 4) F) - 1) =
          Matrix.toLin' ((b'.1 : Matrix (Fin 4) (Fin 4) F) - 1) :=
        congrArg (fun z : {x : ↥(qdEnd C I) // s x = x} => z.1.1) h
      have h2 : ((b.1 : Matrix (Fin 4) (Fin 4) F) - 1) =
          ((b'.1 : Matrix (Fin 4) (Fin 4) F) - 1) :=
        (LinearEquiv.injective Matrix.toLin') h1
      exact Subtype.ext (Units.ext (sub_left_inj.mp h2))
    have hcard : Nat.card ↥B ≤ Nat.card {x : ↥(qdEnd C I) // s x = x} :=
      Nat.card_le_card_of_injective f hf
    calc Nat.card ↥B ^ 2 ≤ Nat.card {x : ↥(qdEnd C I) // s x = x} ^ 2 :=
          Nat.pow_le_pow_left hcard 2
      _ = Nat.card ↥(qdEnd C I) := hdesc
      _ = Nat.card F ^ (Module.finrank F I * Module.finrank F I) := hEcard
      _ = Nat.card F ^ (Module.finrank F I ^ 2) := by rw [sq]

end CFSG.LocalAnalysis.RankThreeUC
