module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM12Gl
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFM12

open Matrix CFSG.Open

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2]

theorem frob_eq : (⇑(iterateFrobenius F 2 2 : F →+* F)) = fun y : F => y ^ 2 ^ 2 := by
  funext a
  rfl

theorem Sm_map_frob (d : Fin 6 → F) (l₀ : F) :
    (Sm d l₀).map (iterateFrobenius F 2 2 : F →+* F) = Sm d l₀ := by
  ext k i
  simp only [Matrix.map_apply, Sm]
  split_ifs <;> simp

theorem eigP_map_frob (d : Fin 6 → F) (l₀ : F) :
    (eigP d l₀).map (iterateFrobenius F 2 2 : F →+* F) = eigP d l₀ := by
  rw [frob_eq]
  exact eigP_map d l₀

theorem mem_SU_iff_n {n : ℕ} (hF : Nat.card F = (2 ^ 2) ^ 2) (hn : 1 ≤ n) (A : GL (Fin n) F) :
    A ∈ StatedSU n (2 ^ 2) F ↔ (A : Matrix (Fin n) (Fin n) F).det = 1 ∧
      (((A : Matrix (Fin n) (Fin n) F)).map (iterateFrobenius F 2 2 : F →+* F))ᵀ *
        (A : Matrix (Fin n) (Fin n) F) = 1 := by
  have h := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hF (n := n) hn).1
  exact Set.ext_iff.1 h A

theorem Smt_mul_one_sub (d : Fin 6 → F) (l₀ : F) :
    (Sm d l₀)ᵀ * (1 - eigP d l₀) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, Smt_mul_eigP, sub_self]

theorem one_sub_mul_Sm (d : Fin 6 → F) (l₀ : F) :
    (1 - eigP d l₀) * Sm d l₀ = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, eigP_mul_Sm, sub_self]

theorem block_unitary (d : Fin 6 → F) (l₀ : F)
    {X : Matrix (Fin (Eset d l₀).card) (Fin (Eset d l₀).card) F}
    (hX : (X.map (iterateFrobenius F 2 2 : F →+* F))ᵀ * X = 1) :
    ((Sm d l₀ * X * (Sm d l₀)ᵀ + (1 - eigP d l₀)).map (iterateFrobenius F 2 2 : F →+* F))ᵀ *
      (Sm d l₀ * X * (Sm d l₀)ᵀ + (1 - eigP d l₀)) = 1 := by
  set φ : F →+* F := iterateFrobenius F 2 2 with hφ
  have hY : (Sm d l₀ * X * (Sm d l₀)ᵀ + (1 - eigP d l₀)).map φ =
      Sm d l₀ * X.map φ * (Sm d l₀)ᵀ + (1 - eigP d l₀) := by
    rw [Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub φ),
      Matrix.map_one _ (map_zero φ) (map_one φ), eigP_map_frob, Matrix.transpose_map, Sm_map_frob]
  rw [hY]
  have hYt : (Sm d l₀ * X.map φ * (Sm d l₀)ᵀ + (1 - eigP d l₀))ᵀ =
      Sm d l₀ * (X.map φ)ᵀ * (Sm d l₀)ᵀ + (1 - eigP d l₀) := by
    simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_sub,
      Matrix.transpose_one, eigP_transpose, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [hYt]
  have t1 : Sm d l₀ * (X.map φ)ᵀ * (Sm d l₀)ᵀ * (Sm d l₀ * X * (Sm d l₀)ᵀ) = eigP d l₀ := by
    calc Sm d l₀ * (X.map φ)ᵀ * (Sm d l₀)ᵀ * (Sm d l₀ * X * (Sm d l₀)ᵀ)
        = Sm d l₀ * ((X.map φ)ᵀ * ((Sm d l₀)ᵀ * Sm d l₀) * X) * (Sm d l₀)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = Sm d l₀ * ((X.map φ)ᵀ * X) * (Sm d l₀)ᵀ := by
          rw [Sm_transpose_mul_Sm, Matrix.mul_one]
      _ = Sm d l₀ * (Sm d l₀)ᵀ := by
          rw [hX, Matrix.mul_one]
      _ = eigP d l₀ := Sm_mul_transpose_eq d l₀
  have t2 : Sm d l₀ * (X.map φ)ᵀ * (Sm d l₀)ᵀ * (1 - eigP d l₀) = 0 := by
    calc Sm d l₀ * (X.map φ)ᵀ * (Sm d l₀)ᵀ * (1 - eigP d l₀)
        = Sm d l₀ * (X.map φ)ᵀ * ((Sm d l₀)ᵀ * (1 - eigP d l₀)) := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [Smt_mul_one_sub, Matrix.mul_zero]
  have t3 : (1 - eigP d l₀) * (Sm d l₀ * X * (Sm d l₀)ᵀ) = 0 := by
    calc (1 - eigP d l₀) * (Sm d l₀ * X * (Sm d l₀)ᵀ)
        = ((1 - eigP d l₀) * Sm d l₀) * X * (Sm d l₀)ᵀ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [one_sub_mul_Sm, Matrix.zero_mul, Matrix.zero_mul]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, t1, t2, t3, one_sub_mul_one_sub]
  simp

@[expose] def Mblk (d : Fin 6 → F) (l₀ : F)
    (X : Matrix (Fin (Eset d l₀).card) (Fin (Eset d l₀).card) F) : Matrix (Fin 6) (Fin 6) F :=
  Sm d l₀ * X * (Sm d l₀)ᵀ + (1 - eigP d l₀)

theorem d_emb (d : Fin 6 → F) (l₀ : F) (i : Fin (Eset d l₀).card) : d (emb d l₀ i) = l₀ :=
  (mem_range_emb_iff d l₀ _).1 ⟨i, rfl⟩

theorem Sm_emb (d : Fin 6 → F) (l₀ : F) (i a : Fin (Eset d l₀).card) :
    Sm d l₀ (emb d l₀ i) a = if i = a then 1 else 0 := by
  simp [Sm, (emb d l₀).injective.eq_iff]

theorem Sm_off {d : Fin 6 → F} {l₀ : F} {k : Fin 6} (hk : ¬ d k = l₀) (a : Fin (Eset d l₀).card) :
    Sm d l₀ k a = 0 := by
  simp only [Sm]
  rw [if_neg]
  intro h
  exact hk ((mem_range_emb_iff d l₀ k).1 ⟨a, h.symm⟩)

theorem SAS_emb (d : Fin 6 → F) (l₀ : F) (X : Matrix (Fin (Eset d l₀).card) (Fin (Eset d l₀).card) F)
    (i j : Fin (Eset d l₀).card) :
    (Sm d l₀ * X * (Sm d l₀)ᵀ) (emb d l₀ i) (emb d l₀ j) = X i j := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, Sm_emb, Finset.sum_ite_eq']

theorem SAS_off {d : Fin 6 → F} {l₀ : F} (X : Matrix (Fin (Eset d l₀).card) (Fin (Eset d l₀).card) F)
    {k k' : Fin 6} (hk : ¬ d k = l₀) : (Sm d l₀ * X * (Sm d l₀)ᵀ) k k' = 0 := by
  simp only [Matrix.mul_apply, Sm_off hk, zero_mul, Finset.sum_const_zero]

theorem det_block (d : Fin 6 → F) (l₀ : F)
    (X : Matrix (Fin (Eset d l₀).card) (Fin (Eset d l₀).card) F) :
    (Mblk d l₀ X).det = X.det := by
  classical
  let ε : Fin (Eset d l₀).card ⊕ {k : Fin 6 // ¬ d k = l₀} ≃ Fin 6 :=
    Equiv.ofBijective (Sum.elim (emb d l₀) Subtype.val) (by
      constructor
      · rintro (i | k) (j | l) h
        · exact congrArg Sum.inl ((emb d l₀).injective h)
        · exfalso
          have h' : emb d l₀ i = l.1 := h
          exact l.2 (h' ▸ d_emb d l₀ i)
        · exfalso
          have h' : k.1 = emb d l₀ j := h
          exact k.2 (h' ▸ d_emb d l₀ j)
        · exact congrArg Sum.inr (Subtype.ext h)
      · intro k
        by_cases hk : d k = l₀
        · obtain ⟨i, hi⟩ : k ∈ Set.range (emb d l₀) := (mem_range_emb_iff d l₀ k).2 hk
          exact ⟨Sum.inl i, hi⟩
        · exact ⟨Sum.inr ⟨k, hk⟩, rfl⟩)
  have hM21 : ∀ (k : {k : Fin 6 // ¬ d k = l₀}) (j : Fin (Eset d l₀).card),
      Mblk d l₀ X k.1 (emb d l₀ j) = 0 := by
    intro k j
    have hne : k.1 ≠ emb d l₀ j := fun h => k.2 (h ▸ d_emb d l₀ j)
    simp [Mblk, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, eigP, Matrix.diagonal_apply,
      SAS_off X k.2, hne]
  have hcomp : ∀ k l : {k : Fin 6 // ¬ d k = l₀},
      Mblk d l₀ X k.1 l.1 = if k = l then 1 else 0 := by
    intro k l
    have hkl : k.1 = l.1 ↔ k = l := Subtype.ext_iff.symm
    simp [Mblk, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, eigP, Matrix.diagonal_apply,
      SAS_off X k.2, k.2, hkl]
  have hemb : ∀ i j : Fin (Eset d l₀).card, Mblk d l₀ X (emb d l₀ i) (emb d l₀ j) = X i j := by
    intro i j
    simp [Mblk, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, eigP, Matrix.diagonal_apply,
      SAS_emb, d_emb]
  have hN : (Mblk d l₀ X).submatrix ε ε =
      Matrix.fromBlocks X
        (Matrix.of fun (i : Fin (Eset d l₀).card) (k : {k : Fin 6 // ¬ d k = l₀}) =>
          Mblk d l₀ X (emb d l₀ i) k.1)
        0 (Matrix.of fun (k l : {k : Fin 6 // ¬ d k = l₀}) => if k = l then (1 : F) else 0) := by
    ext x y
    rcases x with i | k <;> rcases y with j | l
    · exact hemb i j
    · rfl
    · exact hM21 k j
    · exact hcomp k l
  have hD : (Matrix.of fun (k l : {k : Fin 6 // ¬ d k = l₀}) => if k = l then (1 : F) else 0) = 1 := by
    ext k l
    simp [Matrix.one_apply]
  rw [← Matrix.det_submatrix_equiv_self ε, hN, Matrix.det_fromBlocks_zero₂₁, hD, Matrix.det_one,
    mul_one]

theorem Mblk_mul (d : Fin 6 → F) (l₀ : F)
    (X Z : Matrix (Fin (Eset d l₀).card) (Fin (Eset d l₀).card) F) :
    Mblk d l₀ X * Mblk d l₀ Z = Mblk d l₀ (X * Z) := by
  unfold Mblk
  have hQS : (1 - eigP d l₀) * Sm d l₀ = 0 := one_sub_mul_Sm d l₀
  have e1 : Sm d l₀ * X * (Sm d l₀)ᵀ * (Sm d l₀ * Z * (Sm d l₀)ᵀ) = Sm d l₀ * (X * Z) * (Sm d l₀)ᵀ := by
    calc Sm d l₀ * X * (Sm d l₀)ᵀ * (Sm d l₀ * Z * (Sm d l₀)ᵀ)
        = Sm d l₀ * (X * ((Sm d l₀)ᵀ * Sm d l₀) * Z) * (Sm d l₀)ᵀ := by simp only [Matrix.mul_assoc]
      _ = Sm d l₀ * (X * Z) * (Sm d l₀)ᵀ := by rw [Sm_transpose_mul_Sm, Matrix.mul_one]
  have e2 : Sm d l₀ * X * (Sm d l₀)ᵀ * (1 - eigP d l₀) = 0 := by
    calc Sm d l₀ * X * (Sm d l₀)ᵀ * (1 - eigP d l₀)
        = Sm d l₀ * X * ((Sm d l₀)ᵀ * (1 - eigP d l₀)) := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [Smt_mul_one_sub, Matrix.mul_zero]
  have e3 : (1 - eigP d l₀) * (Sm d l₀ * Z * (Sm d l₀)ᵀ) = 0 := by
    calc (1 - eigP d l₀) * (Sm d l₀ * Z * (Sm d l₀)ᵀ)
        = ((1 - eigP d l₀) * Sm d l₀) * Z * (Sm d l₀)ᵀ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hQS, Matrix.zero_mul, Matrix.zero_mul]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, e1, e2, e3, one_sub_mul_one_sub]
  simp [add_assoc]

theorem Mblk_one (d : Fin 6 → F) (l₀ : F) : Mblk d l₀ 1 = 1 := by
  unfold Mblk
  rw [Matrix.mul_one, Sm_mul_transpose_eq, add_sub_cancel]

theorem Mblk_comm_P (d : Fin 6 → F) (l₀ : F) (X : Matrix (Fin (Eset d l₀).card) (Fin (Eset d l₀).card) F) :
    Mblk d l₀ X * eigP d l₀ = eigP d l₀ * Mblk d l₀ X := by
  unfold Mblk
  have h1 : (Sm d l₀ * X * (Sm d l₀)ᵀ + (1 - eigP d l₀)) * eigP d l₀ = Sm d l₀ * X * (Sm d l₀)ᵀ := by
    rw [Matrix.add_mul, one_sub_mul_eigP, add_zero, Matrix.mul_assoc, Smt_mul_eigP]
  have h2 : eigP d l₀ * (Sm d l₀ * X * (Sm d l₀)ᵀ + (1 - eigP d l₀)) = Sm d l₀ * X * (Sm d l₀)ᵀ := by
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, eigP_mul_Sm, eigP_mul_one_sub,
      add_zero]
  rw [h1, h2]

theorem Mblk_mul_one_sub (d : Fin 6 → F) (l₀ : F) (X : Matrix (Fin (Eset d l₀).card) (Fin (Eset d l₀).card) F) :
    Mblk d l₀ X * (1 - eigP d l₀) = 1 - eigP d l₀ := by
  unfold Mblk
  rw [Matrix.add_mul, Matrix.mul_assoc, Smt_mul_one_sub, Matrix.mul_zero, zero_add,
    one_sub_mul_one_sub]

theorem Smt_Mblk (d : Fin 6 → F) (l₀ : F) (X : Matrix (Fin (Eset d l₀).card) (Fin (Eset d l₀).card) F) :
    (Sm d l₀)ᵀ * Mblk d l₀ X * Sm d l₀ = X := by
  unfold Mblk
  rw [Matrix.mul_add, Matrix.add_mul]
  have h1 : (Sm d l₀)ᵀ * (Sm d l₀ * X * (Sm d l₀)ᵀ) * Sm d l₀ = X := by
    calc (Sm d l₀)ᵀ * (Sm d l₀ * X * (Sm d l₀)ᵀ) * Sm d l₀
        = ((Sm d l₀)ᵀ * Sm d l₀) * X * ((Sm d l₀)ᵀ * Sm d l₀) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [Sm_transpose_mul_Sm, Matrix.one_mul, Matrix.mul_one]
  have h2 : (Sm d l₀)ᵀ * (1 - eigP d l₀) * Sm d l₀ = 0 := by
    rw [Smt_mul_one_sub, Matrix.zero_mul]
  rw [h1, h2, add_zero]

theorem block_form {d : Fin 6 → F} {l₀ : F} {g : Matrix (Fin 6) (Fin 6) F}
    (hg : g * eigP d l₀ = eigP d l₀ * g) (hQ : g * (1 - eigP d l₀) = 1 - eigP d l₀) :
    Mblk d l₀ ((Sm d l₀)ᵀ * g * Sm d l₀) = g := by
  unfold Mblk
  have h1 : Sm d l₀ * ((Sm d l₀)ᵀ * g * Sm d l₀) * (Sm d l₀)ᵀ = eigP d l₀ * g * eigP d l₀ := by
    rw [← Sm_mul_transpose_eq]
    simp only [Matrix.mul_assoc]
  rw [h1, comm_proj hg, ← hQ, ← Matrix.mul_add, add_sub_cancel, Matrix.mul_one]

theorem rhoX_unitary {d : Fin 6 → F} {l₀ : F} {g : Matrix (Fin 6) (Fin 6) F}
    (hg : g * eigP d l₀ = eigP d l₀ * g)
    (hU : (g.map (iterateFrobenius F 2 2 : F →+* F))ᵀ * g = 1) :
    (((Sm d l₀)ᵀ * g * Sm d l₀).map (iterateFrobenius F 2 2 : F →+* F))ᵀ *
      ((Sm d l₀)ᵀ * g * Sm d l₀) = 1 := by
  have hmap : (((Sm d l₀)ᵀ * g * Sm d l₀).map (iterateFrobenius F 2 2 : F →+* F)) =
      (Sm d l₀)ᵀ * g.map (iterateFrobenius F 2 2 : F →+* F) * Sm d l₀ := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Sm_map_frob]
  rw [hmap]
  have ht : ((Sm d l₀)ᵀ * g.map (iterateFrobenius F 2 2 : F →+* F) * Sm d l₀)ᵀ =
      (Sm d l₀)ᵀ * (g.map (iterateFrobenius F 2 2 : F →+* F))ᵀ * Sm d l₀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [ht]
  calc (Sm d l₀)ᵀ * (g.map (iterateFrobenius F 2 2 : F →+* F))ᵀ * Sm d l₀ * ((Sm d l₀)ᵀ * g * Sm d l₀)
      = (Sm d l₀)ᵀ * ((g.map (iterateFrobenius F 2 2 : F →+* F))ᵀ * (Sm d l₀ * (Sm d l₀)ᵀ) * g) *
          Sm d l₀ := by simp only [Matrix.mul_assoc]
    _ = (Sm d l₀)ᵀ * ((g.map (iterateFrobenius F 2 2 : F →+* F))ᵀ * eigP d l₀ * g) * Sm d l₀ := by
        rw [Sm_mul_transpose_eq]
    _ = (Sm d l₀)ᵀ * ((g.map (iterateFrobenius F 2 2 : F →+* F))ᵀ * (eigP d l₀ * g)) * Sm d l₀ := by
        simp only [Matrix.mul_assoc]
    _ = (Sm d l₀)ᵀ * ((g.map (iterateFrobenius F 2 2 : F →+* F))ᵀ * (g * eigP d l₀)) * Sm d l₀ := by
        rw [← hg]
    _ = (Sm d l₀)ᵀ * (((g.map (iterateFrobenius F 2 2 : F →+* F))ᵀ * g) * eigP d l₀) * Sm d l₀ := by
        simp only [Matrix.mul_assoc]
    _ = (Sm d l₀)ᵀ * ((g.map (iterateFrobenius F 2 2 : F →+* F))ᵀ * g) * (eigP d l₀ * Sm d l₀) := by
        simp only [Matrix.mul_assoc]
    _ = (Sm d l₀)ᵀ * ((g.map (iterateFrobenius F 2 2 : F →+* F))ᵀ * g) * Sm d l₀ := by
        rw [eigP_mul_Sm]
    _ = (Sm d l₀)ᵀ * (1 : Matrix (Fin 6) (Fin 6) F) * Sm d l₀ := by rw [hU]
    _ = (Sm d l₀)ᵀ * Sm d l₀ := by rw [Matrix.mul_one]
    _ = 1 := Sm_transpose_mul_Sm d l₀

theorem rhoU_mem_SU {d : Fin 6 → F} {l₀ : F} (hF : Nat.card F = (2 ^ 2) ^ 2)
    (ha : 3 ≤ (Eset d l₀).card) (h : ↥(Ug d l₀)) :
    rhoU d l₀ h.1.1 ∈ StatedSU (Eset d l₀).card (2 ^ 2) F := by
  have hg : (h.1.1 : Matrix (Fin 6) (Fin 6) F) * eigP d l₀ = eigP d l₀ * h.1.1 := h.2.1 l₀
  have hQ : (h.1.1 : Matrix (Fin 6) (Fin 6) F) * (1 - eigP d l₀) = 1 - eigP d l₀ := h.2.2
  obtain ⟨hdet, hunit⟩ := (mem_SU_iff hF h.1.1).1 h.1.2
  have hX : ((Sm d l₀)ᵀ * (h.1.1 : Matrix (Fin 6) (Fin 6) F) * Sm d l₀).det = 1 := by
    rw [← det_block, block_form hg hQ]
    exact hdet
  rw [mem_SU_iff_n hF (by omega)]
  refine ⟨?_, ?_⟩
  · rw [rhoU_val hg]
    exact hX
  · rw [rhoU_val hg]
    exact rhoX_unitary hg hunit

@[expose] def rhoSU (d : Fin 6 → F) (l₀ : F) (hF : Nat.card F = (2 ^ 2) ^ 2)
    (ha : 3 ≤ (Eset d l₀).card) : ↥(Ug d l₀) →* ↥(StatedSU (Eset d l₀).card (2 ^ 2) F) where
  toFun h := ⟨rhoU d l₀ h.1.1, rhoU_mem_SU hF ha h⟩
  map_one' := Subtype.ext ((rhoHom d l₀).map_one)
  map_mul' := fun h k => Subtype.ext ((rhoHom d l₀).map_mul h k)

theorem rhoSU_injective (d : Fin 6 → F) (l₀ : F) (hF : Nat.card F = (2 ^ 2) ^ 2)
    (ha : 3 ≤ (Eset d l₀).card) : Function.Injective (rhoSU d l₀ hF ha) := by
  intro x y h
  exact rhoHom_injective d l₀ (congrArg Subtype.val h)

theorem eigP_mul_Sm_ne {d : Fin 6 → F} {l₀ m : F} (hm : m ≠ l₀) :
    eigP d m * Sm d l₀ = 0 := by
  ext k i
  rw [Matrix.zero_apply, eigP, Matrix.diagonal_mul]
  by_cases hk : d k = m
  · have hne : k ≠ emb d l₀ i := fun h => hm (by rw [← hk, h, d_emb d l₀ i])
    simp [Sm, hne]
  · simp [hk]

theorem Mblk_comm_eigP (d : Fin 6 → F) (l₀ m : F)
    (X : Matrix (Fin (Eset d l₀).card) (Fin (Eset d l₀).card) F) :
    Mblk d l₀ X * eigP d m = eigP d m * Mblk d l₀ X := by
  by_cases hm : m = l₀
  · rw [hm]
    exact Mblk_comm_P d l₀ X
  · have h1 : eigP d m * Sm d l₀ = 0 := eigP_mul_Sm_ne hm
    have h2 : (Sm d l₀)ᵀ * eigP d m = 0 := by
      have := congrArg Matrix.transpose h1
      rw [Matrix.transpose_mul, eigP_transpose, Matrix.transpose_zero] at this
      exact this
    have h3 : eigP d l₀ * eigP d m = 0 := eigP_mul_ne d (Ne.symm hm)
    have h4 : eigP d m * eigP d l₀ = 0 := eigP_mul_ne d hm
    have hL : Mblk d l₀ X * eigP d m = eigP d m := by
      unfold Mblk
      rw [Matrix.add_mul, Matrix.mul_assoc, h2, Matrix.mul_zero, zero_add, Matrix.sub_mul,
        Matrix.one_mul, h3, sub_zero]
    have hR : eigP d m * Mblk d l₀ X = eigP d m := by
      unfold Mblk
      rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.zero_mul,
        Matrix.zero_mul, zero_add, Matrix.mul_sub, Matrix.mul_one, h4, sub_zero]
    rw [hL, hR]

theorem rhoSU_surjective (d : Fin 6 → F) (l₀ : F) (hF : Nat.card F = (2 ^ 2) ^ 2)
    (ha : 3 ≤ (Eset d l₀).card) : Function.Surjective (rhoSU d l₀ hF ha) := by
  intro A
  obtain ⟨hdetA, hunitA⟩ := (mem_SU_iff_n hF (by omega) (A.1 : GL (Fin (Eset d l₀).card) F)).1 A.2
  let Y : GL (Fin 6) F :=
    Units.mk (Mblk d l₀ ((A.1 : GL (Fin (Eset d l₀).card) F) : Matrix _ _ F))
      (Mblk d l₀ (((A.1⁻¹ : GL (Fin (Eset d l₀).card) F)) : Matrix _ _ F))
      (by rw [Mblk_mul, Units.mul_inv, Mblk_one])
      (by rw [Mblk_mul, Units.inv_mul, Mblk_one])
  have hYval : (Y : Matrix (Fin 6) (Fin 6) F) =
      Mblk d l₀ ((A.1 : GL (Fin (Eset d l₀).card) F) : Matrix _ _ F) := rfl
  have hYSU : Y ∈ StatedSU 6 (2 ^ 2) F := by
    rw [mem_SU_iff hF]
    refine ⟨?_, ?_⟩
    · rw [hYval, det_block, hdetA]
    · rw [hYval]
      exact block_unitary d l₀ hunitA
  have hYcomm : ∀ m, (Y : Matrix (Fin 6) (Fin 6) F) * eigP d m = eigP d m * (Y : Matrix (Fin 6) (Fin 6) F) :=
    fun m => by rw [hYval]; exact Mblk_comm_eigP d l₀ m _
  have hYQ : (Y : Matrix (Fin 6) (Fin 6) F) * (1 - eigP d l₀) = 1 - eigP d l₀ := by
    rw [hYval]; exact Mblk_mul_one_sub d l₀ _
  refine ⟨⟨⟨Y, hYSU⟩, ⟨hYcomm, hYQ⟩⟩, ?_⟩
  apply Subtype.ext
  show rhoU d l₀ Y = A.1
  apply Units.ext
  rw [rhoU_val (hYcomm l₀), hYval, Smt_Mblk]

noncomputable def ugEquivSU (d : Fin 6 → F) (l₀ : F) (hF : Nat.card F = (2 ^ 2) ^ 2)
    (ha : 3 ≤ (Eset d l₀).card) : ↥(Ug d l₀) ≃* ↥(StatedSU (Eset d l₀).card (2 ^ 2) F) :=
  MulEquiv.ofBijective (rhoSU d l₀ hF ha)
    ⟨rhoSU_injective d l₀ hF ha, rhoSU_surjective d l₀ hF ha⟩

theorem isQuasisimple_Ug [Finite F] (d : Fin 6 → F) (l₀ : F) (hF : Nat.card F = (2 ^ 2) ^ 2)
    (ha : 3 ≤ (Eset d l₀).card) : CFSG.Open.IsQuasisimple ↥(Ug d l₀) := by
  have hnq : ((Eset d l₀).card, 2 ^ 2) ≠ (3, 2) := by
    intro h
    have := congrArg Prod.snd h
    norm_num at this
  have hq := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := 2)
    (n := (Eset d l₀).card) hF ha hnq).1
  have hq' : CFSG.Open.IsQuasisimple (StatedSU (Eset d l₀).card (2 ^ 2) F) :=
    ⟨hq.1.commutator_eq_top, hq.2.1⟩
  exact hq'.of_mulEquiv (ugEquivSU d l₀ hF ha)

end CFSG.LocalAnalysis.GLTheoremA.SFM12



