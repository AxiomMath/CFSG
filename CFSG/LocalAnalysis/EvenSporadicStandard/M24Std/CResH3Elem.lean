module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH2Gen
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH2Unip
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.EvenSporadicStandard.M24Std.CResH3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

@[expose] def Fmat (K : Type) [Field K] (n : ℕ) : Matrix (Fin n) (Fin 2) K :=
  Matrix.of fun i a => if i.val / 2 = a.val then 1 else 0

@[expose] def Nmat (K : Type) [Field K] (n : ℕ) (S : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin n) (Fin n) K :=
  Fmat K n * S * (Fmat K n).transpose

@[expose] def Smat (σ : K →+* K) (a d b : K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of ![![a, b], ![σ b, d]]

theorem Fmat_transpose_mul [CharP K 2] {n : ℕ} (hn : n = 4 ∨ n = 5) :
    (Fmat K n).transpose * Fmat K n = 0 := by
  rcases hn with rfl | rfl
  · ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Fmat, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero]
  · ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Fmat, Matrix.mul_apply, Fin.sum_univ_five, CharTwo.add_self_eq_zero]

theorem Nmat_add {n : ℕ} (S S' : Matrix (Fin 2) (Fin 2) K) :
    Nmat K n (S + S') = Nmat K n S + Nmat K n S' := by
  simp only [Nmat, Matrix.mul_add, Matrix.add_mul]

theorem Nmat_zero {n : ℕ} : Nmat K n (0 : Matrix (Fin 2) (Fin 2) K) = 0 := by
  simp [Nmat]

theorem Nmat_mul [CharP K 2] {n : ℕ} (hn : n = 4 ∨ n = 5) (S S' : Matrix (Fin 2) (Fin 2) K) :
    Nmat K n S * Nmat K n S' = 0 := by
  have hF := Fmat_transpose_mul (K := K) hn
  calc Nmat K n S * Nmat K n S'
      = Fmat K n * S * ((Fmat K n).transpose * Fmat K n) * S' * (Fmat K n).transpose := by
        simp only [Nmat, Matrix.mul_assoc]
    _ = 0 := by rw [hF]; simp

theorem one_add_mul_one_add [CharP K 2] {n : ℕ} (hn : n = 4 ∨ n = 5)
    (S S' : Matrix (Fin 2) (Fin 2) K) :
    (1 + Nmat K n S) * (1 + Nmat K n S') = 1 + Nmat K n (S + S') := by
  have key : ∀ X Y : Matrix (Fin n) (Fin n) K, (1 + X) * (1 + Y) = 1 + (X + Y) + X * Y :=
    fun X Y => by noncomm_ring
  rw [key, Nmat_mul hn, add_zero, Nmat_add]

theorem det_one_add_Nmat [CharP K 2] {n : ℕ} (hn : n = 4 ∨ n = 5)
    (S : Matrix (Fin 2) (Fin 2) K) : (1 + Nmat K n S).det = 1 := by
  have hF := Fmat_transpose_mul (K := K) hn
  rw [Nmat, Matrix.det_one_add_mul_comm,
    show (Fmat K n).transpose * (Fmat K n * S) = 0 by rw [← Matrix.mul_assoc, hF, Matrix.zero_mul]]
  simp

theorem one_add_Nmat_mul_self [CharP K 2] {n : ℕ} (hn : n = 4 ∨ n = 5)
    (S : Matrix (Fin 2) (Fin 2) K) : (1 + Nmat K n S) * (1 + Nmat K n S) = 1 := by
  rw [one_add_mul_one_add hn]
  have : S + S = 0 := by
    ext i j
    simp [CharTwo.add_self_eq_zero]
  rw [this, Nmat_zero, add_zero]

theorem Nmat_apply (S : Matrix (Fin 2) (Fin 2) K) {n : ℕ} (i j : Fin n) (a b : Fin 2)
    (hi : i.val / 2 = a.val) (hj : j.val / 2 = b.val) : Nmat K n S i j = S a b := by
  have hFi : ∀ c : Fin 2, Fmat K n i c = if c = a then 1 else 0 := by
    intro c
    simp only [Fmat, Matrix.of_apply]
    rw [hi]
    simp [Fin.ext_iff, eq_comm]
  have hFj : ∀ c : Fin 2, Fmat K n j c = if c = b then 1 else 0 := by
    intro c
    simp only [Fmat, Matrix.of_apply]
    rw [hj]
    simp [Fin.ext_iff, eq_comm]
  simp only [Nmat, Matrix.mul_apply, Matrix.transpose_apply, hFi, hFj, Fin.sum_univ_two]
  fin_cases a <;> fin_cases b <;> simp

theorem Fmat_map (σ : K →+* K) {n : ℕ} : (Fmat K n).map σ = Fmat K n := by
  ext i a
  simp only [Matrix.map_apply, Fmat, Matrix.of_apply]
  split_ifs <;> simp

theorem Nmat_map (σ : K →+* K) {n : ℕ} (S : Matrix (Fin 2) (Fin 2) K) :
    (Nmat K n S).map σ = Nmat K n (S.map σ) := by
  have hFt : (Fmat K n).transpose.map σ = (Fmat K n).transpose := by
    rw [Matrix.transpose_map, Fmat_map]
  simp only [Nmat]
  rw [Matrix.map_mul, Matrix.map_mul, Fmat_map, hFt]

theorem Nmat_transpose {n : ℕ} (S : Matrix (Fin 2) (Fin 2) K) :
    (Nmat K n S).transpose = Nmat K n S.transpose := by
  simp only [Nmat, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem Smat_add (σ : K →+* K) (a d b a' d' b' : K) :
    Smat σ a d b + Smat σ a' d' b' = Smat σ (a + a') (d + d') (b + b') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Smat, map_add]

theorem Smat_zero (σ : K →+* K) : Smat σ 0 0 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Smat]

@[expose] def emb [CharP K 2] : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K

theorem emb_injective [CharP K 2] : Function.Injective (emb : ZMod 2 →+* K) :=
  (emb : ZMod 2 →+* K).injective

theorem map_emb [CharP K 2] (σ : K →+* K) (a : ZMod 2) : σ (emb a) = emb a :=
  congrArg (fun f : ZMod 2 →+* K => f a) (RingHom.ext_zmod (σ.comp emb) emb)

@[expose] def Mmat [CharP K 2] (σ : K →+* K) (n : ℕ) (x : ZMod 2 × ZMod 2 × K) :
    Matrix (Fin n) (Fin n) K :=
  1 + Nmat K n (Smat σ (emb x.1) (emb x.2.1) x.2.2)

theorem Mmat_zero [CharP K 2] (σ : K →+* K) (n : ℕ) : Mmat σ n 0 = 1 := by
  simp [Mmat, Smat_zero, Nmat_zero]

theorem Mmat_add [CharP K 2] (σ : K →+* K) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (x y : ZMod 2 × ZMod 2 × K) : Mmat σ n (x + y) = Mmat σ n x * Mmat σ n y := by
  simp only [Mmat]
  rw [one_add_mul_one_add hn, Smat_add]
  simp [map_add]

theorem Mmat_mul_self [CharP K 2] (σ : K →+* K) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (x : ZMod 2 × ZMod 2 × K) : Mmat σ n x * Mmat σ n x = 1 :=
  one_add_Nmat_mul_self hn _

theorem det_Mmat [CharP K 2] (σ : K →+* K) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (x : ZMod 2 × ZMod 2 × K) : (Mmat σ n x).det = 1 :=
  det_one_add_Nmat hn _

theorem Mmat_adj [CharP K 2] (h : UnitaryFieldData 2 1 K) (n : ℕ) (x : ZMod 2 × ZMod 2 × K) :
    ((Mmat h.bar n x).map h.bar).transpose = Mmat h.bar n x := by
  have hS : ((Smat h.bar (emb x.1) (emb x.2.1) x.2.2).map h.bar).transpose =
      Smat h.bar (emb x.1) (emb x.2.1) x.2.2 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Smat, map_emb, h.bar_bar]
  simp only [Mmat]
  rw [Matrix.map_add h.bar (map_add h.bar), Matrix.map_one h.bar (map_zero h.bar) (map_one h.bar),
    Matrix.transpose_add, Matrix.transpose_one, Nmat_map, Nmat_transpose, hS]

@[expose] def Munit [CharP K 2] (σ : K →+* K) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (x : ZMod 2 × ZMod 2 × K) : GL (Fin n) K :=
  ⟨Mmat σ n x, Mmat σ n x, Mmat_mul_self σ hn x, Mmat_mul_self σ hn x⟩

@[expose] def Mhom [CharP K 2] (σ : K →+* K) {n : ℕ} (hn : n = 4 ∨ n = 5) :
    Multiplicative (ZMod 2 × ZMod 2 × K) →* GL (Fin n) K where
  toFun x := Munit σ hn (Multiplicative.toAdd x)
  map_one' := Units.ext (by simp [Munit, Mmat_zero])
  map_mul' x y := Units.ext (by simp [Munit, Mmat_add σ hn])

theorem Mhom_coe [CharP K 2] (σ : K →+* K) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (x : Multiplicative (ZMod 2 × ZMod 2 × K)) :
    ((Mhom σ hn x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Mmat σ n (Multiplicative.toAdd x) := rfl

theorem Mhom_mem [CharP K 2] (h : UnitaryFieldData 2 1 K) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (x : Multiplicative (ZMod 2 × ZMod 2 × K)) : Mhom h.bar hn x ∈ StatedSU n (2 ^ 1) K := by
  refine (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).2 ⟨?_, ?_⟩
  · rw [Mhom_coe]
    exact det_Mmat h.bar hn _
  · rw [Mhom_coe, Mmat_adj h]
    exact Mmat_mul_self h.bar hn _

theorem eq_one_of_scalar_Mhom [CharP K 2] (σ : K →+* K) {n : ℕ} (hn : n = 4 ∨ n = 5) {c : Kˣ}
    {x : Multiplicative (ZMod 2 × ZMod 2 × K)}
    (h : Matrix.GeneralLinearGroup.scalar (Fin n) c = Mhom σ hn x) : x = 1 := by
  have hn4 : 4 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  obtain ⟨i0, hi0⟩ : ∃ i : Fin n, i.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨i1, hi1⟩ : ∃ i : Fin n, i.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
  obtain ⟨i2, hi2⟩ : ∃ i : Fin n, i.val = 2 := ⟨⟨2, by omega⟩, rfl⟩
  obtain ⟨i3, hi3⟩ : ∃ i : Fin n, i.val = 3 := ⟨⟨3, by omega⟩, rfl⟩
  have key : ∀ i j : Fin n, i ≠ j → (Mmat σ n (Multiplicative.toAdd x)) i j = 0 := by
    intro i j hij
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) i j) h
    simpa [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij,
      Mhom_coe] using this.symm
  have hne01 : i0 ≠ i1 := fun h => by subst h; omega
  have hne23 : i2 ≠ i3 := fun h => by subst h; omega
  have hne02 : i0 ≠ i2 := fun h => by subst h; omega
  have h01 := key i0 i1 hne01
  have h23 := key i2 i3 hne23
  have h02 := key i0 i2 hne02
  simp only [Mmat, Matrix.add_apply] at h01 h23 h02
  rw [Matrix.one_apply_ne hne01, zero_add,
    Nmat_apply _ i0 i1 0 0 (by rw [hi0]; rfl) (by rw [hi1]; rfl)] at h01
  rw [Matrix.one_apply_ne hne23, zero_add,
    Nmat_apply _ i2 i3 1 1 (by rw [hi2]; rfl) (by rw [hi3]; rfl)] at h23
  rw [Matrix.one_apply_ne hne02, zero_add,
    Nmat_apply _ i0 i2 0 1 (by rw [hi0]; rfl) (by rw [hi2]; rfl)] at h02
  have e1 : emb (Multiplicative.toAdd x).1 = (0 : K) := by simpa [Smat] using h01
  have e2 : emb (Multiplicative.toAdd x).2.1 = (0 : K) := by simpa [Smat] using h23
  have e3 : (Multiplicative.toAdd x).2.2 = 0 := by simpa [Smat] using h02
  apply Multiplicative.toAdd.injective
  exact Prod.ext (emb_injective (e1.trans (map_zero emb).symm))
    (Prod.ext (emb_injective (e2.trans (map_zero emb).symm)) e3)

theorem exists_elemAb (h : UnitaryFieldData 2 1 K) {n : ℕ} (hn : n = 4 ∨ n = 5) {E : Type}
    [Group E] (e : E ≃* StatedProj (StatedSU n (2 ^ 1) K)) :
    ∃ S₀ : Subgroup E, (∀ a ∈ S₀, ∀ b ∈ S₀, a * b = b * a) ∧ (∀ a ∈ S₀, a * a = 1) ∧
      Nat.card S₀ = 2 ^ 4 := by
  have := h.charP
  obtain ⟨ψ, hψ⟩ := CResH2.exists_injective_proj (StatedSU n (2 ^ 1) K) (Mhom h.bar hn)
    (Mhom_mem h hn) (fun _ _ hs => eq_one_of_scalar_Mhom h.bar hn hs)
  have h2 : ∀ a : Multiplicative (ZMod 2 × ZMod 2 × K), a * a = 1 := fun a => by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_one]
    exact Prod.ext (CharTwo.add_self_eq_zero _) (Prod.ext (CharTwo.add_self_eq_zero _)
      (CharTwo.add_self_eq_zero _))
  obtain ⟨hab, h2', hS⟩ := range_elemAb_of_injective (e.symm.toMonoidHom.comp ψ)
    (e.symm.injective.comp hψ) h2
  refine ⟨_, hab, h2', ?_⟩
  rw [hS, Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_prod, Nat.card_zmod,
    h.card]
  norm_num

end CFSG.EvenSporadicStandard.M24Std.CResH3
