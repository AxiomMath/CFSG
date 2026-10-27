module

public import CFSG.LargeExtraspecial.S14C12TSp
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE

open Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.Models.SymplecticPairs (inclMat inclMat_transpose_mul)
open scoped MatrixGroups

variable {K : Type} [Field K]

section Embed

variable {m n : ℕ} (σ : Fin m → Fin n)

@[expose] def slEmbedMat (g : Matrix (Fin m) (Fin m) K) : Matrix (Fin n) (Fin n) K :=
  1 + inclMat (K := K) σ * (g - 1) * (inclMat (K := K) σ)ᵀ

variable {σ}

theorem slEmbedMat_one : slEmbedMat σ (1 : Matrix (Fin m) (Fin m) K) = 1 := by
  simp [slEmbedMat]

theorem slEmbedMat_mul (hσ : Function.Injective σ) (g h : Matrix (Fin m) (Fin m) K) :
    slEmbedMat σ (g * h) = slEmbedMat σ g * slEmbedMat σ h := by
  simp only [slEmbedMat]
  set P := inclMat (K := K) σ
  have hPP : Pᵀ * P = 1 := inclMat_transpose_mul hσ
  have e1 : g * h - 1 = (g - 1) + (h - 1) + (g - 1) * (h - 1) := by noncomm_ring
  have e2 : P * (g - 1) * Pᵀ * (P * (h - 1) * Pᵀ) = P * ((g - 1) * (h - 1)) * Pᵀ := by
    calc P * (g - 1) * Pᵀ * (P * (h - 1) * Pᵀ) = P * (g - 1) * (Pᵀ * P) * (h - 1) * Pᵀ := by
          simp only [Matrix.mul_assoc]
      _ = P * ((g - 1) * (h - 1)) * Pᵀ := by
          rw [hPP, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  have e3 : P * (g * h - 1) * Pᵀ = P * (g - 1) * Pᵀ + P * (h - 1) * Pᵀ +
      P * (g - 1) * Pᵀ * (P * (h - 1) * Pᵀ) := by
    rw [e2, e1, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  rw [e3]
  noncomm_ring

theorem det_slEmbedMat (hσ : Function.Injective σ) (g : Matrix (Fin m) (Fin m) K) :
    (slEmbedMat σ g).det = g.det := by
  set P := inclMat (K := K) σ
  have hPP : Pᵀ * P = 1 := inclMat_transpose_mul hσ
  rw [slEmbedMat, Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hPP,
    Matrix.mul_one, add_sub_cancel]

theorem slEmbedMat_injective (hσ : Function.Injective σ) :
    Function.Injective (slEmbedMat (K := K) σ) := by
  intro g h hgh
  set P := inclMat (K := K) σ
  have hPP : Pᵀ * P = 1 := inclMat_transpose_mul hσ
  have key : ∀ g : Matrix (Fin m) (Fin m) K, Pᵀ * slEmbedMat σ g * P = g := by
    intro g
    rw [slEmbedMat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPP]
    calc 1 + Pᵀ * (P * (g - 1) * Pᵀ) * P = 1 + (Pᵀ * P) * (g - 1) * (Pᵀ * P) := by
          simp only [Matrix.mul_assoc]
      _ = g := by rw [hPP, Matrix.one_mul, Matrix.mul_one, add_sub_cancel]
  rw [← key g, ← key h, hgh]

variable (σ)

@[expose] def slEmbed (hσ : Function.Injective σ) :
    SpecialLinearGroup (Fin m) K →* SpecialLinearGroup (Fin n) K where
  toFun g := ⟨slEmbedMat σ (g : Matrix (Fin m) (Fin m) K), by
    rw [det_slEmbedMat hσ, g.2]⟩
  map_one' := Subtype.ext slEmbedMat_one
  map_mul' g h := Subtype.ext (slEmbedMat_mul hσ (g : Matrix (Fin m) (Fin m) K) h)

variable {σ}

theorem slEmbed_injective (hσ : Function.Injective σ) :
    Function.Injective (slEmbed (K := K) σ hσ) := fun _ _ h =>
  Subtype.ext (slEmbedMat_injective hσ (congrArg Subtype.val h))

end Embed

@[expose] def transvectionSL {n : ℕ} (i j : Fin n) (hij : i ≠ j) : SpecialLinearGroup (Fin n) K :=
  ⟨transvection i j (1 : K), det_transvection_of_ne i j hij 1⟩

theorem transvectionSL_mem_unitriangular {n : ℕ} {i j : Fin n} (hij : i < j) :
    transvectionSL (K := K) i j hij.ne ∈ LinearFlag.unitriangular n K := by
  refine ⟨fun a b hba => ?_, fun a => ?_⟩
  · show (1 + Matrix.single i j (1 : K)) a b = 0
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hba), zero_add, Matrix.single_apply]
    exact ite_eq_right fun h => by
      obtain ⟨rfl, rfl⟩ := h
      exact absurd hij (not_lt.mpr hba.le)
  · show (1 + Matrix.single i j (1 : K)) a a = 1
    rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply]
    exact (add_eq_left.mpr (ite_eq_right fun h => hij.ne (h.1.trans h.2.symm)))

theorem commute_single_of_commute_transvectionSL {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {y : SpecialLinearGroup (Fin n) K} (h : Commute (transvectionSL i j hij) y) :
    (y : Matrix (Fin n) (Fin n) K) * Matrix.single i j 1 =
      Matrix.single i j 1 * (y : Matrix (Fin n) (Fin n) K) := by
  have h' : ((transvectionSL i j hij * y : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) =
      ((y * transvectionSL i j hij : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) := by
    rw [h.eq]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h'
  change (1 + Matrix.single i j (1 : K)) * (y : Matrix (Fin n) (Fin n) K) =
    (y : Matrix (Fin n) (Fin n) K) * (1 + Matrix.single i j (1 : K)) at h'
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one] at h'
  exact (add_left_cancel h').symm

section Entries

variable {n : ℕ} {X : Matrix (Fin n) (Fin n) K}

theorem entries_of_single_comm (i j : Fin n)
    (h : X * Matrix.single i j (1 : K) = Matrix.single i j 1 * X) :
    (∀ a, a ≠ i → X a i = 0) ∧ (∀ b, b ≠ j → X j b = 0) ∧ X i i = X j j := by
  refine ⟨fun a ha => ?_, fun b hb => ?_, ?_⟩
  · have := congrFun (congrFun h a) j
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ ha, mul_one] at this
    exact this
  · have := congrFun (congrFun h i) b
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hb, Matrix.single_mul_apply_same, one_mul] at this
    exact this.symm
  · have := congrFun (congrFun h i) j
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_same, mul_one, one_mul] at this
    exact this

end Entries

@[expose] def midCoord (c : Fin 7) : Fin 9 := ⟨c.val + 1, by omega⟩

theorem midCoord_injective : Function.Injective midCoord := fun a b h =>
  Fin.ext (by have := congrArg Fin.val h; simp only [midCoord] at this; omega)

section Nine

variable {X : Matrix (Fin 9) (Fin 9) K}

@[expose] def CommHyp9 (X : Matrix (Fin 9) (Fin 9) K) : Prop :=
  ∀ k : Fin 9, 0 < k.val → k.val < 8 →
    X * Matrix.single 0 k (1 : K) = Matrix.single 0 k 1 * X ∧
      X * Matrix.single k 8 (1 : K) = Matrix.single k 8 1 * X

theorem CommHyp9.entries (hX : CommHyp9 X) (c : Fin 7) (a : Fin 9) :
    X a (midCoord c) = (if a = midCoord c then X 0 0 else 0) ∧
      X (midCoord c) a = (if a = midCoord c then X 0 0 else 0) := by
  have hk0 : 0 < (midCoord c).val := by simp only [midCoord]; omega
  have hk8 : (midCoord c).val < 8 := by have := c.isLt; simp only [midCoord]; omega
  obtain ⟨h0k, hk8'⟩ := hX (midCoord c) hk0 hk8
  obtain ⟨-, hrow, hdiag⟩ := entries_of_single_comm 0 (midCoord c) h0k
  obtain ⟨hcol, -, -⟩ := entries_of_single_comm (midCoord c) 8 hk8'
  refine ⟨?_, ?_⟩ <;> split_ifs with ha
  · subst ha; exact hdiag.symm
  · exact hcol a ha
  · subst ha; exact hdiag.symm
  · exact hrow a ha

theorem CommHyp9.mul_incl (hX : CommHyp9 X) :
    X * inclMat (K := K) midCoord = X 0 0 • inclMat (K := K) midCoord := by
  ext a c
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [inclMat, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (midCoord c)]
  simp only [Finset.mem_univ, ite_true]
  rw [(hX.entries c a).1]

theorem CommHyp9.incl_transpose_mul (hX : CommHyp9 X) :
    (inclMat (K := K) midCoord)ᵀ * X = X 0 0 • (inclMat (K := K) midCoord)ᵀ := by
  ext c b
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
  simp_rw [Matrix.transpose_apply, inclMat, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (midCoord c)]
  simp only [Finset.mem_univ, ite_true]
  rw [(hX.entries c b).2]
  by_cases h : b = midCoord c <;> simp [h]

theorem CommHyp9.commute_slEmbedMat (hX : CommHyp9 X) (g : Matrix (Fin 7) (Fin 7) K) :
    X * slEmbedMat midCoord g = slEmbedMat midCoord g * X := by
  have h1 := hX.mul_incl
  have h2 := hX.incl_transpose_mul
  rw [slEmbedMat]
  set P := inclMat (K := K) midCoord
  set c := X 0 0
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  calc X * (P * (g - 1) * Pᵀ) = X * P * (g - 1) * Pᵀ := by simp only [Matrix.mul_assoc]
    _ = c • (P * (g - 1) * Pᵀ) := by rw [h1, Matrix.smul_mul, Matrix.smul_mul]
    _ = P * (g - 1) * (Pᵀ * X) := by rw [h2, Matrix.mul_smul]
    _ = P * (g - 1) * Pᵀ * X := by simp only [Matrix.mul_assoc]

theorem commHyp9_of_commute {y : SpecialLinearGroup (Fin 9) K}
    (hy : ∀ u ∈ LinearFlag.unitriangular 9 K, Commute u y) :
    CommHyp9 (y : Matrix (Fin 9) (Fin 9) K) := by
  intro k hk0 hk8
  have h0k : (0 : Fin 9) < k := by rw [Fin.lt_def]; exact hk0
  have hk8' : k < (8 : Fin 9) := by rw [Fin.lt_def]; exact hk8
  exact ⟨commute_single_of_commute_transvectionSL h0k.ne
      (hy _ (transvectionSL_mem_unitriangular h0k)),
    commute_single_of_commute_transvectionSL hk8'.ne
      (hy _ (transvectionSL_mem_unitriangular hk8'))⟩

end Nine

section OneTwoSeven

variable [Finite K]

theorem exists_orderOf_eq_127 (hK : Nat.card K = 2) :
    ∃ g : SpecialLinearGroup (Fin 7) K, orderOf g = 127 := by
  have : Fact (Nat.Prime 127) := ⟨by norm_num⟩
  have hc : Nat.card (SpecialLinearGroup (Fin 7) K) = 2 ^ 21 * 3 * 7 * 15 * 31 * 63 * 127 := by
    rw [LinearFlag.card_SL_eq (by norm_num), hK]
    decide
  have : Finite (SpecialLinearGroup (Fin 7) K) := Nat.finite_of_card_ne_zero (by rw [hc]; decide)
  exact exists_prime_orderOf_dvd_card' 127 (by rw [hc]; decide)

theorem exists_orderOf_eq_127_commute (hK : Nat.card K = 2) {y : SpecialLinearGroup (Fin 9) K}
    (hy : ∀ u ∈ LinearFlag.unitriangular 9 K, Commute u y) :
    ∃ h : SpecialLinearGroup (Fin 9) K, orderOf h = 127 ∧ Commute h y := by
  obtain ⟨g, hg⟩ := exists_orderOf_eq_127 hK
  refine ⟨slEmbed midCoord midCoord_injective g, ?_, ?_⟩
  · rw [orderOf_injective _ (slEmbed_injective midCoord_injective) g, hg]
  · exact Subtype.ext
      ((commHyp9_of_commute hy).commute_slEmbedMat (g : Matrix (Fin 7) (Fin 7) K)).symm

end OneTwoSeven

theorem scalars_eq_bot_of_natCard_eq_two {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2) :
    LinearFlag.scalars n K = ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have h := LinearFlag.card_scalars_dvd (K := K) hn
  rw [hK] at h
  exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.mp h)

theorem isPGroup_unitriangular_two (n : ℕ) (hK : Nat.card K = 2) :
    IsPGroup 2 (LinearFlag.unitriangular n K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  exact IsPGroup.of_card (n := n * (n - 1) / 2) (by rw [LinearFlag.card_unitriangular, hK])

theorem dvd_card_centralizer_of_orderOf_commute {H : Type} [Group H] [Finite H] {x h : H} {q : ℕ}
    (hh : orderOf h = q) (hc : Commute h x) :
    q ∣ Nat.card (Subgroup.centralizer ({x} : Set H)) := by
  have hmem : h ∈ Subgroup.centralizer ({x} : Set H) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hc.eq
  rw [← hh, ← Subgroup.orderOf_mk h hmem]
  exact orderOf_dvd_natCard _

theorem dvd_card_centralizer_PSL9_127 {H : Type} [Group H] [Finite H]
    (h : LieModel H .PSL 9 2 1) {x : H}
    (hS : ∃ P : Sylow 2 H, (P : Subgroup H) ≤ Subgroup.centralizer ({x} : Set H)) :
    127 ∣ Nat.card (Subgroup.centralizer ({x} : Set H)) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : H ≃* SpecialLinearGroup (Fin 9) K := e.trans
    ((QuotientGroup.quotientMulEquivOfEq (scalars_eq_bot_of_natCard_eq_two (by norm_num) hK2)).trans
      QuotientGroup.quotientBot)
  obtain ⟨h₁, hh₁, hc₁⟩ := LargeExtraspecial.S14.Sp12.exists_commute_of_sylow_le_centralizer
    ((isPGroup_unitriangular_two 9 hK2).map f.symm.toMonoidHom) (q := 127) (fun y hy => by
      obtain ⟨h₀, hh₀, hc₀⟩ := exists_orderOf_eq_127_commute hK2 (y := f y) fun u hu => by
        simpa using (hy (f.symm u) ⟨u, hu, rfl⟩).map f.toMonoidHom
      exact ⟨f.symm h₀, by rw [MulEquiv.orderOf_eq, hh₀], by
        simpa using hc₀.map f.symm.toMonoidHom⟩) hS
  exact dvd_card_centralizer_of_orderOf_commute hh₁ hc₁

end CFSG.GF2Type.SmithTypeE
