module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def ofStrict (Y : Matrix (Fin n) (Fin n) K) (hY : ∀ i j : Fin n, j ≤ i → Y i j = 0) :
    SpecialLinearGroup (Fin n) K :=
  ⟨1 + Y, by
    have hU : (1 + Y).IsUpperTriangular := by
      intro i j hij
      have hji : j < i := hij
      rw [Matrix.add_apply, one_apply_ne (ne_of_gt hji), hY i j hji.le, add_zero]
    rw [det_of_isUpperTriangular hU]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [Matrix.add_apply, one_apply_eq, hY i i le_rfl, add_zero]⟩

theorem coe_ofStrict (Y : Matrix (Fin n) (Fin n) K) (hY : ∀ i j : Fin n, j ≤ i → Y i j = 0) :
    ((ofStrict Y hY : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + Y := rfl

theorem ofStrict_mem (Y : Matrix (Fin n) (Fin n) K) (hY : ∀ i j : Fin n, j ≤ i → Y i j = 0) :
    ofStrict Y hY ∈ unitriangular n K := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [coe_ofStrict, Matrix.add_apply, one_apply_ne (ne_of_gt hij), hY i j hij.le, add_zero]
  · rw [coe_ofStrict, Matrix.add_apply, one_apply_eq, hY i i le_rfl, add_zero]

theorem strict_of_mem {A : SpecialLinearGroup (Fin n) K} (hA : A ∈ unitriangular n K) :
    ∀ i j : Fin n, j ≤ i → ((A : Matrix (Fin n) (Fin n) K) - 1) i j = 0 := by
  intro i j hji
  rcases hji.lt_or_eq with h | rfl
  · rw [Matrix.sub_apply, hA.1 i j h, one_apply_ne (ne_of_gt h), sub_zero]
  · rw [Matrix.sub_apply, hA.2, one_apply_eq, sub_self]

theorem strict_single {i j : Fin n} (hij : i < j) (c : K) :
    ∀ a b : Fin n, b ≤ a → (single i j c : Matrix (Fin n) (Fin n) K) a b = 0 := by
  intro a b hba
  apply single_apply_of_ne
  rintro ⟨rfl, rfl⟩
  exact absurd hij (not_lt.mpr hba)

@[expose] def strictUpper (n : ℕ) (K : Type*) [Field K] :
    AddSubgroup (Matrix (Fin n) (Fin n) K) where
  carrier := {Y | ∀ i j : Fin n, j ≤ i → Y i j = 0}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := fun {Y Y'} hY hY' i j hji => by
    rw [Matrix.add_apply, hY i j hji, hY' i j hji, add_zero]
  neg_mem' := fun {Y} hY i j hji => by
    rw [Matrix.neg_apply, hY i j hji, neg_zero]

@[expose] def superdiag (n : ℕ) (K : Type*) [Field K] : strictUpper n K →+ (Fin (n - 1) → K) where
  toFun Y i := (Y : Matrix (Fin n) (Fin n) K) ⟨i, by omega⟩ ⟨i + 1, by omega⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem superdiag_apply (Y : strictUpper n K) (i : Fin (n - 1)) :
    superdiag n K Y i = (Y : Matrix (Fin n) (Fin n) K) ⟨i, by omega⟩ ⟨i + 1, by omega⟩ := rfl

theorem superdiag_surjective : Function.Surjective (superdiag n K) := by
  intro v
  refine ⟨⟨Matrix.of fun a b => if h : b.val = a.val + 1 then v ⟨a.val, by omega⟩ else 0,
    fun i j hji => ?_⟩, ?_⟩
  · rw [Fin.le_def] at hji
    simp only [Matrix.of_apply]
    rw [dite_eq_right_iff.mpr fun h => absurd h (by omega)]
  · funext i
    rw [superdiag_apply]
    simp only [Matrix.of_apply, dite_true]

theorem mul_superdiag_eq_zero {X Y : Matrix (Fin n) (Fin n) K} (hX : X ∈ strictUpper n K)
    (hY : Y ∈ strictUpper n K) (i : Fin (n - 1)) :
    (X * Y) ⟨i, by omega⟩ ⟨i + 1, by omega⟩ = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k.val ≤ i.val
  · rw [hX _ k (by rw [Fin.le_def]; exact hk), zero_mul]
  · rw [hY k _ (by rw [Fin.le_def]; simp only; omega), mul_zero]

theorem mul_mem_strictUpper {X Y : Matrix (Fin n) (Fin n) K} (hX : X ∈ strictUpper n K)
    (hY : Y ∈ strictUpper n K) : X * Y ∈ strictUpper n K := by
  intro i j hji
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k ≤ i
  · rw [hX i k hk, zero_mul]
  · rw [hY k j (le_trans hji (le_of_lt (not_le.mp hk))), mul_zero]

@[expose] def adStrict {X : Matrix (Fin n) (Fin n) K} (hX : X ∈ strictUpper n K) :
    strictUpper n K →+ strictUpper n K where
  toFun Y := ⟨X * Y - Y * X, (strictUpper n K).sub_mem (mul_mem_strictUpper hX Y.2)
    (mul_mem_strictUpper Y.2 hX)⟩
  map_zero' := by ext; simp
  map_add' Y Y' := by ext; simp [Matrix.mul_add, Matrix.add_mul]; abel

theorem range_adStrict_le {X : Matrix (Fin n) (Fin n) K} (hX : X ∈ strictUpper n K) :
    (adStrict hX).range ≤ (superdiag n K).ker := by
  rintro _ ⟨Y, rfl⟩
  rw [AddMonoidHom.mem_ker]
  funext i
  rw [superdiag_apply, Pi.zero_apply]
  show (X * (Y : Matrix (Fin n) (Fin n) K) - (Y : Matrix (Fin n) (Fin n) K) * X)
    ⟨i, by omega⟩ ⟨i + 1, by omega⟩ = 0
  rw [Matrix.sub_apply, mul_superdiag_eq_zero hX Y.2, mul_superdiag_eq_zero Y.2 hX, sub_zero]

theorem pow_card_le_card_ker_adStrict [Finite K] {X : Matrix (Fin n) (Fin n) K}
    (hX : X ∈ strictUpper n K) :
    Nat.card K ^ (n - 1) ≤ Nat.card (adStrict hX).ker := by
  have h1 := AddSubgroup.card_ker_mul_card_range (superdiag n K)
  have h2 := AddSubgroup.card_ker_mul_card_range (adStrict hX)
  rw [AddMonoidHom.range_eq_top_of_surjective _ superdiag_surjective, AddSubgroup.card_top,
    Nat.card_fun, Nat.card_eq_fintype_card (α := Fin (n - 1)), Fintype.card_fin] at h1
  have h3 : Nat.card (adStrict hX).range ≤ Nat.card (superdiag n K).ker :=
    AddSubgroup.card_le_of_le (range_adStrict_le hX)
  have hpos : 0 < Nat.card (superdiag n K).ker := Nat.card_pos
  have h4 : Nat.card (superdiag n K).ker * Nat.card K ^ (n - 1) ≤
      Nat.card (superdiag n K).ker * Nat.card (adStrict hX).ker := by
    calc Nat.card (superdiag n K).ker * Nat.card K ^ (n - 1) = Nat.card (strictUpper n K) := h1
      _ = Nat.card (adStrict hX).ker * Nat.card (adStrict hX).range := h2.symm
      _ ≤ Nat.card (adStrict hX).ker * Nat.card (superdiag n K).ker := Nat.mul_le_mul_left _ h3
      _ = _ := mul_comm _ _
  exact Nat.le_of_mul_le_mul_left h4 hpos

theorem card_ker_adStrict_le_card_unitriangular_inf_centralizer [Finite K]
    {A : SpecialLinearGroup (Fin n) K} (hA : A ∈ unitriangular n K) :
    Nat.card (adStrict (strict_of_mem hA)).ker ≤
      Nat.card (unitriangular n K ⊓ Subgroup.centralizer ({A} : Set _) : Subgroup _) := by
  have hX : (A : Matrix (Fin n) (Fin n) K) - 1 ∈ strictUpper n K := strict_of_mem hA
  let φ : (adStrict hX).ker →
      ↥(unitriangular n K ⊓ Subgroup.centralizer ({A} : Set _)) := fun Y =>
    ⟨ofStrict (Y : strictUpper n K) (Y : strictUpper n K).2, ofStrict_mem _ _, by
      show _ ∈ Subgroup.centralizer ({A} : Set _)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hY := Y.2
      rw [AddMonoidHom.mem_ker] at hY
      have hc : ((A : Matrix (Fin n) (Fin n) K) - 1) * (Y : strictUpper n K) =
          ((Y : strictUpper n K) : Matrix (Fin n) (Fin n) K) *
            ((A : Matrix (Fin n) (Fin n) K) - 1) :=
        sub_eq_zero.mp (congrArg Subtype.val hY)
      apply Subtype.ext
      show (1 + ((Y : strictUpper n K) : Matrix (Fin n) (Fin n) K)) * A =
        (A : Matrix (Fin n) (Fin n) K) * (1 + (Y : strictUpper n K))
      set Xm := (A : Matrix (Fin n) (Fin n) K) - 1
      set Ym := ((Y : strictUpper n K) : Matrix (Fin n) (Fin n) K)
      have hA1 : (A : Matrix (Fin n) (Fin n) K) = 1 + Xm := by
        simp only [Xm]; abel
      rw [hA1]
      calc (1 + Ym) * (1 + Xm) = 1 + Xm + Ym + Ym * Xm := by
            rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, Matrix.one_mul,
              Matrix.mul_one]; abel
        _ = 1 + Ym + Xm + Xm * Ym := by rw [hc]; abel
        _ = (1 + Xm) * (1 + Ym) := by
            rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, Matrix.one_mul,
              Matrix.mul_one]; abel⟩
  refine Nat.card_le_card_of_injective φ fun Y Y' h => ?_
  have h1 := congrArg (fun g : ↥(unitriangular n K ⊓ Subgroup.centralizer ({A} : Set _)) =>
    ((g : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) h
  have h2 : (1 : Matrix (Fin n) (Fin n) K) + (Y : strictUpper n K) =
      1 + ((Y' : (adStrict hX).ker) : strictUpper n K) := h1
  exact Subtype.ext (Subtype.ext (add_left_cancel h2))

theorem pow_card_le_card_unitriangular_inf_centralizer [Finite K]
    {A : SpecialLinearGroup (Fin n) K} (hA : A ∈ unitriangular n K) :
    Nat.card K ^ (n - 1) ≤
      Nat.card (unitriangular n K ⊓ Subgroup.centralizer ({A} : Set _) : Subgroup _) :=
  (pow_card_le_card_ker_adStrict _).trans
    (card_ker_adStrict_le_card_unitriangular_inf_centralizer hA)

theorem card_unitriangular_inf_centralizer_le_card_proj [Finite K]
    (A : SpecialLinearGroup (Fin n) K) :
    Nat.card (unitriangular n K ⊓ Subgroup.centralizer ({A} : Set _) : Subgroup _) ≤
      Nat.card (projUnitriangular n K ⊓
        Subgroup.centralizer ({proj n K A} : Set _) : Subgroup _) := by
  let f : ↥(unitriangular n K ⊓ Subgroup.centralizer ({A} : Set _)) →
      ↥(projUnitriangular n K ⊓ Subgroup.centralizer ({proj n K A} : Set _)) := fun g =>
    ⟨proj n K g, ⟨g, g.2.1, rfl⟩, by
      show proj n K g ∈ Subgroup.centralizer ({proj n K A} : Set _)
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.mp g.2.2]⟩
  refine Nat.card_le_card_of_injective f fun g g' h => ?_
  have h1 : proj n K g = proj n K g' := congrArg Subtype.val h
  exact Subtype.ext (proj_injOn_unitriangular n g.2.1 g'.2.1 h1)

theorem pow_card_le_card_projUnitriangular_inf_centralizer [Finite K]
    {t : projectiveSL n K} (ht : t ∈ projUnitriangular n K) :
    Nat.card K ^ (n - 1) ≤
      Nat.card (projUnitriangular n K ⊓ Subgroup.centralizer ({t} : Set _) : Subgroup _) := by
  obtain ⟨A, hA, rfl⟩ := ht
  exact (pow_card_le_card_unitriangular_inf_centralizer hA).trans
    (card_unitriangular_inf_centralizer_le_card_proj A)

theorem dvd81_card_projUnitriangular_inf_centralizer_of_le [Finite K] [CharP K 3] (hn : 1 ≤ n)
    {t : projectiveSL n K}
    (h : 81 ≤ Nat.card (projUnitriangular n K ⊓ Subgroup.centralizer ({t} : Set _) : Subgroup _)) :
    81 ∣ Nat.card (projUnitriangular n K ⊓ Subgroup.centralizer ({t} : Set _) : Subgroup _) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := K) 3 (n := n) hn
  have hp : IsPGroup 3
      (projUnitriangular n K ⊓ Subgroup.centralizer ({t} : Set _) : Subgroup _) :=
    (hP ▸ P.isPGroup').to_le inf_le_left
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  rw [hk] at h ⊢
  have h81 : 3 ^ 4 ≤ 3 ^ k := le_trans (by norm_num) h
  have hk4 : 4 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).mp h81
  exact Nat.pow_dvd_pow 3 hk4

theorem dvd81_card_projUnitriangular_inf_centralizer [Finite K] [CharP K 3] (hn : 1 ≤ n)
    (hK : 81 ≤ Nat.card K ^ (n - 1)) {t : projectiveSL n K} (ht : t ∈ projUnitriangular n K) :
    81 ∣ Nat.card (projUnitriangular n K ⊓ Subgroup.centralizer ({t} : Set _) : Subgroup _) :=
  dvd81_card_projUnitriangular_inf_centralizer_of_le hn
    (hK.trans (pow_card_le_card_projUnitriangular_inf_centralizer ht))

end CFSG.HardMathSupport.Malle.E27Lie
