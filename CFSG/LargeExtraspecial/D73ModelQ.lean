module

public import CFSG.LargeExtraspecial.D73Model
public import CFSG.LargeExtraspecial.S3Qa

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW.D73

open Subgroup Matrix
open scoped MatrixGroups

variable {N : ℕ} (hN : 2 ≤ N)

theorem tZero_mem_Qm : tZero hN ∈ Qm hN := by
  rw [tZero_eq_qmat]
  exact qmat_mem_Qm hN _ _ _

theorem tZero_ne_one : tZero hN ≠ 1 := fun h => by
  rw [tZero_eq_qmat, ← qmat_zero hN] at h
  exact one_ne_zero (qmat_injective hN h).2.2

theorem tZero_mul_self : tZero hN * tZero hN = 1 := by
  rw [tZero_eq_qmat, qmat_mul, ← qmat_zero hN, add_zero, dotProduct_zero, add_zero]
  congr 1

theorem tZero_mem_center : tZero hN ∈ center (Ct N hN) :=
  mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_singleton_iff.mp g.2)

theorem mem_zpowers_tZero_iff {x : Ct N hN} : x ∈ zpowers (tZero hN) ↔ x = 1 ∨ x = tZero hN :=
  Setting.mem_zpowers_iff_of_mul_self (tZero_mul_self hN)

theorem qmat_zero_zero_eq (c : ZMod 2) : qmat hN 0 0 c = 1 ∨ qmat hN 0 0 c = tZero hN := by
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · exact Or.inl (qmat_zero hN)
  · exact Or.inr (tZero_eq_qmat hN).symm

theorem exists_qmat_of_mem_Qm {x : Ct N hN} (hx : x ∈ Qm hN) : ∃ a b c, x = qmat hN a b c :=
  ⟨_, _, _, eq_qmat_of_mem_Qm hN hx⟩

theorem qmat_mul_comm_iff (a b a' b' : Fin (N - 2) → ZMod 2) (c c' : ZMod 2) :
    qmat hN a b c * qmat hN a' b' c' = qmat hN a' b' c' * qmat hN a b c ↔ a ⬝ᵥ b' = a' ⬝ᵥ b := by
  rw [qmat_mul, qmat_mul]
  constructor
  · intro h
    have h3 := (qmat_injective hN h).2.2
    rw [add_comm c c'] at h3
    exact add_left_cancel h3
  · intro h
    rw [add_comm a a', add_comm b b', add_comm c c', h]

theorem commutator_eq_of_mul_eq {G : Type*} [Group G] {x y t : G} (ht : ∀ g, t * g = g * t)
    (h : x * y = y * x * t) : x * y * x⁻¹ * y⁻¹ = t := by
  rw [h]
  calc y * x * t * x⁻¹ * y⁻¹ = y * x * (t * (x⁻¹ * y⁻¹)) := by group
    _ = y * x * ((x⁻¹ * y⁻¹) * t) := by rw [ht]
    _ = t := by group

theorem qmat_commutator (a b a' b' : Fin (N - 2) → ZMod 2) (c c' : ZMod 2) :
    qmat hN a b c * qmat hN a' b' c' * (qmat hN a b c)⁻¹ * (qmat hN a' b' c')⁻¹ =
      qmat hN 0 0 (a ⬝ᵥ b' + a' ⬝ᵥ b) := by
  refine commutator_eq_of_mul_eq (fun g => ?_) ?_
  · rcases qmat_zero_zero_eq hN (a ⬝ᵥ b' + a' ⬝ᵥ b) with h | h <;> rw [h]
    · rw [one_mul, mul_one]
    · exact (mem_center_iff.mp (tZero_mem_center hN) g).symm
  · rw [qmat_mul, qmat_mul, qmat_mul, add_zero, add_zero, dotProduct_zero, add_zero]
    have key : ∀ c c' p q : ZMod 2, c + c' + p = c' + c + q + (p + q) := by decide
    rw [add_comm a a', add_comm b b', key c c' (a ⬝ᵥ b') (a' ⬝ᵥ b)]

theorem qmat_sq (a b : Fin (N - 2) → ZMod 2) (c : ZMod 2) :
    qmat hN a b c ^ 2 = qmat hN 0 0 (a ⬝ᵥ b) := by
  have h2 : ∀ v : Fin (N - 2) → ZMod 2, v + v = 0 := fun v =>
    funext fun i => CharTwo.add_self_eq_zero (v i)
  rw [pow_two, qmat_mul, h2, h2, CharTwo.add_self_eq_zero, zero_add]

theorem exists_not_mul_comm_Qm (h3 : 3 ≤ N) : ∃ x ∈ Qm hN, ∃ y ∈ Qm hN, x * y ≠ y * x := by
  set j₀ : Fin (N - 2) := ⟨0, by omega⟩
  refine ⟨qmat hN (Pi.single j₀ 1) 0 0, qmat_mem_Qm hN _ _ _, qmat hN 0 (Pi.single j₀ 1) 0,
    qmat_mem_Qm hN _ _ _, fun h => ?_⟩
  rw [qmat_mul_comm_iff, dotProduct_single, zero_dotProduct] at h
  simp at h

theorem eq_one_or_tZero_of_commute {x : Ct N hN} (hx : x ∈ Qm hN)
    (h : ∀ y ∈ Qm hN, x * y = y * x) : x = 1 ∨ x = tZero hN := by
  obtain ⟨a, b, c, rfl⟩ := exists_qmat_of_mem_Qm hN hx
  have ha : a = 0 := funext fun j => by
    have := (qmat_mul_comm_iff hN _ _ _ _ _ _).mp (h _ (qmat_mem_Qm hN 0 (Pi.single j 1) 0))
    simpa [dotProduct_single] using this
  have hb : b = 0 := funext fun i => by
    have := (qmat_mul_comm_iff hN _ _ _ _ _ _).mp (h _ (qmat_mem_Qm hN (Pi.single i 1) 0 0))
    simpa [single_dotProduct] using this.symm
  subst ha hb
  exact qmat_zero_zero_eq hN c

theorem isExtraspecialPGroup_Qm {N : ℕ} (hN : 3 ≤ N) :
    IsExtraspecialPGroup 2 (Qm (N := N) (by omega)) := by
  have h2 : 2 ≤ N := by omega
  refine isExtraspecialPGroup_two_of_center (c := tZero h2) (IsPGroup.of_card (card_Qm h2))
    (tZero_mem_Qm h2) (tZero_ne_one h2) (fun x hx => ⟨eq_one_or_tZero_of_commute h2 hx, ?_⟩)
    (fun x hx y hy => ?_) (fun x hx => ?_) (exists_not_mul_comm_Qm h2 hN)
  · rintro (rfl | rfl) y -
    · rw [one_mul, mul_one]
    · exact (mem_center_iff.mp (tZero_mem_center h2) y).symm
  · obtain ⟨a, b, c, rfl⟩ := exists_qmat_of_mem_Qm h2 hx
    obtain ⟨a', b', c', rfl⟩ := exists_qmat_of_mem_Qm h2 hy
    rw [qmat_commutator]
    exact qmat_zero_zero_eq h2 _
  · obtain ⟨a, b, c, rfl⟩ := exists_qmat_of_mem_Qm h2 hx
    rw [qmat_sq]
    exact qmat_zero_zero_eq h2 _

theorem mem_Qm_of_commute {g : Ct N hN}
    (h : ∀ i : Fin (N - 2), qmat hN (Pi.single i 1) 0 0 * g = g * qmat hN (Pi.single i 1) 0 0) :
    g ∈ Qm hN := by
  refine (mem_Qm_iff hN).mpr fun i j => ?_
  have h1 := congrArg
    (fun x : Ct N hN => ((x : SL(N, ZMod 2)) : Matrix (Fin N) (Fin N) (ZMod 2)) (idx0 hN)
      (midIdx j)) (h i)
  simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    sum_fin_eq hN, coe_qmat, qmatMat_idx0_idx0, qmatMat_idx0_idxL, qmatMat_idx0_midIdx,
    qmatMat_idxL_midIdx, qmatMat_midIdx_midIdx, Ct_idx0_idx0, Ct_idxL_midIdx] at h1
  simp [Pi.single_apply, Matrix.one_apply, eq_comm] at h1 ⊢
  linear_combination h1

theorem centralizer_Qm_le {N : ℕ} (hN : 3 ≤ N) :
    centralizer ((Qm (N := N) (by omega) : Subgroup (Ct N (by omega))) : Set (Ct N (by omega)))
      ≤ Qm (N := N) (by omega) := fun g hg =>
  mem_Qm_of_commute (by omega) fun i =>
    (mem_centralizer_iff.mp hg) _ (qmat_mem_Qm (by omega) _ _ _)

theorem le_Qm_of_normal {N : ℕ} (hN : 3 ≤ N) (P : Subgroup (Ct N (by omega))) (hP : P.Normal)
    (h2 : IsPGroup 2 P) : P ≤ Qm (N := N) (by omega) :=
  (Subgroup.map_eq_bot_iff P).mp (eq_bot_of_normal_of_isPGroup (N - 2) _
    (hP.map _ (midBlock_surjective (by omega))) (h2.map _))

theorem center_Ct {N : ℕ} (hN : 3 ≤ N) :
    Subgroup.center (Ct N (by omega)) = Subgroup.zpowers (tZero (N := N) (by omega)) := by
  have h2 : 2 ≤ N := by omega
  refine le_antisymm (fun g hg => ?_) ((zpowers_le).mpr (tZero_mem_center h2))
  have hc : ∀ y : Ct N h2, y * g = g * y := fun y => (mem_center_iff.mp hg y)
  have hgQ : g ∈ Qm h2 := mem_Qm_of_commute h2 fun i => hc _
  rw [mem_zpowers_tZero_iff]
  exact eq_one_or_tZero_of_commute h2 hgQ fun y _ => (hc y).symm

theorem mul_apply_of_row_eq_one {M M' : Matrix (Fin N) (Fin N) (ZMod 2)} {k : Fin N}
    (h : ∀ m, M k m = (1 : Matrix (Fin N) (Fin N) (ZMod 2)) k m) (l : Fin N) :
    (M * M') k l = M' k l := by
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun m _ => by rw [h m], ← Matrix.mul_apply,
    Matrix.one_mul]

theorem mul_apply_of_col_eq_one {M M' : Matrix (Fin N) (Fin N) (ZMod 2)} {l : Fin N}
    (h : ∀ m, M' m l = (1 : Matrix (Fin N) (Fin N) (ZMod 2)) m l) (k : Fin N) :
    (M * M') k l = M k l := by
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun m _ => by rw [h m], ← Matrix.mul_apply,
    Matrix.mul_one]

theorem coe_mul_inv_self (g : Ct N hN) :
    ((g : SL(N, ZMod 2)) : Matrix (Fin N) (Fin N) (ZMod 2)) * ((g⁻¹ : Ct N hN) : SL(N, ZMod 2)) =
      1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, ← Subgroup.coe_mul, mul_inv_cancel]
  rfl

theorem coe_inv_mul_self (g : Ct N hN) :
    (((g⁻¹ : Ct N hN) : SL(N, ZMod 2)) : Matrix (Fin N) (Fin N) (ZMod 2)) * (g : SL(N, ZMod 2)) =
      1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, ← Subgroup.coe_mul, inv_mul_cancel]
  rfl

@[expose] def Am {N : ℕ} (hN : 2 ≤ N) : Subgroup (Ct N hN) where
  carrier := {g | ∀ k l : Fin N, k ≠ idx0 hN →
    ((g : SL(N, ZMod 2)) : Matrix (Fin N) (Fin N) (ZMod 2)) k l =
      (1 : Matrix (Fin N) (Fin N) (ZMod 2)) k l}
  mul_mem' {g h} hg hh k l hk := by
    simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    rw [mul_apply_of_row_eq_one (hg k · hk), hh k l hk]
  one_mem' _ _ _ := rfl
  inv_mem' {g} hg k l hk := by
    have h1 := congrFun (congrFun (coe_mul_inv_self hN g) k) l
    rwa [mul_apply_of_row_eq_one (hg k · hk)] at h1

@[expose] def Bm {N : ℕ} (hN : 2 ≤ N) : Subgroup (Ct N hN) where
  carrier := {g | ∀ k l : Fin N, l ≠ idxL hN →
    ((g : SL(N, ZMod 2)) : Matrix (Fin N) (Fin N) (ZMod 2)) k l =
      (1 : Matrix (Fin N) (Fin N) (ZMod 2)) k l}
  mul_mem' {g h} hg hh k l hl := by
    simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    rw [mul_apply_of_col_eq_one (hh · l hl), hg k l hl]
  one_mem' _ _ _ := rfl
  inv_mem' {g} hg k l hl := by
    have h1 := congrFun (congrFun (coe_inv_mul_self hN g) k) l
    rwa [mul_apply_of_col_eq_one (hg · l hl)] at h1

instance Am_normal {N : ℕ} (hN : 2 ≤ N) : (Am hN).Normal where
  conj_mem g hg h k l hk := by
    have hrow : ∀ m, ((((h * g : Ct N hN) : SL(N, ZMod 2)) :
        Matrix (Fin N) (Fin N) (ZMod 2))) k m = ((h : SL(N, ZMod 2)) :
          Matrix (Fin N) (Fin N) (ZMod 2)) k m := fun m => by
      simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      rw [Matrix.mul_apply, Finset.sum_congr rfl fun n _ => ?_, ← Matrix.mul_apply,
        Matrix.mul_one]
      by_cases hn : n = idx0 hN
      · rw [hn, Ct_apply_idx0, ite_eq_right hk, zero_mul, zero_mul]
      · rw [hg n m hn]
    have h1 := congrFun (congrFun (coe_mul_inv_self hN h) k) l
    simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at hrow ⊢
    rw [Matrix.mul_apply, Finset.sum_congr rfl fun m _ => by rw [hrow m], ← Matrix.mul_apply, h1]

instance Bm_normal {N : ℕ} (hN : 2 ≤ N) : (Bm hN).Normal where
  conj_mem g hg h k l hl := by
    have hcol : ∀ m, ((((g * h⁻¹ : Ct N hN) : SL(N, ZMod 2)) :
        Matrix (Fin N) (Fin N) (ZMod 2))) m l = (((h⁻¹ : Ct N hN) : SL(N, ZMod 2)) :
          Matrix (Fin N) (Fin N) (ZMod 2)) m l := fun m => by
      simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      rw [Matrix.mul_apply, Finset.sum_congr rfl fun n _ => ?_, ← Matrix.mul_apply,
        Matrix.one_mul]
      by_cases hn : n = idxL hN
      · rw [hn, Ct_idxL_apply, ite_eq_right hl, mul_zero, mul_zero]
      · rw [hg m n hn]
    have h1 := congrFun (congrFun (coe_mul_inv_self hN h) k) l
    simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at hcol h1 ⊢
    rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_congr rfl fun m _ => by rw [hcol m],
      ← Matrix.mul_apply, h1]

theorem one_midIdx_midIdx (i j : Fin (N - 2)) :
    (1 : Matrix (Fin N) (Fin N) (ZMod 2)) (midIdx i) (midIdx j) =
      (1 : Matrix (Fin (N - 2)) (Fin (N - 2)) (ZMod 2)) i j := by
  simp [Matrix.one_apply]

theorem qmat_mem_Am (a : Fin (N - 2) → ZMod 2) (c : ZMod 2) : qmat hN a 0 c ∈ Am hN := by
  intro k l hk
  rw [coe_qmat]
  rcases idx_cases hN k with rfl | rfl | ⟨i, rfl⟩
  · exact absurd rfl hk
  · rcases idx_cases hN l with rfl | rfl | ⟨j, rfl⟩ <;> simp
  · rcases idx_cases hN l with rfl | rfl | ⟨j, rfl⟩ <;> simp [one_midIdx_midIdx]

theorem qmat_mem_Bm (b : Fin (N - 2) → ZMod 2) (c : ZMod 2) : qmat hN 0 b c ∈ Bm hN := by
  intro k l hl
  rw [coe_qmat]
  rcases idx_cases hN l with rfl | rfl | ⟨j, rfl⟩
  · rcases idx_cases hN k with rfl | rfl | ⟨i, rfl⟩ <;> simp
  · exact absurd rfl hl
  · rcases idx_cases hN k with rfl | rfl | ⟨i, rfl⟩ <;> simp [one_midIdx_midIdx]

theorem Am_le_Qm {N : ℕ} (hN : 2 ≤ N) : Am hN ≤ Qm hN := fun _ hg =>
  (mem_Qm_iff hN).mpr fun i j => (hg _ _ (midIdx_ne_idx0 hN i)).trans (one_midIdx_midIdx i j)

theorem Bm_le_Qm {N : ℕ} (hN : 2 ≤ N) : Bm hN ≤ Qm hN := fun _ hg =>
  (mem_Qm_iff hN).mpr fun i j => (hg _ _ (midIdx_ne_idxL hN j)).trans (one_midIdx_midIdx i j)

theorem exists_qmat_of_mem_Am {g : Ct N hN} (hg : g ∈ Am hN) : ∃ a c, g = qmat hN a 0 c := by
  refine ⟨fun j => ((g : SL(N, ZMod 2)) : Matrix (Fin N) (Fin N) (ZMod 2)) (idx0 hN) (midIdx j),
    ((g : SL(N, ZMod 2)) : Matrix (Fin N) (Fin N) (ZMod 2)) (idx0 hN) (idxL hN),
    (eq_qmat_of_mem_Qm hN (Am_le_Qm hN hg)).trans ?_⟩
  congr 1
  exact funext fun i =>
    (hg _ _ (midIdx_ne_idx0 hN i)).trans (Matrix.one_apply_ne (midIdx_ne_idxL hN i))

theorem exists_qmat_of_mem_Bm {g : Ct N hN} (hg : g ∈ Bm hN) : ∃ b c, g = qmat hN 0 b c := by
  refine ⟨fun i => ((g : SL(N, ZMod 2)) : Matrix (Fin N) (Fin N) (ZMod 2)) (midIdx i) (idxL hN),
    ((g : SL(N, ZMod 2)) : Matrix (Fin N) (Fin N) (ZMod 2)) (idx0 hN) (idxL hN),
    (eq_qmat_of_mem_Qm hN (Bm_le_Qm hN hg)).trans ?_⟩
  congr 1
  exact funext fun j =>
    (hg _ _ (midIdx_ne_idxL hN j)).trans (Matrix.one_apply_ne (idx0_ne_midIdx hN j))

instance Am_isElementaryAbelian {N : ℕ} (hN : 2 ≤ N) : IsElementaryAbelian 2 (Am hN) where
  toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (by
    obtain ⟨a, c, hx⟩ := exists_qmat_of_mem_Am hN x.2
    obtain ⟨a', c', hy⟩ := exists_qmat_of_mem_Am hN y.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hx, hy]
    exact (qmat_mul_comm_iff hN _ _ _ _ _ _).mpr (by simp))⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
    obtain ⟨a, c, hx⟩ := exists_qmat_of_mem_Am hN x.2
    rw [Subgroup.coe_pow, hx, qmat_sq, dotProduct_zero, qmat_zero]
    rfl)

instance Bm_isElementaryAbelian {N : ℕ} (hN : 2 ≤ N) : IsElementaryAbelian 2 (Bm hN) where
  toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (by
    obtain ⟨b, c, hx⟩ := exists_qmat_of_mem_Bm hN x.2
    obtain ⟨b', c', hy⟩ := exists_qmat_of_mem_Bm hN y.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hx, hy]
    exact (qmat_mul_comm_iff hN _ _ _ _ _ _).mpr (by simp))⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
    obtain ⟨b, c, hx⟩ := exists_qmat_of_mem_Bm hN x.2
    rw [Subgroup.coe_pow, hx, qmat_sq, zero_dotProduct, qmat_zero]
    rfl)

theorem card_Am {N : ℕ} (hN : 2 ≤ N) : Nat.card (Am hN) = 2 ^ (N - 1) := by
  have hbij : Function.Bijective (fun x : (Fin (N - 2) → ZMod 2) × ZMod 2 =>
      (⟨qmat hN x.1 0 x.2, qmat_mem_Am hN _ _⟩ : Am hN)) := by
    refine ⟨fun x y h => ?_, fun g => ?_⟩
    · obtain ⟨h1, -, h3⟩ := qmat_injective hN (congrArg Subtype.val h)
      exact Prod.ext h1 h3
    · obtain ⟨a, c, hg⟩ := exists_qmat_of_mem_Am hN g.2
      exact ⟨(a, c), Subtype.ext hg.symm⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_prod, Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_succ]
  congr 1
  omega

theorem card_Bm {N : ℕ} (hN : 2 ≤ N) : Nat.card (Bm hN) = 2 ^ (N - 1) := by
  have hbij : Function.Bijective (fun x : (Fin (N - 2) → ZMod 2) × ZMod 2 =>
      (⟨qmat hN 0 x.1 x.2, qmat_mem_Bm hN _ _⟩ : Bm hN)) := by
    refine ⟨fun x y h => ?_, fun g => ?_⟩
    · obtain ⟨-, h2, h3⟩ := qmat_injective hN (congrArg Subtype.val h)
      exact Prod.ext h2 h3
    · obtain ⟨b, c, hg⟩ := exists_qmat_of_mem_Bm hN g.2
      exact ⟨(b, c), Subtype.ext hg.symm⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_prod, Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_succ]
  congr 1
  omega

theorem Am_inf_Bm {N : ℕ} (hN : 2 ≤ N) : Am hN ⊓ Bm hN = Subgroup.zpowers (tZero hN) := by
  ext g
  rw [Subgroup.mem_inf, mem_zpowers_tZero_iff]
  constructor
  · rintro ⟨hA, hB⟩
    obtain ⟨a, c, rfl⟩ := exists_qmat_of_mem_Am hN hA
    have ha : a = 0 := funext fun j => by
      have h1 := (hB (idx0 hN) (midIdx j) (midIdx_ne_idxL hN j)).trans
        (Matrix.one_apply_ne (idx0_ne_midIdx hN j))
      rwa [coe_qmat, qmatMat_idx0_midIdx] at h1
    subst ha
    exact qmat_zero_zero_eq hN c
  · rintro (rfl | rfl)
    · exact ⟨one_mem _, one_mem _⟩
    · rw [tZero_eq_qmat]
      exact ⟨qmat_mem_Am hN _ _, qmat_mem_Bm hN _ _⟩

end CFSG.LargeExtraspecial.DW.D73
