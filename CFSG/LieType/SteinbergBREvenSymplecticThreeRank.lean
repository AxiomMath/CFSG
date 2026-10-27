module

public import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.Open.StatedAPI

public section

namespace CFSG.LieType.SteinbergBR.EvenSp

open Matrix CFSG.Assembly.LowTwoRank

section Blocks

variable {K : Type*} [CommRing K] {n : ℕ}

@[expose] def planeMat (h : Fin n → Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  fromBlocks (diagonal fun j => h j 0 0) (diagonal fun j => h j 0 1)
    (diagonal fun j => h j 1 0) (diagonal fun j => h j 1 1)

theorem planeMat_mul (h h' : Fin n → Matrix (Fin 2) (Fin 2) K) :
    planeMat h * planeMat h' = planeMat fun j => h j * h' j := by
  simp only [planeMat, fromBlocks_multiply, diagonal_mul_diagonal, diagonal_add, Matrix.mul_apply,
    Fin.sum_univ_two]

theorem planeMat_one : planeMat (n := n) (fun _ => (1 : Matrix (Fin 2) (Fin 2) K)) = 1 := by
  simp only [planeMat, one_apply_eq, one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), diagonal_zero]
  exact fromBlocks_one

theorem planeMat_transpose (h : Fin n → Matrix (Fin 2) (Fin 2) K) :
    (planeMat h)ᵀ = planeMat fun j => (h j)ᵀ := by
  simp only [planeMat, fromBlocks_transpose, diagonal_transpose, transpose_apply]

theorem planeMat_gram :
    planeMat (n := n) (fun _ => !![(0 : K), 1; -1, 0]) = fromBlocks 0 1 (-1) 0 := by
  simp only [planeMat, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one, diagonal_zero, diagonal_one]
  rw [show (diagonal fun _ => (-1 : K) : Matrix (Fin n) (Fin n) K) = -1 by
    rw [← diagonal_one, diagonal_neg]]

theorem planeMat_injective : Function.Injective (planeMat (K := K) (n := n)) := by
  intro h h' hh
  funext j
  ext a b
  fin_cases a <;> fin_cases b
  · simpa [planeMat] using congrFun₂ hh (Sum.inl j) (Sum.inl j)
  · simpa [planeMat] using congrFun₂ hh (Sum.inl j) (Sum.inr j)
  · simpa [planeMat] using congrFun₂ hh (Sum.inr j) (Sum.inl j)
  · simpa [planeMat] using congrFun₂ hh (Sum.inr j) (Sum.inr j)

theorem transpose_mul_gram_two_mul (A : Matrix (Fin 2) (Fin 2) K) :
    Aᵀ * !![0, 1; -1, 0] * A = A.det • !![(0 : K), 1; -1, 0] := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : K, A = !![a, b; c, d] := ⟨_, _, _, _, eta_fin_two A⟩
  rw [det_fin_two_of]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem planeMat_symplectic (h : Fin n → Matrix (Fin 2) (Fin 2) K) (hdet : ∀ j, (h j).det = 1) :
    (planeMat h)ᵀ * fromBlocks 0 1 (-1) 0 * planeMat h = fromBlocks 0 1 (-1) 0 := by
  rw [planeMat_transpose, ← planeMat_gram, planeMat_mul, planeMat_mul]
  congr 1
  funext j
  rw [transpose_mul_gram_two_mul, hdet, one_smul]

end Blocks

variable {K : Type} [Field K] {n : ℕ}

@[expose] def planeHom : (Fin n → GL (Fin 2) K) →* GL (Fin n ⊕ Fin n) K where
  toFun g := ⟨planeMat fun j => (g j : Matrix (Fin 2) (Fin 2) K),
    planeMat fun j => ((g j)⁻¹ : GL (Fin 2) K), by
      rw [planeMat_mul]
      simp only [Units.mul_inv]
      exact planeMat_one, by
      rw [planeMat_mul]
      simp only [Units.inv_mul]
      exact planeMat_one⟩
  map_one' := Units.ext (by
    change planeMat (fun _ => ((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = 1
    exact planeMat_one)
  map_mul' g g' := Units.ext (by
    change planeMat (fun j => ((g j * g' j : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) =
      planeMat (fun j => (g j : Matrix (Fin 2) (Fin 2) K)) *
        planeMat (fun j => (g' j : Matrix (Fin 2) (Fin 2) K))
    rw [planeMat_mul]
    rfl)

theorem planeHom_val (g : Fin n → GL (Fin 2) K) :
    ((planeHom g : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      planeMat fun j => (g j : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem planeHom_injective : Function.Injective (planeHom (K := K) (n := n)) := by
  intro g g' hg
  have := planeMat_injective (congrArg (fun x : GL (Fin n ⊕ Fin n) K =>
    (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) hg)
  funext j
  exact Units.ext (congrFun this j)

theorem mem_statedSp_iff' {g : GL (Fin n ⊕ Fin n) K} :
    g ∈ StatedSp n K ↔ (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * fromBlocks 0 1 (-1) 0 *
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = fromBlocks 0 1 (-1) 0 :=
  CFSG.Open.StatedAPI.mem_statedSp_iff

theorem planeHom_mem_statedSp (g : Fin n → GL (Fin 2) K)
    (hg : ∀ j, (g j : Matrix (Fin 2) (Fin 2) K).det = 1) : planeHom g ∈ StatedSp n K := by
  rw [mem_statedSp_iff', planeHom_val]
  exact planeMat_symplectic _ hg

variable [CharP K 2]

theorem statedScalars_subgroupOf_statedSp (hn : 1 ≤ n) :
    (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  obtain ⟨c, hc⟩ := hx
  have hmem : (c : K) ^ 2 = 1 := by
    have h := x.2
    rw [← hc, CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic,
      TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup, Matrix.GeneralLinearGroup.coe_scalar,
      CFSG.ClassicalGroups.Symplectic.scalar_mem_symplecticGroup_iff hn] at h
    exact h
  have hc1 : (c : K) = 1 := by
    have h := sub_pow_char (p := 2) (c : K) 1
    rw [hmem, one_pow, sub_self] at h
    exact sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [OneMemClass.coe_one, ← hc, show c = 1 from Units.ext hc1, map_one]

@[expose] noncomputable def projEquiv (hn : 1 ≤ n) : StatedProj (StatedSp n K) ≃* StatedSp n K :=
  (QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_statedSp hn)).trans
    QuotientGroup.quotientBot

@[expose] def tGL : GL (Fin 2) K :=
  ⟨!![0, 1; 1, 1], !![1, 1; 1, 0], by
    rw [mul_fin_two, one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero], by
    rw [mul_fin_two, one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]⟩

theorem det_tGL : ((tGL (K := K) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  change (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) K).det = 1
  rw [det_fin_two_of, zero_mul, one_mul, zero_sub, CharTwo.neg_eq]

theorem tGL_pow_three : tGL (K := K) ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, pow_succ, sq]
  change !![0, 1; 1, 1] * !![0, 1; 1, 1] * !![0, 1; 1, 1] = (1 : Matrix (Fin 2) (Fin 2) K)
  rw [mul_fin_two, mul_fin_two, one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]

theorem tGL_ne_one : tGL (K := K) ≠ 1 := by
  intro h
  have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [tGL] at this

theorem orderOf_tGL : orderOf (tGL (K := K)) = 3 := orderOf_eq_prime tGL_pow_three tGL_ne_one

theorem det_of_mem_zpowers {g : GL (Fin 2) K} (hg : g ∈ Subgroup.zpowers (tGL (K := K))) :
    (g : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  rw [← Matrix.GeneralLinearGroup.val_det_apply, map_zpow]
  have : Matrix.GeneralLinearGroup.det (tGL (K := K)) = 1 := Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_det_apply, det_tGL, Units.val_one])
  rw [this, _root_.one_zpow, Units.val_one]

@[expose] noncomputable def torusHom (hn : 1 ≤ n) :
    (Fin n → Subgroup.zpowers (tGL (K := K))) →* StatedProj (StatedSp n K) :=
  (projEquiv hn).symm.toMonoidHom.comp
    ((planeHom.comp (MonoidHom.compLeft (Subgroup.zpowers tGL).subtype (Fin n))).codRestrict
      (StatedSp n K) fun x => planeHom_mem_statedSp _ fun j => det_of_mem_zpowers (x j).2)

theorem torusHom_injective (hn : 1 ≤ n) : Function.Injective (torusHom (K := K) hn) := by
  intro x y hxy
  have h1 := (projEquiv hn).symm.injective hxy
  have h2 := planeHom_injective (congrArg Subtype.val h1)
  funext j
  exact Subtype.ext (congrFun h2 j)

theorem isElementaryAbelian_range {G H : Type*} [Group G] [Group H] {p : ℕ} (f : G →* H)
    (hcomm : ∀ x y : G, x * y = y * x) (hp : ∀ x : G, x ^ p = 1) :
    IsElementaryAbelian p f.range where
  is_comm := ⟨fun a b => by
    obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    apply Subtype.ext
    change (a : H) * b = b * a
    rw [← hx, ← hy, ← map_mul, ← map_mul, hcomm]⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
    obtain ⟨x, hx⟩ := a.2
    apply Subtype.ext
    change (a : H) ^ p = 1
    rw [← hx, ← map_pow, hp, map_one]

end CFSG.LieType.SteinbergBR.EvenSp

namespace CFSG.LieType

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.SteinbergBR CFSG.LieType.SteinbergBR.EvenSp

theorem unique_even_symplectic_prime_field_three_rank {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 1 ≤ n) :
    (∃ A : Subgroup (StatedProj (StatedSp n K)), IsElementaryAbelian 3 A ∧ Nat.card A = 3 ^ n) ∧
    (CFSG.IsStronglyQuasithin (StatedProj (StatedSp n K)) → n ≤ 2) := by
  have hA : IsElementaryAbelian 3 (torusHom (K := K) hn).range :=
    isElementaryAbelian_range _ (fun x y => funext fun j => Subtype.ext
      (by
        obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 (x j).2
        obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.1 (y j).2
        change ((x j : GL (Fin 2) K)) * (y j) = (y j) * (x j)
        rw [← ha, ← hb, ← _root_.zpow_add, ← _root_.zpow_add, add_comm]))
      fun x => funext fun j => Subtype.ext (by
        obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 (x j).2
        change ((x j : GL (Fin 2) K)) ^ 3 = 1
        rw [← ha, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
          tGL_pow_three, _root_.one_zpow])
  have hcard : Nat.card (torusHom (K := K) hn).range = 3 ^ n := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (torusHom_injective hn)).toEquiv, Nat.card_fun,
      Nat.card_zpowers, orderOf_tGL, Nat.card_fin]
  refine ⟨⟨_, hA, hcard⟩, fun hSQT => ?_⟩
  have hle := le_pRank_of_card (by norm_num) _ hA hcard
  exact hle.trans (hSQT 3 Nat.prime_three (by norm_num))

end CFSG.LieType
