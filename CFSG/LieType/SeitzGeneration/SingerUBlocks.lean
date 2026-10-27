module

public import CFSG.LieType.SeitzGeneration.HeisTorusU85
public import CFSG.LieType.SeitzGeneration.OutdiagHeisGen

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped Fin.NatCast Fin.CommRing

variable {ℓ f : ℕ} {K : Type} [Field K]

section Monomial

variable {n : ℕ}

private theorem singerU_monomial_apply (σ : Equiv.Perm (Fin n)) (d : Fin n → K) (i j : Fin n) :
    (Equiv.Perm.permMatrix K σ * Matrix.diagonal d) i j = if σ i = j then d j else 0 := by
  rw [Matrix.mul_diagonal]
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, ite_mul]

private theorem singerU_monomial_rel_entry {σ : Equiv.Perm (Fin n)} {d : Fin n → K}
    {y y' : Matrix (Fin n) (Fin n) K}
    (hrel : y' * (Equiv.Perm.permMatrix K σ * Matrix.diagonal d) =
      (Equiv.Perm.permMatrix K σ * Matrix.diagonal d) * y) (i j : Fin n) :
    y' i j * d (σ j) = d (σ i) * y (σ i) (σ j) := by
  have h1 := congrFun (congrFun hrel i) (σ j)
  rw [Matrix.mul_apply, Matrix.mul_apply] at h1
  simp only [singerU_monomial_apply, σ.injective.eq_iff, ite_mul, mul_ite, mul_zero, zero_mul,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
  exact h1

private theorem singerU_monomial_block_iff {σ : Equiv.Perm (Fin n)} {d : Fin n → K}
    (hd : ∀ k, d k ≠ 0) {A B : Fin n} {y y' : Matrix (Fin n) (Fin n) K}
    (hrel : y' * (Equiv.Perm.permMatrix K σ * Matrix.diagonal d) =
      (Equiv.Perm.permMatrix K σ * Matrix.diagonal d) * y) :
    IsCoordBlockOn (σ.symm A) (σ.symm B) y' ↔ IsCoordBlockOn A B y := by
  constructor
  · intro hy' i j hij
    have E := singerU_monomial_rel_entry hrel (σ.symm i) (σ.symm j)
    simp only [Equiv.apply_symm_apply] at E
    have hc := hy' (σ.symm i) (σ.symm j)
      (by
        rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨fun e => h1 (σ.symm.injective e), fun e => h2 (σ.symm.injective e)⟩
        · exact Or.inr ⟨fun e => h1 (σ.symm.injective e), fun e => h2 (σ.symm.injective e)⟩)
    simp only [σ.symm.injective.eq_iff] at hc
    rw [hc] at E
    by_cases hij' : i = j
    · subst hij'
      rw [if_pos rfl] at E
      rw [if_pos rfl]
      apply mul_left_cancel₀ (hd i)
      linear_combination -E
    · rw [if_neg hij'] at E
      rw [if_neg hij']
      apply mul_left_cancel₀ (hd i)
      linear_combination -E
  · intro hy i j hij
    have E := singerU_monomial_rel_entry hrel i j
    have hc := hy (σ i) (σ j)
      (by
        rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨fun e => h1 ((σ.eq_symm_apply).2 e), fun e => h2 ((σ.eq_symm_apply).2 e)⟩
        · exact Or.inr ⟨fun e => h1 ((σ.eq_symm_apply).2 e), fun e => h2 ((σ.eq_symm_apply).2 e)⟩)
    simp only [σ.injective.eq_iff] at hc
    rw [hc] at E
    by_cases hij' : i = j
    · subst hij'
      rw [if_pos rfl] at E
      rw [if_pos rfl]
      apply mul_left_cancel₀ (hd (σ i))
      linear_combination E
    · rw [if_neg hij'] at E
      rw [if_neg hij']
      apply mul_left_cancel₀ (hd (σ j))
      linear_combination E

private theorem singerU_monomial_adj_mul (h : UnitaryFieldData ℓ f K) (σ : Equiv.Perm (Fin n))
    (d : Fin n → K) (hd : ∀ k, h.bar (d k) * d k = 1) :
    ug83_adj h (Equiv.Perm.permMatrix K σ * Matrix.diagonal d) *
      (Equiv.Perm.permMatrix K σ * Matrix.diagonal d) = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [ug83_adj_apply, singerU_monomial_apply, apply_ite h.bar, map_zero, Matrix.one_apply]
  rw [Finset.sum_eq_single (σ.symm i)]
  · by_cases hij : i = j
    · subst hij
      simp [hd i]
    · simp [hij]
  · intro k _ hk
    have hne : σ k ≠ i := fun e => hk (by rw [← e, Equiv.symm_apply_apply])
    simp [hne]
  · intro hk
    exact absurd (Finset.mem_univ _) hk

private def singerUWeyl (a b : Fin n) : Matrix (Fin n) (Fin n) K :=
  Equiv.Perm.permMatrix K (Equiv.swap a b) *
    Matrix.diagonal (fun k : Fin n => if k = b then (-1 : K) else 1)

private theorem singerUWeyl_det {a b : Fin n} (hab : a ≠ b) :
    (singerUWeyl a b : Matrix (Fin n) (Fin n) K).det = 1 := by
  unfold singerUWeyl
  rw [Matrix.det_mul, Matrix.det_permutation, Equiv.Perm.sign_swap hab, Matrix.det_diagonal]
  simp

private theorem singerUWeyl_isCoordBlockOn (a b : Fin n) :
    IsCoordBlockOn a b (singerUWeyl a b : Matrix (Fin n) (Fin n) K) := by
  intro i j hij
  unfold singerUWeyl
  rw [singerU_monomial_apply]
  have hkey : Equiv.swap a b i = j ↔ i = j := by
    rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
    · constructor
      · intro e
        have h3 : i = Equiv.swap a b j := by rw [← e, Equiv.swap_apply_self]
        rw [h3, Equiv.swap_apply_of_ne_of_ne h1 h2]
      · intro e
        rw [e, Equiv.swap_apply_of_ne_of_ne h1 h2]
  simp only [hkey]
  by_cases hij' : i = j
  · subst hij'
    have hib : i ≠ b := by
      rcases hij with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact h2
      · exact h2
    simp [hib]
  · simp [hij']

end Monomial

section Conj

variable {m : ℕ}

private theorem singerU_exists_unit (h : UnitaryFieldData ℓ f K)
    {M : Matrix (Fin m) (Fin m) K} (hM : ug83_adj h M * M = 1) :
    ∃ g : GL (Fin m) K, (g : Matrix (Fin m) (Fin m) K) = M ∧
      ((g⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = ug83_adj h M :=
  ⟨Units.mk M (ug83_adj h M) (mul_eq_one_comm.mp hM) hM, rfl, rfl⟩

private theorem singerU_adj_conj_one (h : UnitaryFieldData ℓ f K)
    {A B Y : Matrix (Fin m) (Fin m) K} (hAB : A * B = 1) (hA : ug83_adj h A * A = 1)
    (hY : ug83_adj h Y * Y = 1) : ug83_adj h (B * Y * A) * (B * Y * A) = 1 := by
  have hB : B = ug83_adj h A := by
    calc B = ug83_adj h A * A * B := by rw [hA, Matrix.one_mul]
      _ = ug83_adj h A * (A * B) := by rw [Matrix.mul_assoc]
      _ = ug83_adj h A := by rw [hAB, Matrix.mul_one]
  have hBa : ug83_adj h B = A := by rw [hB, ug83_adj_adj]
  rw [ug83_adj_mul, ug83_adj_mul, hBa]
  calc ug83_adj h A * (ug83_adj h Y * A) * (B * Y * A)
      = ug83_adj h A * (ug83_adj h Y * ((A * B) * (Y * A))) := by simp only [Matrix.mul_assoc]
    _ = ug83_adj h A * (ug83_adj h Y * (Y * A)) := by rw [hAB, Matrix.one_mul]
    _ = ug83_adj h A * ((ug83_adj h Y * Y) * A) := by simp only [Matrix.mul_assoc]
    _ = ug83_adj h A * A := by rw [hY, Matrix.one_mul]
    _ = 1 := hA

private theorem singerU_adj_conj_two (h : UnitaryFieldData ℓ f K)
    {A B Y : Matrix (Fin m) (Fin m) K} (hAB : A * B = 1) (hA : ug83_adj h A * A = 1)
    (hY : ug83_adj h Y * Y = 1) : ug83_adj h (A * Y * B) * (A * Y * B) = 1 := by
  have hB : B = ug83_adj h A := by
    calc B = ug83_adj h A * A * B := by rw [hA, Matrix.one_mul]
      _ = ug83_adj h A * (A * B) := by rw [Matrix.mul_assoc]
      _ = ug83_adj h A := by rw [hAB, Matrix.mul_one]
  have hBa : ug83_adj h B = A := by rw [hB, ug83_adj_adj]
  rw [ug83_adj_mul, ug83_adj_mul, hBa]
  calc A * (ug83_adj h Y * ug83_adj h A) * (A * Y * B)
      = A * (ug83_adj h Y * ((ug83_adj h A * A) * (Y * B))) := by simp only [Matrix.mul_assoc]
    _ = A * (ug83_adj h Y * (Y * B)) := by rw [hA, Matrix.one_mul]
    _ = A * ((ug83_adj h Y * Y) * B) := by simp only [Matrix.mul_assoc]
    _ = A * B := by rw [hY, Matrix.one_mul]
    _ = 1 := hAB

private theorem singerU_conj_mem (h : UnitaryFieldData ℓ f K) {g : GL (Fin m) K}
    (hg : ug83_adj h (g : Matrix (Fin m) (Fin m) K) * (g : Matrix (Fin m) (Fin m) K) = 1)
    {y : GL (Fin m) K} (hy : y ∈ unitarySU ℓ f K m) :
    g⁻¹ * y * g ∈ unitarySU ℓ f K m ∧ g * y * g⁻¹ ∈ unitarySU ℓ f K m := by
  obtain ⟨hYd, hYu⟩ := (mem_unitarySU_iff h).1 hy
  have hAB : (g : Matrix (Fin m) (Fin m) K) * ((g⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBA : ((g⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) * (g : Matrix (Fin m) (Fin m) K) =
      1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨(mem_unitarySU_iff h).2 ⟨?_, ?_⟩, (mem_unitarySU_iff h).2 ⟨?_, ?_⟩⟩
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hYd, mul_one,
      ← Matrix.det_mul, hBA, Matrix.det_one]
  · rw [Units.val_mul, Units.val_mul]
    exact singerU_adj_conj_one h hAB hg hYu
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hYd, mul_one,
      ← Matrix.det_mul, hAB, Matrix.det_one]
  · rw [Units.val_mul, Units.val_mul]
    exact singerU_adj_conj_two h hAB hg hYu

private theorem singerU_companion_adj_mul (h : UnitaryFieldData ℓ f K) {p : ℕ} {c : K}
    (hcu : h.bar c * c = 1) : ug83_adj h (companionMat p c) * companionMat p c = 1 := by
  unfold companionMat
  refine singerU_monomial_adj_mul h _ _ (fun j => ?_)
  by_cases hj : (j : ℕ) = p - 1 <;> simp [hj, hcu]

end Conj

private theorem singerU_finRotate_add_one {p : ℕ} [NeZero p] (x : Fin p) :
    finRotate p x = x + 1 :=
  finRotate_apply x

private theorem singerU_natCast_mul_ne {p : ℕ} [Fact p.Prime] [NeZero p] {m : ℕ} (hm0 : 0 < m)
    (hmp : m < p) {t : Fin p} (ht : t ≠ 0) : (m : Fin p) * t ≠ 0 := by
  intro e
  have h1 := congrArg (ZMod.finEquiv p) e
  rw [map_mul, map_natCast, map_zero] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · rw [ZMod.natCast_eq_zero_iff] at h2
    exact absurd (Nat.le_of_dvd hm0 h2) (by omega)
  · exact ht ((ZMod.finEquiv p).injective (by rw [h2, map_zero]))

private theorem singerU_exists_natCast_mul_eq {p : ℕ} [Fact p.Prime] [NeZero p] {δ t : Fin p}
    (hδ : δ ≠ 0) (ht : t ≠ 0) : ∃ m : ℕ, 0 < m ∧ m < p ∧ (m : Fin p) * δ = t := by
  have hδ' : ZMod.finEquiv p δ ≠ 0 :=
    fun h0 => hδ ((ZMod.finEquiv p).injective (by rw [h0, map_zero]))
  have ht' : ZMod.finEquiv p t ≠ 0 :=
    fun h0 => ht ((ZMod.finEquiv p).injective (by rw [h0, map_zero]))
  have hs0 : ZMod.finEquiv p t / ZMod.finEquiv p δ ≠ 0 := div_ne_zero ht' hδ'
  refine ⟨(ZMod.finEquiv p t / ZMod.finEquiv p δ).val, ?_, ZMod.val_lt _, ?_⟩
  · rcases Nat.eq_zero_or_pos (ZMod.finEquiv p t / ZMod.finEquiv p δ).val with h0 | h0
    · exact absurd ((ZMod.val_eq_zero _).1 h0) hs0
    · exact h0
  · apply (ZMod.finEquiv p).injective
    rw [map_mul, map_natCast, ZMod.natCast_zmod_val, div_mul_cancel₀ _ hδ']

private theorem singerU_ne_add {p : ℕ} [NeZero p] (x t : Fin p) (ht : t ≠ 0) : x ≠ x + t :=
  fun e => ht (by linear_combination (-1 : Fin p) * e)

theorem block_mem_of_block_mem_of_block_mem (h : UnitaryFieldData ℓ f K) {n : ℕ}
    (H : Subgroup (GL (Fin n) K)) {a b d : Fin n} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (h1 : ∀ y ∈ unitarySU ℓ f K n, IsCoordBlockOn a b (y : Matrix (Fin n) (Fin n) K) → y ∈ H)
    (h2 : ∀ y ∈ unitarySU ℓ f K n, IsCoordBlockOn b d (y : Matrix (Fin n) (Fin n) K) → y ∈ H) :
    ∀ y ∈ unitarySU ℓ f K n, IsCoordBlockOn a d (y : Matrix (Fin n) (Fin n) K) → y ∈ H := by
  intro y hy hblk
  have hd : ∀ k : Fin n, (fun k : Fin n => if k = b then (-1 : K) else 1) k ≠ 0 := by
    intro k
    dsimp only
    split_ifs <;> norm_num
  have hWd : ∀ k : Fin n, h.bar ((fun k : Fin n => if k = b then (-1 : K) else 1) k) *
      (fun k : Fin n => if k = b then (-1 : K) else 1) k = 1 := by
    intro k
    dsimp only
    split_ifs <;> simp
  have hWadj : ug83_adj h (singerUWeyl a b) * singerUWeyl a b = 1 :=
    singerU_monomial_adj_mul h (Equiv.swap a b) (fun k : Fin n => if k = b then (-1 : K) else 1) hWd
  obtain ⟨ω, hω, hωi⟩ := singerU_exists_unit h hWadj
  have hωSU : ω ∈ unitarySU ℓ f K n := by
    refine (mem_unitarySU_iff h).2 ⟨?_, ?_⟩
    · rw [hω]
      exact singerUWeyl_det hab
    · rw [hω]
      exact hWadj
  have hωH : ω ∈ H := h1 ω hωSU (by rw [hω]; exact singerUWeyl_isCoordBlockOn a b)
  have hyc := (singerU_conj_mem h (g := ω) (by rw [hω]; exact hWadj) hy).2
  have hrel : ((ω * y * ω⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * singerUWeyl a b =
      singerUWeyl a b * (y : Matrix (Fin n) (Fin n) K) := by
    rw [Units.val_mul, Units.val_mul, hω, hωi]
    simp only [Matrix.mul_assoc, hWadj, Matrix.mul_one]
  have hbl : IsCoordBlockOn b d ((ω * y * ω⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have key := (singerU_monomial_block_iff (σ := Equiv.swap a b)
      (d := fun k : Fin n => if k = b then (-1 : K) else 1) hd (A := a) (B := d) hrel).2 hblk
    simpa only [Equiv.symm_swap, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm] using key
  have hyH := h2 _ hyc hbl
  have hconj : y = ω⁻¹ * (ω * y * ω⁻¹) * ω := by group
  rw [hconj]
  exact mul_mem (mul_mem (inv_mem hωH) hyH) hωH

theorem unitarySU_le_of_companion_blocks (h : UnitaryFieldData ℓ f K) (hq : 4 ≤ ℓ ^ f)
    {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) {c : K} (hc : c ≠ 0) (hcu : h.bar c * c = 1)
    (H : Subgroup (GL (Fin p) K))
    (hC : ∀ g ∈ H, ∀ g' : GL (Fin p) K,
      (g' : Matrix (Fin p) (Fin p) K) * companionMat p c = companionMat p c * g → g' ∈ H)
    {a b : Fin p} (hab : a ≠ b)
    (hH : ∀ y ∈ unitarySU ℓ f K p, IsCoordBlockOn a b (y : Matrix (Fin p) (Fin p) K) → y ∈ H) :
    unitarySU ℓ f K p ≤ H := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨g, hg, -⟩ := singerU_exists_unit h (singerU_companion_adj_mul (p := p) h hcu)
  have hgU : ug83_adj h (g : Matrix (Fin p) (Fin p) K) * (g : Matrix (Fin p) (Fin p) K) = 1 := by
    rw [hg]
    exact singerU_companion_adj_mul (p := p) h hcu
  have hd : ∀ j : Fin p, (fun j : Fin p => if (j : ℕ) = p - 1 then c else 1) j ≠ 0 := by
    intro j
    dsimp only
    split_ifs <;> simp [hc]
  obtain ⟨δ, hδ⟩ : ∃ δ : Fin p, δ = b - a := ⟨_, rfl⟩
  have hδ0 : δ ≠ 0 := by
    rw [hδ]
    exact sub_ne_zero.2 (Ne.symm hab)
  have hA : ∀ k : ℕ, ∀ y ∈ unitarySU ℓ f K p,
      IsCoordBlockOn (a + (k : Fin p)) (a + (k : Fin p) + δ) (y : Matrix (Fin p) (Fin p) K) →
        y ∈ H := by
    intro k
    induction k with
    | zero =>
      intro y hy hblk
      have e0 : a + ((0 : ℕ) : Fin p) = a := by simp
      have e1 : a + δ = b := by
        rw [hδ]
        ring
      rw [e0, e1] at hblk
      exact hH y hy hblk
    | succ k ih =>
      intro y hy hblk
      have hrel : (y : Matrix (Fin p) (Fin p) K) * companionMat p c =
          companionMat p c * (((g⁻¹ * y * g : GL (Fin p) K)) : Matrix (Fin p) (Fin p) K) := by
        have key : g * (g⁻¹ * y * g) = y * g := by group
        have key' := congrArg (fun x : GL (Fin p) K => (x : Matrix (Fin p) (Fin p) K)) key
        simp only [Units.val_mul] at key'
        rw [← hg]
        simp only [Units.val_mul]
        exact key'.symm
      have hzU : g⁻¹ * y * g ∈ unitarySU ℓ f K p := (singerU_conj_mem h hgU hy).1
      have hblk' : IsCoordBlockOn (a + (k : Fin p)) (a + (k : Fin p) + δ)
          ((g⁻¹ * y * g : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) := by
        have e2 : (finRotate p).symm.symm (a + (k : Fin p)) = a + ((k + 1 : ℕ) : Fin p) := by
          rw [Equiv.symm_symm, singerU_finRotate_add_one, Nat.cast_succ]
          ring
        have e3 : (finRotate p).symm.symm (a + (k : Fin p) + δ) =
            a + ((k + 1 : ℕ) : Fin p) + δ := by
          rw [Equiv.symm_symm, singerU_finRotate_add_one, Nat.cast_succ]
          ring
        have hblk'' : IsCoordBlockOn ((finRotate p).symm.symm (a + (k : Fin p)))
            ((finRotate p).symm.symm (a + (k : Fin p) + δ))
            (y : Matrix (Fin p) (Fin p) K) := by
          rw [e2, e3]
          exact hblk
        exact (singerU_monomial_block_iff (σ := (finRotate p).symm)
          (d := fun j : Fin p => if (j : ℕ) = p - 1 then c else 1) hd
          (A := a + (k : Fin p)) (B := a + (k : Fin p) + δ) hrel).1 hblk''
      exact hC _ (ih _ hzU hblk') y hrel
  have hB : ∀ x : Fin p, ∀ y ∈ unitarySU ℓ f K p,
      IsCoordBlockOn x (x + δ) (y : Matrix (Fin p) (Fin p) K) → y ∈ H := by
    intro x y hy hblk
    have hx : a + (((x - a : Fin p) : ℕ) : Fin p) = x := by
      rw [Fin.cast_val_eq_self]
      ring
    have key := hA ((x - a : Fin p) : ℕ) y hy
    rw [hx] at key
    exact key hblk
  have hC' : ∀ m : ℕ, 1 ≤ m → m < p → ∀ x : Fin p, ∀ y ∈ unitarySU ℓ f K p,
      IsCoordBlockOn x (x + (m : Fin p) * δ) (y : Matrix (Fin p) (Fin p) K) → y ∈ H := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      intro _ x y hy hblk
      rw [Nat.cast_one, one_mul] at hblk
      exact hB x y hy hblk
    | succ m hm ih =>
      intro hmp x y hy hblk
      have hm_ne : (m : Fin p) * δ ≠ 0 := singerU_natCast_mul_ne (by omega) (by omega) hδ0
      have hm1_ne : ((m + 1 : ℕ) : Fin p) * δ ≠ 0 :=
        singerU_natCast_mul_ne (Nat.succ_pos m) hmp hδ0
      have hsplit : x + ((m + 1 : ℕ) : Fin p) * δ = (x + (m : Fin p) * δ) + δ := by
        push_cast
        ring
      have h1 : ∀ y' ∈ unitarySU ℓ f K p,
          IsCoordBlockOn x (x + (m : Fin p) * δ) (y' : Matrix (Fin p) (Fin p) K) → y' ∈ H :=
        fun y' hy' hb => ih (by omega) x y' hy' hb
      have h2 : ∀ y' ∈ unitarySU ℓ f K p,
          IsCoordBlockOn (x + (m : Fin p) * δ) (x + ((m + 1 : ℕ) : Fin p) * δ)
            (y' : Matrix (Fin p) (Fin p) K) → y' ∈ H :=
        fun y' hy' hb => hB _ y' hy' (by rw [hsplit] at hb; exact hb)
      have hbd : x + (m : Fin p) * δ ≠ x + ((m + 1 : ℕ) : Fin p) * δ := by
        rw [hsplit]
        exact singerU_ne_add _ _ hδ0
      exact block_mem_of_block_mem_of_block_mem h H (singerU_ne_add _ _ hm_ne)
        (singerU_ne_add _ _ hm1_ne) hbd h1 h2 y hy hblk
  have hE : ∀ x z : Fin p, x ≠ z → ∀ y ∈ unitarySU ℓ f K p,
      IsCoordBlockOn x z (y : Matrix (Fin p) (Fin p) K) → y ∈ H := by
    intro x z hxz y hy hblk
    obtain ⟨m, hm0, hmp, hmd⟩ := singerU_exists_natCast_mul_eq hδ0
      (sub_ne_zero.2 (Ne.symm hxz))
    have hz : x + (m : Fin p) * δ = z := by
      rw [hmd]
      ring
    exact hC' m hm0 hmp x y hy (by rw [hz]; exact hblk)
  exact unitarySU_le_of_blocks h hq (by omega) H
    (fun a' b' hne y hy hblk => hE a' b' hne y hy hblk)

theorem eq_unitarySU_of_fixer_companion (h : UnitaryFieldData ℓ f K)
    {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hpq : p ∣ ℓ ^ f + 1) {c : K} (hc : c ≠ 0)
    (hcu : h.bar c * c = 1)
    (H : Subgroup (GL (Fin p) K)) (hHU : H ≤ unitarySU ℓ f K p)
    (hT : ∀ g ∈ unitarySU ℓ f K p, (∃ t, (g : Matrix (Fin p) (Fin p) K) = diagonal t) → g ∈ H)
    (hC : ∀ g ∈ H, ∀ g' : GL (Fin p) K,
      (g' : Matrix (Fin p) (Fin p) K) * companionMat p c = companionMat p c * g → g' ∈ H)
    (hfix : ∃ g ∈ H, (∀ i, i ≠ 0 → (g : Matrix (Fin p) (Fin p) K) i 0 = 0) ∧
      ¬ IsMonomialMat (g : Matrix (Fin p) (Fin p) K)) :
    H = unitarySU ℓ f K p := by
  obtain ⟨hq, he⟩ := ug85_bounds hp hpq
  refine le_antisymm hHU ?_
  have hplane : ∃ a b : Fin p, a ≠ b ∧ ∀ y ∈ unitarySU ℓ f K p,
      IsCoordBlockOn a b (y : Matrix (Fin p) (Fin p) K) → y ∈ H := by
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
    obtain ⟨g, hgH, hg0, hgm⟩ := hfix
    obtain ⟨a, b, hab, hblk⟩ := ug85_core h hq he (by omega) H hHU hT
      ⟨g, hgH, fun i => hg0 i.succ (Fin.succ_ne_zero i), hgm⟩
    exact ⟨a.succ, b.succ, fun e => hab (Fin.succ_injective _ e), hblk⟩
  obtain ⟨a, b, hab, hplaneH⟩ := hplane
  exact unitarySU_le_of_companion_blocks h hq hp hc hcu H hC hab hplaneH

end CFSG.LieType.SeitzGeneration
