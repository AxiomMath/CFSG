module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UbGen
public import CFSG.GH74.GLS.Stage2.OddAut.LinNEig
public import CFSG.GH74.GLS.Stage2.OddAut.ElemAbBasis

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Ub

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.GH74.GLS.Stage2.OddAut

variable {K : Type*} [Field K] {σ : K ≃+* K} {n r : ℕ}

@[expose] def bcol (B : Matrix (Fin n) (Fin n) K) (k : Fin n) : Fin n → K := fun i => B i k

structure WtBasis (σ : K ≃+* K) (n : ℕ) (a b : SUid σ n) where
  B : Matrix (Fin n) (Fin n) K
  da : Fin n → K
  db : Fin n → K
  hB : IsUnit B.det
  ha : ∀ k, a • bcol B k = da k • bcol B k
  hb : ∀ k, b • bcol B k = db k • bcol B k

theorem smul_bcol_of_mul_eq {a : SUid σ n} {B : Matrix (Fin n) (Fin n) K} {d : Fin n → K}
    (h : ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * B = B * Matrix.diagonal d) (k : Fin n) :
    a • bcol B k = d k • bcol B k := by
  funext i
  have h1 := congrFun (congrFun h i) k
  rw [Matrix.mul_diagonal] at h1
  have h2 : (a • bcol B k) i = (((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * B) i k := by
    rw [Matrix.mul_apply]
    rfl
  rw [h2, h1]
  simp only [bcol, Pi.smul_apply, smul_eq_mul]
  ring

theorem exists_wtBasis (hr : 0 < r) {ξ : K} (hξ : IsPrimitiveRoot ξ r) (a b : SUid σ n)
    (hab : a * b = b * a) (ha : a ^ r = 1) (hb : b ^ r = 1) : Nonempty (WtBasis σ n a b) := by
  have hmat : ∀ x : SUid σ n, x ^ r = 1 →
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ r = 1 := by
    intro x hx
    have := congrArg (fun y : SUid σ n => ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hx
    simpa [Units.val_pow_eq_pow_val] using this
  have hcomm : ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have := congrArg (fun y : SUid σ n => ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hab
    simpa using this
  obtain ⟨B, da, db, hB, hAB, hBB⟩ := exists_joint_eigenbasis_n hr hξ _ _ (hmat a ha) (hmat b hb)
    hcomm
  exact ⟨⟨B, da, db, hB, smul_bcol_of_mul_eq hAB, smul_bcol_of_mul_eq hBB⟩⟩

namespace WtBasis

variable {a b : SUid σ n} (W : WtBasis σ n a b)

theorem bcol_ne_zero (k : Fin n) : bcol W.B k ≠ 0 := by
  intro h0
  have hinj : Function.Injective W.B.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det W.B).2 W.hB)
  have h1 : W.B.mulVec (Pi.single k 1) = bcol W.B k := by
    funext i
    simp [bcol]
  have h2 : W.B.mulVec (Pi.single k 1) = W.B.mulVec 0 := by
    rw [h1, h0, Matrix.mulVec_zero]
  have h3 := hinj h2
  have := congrFun h3 k
  simp at this

theorem span (y : Fin n → K) : ∃ c : Fin n → K, y = ∑ k, c k • bcol W.B k := by
  have hinj : Function.Surjective W.B.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det W.B).2 W.hB)
  obtain ⟨c, hc⟩ := hinj y
  refine ⟨c, ?_⟩
  rw [← hc]
  funext i
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, bcol]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

end WtBasis


theorem pow_smul_of_smul_eq {x : SUid σ n} {v : Fin n → K} {c : K} (h : x • v = c • v) (m : ℕ) :
    x ^ m • v = c ^ m • v := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, mul_smul, h, smul_comm, ih, smul_smul, pow_succ, mul_comm]

namespace WtBasis

variable {a b : SUid σ n} (W : WtBasis σ n a b)

theorem eq_one_of_fix {x : SUid σ n} (hx : ∀ k, x • bcol W.B k = bcol W.B k) : x = 1 := by
  apply ext_smul
  intro v
  obtain ⟨c, rfl⟩ := W.span v
  rw [one_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_comm, hx]

theorem da_pow (ha : a ^ r = 1) (k : Fin n) : W.da k ^ r = 1 := by
  have h1 := pow_smul_of_smul_eq (W.ha k) r
  rw [ha, one_smul] at h1
  have h2 : (W.da k ^ r - 1) • bcol W.B k = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
  rcases smul_eq_zero.1 h2 with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h (W.bcol_ne_zero k)

theorem db_pow (hb : b ^ r = 1) (k : Fin n) : W.db k ^ r = 1 := by
  have h1 := pow_smul_of_smul_eq (W.hb k) r
  rw [hb, one_smul] at h1
  have h2 : (W.db k ^ r - 1) • bcol W.B k = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
  rcases smul_eq_zero.1 h2 with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h (W.bcol_ne_zero k)

theorem wt_orth (ha : a ^ r = 1) (hb : b ^ r = 1) (hσq : ∀ u : K, u ^ r = 1 → σ u = u)
    {k l : Fin n} (h : herm σ (bcol W.B k) (bcol W.B l) ≠ 0) :
    W.da k * W.da l = 1 ∧ W.db k * W.db l = 1 := by
  constructor
  · have h1 := herm_smul_smul σ a (bcol W.B k) (bcol W.B l)
    rw [W.ha k, W.ha l, herm_smul_left, herm_smul_right, hσq _ (W.da_pow ha k)] at h1
    have h2 : (W.da k * W.da l - 1) * herm σ (bcol W.B k) (bcol W.B l) = 0 := by
      linear_combination h1
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact sub_eq_zero.1 h3
    · exact absurd h3 h
  · have h1 := herm_smul_smul σ b (bcol W.B k) (bcol W.B l)
    rw [W.hb k, W.hb l, herm_smul_left, herm_smul_right, hσq _ (W.db_pow hb k)] at h1
    have h2 : (W.db k * W.db l - 1) * herm σ (bcol W.B k) (bcol W.B l) = 0 := by
      linear_combination h1
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact sub_eq_zero.1 h3
    · exact absurd h3 h

theorem exists_partner (k : Fin n) : ∃ l, herm σ (bcol W.B k) (bcol W.B l) ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_herm_ne_zero σ (W.bcol_ne_zero k)
  obtain ⟨c, rfl⟩ := W.span y
  by_contra hcon
  push Not at hcon
  apply hy
  have : herm σ (bcol W.B k) (∑ l, c l • bcol W.B l) =
      ∑ l, c l * herm σ (bcol W.B k) (bcol W.B l) := by
    rw [← hermL_apply, map_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [map_smul, hermL_apply, smul_eq_mul]
  rw [this]
  exact Finset.sum_eq_zero fun l _ => by rw [hcon l, mul_zero]

end WtBasis


theorem exists_exps {α β : K} (hr : r.Prime) (hα : α ^ r = 1) (hβ : β ^ r = 1) :
    ∃ I J : ℕ, ¬ (r ∣ I ∧ r ∣ J) ∧ α ^ I * β ^ J = 1 := by
  classical
  have hr0 : 0 < r := hr.pos
  set S : Finset K := Polynomial.nthRootsFinset r (1 : K) with hS
  have hSc : S.card ≤ r := by
    rw [hS]
    unfold Polynomial.nthRootsFinset
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots r 1)
  let ψ : Fin r × Fin r → K := fun p => α ^ (p.1 : ℕ) * β ^ (p.2 : ℕ)
  have hmaps : Set.MapsTo ψ ((Finset.univ : Finset (Fin r × Fin r)) : Set (Fin r × Fin r))
      (S : Set K) := by
    intro p _
    rw [Finset.mem_coe, hS, Polynomial.mem_nthRootsFinset hr0]
    simp only [ψ]
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (p.1 : ℕ) r, mul_comm (p.2 : ℕ) r, pow_mul,
      pow_mul, hα, hβ]
    simp
  have hcard : S.card < (Finset.univ : Finset (Fin r × Fin r)).card := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    have := hr.two_le
    nlinarith
  obtain ⟨p, -, q, -, hne, hpq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  obtain ⟨i, j⟩ := p
  obtain ⟨i', j'⟩ := q
  simp only [ψ] at hpq
  refine ⟨(i : ℕ) + (r - i'), (j : ℕ) + (r - j'), ?_, ?_⟩
  · rintro ⟨h1, h2⟩
    apply hne
    have e1 := eq_of_dvd_add_sub' i.2 i'.2 h1
    have e2 := eq_of_dvd_add_sub' j.2 j'.2 h2
    rw [Fin.ext e1, Fin.ext e2]
  · calc α ^ ((i : ℕ) + (r - i')) * β ^ ((j : ℕ) + (r - j'))
        = (α ^ (i : ℕ) * β ^ (j : ℕ)) * (α ^ (r - i') * β ^ (r - j')) := by
          rw [pow_add, pow_add]; ring
      _ = (α ^ (i' : ℕ) * β ^ (j' : ℕ)) * (α ^ (r - i') * β ^ (r - j')) := by rw [hpq]
      _ = α ^ ((i' : ℕ) + (r - i')) * β ^ ((j' : ℕ) + (r - j')) := by
          rw [pow_add, pow_add]; ring
      _ = 1 := by
          rw [Nat.add_sub_cancel' i'.2.le, Nat.add_sub_cancel' j'.2.le, hα, hβ, one_mul]

namespace WtBasis

variable {a b : SUid σ n} (W : WtBasis σ n a b)

theorem exists_k1 (hr : r.Prime) (ha : a ^ r = 1) (hb : b ^ r = 1)
    (hind : ∀ i j : ℕ, a ^ i * b ^ j = 1 → r ∣ i ∧ r ∣ j) (k₀ : Fin n) :
    ∃ k₁ : Fin n, ∀ m : ℕ, ¬ (W.da k₁ = W.da k₀ ^ m ∧ W.db k₁ = W.db k₀ ^ m) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨I, J, hIJ, hα⟩ := exists_exps hr (W.da_pow ha k₀) (W.db_pow hb k₀)
  apply hIJ
  apply hind I J
  apply W.eq_one_of_fix
  intro k
  obtain ⟨m, hm1, hm2⟩ := hcon k
  rw [mul_smul, pow_smul_of_smul_eq (W.hb k) J, smul_comm (a ^ I), pow_smul_of_smul_eq (W.ha k) I,
    smul_smul, hm1, hm2]
  have : (W.db k₀ ^ m) ^ J * (W.da k₀ ^ m) ^ I = 1 := by
    rw [mul_comm, ← pow_mul, ← pow_mul, mul_comm m I, mul_comm m J, pow_mul, pow_mul, ← mul_pow,
      hα, one_pow]
  rw [this, one_smul]

theorem exists_k0 (hind : ∀ i j : ℕ, a ^ i * b ^ j = 1 → r ∣ i ∧ r ∣ j)
    (hr : r.Prime) : ∃ k₀ : Fin n, ¬ (W.da k₀ = 1 ∧ W.db k₀ = 1) := by
  by_contra hcon
  push Not at hcon
  have h1 : a = 1 := by
    apply W.eq_one_of_fix
    intro k
    rw [W.ha k, (hcon k).1, one_smul]
  have := hind 1 0 (by rw [h1]; simp)
  exact hr.one_lt.ne' (Nat.dvd_one.1 this.1)

end WtBasis


theorem sq_eq_one_of_pow {u : K} (hr : r.Prime) (hr2 : r ≠ 2) (hu : u ^ r = 1) (h : u * u = 1) :
    u = 1 := by
  have h2 : u ^ 2 = 1 := by rw [sq]; exact h
  have hcop : Nat.Coprime r 2 := (Nat.coprime_primes hr Nat.prime_two).2 hr2
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hu)
    (orderOf_dvd_of_pow_eq_one h2))

theorem ne_zero_of_pow_eq_one {u : K} (hr : 0 < r) (hu : u ^ r = 1) : u ≠ 0 := by
  rintro rfl
  rw [zero_pow hr.ne'] at hu
  exact zero_ne_one hu

theorem eq_pow_pred_of_mul_eq_one {u v : K} (hr : 0 < r) (hu : u ^ r = 1) (h : u * v = 1) :
    v = u ^ (r - 1) := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [zero_pow hr.ne'] at hu
    exact zero_ne_one hu
  have : u * u ^ (r - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel hr]; exact hu
  exact mul_left_cancel₀ hu0 (h.trans this.symm)

theorem FrameRel.mk' {e₁ f₁ e₂ f₂ : Fin n → K} (hσ : ∀ c, σ (σ c) = c)
    (h1 : herm σ e₁ e₁ = 0) (h2 : herm σ e₁ f₁ = 1) (h3 : herm σ e₁ e₂ = 0)
    (h4 : herm σ e₁ f₂ = 0) (h5 : herm σ f₁ f₁ = 0) (h6 : herm σ f₁ e₂ = 0)
    (h7 : herm σ f₁ f₂ = 0) (h8 : herm σ e₂ e₂ = 0) (h9 : herm σ e₂ f₂ = 1)
    (h10 : herm σ f₂ f₂ = 0) : FrameRel σ e₁ f₁ e₂ f₂ where
  e1e1 := h1
  e1f1 := h2
  e1e2 := h3
  e1f2 := h4
  f1e1 := by rw [herm_conj σ hσ e₁ f₁, h2, map_one]
  f1f1 := h5
  f1e2 := h6
  f1f2 := h7
  e2e1 := herm_eq_zero_comm σ hσ h3
  e2f1 := herm_eq_zero_comm σ hσ h6
  e2e2 := h8
  e2f2 := h9
  f2e1 := herm_eq_zero_comm σ hσ h4
  f2f1 := herm_eq_zero_comm σ hσ h7
  f2e2 := by rw [herm_conj σ hσ e₂ f₂, h9, map_one]
  f2f2 := h10

theorem exists_frame_weights (hσ : IsUnitaryInvolution σ) (hr : r.Prime) (hr2 : r ≠ 2) {ξ : K}
    (hξ : IsPrimitiveRoot ξ r) (hσq : ∀ u : K, u ^ r = 1 → σ u = u) (a b : SUid σ n)
    (hab : a * b = b * a) (ha : a ^ r = 1) (hb : b ^ r = 1)
    (hind : ∀ i j : ℕ, a ^ i * b ^ j = 1 → r ∣ i ∧ r ∣ j) :
    ∃ (e₁ f₁ e₂ f₂ : Fin n → K) (α₁ α₂ β₁ β₂ : K), FrameRel σ e₁ f₁ e₂ f₂ ∧
      α₁ ^ r = 1 ∧ α₂ ^ r = 1 ∧ β₁ ^ r = 1 ∧ β₂ ^ r = 1 ∧
      (a • e₁ = α₁ • e₁ ∧ a • f₁ = α₁⁻¹ • f₁ ∧ a • e₂ = α₂ • e₂ ∧ a • f₂ = α₂⁻¹ • f₂) ∧
      (b • e₁ = β₁ • e₁ ∧ b • f₁ = β₁⁻¹ • f₁ ∧ b • e₂ = β₂ • e₂ ∧ b • f₂ = β₂⁻¹ • f₂) := by
  obtain ⟨W⟩ := exists_wtBasis hr.pos hξ a b hab ha hb
  obtain ⟨k₀, hk₀⟩ := W.exists_k0 hind hr
  obtain ⟨l₀, hl₀⟩ := W.exists_partner k₀
  obtain ⟨k₁, hk₁⟩ := W.exists_k1 hr ha hb hind k₀
  obtain ⟨l₁, hl₁⟩ := W.exists_partner k₁
  have hw₀ := W.wt_orth ha hb hσq hl₀
  have hw₁ := W.wt_orth ha hb hσq hl₁
  have hal₀ : W.da l₀ = (W.da k₀)⁻¹ := eq_inv_of_mul_eq_one_right hw₀.1
  have hbl₀ : W.db l₀ = (W.db k₀)⁻¹ := eq_inv_of_mul_eq_one_right hw₀.2
  have hal₁ : W.da l₁ = (W.da k₁)⁻¹ := eq_inv_of_mul_eq_one_right hw₁.1
  have hbl₁ : W.db l₁ = (W.db k₁)⁻¹ := eq_inv_of_mul_eq_one_right hw₁.2
  have hz : ∀ p q : Fin n, (W.da p * W.da q ≠ 1 ∨ W.db p * W.db q ≠ 1) →
      herm σ (bcol W.B p) (bcol W.B q) = 0 := by
    intro p q h
    by_contra h'
    rcases h with h | h
    · exact h (W.wt_orth ha hb hσq h').1
    · exact h (W.wt_orth ha hb hσq h').2
  have s₀₀ : herm σ (bcol W.B k₀) (bcol W.B k₀) = 0 := by
    refine hz _ _ ?_
    by_contra hc
    push Not at hc
    exact hk₀ ⟨sq_eq_one_of_pow hr hr2 (W.da_pow ha k₀) hc.1,
      sq_eq_one_of_pow hr hr2 (W.db_pow hb k₀) hc.2⟩
  have s₀₁ : herm σ (bcol W.B l₀) (bcol W.B l₀) = 0 := by
    refine hz _ _ ?_
    by_contra hc
    push Not at hc
    have h1 := sq_eq_one_of_pow hr hr2 (W.da_pow ha l₀) hc.1
    have h2 := sq_eq_one_of_pow hr hr2 (W.db_pow hb l₀) hc.2
    rw [hal₀, inv_eq_one] at h1
    rw [hbl₀, inv_eq_one] at h2
    exact hk₀ ⟨h1, h2⟩
  have s₁₀ : herm σ (bcol W.B k₁) (bcol W.B k₁) = 0 := by
    refine hz _ _ ?_
    by_contra hc
    push Not at hc
    exact hk₁ 0 ⟨by rw [pow_zero]; exact sq_eq_one_of_pow hr hr2 (W.da_pow ha k₁) hc.1,
      by rw [pow_zero]; exact sq_eq_one_of_pow hr hr2 (W.db_pow hb k₁) hc.2⟩
  have s₁₁ : herm σ (bcol W.B l₁) (bcol W.B l₁) = 0 := by
    refine hz _ _ ?_
    by_contra hc
    push Not at hc
    have h1 := sq_eq_one_of_pow hr hr2 (W.da_pow ha l₁) hc.1
    have h2 := sq_eq_one_of_pow hr hr2 (W.db_pow hb l₁) hc.2
    rw [hal₁, inv_eq_one] at h1
    rw [hbl₁, inv_eq_one] at h2
    exact hk₁ 0 ⟨by rw [pow_zero]; exact h1, by rw [pow_zero]; exact h2⟩
  have c₀₀ : herm σ (bcol W.B k₀) (bcol W.B k₁) = 0 := by
    by_contra h'
    obtain ⟨h1, h2⟩ := W.wt_orth ha hb hσq h'
    exact hk₁ (r - 1) ⟨eq_pow_pred_of_mul_eq_one hr.pos (W.da_pow ha k₀) h1,
      eq_pow_pred_of_mul_eq_one hr.pos (W.db_pow hb k₀) h2⟩
  have c₀₁ : herm σ (bcol W.B k₀) (bcol W.B l₁) = 0 := by
    by_contra h'
    obtain ⟨h1, h2⟩ := W.wt_orth ha hb hσq h'
    rw [hal₁] at h1
    rw [hbl₁] at h2
    exact hk₁ 1 ⟨by rw [pow_one]; exact ((mul_inv_eq_one₀ (ne_zero_of_pow_eq_one hr.pos
      (W.da_pow ha k₁))).1 h1).symm,
      by rw [pow_one]; exact ((mul_inv_eq_one₀ (ne_zero_of_pow_eq_one hr.pos
      (W.db_pow hb k₁))).1 h2).symm⟩
  have c₁₀ : herm σ (bcol W.B l₀) (bcol W.B k₁) = 0 := by
    by_contra h'
    obtain ⟨h1, h2⟩ := W.wt_orth ha hb hσq h'
    rw [hal₀] at h1
    rw [hbl₀] at h2
    exact hk₁ 1 ⟨by rw [pow_one]; exact ((inv_mul_eq_one₀ (ne_zero_of_pow_eq_one hr.pos
      (W.da_pow ha k₀))).1 h1).symm,
      by rw [pow_one]; exact ((inv_mul_eq_one₀ (ne_zero_of_pow_eq_one hr.pos
      (W.db_pow hb k₀))).1 h2).symm⟩
  have c₁₁ : herm σ (bcol W.B l₀) (bcol W.B l₁) = 0 := by
    by_contra h'
    obtain ⟨h1, h2⟩ := W.wt_orth ha hb hσq h'
    rw [hal₀, hal₁, ← mul_inv, inv_eq_one] at h1
    rw [hbl₀, hbl₁, ← mul_inv, inv_eq_one] at h2
    exact hk₁ (r - 1) ⟨eq_pow_pred_of_mul_eq_one hr.pos (W.da_pow ha k₀) h1,
      eq_pow_pred_of_mul_eq_one hr.pos (W.db_pow hb k₀) h2⟩
  have hg₁ : herm σ (bcol W.B k₀) (bcol W.B l₀) ≠ 0 := hl₀
  have hg₂ : herm σ (bcol W.B k₁) (bcol W.B l₁) ≠ 0 := hl₁
  set g₁ := herm σ (bcol W.B k₀) (bcol W.B l₀) with hg₁def
  set g₂ := herm σ (bcol W.B k₁) (bcol W.B l₁) with hg₂def
  have hinv := hσ.invol
  refine ⟨bcol W.B k₀, g₁⁻¹ • bcol W.B l₀, bcol W.B k₁, g₂⁻¹ • bcol W.B l₁, W.da k₀, W.da k₁,
    W.db k₀, W.db k₁, ?_, W.da_pow ha k₀, W.da_pow ha k₁, W.db_pow hb k₀, W.db_pow hb k₁,
    ⟨W.ha k₀, ?_, W.ha k₁, ?_⟩, ⟨W.hb k₀, ?_, W.hb k₁, ?_⟩⟩
  · refine FrameRel.mk' hinv s₀₀ ?_ c₀₀ ?_ ?_ ?_ ?_ s₁₀ ?_ ?_
    · rw [herm_smul_right, inv_mul_cancel₀ hg₁]
    · rw [herm_smul_right, c₀₁, mul_zero]
    · rw [herm_smul_left, herm_smul_right, s₀₁, mul_zero, mul_zero]
    · rw [herm_smul_left, c₁₀, mul_zero]
    · rw [herm_smul_left, herm_smul_right, c₁₁, mul_zero, mul_zero]
    · rw [herm_smul_right, inv_mul_cancel₀ hg₂]
    · rw [herm_smul_left, herm_smul_right, s₁₁, mul_zero, mul_zero]
  · rw [smul_comm a g₁⁻¹, W.ha l₀, hal₀, smul_comm]
  · rw [smul_comm a g₂⁻¹, W.ha l₁, hal₁, smul_comm]
  · rw [smul_comm b g₁⁻¹, W.hb l₀, hbl₀, smul_comm]
  · rw [smul_comm b g₂⁻¹, W.hb l₁, hbl₁, smul_comm]

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Ub
