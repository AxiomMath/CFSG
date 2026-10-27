module

public import CFSG.LieType.SemisimpleCentralizers.HeldUnitaryComponents

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open CFSG.Open CFSG.Open.StatedAPI CFSG.LieType.SemisimpleCentralizers.Held Matrix

theorem three_dvd_four_pow_sub_one (k : ℕ) : 3 ∣ 4 ^ k - 1 := by
  have h : 4 ^ k % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have hpos : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  generalize 4 ^ k = N at h hpos ⊢
  omega

theorem exists_ord3_of_card_four_pow (E : Type) [Field E] [Finite E] {k : ℕ}
    (hk : Nat.card E = 4 ^ k) : ∃ ω : E, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hdvd : 3 ∣ Nat.card Eˣ := by
    rw [Nat.card_units, hk]
    exact three_dvd_four_pow_sub_one k
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have h3 : x ^ 3 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  refine ⟨(x : E), ?_, ?_⟩
  · rw [← Units.val_pow_eq_pow_val, h3, Units.val_one]
  · intro h
    have hx1 : x = 1 := Units.ext h
    rw [hx1, orderOf_one] at hx
    norm_num at hx

theorem pow_eq_pow_mod_three {M : Type} [Monoid M] {ω : M} (hω : ω ^ 3 = 1) (n : ℕ) :
    ω ^ n = ω ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3]
  rw [pow_add, pow_mul, hω, one_pow, one_mul]

theorem two_pow_mod_three_of_odd {d : ℕ} (hd : Odd d) : 2 ^ d % 3 = 2 := by
  obtain ⟨m, rfl⟩ := hd
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem pow_two_pow_of_odd {M : Type} [Monoid M] {ω : M} (hω : ω ^ 3 = 1) {d : ℕ} (hd : Odd d) :
    ω ^ (2 ^ d) = ω ^ 2 := by
  rw [pow_eq_pow_mod_three hω, two_pow_mod_three_of_odd hd]

theorem two_eq_zero_of_card_eq_two_pow (E : Type) [Field E] [Finite E] {k : ℕ}
    (hk : Nat.card E = 2 ^ k) : (2 : E) = 0 := by
  have : Fintype E := Fintype.ofFinite E
  obtain ⟨p, hp, n, hpp, hcard⟩ := FiniteField.card' E
  rw [Nat.card_eq_fintype_card] at hk
  have hdvd : p ∣ 2 ^ k := by
    rw [← hk, hcard]
    exact dvd_pow_self p n.ne_zero
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow hdvd)
  subst hp2
  exact_mod_cast CharP.cast_eq_zero E 2

@[expose] def diagUnit {a : ℕ} {E : Type} [Field E] (d : Fin a → E) (hd : ∀ i, d i ≠ 0) :
    GL (Fin a) E :=
  Units.mk (diagonal d) (diagonal fun i => (d i)⁻¹)
    (by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      simp [hd i])
    (by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      simp [hd i])

theorem diagUnit_val {a : ℕ} {E : Type} [Field E] (d : Fin a → E) (hd : ∀ i, d i ≠ 0) :
    ((diagUnit d hd : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) = diagonal d := rfl

theorem diagUnit_mem_heldSU {a : ℕ} {E : Type} [Field E] {τ : E ≃+* E} (hτ : ∀ x, τ (τ x) = x)
    (d : Fin a → E) (hd : ∀ i, d i ≠ 0) (hu : ∀ i, τ (d i) * d i = 1) (hdet : ∏ i, d i = 1) :
    diagUnit d hd ∈ heldSU a E τ hτ := by
  refine Subgroup.mem_inf.mpr ⟨?_, mem_statedSL_of_det ?_⟩
  · rw [mem_heldGU, diagUnit_val, diagonal_map (map_zero τ), diagonal_transpose, diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1
    funext i
    exact hu i
  · rw [diagUnit_val, det_diagonal]
    exact hdet

@[expose] def permUnit {a : ℕ} (E : Type) [Field E] (σ : Equiv.Perm (Fin a)) : GL (Fin a) E :=
  Units.mk (σ.permMatrix E) (σ⁻¹.permMatrix E)
    (by rw [← Matrix.permMatrix_mul]; simp)
    (by rw [← Matrix.permMatrix_mul]; simp)

theorem permUnit_val {a : ℕ} (E : Type) [Field E] (σ : Equiv.Perm (Fin a)) :
    ((permUnit E σ : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) = σ.permMatrix E := rfl

theorem swap_mem_heldSU {m : ℕ} {E : Type} [Field E] {τ : E ≃+* E} (hτ : ∀ x, τ (τ x) = x)
    (h2 : (2 : E) = 0) :
    permUnit E (Equiv.swap (0 : Fin (m + 2)) 1) ∈ heldSU (m + 2) E τ hτ := by
  have hmap : ((Equiv.swap (0 : Fin (m + 2)) 1).permMatrix E).map τ =
      (Equiv.swap (0 : Fin (m + 2)) 1).permMatrix E := by
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix]
    split_ifs <;> simp
  refine Subgroup.mem_inf.mpr ⟨?_, mem_statedSL_of_det ?_⟩
  · rw [mem_heldGU, permUnit_val, hmap, Matrix.transpose_permMatrix]
    rw [← Matrix.permMatrix_mul]
    simp
  · rw [permUnit_val, Matrix.det_permutation, Equiv.Perm.sign_swap (by simp)]
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    have : (-1 : E) = 1 := by
      rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, h2]
    exact this

@[expose] def ord3Diag {E : Type} [Field E] (m : ℕ) (ω : E) : Fin (m + 2) → E :=
  Fin.cons ω (Fin.cons (ω ^ 2) fun _ : Fin m => (1 : E))

theorem ord3Diag_ne_zero {E : Type} [Field E] {m : ℕ} {ω : E} (hω3 : ω ^ 3 = 1) :
    ∀ i, ord3Diag m ω i ≠ 0 := by
  have hω0 : ω ≠ 0 := by
    intro h
    rw [h] at hω3
    norm_num at hω3
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [ord3Diag] using hω0
  · refine Fin.cases ?_ (fun l => ?_) j
    · simpa [ord3Diag] using pow_ne_zero 2 hω0
    · simp [ord3Diag]

theorem ord3Diag_cube {E : Type} [Field E] {m : ℕ} {ω : E} (hω3 : ω ^ 3 = 1) :
    ∀ i, ord3Diag m ω i ^ 3 = 1 := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [ord3Diag] using hω3
  · refine Fin.cases ?_ (fun l => ?_) j
    · simp only [ord3Diag, Fin.cons_succ, Fin.cons_zero]
      rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
    · simp [ord3Diag]

theorem ord3Diag_prod {E : Type} [Field E] {m : ℕ} {ω : E} (hω3 : ω ^ 3 = 1) :
    ∏ i, ord3Diag m ω i = 1 := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [ord3Diag, Fin.cons_succ, Fin.cons_zero, Finset.prod_const_one, mul_one]
  linear_combination hω3

theorem ord3Diag_unitary {E : Type} [Field E] {m : ℕ} {τ : E ≃+* E} {ω : E} (hω3 : ω ^ 3 = 1)
    (hτω : τ ω = ω ^ 2) (i : Fin (m + 2)) : τ (ord3Diag m ω i) * ord3Diag m ω i = 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [ord3Diag, Fin.cons_zero]
    rw [hτω]
    linear_combination hω3
  · refine Fin.cases ?_ (fun l => ?_) j
    · simp only [ord3Diag, Fin.cons_succ, Fin.cons_zero]
      rw [map_pow, hτω]
      linear_combination (ω ^ 3 + 1) * hω3
    · simp [ord3Diag]

theorem three_dvd_card_heldSU_quot {a : ℕ} (ha : 2 ≤ a) {E : Type} [Field E] [Finite E] {dd : ℕ}
    {τ : E ≃+* E} (hτ : ∀ x, τ (τ x) = x) (hτdd : ∀ x : E, τ x = x ^ (2 ^ dd)) (hdd : Odd dd)
    (hcard : Nat.card E = (2 ^ dd) ^ 2) :
    3 ∣ Nat.card (heldSU a E τ hτ ⧸ Subgroup.center (heldSU a E τ hτ)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨ω, hω3, hω1⟩ := exists_ord3_of_card_four_pow E (k := dd)
    (by rw [hcard, ← pow_mul, mul_comm, pow_mul]; norm_num)
  have h2 : (2 : E) = 0 := two_eq_zero_of_card_eq_two_pow E (k := dd * 2)
    (by rw [hcard, ← pow_mul])
  have hτω : τ ω = ω ^ 2 := by rw [hτdd, pow_two_pow_of_odd hω3 hdd]
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 2 := ⟨a - 2, by omega⟩
  let g : GL (Fin (m + 2)) E := diagUnit (ord3Diag m ω) (ord3Diag_ne_zero hω3)
  have hgmem : g ∈ heldSU (m + 2) E τ hτ :=
    diagUnit_mem_heldSU hτ _ _ (ord3Diag_unitary hω3 hτω) (ord3Diag_prod hω3)
  let g' : ↥(heldSU (m + 2) E τ hτ) := ⟨g, hgmem⟩
  have hg3 : g' ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    show (diagonal (ord3Diag m ω)) ^ 3 = 1
    rw [diagonal_pow]
    have h1 : ord3Diag m ω ^ 3 = 1 := by
      funext i
      rw [Pi.pow_apply, Pi.one_apply]
      exact ord3Diag_cube hω3 i
    rw [h1]
    exact diagonal_one
  have hg1 : (QuotientGroup.mk g' : ↥(heldSU (m + 2) E τ hτ) ⧸ Subgroup.center ↥(heldSU (m + 2) E τ hτ)) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    intro hc
    have hcomm := Subgroup.mem_center_iff.mp hc
      ⟨permUnit E (Equiv.swap (0 : Fin (m + 2)) 1), swap_mem_heldSU hτ h2⟩
    have hval := congrArg (fun z : ↥(heldSU (m + 2) E τ hτ) => (z : GL (Fin (m + 2)) E) :
      ↥(heldSU (m + 2) E τ hτ) → GL (Fin (m + 2)) E) hcomm
    have hm := congrArg (fun A : GL (Fin (m + 2)) E => (A : Matrix (Fin (m + 2)) (Fin (m + 2)) E)) hval
    have hentry := congrFun (congrFun hm 0) 1
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_diagonal, Matrix.diagonal_mul,
      permUnit_val] at hentry
    have hgdiag : ((g' : GL (Fin (m + 2)) E) : Matrix (Fin (m + 2)) (Fin (m + 2)) E) =
        diagonal (ord3Diag m ω) := rfl
    rw [hgdiag, Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
    have hP : (Equiv.Perm.permMatrix E (Equiv.swap (0 : Fin (m + 2)) 1)) 0 1 = 1 := by
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    rw [hP] at hentry
    have hω0 : ω ≠ 0 := by
      intro h
      rw [h] at hω3
      norm_num at hω3
    have h01 : ω ^ 2 = ω := by
      simp [ord3Diag] at hentry
      first
        | linear_combination hentry
        | linear_combination (-1 : E) * hentry
    have hfac : ω * (ω - 1) = 0 := by linear_combination h01
    rcases mul_eq_zero.mp hfac with h | h
    · exact hω0 h
    · exact hω1 (sub_eq_zero.mp h)
  have hord : orderOf (QuotientGroup.mk g' : ↥(heldSU (m + 2) E τ hτ) ⧸ Subgroup.center ↥(heldSU (m + 2) E τ hτ)) = 3 := by
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, hg3]
      simp
    · exact hg1
  have hdvd := orderOf_dvd_natCard (QuotientGroup.mk g' : ↥(heldSU (m + 2) E τ hτ) ⧸ Subgroup.center ↥(heldSU (m + 2) E τ hτ))
  rw [hord] at hdvd
  exact hdvd

theorem diagUnit_ord3_pow {m : ℕ} {E : Type} [Field E] {ω : E} (hω3 : ω ^ 3 = 1) :
    (diagUnit (ord3Diag m ω) (ord3Diag_ne_zero hω3)) ^ 3 = 1 := by
  apply Units.ext
  show (diagonal (ord3Diag m ω)) ^ 3 = 1
  rw [diagonal_pow]
  have h1 : ord3Diag m ω ^ 3 = 1 := by
    funext i
    rw [Pi.pow_apply, Pi.one_apply]
    exact ord3Diag_cube hω3 i
  rw [h1]
  exact diagonal_one

theorem three_dvd_card_statedProj_statedSL {b : ℕ} (hb : 2 ≤ b) {E : Type} [Field E] [Finite E] {k : ℕ}
    (hk : Nat.card E = 4 ^ k) : 3 ∣ Nat.card (StatedProj (StatedSL b E)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨ω, hω3, hω1⟩ := exists_ord3_of_card_four_pow E hk
  obtain ⟨m, rfl⟩ : ∃ m, b = m + 2 := ⟨b - 2, by omega⟩
  have hgmem : diagUnit (ord3Diag m ω) (ord3Diag_ne_zero hω3) ∈ StatedSL (m + 2) E := by
    apply mem_statedSL_of_det
    rw [diagUnit_val, det_diagonal]
    exact ord3Diag_prod hω3
  let g' : ↥(StatedSL (m + 2) E) := ⟨_, hgmem⟩
  have hg3 : g' ^ 3 = 1 := Subtype.ext (diagUnit_ord3_pow hω3)
  have hg1 : (QuotientGroup.mk g' : StatedProj (StatedSL (m + 2) E)) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    intro hc
    simp only [StatedScalars, MonoidHom.mem_range] at hc
    obtain ⟨c, hc⟩ := hc
    have hm := congrArg (fun A : GL (Fin (m + 2)) E => (A : Matrix (Fin (m + 2)) (Fin (m + 2)) E)) hc
    have h00 := congrFun (congrFun hm 0) 0
    have h11 := congrFun (congrFun hm 1) 1
    simp [g', diagUnit_val, ord3Diag, Matrix.scalar_apply] at h00 h11
    have hω0 : ω ≠ 0 := by
      intro h
      rw [h] at hω3
      norm_num at hω3
    have key : ω ^ 2 = ω := by
      first
        | linear_combination h00 - h11
        | linear_combination h11 - h00
        | linear_combination (-1 : E) * (h00 - h11)
        | linear_combination h00 + h11
    have hfac : ω * (ω - 1) = 0 := by linear_combination key
    rcases mul_eq_zero.mp hfac with h | h
    · exact hω0 h
    · exact hω1 (sub_eq_zero.mp h)
  have hord : orderOf (QuotientGroup.mk g' : StatedProj (StatedSL (m + 2) E)) = 3 := by
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, hg3]
      simp
    · exact hg1
  have hdvd := orderOf_dvd_natCard (QuotientGroup.mk g' : StatedProj (StatedSL (m + 2) E))
  rw [hord] at hdvd
  exact hdvd

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end
