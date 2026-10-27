module

public import CFSG.LocalAnalysis.SectionRank.TwoGenerators
public import CFSG.Open.StatedCenterThree

public section

namespace GL83.I713

open Matrix CFSG.Open

namespace UnitaryDiag

@[expose] def diagHomGL (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K] :
    (ι → Kˣ) →* GL ι K where
  toFun c := ⟨diagonal fun i => (c i : K), diagonal fun i => ((c i)⁻¹ : Kˣ),
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      simp,
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      simp⟩
  map_one' := Units.ext (by simp)
  map_mul' c d := Units.ext (by simp [diagonal_mul_diagonal])

section

variable {K : Type} [Field K]

@[simp] theorem coe_diagHomGL {ι : Type} [Fintype ι] [DecidableEq ι] (c : ι → Kˣ) :
    ((diagHomGL ι K c : GL ι K) : Matrix ι ι K) = diagonal fun i => (c i : K) := rfl

theorem diagHomGL_mem_statedSU {n q : ℕ} (hq : q ≠ 0) {c : Fin n → Kˣ}
    (hdet : ∏ i, c i = 1) (hc : ∀ i, c i ^ (q + 1) = 1) :
    diagHomGL (Fin n) K c ∈ StatedSU n q K := by
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · rw [coe_diagHomGL, det_diagonal, ← Units.coe_prod, hdet, Units.val_one]
  · rw [coe_diagHomGL]
    change ((diagonal fun i => (c i : K)).map (· ^ q))ᵀ * (diagonal fun i => (c i : K)) = 1
    rw [diagonal_map (f := fun x : K => x ^ q) (zero_pow hq), diagonal_transpose,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← pow_succ, ← Units.val_pow_eq_pow_val, hc i, Units.val_one]

def rootVec {n : ℕ} (a b : Fin n) (ω : Kˣ) : Fin n → Kˣ :=
  fun i => if i = a then ω else if i = b then ω⁻¹ else 1

theorem rootVec_left {n : ℕ} (a b : Fin n) (ω : Kˣ) : rootVec a b ω a = ω := by
  simp [rootVec]

theorem rootVec_right {n : ℕ} {a b : Fin n} (hab : a ≠ b) (ω : Kˣ) : rootVec a b ω b = ω⁻¹ := by
  simp [rootVec, hab.symm]

theorem rootVec_of_ne {n : ℕ} {a b i : Fin n} (ha : i ≠ a) (hb : i ≠ b) (ω : Kˣ) :
    rootVec a b ω i = 1 := by
  simp [rootVec, ha, hb]

theorem prod_rootVec {n : ℕ} {a b : Fin n} (hab : a ≠ b) (ω : Kˣ) :
    ∏ i, rootVec a b ω i = 1 := by
  rw [Fintype.prod_eq_mul a b hab fun x hx => rootVec_of_ne hx.1 hx.2 ω, rootVec_left,
    rootVec_right hab, mul_inv_cancel]

theorem rootVec_pow_eq_one {n : ℕ} (a b : Fin n) {ω : Kˣ} {m : ℕ} (hω : ω ^ m = 1) :
    rootVec a b ω ^ m = 1 := by
  funext i
  simp only [Pi.pow_apply, Pi.one_apply, rootVec]
  split_ifs <;> simp [hω, inv_pow]

theorem diagHomGL_rootVec_mem {n q : ℕ} (hq : q ≠ 0) {a b : Fin n} (hab : a ≠ b) {ω : Kˣ}
    (hω : ω ^ (q + 1) = 1) : diagHomGL (Fin n) K (rootVec a b ω) ∈ StatedSU n q K :=
  diagHomGL_mem_statedSU hq (prod_rootVec hab ω) fun i => by
    simpa using congrFun (rootVec_pow_eq_one a b hω) i

theorem exists_unit_of_mk_eq_diagonal {n q : ℕ} {g g' : StatedSU n q K} {d d' : Fin n → K}
    (hg : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal d)
    (hg' : ((g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal d')
    (h : (QuotientGroup.mk g : StatedProj (StatedSU n q K)) = QuotientGroup.mk g') :
    ∃ u : Kˣ, ∀ i, d' i = d i * u := by
  obtain ⟨u, hu⟩ := (CFSG.Open.StatedAPI.statedProj_mk_eq_iff (StatedSU n q K) g g').1 h
  refine ⟨u, fun i => ?_⟩
  rw [hg, hg', smul_one_eq_diagonal, diagonal_mul_diagonal] at hu
  exact congrFun (diagonal_injective hu) i

theorem coe_pow_of_eq_diagHomGL {n q : ℕ} {g : StatedSU n q K} {c : Fin n → Kˣ}
    (hg : (g : GL (Fin n) K) = diagHomGL (Fin n) K c) (m : ℕ) :
    ((g ^ m : StatedSU n q K) : GL (Fin n) K) = diagHomGL (Fin n) K (c ^ m) := by
  rw [Subgroup.coe_pow, hg, map_pow]

theorem mk_ne_one_of_rootVec {n q : ℕ} {a b c : Fin n} (hca : c ≠ a) (hcb : c ≠ b) {ω : Kˣ}
    (hω1 : ω ≠ 1) {g : StatedSU n q K}
    (hg : (g : GL (Fin n) K) = diagHomGL (Fin n) K (rootVec a b ω)) :
    (QuotientGroup.mk g : StatedProj (StatedSU n q K)) ≠ 1 := by
  intro h
  rw [← QuotientGroup.mk_one] at h
  obtain ⟨u, hu⟩ := exists_unit_of_mk_eq_diagonal (g := g) (g' := 1)
    (d := fun i => (rootVec a b ω i : K)) (d' := fun _ => 1) (by rw [hg, coe_diagHomGL])
    (by rw [Subgroup.coe_one, Units.val_one, diagonal_one]) h
  have h1 := hu a
  have h2 := hu c
  rw [rootVec_of_ne hca hcb, Units.val_one, one_mul] at h2
  rw [rootVec_left, ← h2, mul_one] at h1
  exact hω1 (Units.ext h1.symm)

theorem two_le_pRank_top_four [Finite K] {n q ℓ : ℕ} (hq : q ≠ 0) (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hn : 4 ≤ n) {ω : Kˣ} (hωo : orderOf ω = ℓ) (hωq : ω ^ (q + 1) = 1) :
    2 ≤ pRank ℓ (⊤ : Subgroup (StatedProj (StatedSU n q K))) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hωℓ : ω ^ ℓ = 1 := hωo ▸ pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hωo
    exact hℓ.one_lt.ne hωo
  have hωi : ω ≠ ω⁻¹ := by
    intro h
    have h2 : ω ^ 2 = 1 := by
      rw [sq]
      nth_rw 2 [h]
      exact mul_inv_cancel ω
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hωo] at this
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 this)
  obtain ⟨i0, hi0⟩ : ∃ i : Fin n, i.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨i1, hi1⟩ : ∃ i : Fin n, i.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
  obtain ⟨i2, hi2⟩ : ∃ i : Fin n, i.val = 2 := ⟨⟨2, by omega⟩, rfl⟩
  obtain ⟨i3, hi3⟩ : ∃ i : Fin n, i.val = 3 := ⟨⟨3, by omega⟩, rfl⟩
  have hne : ∀ {i j : Fin n}, i.val ≠ j.val → i ≠ j := fun h h' => h (congrArg Fin.val h')
  have h01 : i0 ≠ i1 := hne (by omega)
  have h20 : i2 ≠ i0 := hne (by omega)
  have h21 : i2 ≠ i1 := hne (by omega)
  have h23 : i2 ≠ i3 := hne (by omega)
  have h30 : i3 ≠ i0 := hne (by omega)
  have h31 : i3 ≠ i1 := hne (by omega)
  obtain ⟨gx, hgx⟩ : ∃ gx : StatedSU n q K,
      (gx : GL (Fin n) K) = diagHomGL (Fin n) K (rootVec i0 i1 ω) :=
    ⟨⟨_, diagHomGL_rootVec_mem hq h01 hωq⟩, rfl⟩
  obtain ⟨gy, hgy⟩ : ∃ gy : StatedSU n q K,
      (gy : GL (Fin n) K) = diagHomGL (Fin n) K (rootVec i2 i3 ω) :=
    ⟨⟨_, diagHomGL_rootVec_mem hq h23 hωq⟩, rfl⟩
  refine CFSG.SectionRank.two_le_pRank_top_of_commute (x := QuotientGroup.mk gx)
    (y := QuotientGroup.mk gy) ?_ ?_ ?_ (mk_ne_one_of_rootVec h20 h21 hω1 hgx) ?_
  · have : gx ^ ℓ = 1 := Subtype.ext (by
      rw [coe_pow_of_eq_diagHomGL hgx, rootVec_pow_eq_one i0 i1 hωℓ, map_one]
      rfl)
    rw [← QuotientGroup.mk_pow, this, QuotientGroup.mk_one]
  · have : gy ^ ℓ = 1 := Subtype.ext (by
      rw [coe_pow_of_eq_diagHomGL hgy, rootVec_pow_eq_one i2 i3 hωℓ, map_one]
      rfl)
    rw [← QuotientGroup.mk_pow, this, QuotientGroup.mk_one]
  · show QuotientGroup.mk gx * QuotientGroup.mk gy = QuotientGroup.mk gy * QuotientGroup.mk gx
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hgx, hgy, ← map_mul, ← map_mul, mul_comm])
  · intro m h
    rw [← QuotientGroup.mk_pow] at h
    obtain ⟨u, hu⟩ := exists_unit_of_mk_eq_diagonal (g := gx ^ m) (g' := gy)
      (d := fun i => ((rootVec i0 i1 ω ^ m) i : K)) (d' := fun i => (rootVec i2 i3 ω i : K))
      (by rw [coe_pow_of_eq_diagHomGL hgx, coe_diagHomGL]) (by rw [hgy, coe_diagHomGL]) h
    have e2 := hu i2
    have e3 := hu i3
    simp only [Pi.pow_apply, rootVec_left, rootVec_right h23, rootVec_of_ne h20 h21,
      rootVec_of_ne h30 h31, one_pow, Units.val_one, one_mul] at e2 e3
    exact hωi (Units.ext (e2.trans e3.symm))

open CFSG.Open.StatedCenterThree in
theorem cyc3_pow_three : (cyc3 : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
  rw [pow_succ, sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc3, Matrix.mul_apply, Fin.sum_univ_three]

open CFSG.Open.StatedCenterThree in
theorem cyc3_mul_diag_eq {ω : Kˣ} (hω : ω ^ 3 = 1) :
    (cyc3 : Matrix (Fin 3) (Fin 3) K) * diagonal (fun i => (rootVec (0 : Fin 3) 1 ω i : K)) =
      (diagonal (fun i => (rootVec (0 : Fin 3) 1 ω i : K)) * cyc3) *
        ((ω : K) • (1 : Matrix (Fin 3) (Fin 3) K)) := by
  have hinv : ω⁻¹ = ω * ω := inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact hω)
  have hω' : (ω : K) * ω * ω = 1 := by
    rw [← Units.val_mul, ← Units.val_mul, ← pow_three', hω, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cyc3, rootVec, Matrix.mul_apply, Fin.sum_univ_three, diagonal_apply, hinv, hω']

open CFSG.Open.StatedCenterThree in
theorem two_le_pRank_top_three [Finite K] {q : ℕ} (hq : q ≠ 0) {ω : Kˣ} (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) (hωq : ω ^ (q + 1) = 1) :
    2 ≤ pRank 3 (⊤ : Subgroup (StatedProj (StatedSU 3 q K))) := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  obtain ⟨gx, hgx⟩ : ∃ gx : StatedSU 3 q K,
      (gx : GL (Fin 3) K) = diagHomGL (Fin 3) K (rootVec 0 1 ω) :=
    ⟨⟨_, diagHomGL_rootVec_mem hq h01 hωq⟩, rfl⟩
  obtain ⟨gy, hgy⟩ : ∃ gy : StatedSU 3 q K, (gy : GL (Fin 3) K) = cyc3GL :=
    ⟨⟨_, cyc3GL_mem hq⟩, rfl⟩
  refine CFSG.SectionRank.two_le_pRank_top_of_commute (x := QuotientGroup.mk gx)
    (y := QuotientGroup.mk gy) ?_ ?_ ?_ (mk_ne_one_of_rootVec h20 h21 hω1 hgx) ?_
  · have : gx ^ 3 = 1 := Subtype.ext (by
      rw [coe_pow_of_eq_diagHomGL hgx, rootVec_pow_eq_one 0 1 hω3, map_one]
      rfl)
    rw [← QuotientGroup.mk_pow, this, QuotientGroup.mk_one]
  · have : gy ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, hgy]
      apply Units.ext
      rw [Units.val_pow_eq_pow_val]
      exact cyc3_pow_three)
    rw [← QuotientGroup.mk_pow, this, QuotientGroup.mk_one]
  · show QuotientGroup.mk gx * QuotientGroup.mk gy = QuotientGroup.mk gy * QuotientGroup.mk gx
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    refine (CFSG.Open.StatedAPI.statedProj_mk_eq_iff (StatedSU 3 q K) (gx * gy) (gy * gx)).2
      ⟨ω, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hgx, hgy,
      coe_diagHomGL]
    exact cyc3_mul_diag_eq hω3
  · intro m h
    rw [← QuotientGroup.mk_pow] at h
    obtain ⟨u, hu⟩ :=
      (CFSG.Open.StatedAPI.statedProj_mk_eq_iff (StatedSU 3 q K) (gx ^ m) gy).1 h
    rw [hgy, coe_pow_of_eq_diagHomGL hgx, coe_diagHomGL, smul_one_eq_diagonal,
      diagonal_mul_diagonal] at hu
    have h00 := congrFun (congrFun hu 0) 0
    rw [diagonal_apply_eq] at h00
    have hc0 : ((cyc3GL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 = 0 := by
      simp [cyc3GL, cyc3]
    rw [hc0] at h00
    exact mul_ne_zero (Units.ne_zero _) (Units.ne_zero _) h00.symm

end

end UnitaryDiag

theorem two_le_pRank_statedPSU_of_dvd {K : Type} [Field K] [Finite K] {q n ℓ : ℕ}
    (hK : Nat.card K = q ^ 2) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hn : 3 ≤ n) (hℓn : ℓ ∣ n)
    (hℓq : ℓ ∣ q + 1) :
    2 ≤ pRank ℓ (⊤ : Subgroup (StatedProj (StatedSU n q K))) := by
  have hq2 : 2 ≤ q := CFSG.Open.StatedCenterThree.two_le_of_card_eq_sq hK
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨ω, hω⟩ : ∃ ω : Kˣ, orderOf ω = ℓ := exists_prime_orderOf_dvd_card' ℓ (by
    rw [Nat.card_units, hK, CFSG.Open.StatedCenterThree.sq_sub_one_eq (by omega)]
    exact Dvd.dvd.mul_left hℓq _)
  have hωq : ω ^ (q + 1) = 1 := by
    obtain ⟨k, hk⟩ := hℓq
    rw [hk, pow_mul, ← hω, pow_orderOf_eq_one, one_pow]
  rcases Nat.lt_or_ge n 4 with h3 | h4
  · obtain rfl : n = 3 := by omega
    obtain rfl : ℓ = 3 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 hℓn
    exact UnitaryDiag.two_le_pRank_top_three (by omega) (hω ▸ pow_orderOf_eq_one ω)
      (fun h => by rw [h, orderOf_one] at hω; omega) hωq
  · exact UnitaryDiag.two_le_pRank_top_four (by omega) hℓ hℓ2 h4 hω hωq

end GL83.I713
