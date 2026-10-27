module

public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.DiagCube
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.CubicFrame

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem transvMat_comm_of_orth {h : UnitaryFieldData p f K} {e e' : Fin n → K}
    (_he : hpair h e e = 0) (_he' : hpair h e' e' = 0) (hee : hpair h e e' = 0) (β β' : K) :
    transvMat h e β * transvMat h e' β' = transvMat h e' β' * transvMat h e β := by
  have h1 : hpair h e' e = 0 := by rw [hpair_comm e e', hee, map_zero]
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [transvMat_mulVec, hpair_add_right, hpair_smul_right, hee, h1, mul_zero, add_zero]
  module

theorem commute_transvMat {h : UnitaryFieldData p f K} {e e' : Fin n → K}
    (he : hpair h e e = 0) (he' : hpair h e' e' = 0) (hee : hpair h e e' = 0) (β β' : K) :
    Commute (transvMat h e β) (transvMat h e' β') :=
  transvMat_comm_of_orth he he' hee β β'

@[expose] noncomputable def triTransv (h : UnitaryFieldData p f K) (v : Fin 3 → Fin n → K) (β : K) :
    Matrix (Fin n) (Fin n) K :=
  transvMat h (v 0) β * transvMat h (v 1) β * transvMat h (v 2) β

theorem triTransv_pow_char {h : UnitaryFieldData p f K} {v : Fin 3 → Fin n → K}
    (hv : ∀ i j, hpair h (v i) (v j) = 0) (β : K) : triTransv h v β ^ p = 1 := by
  have c : ∀ i j, Commute (transvMat h (v i) β) (transvMat h (v j) β) :=
    fun i j => commute_transvMat (hv i i) (hv j j) (hv i j) β β
  unfold triTransv
  rw [((c 0 2).mul_left (c 1 2)).mul_pow, (c 0 1).mul_pow, transvMat_pow_char (hv 0 0),
    transvMat_pow_char (hv 1 1), transvMat_pow_char (hv 2 2)]
  simp

theorem triTransv_commute {h : UnitaryFieldData p f K} {B B' : Matrix (Fin n) (Fin n) K}
    (hB : (B.map h.bar)ᵀ * B = 1) (hBB : B * B' = 1) (hBB' : B' * B = 1)
    {l : K} (hl : h.bar l * l = 1) (v : Fin 3 → Fin n → K)
    (hv : ∀ i j, hpair h (v i) (v j) = 0) (β : K)
    (h01 : B *ᵥ v 0 = v 1) (h12 : B *ᵥ v 1 = v 2) (h20 : B *ᵥ v 2 = l • v 0) :
    B * triTransv h v β = triTransv h v β * B := by
  have c : ∀ i j, Commute (transvMat h (v i) β) (transvMat h (v j) β) :=
    fun i j => commute_transvMat (hv i i) (hv j j) (hv i j) β β
  have conj : ∀ w, B * transvMat h w β * B' = transvMat h (B *ᵥ w) β :=
    fun w => conj_transvMat hB hBB w β
  have hBB'' : ∀ Z : Matrix (Fin n) (Fin n) K, B' * (B * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hBB', Matrix.one_mul]
  have key : B * triTransv h v β * B' = triTransv h v β := by
    have e1 : B * triTransv h v β * B' =
        (B * transvMat h (v 0) β * B') * (B * transvMat h (v 1) β * B') *
          (B * transvMat h (v 2) β * B') := by
      unfold triTransv
      simp only [Matrix.mul_assoc, hBB'']
    rw [e1, conj, conj, conj, h01, h12, h20, transvMat_smul_vec, hl, mul_one]
    unfold triTransv
    rw [Matrix.mul_assoc, ← (c 0 2).eq, ← Matrix.mul_assoc, ← (c 0 1).eq, Matrix.mul_assoc]
  calc B * triTransv h v β = B * triTransv h v β * (B' * B) := by rw [hBB', Matrix.mul_one]
    _ = (B * triTransv h v β * B') * B := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [key]

theorem triTransv_pair_cube {h : UnitaryFieldData p f K} {e g : Fin 3 → Fin n → K}
    (hee : ∀ i j, hpair h (e i) (e j) = 0) (hgg : ∀ i j, hpair h (g i) (g j) = 0)
    (heg : ∀ i j, hpair h (e i) (g j) = if i = j then 1 else 0) {β β' : K}
    (hββ : β * β' = -3) :
    (triTransv h e β * triTransv h g β') ^ 3 = 1 := by
  have caa : ∀ i j, Commute (transvMat h (e i) β) (transvMat h (e j) β) :=
    fun i j => commute_transvMat (hee i i) (hee j j) (hee i j) β β
  have cbb : ∀ i j, Commute (transvMat h (g i) β') (transvMat h (g j) β') :=
    fun i j => commute_transvMat (hgg i i) (hgg j j) (hgg i j) β' β'
  have cab : ∀ i j, i ≠ j → Commute (transvMat h (e i) β) (transvMat h (g j) β') :=
    fun i j hij => commute_transvMat (hee i i) (hgg j j) (by rw [heg]; simp [hij]) β β'
  have hS : ∀ i j, i ≠ j → Commute (transvMat h (e i) β * transvMat h (g i) β')
      (transvMat h (e j) β * transvMat h (g j) β') := fun i j hij =>
    ((caa i j).mul_right (cab i j hij)).mul_left
      ((cab j i hij.symm).symm.mul_right (cbb i j))
  have hr : triTransv h e β * triTransv h g β' =
      (transvMat h (e 0) β * transvMat h (g 0) β') * (transvMat h (e 1) β * transvMat h (g 1) β') *
        (transvMat h (e 2) β * transvMat h (g 2) β') := by
    unfold triTransv
    simp only [Matrix.mul_assoc]
    rw [(cab 2 0 (by decide)).left_comm, (cab 1 0 (by decide)).left_comm,
      (cab 2 1 (by decide)).left_comm]
  have hc : ∀ i, (transvMat h (e i) β * transvMat h (g i) β') ^ 3 = 1 := fun i =>
    transvMat_pair_cube (hee i i) (hgg i i) (by rw [heg]; simp)
      (by rw [heg]; simp only [↓reduceIte, map_one]; linear_combination hββ)
  rw [hr, ((hS 0 2 (by decide)).mul_left (hS 1 2 (by decide))).mul_pow,
    (hS 0 1 (by decide)).mul_pow, hc 0, hc 1, hc 2]
  simp

theorem triTransv_pair_not_scalar {h : UnitaryFieldData p f K} {e g : Fin 3 → Fin n → K}
    (hee : ∀ i j, hpair h (e i) (e j) = 0) (hgg : ∀ i j, hpair h (g i) (g j) = 0)
    (heg : ∀ i j, hpair h (e i) (g j) = if i = j then 1 else 0) {β β' : K} (hβ' : β' ≠ 0)
    (s : K) : triTransv h e β * triTransv h g β' ≠ s • (1 : Matrix (Fin n) (Fin n) K) := by
  intro hs
  have hge : ∀ i j, hpair h (g i) (e j) = if i = j then 1 else 0 := by
    intro i j
    rw [hpair_comm (e j) (g i), heg]
    by_cases hij : j = i
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  have hv := congrArg (fun M => M *ᵥ e 1) hs
  simp only [triTransv] at hv
  simp only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    transvMat_mulVec, hpair_add_right, hpair_smul_right, hee, hgg, heg, hge] at hv
  have := congrArg (hpair h (e 1)) hv
  simp [hpair_add_right, hpair_smul_right, hee, heg] at this
  exact hβ' this

theorem hasFixedThreePair_diag_of_nonCube (h : UnitaryFieldData p f K) (h3 : 3 ∣ p ^ f + 1)
    (hn : 6 ≤ n)
    (B : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) {l : K}
    (hB3 : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ 3 = l • (1 : Matrix (Fin n) (Fin n) K))
    (hl : ∀ x : K, x ^ 3 ≠ l) :
    HasFixedThreePair
      (primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) B) := by
  classical
  have hp3 : p ≠ 3 := prime_ne_three_of_dvd h.prime h.one_le h3
  have hchar := h.charP
  have h3K : (3 : K) ≠ 0 := by
    intro h0
    have : ((3 : ℕ) : K) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff K p] at this
    exact hp3 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).1 this)
  set Bm : Matrix (Fin n) (Fin n) K := ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hBm
  set Bi : Matrix (Fin n) (Fin n) K :=
    (((B : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hBi
  have hB : (Bm.map h.bar)ᵀ * Bm = 1 := by
    have := mem_primeFormUnitary.1 B.2
    simpa using this
  have hBB : Bm * Bi = 1 := by rw [hBm, hBi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBB' : Bi * Bm = 1 := by rw [hBm, hBi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hlN : h.bar l * l = 1 := by
    have h1 := mem_primeFormUnitary.1 (B ^ 3).2
    have hc : (((B ^ 3 : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
        GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = l • 1 := by
      simpa using hB3
    rw [hc] at h1
    have h2 := congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩
    simpa [Matrix.mul_apply, Matrix.one_apply, mul_comm] using h2
  obtain ⟨w, w', hw0, hee0, hff0, hef0⟩ := exists_frame (h := h) hn Bm hB hB3 hl
  set e : Fin 3 → Fin n → K := fun i => (Bm ^ (i : ℕ)) *ᵥ w with he
  set g : Fin 3 → Fin n → K := fun i => (Bm ^ (i : ℕ)) *ᵥ w' with hg
  have hee : ∀ i j, hpair h (e i) (e j) = 0 := hee0
  have hgg : ∀ i j, hpair h (g i) (g j) = 0 := hff0
  have heg : ∀ i j, hpair h (e i) (g j) = if i = j then 1 else 0 := hef0
  have step : ∀ (x : Fin n → K) (k : ℕ), Bm *ᵥ ((Bm ^ k) *ᵥ x) = (Bm ^ (k + 1)) *ᵥ x :=
    fun x k => by rw [Matrix.mulVec_mulVec, ← pow_succ']
  have he01 : Bm *ᵥ e 0 = e 1 := step w 0
  have he12 : Bm *ᵥ e 1 = e 2 := step w 1
  have he20 : Bm *ᵥ e 2 = l • e 0 := by
    show Bm *ᵥ ((Bm ^ 2) *ᵥ w) = l • ((Bm ^ 0) *ᵥ w)
    rw [step w 2, pow_zero, Matrix.one_mulVec]
    exact pow_three_mulVec hB3 w
  have hg01 : Bm *ᵥ g 0 = g 1 := step w' 0
  have hg12 : Bm *ᵥ g 1 = g 2 := step w' 1
  have hg20 : Bm *ᵥ g 2 = l • g 0 := by
    show Bm *ᵥ ((Bm ^ 2) *ᵥ w') = l • ((Bm ^ 0) *ᵥ w')
    rw [step w' 2, pow_zero, Matrix.one_mulVec]
    exact pow_three_mulVec hB3 w'
  obtain ⟨c0, hc0⟩ := h.exists_bar_ne
  set τ : K := c0 - h.bar c0 with hτ
  have hτ0 : τ ≠ 0 := fun h0 => hc0 (by rw [hτ, sub_eq_zero] at h0; exact h0.symm)
  have hbτ : h.bar τ = -τ := by
    rw [hτ, map_sub, h.bar_bar]; ring
  set β' : K := -3 / τ with hβ'
  have hβτ : τ + h.bar τ = 0 := by rw [hbτ]; ring
  have hβ'1 : β' + h.bar β' = 0 := by
    have hb3 : h.bar (3 : K) = 3 := map_ofNat h.bar 3
    rw [hβ', map_div₀, map_neg, hb3, hbτ]
    field_simp
    ring
  have hββ : τ * β' = -3 := by
    rw [hβ']
    field_simp
  have hβ'0 : β' ≠ 0 := by
    rw [hβ']
    exact div_ne_zero (neg_ne_zero.2 h3K) hτ0
  have hx := mul_mem (mul_mem (transvGL_mem_gramSU h (hee 0 0) hβτ)
    (transvGL_mem_gramSU h (hee 1 1) hβτ)) (transvGL_mem_gramSU h (hee 2 2) hβτ)
  have hy := mul_mem (mul_mem (transvGL_mem_gramSU h (hgg 0 0) hβ'1)
    (transvGL_mem_gramSU h (hgg 1 1) hβ'1)) (transvGL_mem_gramSU h (hgg 2 2) hβ'1)
  let x : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := ⟨_, hx⟩
  let y : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := ⟨_, hy⟩
  have hxv : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = triTransv h e τ := rfl
  have hyv : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = triTransv h g β' := rfl
  have hcop : (Nat.Coprime p 3) := (Nat.coprime_primes h.prime Nat.prime_three).2 hp3
  have hxp : ((x : GL (Fin n) K)) ^ p = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, hxv]; exact triTransv_pow_char hee τ)
  have hyp : ((y : GL (Fin n) K)) ^ p = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, hyv]; exact triTransv_pow_char hgg β')
  have hcx : (B : GL (Fin n) K) * (x : GL (Fin n) K) = (x : GL (Fin n) K) * (B : GL (Fin n) K) := by
    apply Units.ext
    show Bm * triTransv h e τ = triTransv h e τ * Bm
    exact triTransv_commute hB hBB hBB' hlN e hee τ he01 he12 he20
  have hcy : (B : GL (Fin n) K) * (y : GL (Fin n) K) = (y : GL (Fin n) K) * (B : GL (Fin n) K) := by
    apply Units.ext
    show Bm * triTransv h g β' = triTransv h g β' * Bm
    exact triTransv_commute hB hBB hBB' hlN g hgg β' hg01 hg12 hg20
  refine ⟨(x : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
    (y : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)), ?_, ?_, ?_, ?_, ?_⟩
  · exact fixed_conjHom_of_commute h B x hcx
  · exact fixed_conjHom_of_commute h B y hcy
  · exact Nat.Coprime.coprime_dvd_left (orderOf_mk_dvd h x p hxp) hcop
  · exact Nat.Coprime.coprime_dvd_left (orderOf_mk_dvd h y p hyp) hcop
  · rw [← QuotientGroup.mk_mul]
    refine orderOf_mk_eq_three h (x * y) ?_ ?_
    · apply Units.ext
      rw [Units.val_pow_eq_pow_val]
      exact triTransv_pair_cube hee hgg heg hββ
    · intro s
      exact triTransv_pair_not_scalar hee hgg heg hβ'0 s

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
