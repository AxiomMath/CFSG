module

public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.Open.StatedAPI

public section

namespace CFSG.LieType.Universal.Unitary

open Matrix CFSG.Assembly.LowTwoRank

section General

variable {F : Type*} [Field F] (σ : F ≃+* F)

@[expose] def SUid (n : ℕ) : Subgroup (GL (Fin n) F) where
  carrier := {B | (B : Matrix (Fin n) (Fin n) F).det = 1 ∧
    conjTr σ (B : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F) = 1}
  mul_mem' {A B} hA hB := by
    refine ⟨by rw [Units.val_mul, det_mul, hA.1, hB.1, one_mul], ?_⟩
    have e : conjTr σ ((A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F)) *
        ((A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F)) =
        conjTr σ (B : Matrix (Fin n) (Fin n) F) *
          (conjTr σ (A : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F)) *
            (B : Matrix (Fin n) (Fin n) F) := by
      rw [conjTr_mul]
      simp only [Matrix.mul_assoc]
    rw [Units.val_mul, e, hA.2, Matrix.mul_one, hB.2]
  one_mem' := ⟨by simp, by simp [conjTr_one]⟩
  inv_mem' {A} hA := by
    have hAB : (A : Matrix (Fin n) (Fin n) F) * ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    refine ⟨?_, ?_⟩
    · have := congrArg Matrix.det hAB
      rw [det_mul, det_one, hA.1, one_mul] at this
      exact this
    · have key : conjTr σ ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F) *
          (conjTr σ (A : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F)) *
            ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F) =
          conjTr σ ((A : Matrix _ _ F) * ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F)) *
            ((A : Matrix _ _ F) * ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F)) := by
        rw [conjTr_mul]
        simp only [Matrix.mul_assoc]
      rw [hA.2, Matrix.mul_one, hAB, conjTr_one, Matrix.one_mul] at key
      exact key

variable {σ}

theorem mem_SUid {n : ℕ} {B : GL (Fin n) F} :
    B ∈ SUid σ n ↔ (B : Matrix (Fin n) (Fin n) F).det = 1 ∧
      conjTr σ (B : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F) = 1 :=
  Iff.rfl

private theorem val_mul_val_inv {n : ℕ} (P : GL (Fin n) F) :
    (P : Matrix (Fin n) (Fin n) F) * ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

private theorem val_inv_mul_val {n : ℕ} (P : GL (Fin n) F) :
    ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

@[expose] noncomputable def conjEquiv {n : ℕ} (P : GL (Fin n) F)
    (hP : conjTr σ (P : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F) = antidiag n) :
    SU σ n ≃* SUid σ n where
  toFun A := ⟨P * A * P⁻¹, by
    obtain ⟨hdet, hiso⟩ := A.2
    set Pm := (P : Matrix (Fin n) (Fin n) F)
    set Pi := ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    set Am := ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hdet, mul_one, ← det_mul,
        val_mul_val_inv, det_one]
    · rw [Units.val_mul, Units.val_mul]
      calc conjTr σ (Pm * Am * Pi) * (Pm * Am * Pi)
          = conjTr σ Pi * (conjTr σ Am * (conjTr σ Pm * Pm) * Am) * Pi := by
            simp only [conjTr_mul, Matrix.mul_assoc]
        _ = conjTr σ Pi * (conjTr σ Pm * Pm) * Pi := by rw [hP, hiso]
        _ = conjTr σ (Pm * Pi) * (Pm * Pi) := by simp only [conjTr_mul, Matrix.mul_assoc]
        _ = 1 := by rw [val_mul_val_inv, conjTr_one, Matrix.one_mul]⟩
  invFun B := ⟨P⁻¹ * B * P, by
    obtain ⟨hdet, hiso⟩ := B.2
    set Pm := (P : Matrix (Fin n) (Fin n) F)
    set Pi := ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    set Bm := ((B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hdet, mul_one, ← det_mul,
        val_inv_mul_val, det_one]
    · rw [Units.val_mul, Units.val_mul]
      calc conjTr σ (Pi * Bm * Pm) * antidiag n * (Pi * Bm * Pm)
          = conjTr σ Pm * (conjTr σ Bm * (conjTr σ Pi * antidiag n * Pi) * Bm) * Pm := by
            simp only [conjTr_mul, Matrix.mul_assoc]
        _ = conjTr σ Pm * (conjTr σ Bm * (conjTr σ (Pm * Pi) * (Pm * Pi)) * Bm) * Pm := by
            rw [← hP]; simp only [conjTr_mul, Matrix.mul_assoc]
        _ = antidiag n := by
            rw [val_mul_val_inv, conjTr_one, Matrix.one_mul, Matrix.mul_one, hiso, Matrix.mul_one,
              hP]⟩
  left_inv A := Subtype.ext (by simp [mul_assoc])
  right_inv B := Subtype.ext (by simp [mul_assoc])
  map_mul' A B := Subtype.ext (by simp [mul_assoc])

theorem coe_conjEquiv {n : ℕ} (P : GL (Fin n) F)
    (hP : conjTr σ (P : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F) = antidiag n)
    (A : SU σ n) : ((conjEquiv P hP A : SUid σ n) : GL (Fin n) F) = P * A * P⁻¹ :=
  rfl

end General

section Witt

variable {F : Type*} [Field F] (σ : F ≃+* F)

private def herm {n : ℕ} (x y : Fin n → F) : F := ∑ r, σ (x r) * y r

private theorem herm_single_single {n : ℕ} (a b : Fin n) (x y : F) :
    herm σ (Pi.single a x) (Pi.single b y) = if a = b then σ x * y else 0 := by
  unfold herm
  split_ifs with hab
  · subst hab
    rw [Finset.sum_eq_single a (fun r _ hr => by simp [Pi.single_eq_of_ne hr]) (by simp)]
    simp
  · refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hr : r = a
    · subst hr; simp [Pi.single_eq_of_ne hab]
    · simp [Pi.single_eq_of_ne hr]

private theorem herm_add_left {n : ℕ} (x x' y : Fin n → F) :
    herm σ (x + x') y = herm σ x y + herm σ x' y := by
  simp only [herm, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

private theorem herm_add_right {n : ℕ} (x y y' : Fin n → F) :
    herm σ x (y + y') = herm σ x y + herm σ x y' := by
  simp only [herm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem herm_smul_left {n : ℕ} (c : F) (x y : Fin n → F) :
    herm σ (c • x) y = σ c * herm σ x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

private theorem herm_smul_right {n : ℕ} (c : F) (x y : Fin n → F) :
    herm σ x (c • y) = c * herm σ x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by ring

private def planeVec {n : ℕ} (k : ℕ) (hk : 2 * k + 1 < n) (x y : F) : Fin n → F :=
  Pi.single ⟨2 * k, by omega⟩ x + Pi.single ⟨2 * k + 1, hk⟩ y

private theorem herm_planeVec {n : ℕ} {k k' : ℕ} (hk : 2 * k + 1 < n) (hk' : 2 * k' + 1 < n)
    (x y x' y' : F) :
    herm σ (planeVec k hk x y) (planeVec k' hk' x' y') =
      if k = k' then σ x * x' + σ y * y' else 0 := by
  simp only [planeVec, herm_add_left, herm_add_right, herm_single_single, Fin.mk.injEq]
  by_cases h : k = k'
  · subst h; simp
  · have h1 : ¬ 2 * k = 2 * k' := by omega
    have h2 : ¬ 2 * k = 2 * k' + 1 := by omega
    have h3 : ¬ 2 * k + 1 = 2 * k' := by omega
    simp [h, h1, h2, h3]

private theorem herm_planeVec_single {n : ℕ} {k : ℕ} (hk : 2 * k + 1 < n) {a : Fin n}
    (ha : 2 * k + 1 < a.val) (x y z : F) :
    herm σ (planeVec k hk x y) (Pi.single a z) = 0 := by
  simp only [planeVec, herm_add_left, herm_single_single, Fin.ext_iff]
  have h1 : ¬ 2 * k = a.val := by omega
  have h2 : ¬ 2 * k + 1 = a.val := by omega
  simp [h1, h2]

private theorem herm_single_planeVec {n : ℕ} {k : ℕ} (hk : 2 * k + 1 < n) {a : Fin n}
    (ha : 2 * k + 1 < a.val) (x y z : F) :
    herm σ (Pi.single a z) (planeVec k hk x y) = 0 := by
  simp only [planeVec, herm_add_right, herm_single_single, Fin.ext_iff]
  have h1 : ¬ a.val = 2 * k := by omega
  have h2 : ¬ a.val = 2 * k + 1 := by omega
  simp [h1, h2]

private noncomputable def wittCol (n : ℕ) (u ω : F) (c : Fin n) : Fin n → F :=
  if hc : c.val < n / 2 then planeVec c.val (by omega) 1 u
  else if hc' : n - n / 2 ≤ c.val then
    (1 - ω)⁻¹ • planeVec (n - 1 - c.val) (by omega) 1 (u * ω)
  else Pi.single ⟨n - 1, by omega⟩ 1

private theorem wittCol_of_lt {n : ℕ} (u ω : F) {c : Fin n} (hc : c.val < n / 2) :
    wittCol n u ω c = planeVec c.val (by omega) 1 u := by
  simp only [wittCol, hc, ↓reduceDIte]

private theorem wittCol_of_ge {n : ℕ} (u ω : F) {c : Fin n} (hc : n - n / 2 ≤ c.val) :
    wittCol n u ω c = (1 - ω)⁻¹ • planeVec (n - 1 - c.val) (by omega) 1 (u * ω) := by
  have hc0 : ¬ c.val < n / 2 := by omega
  simp only [wittCol, hc0, hc, ↓reduceDIte]

private theorem wittCol_mid {n : ℕ} (u ω : F) {c : Fin n} (hc : ¬ c.val < n / 2)
    (hc' : ¬ n - n / 2 ≤ c.val) :
    wittCol n u ω c = Pi.single ⟨n - 1, by omega⟩ 1 := by
  simp only [wittCol, hc, hc', ↓reduceDIte]

private theorem herm_wittCol {n : ℕ} {u ω : F}
    (hu : σ u * u = -1) (hω : σ ω * ω = 1) (hω1 : ω ≠ 1) (a b : Fin n) :
    herm σ (wittCol n u ω a) (wittCol n u ω b) = if b.val = n - (a.val + 1) then 1 else 0 := by
  have hs : (1 - ω) ≠ 0 := sub_ne_zero.mpr (Ne.symm hω1)
  have ha := a.isLt
  have hb := b.isLt
  have hsσ : σ (1 - ω)⁻¹ * (1 - σ ω) = 1 := by
    rw [map_inv₀, show (1 - σ ω) = σ (1 - ω) by rw [map_sub, map_one]]
    exact inv_mul_cancel₀ (by rwa [Ne, map_eq_zero_iff _ σ.injective])
  have key1 : σ 1 * 1 + σ u * u = 0 := by rw [map_one, one_mul, hu]; ring
  have key2 : σ 1 * 1 + σ u * (u * ω) = 1 - ω := by
    rw [map_one, one_mul, ← mul_assoc, hu]; ring
  have key3 : σ 1 * 1 + σ (u * ω) * u = 1 - σ ω := by
    rw [map_one, one_mul, map_mul, mul_comm (σ u), mul_assoc, hu]; ring
  have key4 : σ 1 * 1 + σ (u * ω) * (u * ω) = 0 := by
    rw [map_one, one_mul, map_mul,
      show σ u * σ ω * (u * ω) = (σ u * u) * (σ ω * ω) by ring, hu, hω]; ring
  by_cases ha1 : a.val < n / 2
  · rw [wittCol_of_lt u ω ha1]
    by_cases hb1 : b.val < n / 2
    · rw [wittCol_of_lt u ω hb1, herm_planeVec]
      have : ¬ b.val = n - (a.val + 1) := by omega
      simp only [this, ↓reduceIte]
      split_ifs
      · exact key1
      · rfl
    · by_cases hb2 : n - n / 2 ≤ b.val
      · rw [wittCol_of_ge u ω hb2, herm_smul_right, herm_planeVec]
        by_cases hab : b.val = n - (a.val + 1)
        · have h' : a.val = n - 1 - b.val := by omega
          rw [ite_eq_left h', ite_eq_left hab, key2, inv_mul_cancel₀ hs]
        · have h' : ¬ a.val = n - 1 - b.val := by omega
          rw [ite_eq_right h', ite_eq_right hab, mul_zero]
      · have hab : ¬ b.val = n - (a.val + 1) := by omega
        rw [wittCol_mid u ω hb1 hb2, herm_planeVec_single σ _ (by simp; omega)]
        simp only [hab, ↓reduceIte]
  · by_cases ha2 : n - n / 2 ≤ a.val
    · rw [wittCol_of_ge u ω ha2, herm_smul_left]
      by_cases hb1 : b.val < n / 2
      · rw [wittCol_of_lt u ω hb1, herm_planeVec]
        by_cases hab : b.val = n - (a.val + 1)
        · have h' : n - 1 - a.val = b.val := by omega
          rw [ite_eq_left h', ite_eq_left hab, key3, hsσ]
        · have h' : ¬ n - 1 - a.val = b.val := by omega
          rw [ite_eq_right h', ite_eq_right hab, mul_zero]
      · by_cases hb2 : n - n / 2 ≤ b.val
        · rw [wittCol_of_ge u ω hb2, herm_smul_right, herm_planeVec]
          have hab : ¬ b.val = n - (a.val + 1) := by omega
          simp only [hab, ↓reduceIte]
          split_ifs
          · rw [key4, mul_zero, mul_zero]
          · rw [mul_zero, mul_zero]
        · have hab : ¬ b.val = n - (a.val + 1) := by omega
          rw [wittCol_mid u ω hb1 hb2, herm_planeVec_single σ _ (by simp; omega), mul_zero]
          simp only [hab, ↓reduceIte]
    · rw [wittCol_mid u ω ha1 ha2]
      by_cases hb1 : b.val < n / 2
      · have hab : ¬ b.val = n - (a.val + 1) := by omega
        rw [wittCol_of_lt u ω hb1, herm_single_planeVec σ _ (by simp; omega)]
        simp only [hab, ↓reduceIte]
      · by_cases hb2 : n - n / 2 ≤ b.val
        · have hab : ¬ b.val = n - (a.val + 1) := by omega
          rw [wittCol_of_ge u ω hb2, herm_smul_right, herm_single_planeVec σ _
            (by simp; omega), mul_zero]
          simp only [hab, ↓reduceIte]
        · have hab : b.val = n - (a.val + 1) := by omega
          rw [wittCol_mid u ω hb1 hb2, herm_single_single]
          simp only [hab, ↓reduceIte, map_one, one_mul]

private theorem wittMatrix_gram {n : ℕ} {u ω : F}
    (hu : σ u * u = -1) (hω : σ ω * ω = 1) (hω1 : ω ≠ 1) :
    conjTr σ (Matrix.of fun r c => wittCol n u ω c r) * (Matrix.of fun r c => wittCol n u ω c r) =
      antidiag n := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [conjTr, transpose_apply, map_apply, of_apply, antidiag, Fin.ext_iff, Fin.val_rev]
  exact herm_wittCol σ hu hω hω1 a b

theorem antidiag_mul_self (n : ℕ) : (antidiag n : Matrix (Fin n) (Fin n) F) * antidiag n = 1 := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev a)]
  · simp only [antidiag, of_apply, ↓reduceIte, one_mul, Fin.rev_rev, Matrix.one_apply]
    by_cases h : b = a
    · simp [h]
    · simp [h, Ne.symm h]
  · intro c _ hc
    simp [antidiag, hc]
  · simp

theorem det_antidiag_ne_zero (n : ℕ) : (antidiag n : Matrix (Fin n) (Fin n) F).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (antidiag_mul_self (F := F) n)
  rw [det_mul, h, zero_mul, det_one] at this
  exact zero_ne_one this

theorem exists_wittMatrix_of {n : ℕ} {u ω : F} (hu : σ u * u = -1) (hω : σ ω * ω = 1)
    (hω1 : ω ≠ 1) :
    ∃ P : GL (Fin n) F, conjTr σ (P : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F) =
      antidiag n := by
  set M : Matrix (Fin n) (Fin n) F := Matrix.of fun r c => wittCol n u ω c r
  have hM := wittMatrix_gram σ (n := n) hu hω hω1
  have hdet : M.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hM
    rw [det_mul, h, mul_zero] at this
    exact det_antidiag_ne_zero n this.symm
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, hM⟩

end Witt

section Finite

open CFSG.LieType.BorelTits

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

omit [Finite F] [Fact p.Prime] [CharP F p] in
theorem det_eq_one_of_mem_statedSU {n q : ℕ} {B : GL (Fin n) F} (hB : B ∈ StatedSU n q F) :
    (B : Matrix (Fin n) (Fin n) F).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSU hB

theorem SUid_eq_statedSU (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ) :
    SUid (unitaryInvolution F p f) n = StatedSU n (p ^ f) F := by
  ext B
  constructor
  · rintro ⟨hdet, hiso⟩
    have hpres := (unitaryForm_preserves_iff hF (B : Matrix (Fin n) (Fin n) F)).mpr hiso
    have hmem := mkOfDetNeZero_mem_statedSU hF (B : Matrix (Fin n) (Fin n) F) hdet hpres
    convert hmem using 1
    ext1
    rfl
  · intro hB
    exact ⟨det_eq_one_of_mem_statedSU hB,
      (unitaryForm_preserves_iff hF _).mp (statedSU_preserves hF hB)⟩

omit [Fact p.Prime] [CharP F p] in
private theorem card_units_eq (hF : Nat.card F = (p ^ f) ^ 2) :
    Nat.card Fˣ = (p ^ f) ^ 2 - 1 := by
  classical
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hF]

omit [Fact p.Prime] [CharP F p] in
private theorem one_lt_pow (hF : Nat.card F = (p ^ f) ^ 2) : 1 < p ^ f := by
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  rw [hF] at h1
  by_contra h
  have : p ^ f ≤ 1 := not_lt.mp h
  nlinarith [Nat.zero_le (p ^ f)]

private theorem norm_eq_pow (c : F) :
    unitaryInvolution F p f c * c = c ^ (p ^ f + 1) := by
  rw [unitaryInvolution_apply, pow_succ]

theorem exists_norm_eq_one_ne_one (hF : Nat.card F = (p ^ f) ^ 2) :
    ∃ ω : F, unitaryInvolution F p f ω * ω = 1 ∧ ω ≠ 1 := by
  have hp := (Fact.out : p.Prime)
  have hq := one_lt_pow hF
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, card_units_eq hF]
  refine ⟨((g ^ (p ^ f - 1) : Fˣ) : F), ?_, ?_⟩
  · rw [norm_eq_pow, ← Units.val_pow_eq_pow_val, ← pow_mul]
    have : (p ^ f - 1) * (p ^ f + 1) = (p ^ f) ^ 2 - 1 := by
      have h1 : 1 ≤ p ^ f := hq.le
      zify [h1, Nat.one_le_pow 2 _ (by omega : 0 < p ^ f)]
      ring
    rw [this, ← hord, pow_orderOf_eq_one, Units.val_one]
  · intro h
    have h1 : g ^ (p ^ f - 1) = 1 := Units.ext h
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at h2
    have h3 : (p ^ f) ^ 2 - 1 ≤ p ^ f - 1 := Nat.le_of_dvd (by omega) h2
    have : p ^ f < (p ^ f) ^ 2 := by nlinarith
    omega

theorem exists_norm_eq_neg_one (hF : Nat.card F = (p ^ f) ^ 2) :
    ∃ u : F, unitaryInvolution F p f u * u = -1 := by
  have hp := (Fact.out : p.Prime)
  have hq := one_lt_pow hF
  rcases hp.eq_two_or_odd' with rfl | hodd
  · refine ⟨1, ?_⟩
    rw [map_one, one_mul]
    exact (CharTwo.neg_eq (1 : F)).symm
  · obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
    have hord : orderOf g = (p ^ f) ^ 2 - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, card_units_eq hF]
    obtain ⟨t, ht⟩ : ∃ t, p ^ f = 2 * t + 1 := Odd.pow hodd
    refine ⟨((g ^ t : Fˣ) : F), ?_⟩
    rw [norm_eq_pow, ← Units.val_pow_eq_pow_val, ← pow_mul]
    set x := g ^ (t * (p ^ f + 1)) with hx
    have hsq : x ^ 2 = 1 := by
      rw [hx, ← pow_mul]
      have : t * (p ^ f + 1) * 2 = orderOf g := by
        rw [hord, ht, show (2 * t + 1) ^ 2 = t * (2 * t + 1 + 1) * 2 + 1 by ring,
          Nat.add_sub_cancel]
      rw [this, pow_orderOf_eq_one]
    have hne : x ≠ 1 := by
      intro h1
      have h2 := orderOf_dvd_of_pow_eq_one (show g ^ (t * (p ^ f + 1)) = 1 from h1)
      rw [hord] at h2
      have htpos : 0 < t := by
        rcases Nat.eq_zero_or_pos t with h0 | h0
        · rw [h0] at ht; omega
        · exact h0
      have h3 : (p ^ f) ^ 2 - 1 ≤ t * (p ^ f + 1) := Nat.le_of_dvd (by positivity) h2
      rw [ht, show (2 * t + 1) ^ 2 = t * (2 * t + 1 + 1) * 2 + 1 by ring,
        Nat.add_sub_cancel] at h3
      nlinarith
    have hval : (x : F) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, hsq, Units.val_one]
    have hval' : (x : F) ≠ 1 := fun h => hne (Units.ext h)
    rw [pow_two] at hval
    rcases mul_self_eq_one_iff.mp hval with h | h
    · exact absurd h hval'
    · exact h

theorem exists_wittMatrix (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ) :
    ∃ P : GL (Fin n) F, conjTr (unitaryInvolution F p f) (P : Matrix (Fin n) (Fin n) F) *
      (P : Matrix (Fin n) (Fin n) F) = antidiag n := by
  obtain ⟨u, hu⟩ := exists_norm_eq_neg_one hF
  obtain ⟨ω, hω, hω1⟩ := exists_norm_eq_one_ne_one hF
  exact exists_wittMatrix_of _ hu hω hω1

noncomputable def equivStatedSU (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ) :
    SU (unitaryInvolution F p f) n ≃* StatedSU n (p ^ f) F :=
  (conjEquiv (exists_wittMatrix hF n).choose (exists_wittMatrix hF n).choose_spec).trans
    (MulEquiv.subgroupCongr (SUid_eq_statedSU hF n))

end Finite

end CFSG.LieType.Universal.Unitary
