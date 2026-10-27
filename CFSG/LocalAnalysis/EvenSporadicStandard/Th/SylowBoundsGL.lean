module

public import CFSG.Quasithin.Background.FFC3Unitri

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Matrix CFSG.Quasithin.FFC

namespace SylowBounds

abbrev P6 := Fin 6 → ZMod 2

@[expose] def fixCard (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) : ℕ :=
  (Finset.univ.filter fun v : Fin 4 → ZMod 2 => M *ᵥ v = v).card

theorem fixCard_eq_natCard (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    fixCard M = Nat.card {v : Fin 4 → ZMod 2 // M *ᵥ v = v} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

@[expose] def tup (x : GL (Fin 4) (ZMod 2)) : P6 :=
  ![(x : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 1, (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 2,
    (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 3, (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 2,
    (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 3, (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) 2 3]

@[expose] def mk6 (a : P6) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, a 0, a 1, a 2; 0, 1, a 3, a 4; 0, 0, 1, a 5; 0, 0, 0, 1]

@[expose] def CommS (a b : P6) : Prop :=
  a 0 * b 3 = b 0 * a 3 ∧ a 3 * b 5 = b 3 * a 5 ∧ a 0 * b 4 + a 1 * b 5 = b 0 * a 4 + b 1 * a 5

instance (a b : P6) : Decidable (CommS a b) := by unfold CommS; infer_instance

theorem val_eq_mk6 {x : GL (Fin 4) (ZMod 2)} (hx : x ∈ UT 4) :
    (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) = mk6 (tup x) := by
  have h00 := UT_diag hx 0
  have h11 := UT_diag hx 1
  have h22 := UT_diag hx 2
  have h33 := UT_diag hx 3
  have h10 := mem_UT.1 hx 1 0 (by decide)
  have h20 := mem_UT.1 hx 2 0 (by decide)
  have h30 := mem_UT.1 hx 3 0 (by decide)
  have h21 := mem_UT.1 hx 2 1 (by decide)
  have h31 := mem_UT.1 hx 3 1 (by decide)
  have h32 := mem_UT.1 hx 3 2 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mk6, tup, h00, h11, h22, h33, h10, h20, h30, h21, h31, h32]

theorem tup_injOn {x y : GL (Fin 4) (ZMod 2)} (hx : x ∈ UT 4) (hy : y ∈ UT 4)
    (h : tup x = tup y) : x = y :=
  Units.ext (by rw [val_eq_mk6 hx, val_eq_mk6 hy, h])

theorem commS_tup {x y : GL (Fin 4) (ZMod 2)} (hx : x ∈ UT 4) (hy : y ∈ UT 4)
    (h : x * y = y * x) : CommS (tup x) (tup y) := by
  have hxy := congrArg (fun z : GL (Fin 4) (ZMod 2) => (z : Matrix (Fin 4) (Fin 4) (ZMod 2))) h
  simp only [Units.val_mul] at hxy
  rw [val_eq_mk6 hx, val_eq_mk6 hy] at hxy
  have e02 := congrFun (congrFun hxy 0) 2
  have e13 := congrFun (congrFun hxy 1) 3
  have e03 := congrFun (congrFun hxy 0) 3
  simp [mk6, Matrix.mul_apply, Fin.sum_univ_four] at e02 e13 e03
  refine ⟨?_, ?_, ?_⟩
  · linear_combination e02
  · linear_combination e13
  · linear_combination e03

@[expose] def E32 : Finset P6 :=
  Finset.univ.filter fun t => 32 ≤ (Finset.univ.filter fun s => CommS t s).card

set_option maxRecDepth 100000 in
theorem card_E32 : E32.card ≤ 8 := by
  unfold E32
  decide

theorem card_lt_32 (R : Finset P6) (hR : ∀ a ∈ R, ∀ b ∈ R, CommS a b) : R.card < 32 := by
  by_contra hcon
  push Not at hcon
  have hsub : R ⊆ E32 := by
    intro a ha
    unfold E32
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have : R ⊆ Finset.univ.filter fun s => CommS a s := by
      intro b hb
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hR a ha b hb⟩
    exact hcon.trans (Finset.card_le_card this)
  have := Finset.card_le_card hsub
  have := card_E32
  omega

@[expose] def TvSet : Finset P6 := Finset.univ.filter fun a => a = 0 ∨ 8 ≤ fixCard (mk6 a)

@[expose] def z0 : P6 := ![0, 0, 1, 0, 0, 0]

set_option maxRecDepth 100000 in
theorem card_comm_tv :
    ∀ a ∈ TvSet, a ≠ 0 → a ≠ z0 → (TvSet.filter fun s => CommS a s).card ≤ 14 := by
  unfold TvSet z0
  decide

theorem card_le_14 (R : Finset P6) (hR : ∀ a ∈ R, ∀ b ∈ R, CommS a b) (hT : R ⊆ TvSet) :
    R.card ≤ 14 := by
  by_cases h : ∃ a ∈ R, a ≠ 0 ∧ a ≠ z0
  · obtain ⟨a, haR, ha0, haz⟩ := h
    have hsub : R ⊆ TvSet.filter fun s => CommS a s := fun b hb =>
      Finset.mem_filter.2 ⟨hT hb, hR a haR b hb⟩
    exact (Finset.card_le_card hsub).trans (card_comm_tv a (hT haR) ha0 haz)
  · push Not at h
    have hsub : R ⊆ {0, z0} := fun a ha => by
      by_cases h0 : a = 0
      · simp [h0]
      · simp [h a ha h0]
    exact (Finset.card_le_card hsub).trans (Finset.card_le_two.trans (by norm_num))

theorem fixCard_conj (h x : GL (Fin 4) (ZMod 2)) :
    fixCard ((h⁻¹ * x * h : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      fixCard (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
  set H : Matrix (Fin 4) (Fin 4) (ZMod 2) := (h : Matrix (Fin 4) (Fin 4) (ZMod 2)) with hH
  set Hi : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
    ((h⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) with hHi
  set X : Matrix (Fin 4) (Fin 4) (ZMod 2) := (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) with hX
  have h1 : H * Hi = 1 := by rw [hH, hHi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : Hi * H = 1 := by rw [hH, hHi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have key : ∀ v, (Hi * X * H) *ᵥ v = v ↔ X *ᵥ (H *ᵥ v) = H *ᵥ v := by
    intro v
    constructor
    · intro hv
      calc X *ᵥ (H *ᵥ v) = (X * H) *ᵥ v := Matrix.mulVec_mulVec v X H
        _ = (H * (Hi * X * H)) *ᵥ v := by rw [← mul_assoc, ← mul_assoc, h1, one_mul]
        _ = H *ᵥ ((Hi * X * H) *ᵥ v) := (Matrix.mulVec_mulVec v H _).symm
        _ = H *ᵥ v := by rw [hv]
    · intro hv
      calc (Hi * X * H) *ᵥ v = Hi *ᵥ (X *ᵥ (H *ᵥ v)) := by
            rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
        _ = Hi *ᵥ (H *ᵥ v) := by rw [hv]
        _ = v := by rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  unfold fixCard
  rw [Units.val_mul, Units.val_mul]
  refine Finset.card_nbij' (fun v => H *ᵥ v) (fun v => Hi *ᵥ v) ?_ ?_ ?_ ?_
  · intro v hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
    exact (key v).1 hv
  · intro v hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
    have e : H *ᵥ (Hi *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    rw [key, e]
    exact hv
  · intro v _
    simp [Matrix.mulVec_mulVec, h2]
  · intro v _
    simp [Matrix.mulVec_mulVec, h1]

theorem tup_one : tup (1 : GL (Fin 4) (ZMod 2)) = 0 := by
  ext i
  fin_cases i <;> simp [tup]

theorem exists_conj_le_UT {Q : Subgroup (GL (Fin 4) (ZMod 2))} (hQ : IsPGroup 2 Q) :
    ∃ h : GL (Fin 4) (ZMod 2), ∀ x ∈ Q, h⁻¹ * x * h ∈ UT 4 := by
  obtain ⟨P, hQP⟩ := hQ.exists_le_sylow
  obtain ⟨h, hh⟩ := exists_conj_UT P.isPGroup' P.not_dvd_index
  exact ⟨h, fun x hx => (hh x).1 (hQP hx)⟩

theorem exists_coords {Q : Subgroup (GL (Fin 4) (ZMod 2))} (hQ : IsPGroup 2 Q)
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) :
    ∃ (h : GL (Fin 4) (ZMod 2)) (R : Finset P6), R.card = Nat.card Q ∧
      (∀ a ∈ R, ∀ b ∈ R, CommS a b) ∧
      ∀ a ∈ R, ∃ x ∈ Q, h⁻¹ * x * h ∈ UT 4 ∧ a = tup (h⁻¹ * x * h) := by
  classical
  obtain ⟨h, hh⟩ := exists_conj_le_UT hQ
  have : Fintype Q := Fintype.ofFinite Q
  refine ⟨h, Finset.univ.image fun q : Q => tup (h⁻¹ * (q : GL (Fin 4) (ZMod 2)) * h), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective, Finset.card_univ, Nat.card_eq_fintype_card]
    intro q q' hqq
    have := tup_injOn (hh q q.2) (hh q' q'.2) hqq
    exact Subtype.ext (by simpa using this)
  · intro a ha b hb
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb
    obtain ⟨q, rfl⟩ := ha
    obtain ⟨q', rfl⟩ := hb
    refine commS_tup (hh q q.2) (hh q' q'.2) ?_
    calc h⁻¹ * (q : GL (Fin 4) (ZMod 2)) * h * (h⁻¹ * (q' : GL (Fin 4) (ZMod 2)) * h)
        = h⁻¹ * ((q : GL (Fin 4) (ZMod 2)) * q') * h := by group
      _ = h⁻¹ * ((q' : GL (Fin 4) (ZMod 2)) * q) * h := by rw [hcomm q q.2 q' q'.2]
      _ = h⁻¹ * (q' : GL (Fin 4) (ZMod 2)) * h * (h⁻¹ * (q : GL (Fin 4) (ZMod 2)) * h) := by
        group
  · intro a ha
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha
    obtain ⟨q, rfl⟩ := ha
    exact ⟨q, q.2, hh q q.2, rfl⟩

theorem card_le_sixteen {Q : Subgroup (GL (Fin 4) (ZMod 2))} (hQ : IsPGroup 2 Q)
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) : Nat.card Q ≤ 16 := by
  obtain ⟨h, R, hRc, hRcomm, -⟩ := exists_coords hQ hcomm
  have h1 := card_lt_32 R hRcomm
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  rw [hn] at hRc ⊢
  by_contra hcon
  have hn5 : 5 ≤ n := by
    by_contra h5
    push Not at h5
    have : 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn5
  omega

theorem card_le_eight_of_transvections {Q : Subgroup (GL (Fin 4) (ZMod 2))}
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) (hsq : ∀ x ∈ Q, x * x = 1)
    (htv : ∀ x ∈ Q, x ≠ 1 → 8 ≤ fixCard (x : Matrix (Fin 4) (Fin 4) (ZMod 2))) :
    Nat.card Q ≤ 8 := by
  have hQ : IsPGroup 2 Q := fun g => ⟨1, by
    rw [pow_one, sq]
    exact Subtype.ext (hsq g g.2)⟩
  obtain ⟨h, R, hRc, hRcomm, hRmem⟩ := exists_coords hQ hcomm
  have hRT : R ⊆ TvSet := by
    intro a ha
    obtain ⟨x, hxQ, hxU, rfl⟩ := hRmem a ha
    unfold TvSet
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    by_cases hx1 : x = 1
    · left
      rw [hx1]
      simpa using tup_one
    · right
      rw [← val_eq_mk6 hxU, fixCard_conj]
      exact htv x hxQ hx1
  have h1 := card_le_14 R hRcomm hRT
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  rw [hn] at hRc ⊢
  by_contra hcon
  have hn4 : 4 ≤ n := by
    by_contra h4
    push Not at h4
    have : 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn4
  omega

end SylowBounds

end CFSG.EvenSporadicStandard.ThStd
