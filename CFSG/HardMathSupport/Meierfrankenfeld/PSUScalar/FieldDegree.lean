module

public import CFSG.LieType.Universal.Unitary.BinaryModel.Weight
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.DoubledWord

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.HardMathSupport.U4FF
open Matrix

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2] {k : Type} [Field k] {n : ℕ}

@[expose] def labelStar {n : ℕ} (j : Fin n) : Fin n :=
  ⟨(n - (j : ℕ)) % n, Nat.mod_lt _ (Fin.pos j)⟩

theorem labelStar_apply (j : Fin n) : (labelStar j : ℕ) = (n - (j : ℕ)) % n := rfl

theorem labelStar_eq_of_ne_zero {j : Fin n} (hj : j.val ≠ 0) :
    labelStar j = ⟨n - (j : ℕ), by have := j.isLt; omega⟩ := by
  ext
  simp only [labelStar, Fin.val_mk]
  rw [Nat.mod_eq_of_lt]
  omega

theorem labelStar_labelStar (j : Fin n) : labelStar (labelStar j) = j := by
  by_cases h0 : j.val = 0
  · have h1 : labelStar j = j := by
      ext
      simp only [labelStar, Fin.val_mk]
      rw [h0, Nat.sub_zero, Nat.mod_self]
    rw [h1, h1]
  · have hne : (n - (j : ℕ)) ≠ 0 := by have := j.isLt; omega
    rw [labelStar_eq_of_ne_zero h0, labelStar_eq_of_ne_zero hne]
    ext
    change n - (n - (j : ℕ)) = (j : ℕ)
    omega

theorem labelStar_injective : Function.Injective (labelStar (n := n)) :=
  Function.Involutive.injective labelStar_labelStar

theorem labelStar_bijective : Function.Bijective (labelStar (n := n)) :=
  Function.Involutive.bijective labelStar_labelStar

theorem mem_image_labelStar_iff {s : Finset (Fin n)} {j : Fin n} :
    j ∈ s.image labelStar ↔ labelStar j ∈ s := by
  constructor
  · intro h
    rw [Finset.mem_image] at h
    obtain ⟨a, ha, rfl⟩ := h
    rwa [labelStar_labelStar]
  · intro h
    exact Finset.mem_image.mpr ⟨labelStar j, h, labelStar_labelStar j⟩

theorem image_labelStar_image (s : Finset (Fin n)) :
    (s.image labelStar).image labelStar = s := by
  ext j
  rw [mem_image_labelStar_iff, mem_image_labelStar_iff, labelStar_labelStar]

theorem erase_image_labelStar (s : Finset (Fin n)) (j : Fin n) :
    (s.erase j).image labelStar = (s.image labelStar).erase (labelStar j) := by
  ext a
  rw [mem_image_labelStar_iff, Finset.mem_erase, Finset.mem_erase, mem_image_labelStar_iff]
  constructor
  · rintro ⟨hne, hmem⟩
    refine ⟨?_, hmem⟩
    intro h
    apply hne
    rw [h, labelStar_labelStar]
  · rintro ⟨hne, hmem⟩
    refine ⟨?_, hmem⟩
    intro h
    apply hne
    rw [← labelStar_labelStar a, h]

theorem nodeLo_lt {n : ℕ} (s : Fin (n / 2)) : (s : ℕ) + 1 < n :=
  lt_of_le_of_lt (Nat.succ_le_of_lt s.isLt)
    (Nat.div_lt_self (lt_of_lt_of_le (Fin.pos s) (Nat.div_le_self n 2)) (by norm_num))

theorem nodeHi_lt {n : ℕ} (s : Fin (n / 2)) : n - 1 - (s : ℕ) < n :=
  lt_of_le_of_lt (Nat.sub_le _ _)
    (Nat.sub_lt (lt_of_lt_of_le (Fin.pos s) (Nat.div_le_self n 2)) (by norm_num))

theorem labelStar_nodeLo (s : Fin (n / 2)) :
    labelStar (⟨(s : ℕ) + 1, nodeLo_lt s⟩ : Fin n) =
      ⟨n - 1 - (s : ℕ), nodeHi_lt s⟩ := by
  rw [labelStar_eq_of_ne_zero (by simp)]
  ext
  change n - ((s : ℕ) + 1) = n - 1 - (s : ℕ)
  omega

theorem labelStar_nodeHi (s : Fin (n / 2)) :
    labelStar (⟨n - 1 - (s : ℕ), nodeHi_lt s⟩ : Fin n) =
      ⟨(s : ℕ) + 1, nodeLo_lt s⟩ := by
  have h := congrArg labelStar (labelStar_nodeLo s)
  rw [labelStar_labelStar] at h
  exact h.symm

@[expose] def rotEps (hf : 0 < f) (ε : Fin f → Finset (Fin n)) : Fin f → Finset (Fin n) :=
  fun r => if h : (r : ℕ) = 0 then (ε ⟨f - 1, by omega⟩).image labelStar
    else ε ⟨(r : ℕ) - 1, by have := r.isLt; omega⟩

private theorem rotEps_apply_zero {m : ℕ} (hf : 0 < m + 1) (ε : Fin (m + 1) → Finset (Fin n)) :
    rotEps hf ε (0 : Fin (m + 1)) = (ε (Fin.last m)).image labelStar := by
  simp only [rotEps]
  exact congrArg (fun t => (ε t).image labelStar) (Fin.ext rfl)

private theorem rotEps_apply_succ {m : ℕ} (hf : 0 < m + 1) (ε : Fin (m + 1) → Finset (Fin n))
    (s : Fin m) : rotEps hf ε (Fin.succ s) = ε (Fin.castSucc s) := by
  simp only [rotEps, Fin.val_succ]
  rw [dif_neg (by simp)]
  exact congrArg ε (Fin.ext rfl)

theorem isFullNode_image_labelStar_iff (ε : Fin f → Finset (Fin n)) (s : Fin (n / 2)) :
    IsFullNode (fun r => (ε r).image labelStar) s ↔ IsFullNode ε s := by
  constructor
  · intro h r
    have h1 : (⟨(s : ℕ) + 1, nodeLo_lt s⟩ : Fin n) ∈ (ε r).image labelStar := (h r).1
    have h2 : (⟨n - 1 - (s : ℕ), nodeHi_lt s⟩ : Fin n) ∈ (ε r).image labelStar := (h r).2
    rw [mem_image_labelStar_iff, labelStar_nodeLo] at h1
    rw [mem_image_labelStar_iff, labelStar_nodeHi] at h2
    exact ⟨h2, h1⟩
  · intro h r
    have h1 : (⟨(s : ℕ) + 1, nodeLo_lt s⟩ : Fin n) ∈ ε r := (h r).1
    have h2 : (⟨n - 1 - (s : ℕ), nodeHi_lt s⟩ : Fin n) ∈ ε r := (h r).2
    exact ⟨(mem_image_labelStar_iff).mpr (by simpa [labelStar_nodeLo] using h2),
      (mem_image_labelStar_iff).mpr (by simpa [labelStar_nodeHi] using h1)⟩

theorem isFullNode_rotEps_iff (hf : 0 < f) (ε : Fin f → Finset (Fin n))
    (s : Fin (n / 2)) : IsFullNode (rotEps hf ε) s ↔ IsFullNode ε s := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hf)
  let lo : Fin n := ⟨(s : ℕ) + 1, by have := s.isLt; omega⟩
  let hi : Fin n := ⟨n - 1 - (s : ℕ), by have := s.isLt; omega⟩
  let P : (Fin (m + 1) → Finset (Fin n)) → Fin (m + 1) → Prop :=
    fun δ r => lo ∈ δ r ∧ hi ∈ δ r
  have hsplit : (∀ r, P ε r) ↔ (∀ t : Fin m, P ε (Fin.castSucc t)) ∧ P ε (Fin.last m) :=
    Fin.forall_fin_succ'
  have hsplitRot : (∀ r, P (rotEps hf ε) r) ↔
      P (rotEps hf ε) 0 ∧ ∀ t : Fin m, P (rotEps hf ε) (Fin.succ t) := by
    constructor
    · intro h
      exact ⟨h 0, fun t => h (Fin.succ t)⟩
    · rintro ⟨h0, ht⟩ r
      rcases Fin.eq_zero_or_eq_succ r with rfl | ⟨t, rfl⟩
      · exact h0
      · exact ht t
  have h0 : P (rotEps hf ε) 0 ↔ P ε (Fin.last m) := by
    have hmem : lo ∈ (ε (Fin.last m)).image labelStar ↔ hi ∈ ε (Fin.last m) := by
      rw [mem_image_labelStar_iff, labelStar_nodeLo]
    have hmem' : hi ∈ (ε (Fin.last m)).image labelStar ↔ lo ∈ ε (Fin.last m) := by
      rw [mem_image_labelStar_iff, labelStar_nodeHi]
    constructor
    · intro h
      change lo ∈ rotEps hf ε 0 ∧ hi ∈ rotEps hf ε 0 at h
      rw [rotEps_apply_zero] at h
      exact ⟨hmem'.mp h.2, hmem.mp h.1⟩
    · intro h
      change lo ∈ rotEps hf ε 0 ∧ hi ∈ rotEps hf ε 0
      rw [rotEps_apply_zero]
      exact ⟨hmem.mpr h.2, hmem'.mpr h.1⟩
  have hsucc : ∀ t : Fin m, P (rotEps hf ε) (Fin.succ t) ↔ P ε (Fin.castSucc t) := by
    intro t
    change lo ∈ rotEps hf ε (Fin.succ t) ∧ hi ∈ rotEps hf ε (Fin.succ t) ↔
      lo ∈ ε (Fin.castSucc t) ∧ hi ∈ ε (Fin.castSucc t)
    rw [rotEps_apply_succ]
  change (∀ r, P (rotEps hf ε) r) ↔ (∀ r, P ε r)
  rw [hsplitRot, hsplit]
  constructor
  · rintro ⟨h0r, hs⟩
    exact ⟨fun t => (hsucc t).mp (hs t), h0.mp h0r⟩
  · rintro ⟨hs, hlast⟩
    exact ⟨h0.mpr hlast, fun t => (hsucc t).mpr (hs t)⟩

private theorem sum_digit_eq {f n : ℕ} (ε : Fin f → Finset (Fin n)) (p : Fin n → Prop)
    [DecidablePred p] :
    (∑ j : Fin n, if p j then bDigit ε j else 0)
      = ∑ r : Fin f, 2 ^ (r : ℕ) * ((ε r).filter p).card := by
  have h1 : (∑ j : Fin n, if p j then bDigit ε j else 0)
      = ∑ j : Fin n, ∑ r : Fin f, (if p j ∧ j ∈ ε r then 2 ^ (r : ℕ) else 0) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hp : p j
    · simp only [hp, if_true, bDigit]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hj : j ∈ ε r <;> simp [hj]
    · simp [hp]
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h2 : (∑ j : Fin n, if p j ∧ j ∈ ε r then 2 ^ (r : ℕ) else 0)
      = ∑ j : Fin n, 2 ^ (r : ℕ) * (if p j ∧ j ∈ ε r then 1 else 0) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : p j ∧ j ∈ ε r <;> simp [h]
  rw [h2]
  have h3 : (∑ j : Fin n, 2 ^ (r : ℕ) * (if p j ∧ j ∈ ε r then 1 else 0))
      = 2 ^ (r : ℕ) * ∑ j : Fin n, (if j ∈ ε r then (if p j then 1 else 0) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j ∈ ε r <;> by_cases hp : p j <;> simp [hj, hp]
  rw [h3, Finset.sum_ite_mem, Finset.sum_boole]
  simp

private theorem bExp_eq_sum_bDigit {f n : ℕ} (ε : Fin f → Finset (Fin n)) (a : Fin n) :
    bExp ε a = ∑ j : Fin n, if a < j then bDigit ε j else 0 := by
  rw [bExp]
  exact (sum_digit_eq ε (fun j => a < j)).symm

private def expZero {f n : ℕ} (ε : Fin f → Finset (Fin n)) : ℕ :=
  ∑ r : Fin f, 2 ^ (r : ℕ) * ((ε r).filter fun j => j.val ≠ 0).card

private theorem expZero_eq_sum {f n : ℕ} (ε : Fin f → Finset (Fin n)) :
    expZero ε = ∑ j : Fin n, if j.val ≠ 0 then bDigit ε j else 0 :=
  (sum_digit_eq ε (fun j => j.val ≠ 0)).symm

private theorem bDigit_image {f n : ℕ} (ε : Fin f → Finset (Fin n)) (j : Fin n) :
    bDigit (fun r => (ε r).image labelStar) j = bDigit ε (labelStar j) := by
  rw [bDigit, bDigit]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h : labelStar j ∈ ε r
  · rw [if_pos ((mem_image_labelStar_iff).mpr h), if_pos h]
  · rw [if_neg (fun hh => h ((mem_image_labelStar_iff).mp hh)), if_neg h]

private theorem bExp_image_add {f n : ℕ} (ε : Fin f → Finset (Fin n)) (a : Fin n) :
    bExp (fun r => (ε r).image labelStar) a + bExp ε (Fin.rev a) = expZero ε := by
  rw [bExp_eq_sum_bDigit, bExp_eq_sum_bDigit]
  have h1 : (∑ j : Fin n, if a < j then
        bDigit (fun r => (ε r).image labelStar) j else 0)
      = ∑ j : Fin n, if a < labelStar j then bDigit ε j else 0 := by
    refine Fintype.sum_bijective labelStar labelStar_bijective _ _ ?_
    intro j
    simp [bDigit_image, labelStar_labelStar]
  rw [h1, expZero_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h0 : j.val = 0
  · have hp : ¬ (a < labelStar j) := by
      simp only [Fin.lt_def]
      have : (labelStar j : ℕ) = 0 := by
        rw [labelStar_apply, h0, Nat.sub_zero, Nat.mod_self]
      omega
    have hq : ¬ (Fin.rev a < j) := by
      simp only [Fin.lt_def, Fin.val_rev]
      omega
    simp [h0, hp, hq]
  · have hpv : (a < labelStar j) ↔ ¬ (Fin.rev a < j) := by
      simp only [Fin.lt_def, Fin.val_rev]
      have : (labelStar j : ℕ) = n - (j : ℕ) := by
        rw [labelStar_eq_of_ne_zero h0]
      omega
    by_cases hp : a < labelStar j
    · have hq : ¬ (Fin.rev a < j) := hpv.mp hp
      simp [h0, hp, hq]
    · have hq : Fin.rev a < j := by
        by_contra h
        exact hp (hpv.mpr h)
      simp [h0, hp, hq]

private theorem bDigit_rotEps {m n : ℕ} (hf : 0 < m + 1)
    (ε : Fin (m + 1) → Finset (Fin n)) (j : Fin n) :
    bDigit (rotEps hf ε) j + 2 ^ (m + 1) * (if j ∈ ε (Fin.last m) then 1 else 0) =
      2 * bDigit ε j +
        (if j ∈ (ε (Fin.last m)).image labelStar then 1 else 0) := by
  have h0 : (∑ r : Fin (m + 1), (if j ∈ rotEps hf ε r then 2 ^ (r : ℕ) else 0))
      = (if j ∈ (ε (Fin.last m)).image labelStar then 1 else 0) +
        2 * (∑ s : Fin m, (if j ∈ ε (Fin.castSucc s) then 2 ^ (s : ℕ) else 0)) := by
    rw [Fin.sum_univ_succ]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [rotEps_apply_succ, Fin.val_succ, pow_succ]
    by_cases h : j ∈ ε (Fin.castSucc s) <;> simp [h]; ring
  have h1 : (∑ r : Fin (m + 1), (if j ∈ ε r then 2 ^ (r : ℕ) else 0))
      = (∑ s : Fin m, (if j ∈ ε (Fin.castSucc s) then 2 ^ (s : ℕ) else 0)) +
        (if j ∈ ε (Fin.last m) then 2 ^ m else 0) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
  rw [bDigit, bDigit, h0, h1]
  by_cases hL : j ∈ ε (Fin.last m)
  · simp only [hL, if_true]
    rw [pow_succ]
    ring
  · simp only [hL, if_false]
    ring

private def rotD {m n : ℕ} (ε : Fin (m + 1) → Finset (Fin n)) (a : Fin n) : ℕ :=
  ((ε (Fin.last m)).filter fun j => a < j).card

private def rotG {m n : ℕ} (ε : Fin (m + 1) → Finset (Fin n)) (a : Fin n) : ℕ :=
  (((ε (Fin.last m)).image labelStar).filter fun j => a < j).card

private def rotC {m n : ℕ} (ε : Fin (m + 1) → Finset (Fin n)) : ℕ :=
  ((ε (Fin.last m)).filter fun j => j.val ≠ 0).card

private theorem sum_filter_eq_sum_univ {n : ℕ} {s : Finset (Fin n)} (q : Fin n → Prop)
    [DecidablePred q] :
    (∑ j : Fin n, if q j then (if j ∈ s then 1 else 0) else 0)
      = ∑ j ∈ s, if q j then 1 else 0 := by
  rw [show (∑ j : Fin n, if q j then (if j ∈ s then 1 else 0) else 0)
      = ∑ j : Fin n, if j ∈ s then (if q j then 1 else 0) else 0 from by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j ∈ s <;> by_cases hq : q j <;> simp [hj, hq]]
  rw [Finset.sum_ite_mem]
  simp

private theorem rotG_add_rotD_rev {m n : ℕ} (ε : Fin (m + 1) → Finset (Fin n))
    (a : Fin n) : rotG ε a + rotD ε (Fin.rev a) = rotC ε := by
  have hG : rotG ε a = ∑ j ∈ ε (Fin.last m), if a < labelStar j then 1 else 0 := by
    rw [rotG, Finset.filter_image, Finset.card_image_of_injective _ labelStar_injective,
      Finset.card_filter]
  have hD : rotD ε (Fin.rev a) =
      ∑ j ∈ ε (Fin.last m), if Fin.rev a < j then 1 else 0 := by
    rw [rotD, Finset.card_filter]
  have hC : rotC ε = ∑ j ∈ ε (Fin.last m), if j.val ≠ 0 then 1 else 0 := by
    rw [rotC, Finset.card_filter]
  rw [hG, hD, hC, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h0 : j.val = 0
  · have hp : ¬ (a < labelStar j) := by
      simp only [Fin.lt_def]
      have : (labelStar j : ℕ) = 0 := by
        rw [labelStar_apply, h0, Nat.sub_zero, Nat.mod_self]
      omega
    have hq : ¬ (Fin.rev a < j) := by
      simp only [Fin.lt_def, Fin.val_rev]
      omega
    simp [h0, hp, hq]
  · have hpv : (a < labelStar j) ↔ ¬ (Fin.rev a < j) := by
      simp only [Fin.lt_def, Fin.val_rev]
      have : (labelStar j : ℕ) = n - (j : ℕ) := by
        rw [labelStar_eq_of_ne_zero h0]
      omega
    by_cases hp : a < labelStar j
    · have hq : ¬ (Fin.rev a < j) := hpv.mp hp
      simp [h0, hp, hq]
    · have hq : Fin.rev a < j := by
        by_contra h
        exact hp (hpv.mpr h)
      simp [h0, hp, hq]

private theorem bExp_rotEps {m n : ℕ} (hf : 0 < m + 1)
    (ε : Fin (m + 1) → Finset (Fin n)) (a : Fin n) :
    bExp (rotEps hf ε) a + 2 ^ (m + 1) * rotD ε a = 2 * bExp ε a + rotG ε a := by
  have hL := bExp_eq_sum_bDigit (rotEps hf ε) a
  have hR := bExp_eq_sum_bDigit ε a
  have hD : rotD ε a = ∑ j : Fin n, if a < j then
      (if j ∈ ε (Fin.last m) then 1 else 0) else 0 := by
    rw [rotD, Finset.card_filter]
    exact (sum_filter_eq_sum_univ (fun j : Fin n => a < j)).symm
  have hG : rotG ε a = ∑ j : Fin n, if a < j then
      (if j ∈ (ε (Fin.last m)).image labelStar then 1 else 0) else 0 := by
    rw [rotG, Finset.card_filter]
    exact (sum_filter_eq_sum_univ (fun j : Fin n => a < j)).symm
  rw [hL, hR, hD, hG]
  have hmul : 2 ^ (m + 1) *
      (∑ j : Fin n, if a < j then (if j ∈ ε (Fin.last m) then 1 else 0) else 0)
      = ∑ j : Fin n, if a < j then
          (2 ^ (m + 1) * (if j ∈ ε (Fin.last m) then 1 else 0)) else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : a < j <;> simp [h]
  have h2 : 2 * (∑ j : Fin n, if a < j then bDigit ε j else 0)
      = ∑ j : Fin n, if a < j then 2 * bDigit ε j else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : a < j <;> simp [h]
  rw [hmul, h2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : a < j
  · have := bDigit_rotEps hf ε j
    simp only [h, if_true] at this ⊢
    exact this
  · simp [h]



theorem chiEps_sq (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 0 < f) (φ₀ : F →+* k)
    (ε : Fin f → Finset (Fin n)) {g : SU (unitaryInvolution F 2 f) n}
    (hg : g ∈ diagSubgroup (unitaryInvolution F 2 f) n) :
    chiEps φ₀ ε g ^ 2 = chiEps φ₀ (rotEps hf ε) g := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hf)
  obtain ⟨d, hd⟩ := hg
  have hunit : ∀ a, unitaryInvolution F 2 (m + 1) (d a) * d (Fin.rev a) = 1 :=
    fun a => unitary_of_coe_eq_diagonal hd a
  have hd0 : ∀ a, d a ≠ 0 := fun a => ne_zero_of_unitary hunit a
  have hdet : ∏ a, d a = 1 := by
    have h := g.2.1
    rw [hd, Matrix.det_diagonal] at h
    exact h
  have hmatd : SUExtras.mat (unitaryInvolution F 2 (m + 1)) n g = diagonal d := by
    rw [SUExtras.mat_apply]
    exact hd
  have hmat : ∀ a, SUExtras.mat (unitaryInvolution F 2 (m + 1)) n g a a = d a := by
    intro a
    rw [hmatd]
    simp
  have hExp : ∀ a, bExp (rotEps hf ε) a + 2 ^ (m + 1) * rotD ε a =
      2 * bExp ε a + rotG ε a := fun a => bExp_rotEps hf ε a
  have hB : (∏ a, d a ^ (2 ^ (m + 1) * rotD ε a)) =
      (∏ a, d (Fin.rev a) ^ rotD ε a)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [pow_mul, ← unitaryInvolution_apply, eq_inv_of_mul_eq_one_left (hunit a), inv_pow]
  have hE : (∏ a, d a ^ rotG ε a) = (∏ a, d (Fin.rev a) ^ rotD ε a)⁻¹ := by
    have hP : (∏ a, d a ^ rotD ε (Fin.rev a)) = ∏ a, d (Fin.rev a) ^ rotD ε a := by
      refine Fintype.prod_bijective (fun a => Fin.rev a) Fin.rev_bijective _ _ ?_
      intro a
      simp [Fin.rev_rev]
    have h1 : (∏ a, d a ^ rotG ε a) * (∏ a, d a ^ rotD ε (Fin.rev a)) = 1 := by
      rw [← Finset.prod_mul_distrib]
      have hterm : ∀ a, d a ^ rotG ε a * d a ^ rotD ε (Fin.rev a) = d a ^ rotC ε := by
        intro a
        rw [← pow_add, rotG_add_rotD_rev]
      rw [Finset.prod_congr rfl (fun a _ => hterm a), Finset.prod_pow, hdet, one_pow]
    rw [hP] at h1
    exact eq_inv_of_mul_eq_one_left h1
  have hGD : (∏ a, d a ^ (2 ^ (m + 1) * rotD ε a)) = ∏ a, d a ^ rotG ε a :=
    hB.trans hE.symm
  have hprod : (∏ a, d a ^ bExp (rotEps hf ε) a) * (∏ a, d a ^ (2 ^ (m + 1) * rotD ε a))
      = (∏ a, d a ^ (2 * bExp ε a)) * (∏ a, d a ^ rotG ε a) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← pow_add, ← pow_add, hExp a]
  have hBne : (∏ a, d a ^ (2 ^ (m + 1) * rotD ε a)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro a _
    exact pow_ne_zero _ (hd0 a)
  have hA : (∏ a, d a ^ bExp (rotEps hf ε) a) = ∏ a, d a ^ (2 * bExp ε a) :=
    mul_right_cancel₀ hBne (hprod.trans (by rw [hGD]))
  have hsq : (∏ a, d a ^ bExp ε a) ^ 2 = ∏ a, d a ^ bExp (rotEps hf ε) a := by
    calc (∏ a, d a ^ bExp ε a) ^ 2
        = ∏ a, (d a ^ bExp ε a) ^ 2 := by rw [Finset.prod_pow]
      _ = ∏ a, d a ^ (2 * bExp ε a) := by
          refine Finset.prod_congr rfl fun a _ => ?_
          rw [← pow_mul, Nat.mul_comm]
      _ = ∏ a, d a ^ bExp (rotEps hf ε) a := hA.symm
  simp only [chiEps]
  have hl : (∏ a, SUExtras.mat (unitaryInvolution F 2 (m + 1)) n g a a ^ bExp ε a)
      = ∏ a, d a ^ bExp ε a := by
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [hmat a]
  have hr : (∏ a, SUExtras.mat (unitaryInvolution F 2 (m + 1)) n g a a ^ bExp (rotEps hf ε) a)
      = ∏ a, d a ^ bExp (rotEps hf ε) a := by
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [hmat a]
  rw [hl, hr, ← map_pow]
  exact congrArg φ₀ hsq

theorem chiEps_comp_unitaryInvolution (hF : Nat.card F = (2 ^ f) ^ 2) (φ₀ : F →+* k)
    (ε : Fin f → Finset (Fin n)) {g : SU (unitaryInvolution F 2 f) n}
    (hg : g ∈ diagSubgroup (unitaryInvolution F 2 f) n) :
    chiEps (φ₀.comp (unitaryInvolution F 2 f).toRingHom) ε g =
      chiEps φ₀ (fun r => (ε r).image labelStar) g := by
  rcases Nat.eq_zero_or_pos f with h0 | hpos
  · subst h0
    simp [chiEps, bExp]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
    obtain ⟨d, hd⟩ := hg
    have hunit : ∀ a, unitaryInvolution F 2 (m + 1) (d a) * d (Fin.rev a) = 1 :=
      fun a => unitary_of_coe_eq_diagonal hd a
    have hdet : ∏ a, d a = 1 := by
      have h := g.2.1
      rw [hd, Matrix.det_diagonal] at h
      exact h
    have hmatd : SUExtras.mat (unitaryInvolution F 2 (m + 1)) n g = diagonal d := by
      rw [SUExtras.mat_apply]
      exact hd
    have hmat : ∀ a, SUExtras.mat (unitaryInvolution F 2 (m + 1)) n g a a = d a := by
      intro a
      rw [hmatd]
      simp
    have hAB : (∏ a, d a ^ bExp (fun r => (ε r).image labelStar) a) *
        (∏ a, d a ^ bExp ε (Fin.rev a)) = 1 := by
      rw [← Finset.prod_mul_distrib]
      have hterm : ∀ a, d a ^ bExp (fun r => (ε r).image labelStar) a *
          d a ^ bExp ε (Fin.rev a) = d a ^ expZero ε := by
        intro a
        rw [← pow_add, bExp_image_add]
      rw [Finset.prod_congr rfl (fun a _ => hterm a), Finset.prod_pow, hdet, one_pow]
    have hA : (∏ a, d a ^ bExp (fun r => (ε r).image labelStar) a) =
        (∏ a, d a ^ bExp ε (Fin.rev a))⁻¹ := eq_inv_of_mul_eq_one_left hAB
    have hσ1 : (∏ a, unitaryInvolution F 2 (m + 1) (d a) ^ bExp ε a) =
        (∏ a, d (Fin.rev a) ^ bExp ε a)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [eq_inv_of_mul_eq_one_left (hunit a), inv_pow]
    have hBrev : (∏ a, d (Fin.rev a) ^ bExp ε a) = ∏ a, d a ^ bExp ε (Fin.rev a) := by
      refine Fintype.prod_bijective (fun a => Fin.rev a) Fin.rev_bijective _ _ ?_
      intro a
      simp [Fin.rev_rev]
    have hσ : (∏ a, unitaryInvolution F 2 (m + 1) (d a) ^ bExp ε a) =
        (∏ a, d a ^ bExp ε (Fin.rev a))⁻¹ := hσ1.trans (by rw [hBrev])
    have harg : (∏ a, d a ^ bExp (fun r => (ε r).image labelStar) a) =
        ∏ a, unitaryInvolution F 2 (m + 1) (d a) ^ bExp ε a :=
      hA.trans hσ.symm
    simp only [chiEps]
    have hl : (∏ a, SUExtras.mat (unitaryInvolution F 2 (m + 1)) n g a a ^ bExp ε a)
        = ∏ a, d a ^ bExp ε a := by
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [hmat a]
    have hr : (∏ a, SUExtras.mat (unitaryInvolution F 2 (m + 1)) n g a a ^
        bExp (fun r => (ε r).image labelStar) a)
        = ∏ a, d a ^ bExp (fun r => (ε r).image labelStar) a := by
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [hmat a]
    rw [hl, hr, RingHom.comp_apply]
    congr 1
    rw [map_prod]
    simp only [map_pow]
    exact harg.symm


private theorem eq_of_add_mul_eq {q a b a' b' : ℕ} (hq : 0 < q)
    (ha : a < q) (ha' : a' < q)
    (h : a + q * b = a' + q * b') : a = a' ∧ b = b' := by
  have hb : b = b' := by
    have h1 : (a + q * b) / q = b := by
      rw [Nat.add_comm a (q * b), Nat.mul_add_div (m := q) hq, Nat.div_eq_of_lt ha,
        Nat.add_zero]
    have h2 : (a' + q * b') / q = b' := by
      rw [Nat.add_comm a' (q * b'), Nat.mul_add_div (m := q) hq, Nat.div_eq_of_lt ha',
        Nat.add_zero]
    rw [h] at h1
    rw [h1] at h2
    exact h2
  subst hb
  exact ⟨add_right_cancel h, rfl⟩

private theorem eq_or_full_empty_of_modEq {q a a' : ℕ} (hq : 1 < q)
    (ha : a < q) (ha' : a' < q) (h : a ≡ a' [MOD q - 1]) :
    a = a' ∨ (a = q - 1 ∧ a' = 0) ∨ (a = 0 ∧ a' = q - 1) := by
  have hm : 0 < q - 1 := by omega
  by_cases haa : a = q - 1
  · subst haa
    have h0 : a' % (q - 1) = 0 := by
      simpa [Nat.ModEq, eq_comm] using h
    by_cases hlt : a' < q - 1
    · rw [Nat.mod_eq_of_lt hlt] at h0
      exact Or.inr (Or.inl ⟨rfl, h0⟩)
    · have hle : q - 1 ≤ a' := Nat.le_of_not_lt hlt
      have ha'eq : a' = q - 1 := by omega
      exact Or.inl ha'eq.symm
  · have ham : a < q - 1 := by omega
    have h0 : a' % (q - 1) = a := by
      have := h
      rw [Nat.ModEq, Nat.mod_eq_of_lt ham] at this
      exact this.symm
    by_cases ha'eq : a' = q - 1
    · subst ha'eq
      rw [Nat.mod_self] at h0
      exact Or.inr (Or.inr ⟨by omega, rfl⟩)
    · have ha'm : a' < q - 1 := by omega
      rw [Nat.mod_eq_of_lt ha'm] at h0
      exact Or.inl h0.symm

private theorem pred_add_mul_pred {q : ℕ} (hq : 0 < q) :
    (q - 1) + q * (q - 1) = q * q - 1 := by
  have h1 : q * (q - 1) = q * q - q := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  have h2 : q ≤ q * q := Nat.le_mul_of_pos_left q hq
  rw [h1]
  omega

private theorem eq_top_of_add_mul_eq {q a b : ℕ} (hq : 1 < q)
    (ha : a < q) (_hb : b < q) (h : a + q * b = q * q - 1) :
    a = q - 1 ∧ b = q - 1 := by
  have hqeq := pred_add_mul_pred (by omega : 0 < q)
  have h' : (q - 1) + q * (q - 1) = a + q * b := by rw [h, hqeq]
  have := eq_of_add_mul_eq (by omega : 0 < q) (by omega : q - 1 < q) ha h'
  exact ⟨this.1.symm, this.2.symm⟩

private theorem eq_zero_of_add_mul_eq {q a b : ℕ} (hq : 0 < q)
    (h : a + q * b = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨ha, hb⟩ := Nat.add_eq_zero.mp h
  refine ⟨ha, ?_⟩
  rcases Nat.mul_eq_zero.mp (by rwa [ha, Nat.zero_add] at h) with hq0 | hb0
  · omega
  · exact hb0


private def loIdx {n : ℕ} (s : Fin (n / 2)) : Fin n :=
  ⟨(s : ℕ) + 1, nodeLo_lt s⟩

private def hiIdx {n : ℕ} (s : Fin (n / 2)) : Fin n :=
  ⟨n - 1 - (s : ℕ), nodeHi_lt s⟩

private theorem isFullNode_iff_digits {f n : ℕ} (ε : Fin f → Finset (Fin n))
    (s : Fin (n / 2)) :
    IsFullNode ε s ↔ bDigit ε (loIdx s) = 2 ^ f - 1 ∧ bDigit ε (hiIdx s) = 2 ^ f - 1 := by
  have hlo : (⟨(s : ℕ) + 1, by omega⟩ : Fin n) = loIdx s := Fin.ext rfl
  have hhi : (⟨n - 1 - (s : ℕ), by omega⟩ : Fin n) = hiIdx s := Fin.ext rfl
  constructor
  · intro h
    refine ⟨(bDigit_eq_iff ε _).mpr ?_, (bDigit_eq_iff ε _).mpr ?_⟩
    · intro r
      simpa [hlo] using (h r).1
    · intro r
      simpa [hhi] using (h r).2
  · rintro ⟨h1, h2⟩ r
    exact ⟨by rw [hlo]; exact (bDigit_eq_iff ε _).mp h1 r,
      by rw [hhi]; exact (bDigit_eq_iff ε _).mp h2 r⟩

private theorem not_isFullNode_of_digit_zero {f n : ℕ} (hf : 0 < f)
    {ε : Fin f → Finset (Fin n)} {s : Fin (n / 2)}
    (h : bDigit ε (loIdx s) = 0) : ¬ IsFullNode ε s := by
  intro hfull
  have hb := (isFullNode_iff_digits ε s).mp hfull
  have h2 : 1 < 2 ^ f := Nat.one_lt_pow (Nat.ne_of_gt hf) (by norm_num)
  have : 2 ^ f - 1 = 0 := by rw [← hb.1, h]
  omega

private theorem bDigit_eq_sum_filter {f n : ℕ} (ε : Fin f → Finset (Fin n)) (j : Fin n) :
    bDigit ε j = ∑ r ∈ (Finset.univ.filter fun r : Fin f => j ∈ ε r), 2 ^ (r : ℕ) := by
  rw [bDigit, ← Finset.sum_filter]

private theorem mem_iff_of_bDigit_eq {f n : ℕ} {ε ε' : Fin f → Finset (Fin n)} {j : Fin n}
    (h : bDigit ε j = bDigit ε' j) (r : Fin f) : j ∈ ε r ↔ j ∈ ε' r := by
  let C : Finset ℕ := (Finset.univ.filter fun r : Fin f => j ∈ ε r).image Fin.val
  let C' : Finset ℕ := (Finset.univ.filter fun r : Fin f => j ∈ ε' r).image Fin.val
  have hC : bDigit ε j = ∑ m ∈ C, 2 ^ m := by
    rw [bDigit_eq_sum_filter]
    exact (Finset.sum_image (s := Finset.univ.filter fun r : Fin f => j ∈ ε r)
      (g := Fin.val) (f := fun m => 2 ^ m)
      (by intro a _ b _ hab; exact Fin.ext hab)).symm
  have hC' : bDigit ε' j = ∑ m ∈ C', 2 ^ m := by
    rw [bDigit_eq_sum_filter]
    exact (Finset.sum_image (s := Finset.univ.filter fun r : Fin f => j ∈ ε' r)
      (g := Fin.val) (f := fun m => 2 ^ m)
      (by intro a _ b _ hab; exact Fin.ext hab)).symm
  have hCC : C = C' := digits_eq_of_sum_eq (by rw [← hC, ← hC', h])
  have hmem1 : r.val ∈ C ↔ j ∈ ε r := by
    rw [show C = (Finset.univ.filter fun s : Fin f => j ∈ ε s).image Fin.val from rfl,
      Finset.mem_image]
    constructor
    · rintro ⟨s, hs, hsv⟩
      have hsr : s = r := Fin.ext hsv
      simpa [hsr] using (Finset.mem_filter.mp hs).2
    · intro hjr
      exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjr⟩, rfl⟩
  have hmem2 : r.val ∈ C' ↔ j ∈ ε' r := by
    rw [show C' = (Finset.univ.filter fun s : Fin f => j ∈ ε' s).image Fin.val from rfl,
      Finset.mem_image]
    constructor
    · rintro ⟨s, hs, hsv⟩
      have hsr : s = r := Fin.ext hsv
      simpa [hsr] using (Finset.mem_filter.mp hs).2
    · intro hjr
      exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjr⟩, rfl⟩
  exact hmem1.symm.trans ((by rw [hCC] : r.val ∈ C ↔ r.val ∈ C').trans hmem2)


theorem eq_of_chiEps_eq (hF : Nat.card F = (2 ^ f) ^ 2) (hn : 0 < n) (φ₀ : F →+* k)
    {ε ε' : Fin f → Finset (Fin n)}
    (h0 : ∀ r, (⟨0, hn⟩ : Fin n) ∉ ε r) (h0' : ∀ r, (⟨0, hn⟩ : Fin n) ∉ ε' r)
    (hχ : ∀ h ∈ ⨆ s, levelTorus (unitaryInvolution F 2 f) s, chiEps φ₀ ε h = chiEps φ₀ ε' h)
    (hfull : ∀ s, IsFullNode ε s ↔ IsFullNode ε' s) : ε = ε' := by
  classical
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · exfalso
      rw [h, pow_zero, one_pow] at hF
      have := Finite.one_lt_card (α := F)
      omega
    · exact h
  let q : ℕ := 2 ^ f
  have hq : 1 < q := by
    dsimp [q]
    exact Nat.one_lt_pow (Nat.ne_of_gt hf) (by norm_num)
  have hq0 : 0 < q := by omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hgo : orderOf g = q * q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hF, pow_two]
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (fixedSubfield F 2 f)ˣ)
  have huo : orderOf u = q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_units, card_fixedSubfield hF]
  let cfix : F := ((u : (fixedSubfield F 2 f)ˣ) : fixedSubfield F 2 f)
  have hcfix : cfix ≠ 0 := by
    intro h
    exact u.ne_zero (Subtype.ext h)
  have hσcfix : unitaryInvolution F 2 f cfix = cfix :=
    mem_fixedSubfield.mp (u : fixedSubfield F 2 f).2
  have hnode : ∀ s : Fin (n / 2),
      bDigit ε (loIdx s) = bDigit ε' (loIdx s) ∧
      bDigit ε (hiIdx s) = bDigit ε' (hiIdx s) := by
    intro s
    by_cases heven : ¬ s.val + 1 < n / 2 ∧ Even n
    ·
      obtain ⟨hlt, hneven⟩ := heven
      have hPeq : 2 * (s : ℕ) + 2 = n := by obtain ⟨k, hk⟩ := hneven; omega
      have hlohi : loIdx s = hiIdx s := by
        ext
        simp [loIdx, hiIdx]
        omega
      let e : ℕ := bDigit ε (loIdx s)
      let e' : ℕ := bDigit ε' (loIdx s)
      have hloeq : (⟨(s : ℕ) + 1, by omega⟩ : Fin n) = loIdx s := Fin.ext rfl
      have he_lt : e < q := by simpa [e, q] using bDigit_lt ε (loIdx s)
      have he'_lt : e' < q := by simpa [e', q] using bDigit_lt ε' (loIdx s)
      obtain ⟨x, hxH, hxmat⟩ := exists_mem_levelTorus_tFun_even hF s hlt hneven hcfix hσcfix
      have hχx := hχ x (Subgroup.mem_iSup_of_mem s hxH)
      have h1 : chiEps φ₀ ε x = φ₀ cfix ^ e := by
        rw [chiEps_of_tFun φ₀ ε s hcfix hxmat, if_pos hPeq, mul_one, hloeq]
      have h2 : chiEps φ₀ ε' x = φ₀ cfix ^ e' := by
        rw [chiEps_of_tFun φ₀ ε' s hcfix hxmat, if_pos hPeq, mul_one, hloeq]
      rw [h1, h2] at hχx
      have hφ : φ₀ (cfix ^ e) = φ₀ (cfix ^ e') := by simpa [map_pow] using hχx
      have hpow : cfix ^ e = cfix ^ e' := RingHom.injective φ₀ hφ
      have hu_pow : u ^ e = u ^ e' := by
        apply Units.ext
        apply Subtype.ext
        simpa [cfix, Units.val_pow_eq_pow_val] using hpow
      have hmodu : e ≡ e' [MOD q - 1] := by
        have := (pow_eq_pow_iff_modEq (x := u) (n := e) (m := e')).mp hu_pow
        rwa [huo] at this
      have hcases := eq_or_full_empty_of_modEq hq he_lt he'_lt hmodu
      rcases hcases with hEq | ⟨hTop, hZero⟩ | ⟨hZero, hTop⟩
      · refine ⟨hEq, ?_⟩
        rw [← hlohi]
        exact hEq
      · exfalso
        have hfullε : IsFullNode ε s := by
          rw [isFullNode_iff_digits]
          exact ⟨hTop, by rw [← hlohi]; exact hTop⟩
        have hnotε' : ¬ IsFullNode ε' s :=
          not_isFullNode_of_digit_zero hf (by simpa [e'] using hZero)
        exact hnotε' ((hfull s).mp hfullε)
      · exfalso
        have hfullε' : IsFullNode ε' s := by
          rw [isFullNode_iff_digits]
          exact ⟨hTop, by rw [← hlohi]; exact hTop⟩
        have hnotε : ¬ IsFullNode ε s :=
          not_isFullNode_of_digit_zero hf (by simpa [e] using hZero)
        exact hnotε ((hfull s).mpr hfullε')
    ·
      have hnotEven : ¬ 2 * (s : ℕ) + 2 = n := by
        intro h
        apply heven
        refine ⟨by omega, ?_⟩
        exact ⟨s + 1, by omega⟩
      let a : ℕ := bDigit ε (loIdx s)
      let b : ℕ := bDigit ε (hiIdx s)
      let a' : ℕ := bDigit ε' (loIdx s)
      let b' : ℕ := bDigit ε' (hiIdx s)
      have ha : a < q := by simpa [a, q] using bDigit_lt ε (loIdx s)
      have hb : b < q := by simpa [b, q] using bDigit_lt ε (hiIdx s)
      have ha' : a' < q := by simpa [a', q] using bDigit_lt ε' (loIdx s)
      have hb' : b' < q := by simpa [b', q] using bDigit_lt ε' (hiIdx s)
      let e : ℕ := a + q * b
      let e' : ℕ := a' + q * b'
      have hloeq : (⟨(s : ℕ) + 1, by omega⟩ : Fin n) = loIdx s := Fin.ext rfl
      have hhieq : (⟨n - 1 - (s : ℕ), by omega⟩ : Fin n) = hiIdx s := Fin.ext rfl
      let cgen : F := (g : F)
      have hcgen : cgen ≠ 0 := g.ne_zero
      obtain ⟨x, hxH, hxmat⟩ := exists_mem_levelTorus_tFun hF s hcgen heven
      have hχx := hχ x (Subgroup.mem_iSup_of_mem s hxH)
      have hσgen : φ₀ (unitaryInvolution F 2 f cgen) = φ₀ cgen ^ q := by
        rw [unitaryInvolution_apply, map_pow]
      have h1 : chiEps φ₀ ε x = φ₀ cgen ^ e := by
        rw [chiEps_of_tFun φ₀ ε s hcgen hxmat, if_neg hnotEven, hloeq, hhieq, hσgen,
          ← pow_mul, ← pow_add]
      have h2 : chiEps φ₀ ε' x = φ₀ cgen ^ e' := by
        rw [chiEps_of_tFun φ₀ ε' s hcgen hxmat, if_neg hnotEven, hloeq, hhieq, hσgen,
          ← pow_mul, ← pow_add]
      rw [h1, h2] at hχx
      have hφ : φ₀ (cgen ^ e) = φ₀ (cgen ^ e') := by simpa [map_pow] using hχx
      have hpow : cgen ^ e = cgen ^ e' := RingHom.injective φ₀ hφ
      have hg_pow : g ^ e = g ^ e' := by
        apply Units.ext
        simpa [cgen, Units.val_pow_eq_pow_val] using hpow
      have hmodg : e ≡ e' [MOD q * q - 1] := by
        have := (pow_eq_pow_iff_modEq (x := g) (n := e) (m := e')).mp hg_pow
        rwa [hgo] at this
      have he_lt : e < q * q := by
        have hb1 : b + 1 ≤ q := by omega
        have h1 : a + q * b < q + q * b := Nat.add_lt_add_right ha (q * b)
        have h2 : q + q * b = q * (b + 1) := by ring
        have h3 : q * (b + 1) ≤ q * q := Nat.mul_le_mul_left q hb1
        calc a + q * b < q + q * b := h1
          _ = q * (b + 1) := h2
          _ ≤ q * q := h3
      have he'_lt : e' < q * q := by
        have hb1 : b' + 1 ≤ q := by omega
        have h1 : a' + q * b' < q + q * b' := Nat.add_lt_add_right ha' (q * b')
        have h2 : q + q * b' = q * (b' + 1) := by ring
        have h3 : q * (b' + 1) ≤ q * q := Nat.mul_le_mul_left q hb1
        calc a' + q * b' < q + q * b' := h1
          _ = q * (b' + 1) := h2
          _ ≤ q * q := h3
      have hqq : 1 < q * q := by nlinarith
      have hcases := eq_or_full_empty_of_modEq hqq he_lt he'_lt hmodg
      rcases hcases with hEq | ⟨hTop, hZero⟩ | ⟨hZero, hTop⟩
      · have hab := eq_of_add_mul_eq hq0 ha ha' (by simpa [e, e'] using hEq)
        exact ⟨by simpa [a, a'] using hab.1, by simpa [b, b'] using hab.2⟩
      · exfalso
        have hz := eq_zero_of_add_mul_eq hq0 (by simpa [e'] using hZero)
        have ht := eq_top_of_add_mul_eq hq ha hb (by simpa [e] using hTop)
        have hfullε : IsFullNode ε s := by
          rw [isFullNode_iff_digits]
          exact ⟨by simpa [a] using ht.1, by simpa [b] using ht.2⟩
        have hnotε' : ¬ IsFullNode ε' s :=
          not_isFullNode_of_digit_zero hf (by simpa [a'] using hz.1)
        exact hnotε' ((hfull s).mp hfullε)
      · exfalso
        have hz := eq_zero_of_add_mul_eq hq0 (by simpa [e] using hZero)
        have ht := eq_top_of_add_mul_eq hq ha' hb' (by simpa [e'] using hTop)
        have hfullε' : IsFullNode ε' s := by
          rw [isFullNode_iff_digits]
          exact ⟨by simpa [a'] using ht.1, by simpa [b'] using ht.2⟩
        have hnotε : ¬ IsFullNode ε s :=
          not_isFullNode_of_digit_zero hf (by simpa [a] using hz.1)
        exact hnotε ((hfull s).mpr hfullε')
  have hdigit : ∀ j : Fin n, (j : ℕ) ≠ 0 → bDigit ε j = bDigit ε' j := by
    intro j hj
    by_cases hle : (j : ℕ) ≤ n / 2
    · let s : Fin (n / 2) := ⟨j.val - 1, by omega⟩
      have hlo : loIdx s = j := by
        ext
        simp [loIdx, s]
        omega
      rw [← hlo]
      exact (hnode s).1
    · let s : Fin (n / 2) := ⟨n - 1 - j.val, by omega⟩
      have hhi : hiIdx s = j := by
        ext
        simp [hiIdx, s]
        omega
      rw [← hhi]
      exact (hnode s).2
  funext r
  ext j
  by_cases hj : (j : ℕ) = 0
  · have hjeq : j = (⟨0, hn⟩ : Fin n) := Fin.ext (by simpa using hj)
    rw [hjeq]
    simp [h0 r, h0' r]
  · exact mem_iff_of_bDigit_eq (hdigit j hj) r


private def mkWord {f n : ℕ} (hf : 0 < f) (ε : Fin f → Finset (Fin n))
    (i : ZMod (2 * f)) : Finset (Fin n) :=
  letI : NeZero (2 * f) := ⟨by omega⟩
  if h : i.val < f then ε ⟨i.val, h⟩
  else (ε ⟨i.val - f, by have := ZMod.val_lt i; omega⟩).image labelStar

private theorem mkWord_apply_lt {f n : ℕ} (hf : 0 < f) (ε : Fin f → Finset (Fin n))
    {i : ZMod (2 * f)} (h : i.val < f) :
    mkWord hf ε i = ε ⟨i.val, h⟩ := by
  dsimp [mkWord]
  rw [dif_pos h]

private theorem rotEps_eq_zero {f n : ℕ} (hf : 0 < f) (ε : Fin f → Finset (Fin n))
    (r : Fin f) (hr : (r : ℕ) = 0) :
    rotEps hf ε r = (ε ⟨f - 1, by omega⟩).image labelStar := by
  rw [rotEps, dif_pos hr]

private theorem rotEps_ne_zero {f n : ℕ} (hf : 0 < f) (ε : Fin f → Finset (Fin n))
    (r : Fin f) (hr : (r : ℕ) ≠ 0) :
    rotEps hf ε r = ε ⟨(r : ℕ) - 1, by have := r.isLt; omega⟩ := by
  rw [rotEps, dif_neg hr]

private theorem mkWord_apply_ge {f n : ℕ} (hf : 0 < f) (ε : Fin f → Finset (Fin n))
    {i : ZMod (2 * f)} (h : ¬ i.val < f) :
    mkWord hf ε i =
      (ε ⟨i.val - f, by
        have : NeZero (2 * f) := ⟨by omega⟩
        have := ZMod.val_lt i
        omega⟩).image labelStar := by
  dsimp [mkWord]
  rw [dif_neg h]

private theorem mkWord_rotEps {f n : ℕ} (hf : 0 < f) (ε : Fin f → Finset (Fin n))
    (i : ZMod (2 * f)) :
    mkWord hf (rotEps hf ε) i = mkWord hf ε (i - 1) := by
  have : NeZero (2 * f) := ⟨by omega⟩
  have : Fact (1 < 2 * f) := ⟨by omega⟩
  have hval_one : (1 : ZMod (2 * f)).val = 1 := ZMod.val_one _
  have hzero : (0 : ZMod (2 * f)).val = 0 := ZMod.val_zero
  have hneg : ((0 : ZMod (2 * f)) - 1).val = 2 * f - 1 := by
    rw [zero_sub]
    have : NeZero (1 : ZMod (2 * f)) :=
      ⟨by intro h; rw [ZMod.one_eq_zero_iff] at h; omega⟩
    rw [ZMod.val_neg_of_ne_zero (1 : ZMod (2 * f))]
    simp [hval_one]
  have hival : i.val < 2 * f := ZMod.val_lt i
  have hsub_pos : ∀ {i : ZMod (2 * f)}, 0 < i.val → (i - 1).val = i.val - 1 := by
    intro i hi
    rw [ZMod.val_sub]
    · rw [hval_one]
    · rw [hval_one]
      omega
  by_cases hi : i.val < f
  · by_cases h0 : i.val = 0
    · have hi0 : i = 0 := (ZMod.val_eq_zero i).mp h0
      subst hi0
      have hlt0 : (0 : ZMod (2 * f)).val < f := by rw [hzero]; exact hf
      rw [mkWord_apply_lt hf (rotEps hf ε) hlt0]
      have hge : ¬ ((0 : ZMod (2 * f)) - 1).val < f := by rw [hneg]; omega
      rw [mkWord_apply_ge hf ε hge]
      have hidx0 : (⟨(0 : ZMod (2 * f)).val, hlt0⟩ : Fin f) = ⟨0, by omega⟩ := by
        ext
        exact hzero
      rw [hidx0, rotEps_eq_zero hf ε ⟨0, by omega⟩ rfl]
      have hidx1 : (⟨((0 : ZMod (2 * f)) - 1).val - f,
          by have := ZMod.val_lt ((0 : ZMod (2 * f)) - 1); omega⟩ : Fin f) =
          ⟨f - 1, by omega⟩ := by
        ext
        change ((0 : ZMod (2 * f)) - 1).val - f = f - 1
        omega
      rw [hidx1]
    · have hpos : 0 < i.val := Nat.pos_of_ne_zero h0
      have hsub : (i - 1).val = i.val - 1 := hsub_pos hpos
      have hlt : (i - 1).val < f := by rw [hsub]; omega
      rw [mkWord_apply_lt hf (rotEps hf ε) hi, mkWord_apply_lt hf ε hlt]
      rw [rotEps_ne_zero hf ε ⟨i.val, hi⟩ h0]
      congr 1
      ext
      exact hsub.symm
  · have hgei : f ≤ i.val := by omega
    by_cases h0 : i.val = f
    · have hif : i = (f : ZMod (2 * f)) := by
        apply ZMod.val_injective (2 * f)
        rw [ZMod.val_natCast_of_lt (by omega : f < 2 * f)]
        exact h0
      subst hif
      have hval : ((f : ZMod (2 * f)) - 1).val = f - 1 := by
        rw [ZMod.val_sub]
        · rw [ZMod.val_natCast_of_lt (by omega : f < 2 * f), hval_one]
        · rw [ZMod.val_natCast_of_lt (by omega : f < 2 * f), hval_one]
          omega
      have hlt : ((f : ZMod (2 * f)) - 1).val < f := by rw [hval]; omega
      rw [mkWord_apply_ge hf (rotEps hf ε) hi, mkWord_apply_lt hf ε hlt]
      have hidx0 : (⟨(f : ZMod (2 * f)).val - f,
          by have := ZMod.val_lt ((f : ZMod (2 * f)) - 1); omega⟩ : Fin f) =
          ⟨0, by omega⟩ := by
        ext
        have hfv : (f : ZMod (2 * f)).val = f :=
          ZMod.val_natCast_of_lt (by omega : f < 2 * f)
        change (f : ZMod (2 * f)).val - f = 0
        omega
      rw [hidx0, rotEps_eq_zero hf ε ⟨0, by omega⟩ rfl, image_labelStar_image]
      congr 1
      ext
      exact hval.symm
    · have hltfi : f < i.val := by omega
      have hpos : 0 < i.val := by omega
      have hsub : (i - 1).val = i.val - 1 := hsub_pos hpos
      have hge' : ¬ (i - 1).val < f := by rw [hsub]; omega
      rw [mkWord_apply_ge hf (rotEps hf ε) hi, mkWord_apply_ge hf ε hge']
      rw [rotEps_ne_zero hf ε ⟨i.val - f, by omega⟩ (by
        intro h
        have : i.val - f = 0 := h
        omega)]
      have hidx : (⟨i.val - f - 1, by omega⟩ : Fin f) =
          ⟨(i - 1).val - f, by omega⟩ := by
        ext
        change i.val - f - 1 = (i - 1).val - f
        omega
      rw [hidx]


private theorem mkWord_iterate {f n : ℕ} (hf : 0 < f) (ε : Fin f → Finset (Fin n))
    (k : ℕ) :
    mkWord hf ((rotEps hf)^[k] ε) = fun i : ZMod (2 * f) => mkWord hf ε (i - k) := by
  induction k with
  | zero =>
      funext i
      simp
  | succ k ih =>
      funext i
      rw [Function.iterate_succ_apply', mkWord_rotEps, ih]
      push_cast
      ring_nf

private theorem mkWord_period {f n : ℕ} (hf : 0 < f) (ε : Fin f → Finset (Fin n))
    {s : ℕ} (hrot : (rotEps hf)^[s] ε = ε) :
    ∀ i : ZMod (2 * f), mkWord hf ε (i + (s : ZMod (2 * f))) = mkWord hf ε i := by
  intro i
  have hiter := congrFun (mkWord_iterate hf ε s) (i + (s : ZMod (2 * f)))
  rw [hrot] at hiter
  simpa [add_sub_cancel_right] using hiter


private theorem mkWord_star {f n : ℕ} (hf : 0 < f) (ε : Fin f → Finset (Fin n))
    (i : ZMod (2 * f)) :
    mkWord hf ε (i + (f : ZMod (2 * f))) = (mkWord hf ε i).image labelStar := by
  have : NeZero (2 * f) := ⟨by omega⟩
  have hfi : (f : ZMod (2 * f)).val = f := ZMod.val_natCast_of_lt (by omega)
  have hval1 : ∀ i : ZMod (2 * f), i.val < f →
      (i + (f : ZMod (2 * f))).val = i.val + f := by
    intro i hi
    rw [ZMod.val_add_of_lt]
    · rw [hfi]
    · rw [hfi]
      omega
  have hval2 : ∀ i : ZMod (2 * f), ¬ i.val < f →
      (i + (f : ZMod (2 * f))).val = i.val - f := by
    intro i hi
    rw [ZMod.val_add_of_le]
    · rw [hfi]
      omega
    · rw [hfi]
      omega
  by_cases hi : i.val < f
  · have hsum : (i + (f : ZMod (2 * f))).val = i.val + f := hval1 i hi
    have hge : ¬ (i + (f : ZMod (2 * f))).val < f := by rw [hsum]; omega
    rw [mkWord_apply_ge hf ε hge, mkWord_apply_lt hf ε hi]
    apply congrArg (fun t => (ε t).image labelStar)
    ext
    change (i + (f : ZMod (2 * f))).val - f = i.val
    omega
  · have hsum : (i + (f : ZMod (2 * f))).val = i.val - f := hval2 i hi
    have hlt : (i + (f : ZMod (2 * f))).val < f := by
      rw [hsum]
      have := ZMod.val_lt i
      omega
    rw [mkWord_apply_lt hf ε hlt, mkWord_apply_ge hf ε hi, image_labelStar_image]
    apply congrArg ε
    ext
    change (i + (f : ZMod (2 * f))).val = i.val - f
    omega


theorem le_mul_card_of_chiEps_pow (hF : Nat.card F = (2 ^ f) ^ 2) (hn : 0 < n) (φ₀ : F →+* k)
    {ε : Fin f → Finset (Fin n)} (h0 : ∀ r, (⟨0, hn⟩ : Fin n) ∉ ε r) (ht : ∃ r, ε r ≠ ∅)
    {s : ℕ} (hs : 0 < s)
    (hχ : ∀ h ∈ ⨆ i, levelTorus (unitaryInvolution F 2 f) i,
      chiEps φ₀ ε h ^ 2 ^ s = chiEps φ₀ ε h) :
    f ≤ s * (Finset.univ.filter fun r => ε r ≠ ∅).card := by
  classical
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · exfalso
      rw [h, pow_zero, one_pow] at hF
      have := Finite.one_lt_card (α := F)
      omega
    · exact h
  let H : Subgroup (SU (unitaryInvolution F 2 f) n) :=
    ⨆ i, levelTorus (unitaryInvolution F 2 f) i
  have hHdiag : H ≤ diagSubgroup (unitaryInvolution F 2 f) n := by
    dsimp [H]
    exact iSup_le fun i => levelTorus_le_diagSubgroup i
  have hiter : ∀ (k : ℕ) (h : SU (unitaryInvolution F 2 f) n), h ∈ H →
      chiEps φ₀ ((rotEps hf)^[k] ε) h = chiEps φ₀ ε h ^ (2 ^ k) := by
    intro k
    induction k with
    | zero =>
        intro h hh
        simp
    | succ k ih =>
        intro h hh
        rw [Function.iterate_succ_apply']
        rw [← chiEps_sq hF hf φ₀ ((rotEps hf)^[k] ε) (hHdiag hh)]
        rw [ih h hh]
        rw [← pow_mul]
        congr 1
  have h0_rot : ∀ (k : ℕ) (r : Fin f),
      (⟨0, hn⟩ : Fin n) ∉ ((rotEps hf)^[k] ε) r := by
    intro k
    induction k with
    | zero =>
        intro r
        simpa using h0 r
    | succ k ih =>
        intro r
        rw [Function.iterate_succ_apply']
        by_cases hr : (r : ℕ) = 0
        · rw [rotEps_eq_zero hf _ r hr, mem_image_labelStar_iff]
          have hz : labelStar (⟨0, hn⟩ : Fin n) = ⟨0, hn⟩ := by
            ext
            simp [labelStar]
          rw [hz]
          exact ih _
        · rw [rotEps_ne_zero hf _ r hr]
          exact ih _
  have hfull_rot : ∀ (k : ℕ) (r : Fin (n / 2)),
      IsFullNode ((rotEps hf)^[k] ε) r ↔ IsFullNode ε r := by
    intro k
    induction k with
    | zero =>
        intro r
        simp
    | succ k ih =>
        intro r
        rw [Function.iterate_succ_apply', isFullNode_rotEps_iff hf ((rotEps hf)^[k] ε) r, ih r]
  have hrot : (rotEps hf)^[s] ε = ε := by
    symm
    apply eq_of_chiEps_eq hF hn φ₀ h0 (h0_rot s)
    · intro h hh
      rw [hiter s h hh]
      exact (hχ h hh).symm
    · intro r
      exact (hfull_rot s r).symm
  let w : ZMod (2 * f) → Finset (Fin n) := mkWord hf ε
  have hw : ∀ i, w (i + (f : ZMod (2 * f))) = (w i).image labelStar := by
    intro i
    exact mkWord_star hf ε i
  have hper : ∀ i, w (i + (s : ZMod (2 * f))) = w i := by
    intro i
    exact mkWord_period hf ε hrot i
  let P : ℕ → Prop := fun p => 0 < p ∧ ∀ i, w (i + (p : ZMod (2 * f))) = w i
  have hPs : P s := ⟨hs, hper⟩
  have hPex : ∃ p, P p := ⟨s, hPs⟩
  let p : ℕ := Nat.find hPex
  have hpP : P p := Nat.find_spec hPex
  have hps : p ≤ s := Nat.find_le hPs
  have hpmin : ∀ q, q < p → ¬ P q := fun q hq => Nat.find_min hPex hq
  have hmin' : ∀ q, 0 < q → q < p → ∃ i, w (i + (q : ZMod (2 * f))) ≠ w i := by
    intro q hq hlt
    by_contra h
    push Not at h
    exact hpmin q hlt ⟨hq, h⟩
  let t : ℕ := Nat.card {r : Fin f // ε r ≠ ∅}
  have hfirst : Nat.card {i : ZMod (2 * f) // i.val < f ∧ w i ≠ ∅} = t := by
    have : NeZero (2 * f) := ⟨by omega⟩
    dsimp [t]
    let e0 : {i : ZMod (2 * f) // i.val < f} ≃ Fin f :=
      { toFun := fun i => ⟨i.1.val, i.2⟩
        invFun := fun r => ⟨(r.val : ZMod (2 * f)), by
          rw [ZMod.val_natCast_of_lt]
          · exact r.isLt
          · omega⟩
        left_inv := by
          intro i
          apply Subtype.ext
          exact ZMod.natCast_zmod_val i.1
        right_inv := by
          intro r
          apply Fin.ext
          simp [ZMod.val_natCast_of_lt (by omega : r.val < 2 * f)] }
    have hpred : ∀ i : {i : ZMod (2 * f) // i.val < f},
        (w i.1 ≠ ∅) ↔ (ε (e0 i) ≠ ∅) := by
      intro i
      have hwval : w i.1 = ε (e0 i) := by
        dsimp [w, e0]
        rw [mkWord_apply_lt hf ε i.2]
      rw [hwval]
    exact Nat.card_congr
      ((Equiv.subtypeSubtypeEquivSubtypeInter (fun i : ZMod (2 * f) => i.val < f)
        (fun i => w i ≠ ∅)).symm.trans (Equiv.subtypeEquiv e0 hpred))
  have hcardT : Nat.card {i : ZMod (2 * f) // w i ≠ ∅} = 2 * t := by
    rw [card_ne_eq_two_mul (fun s : Finset (Fin n) => s.image labelStar)
      (∅ : Finset (Fin n)) w hf hw (fun s => image_labelStar_image s) (by simp)]
    rw [hfirst]
  have htpos : 0 < t := by
    dsimp [t]
    obtain ⟨r, hr⟩ := ht
    exact Nat.card_pos_iff.mpr ⟨⟨⟨r, hr⟩⟩, inferInstance⟩
  have hTpos : 0 < Nat.card {i : ZMod (2 * f) // w i ≠ ∅} := by
    rw [hcardT]
    exact Nat.mul_pos (by norm_num) htpos
  have hbound := two_mul_le_mul_card_ne (fun s : Finset (Fin n) => s.image labelStar)
    (∅ : Finset (Fin n)) w hf hpP.1 hpP.2 hmin' hTpos
  rw [hcardT] at hbound
  have hbound' : 2 * f ≤ s * (2 * t) := by
    calc 2 * f ≤ p * (2 * t) := hbound
      _ ≤ s * (2 * t) := Nat.mul_le_mul_right _ hps
  have hfin : 2 * f ≤ 2 * (s * t) := by
    calc 2 * f ≤ s * (2 * t) := hbound'
      _ = 2 * (s * t) := by ring
  have hft : f ≤ s * t := Nat.le_of_mul_le_mul_left hfin (by norm_num)
  have htcard : (Finset.univ.filter fun r : Fin f => ε r ≠ ∅).card = t := by
    dsimp [t]
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [htcard]
  exact hft


theorem two_mul_le_of_chiEps_pow (hF : Nat.card F = (2 ^ f) ^ 2) (hn : 0 < n) (φ₀ : F →+* k)
    {ε : Fin f → Finset (Fin n)} (h0 : ∀ r, (⟨0, hn⟩ : Fin n) ∉ ε r) {s : ℕ} (hs : 0 < s)
    (hχ : ∀ h ∈ ⨆ i, levelTorus (unitaryInvolution F 2 f) i,
      chiEps φ₀ ε h ^ 2 ^ s = chiEps φ₀ ε h)
    (ht : (Finset.univ.filter fun r => ε r ≠ ∅).card ≤ 2)
    (hns : ∃ r, (ε r).image labelStar ≠ ε r) :
    2 * f ≤ s := by
  classical
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · exfalso
      rw [h, pow_zero, one_pow] at hF
      have := Finite.one_lt_card (α := F)
      omega
    · exact h
  have hne : ∃ r, ε r ≠ ∅ := by
    obtain ⟨r, hr⟩ := hns
    refine ⟨r, ?_⟩
    intro hempty
    exact hr (by rw [hempty, Finset.image_empty])
  let H : Subgroup (SU (unitaryInvolution F 2 f) n) :=
    ⨆ i, levelTorus (unitaryInvolution F 2 f) i
  have hHdiag : H ≤ diagSubgroup (unitaryInvolution F 2 f) n := by
    dsimp [H]
    exact iSup_le fun i => levelTorus_le_diagSubgroup i
  have hiter : ∀ (k : ℕ) (h : SU (unitaryInvolution F 2 f) n), h ∈ H →
      chiEps φ₀ ((rotEps hf)^[k] ε) h = chiEps φ₀ ε h ^ (2 ^ k) := by
    intro k
    induction k with
    | zero =>
        intro h hh
        simp
    | succ k ih =>
        intro h hh
        rw [Function.iterate_succ_apply']
        rw [← chiEps_sq hF hf φ₀ ((rotEps hf)^[k] ε) (hHdiag hh)]
        rw [ih h hh]
        rw [← pow_mul]
        congr 1
  have h0_rot : ∀ (k : ℕ) (r : Fin f),
      (⟨0, hn⟩ : Fin n) ∉ ((rotEps hf)^[k] ε) r := by
    intro k
    induction k with
    | zero =>
        intro r
        simpa using h0 r
    | succ k ih =>
        intro r
        rw [Function.iterate_succ_apply']
        by_cases hr : (r : ℕ) = 0
        · rw [rotEps_eq_zero hf _ r hr, mem_image_labelStar_iff]
          have hz : labelStar (⟨0, hn⟩ : Fin n) = ⟨0, hn⟩ := by
            ext
            simp [labelStar]
          rw [hz]
          exact ih _
        · rw [rotEps_ne_zero hf _ r hr]
          exact ih _
  have hfull_rot : ∀ (k : ℕ) (r : Fin (n / 2)),
      IsFullNode ((rotEps hf)^[k] ε) r ↔ IsFullNode ε r := by
    intro k
    induction k with
    | zero =>
        intro r
        simp
    | succ k ih =>
        intro r
        rw [Function.iterate_succ_apply', isFullNode_rotEps_iff hf ((rotEps hf)^[k] ε) r, ih r]
  have hrot : (rotEps hf)^[s] ε = ε := by
    symm
    apply eq_of_chiEps_eq hF hn φ₀ h0 (h0_rot s)
    · intro h hh
      rw [hiter s h hh]
      exact (hχ h hh).symm
    · intro r
      exact (hfull_rot s r).symm
  let w : ZMod (2 * f) → Finset (Fin n) := mkWord hf ε
  have hw : ∀ i, w (i + (f : ZMod (2 * f))) = (w i).image labelStar := by
    intro i
    exact mkWord_star hf ε i
  have hper : ∀ i, w (i + (s : ZMod (2 * f))) = w i := by
    intro i
    exact mkWord_period hf ε hrot i
  let P : ℕ → Prop := fun p => 0 < p ∧ ∀ i, w (i + (p : ZMod (2 * f))) = w i
  have hPs : P s := ⟨hs, hper⟩
  have hPex : ∃ p, P p := ⟨s, hPs⟩
  let p : ℕ := Nat.find hPex
  have hpP : P p := Nat.find_spec hPex
  have hps : p ≤ s := Nat.find_le hPs
  have hpmin : ∀ q, q < p → ¬ P q := fun q hq => Nat.find_min hPex hq
  have hmin' : ∀ q, 0 < q → q < p → ∃ i, w (i + (q : ZMod (2 * f))) ≠ w i := by
    intro q hq hlt
    by_contra h
    push Not at h
    exact hpmin q hlt ⟨hq, h⟩
  let t : ℕ := Nat.card {r : Fin f // ε r ≠ ∅}
  have hfirst : Nat.card {i : ZMod (2 * f) // i.val < f ∧ w i ≠ ∅} = t := by
    have : NeZero (2 * f) := ⟨by omega⟩
    dsimp [t]
    let e0 : {i : ZMod (2 * f) // i.val < f} ≃ Fin f :=
      { toFun := fun i => ⟨i.1.val, i.2⟩
        invFun := fun r => ⟨(r.val : ZMod (2 * f)), by
          rw [ZMod.val_natCast_of_lt]
          · exact r.isLt
          · omega⟩
        left_inv := by
          intro i
          apply Subtype.ext
          exact ZMod.natCast_zmod_val i.1
        right_inv := by
          intro r
          apply Fin.ext
          simp [ZMod.val_natCast_of_lt (by omega : r.val < 2 * f)] }
    have hpred : ∀ i : {i : ZMod (2 * f) // i.val < f},
        (w i.1 ≠ ∅) ↔ (ε (e0 i) ≠ ∅) := by
      intro i
      have hwval : w i.1 = ε (e0 i) := by
        dsimp [w, e0]
        rw [mkWord_apply_lt hf ε i.2]
      rw [hwval]
    exact Nat.card_congr
      ((Equiv.subtypeSubtypeEquivSubtypeInter (fun i : ZMod (2 * f) => i.val < f)
        (fun i => w i ≠ ∅)).symm.trans (Equiv.subtypeEquiv e0 hpred))
  have hcardT : Nat.card {i : ZMod (2 * f) // w i ≠ ∅} = 2 * t := by
    rw [card_ne_eq_two_mul (fun s : Finset (Fin n) => s.image labelStar)
      (∅ : Finset (Fin n)) w hf hw (fun s => image_labelStar_image s) (by simp)]
    rw [hfirst]
  have htpos : 0 < t := by
    dsimp [t]
    obtain ⟨r, hr⟩ := hne
    exact Nat.card_pos_iff.mpr ⟨⟨⟨r, hr⟩⟩, inferInstance⟩
  have ht2 : t ≤ 2 := by
    dsimp [t]
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact ht
  have ht_cases : t = 1 ∨ t = 2 := by omega
  have hns' : ∃ i : ZMod (2 * f), (w i).image labelStar ≠ w i := by
    obtain ⟨r, hr⟩ := hns
    refine ⟨(r.val : ZMod (2 * f)), ?_⟩
    have hval : (r.val : ZMod (2 * f)).val = r.val :=
      ZMod.val_natCast_of_lt (by omega : r.val < 2 * f)
    have hlt : (r.val : ZMod (2 * f)).val < f := by rw [hval]; exact r.isLt
    have hwval : w (r.val : ZMod (2 * f)) = ε r := by
      dsimp [w]
      rw [mkWord_apply_lt hf ε hlt]
      congr 1
      ext
      simp [hval]
    rwa [hwval]
  rcases ht_cases with ht1 | ht2'
  · have hT2 : Nat.card {i : ZMod (2 * f) // w i ≠ ∅} = 2 := by
      rw [hcardT, ht1]
    have hp_eq : p = 2 * f :=
      eq_two_mul_of_card_ne_eq_two (fun s : Finset (Fin n) => s.image labelStar)
        (∅ : Finset (Fin n)) w hf hw hpP.1 hpP.2 hmin' hT2 hns'
    omega
  · have hT4 : Nat.card {i : ZMod (2 * f) // w i ≠ ∅} = 4 := by
      rw [hcardT, ht2']
    have hp_eq : p = 2 * f :=
      eq_two_mul_of_card_ne_eq_four (fun s : Finset (Fin n) => s.image labelStar)
        (∅ : Finset (Fin n)) w hf hw hpP.1 hpP.2 hmin' hT4 hns'
    omega

end CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

end
