module

public import Certificates.Data.Kernel.HNFSubK
public import CFSG.Certificates.Kernel.HNFFibSound
public import CFSG.Certificates.Kernel.F3152.SortSound
import all CFSG.Certificates.Kernel.Spor.OrdSound

set_option exponentiation.threshold 8192
set_option maxRecDepth 100000

public section

namespace CFSG.KS.HNFSub

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.HNF26720 CFSG.KC.HNF26729 CFSG.KC.HNFFib CFSG.KC.HNFSub
  CFSG.KS.HNF26720 CFSG.KS.HNF26729 CFSG.KS.HNFFib CFSG.KS.HNLocal CFSG.KC.LQT.SecS Matrix

abbrev V := Fin 133 → ZMod 5

@[expose] def coord (x : V) (c : Nat) : ZMod 5 := if h : c < 133 then x ⟨c, h⟩ else 0

theorem coord_sum {ι : Type} (s : Finset ι) (a : ι → ZMod 5) (R : ι → V) (c : Nat) :
    coord (∑ i ∈ s, a i • R i) c = ∑ i ∈ s, a i * coord (R i) c := by
  unfold coord
  split_ifs with h
  · simp [Finset.sum_apply]
  · simp

@[expose] def Normal (W : Submodule (ZMod 5) V) (S : List Nat) (R : Fin 4 → V) : Prop :=
  (∀ i, R i ∈ W) ∧ (∀ i m : Fin 4, coord (R i) (getN 0 S (m : Nat)) = if i = m then 1 else 0) ∧
    ∀ x ∈ W, x = ∑ m : Fin 4, coord x (getN 0 S (m : Nat)) • R m

@[expose] def Vanish (W : Submodule (ZMod 5) V) (S : List Nat) : Prop :=
  ∃ x ∈ W, x ≠ 0 ∧ ∀ m : Fin 4, coord x (getN 0 S (m : Nat)) = 0

@[expose] def NormalAt (W : Submodule (ZMod 5) V) (cols : List (List Nat)) (j : Nat)
    (R : Fin 4 → V) : Prop :=
  Normal W (getLs cols j) R ∧ ∀ l < j, Vanish W (getLs cols l)

theorem eq_zero_of_normal {W : Submodule (ZMod 5) V} {S : List Nat} {R : Fin 4 → V}
    (h : Normal W S R) {x : V} (hx : x ∈ W) (h0 : ∀ m : Fin 4, coord x (getN 0 S (m : Nat)) = 0) :
    x = 0 := by
  rw [h.2.2 x hx]
  simp [h0]

theorem normal_unique {W : Submodule (ZMod 5) V} {cols : List (List Nat)} {j j' : Nat}
    {R R' : Fin 4 → V} (h : NormalAt W cols j R) (h' : NormalAt W cols j' R') : j = j' ∧ R = R' := by
  have hj : j = j' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨x, hx, hx0, hv⟩ := h'.2 j hlt
      exact hx0 (eq_zero_of_normal h.1 hx hv)
    · obtain ⟨x, hx, hx0, hv⟩ := h.2 j' hlt
      exact hx0 (eq_zero_of_normal h'.1 hx hv)
  subst hj
  refine ⟨rfl, funext fun i => ?_⟩
  rw [h'.1.2.2 (R i) (h.1.1 i)]
  simp [h.1.2.1 i]

theorem span_coe (b : Fin 4 → V) :
    (Submodule.span (ZMod 5) (Set.range b) : Set V) =
      Set.range (fun a : Fin 4 → ZMod 5 => ∑ i, a i • b i) := by
  ext x
  rw [SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun]
  rfl

theorem normal_of_span {C R : Fin 4 → V} {S : List Nat}
    (hR : ∀ i, R i ∈ Submodule.span (ZMod 5) (Set.range C))
    (hu : ∀ i m : Fin 4, coord (R i) (getN 0 S (m : Nat)) = if i = m then 1 else 0) :
    Normal (Submodule.span (ZMod 5) (Set.range C)) S R ∧
      Submodule.span (ZMod 5) (Set.range R) = Submodule.span (ZMod 5) (Set.range C) := by
  have hco : ∀ (a : Fin 4 → ZMod 5) (m : Fin 4),
      coord (∑ i, a i • R i) (getN 0 S (m : Nat)) = a m := by
    intro a m
    rw [coord_sum]
    simp [hu]
  have hfinj : Function.Injective (fun a : Fin 4 → ZMod 5 => ∑ i, a i • R i) := by
    intro a b hab
    funext m
    rw [← hco a m, ← hco b m]
    exact congrArg (coord · (getN 0 S (m : Nat))) hab
  have hle : Submodule.span (ZMod 5) (Set.range R) ≤ Submodule.span (ZMod 5) (Set.range C) :=
    Submodule.span_le.2 (Set.range_subset_iff.2 hR)
  have hcard : (Submodule.span (ZMod 5) (Set.range C) : Set V).ncard ≤
      (Submodule.span (ZMod 5) (Set.range R) : Set V).ncard := by
    rw [span_coe C, span_coe R, ← Set.image_univ, ← Set.image_univ,
      Set.ncard_image_of_injective _ hfinj]
    exact Set.ncard_image_le (Set.toFinite _)
  have heq : Submodule.span (ZMod 5) (Set.range R) = Submodule.span (ZMod 5) (Set.range C) :=
    SetLike.coe_injective (Set.eq_of_subset_of_ncard_le hle hcard (Set.toFinite _))
  refine ⟨⟨hR, hu, fun x hx => ?_⟩, heq⟩
  rw [← heq] at hx
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 5)).1 hx
  exact Finset.sum_congr rfl fun m _ => by rw [hco]

@[expose] def Uof (M N : Matrix (Fin 133) (Fin 133) (ZMod 5)) : Submodule (ZMod 5) V where
  carrier := {v | v ᵥ* M = -v ∧ v ᵥ* N = -v}
  add_mem' := by
    rintro a b ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by rw [Matrix.add_vecMul, h1, h3, neg_add], by rw [Matrix.add_vecMul, h2, h4, neg_add]⟩
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' := by
    rintro c a ⟨h1, h2⟩
    exact ⟨by rw [Matrix.smul_vecMul, h1, smul_neg], by rw [Matrix.smul_vecMul, h2, smul_neg]⟩

theorem mem_Uof {M N : Matrix (Fin 133) (Fin 133) (ZMod 5)} {v : V} :
    v ∈ Uof M N ↔ v ᵥ* M = -v ∧ v ᵥ* N = -v := Iff.rfl

theorem vecMul_cancel {P Pi : Matrix (Fin 133) (Fin 133) (ZMod 5)} (h : P * Pi = 1) {x y : V}
    (hxy : x ᵥ* P = y ᵥ* P) : x = y := by
  have := congrArg (· ᵥ* Pi) hxy
  simpa [Matrix.vecMul_vecMul, h] using this

theorem Uof_conj {M Z P Pi : Matrix (Fin 133) (Fin 133) (ZMod 5)} (hPPi : P * Pi = 1)
    (hPiP : Pi * P = 1) (hM : P * M = M * P) :
    Uof M (P * Z * Pi) = (Uof M Z).comap (Matrix.vecMulLinear P) := by
  ext v
  rw [Submodule.mem_comap, Matrix.vecMulLinear_apply, mem_Uof, mem_Uof]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · calc v ᵥ* P ᵥ* M = v ᵥ* M ᵥ* P := by simp only [Matrix.vecMul_vecMul, hM]
        _ = -(v ᵥ* P) := by rw [h1, Matrix.neg_vecMul]
    · calc v ᵥ* P ᵥ* Z = v ᵥ* (P * Z * Pi) ᵥ* P := by
            simp only [Matrix.vecMul_vecMul]
            rw [Matrix.mul_assoc (P * Z) Pi P, hPiP, Matrix.mul_one]
        _ = -(v ᵥ* P) := by rw [h2, Matrix.neg_vecMul]
  · rintro ⟨h1, h2⟩
    refine ⟨vecMul_cancel hPPi ?_, ?_⟩
    · calc v ᵥ* M ᵥ* P = v ᵥ* P ᵥ* M := by simp only [Matrix.vecMul_vecMul, hM]
        _ = -(v ᵥ* P) := h1
        _ = -v ᵥ* P := (Matrix.neg_vecMul _ _).symm
    · calc v ᵥ* (P * Z * Pi) = v ᵥ* P ᵥ* Z ᵥ* Pi := by simp only [Matrix.vecMul_vecMul]
        _ = -(v ᵥ* P) ᵥ* Pi := by rw [h2]
        _ = -v := by rw [Matrix.neg_vecMul, Matrix.vecMul_vecMul, hPPi, Matrix.vecMul_one]

theorem map_eq_comap {P Pi : Matrix (Fin 133) (Fin 133) (ZMod 5)} (hPPi : P * Pi = 1)
    (hPiP : Pi * P = 1) (W : Submodule (ZMod 5) V) :
    W.map (Matrix.vecMulLinear P) = W.comap (Matrix.vecMulLinear Pi) := by
  ext v
  rw [Submodule.mem_map, Submodule.mem_comap, Matrix.vecMulLinear_apply]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, hPPi, Matrix.vecMul_one]
    exact hw
  · intro hv
    refine ⟨v ᵥ* Pi, hv, ?_⟩
    rw [Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, hPiP, Matrix.vecMul_one]

section Fibre

variable {G : Type} [Group G]

theorem fib_card_map [Finite G] {Y : Type} (C K : Subgroup G) (β : G) (φ : G → Y)
    (act : G → Y → Y) (hφ : ∀ c ∈ C, ∀ z, φ (c * z * c⁻¹) = act c (φ z)) (hK : K ≤ C)
    (hKφ : ∀ k ∈ K, φ (k * β * k⁻¹) = φ β) :
    (φ '' conjS C β).ncard * (conjS K β).ncard ≤ (conjS C β).ncard := by
  classical
  have hX : ∀ x ∈ conjS K β, φ x = φ β := by
    rintro x ⟨k, hk, rfl⟩
    exact hKφ k hk
  have hY : ∀ y ∈ φ '' conjS C β, ∃ c ∈ C, φ (c * β * c⁻¹) = y := by
    rintro y ⟨x, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, rfl⟩
  choose! c hcC hcy using hY
  let F : ↥(φ '' conjS C β) × ↥(conjS K β) → ↥(conjS C β) := fun p =>
    ⟨c p.1 * p.2 * (c p.1)⁻¹, by
      obtain ⟨k, hk, hx⟩ := p.2.2
      refine ⟨c p.1 * k, C.mul_mem (hcC _ p.1.2) (hK hk), ?_⟩
      rw [← hx]
      group⟩
  have himg : ∀ yy ∈ φ '' conjS C β, ∀ xx ∈ conjS K β, φ (c yy * xx * (c yy)⁻¹) = yy := by
    intro yy hyy xx hxx
    rw [hφ _ (hcC yy hyy), hX xx hxx, ← hφ _ (hcC yy hyy), hcy yy hyy]
  have hinj : Function.Injective F := by
    rintro ⟨⟨y1, hy1⟩, ⟨x1, hx1⟩⟩ ⟨⟨y2, hy2⟩, ⟨x2, hx2⟩⟩ he
    have he' : c y1 * x1 * (c y1)⁻¹ = c y2 * x2 * (c y2)⁻¹ := congrArg Subtype.val he
    have e1 := himg y1 hy1 x1 hx1
    rw [he', himg y2 hy2 x2 hx2] at e1
    subst e1
    have e2 : x1 = x2 := mul_left_cancel (mul_right_cancel he')
    subst e2
    rfl
  have h := Nat.card_le_card_of_injective F hinj
  rwa [Nat.card_prod, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h

end Fibre

@[expose] noncomputable def keyOf (r0 r1 r2 r3 : Nat) : Nat :=
  bitsN (Nat.add r0 (Nat.add (Nat.mul 7 r1) (Nat.add (Nat.mul 49 r2) (Nat.mul 343 r3)))) 65 130

@[expose] def KeyReal (cols : List (List Nat)) (Q : Set (Submodule (ZMod 5) V)) (k : Nat) : Prop :=
  ∃ W ∈ Q, ∃ j, ∃ rs : Fin 4 → Nat, (∀ i, VCanon 5 133 13 (rs i)) ∧
    NormalAt W cols j (fun i => toVec 5 133 13 (rs i)) ∧ k = keyOf (rs 0) (rs 1) (rs 2) (rs 3)

theorem card_le_keys (cols : List (List Nat)) (Q : Set (Submodule (ZMod 5) V)) (hQ : Q.Finite)
    (l : List Nat) (hnd : l.Nodup) (hl : ∀ k ∈ l, KeyReal cols Q k) : l.length ≤ Q.ncard := by
  classical
  have hfin : Finite ↥Q := hQ.to_subtype
  have hsel : ∀ x : l.toFinset, ∃ W : Q, ∃ j, ∃ rs : Fin 4 → Nat, (∀ i, VCanon 5 133 13 (rs i)) ∧
      NormalAt (W : Submodule (ZMod 5) V) cols j (fun i => toVec 5 133 13 (rs i)) ∧
        x.val = keyOf (rs 0) (rs 1) (rs 2) (rs 3) := fun x => by
    obtain ⟨W, hW, j, rs, hc, hn, hk⟩ := hl x.val (List.mem_toFinset.1 x.2)
    exact ⟨⟨W, hW⟩, j, rs, hc, hn, hk⟩
  choose f j rs hc hn hk using hsel
  have hinj : Function.Injective f := by
    intro x y hxy
    have hn' := hn y
    rw [← hxy] at hn'
    obtain ⟨-, hR⟩ := normal_unique (hn x) hn'
    have e : rs x = rs y := funext fun i =>
      vec_inj (by norm_num) (hc x i) (hc y i) (congrFun hR i)
    exact Subtype.ext (by rw [hk x, hk y, e])
  have h1 := Nat.card_le_card_of_injective f hinj
  rwa [Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd,
    Nat.card_coe_set_eq] at h1

theorem msortH_perm (ks : List Nat) : (msortH ks).Perm ks := by
  unfold msortH
  have h := CFSG.KS.F3152.passK_perm 131072 17 (ks.map fun k => [k])
  rw [CFSG.KS.F3152.flatten_singletons] at h
  exact h

theorem distOK_sound {N : Nat} {segs : List (List (List Nat))} (h : distOK N segs = true) :
    (allKeys segs).length = N ∧ (allKeys segs).Nodup := by
  unfold distOK at h
  have h1 : Nat.beq (allKeys segs).length N = true ∧
      CFSG.KS.F3152.sortedK (msortH (allKeys segs)) = true := by
    revert h
    cases Nat.beq (allKeys segs).length N <;> cases CFSG.KS.F3152.sortedK (msortH (allKeys segs)) <;>
      simp [andB]
  exact ⟨Nat.eq_of_beq_eq_true h1.1, (msortH_perm _).nodup_iff.1
    ((CFSG.KS.F3152.sortedK_pairwise _ h1.2).imp Nat.ne_of_lt)⟩

theorem getSg_mem : ∀ (segs : List (List (List Nat))) (i : Nat), i < segs.length →
    getSg segs i ∈ segs
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | c :: _, 0, _ => List.mem_cons_self
  | c :: cs, i + 1, h => List.mem_cons_of_mem c
      (getSg_mem cs i (by simp only [List.length_cons] at h; omega))

theorem mem_allKeys : ∀ (segs : List (List (List Nat))) (k : Nat), k ∈ allKeys segs →
    ∃ i < segs.length, k ∈ keysOf (getSg segs i)
  | [], _, h => absurd h List.not_mem_nil
  | c :: cs, k, h => by
    have e : allKeys (c :: cs) = keysOf c ++ allKeys cs := rfl
    rw [e] at h
    rcases List.mem_append.1 h with h | h
    · exact ⟨0, by simp, h⟩
    · obtain ⟨i, hi, hk⟩ := mem_allKeys cs k h
      exact ⟨i + 1, by simp only [List.length_cons]; omega, hk⟩

theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem shl_eq (a b : Nat) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

theorem lane_add_mul {w a : Nat} (b : Nat) (ha : a < 2 ^ w) :
    lane w (a + 2 ^ w * b) 0 = a ∧ ∀ k, lane w (a + 2 ^ w * b) (k + 1) = lane w b k := by
  refine ⟨?_, fun k => ?_⟩
  · unfold lane
    rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  · unfold lane
    have e : 2 ^ (w * (k + 1)) = 2 ^ w * 2 ^ (w * k) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    rw [e, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (Nat.two_pow_pos w),
      Nat.div_eq_of_lt ha, Nat.zero_add]

theorem lane_small {w a : Nat} (ha : a < 2 ^ w) (k : Nat) : lane w a (k + 1) = 0 := by
  have := (lane_add_mul 0 ha).2 k
  rw [Nat.mul_zero, Nat.add_zero] at this
  rw [this]
  unfold lane
  simp

theorem mat4_eq (c0 c1 c2 c3 : Nat) :
    mat4 c0 c1 c2 c3 = c0 + 2 ^ 1729 * (c1 + 2 ^ 1729 * (c2 + 2 ^ 1729 * c3)) := by
  unfold mat4
  change c0 + (Nat.shiftLeft c1 1729 + (Nat.shiftLeft c2 3458 + Nat.shiftLeft c3 5187)) = _
  rw [shl_eq, shl_eq, shl_eq]
  have e2 : (2 : Nat) ^ 3458 = 2 ^ 1729 * 2 ^ 1729 := by rw [← Nat.pow_add]
  have e3 : (2 : Nat) ^ 5187 = 2 ^ 1729 * (2 ^ 1729 * 2 ^ 1729) := by
    rw [← Nat.pow_add, ← Nat.pow_add]
  rw [e2, e3]
  generalize (2 : Nat) ^ 1729 = T
  ring

theorem lane_mat4 {c0 c1 c2 c3 : Nat} (h0 : c0 < 2 ^ 1729) (h1 : c1 < 2 ^ 1729)
    (h2 : c2 < 2 ^ 1729) (h3 : c3 < 2 ^ 1729) :
    ∀ k, lane 1729 (mat4 c0 c1 c2 c3) k = [c0, c1, c2, c3].getD k 0 := by
  intro k
  rw [mat4_eq]
  obtain ⟨a0, b0⟩ := lane_add_mul (c1 + 2 ^ 1729 * (c2 + 2 ^ 1729 * c3)) h0
  obtain ⟨a1, b1⟩ := lane_add_mul (c2 + 2 ^ 1729 * c3) h1
  obtain ⟨a2, b2⟩ := lane_add_mul c3 h2
  rcases k with _ | _ | _ | _ | k
  · exact a0
  · rw [b0, a1]
    rfl
  · rw [b0, b1, a2]
    rfl
  · rw [b0, b1, b2]
    unfold lane
    rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt h3]
    rfl
  · rw [b0, b1, b2, lane_small h3]
    rfl

theorem rowK_eq (M k : Nat) : rowK M k = lane 1729 M k := bitsN_lane M 1729 k

theorem ln_eq (v c : Nat) : ln v c = lane 13 v c := bitsN_lane v 13 c

theorem entry_eq (M i j : Nat) (hj : j < 133) :
    M / 2 ^ (1729 * i + 13 * j) % 2 ^ 13 = lane 13 (lane 1729 M i) j := by
  unfold lane
  have e1 : 2 ^ (1729 * i + 13 * j) = 2 ^ (1729 * i) * 2 ^ (13 * j) := Nat.pow_add _ _ _
  have e2 : (2 : Nat) ^ 1729 = 2 ^ (13 * j) * 2 ^ (1729 - 13 * j) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [e1, ← Nat.div_div_eq_div_mul, e2, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  exact Nat.pow_dvd_pow 2 (by omega)

theorem vcanon_lt {v : Nat} (hv : VCanon 5 133 13 v) : v < 2 ^ 1729 := hv.1

theorem lane_mat4' {c : Fin 4 → Nat} (hc : ∀ i, VCanon 5 133 13 (c i)) (k : Nat) :
    lane 1729 (mat4 (c 0) (c 1) (c 2) (c 3)) k =
      if h : k < 4 then c ⟨k, h⟩ else 0 := by
  rw [lane_mat4 (vcanon_lt (hc 0)) (vcanon_lt (hc 1)) (vcanon_lt (hc 2)) (vcanon_lt (hc 3))]
  rcases k with _ | _ | _ | _ | k
  · rfl
  · rfl
  · rfl
  · rfl
  · simp

theorem lane_zero (w j : Nat) : lane w 0 j = 0 := by
  unfold lane
  simp

theorem two_pow_mono {m n : Nat} (h : m ≤ n) : 2 ^ m ≤ 2 ^ n :=
  Nat.pow_le_pow_right (Nat.succ_pos 1) h

theorem canon_mat4 {c : Fin 4 → Nat} (hc : ∀ i, VCanon 5 133 13 (c i)) :
    Canon 5 133 13 (mat4 (c 0) (c 1) (c 2) (c 3)) := by
  refine ⟨?_, fun t ht => ?_⟩
  · rw [mat4_eq]
    have h0 := vcanon_lt (hc 0)
    have h1 := vcanon_lt (hc 1)
    have h2 := vcanon_lt (hc 2)
    have h3 := vcanon_lt (hc 3)
    have hb : ∀ a b n : Nat, a < 2 ^ 1729 → b < 2 ^ (1729 * n) → a + 2 ^ 1729 * b < 2 ^ (1729 * (n + 1)) := by
      intro a b n ha hb
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (1729 * n))]
      calc a + 2 ^ 1729 * b < 2 ^ 1729 + 2 ^ 1729 * b := by omega
        _ = 2 ^ 1729 * (b + 1) := by ring
        _ ≤ 2 ^ 1729 * 2 ^ (1729 * n) := Nat.mul_le_mul_left _ hb
    have h4 := hb _ _ 3 h0 (hb _ _ 2 h1 (hb _ _ 1 h2 (by simpa using h3)))
    exact Nat.lt_of_lt_of_le h4 (two_pow_mono (Nat.le_of_ble_eq_true rfl))
  · have e : 13 * t = 1729 * (t / 133) + 13 * (t % 133) := by omega
    unfold lane
    rw [e, entry_eq _ _ _ (Nat.mod_lt _ (by norm_num)), lane_mat4' hc]
    split_ifs with h
    · exact (hc _).2 _ (Nat.mod_lt _ (by norm_num))
    · rw [lane_zero]
      norm_num

theorem om_mat4 {c : Fin 4 → Nat} (hc : ∀ i, VCanon 5 133 13 (c i)) (i j : Fin 133) :
    OM (mat4 (c 0) (c 1) (c 2) (c 3)) i j =
      if h : i.val < 4 then toVec 5 133 13 (c ⟨i.val, h⟩) j else 0 := by
  change ((mat4 (c 0) (c 1) (c 2) (c 3) / 2 ^ (1729 * i.val + 13 * j.val) % 2 ^ 13 : Nat) :
    ZMod 5) = _
  rw [entry_eq _ _ _ j.isLt, lane_mat4' hc]
  split_ifs with h
  · rfl
  · rw [lane_zero]
    simp

theorem vecMul_mat4_mem {c : Fin 4 → Nat} (hc : ∀ i, VCanon 5 133 13 (c i)) (x : V) :
    x ᵥ* OM (mat4 (c 0) (c 1) (c 2) (c 3)) ∈
      Submodule.span (ZMod 5) (Set.range fun i => toVec 5 133 13 (c i)) := by
  have e : x ᵥ* OM (mat4 (c 0) (c 1) (c 2) (c 3)) =
      ∑ i : Fin 133, x i • (if h : i.val < 4 then toVec 5 133 13 (c ⟨i.val, h⟩) else 0) := by
    funext j
    simp only [Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      om_mat4 hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [e]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  split_ifs with h
  · exact Submodule.subset_span ⟨_, rfl⟩
  · exact Submodule.zero_mem _

theorem mat4_inj {a b : Fin 4 → Nat} (ha : ∀ i, VCanon 5 133 13 (a i))
    (hb : ∀ i, VCanon 5 133 13 (b i))
    (h : mat4 (a 0) (a 1) (a 2) (a 3) = mat4 (b 0) (b 1) (b 2) (b 3)) : a = b := by
  funext i
  have := congrArg (lane 1729 · i) h
  simp only [lane_mat4' ha, lane_mat4' hb, dif_pos i.isLt] at this
  exact this

theorem rowK_mat4 {c : Fin 4 → Nat} (hc : ∀ i, VCanon 5 133 13 (c i)) (i : Fin 4) :
    rowK (mat4 (c 0) (c 1) (c 2) (c 3)) i = c i := by
  rw [rowK_eq, lane_mat4' hc, dif_pos i.isLt]

theorem img4_eq (vec : Nat → Nat → Nat) (P G : Nat) (k : Nat → Bool) :
    img4 vec P G k = k (mat4 (vec (rowK P 0) G) (vec (rowK P 1) G) (vec (rowK P 2) G)
      (vec (rowK P 3) G)) := by
  unfold img4
  simp only [CFSG.KS.HNF26720.strictB_eq]

theorem span_map (c : Fin 4 → V) (M : Matrix (Fin 133) (Fin 133) (ZMod 5)) :
    Submodule.span (ZMod 5) (Set.range fun i => c i ᵥ* M) =
      (Submodule.span (ZMod 5) (Set.range c)).map (Matrix.vecMulLinear M) := by
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem dropN_eq : ∀ (n : Nat) (l : List Nat), dropN n l = l.drop n
  | 0, l => rfl
  | n + 1, l => by
    have e : dropN (n + 1) l =
        dropN n (List.rec (motive := fun _ => List Nat) [] (fun _ t _ => t) l) := rfl
    rw [e, dropN_eq n]
    cases l <;> simp

theorem headN_mem (P : Nat → Prop) {d : Nat} (hd : P d) :
    ∀ l : List Nat, (∀ x ∈ l, P x) → P (headN d l)
  | [], _ => hd
  | x :: _, h => h x List.mem_cons_self

theorem lane_big {v c : Nat} (hv : VCanon 5 133 13 v) (hc : 133 ≤ c) : lane 13 v c = 0 := by
  unfold lane
  rw [Nat.div_eq_of_lt (lt_of_lt_of_le hv.1 (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  rfl

theorem coord_toVec {v : Nat} (hv : VCanon 5 133 13 v) (c : Nat) :
    coord (toVec 5 133 13 v) c = ((lane 13 v c : Nat) : ZMod 5) := by
  unfold coord
  split_ifs with h
  · rfl
  · rw [lane_big hv (by omega)]
    simp

theorem atS_sound {v : Nat} (hv : VCanon 5 133 13 v) {S : List Nat} {e0 e1 e2 e3 : Nat}
    (h : atS v S e0 e1 e2 e3 = true) :
    coord (toVec 5 133 13 v) (getN 0 S 0) = (e0 : ZMod 5) ∧
      coord (toVec 5 133 13 v) (getN 0 S 1) = (e1 : ZMod 5) ∧
      coord (toVec 5 133 13 v) (getN 0 S 2) = (e2 : ZMod 5) ∧
      coord (toVec 5 133 13 v) (getN 0 S 3) = (e3 : ZMod 5) := by
  unfold atS at h
  obtain ⟨h0, h⟩ := andB_true h
  obtain ⟨h1, h⟩ := andB_true h
  obtain ⟨h2, h3⟩ := andB_true h
  simp only [coord_toVec hv, ← ln_eq]
  exact ⟨by rw [Nat.eq_of_beq_eq_true h0], by rw [Nat.eq_of_beq_eq_true h1],
    by rw [Nat.eq_of_beq_eq_true h2], by rw [Nat.eq_of_beq_eq_true h3]⟩

theorem keysOf_cons (r : List Nat) (seg : List (List Nat)) :
    keysOf (r :: seg) = Bool.rec (motive := fun _ => List Nat) (keysOf seg)
      (getN 0 r 5 :: keysOf seg) (Nat.beq (Nat.land (getN 0 r 0) 1) 1) := rfl

@[expose] def InvB (Q : Set (Submodule (ZMod 5) V)) (P : Nat) : Prop :=
  ∃ c : Fin 4 → Nat, (∀ i, VCanon 5 133 13 (c i)) ∧ P = mat4 (c 0) (c 1) (c 2) (c 3) ∧
    Submodule.span (ZMod 5) (Set.range fun i => toVec 5 133 13 (c i)) ∈ Q

@[expose] noncomputable def rvec (r0 : List Nat) (i : Fin 4) : V := toVec 5 133 13 (getN 0 r0 i)

@[expose] noncomputable def spanR (r0 : List Nat) : Submodule (ZMod 5) V :=
  Submodule.span (ZMod 5) (Set.range (rvec r0))

section Sound

variable {L H CM RM ONE LV HV : Nat} (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
include hc

theorem img4_mat4 {c : Fin 4 → Nat} (hcc : ∀ i, VCanon 5 133 13 (c i)) {G : Nat}
    (cG : Canon 5 133 13 G) {k : Nat → Bool}
    (h : img4 (vecR 5 13 1729 133 9 LV HV RM) (mat4 (c 0) (c 1) (c 2) (c 3)) G k = true) :
    ∃ d : Fin 4 → Nat, (∀ i, VCanon 5 133 13 (d i)) ∧
      (∀ i, toVec 5 133 13 (d i) = toVec 5 133 13 (c i) ᵥ* OM G) ∧
        k (mat4 (d 0) (d 1) (d 2) (d 3)) = true := by
  rw [img4_eq] at h
  have e0 : rowK (mat4 (c 0) (c 1) (c 2) (c 3)) 0 = c 0 := rowK_mat4 hcc 0
  have e1 : rowK (mat4 (c 0) (c 1) (c 2) (c 3)) 1 = c 1 := rowK_mat4 hcc 1
  have e2 : rowK (mat4 (c 0) (c 1) (c 2) (c 3)) 2 = c 2 := rowK_mat4 hcc 2
  have e3 : rowK (mat4 (c 0) (c 1) (c 2) (c 3)) 3 = c 3 := rowK_mat4 hcc 3
  rw [e0, e1, e2, e3] at h
  exact ⟨fun i => vecR 5 13 1729 133 9 LV HV RM (c i) G, fun i => (vecR_sound hc (hcc i) cG).1,
    fun i => (vecR_sound hc (hcc i) cG).2, h⟩

theorem stabOK_sound {c : Fin 4 → Nat} (hcc : ∀ i, VCanon 5 133 13 (c i)) :
    ∀ (Lr : List (Nat × Nat)) (ts : List (List Nat)), (∀ p ∈ Lr, Canon 5 133 13 p.1) →
      stabOK (vecR 5 13 1729 133 9 LV HV RM) (validM 5 1729 LV HV)
        (mat4 (c 0) (c 1) (c 2) (c 3)) Lr ts = true →
      ∀ p ∈ Lr, Submodule.span (ZMod 5) (Set.range fun i => toVec 5 133 13 (c i)) ≤
        (Submodule.span (ZMod 5) (Set.range fun i => toVec 5 133 13 (c i))).map
          (Matrix.vecMulLinear (OM p.1))
  | [], _, _, _, p, hp => absurd hp List.not_mem_nil
  | q :: Lr, [], _, h, _, _ => absurd h Bool.false_ne_true
  | q :: Lr, t :: ts, hL, h, p, hp => by
    change img4 _ _ q.1 _ = true at h
    obtain ⟨d, hd, ed, h⟩ := img4_mat4 hc hcc (hL q List.mem_cons_self) h
    obtain ⟨v0, h⟩ := andB_true h
    obtain ⟨v1, h⟩ := andB_true h
    obtain ⟨v2, h⟩ := andB_true h
    obtain ⟨v3, h⟩ := andB_true h
    obtain ⟨hm, h⟩ := andB_true h
    rcases List.mem_cons.1 hp with rfl | hp
    · have cd := canon_mat4 hd
      have ht : ∀ i : Fin 4, VCanon 5 133 13 (getN 0 t i) := by
        intro i
        fin_cases i
        · exact CFSG.KS.J4Hub.validV_canon hc v0
        · exact CFSG.KS.J4Hub.validV_canon hc v1
        · exact CFSG.KS.J4Hub.validV_canon hc v2
        · exact CFSG.KS.J4Hub.validV_canon hc v3
      have he := mat4_inj (a := fun i => vecR 5 13 1729 133 9 LV HV RM (getN 0 t i)
          (mat4 (d 0) (d 1) (d 2) (d 3))) (fun i => (vecR_sound hc (ht i) cd).1) hcc
        (Nat.eq_of_beq_eq_true hm)
      have hsp := span_map (fun i => toVec 5 133 13 (c i)) (OM p.1)
      have hd' : (fun i => toVec 5 133 13 (c i) ᵥ* OM p.1) = fun i => toVec 5 133 13 (d i) :=
        funext fun i => (ed i).symm
      rw [hd'] at hsp
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      have hai : vecR 5 13 1729 133 9 LV HV RM (getN 0 t i) (mat4 (d 0) (d 1) (d 2) (d 3)) = c i :=
        congrFun he i
      have hmem : toVec 5 133 13 (c i) ∈
          Submodule.span (ZMod 5) (Set.range fun i => toVec 5 133 13 (d i)) := by
        rw [← hai, (vecR_sound hc (ht i) cd).2]
        exact vecMul_mat4_mem hd _
      rw [hsp] at hmem
      exact hmem
    · exact stabOK_sound hcc Lr ts (fun p hp => hL p (List.mem_cons_of_mem _ hp)) h p hp

theorem child_sound {Q : Set (Submodule (ZMod 5) V)} {G0 G1 : Nat} (cG0 : Canon 5 133 13 G0)
    (cG1 : Canon 5 133 13 G1)
    (hQ : ∀ W ∈ Q, W.map (Matrix.vecMulLinear (OM G0)) ∈ Q ∧
      W.map (Matrix.vecMulLinear (OM G1)) ∈ Q)
    {P g : Nat} (hP : InvB Q P) {k : Nat → Bool}
    (h : child (vecR 5 13 1729 133 9 LV HV RM) G0 G1 P g k = true) :
    ∃ C, InvB Q C ∧ k C = true := by
  unfold child at h
  cases hg : Nat.beq g 2
  · rw [hg] at h
    obtain ⟨c, hcc, hPc, hcQ⟩ := hP
    rw [hPc] at h
    have key : ∀ G : Nat, Canon 5 133 13 G →
        (∀ W ∈ Q, W.map (Matrix.vecMulLinear (OM G)) ∈ Q) →
        img4 (vecR 5 13 1729 133 9 LV HV RM) (mat4 (c 0) (c 1) (c 2) (c 3)) G k = true →
        ∃ C, InvB Q C ∧ k C = true := by
      intro G cG hG h
      obtain ⟨d, hd, ed, hk⟩ := img4_mat4 hc hcc cG h
      refine ⟨_, ⟨d, hd, rfl, ?_⟩, hk⟩
      have e : (fun i => toVec 5 133 13 (d i)) = fun i => toVec 5 133 13 (c i) ᵥ* OM G :=
        funext ed
      rw [e, span_map]
      exact hG _ hcQ
    generalize hb : Nat.beq g 0 = b at h
    cases b
    · exact key G1 cG1 (fun W hW => (hQ W hW).2) h
    · exact key G0 cG0 (fun W hW => (hQ W hW).1) h
  · rw [hg] at h
    exact ⟨P, hP, h⟩

theorem witOK_sound {c : Fin 4 → Nat} (hcc : ∀ i, VCanon 5 133 13 (c i))
    (cols : List (List Nat)) :
    ∀ (xs : List Nat) (l : Nat) (k : Nat → Bool),
      witOK (vecR 5 13 1729 133 9 LV HV RM) (validM 5 1729 LV HV) (mat4 (c 0) (c 1) (c 2) (c 3))
        cols xs l k = true →
      ∃ j, (∀ l' < j, l ≤ l' →
        Vanish (Submodule.span (ZMod 5) (Set.range fun i => toVec 5 133 13 (c i)))
          (getLs cols l')) ∧ k j = true
  | [], l, k, h => ⟨l, fun l' h1 h2 => absurd h1 (by omega), h⟩
  | x :: xs, l, k, h => by
    change andB (validM 5 1729 LV HV x) (strictB (vecR 5 13 1729 133 9 LV HV RM x
      (mat4 (c 0) (c 1) (c 2) (c 3))) fun y => andB (notB (Nat.beq y 0))
        (andB (atS y (getLs cols l) 0 0 0 0) (strictB (Nat.succ l) fun l' =>
          witOK (vecR 5 13 1729 133 9 LV HV RM) (validM 5 1729 LV HV)
            (mat4 (c 0) (c 1) (c 2) (c 3)) cols xs l' k))) = true at h
    simp only [CFSG.KS.HNF26720.strictB_eq] at h
    obtain ⟨hx, h⟩ := andB_true h
    obtain ⟨hy0, h⟩ := andB_true h
    obtain ⟨hat, h⟩ := andB_true h
    have cx := CFSG.KS.J4Hub.validV_canon hc hx
    have cC := canon_mat4 hcc
    obtain ⟨cy, ey⟩ := vecR_sound hc cx cC
    obtain ⟨j, hj, hk⟩ := witOK_sound hcc cols xs (l + 1) k h
    refine ⟨j, fun l' h1 h2 => ?_, hk⟩
    rcases Nat.lt_or_ge l' (l + 1) with h3 | h3
    · have hl : l' = l := by omega
      subst hl
      refine ⟨_, vecMul_mat4_mem hcc (toVec 5 133 13 x), ?_, ?_⟩
      · rw [← ey]
        intro h0
        have hz : VCanon 5 133 13 0 := ⟨Nat.two_pow_pos _, fun j _ => by
          rw [lane_zero]
          norm_num⟩
        have := vec_inj (by norm_num) cy hz (by rw [h0]; funext i; simp [toVec, lane_zero])
        exact CFSG.KC.LQT.SecS.ne_of_notB hy0 this
      · obtain ⟨a0, a1, a2, a3⟩ := atS_sound cy hat
        rw [← ey]
        intro m
        fin_cases m
        · simpa using a0
        · simpa using a1
        · simpa using a2
        · simpa using a3
    · exact hj l' h1 h3

theorem node_sound {Q : Set (Submodule (ZMod 5) V)} {G0 G1 : Nat} (cG0 : Canon 5 133 13 G0)
    (cG1 : Canon 5 133 13 G1)
    (hQ : ∀ W ∈ Q, W.map (Matrix.vecMulLinear (OM G0)) ∈ Q ∧
      W.map (Matrix.vecMulLinear (OM G1)) ∈ Q)
    {cols : List (List Nat)} {P : Nat} (hP : InvB Q P) {r : List Nat} {k : Nat → Bool}
    (h : node (vecR 5 13 1729 133 9 LV HV RM) (validM 5 1729 LV HV) G0 G1 cols P r k = true) :
    ∃ R, InvB Q R ∧ k R = true ∧ KeyReal cols Q (getN 0 r 5) := by
  unfold node at h
  obtain ⟨C, ⟨c, hcc, hCc, hcQ⟩, h⟩ := child_sound hc cG0 cG1 hQ hP h
  rw [hCc] at h
  obtain ⟨v1, h⟩ := andB_true h
  obtain ⟨v2, h⟩ := andB_true h
  obtain ⟨v3, h⟩ := andB_true h
  obtain ⟨v4, h⟩ := andB_true h
  simp only [CFSG.KS.HNF26720.strictB_eq] at h
  obtain ⟨j, hj, h⟩ := witOK_sound hc hcc cols _ 0 _ h
  obtain ⟨u0, h⟩ := andB_true h
  obtain ⟨u1, h⟩ := andB_true h
  obtain ⟨u2, h⟩ := andB_true h
  obtain ⟨u3, h⟩ := andB_true h
  obtain ⟨hkey, h⟩ := andB_true h
  have cC := canon_mat4 hcc
  let t : Fin 4 → Nat := fun i => getN 0 r (i + 1)
  have ht : ∀ i, VCanon 5 133 13 (t i) := by
    intro i
    fin_cases i
    · exact CFSG.KS.J4Hub.validV_canon hc v1
    · exact CFSG.KS.J4Hub.validV_canon hc v2
    · exact CFSG.KS.J4Hub.validV_canon hc v3
    · exact CFSG.KS.J4Hub.validV_canon hc v4
  let R : Fin 4 → Nat := fun i => vecR 5 13 1729 133 9 LV HV RM (t i) (mat4 (c 0) (c 1) (c 2) (c 3))
  have hR : ∀ i, VCanon 5 133 13 (R i) := fun i => (vecR_sound hc (ht i) cC).1
  have hRmem : ∀ i, toVec 5 133 13 (R i) ∈
      Submodule.span (ZMod 5) (Set.range fun i => toVec 5 133 13 (c i)) := fun i => by
    rw [(vecR_sound hc (ht i) cC).2]
    exact vecMul_mat4_mem hcc _
  have hu : ∀ i m : Fin 4, coord (toVec 5 133 13 (R i)) (getN 0 (getLs cols j) (m : Nat)) =
      if i = m then 1 else 0 := by
    obtain ⟨a00, a01, a02, a03⟩ := atS_sound (hR 0) u0
    obtain ⟨a10, a11, a12, a13⟩ := atS_sound (hR 1) u1
    obtain ⟨a20, a21, a22, a23⟩ := atS_sound (hR 2) u2
    obtain ⟨a30, a31, a32, a33⟩ := atS_sound (hR 3) u3
    intro i m
    fin_cases i <;> fin_cases m <;> simp_all
  obtain ⟨hN, hspan⟩ := normal_of_span hRmem hu
  refine ⟨mat4 (R 0) (R 1) (R 2) (R 3), ⟨R, hR, rfl, by rw [hspan]; exact hcQ⟩, h, ?_⟩
  refine ⟨_, hcQ, j, R, hR, ⟨hN, fun l hl => hj l hl (Nat.zero_le _)⟩, ?_⟩
  exact (Nat.eq_of_beq_eq_true hkey).symm

theorem walk_sound {Q : Set (Submodule (ZMod 5) V)} {G0 G1 : Nat} (cG0 : Canon 5 133 13 G0)
    (cG1 : Canon 5 133 13 G1)
    (hQ : ∀ W ∈ Q, W.map (Matrix.vecMulLinear (OM G0)) ∈ Q ∧
      W.map (Matrix.vecMulLinear (OM G1)) ∈ Q)
    {cols : List (List Nat)} {B : Nat} (hB : InvB Q B) :
    ∀ (seg : List (List Nat)) (st : List Nat), (∀ x ∈ st, InvB Q x) →
      walk (vecR 5 13 1729 133 9 LV HV RM) (validM 5 1729 LV HV) G0 G1 B cols seg st = true →
      ∀ k ∈ keysOf seg, KeyReal cols Q k
  | [], _, _, _, k, hk => absurd hk List.not_mem_nil
  | r :: seg, st, hst, h, k, hk => by
    change node (vecR 5 13 1729 133 9 LV HV RM) (validM 5 1729 LV HV) G0 G1 cols
      (headN B (dropN (Nat.shiftRight (getN 0 r 0) 3) st)) r
      (fun R => walk (vecR 5 13 1729 133 9 LV HV RM) (validM 5 1729 LV HV) G0 G1 B cols seg
        (R :: dropN (Nat.shiftRight (getN 0 r 0) 3) st)) = true at h
    have hst' : ∀ x ∈ dropN (Nat.shiftRight (getN 0 r 0) 3) st, InvB Q x := by
      rw [dropN_eq]
      exact fun x hx => hst x (List.mem_of_mem_drop hx)
    obtain ⟨R, hR, h, hkey⟩ := node_sound hc cG0 cG1 hQ (headN_mem _ hB _ hst') h
    have hst2 : ∀ x ∈ R :: dropN (Nat.shiftRight (getN 0 r 0) 3) st, InvB Q x := fun x hx => by
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hR
      · exact hst' x hx
    rw [keysOf_cons] at hk
    generalize Nat.beq (Nat.land (getN 0 r 0) 1) 1 = bb at hk
    cases bb with
    | false => exact walk_sound cG0 cG1 hQ hB seg _ hst2 h k hk
    | true =>
      rcases List.mem_cons.1 hk with rfl | hk
      · exact hkey
      · exact walk_sound cG0 cG1 hQ hB seg _ hst2 h k hk

theorem seg_sound {A B Bi : Nat} (cA : Canon 5 133 13 A) (cB : Canon 5 133 13 B)
    (cBi : Canon 5 133 13 Bi) {w1 w2 : List Int} {r0 : List Nat} {cols : List (List Nat)}
    {seg : List (List Nat)}
    (h : segOK (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM)
      (validM 5 1729 LV HV) A B Bi ONE w1 w2 r0 cols seg = true)
    (hr0 : ∀ i : Fin 4, VCanon 5 133 13 (getN 0 r0 i))
    (Q : Set (Submodule (ZMod 5) V)) (hB : spanR r0 ∈ Q)
    (hQ : ∀ W ∈ Q, W.map (Matrix.vecMulLinear (MW A B Bi (invW w1))) ∈ Q ∧
      W.map (Matrix.vecMulLinear (MW A B Bi (invW w2))) ∈ Q) :
    ∀ k ∈ keysOf seg, KeyReal cols Q k := by
  unfold segOK at h
  simp only [CFSG.KS.HNF26720.strictB_eq] at h
  obtain ⟨c1i, e1i⟩ := wprod_sound hc cA cB cBi (invW w1)
  obtain ⟨c2i, e2i⟩ := wprod_sound hc cA cB cBi (invW w2)
  have hQ' : ∀ W ∈ Q, W.map (Matrix.vecMulLinear (OM (wprod (mulR 5 13 1729 133 9 L H CM RM) A B
      Bi ONE (invW w1)))) ∈ Q ∧ W.map (Matrix.vecMulLinear (OM (wprod (mulR 5 13 1729 133 9 L H
      CM RM) A B Bi ONE (invW w2)))) ∈ Q := by
    intro W hW
    have a1 : OM (wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE (invW w1)) =
        MW A B Bi (invW w1) := e1i
    have a2 : OM (wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE (invW w2)) =
        MW A B Bi (invW w2) := e2i
    rw [a1, a2]
    exact hQ W hW
  have hB' : InvB Q (base r0) := ⟨fun i => getN 0 r0 i, hr0, rfl, hB⟩
  exact walk_sound hc c1i c2i hQ' hB' seg [] (fun x hx => absurd hx List.not_mem_nil) h

omit hc in
private theorem hs_OM_pk {g : Nat → Nat} (hg : ∀ t < 133 * 133, g t < 2 ^ 13) (i j : Fin 133) :
    OM (pk 13 (133 * 133) g) i j = ((g (133 * i.val + j.val) : Nat) : ZMod 5) :=
  ordMat_pk hg i j

omit hc in
private theorem hs_OM_lane (X : Nat) (i j : Fin 133) :
    OM X i j = ((lane 13 X (133 * i.val + j.val) : Nat) : ZMod 5) := by
  change ((X / 2 ^ (1729 * i.val + 13 * j.val) % 2 ^ 13 : Nat) : ZMod 5) = _
  unfold lane
  rw [show 13 * (133 * i.val + j.val) = 1729 * i.val + 13 * j.val by ring]

private theorem hs_redP_add {X : Nat} (hX : Canon 5 133 13 X) {f : Nat → Nat}
    (hf : ∀ t < 133 * 133, f t < 20) :
    Canon 5 133 13 (redP 13 L H 5 9 (X + pk 13 (133 * 133) f)) ∧
      ∀ i j : Fin 133, OM (redP 13 L H 5 9 (X + pk 13 (133 * 133) f)) i j =
        OM X i j + ((f (133 * i.val + j.val) : Nat) : ZMod 5) := by
  obtain ⟨-, -, -, -, hT, -, hL, hH, -, -, -⟩ := consts_facts hc
  have hXe := pk_lane (w := 13) (n := 133 * 133) (by norm_num) hX.1
  have ha : ∀ t < 133 * 133, lane 13 X t < 5 := hX.2
  rw [hL, hH, hXe]
  generalize lane 13 X = a at ha ⊢
  rw [pk_add]
  have h12 : (2 : Nat) ^ (13 - 1) = 4096 := by norm_num
  have h10 : (5 : Nat) * 2 ^ (9 + 1) = 5120 := by norm_num
  have e : redP 13 (pk 13 (133 * 133) fun _ => 1) (pk 13 (133 * 133) fun _ => 2 ^ (13 - 1)) 5 9
      (pk 13 (133 * 133) (fun t => a t + f t)) = pk 13 (133 * 133) (fun t => (a t + f t) % 5) := by
    refine redP_pk (by norm_num) hT (fun t ht => ?_) (fun t ht => ?_)
    · have := ha t ht
      have := hf t ht
      rw [h12]
      omega
    · have := ha t ht
      have := hf t ht
      rw [h10]
      omega
  rw [e]
  refine ⟨canon_pk (fun t _ => Nat.mod_lt _ (by norm_num)) (by norm_num), fun i j => ?_⟩
  rw [hs_OM_pk (g := fun t => (a t + f t) % 5)
      (fun t _ => lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num)),
    hs_OM_pk (g := a) (fun t ht => lt_trans (ha t ht) (by norm_num))]
  simp only [ZMod.natCast_mod, Nat.cast_add]

private theorem hs_add {X Y : Nat} (hX : Canon 5 133 13 X) (hY : Canon 5 133 13 Y) :
    Canon 5 133 13 (redP 13 L H 5 9 (X + Y)) ∧ OM (redP 13 L H 5 9 (X + Y)) = OM X + OM Y := by
  have hYe := pk_lane (w := 13) (n := 133 * 133) (by norm_num) hY.1
  have hb : ∀ t < 133 * 133, lane 13 Y t < 5 := hY.2
  obtain ⟨h1, h2⟩ := hs_redP_add hc hX (f := lane 13 Y) fun t ht => by have := hb t ht; omega
  rw [← hYe] at h1 h2
  refine ⟨h1, Matrix.ext fun i j => ?_⟩
  rw [h2, Matrix.add_apply, hs_OM_lane Y]

private noncomputable def hs_eL (r0 S0 : List Nat) (k t : Nat) : Nat :=
  if t / 133 = getN 0 S0 k then lane 13 (getN 0 r0 k) (t % 133) else 0

omit hc in
private theorem hs_shl_row {v : Nat} (hv : VCanon 5 133 13 v) {s : Nat} (hs : s < 133) :
    Nat.shiftLeft v (1729 * s) =
      pk 13 (133 * 133) (fun t => if t / 133 = s then lane 13 v (t % 133) else 0) := by
  rw [shl_eq, pk_rows 13 133 _ 133, Finset.sum_eq_single s]
  · have e : v = pk 13 133 (lane 13 v) := pk_lane (by norm_num) hv.1
    conv_lhs => rw [e]
    unfold pk
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    rw [if_pos (by omega), show (133 * s + j) % 133 = j by omega, Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    ring
  · intro i _ hi
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    rw [if_neg (by omega), Nat.zero_mul]
  · intro h
    exact absurd (Finset.mem_range.2 hs) h

omit hc in
private theorem hs_eMat {r0 S0 : List Nat} (hr : ∀ i : Fin 4, VCanon 5 133 13 (getN 0 r0 i))
    (hS : ∀ k < 4, getN 0 S0 k < 133) :
    eMat r0 S0 = pk 13 (133 * 133) (fun t => hs_eL r0 S0 0 t + (hs_eL r0 S0 1 t +
      (hs_eL r0 S0 2 t + hs_eL r0 S0 3 t))) := by
  unfold eMat
  change Nat.shiftLeft (getN 0 r0 0) (1729 * getN 0 S0 0) +
    (Nat.shiftLeft (getN 0 r0 1) (1729 * getN 0 S0 1) +
      (Nat.shiftLeft (getN 0 r0 2) (1729 * getN 0 S0 2) +
        Nat.shiftLeft (getN 0 r0 3) (1729 * getN 0 S0 3))) = _
  rw [hs_shl_row (v := getN 0 r0 0) (s := getN 0 S0 0) (hr 0) (hS 0 (by norm_num)),
    hs_shl_row (v := getN 0 r0 1) (s := getN 0 S0 1) (hr 1) (hS 1 (by norm_num)),
    hs_shl_row (v := getN 0 r0 2) (s := getN 0 S0 2) (hr 2) (hS 2 (by norm_num)),
    hs_shl_row (v := getN 0 r0 3) (s := getN 0 S0 3) (hr 3) (hS 3 (by norm_num)), pk_add, pk_add,
    pk_add]
  rfl

omit hc in
private theorem hs_eL_lt {r0 S0 : List Nat} (hr : ∀ i : Fin 4, VCanon 5 133 13 (getN 0 r0 i))
    (k : Nat) (hk : k < 4) (t : Nat) : hs_eL r0 S0 k t < 5 := by
  unfold hs_eL
  split
  · exact (hr ⟨k, hk⟩).2 _ (Nat.mod_lt _ (by norm_num))
  · norm_num

private def hs_rowM (s : Nat) (r : V) : Matrix (Fin 133) (Fin 133) (ZMod 5) :=
  fun i j => if (i : Nat) = s then r j else 0

omit hc in
private theorem hs_vecMul_rowM (v r : V) {s : Nat} (hs : s < 133) :
    v ᵥ* hs_rowM s r = v ⟨s, hs⟩ • r := by
  funext j
  simp only [Matrix.vecMul, dotProduct, hs_rowM, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single ⟨s, hs⟩]
  · simp
  · intro b _ hb
    have : (b : Nat) ≠ s := fun e => hb (Fin.ext e)
    simp [this]
  · simp

omit hc in
private theorem hs_eL_cast {r0 S0 : List Nat} (k : Nat) (hk : k < 4) (i j : Fin 133) :
    ((hs_eL r0 S0 k (133 * i.val + j.val) : Nat) : ZMod 5) =
      hs_rowM (getN 0 S0 k) (rvec r0 ⟨k, hk⟩) i j := by
  unfold hs_eL hs_rowM rvec toVec
  rw [show (133 * i.val + j.val) / 133 = i.val by omega,
    show (133 * i.val + j.val) % 133 = j.val by omega]
  split_ifs <;> simp

theorem base_sound {A B Bi : Nat} (cA : Canon 5 133 13 A) (cB : Canon 5 133 13 B)
    (cBi : Canon 5 133 13 Bi) {w : List Int} {r0 S0 : List Nat} {X Y : Nat}
    (h : baseOK (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM)
      (validM 5 229957 L H) (validM 5 1729 LV HV) L H A B Bi ONE w r0 S0 X Y = true) :
    (∀ i : Fin 4, VCanon 5 133 13 (getN 0 r0 i)) ∧
      spanR r0 = Uof (OM A) (MW A B Bi (w ++ 1 :: invW w)) := by
  unfold baseOK at h
  obtain ⟨v0, h⟩ := andB_true h
  obtain ⟨v1, h⟩ := andB_true h
  obtain ⟨v2, h⟩ := andB_true h
  obtain ⟨v3, h⟩ := andB_true h
  obtain ⟨vX, h⟩ := andB_true h
  obtain ⟨vY, h⟩ := andB_true h
  obtain ⟨s01, h⟩ := andB_true h
  obtain ⟨s12, h⟩ := andB_true h
  obtain ⟨s23, h⟩ := andB_true h
  obtain ⟨s3, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  simp only [CFSG.KS.HNF26720.strictB_eq] at h
  obtain ⟨a0, h⟩ := andB_true h
  obtain ⟨a1, h⟩ := andB_true h
  obtain ⟨a2, h⟩ := andB_true h
  obtain ⟨a3, h⟩ := andB_true h
  obtain ⟨b0, h⟩ := andB_true h
  obtain ⟨b1, h⟩ := andB_true h
  obtain ⟨b2, h⟩ := andB_true h
  obtain ⟨b3, hE⟩ := andB_true h
  have hr : ∀ i : Fin 4, VCanon 5 133 13 (getN 0 r0 i) := by
    intro i
    fin_cases i
    · exact CFSG.KS.J4Hub.validV_canon hc v0
    · exact CFSG.KS.J4Hub.validV_canon hc v1
    · exact CFSG.KS.J4Hub.validV_canon hc v2
    · exact CFSG.KS.J4Hub.validV_canon hc v3
  refine ⟨hr, ?_⟩
  have cX : Canon 5 133 13 X := validM_canon (d := 133) (S := 1729) hc vX
  have cY : Canon 5 133 13 Y := validM_canon (d := 133) (S := 1729) hc vY
  obtain ⟨cONE, eONE⟩ := one_sound hc
  have eONE' : OM ONE = 1 := eONE
  obtain ⟨cA1, eA1⟩ := hs_add hc cA cONE
  obtain ⟨cβ, eβ⟩ := wprod_sound hc cA cB cBi (w ++ 1 :: invW w)
  obtain ⟨cB1, eB1⟩ := hs_add hc cβ cONE
  rw [eONE'] at eA1 eB1
  have eβ' : OM (wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE (w ++ 1 :: invW w)) =
      MW A B Bi (w ++ 1 :: invW w) := eβ
  rw [eβ'] at eB1
  have hS : ∀ k < 4, getN 0 S0 k < 133 := by
    rw [Nat.blt_eq] at s01 s12 s23 s3
    intro k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> omega
  have hz : toVec 5 133 13 0 = 0 := by
    funext j
    simp [toVec, lane_zero]
  have key : ∀ {x M : Nat}, VCanon 5 133 13 x → Canon 5 133 13 M →
      Nat.beq (vecR 5 13 1729 133 9 LV HV RM x M) 0 = true → toVec 5 133 13 x ᵥ* OM M = 0 := by
    intro x M hx hM e
    rw [← (vecR_sound hc hx hM).2, Nat.eq_of_beq_eq_true e, hz]
  have hneg : ∀ {u : V} {M : Matrix (Fin 133) (Fin 133) (ZMod 5)}, u ᵥ* (M + 1) = 0 → u ᵥ* M = -u := by
    intro u M e
    rw [Matrix.vecMul_add, Matrix.vecMul_one] at e
    exact eq_neg_of_add_eq_zero_left e
  have hrow : ∀ i : Fin 4, rvec r0 i ∈ Uof (OM A) (MW A B Bi (w ++ 1 :: invW w)) := by
    intro i
    have ha : toVec 5 133 13 (getN 0 r0 i) ᵥ* OM (addOne L H ONE A) = 0 := by
      fin_cases i
      · exact key (hr 0) cA1 a0
      · exact key (hr 1) cA1 a1
      · exact key (hr 2) cA1 a2
      · exact key (hr 3) cA1 a3
    have hb : toVec 5 133 13 (getN 0 r0 i) ᵥ*
        OM (addOne L H ONE (wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE (w ++ 1 :: invW w))) =
        0 := by
      fin_cases i
      · exact key (hr 0) cB1 b0
      · exact key (hr 1) cB1 b1
      · exact key (hr 2) cB1 b2
      · exact key (hr 3) cB1 b3
    have eA1' : OM (addOne L H ONE A) = OM A + 1 := eA1
    have eB1' : OM (addOne L H ONE (wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE
        (w ++ 1 :: invW w))) = MW A B Bi (w ++ 1 :: invW w) + 1 := eB1
    rw [eA1'] at ha
    rw [eB1'] at hb
    exact ⟨hneg ha, hneg hb⟩
  have cA1' : Canon 5 133 13 (addOne L H ONE A) := cA1
  have cB1' : Canon 5 133 13 (addOne L H ONE (wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE
    (w ++ 1 :: invW w))) := cB1
  have eA1' : OM (addOne L H ONE A) = OM A + 1 := eA1
  have eB1' : OM (addOne L H ONE (wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE
    (w ++ 1 :: invW w))) = MW A B Bi (w ++ 1 :: invW w) + 1 := eB1
  generalize addOne L H ONE A = a1' at cA1' eA1' hE
  generalize addOne L H ONE (wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE
    (w ++ 1 :: invW w)) = b1' at cB1' eB1' hE
  obtain ⟨cP, eP⟩ := mul_sound hc cA1' cX
  obtain ⟨cQ, eQ⟩ := mul_sound hc cB1' cY
  obtain ⟨cZ, eZ⟩ := hs_add hc cP cQ
  have hf : ∀ t < 133 * 133, hs_eL r0 S0 0 t + (hs_eL r0 S0 1 t +
      (hs_eL r0 S0 2 t + hs_eL r0 S0 3 t)) < 20 := fun t _ => by
    have := hs_eL_lt (S0 := S0) hr 0 (by norm_num) t
    have := hs_eL_lt (S0 := S0) hr 1 (by norm_num) t
    have := hs_eL_lt (S0 := S0) hr 2 (by norm_num) t
    have := hs_eL_lt (S0 := S0) hr 3 (by norm_num) t
    omega
  obtain ⟨-, eF⟩ := hs_redP_add hc cZ hf
  have hE' := Nat.eq_of_beq_eq_true hE
  change redP 13 L H 5 9 (redP 13 L H 5 9 (mulR 5 13 1729 133 9 L H CM RM a1' X +
    mulR 5 13 1729 133 9 L H CM RM b1' Y) + eMat r0 S0) = ONE at hE'
  rw [hs_eMat hr hS] at hE'
  rw [hE'] at eF
  have hid : OM a1' * OM X + OM b1' * OM Y +
      (hs_rowM (getN 0 S0 0) (rvec r0 ⟨0, by norm_num⟩) +
        (hs_rowM (getN 0 S0 1) (rvec r0 ⟨1, by norm_num⟩) +
        (hs_rowM (getN 0 S0 2) (rvec r0 ⟨2, by norm_num⟩) +
          hs_rowM (getN 0 S0 3) (rvec r0 ⟨3, by norm_num⟩)))) = 1 := by
    rw [← eONE', ← eP, ← eQ, ← eZ]
    funext i j
    rw [eF i j, Matrix.add_apply, Matrix.add_apply, Matrix.add_apply, Matrix.add_apply]
    push_cast
    rw [hs_eL_cast 0 (by norm_num), hs_eL_cast 1 (by norm_num), hs_eL_cast 2 (by norm_num),
      hs_eL_cast 3 (by norm_num)]
    rfl
  refine le_antisymm (Submodule.span_le.2 (Set.range_subset_iff.2 hrow)) fun v hv => ?_
  obtain ⟨hvA, hvB⟩ := hv
  have e1 : v ᵥ* OM a1' = 0 := by
    rw [eA1', Matrix.vecMul_add, Matrix.vecMul_one, hvA, neg_add_cancel]
  have e2 : v ᵥ* OM b1' = 0 := by
    rw [eB1', Matrix.vecMul_add, Matrix.vecMul_one, hvB, neg_add_cancel]
  have hv1 : v = v ᵥ* (1 : Matrix (Fin 133) (Fin 133) (ZMod 5)) := (Matrix.vecMul_one v).symm
  rw [← hid, Matrix.vecMul_add, Matrix.vecMul_add, ← Matrix.vecMul_vecMul,
    ← Matrix.vecMul_vecMul, e1, e2, Matrix.zero_vecMul, Matrix.zero_vecMul, zero_add, zero_add,
    Matrix.vecMul_add, Matrix.vecMul_add, Matrix.vecMul_add, hs_vecMul_rowM _ _ (hS 0 (by norm_num)),
    hs_vecMul_rowM _ _ (hS 1 (by norm_num)), hs_vecMul_rowM _ _ (hS 2 (by norm_num)),
    hs_vecMul_rowM _ _ (hS 3 (by norm_num))] at hv1
  rw [hv1]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
      (Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨3, rfl⟩))))

theorem fibU_sound {A B Bi : Nat} (cA : Canon 5 133 13 A) (cB : Canon 5 133 13 B)
    (cBi : Canon 5 133 13 Bi) {w1 w2 w : List Int} {r0 : List Nat} {us ts : List (List Nat)}
    {u N : Nat} {t : List (Nat × Nat)} {ord : List Nat}
    (h : fibU (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM)
      (validM 5 1729 LV HV) A B Bi ONE w1 w2 w r0 us ts u N t ord = true)
    (hr0 : ∀ i : Fin 4, VCanon 5 133 13 (getN 0 r0 i)) :
    OM A * MW A B Bi w1 = MW A B Bi w1 * OM A ∧ OM A * MW A B Bi w2 = MW A B Bi w2 * OM A ∧
      (∀ s ∈ us, ∀ l ∈ decW s, Valid3 l) ∧
      (∀ s ∈ us, spanR r0 ≤ (spanR r0).map (Matrix.vecMulLinear (MS A B Bi w1 w2 (decW s)))) ∧
      ∀ {G : Type} [Group G] [Finite G] (ρ : G →* Matrix (Fin 133) (Fin 133) (ZMod 5))
        (K : Subgroup G) (β : G), ρ β = MW A B Bi (w ++ 1 :: invW w) →
        (∀ s ∈ us, ∃ k ∈ K, ρ k = MS A B Bi w1 w2 (decW s) ∧
          ρ k⁻¹ = MS A B Bi w1 w2 (invW (decW s))) →
        N ≤ (conjS K β).ncard := by
  unfold fibU at h
  obtain ⟨hus, h⟩ := andB_true h
  have vus : ∀ s ∈ us, ∀ l ∈ decW s, Valid3 l := fun s hs => okW_sound s (okWs_sound us hus s hs)
  simp only [CFSG.KS.HNF26720.strictB_eq] at h
  obtain ⟨c1, e1⟩ := wprod_sound hc cA cB cBi w1
  obtain ⟨c1i, e1i⟩ := wprod_sound hc cA cB cBi (invW w1)
  obtain ⟨c2, e2⟩ := wprod_sound hc cA cB cBi w2
  obtain ⟨c2i, e2i⟩ := wprod_sound hc cA cB cBi (invW w2)
  obtain ⟨cbi, ebi⟩ := wprod_sound hc cA cB cBi (w ++ 1 :: invW w)
  obtain ⟨cONE, eONE⟩ := one_sound hc
  generalize wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE w1 = g1 at c1 e1 h
  generalize wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE (invW w1) = g1i at c1i e1i h
  generalize wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE w2 = g2 at c2 e2 h
  generalize wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE (invW w2) = g2i at c2i e2i h
  generalize wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE (w ++ 1 :: invW w) = bi
    at cbi ebi h
  have ebi' : OM bi = MW A B Bi (w ++ 1 :: invW w) := ebi
  have hS : ∀ w : List Int, (∀ l ∈ w, Valid3 l) →
      Canon 5 133 13 (wgoR (mulR 5 13 1729 133 9 L H CM RM) (ltr3 A g1 g1i g2 g2i) w ONE) ∧
        OM (wgoR (mulR 5 13 1729 133 9 L H CM RM) (ltr3 A g1 g1i g2 g2i) w ONE) =
          MS A B Bi w1 w2 w := by
    intro w hw
    obtain ⟨cs, es⟩ := wgoR_sound hc w (fun l hl => ltr3_canon cA c1 c1i c2 c2i (hw l hl)) ONE cONE
    refine ⟨cs, ?_⟩
    rw [es]
    change ordMat 5 133 13 1729 ONE * _ = _
    rw [eONE, one_mul, MS]
    congr 1
    refine List.map_congr_left fun l hl => ?_
    rw [ltr3_map OM A g1 g1i g2 g2i (hw l hl), e1, e1i, e2, e2i]
    rfl
  have meq : ∀ X Y Z V : Nat, Canon 5 133 13 X → Canon 5 133 13 Y → Canon 5 133 13 Z →
      Canon 5 133 13 V →
      Nat.beq (mulR 5 13 1729 133 9 L H CM RM X Y) (mulR 5 13 1729 133 9 L H CM RM Z V) = true →
      OM X * OM Y = OM Z * OM V := by
    intro X Y Z V cX cY cZ cV hb
    rw [← (mul_sound hc cX cY).2, ← (mul_sound hc cZ cV).2]
    exact congrArg OM (Nat.eq_of_beq_eq_true hb)
  obtain ⟨hA1, h⟩ := andB_true h
  obtain ⟨hA2, h⟩ := andB_true h
  simp only [regs_eq] at h
  obtain ⟨hst, h⟩ := andB_true h
  obtain ⟨hu, h⟩ := andB_true h
  obtain ⟨hN, h⟩ := andB_true h
  refine ⟨?_, ?_, vus, ?_, ?_⟩
  · have := meq A g1 g1 A cA c1 c1 cA hA1
    rwa [e1] at this
  · have := meq A g2 g2 A cA c2 c2 cA hA2
    rwa [e2] at this
  · intro s hs
    have hst' := stabOK_sound hc hr0 _ ts (fun p hp => by
      obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hp
      exact (hS (decW s') (vus s' hs')).1) hst _ (List.mem_map.2 ⟨s, hs, rfl⟩)
    dsimp only at hst'
    rw [(hS (decW s) (vus s hs)).2] at hst'
    exact hst'
  · intro G _ _ ρ K β eβ hK
    have cu : VCanon 5 133 13 u := CFSG.KS.J4Hub.validV_canon hc hu
    have hPb : Canon 5 133 13 bi ∧ ∃ k ∈ K, OM bi = ρ (k * β * k⁻¹) :=
      ⟨cbi, 1, K.one_mem, by rw [ebi', ← eβ, one_mul, inv_one, mul_one]⟩
    have hQd : Canon 5 133 13 ONE ∧ Canon 5 133 13 ONE ∧ ∃ k ∈ K, OM ONE = ρ k ∧ OM ONE = ρ k⁻¹ := by
      refine ⟨cONE, cONE, 1, K.one_mem, ?_, ?_⟩
      · change ordMat 5 133 13 1729 ONE = _
        rw [eONE, map_one]
      · change ordMat 5 133 13 1729 ONE = _
        rw [eONE, inv_one, map_one]
    have hQL : ∀ p ∈ us.map (fun s => (wgoR (mulR 5 13 1729 133 9 L H CM RM)
        (ltr3 A g1 g1i g2 g2i) (decW s) ONE, wgoR (mulR 5 13 1729 133 9 L H CM RM)
        (ltr3 A g1 g1i g2 g2i) (invW (decW s)) ONE)),
        Canon 5 133 13 p.1 ∧ Canon 5 133 13 p.2 ∧ ∃ k ∈ K, OM p.1 = ρ k ∧ OM p.2 = ρ k⁻¹ := by
      intro p hp
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hp
      obtain ⟨cs, es⟩ := hS (decW s) (vus s hs)
      obtain ⟨csi, esi⟩ := hS (invW (decW s)) (valid3_invW (vus s hs))
      obtain ⟨k, hk, ek, eki⟩ := hK s hs
      exact ⟨cs, csi, k, hk, es.trans ek.symm, esi.trans eki.symm⟩
    have hstep : ∀ (x : Nat) (p : Nat × Nat),
        (Canon 5 133 13 x ∧ ∃ k ∈ K, OM x = ρ (k * β * k⁻¹)) →
        (Canon 5 133 13 p.1 ∧ Canon 5 133 13 p.2 ∧ ∃ k ∈ K, OM p.1 = ρ k ∧ OM p.2 = ρ k⁻¹) →
        Canon 5 133 13 (mulR 5 13 1729 133 9 L H CM RM (mulR 5 13 1729 133 9 L H CM RM p.1 x) p.2) ∧
          ∃ k ∈ K, OM (mulR 5 13 1729 133 9 L H CM RM (mulR 5 13 1729 133 9 L H CM RM p.1 x) p.2) =
            ρ (k * β * k⁻¹) := by
      rintro x p ⟨cx, k, hk, ex⟩ ⟨cp1, cp2, s, hs, es1, es2⟩
      obtain ⟨c3, e3⟩ := mul_sound hc cp1 cx
      obtain ⟨c4, e4⟩ := mul_sound hc c3 cp2
      refine ⟨c4, s * k, K.mul_mem hs hk, ?_⟩
      rw [e4, e3, es1, es2, ex]
      simp only [map_mul, _root_.mul_inv_rev, mul_assoc]
    obtain ⟨l, hl, hk⟩ := goT_sound _ bi ONE _
      (fun x => Canon 5 133 13 x ∧ ∃ k ∈ K, OM x = ρ (k * β * k⁻¹))
      (fun p => Canon 5 133 13 p.1 ∧ Canon 5 133 13 p.2 ∧ ∃ k ∈ K, OM p.1 = ρ k ∧ OM p.2 = ρ k⁻¹)
      hPb hQd hQL hstep t [bi] _ (fun x hx => by rw [List.mem_singleton.1 hx]; exact hPb) h
    obtain ⟨-, hpw⟩ := incrV_sound _ u bi l ord 0 hk
    have hnd := hpw.imp fun hab => Nat.ne_of_lt hab
    have hcard := card_le_ncard ρ (conjS K β) u _ hnd fun x hx => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      obtain ⟨cz, k, hk, ez⟩ := getN_mem (fun x => Canon 5 133 13 x ∧ ∃ k ∈ K, OM x = ρ (k * β * k⁻¹))
        hPb l hl i
      obtain ⟨c5, e5⟩ := vecR_sound hc cu cz
      exact ⟨c5, k * β * k⁻¹, ⟨k, hk, rfl⟩, by rw [e5]; exact congrArg _ ez⟩
    rw [List.length_map, Nat.eq_of_beq_eq_true hN] at hcard
    exact hcard

end Sound

@[expose] def stabU {G : Type} [Group G] (ρ : G →* Matrix (Fin 133) (Fin 133) (ZMod 5))
    (U : Submodule (ZMod 5) V) : Subgroup G where
  carrier := {k | U.comap (Matrix.vecMulLinear (ρ k)) = U}
  mul_mem' := by
    intro a b ha hb
    change U.comap (Matrix.vecMulLinear (ρ (a * b))) = U
    have e : Matrix.vecMulLinear (ρ (a * b)) =
        (Matrix.vecMulLinear (ρ b)).comp (Matrix.vecMulLinear (ρ a)) :=
      LinearMap.ext fun v => by
        simp only [LinearMap.comp_apply, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, map_mul]
    change U.comap (Matrix.vecMulLinear (ρ a)) = U at ha
    change U.comap (Matrix.vecMulLinear (ρ b)) = U at hb
    rw [e, Submodule.comap_comp, hb, ha]
  one_mem' := by
    change U.comap (Matrix.vecMulLinear (ρ 1)) = U
    ext v
    simp
  inv_mem' := by
    intro a ha
    change U.comap (Matrix.vecMulLinear (ρ a)) = U at ha
    change U.comap (Matrix.vecMulLinear (ρ a⁻¹)) = U
    have hx : ∀ x : V, x ᵥ* ρ a ∈ U ↔ x ∈ U := fun x => by
      rw [← Matrix.vecMulLinear_apply, ← Submodule.mem_comap, ha]
    ext v
    rw [Submodule.mem_comap, Matrix.vecMulLinear_apply, ← hx]
    have e : v ᵥ* ρ a⁻¹ ᵥ* ρ a = v := by
      rw [Matrix.vecMul_vecMul, ← map_mul, inv_mul_cancel, map_one, Matrix.vecMul_one]
    rw [e]

theorem sub_bound {G : Type} [Group G] [Finite G] (ρ : G →* Matrix (Fin 133) (Fin 133) (ZMod 5))
    (C : Subgroup G) (a β : G) (hCa : ∀ c ∈ C, ρ c * ρ a = ρ a * ρ c) {r0 : List Nat}
    (hU : spanR r0 = Uof (ρ a) (ρ β)) {G0 G1 : Matrix (Fin 133) (Fin 133) (ZMod 5)}
    (hG0 : ∃ c ∈ C, ρ c = G0) (hG1 : ∃ c ∈ C, ρ c = G1) {cols : List (List Nat)}
    {l : List Nat} {M N : Nat} (hnd : l.Nodup) (hlen : l.length = M)
    (hkeys : ∀ Q : Set (Submodule (ZMod 5) V), spanR r0 ∈ Q →
      (∀ W ∈ Q, W.map (Matrix.vecMulLinear G0) ∈ Q ∧ W.map (Matrix.vecMulLinear G1) ∈ Q) →
      ∀ k ∈ l, KeyReal cols Q k)
    {us : List (List Nat)} (MSf MSi : List Nat → Matrix (Fin 133) (Fin 133) (ZMod 5))
    (hus : ∀ s ∈ us, ∃ c ∈ C, ρ c = MSf s ∧ ρ c⁻¹ = MSi s)
    (hfix : ∀ s ∈ us, spanR r0 ≤ (spanR r0).map (Matrix.vecMulLinear (MSf s)))
    (hN : ∀ K : Subgroup G, (∀ s ∈ us, ∃ k ∈ K, ρ k = MSf s ∧ ρ k⁻¹ = MSi s) →
      N ≤ (conjS K β).ncard) :
    M * N ≤ (conjS C β).ncard := by
  classical
  let φ : G → Submodule (ZMod 5) V := fun z => Uof (ρ a) (ρ z)
  have hinv : ∀ c : G, ρ c * ρ c⁻¹ = 1 ∧ ρ c⁻¹ * ρ c = 1 := fun c =>
    ⟨by rw [← map_mul, mul_inv_cancel, map_one], by rw [← map_mul, inv_mul_cancel, map_one]⟩
  have hφ : ∀ c ∈ C, ∀ z, φ (c * z * c⁻¹) = (φ z).comap (Matrix.vecMulLinear (ρ c)) := by
    intro c hc z
    change Uof (ρ a) (ρ (c * z * c⁻¹)) = _
    rw [map_mul, map_mul]
    exact Uof_conj (hinv c).1 (hinv c).2 (hCa c hc)
  have hmap : ∀ c ∈ C, ∀ z, (φ z).map (Matrix.vecMulLinear (ρ c)) = φ (c⁻¹ * z * c⁻¹⁻¹) := by
    intro c hc z
    rw [hφ c⁻¹ (C.inv_mem hc) z, map_eq_comap (hinv c).1 (hinv c).2]
  have hM : M ≤ (φ '' conjS C β).ncard := by
    rw [← hlen]
    refine card_le_keys cols _ ((Set.toFinite _).image φ) l hnd (hkeys _ ?_ ?_)
    · refine ⟨β, ⟨1, C.one_mem, by group⟩, ?_⟩
      exact hU.symm
    · rintro W ⟨z, ⟨d, hd, rfl⟩, rfl⟩
      obtain ⟨c0, hc0, e0⟩ := hG0
      obtain ⟨c1, hc1, e1⟩ := hG1
      refine ⟨?_, ?_⟩
      · rw [← e0, hmap c0 hc0]
        exact ⟨_, ⟨c0⁻¹ * d, C.mul_mem (C.inv_mem hc0) hd, by group⟩, rfl⟩
      · rw [← e1, hmap c1 hc1]
        exact ⟨_, ⟨c1⁻¹ * d, C.mul_mem (C.inv_mem hc1) hd, by group⟩, rfl⟩
  let K : Subgroup G := C ⊓ stabU ρ (φ β)
  have hKφ : ∀ k ∈ K, φ (k * β * k⁻¹) = φ β := by
    intro k hk
    rw [hφ k (Subgroup.mem_inf.1 hk).1]
    exact (Subgroup.mem_inf.1 hk).2
  have hKN : N ≤ (conjS K β).ncard := by
    refine hN K fun s hs => ?_
    obtain ⟨c, hc, ec, eci⟩ := hus s hs
    refine ⟨c, Subgroup.mem_inf.2 ⟨hc, ?_⟩, ec, eci⟩
    change (φ β).comap (Matrix.vecMulLinear (ρ c)) = φ β
    have hle := hfix s hs
    rw [← ec, hU] at hle
    have hcard : ((φ β).map (Matrix.vecMulLinear (ρ c)) : Set V).ncard ≤ (φ β : Set V).ncard := by
      rw [Submodule.map_coe]
      exact Set.ncard_image_le (Set.toFinite _)
    have heq : (φ β).map (Matrix.vecMulLinear (ρ c)) = φ β :=
      (SetLike.coe_injective (Set.eq_of_subset_of_ncard_le hle hcard (Set.toFinite _))).symm
    have hinj : Function.Injective (Matrix.vecMulLinear (ρ c)) := fun x y hxy =>
      vecMul_cancel (hinv c).1 (by simpa [Matrix.vecMulLinear_apply] using hxy)
    conv_lhs => rw [← heq]
    exact Submodule.comap_map_eq_of_injective hinj _
  have hfc := fib_card_map C K β φ (fun c W => W.comap (Matrix.vecMulLinear (ρ c))) hφ
    inf_le_left hKφ
  exact (Nat.mul_le_mul hM hKN).trans hfc

end CFSG.KS.HNFSub

end
