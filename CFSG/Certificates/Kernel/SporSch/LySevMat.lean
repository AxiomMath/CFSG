module

public import CFSG.Certificates.Kernel.SporSch.LyKeyLemmas
public import CFSG.Sporadic.Schreier.LyCheckSeven
import CFSG.Certificates.Kernel.Spor.OrdCanon

public section

namespace CFSG.KS.SporSch.LySvM

open CFSG.KC.Enum CFSG.KC.Ord CFSG.KS CFSG.KS.Ord CFSG.KS.SporSch.LyM CFSG.KS.SporSch.LyK
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.Ly.Native CFSG.Sporadic.He.Native

theorem mulM_ent (A B : Array (Array Nat)) {i k : Nat} (hi : i < 111) (hk : k < 111) :
    ((mulM 5 111 A B)[i]!)[k]! = (∑ j ∈ Finset.range 111, (A[i]!)[j]! * (B[j]!)[k]!) % 5 := by
  unfold mulM
  rw [ofFn_get! _ hi, ofFn_get! _ hk]
  unfold dot
  rw [fold_sum]
  refine congrArg (· % 5) (Finset.sum_congr rfl fun j hj => ?_)
  unfold col
  rw [ofFn_get! _ (Finset.mem_range.1 hj)]

theorem mulXU_ent (A : Array (Array Nat)) {i m : Nat} (hi : i < 111) (hm : m < 7) :
    ((mulXU A)[i]!)[m]! = (∑ k ∈ Finset.range 111, (A[i]!)[k]! * (uArr[k]!)[m]!) % 5 := by
  unfold mulXU
  rw [ofFn_get! _ hi, ofFn_get! _ hm]
  dsimp only
  rw [fold_sum]

theorem mulUR_ent (R : Array Nat) {i c : Nat} (hi : i < 111) (hc : c < 7) :
    ((mulUR R)[i]!)[c]! = (∑ m ∈ Finset.range 7, (uArr[i]!)[m]! * R[7 * m + c]!) % 5 := by
  unfold mulUR
  rw [ofFn_get! _ hi, ofFn_get! _ hc]
  dsimp only
  rw [fold_sum]

theorem restr_ent (A : Array (Array Nat)) {t : Nat} (ht : t < 49) :
    (restrArr A)[t]! = ((mulXU A)[t / 7]!)[t % 7]! := by
  unfold restrArr
  rw [ofFn_get! _ ht]

@[expose] def IsPad (PU : Array (Array Nat)) : Prop :=
  ∀ i < 111, ∀ j < 111, (PU[i]!)[j]! = if j < 7 then (uArr[i]!)[j]! else 0

theorem unpack_ent {w S X : Nat} {i j : Nat} (hi : i < 111) (hj : j < 111) :
    ((unpackL 111 w S X)[i]!)[j]! = fld(X, S * i + w * j, 2 ^ w - 1) := by
  unfold unpackL
  rw [ofFn_get! _ hi, ofFn_get! _ hj]

theorem mulPad_ent {PU : Array (Array Nat)} (hPU : IsPad PU) (A : Array (Array Nat)) {i j : Nat}
    (hi : i < 111) (hj : j < 111) :
    ((mulM 5 111 A PU)[i]!)[j]! = if j < 7 then ((mulXU A)[i]!)[j]! else 0 := by
  rw [mulM_ent _ _ hi hj]
  by_cases h7 : j < 7
  · rw [if_pos h7, mulXU_ent A hi h7]
    refine congrArg (· % 5) (Finset.sum_congr rfl fun k hk => ?_)
    rw [hPU k (Finset.mem_range.1 hk) j hj, if_pos h7]
  · rw [if_neg h7]
    have : ∑ k ∈ Finset.range 111, (A[i]!)[k]! * (PU[k]!)[j]! = 0 :=
      Finset.sum_eq_zero fun k hk => by rw [hPU k (Finset.mem_range.1 hk) j hj, if_neg h7, Nat.mul_zero]
    rw [this]

theorem mulXU_lt (A : Array (Array Nat)) {i m : Nat} (hi : i < 111) (hm : m < 7) :
    ((mulXU A)[i]!)[m]! < 5 := by
  rw [mulXU_ent A hi hm]
  exact Nat.mod_lt _ (by norm_num)

theorem land_lane (X b w B : Nat) :
    (X &&& (2 ^ B - 1)) / 2 ^ b % 2 ^ w = if b + w ≤ B then X / 2 ^ b % 2 ^ w else
      if B ≤ b then 0 else (X &&& (2 ^ B - 1)) / 2 ^ b % 2 ^ w := by
  split_ifs with h1 h2
  · apply Nat.eq_of_testBit_eq
    intro r
    rw [testBit_ent, testBit_ent, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    by_cases hr : r < w
    · have : r + b < B := by omega
      simp [hr, this]
    · simp [hr]
  · apply Nat.eq_of_testBit_eq
    intro r
    rw [testBit_ent, Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.zero_testBit]
    have : ¬ r + b < B := by omega
    simp [this]
  · rfl

theorem canon_of_lanes {p d w X : Nat} (hb : X < 2 ^ (w * (d * d)))
    (hl : ∀ i < d, ∀ j < d, X / 2 ^ (d * w * i + w * j) % 2 ^ w < p) : Canon p d w X := by
  refine ⟨hb, fun t ht => ?_⟩
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h
      simp at ht
    · exact h
  have hi : t / d < d := (Nat.div_lt_iff_lt_mul hd).2 ht
  have hj : t % d < d := Nat.mod_lt _ hd
  have e : w * t = d * w * (t / d) + w * (t % d) := by
    have := Nat.div_add_mod t d
    calc w * t = w * (d * (t / d) + t % d) := by rw [this]
      _ = _ := by ring
  unfold lane
  rw [e]
  exact hl _ hi _ hj

theorem placeF_lt {val sh : Nat → Nat} {w B : Nat} :
    ∀ n, (∀ p < n, val p < 2 ^ w) → (∀ p < n, sh p + w ≤ B) → placeF val sh n < 2 ^ B := by
  intro n
  induction n with
  | zero => intro _ _; unfold placeF; simp
  | succ n ih =>
    intro hv hs
    have e : placeF val sh (n + 1) = placeF val sh n ||| val n <<< sh n := by
      unfold placeF
      rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, foldr_lor, Nat.zero_or]
    rw [e]
    refine Nat.or_lt_two_pow (ih (fun p hp => hv p (by omega)) (fun p hp => hs p (by omega))) ?_
    rw [Nat.shiftLeft_eq]
    have h1 := hv n (by omega)
    have h2 := hs n (by omega)
    calc val n * 2 ^ sh n < 2 ^ w * 2 ^ sh n := Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
      _ = 2 ^ (w + sh n) := by rw [Nat.pow_add]
      _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem pm_eq {w S T L H CM RM ONE LV HV X UP : Nat}
    (hc : constsOK 5 w S 111 T L H CM RM ONE LV HV = true)
    (hX : validM 5 (111 * S) L H X = true) (hU : validM 5 (111 * S) L H UP = true) :
    unpackL 111 w S (mulR 5 w S 111 T L H CM RM X UP) =
      mulM 5 111 (unpackL 111 w S X) (unpackL 111 w S UP) :=
  (mulR_eqL hc hX hU).1.symm

theorem restr_eqL {w S T L H CM RM ONE LV HV X UP : Nat}
    (hc : constsOK 5 w S 111 T L H CM RM ONE LV HV = true)
    (hX : validM 5 (111 * S) L H X = true) (hU : validM 5 (111 * S) L H UP = true)
    (hUP : IsPad (unpackL 111 w S UP)) :
    restrArr (unpackL 111 w S X) = Array.ofFn (n := 49) fun t =>
      fld(mulR 5 w S 111 T L H CM RM X UP, S * (t.val / 7) + w * (t.val % 7), 2 ^ w - 1) := by
  unfold restrArr
  dsimp only
  refine congrArg Array.ofFn (funext fun t => ?_)
  have ht7 : t.val / 7 < 111 := by omega
  have hm7 : t.val % 7 < 7 := Nat.mod_lt _ (by norm_num)
  rw [← unpack_ent ht7 (by omega), pm_eq hc hX hU, mulPad_ent hUP _ ht7 (by omega), if_pos hm7]

theorem arr2_ext {A B : Array (Array Nat)} {n m : Nat} (hA : A.size = n) (hB : B.size = n)
    (hA' : ∀ i < n, (A[i]!).size = m) (hB' : ∀ i < n, (B[i]!).size = m) :
    A = B ↔ ∀ i < n, ∀ j < m, (A[i]!)[j]! = (B[i]!)[j]! := by
  constructor
  · rintro rfl
    intro _ _ _ _
    rfl
  · intro h
    refine Array.ext (by rw [hA, hB]) fun i h1 h2 => ?_
    have hi : i < n := by rw [← hA]; exact h1
    have e1 : A[i] = A[i]! := (getElem!_pos A i h1).symm
    have e2 : B[i] = B[i]! := (getElem!_pos B i h2).symm
    rw [e1, e2]
    refine Array.ext (by rw [hA' i hi, hB' i hi]) fun j j1 j2 => ?_
    have hj : j < m := by rw [← hA' i hi]; exact j1
    have := h i hi j hj
    rwa [getElem!_pos _ j j1, getElem!_pos _ j j2] at this

theorem unpack_size (w S X : Nat) : (unpackL 111 w S X).size = 111 ∧
    ∀ i < 111, ((unpackL 111 w S X)[i]!).size = 111 := by
  refine ⟨by simp [unpackL], fun i hi => ?_⟩
  unfold unpackL
  rw [ofFn_get! _ hi]
  simp

theorem mulXU_size (A : Array (Array Nat)) : (mulXU A).size = 111 ∧
    ∀ i < 111, ((mulXU A)[i]!).size = 7 := by
  refine ⟨by simp [mulXU], fun i hi => ?_⟩
  unfold mulXU
  rw [ofFn_get! _ hi]
  simp

theorem mulUR_size (R : Array Nat) : (mulUR R).size = 111 ∧
    ∀ i < 111, ((mulUR R)[i]!).size = 7 := by
  refine ⟨by simp [mulUR], fun i hi => ?_⟩
  unfold mulUR
  rw [ofFn_get! _ hi]
  simp

theorem mulM_size (A B : Array (Array Nat)) : (mulM 5 111 A B).size = 111 ∧
    ∀ i < 111, ((mulM 5 111 A B)[i]!).size = 111 := by
  refine ⟨by simp [mulM], fun i hi => ?_⟩
  unfold mulM
  rw [ofFn_get! _ hi]
  simp

theorem stab_facts {w S T L H CM RM ONE LV HV X UP : Nat}
    (hc : constsOK 5 w S 111 T L H CM RM ONE LV HV = true)
    (hX : validM 5 (111 * S) L H X = true) (hU : validM 5 (111 * S) L H UP = true)
    (hUP : IsPad (unpackL 111 w S UP)) :
    validM 5 (111 * S) L H (Nat.land (mulR 5 w S 111 T L H CM RM X UP) (2 ^ (7 * S) - 1)) = true ∧
    (∀ i < 111, ∀ j < 111, Nat.land (mulR 5 w S 111 T L H CM RM X UP) (2 ^ (7 * S) - 1) /
        2 ^ (S * i + w * j) % 2 ^ w =
      if i < 7 ∧ j < 7 then ((mulXU (unpackL 111 w S X))[i]!)[j]! else 0) ∧
    stabOK (unpackL 111 w S X) = Nat.beq (mulR 5 w S 111 T L H CM RM X UP)
      (mulR 5 w S 111 T L H CM RM UP
        (Nat.land (mulR 5 w S 111 T L H CM RM X UP) (2 ^ (7 * S) - 1))) := by
  obtain ⟨-, hS, hw, -⟩ := cfacts hc
  have hS' : S = 111 * w := hS
  set Pm := mulR 5 w S 111 T L H CM RM X UP with hPm
  set A := unpackL 111 w S X with hA
  have vP : validM 5 (111 * S) L H Pm = true := (mulR_eqL hc hX hU).2
  have cP := validM_canon hc vP
  have hM1 := pm_eq (T := T) (CM := CM) (RM := RM) hc hX hU
  rw [← hPm, ← hA] at hM1
  have pent : ∀ i < 111, ∀ j < 111, Pm / 2 ^ (S * i + w * j) % 2 ^ w =
      if j < 7 then ((mulXU A)[i]!)[j]! else 0 := by
    intro i hi j hj
    rw [← mulPad_ent hUP A hi hj, ← hM1, unpackL_get hi hj]
  have qent : ∀ i < 111, ∀ j < 111, Nat.land Pm (2 ^ (7 * S) - 1) / 2 ^ (S * i + w * j) % 2 ^ w =
      if i < 7 ∧ j < 7 then ((mulXU A)[i]!)[j]! else 0 := by
    intro i hi j hj
    rw [land_eq, land_lane]
    by_cases hi7 : i < 7
    · have h1 : S * i + w * j + w ≤ 7 * S := by
        rw [hS']
        have : w * j + w ≤ 111 * w := by nlinarith
        nlinarith
      rw [if_pos h1, pent i hi j hj]
      by_cases hj7 : j < 7
      · rw [if_pos hj7, if_pos ⟨hi7, hj7⟩]
      · rw [if_neg hj7, if_neg (fun h => hj7 h.2)]
    · have h1 : ¬ S * i + w * j + w ≤ 7 * S := by
        rw [hS']
        nlinarith
      have h2 : 7 * S ≤ S * i + w * j := by
        rw [hS']
        nlinarith
      rw [if_neg h1, if_pos h2, if_neg (fun h => hi7 h.1)]
  have cQ : Canon 5 111 w (Nat.land Pm (2 ^ (7 * S) - 1)) := by
    refine canon_of_lanes (Nat.lt_of_le_of_lt Nat.and_le_left cP.1) fun i hi j hj => ?_
    have e : 111 * w * i = S * i := by rw [hS']
    rw [e, qent i hi j hj]
    split_ifs with h
    · exact mulXU_lt A hi h.2
    · norm_num
  have vQ := CFSG.KS.OrdCanon.validM_of_canon hc cQ
  refine ⟨vQ, qent, ?_⟩
  have vM2 := (mulR_eqL hc hU vQ).2
  rw [← beq_eqL hc vP vM2, ← (mulR_eqL hc hU vQ).1, hM1]
  set Q := Nat.land Pm (2 ^ (7 * S) - 1)
  have q'ent : ∀ k < 111, ∀ j < 111, ((unpackL 111 w S Q)[k]!)[j]! =
      if k < 7 ∧ j < 7 then ((mulXU A)[k]!)[j]! else 0 := by
    intro k hk j hj
    rw [unpackL_get hk hj, qent k hk j hj]
  have m2ent : ∀ i < 111, ∀ j < 111,
      ((mulM 5 111 (unpackL 111 w S UP) (unpackL 111 w S Q))[i]!)[j]! =
        if j < 7 then ((mulUR (restrArr A))[i]!)[j]! else 0 := by
    intro i hi j hj
    rw [mulM_ent _ _ hi hj]
    have hsplit : ∑ k ∈ Finset.range 111, ((unpackL 111 w S UP)[i]!)[k]! *
        ((unpackL 111 w S Q)[k]!)[j]! = ∑ k ∈ Finset.range 7, (uArr[i]!)[k]! *
          (if j < 7 then ((mulXU A)[k]!)[j]! else 0) := by
      rw [← Finset.sum_subset (s₁ := Finset.range 7) (fun x hx => Finset.mem_range.2
        (by have := Finset.mem_range.1 hx; omega))]
      · refine Finset.sum_congr rfl fun k hk => ?_
        have hk7 := Finset.mem_range.1 hk
        rw [hUP i hi k (by omega), if_pos hk7, q'ent k (by omega) j hj]
        by_cases hj7 : j < 7
        · rw [if_pos ⟨hk7, hj7⟩, if_pos hj7]
        · rw [if_neg (fun h => hj7 h.2), if_neg hj7]
      · intro k hk hk'
        have hk7 : ¬ k < 7 := fun h => hk' (Finset.mem_range.2 h)
        rw [hUP i hi k (Finset.mem_range.1 hk), if_neg hk7, Nat.zero_mul]
    rw [hsplit]
    by_cases hj7 : j < 7
    · rw [if_pos hj7, mulUR_ent _ hi hj7]
      simp only [if_pos hj7]
      refine congrArg (· % 5) (Finset.sum_congr rfl fun k hk => ?_)
      have hk7 := Finset.mem_range.1 hk
      rw [restr_ent A (by omega)]
      have e1 : (7 * k + j) / 7 = k := by omega
      have e2 : (7 * k + j) % 7 = j := by omega
      rw [e1, e2]
    · rw [if_neg hj7]
      simp only [if_neg hj7, Nat.mul_zero, Finset.sum_const_zero, Nat.zero_mod]
  unfold stabOK
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  rw [arr2_ext (mulXU_size A).1 (mulUR_size _).1 (mulXU_size A).2 (mulUR_size _).2,
    arr2_ext (mulM_size _ _).1 (mulM_size _ _).1 (mulM_size _ _).2 (mulM_size _ _).2]
  constructor
  · intro h i hi j hj
    rw [mulPad_ent hUP A hi hj, m2ent i hi j hj]
    split_ifs with hj7
    · exact h i hi j hj7
    · rfl
  · intro h i hi j hj
    have := h i hi j (by omega)
    rwa [mulPad_ent hUP A hi (by omega), m2ent i hi j (by omega), if_pos hj, if_pos hj] at this

theorem stab_eqL {w S T L H CM RM ONE LV HV X UP : Nat}
    (hc : constsOK 5 w S 111 T L H CM RM ONE LV HV = true)
    (hX : validM 5 (111 * S) L H X = true) (hU : validM 5 (111 * S) L H UP = true)
    (hUP : IsPad (unpackL 111 w S UP)) :
    stabOK (unpackL 111 w S X) = Nat.beq (mulR 5 w S 111 T L H CM RM X UP)
      (mulR 5 w S 111 T L H CM RM UP (Nat.land (mulR 5 w S 111 T L H CM RM X UP) (2 ^ (7 * S) - 1))) :=
  (stab_facts hc hX hU hUP).2.2

@[expose] noncomputable def packK (K : ByteArray) : Nat :=
  placeF (fun p => keyDigit K p) (fun p => 4 * p) 826

theorem keyDigit_lt (K : ByteArray) (p : Nat) : keyDigit K p < 5 := by
  unfold keyDigit
  exact Nat.mod_lt _ (by norm_num)

theorem packK_fld (K : ByteArray) {p : Nat} (hp : p < 826) :
    fld(packK K, 4 * p, 15) = keyDigit K p := by
  have hspec := placeF_spec (d := 826) (w := 4) (S := 4 * 826) (N := 826) (by omega)
    (pl := fun p => p) (val := fun p => keyDigit K p) (sh := fun p => 4 * p)
    (fun p hp => by omega) (fun p hp q hq h => h)
    (fun p _ => Nat.lt_of_lt_of_le (keyDigit_lt K p) (by norm_num))
    (fun p hp => by rw [Nat.div_eq_of_lt hp, Nat.mod_eq_of_lt hp]; omega) 826 le_rfl
  have e := hspec.1 p hp
  unfold entL at e
  rw [Nat.div_eq_of_lt hp, Nat.mod_eq_of_lt hp, Nat.mul_zero, Nat.zero_add] at e
  rw [land_eq, (by rfl : (15 : Nat) = 2 ^ 4 - 1), Nat.and_two_pow_sub_one_eq_mod]
  change packK K >>> (4 * p) % 2 ^ 4 = _
  rw [Nat.shiftRight_eq_div_pow]
  exact e

theorem bytes_ext {a b : ByteArray} (hs : a.size = b.size) (h : ∀ q < a.size, a.get! q = b.get! q) :
    a = b := by
  cases a with
  | mk a =>
    cases b with
    | mk b =>
      apply ByteArray.ext
      refine Array.ext hs fun q h1 h2 => ?_
      have := h q h1
      change a[q]! = b[q]! at this
      rwa [getElem!_pos a q h1, getElem!_pos b q h2] at this

theorem keyOfD_pack {K : ByteArray} (hs : K.size = 276) (hb : ∀ q < 276, (K.get! q).toNat < 125)
    (h826 : keyDigit K 826 = 0) (h827 : keyDigit K 827 = 0) : keyOfD (packK K) = K := by
  have hd : ∀ p < 828, dF (packK K) p = keyDigit K p := by
    intro p hp
    unfold dF
    split
    · exact packK_fld K ‹_›
    · rcases (by omega : p = 826 ∨ p = 827) with rfl | rfl
      · exact h826.symm
      · exact h827.symm
  refine bytes_ext (by rw [keyOfD_size, hs]) fun q hq => ?_
  rw [keyOfD_size] at hq
  apply UInt8.toNat_inj.1
  rw [keyOfD_get _ hq, hd _ (by omega), hd _ (by omega), hd _ (by omega)]
  unfold keyDigit
  have e0 : 3 * q / 3 = q := by omega
  have e1 : (3 * q + 1) / 3 = q := by omega
  have e2 : (3 * q + 2) / 3 = q := by omega
  have f0 : 3 * q % 3 = 0 := by omega
  have f1 : (3 * q + 1) % 3 = 1 := by omega
  have f2 : (3 * q + 2) % 3 = 2 := by omega
  rw [e0, e1, e2, f0, f1, f2]
  have hb' := hb q hq
  simp only [Nat.pow_zero, Nat.pow_one, Nat.div_one, Nat.mod_mod]
  have : (5 : Nat) ^ 2 = 25 := rfl
  rw [this]
  omega

theorem upOfD_place (w S D : Nat) : upOfD w S D = placeF (fun p => fld(D, 4 * p, 15))
    (fun p => S * (p % 111) + w * (p / 111)) 777 := by
  unfold upOfD placeF
  rw [foldN_eqL]
  rfl

theorem lane7_place (w S : Nat) (R : Array Nat) : lane7 w S R = placeF (fun t => R[t]!)
    (fun t => S * (t / 7) + w * (t % 7)) 49 := by
  unfold lane7 placeF
  rw [foldN_eqL]
  rfl

theorem actKey_fixL {w S T L H CM RM ONE LV HV X UP : Nat} {K : ByteArray}
    (hc : constsOK 5 w S 111 T L H CM RM ONE LV HV = true)
    (hX : validM 5 (111 * S) L H X = true) (hU : validM 5 (111 * S) L H UP = true)
    (hUP : IsPad (unpackL 111 w S UP))
    (hK : K.size = 276 ∧ (∀ q < 276, (K.get! q).toNat < 125) ∧
      rrefOK (keyRows K) #[0, 1, 2, 3, 4, 5, 6] = true ∧ keyDigit K 826 = 0 ∧ keyDigit K 827 = 0 ∧
      ∀ j < 111, ∀ m < 7, (uArr[j]!)[m]! = keyDigit K (111 * m + j))
    (hst : stabOK (unpackL 111 w S X) = true)
    (hR : mul7 (restrArr (unpackL 111 w S X)) (inv7 (restrArr (unpackL 111 w S X))) = id7 ())
    (hS : congr7 (restrArr (unpackL 111 w S X)) (keyS K) = keyS K) :
    actKey (frTable (unpackL 111 w S X)) K = some K := by
  obtain ⟨hK1, hK2, hK3, hK4, hK5, hK6⟩ := hK
  obtain ⟨-, hS', hw, hpw⟩ := cfacts hc
  have hS111 : S = 111 * w := hS'
  obtain ⟨D, hDdef⟩ : ∃ D, D = packK K := ⟨_, rfl⟩
  have hkey : keyOfD D = K := by rw [hDdef]; exact keyOfD_pack hK1 hK2 hK4 hK5
  have hD : ∀ p < 826, fld(D, 4 * p, 15) < 5 := fun p hp => by
    rw [hDdef, packK_fld K hp]
    exact keyDigit_lt K p
  set A := unpackL 111 w S X with hA
  set R := restrArr A with hRdef
  obtain ⟨vQ, qent, hstab⟩ := stab_facts hc hX hU hUP
  rw [← hA] at qent hstab
  set Pm := mulR 5 w S 111 T L H CM RM X UP with hPm
  set Q := Nat.land Pm (2 ^ (7 * S) - 1) with hQ
  have hRs : R.size = 49 ∧ ∀ t < 49, R[t]! < 5 := by
    refine ⟨by simp [hRdef, restrArr], fun t ht => ?_⟩
    rw [hRdef, restr_ent A ht]
    exact mulXU_lt A (by omega) (Nat.mod_lt _ (by norm_num))
  have hrent : ∀ a < 7, ∀ b < 7, R[7 * a + b]! = ((mulXU A)[a]!)[b]! := by
    intro a ha b hb
    rw [hRdef, restr_ent A (by omega)]
    have e1 : (7 * a + b) / 7 = a := by omega
    have e2 : (7 * a + b) % 7 = b := by omega
    rw [e1, e2]
  have cUP := validM_canon hc hU
  have cU' : Canon 5 111 w (upOfD w S D) := by
    refine canon_of_lanes ?_ fun i hi j hj => ?_
    · rw [upOfD_place]
      refine placeF_lt 777 (fun p hp => Nat.lt_of_lt_of_le (hD p (by omega)) hpw) fun p hp => ?_
      rw [hS111]
      have h1 : p % 111 ≤ 110 := by omega
      have h2 : p / 111 ≤ 6 := by omega
      have : 111 * w * (p % 111) ≤ 111 * w * 110 := Nat.mul_le_mul_left _ h1
      have : w * (p / 111) ≤ w * 6 := Nat.mul_le_mul_left _ h2
      linarith
    · have e : 111 * w * i = S * i := by rw [hS111]
      rw [e, upOfD_ent hS111 hpw hD hi hj]
      split_ifs
      · exact hD _ (by omega)
      · norm_num
  have hUPe : upOfD w S D = UP := by
    refine canon_ext cU' cUP fun i hi j hj => ?_
    have e : 111 * w * i = S * i := by rw [hS111]
    rw [e, upOfD_ent hS111 hpw hD hi hj, ← unpackL_get hi hj, hUP i hi j hj]
    split_ifs with h7
    · rw [hK6 i hi j h7, hDdef, packK_fld K (by omega)]
    · rfl
  have cQ := validM_canon hc vQ
  have cL : Canon 5 111 w (lane7 w S R) := by
    refine canon_of_lanes ?_ fun i hi j hj => ?_
    · rw [lane7_place]
      refine placeF_lt 49 (fun t ht => Nat.lt_of_lt_of_le (hRs.2 t ht) hpw) fun t ht => ?_
      rw [hS111]
      have h1 : t / 7 ≤ 6 := by omega
      have h2 : t % 7 ≤ 6 := by omega
      have : 111 * w * (t / 7) ≤ 111 * w * 6 := Nat.mul_le_mul_left _ h1
      have : w * (t % 7) ≤ w * 6 := Nat.mul_le_mul_left _ h2
      linarith
    · have e : 111 * w * i = S * i := by rw [hS111]
      rw [e, lane7_ent hS111 hpw hRs.2 hi hj]
      split_ifs with h
      · exact hRs.2 _ (by omega)
      · norm_num
  have hQe : Q = lane7 w S R := by
    refine canon_ext cQ cL fun i hi j hj => ?_
    have e : 111 * w * i = S * i := by rw [hS111]
    rw [e, qent i hi j hj, lane7_ent hS111 hpw hRs.2 hi hj]
    split_ifs with h
    · rw [hrent i h.1 j h.2]
    · rfl
  have hPmQ : Pm = mulR 5 w S 111 T L H CM RM UP Q := by
    rw [hstab] at hst
    exact Nat.eq_of_beq_eq_true hst
  have hst' : mulR 5 w S 111 T L H CM RM X (upOfD w S D) =
      mulR 5 w S 111 T L H CM RM (upOfD w S D) (lane7 w S R) := by
    rw [hUPe, ← hQe]
    exact hPmQ
  have vU' : validM 5 (111 * S) L H (upOfD w S D) = true := by rw [hUPe]; exact hU
  have vL : validM 5 (111 * S) L H (lane7 w S R) = true := by rw [← hQe]; exact vQ
  have h := actKey_mapL (D := D) (D' := D) (piv := #[0, 1, 2, 3, 4, 5, 6]) hc hX vU' vU' vL hD hD hRs
    (by rw [hkey]; exact hK3) hst' hR (by rw [hkey]; exact hS)
  rw [hkey] at h
  exact h

end CFSG.KS.SporSch.LySvM

end
