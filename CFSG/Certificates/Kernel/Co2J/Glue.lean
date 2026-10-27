module

public import CFSG.Certificates.Kernel.Co2J.Sound
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs
public import CFSG.Perm.ChainSpec

set_option exponentiation.threshold 600

public section

namespace CFSG.KC.Co2J

open CFSG.KC.Loop CFSG.KC.F2W CFSG.KC.Co2InvS CFSG.KC.TabMatGrp CFSG.KLie.CT CFSG.KC.M1F2
  CFSG.KC.Co2Syl CFSG.KC.Co1F2 CFSG.Sporadic.SmallF2.Native
open CFSG.Sporadic.SmallF2 (rowsMatrix rowsMatrix_apply toVecD_apply)

local notation "M22" => Matrix (Fin 22) (Fin 22) (ZMod 2)
local notation "M10" => Matrix (Fin 10) (Fin 10) (ZMod 2)

@[expose] def bv (v : ℕ) : Fin 10 → ZMod 2 := fun i => if v.testBit i.val then 1 else 0

theorem bv_inj {a b : ℕ} (ha : a < 1024) (hb : b < 1024) (h : bv a = bv b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 10
  · have e := congrFun h ⟨j, hj⟩
    simp only [bv] at e
    cases ha' : a.testBit j <;> cases hb' : b.testBit j <;> simp_all
  · have h2 : (1024 : ℕ) ≤ 2 ^ j := by
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.not_lt.1 hj)
      simpa using this
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha h2),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb h2)]

theorem bv_xor (a b : ℕ) : bv (a ^^^ b) = bv a + bv b := by
  funext i
  simp only [bv, Nat.testBit_xor, Pi.add_apply]
  cases a.testBit i.val <;> cases b.testBit i.val <;> decide

theorem bv_zero : bv 0 = 0 := by
  funext i
  simp [bv]

theorem bv_two_pow_add {l u : ℕ} (hu : u < 2 ^ l) : bv (2 ^ l + u) = bv (2 ^ l) + bv u := by
  funext j
  simp only [bv, Pi.add_apply, Nat.testBit_two_pow]
  rcases lt_trichotomy j.val l with h | h | h
  · rw [Nat.testBit_two_pow_add_gt h u, decide_eq_false (Nat.ne_of_gt h)]
    simp
  · subst h
    rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hu]
    simp
  · have h1 : 2 ^ l + u < 2 ^ j.val := by
      have : 2 ^ (l + 1) ≤ 2 ^ j.val := Nat.pow_le_pow_right (by norm_num) h
      rw [pow_succ] at this
      omega
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow (lt_trans hu (Nat.pow_lt_pow_right
      (by norm_num) h)), decide_eq_false (Nat.ne_of_lt h)]
    simp

theorem MatP10_apply (U : Nat) (i j : Fin 10) :
    MatP 10 U i j = if U.testBit (i.val * 10 + j.val) then 1 else 0 := by
  have hr : (unpackR 10 U)[i.val]?.getD 0 = rowF 10 U i.val := by
    simp [unpackR, i.isLt, rowF_eq]
  unfold MatP
  rw [rowsMatrix_apply, hr, toVecD_apply, testBit_rowF 10 _ _ _ j.isLt]

theorem recXor_eq (c : ℕ → Bool) : ∀ n,
    (if (Nat.rec (motive := fun _ => Bool) false (fun k b => c k ^^ b) n : Bool) = true then
      (1 : ZMod 2) else 0) = ∑ k ∈ Finset.range n, if c k = true then 1 else 0
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, ← recXor_eq c n]
    change (if (c n ^^ (Nat.rec (motive := fun _ => Bool) false (fun k b => c k ^^ b) n : Bool))
      = true then (1 : ZMod 2) else 0) = _
    generalize (Nat.rec (motive := fun _ => Bool) false (fun k b => c k ^^ b) n : Bool) = b
    cases c n <;> cases b <;> decide

theorem bv_vmF (P v : ℕ) : bv (vmF 10 P v) = Matrix.vecMul (bv v) (MatP 10 P) := by
  funext j
  change (if (vmF 10 P v).testBit j.val then (1 : ZMod 2) else 0) = _
  rw [testBit_vmF 10 P v j.val j.isLt, recXor_eq, Matrix.vecMul, dotProduct,
    ← Fin.sum_univ_eq_sum_range (fun k => if (v.testBit k && P.testBit (k * 10 + j.val)) = true
      then (1 : ZMod 2) else 0) 10]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [MatP10_apply]
  simp only [bv]
  cases v.testBit k.val <;> cases P.testBit (k.val * 10 + j.val) <;> decide

theorem bv_rowT (M : ℕ) (i : Fin 10) : bv (rowT M i.val) = MatP 10 M i := by
  funext j
  rw [MatP10_apply]
  change (if ((M >>> (10 * i.val)) &&& 1023).testBit j.val = true then (1 : ZMod 2) else 0) = _
  have e : (1023 : ℕ) = 2 ^ 10 - 1 := by norm_num
  rw [Nat.testBit_and, Nat.testBit_shiftRight, e, Nat.testBit_two_pow_sub_one,
    decide_eq_true j.isLt, Bool.and_true, Nat.mul_comm 10 i.val]

theorem bv_two_pow_vecMul (i : Fin 10) (X : M10) : Matrix.vecMul (bv (2 ^ i.val)) X = X i := by
  funext j
  rw [Matrix.vecMul, dotProduct, Finset.sum_eq_single i]
  · simp [bv, Nat.testBit_two_pow]
  · intro k _ hk
    have : i.val ≠ k.val := fun e => hk (Fin.ext e).symm
    simp [bv, Nat.testBit_two_pow, this]
  · simp

theorem vmF_lt' (P v : ℕ) : vmF 10 P v < 1024 := vmF_lt 10 P v

theorem vmF_congr {P P' : ℕ} (h : MatP 10 P = MatP 10 P') (v : ℕ) : vmF 10 P v = vmF 10 P' v :=
  bv_inj (vmF_lt' _ _) (vmF_lt' _ _) (by rw [bv_vmF, bv_vmF, h])

theorem vmF_mulT (A B v : ℕ) : vmF 10 (mulT A B) v = vmF 10 B (vmF 10 A v) :=
  bv_inj (vmF_lt' _ _) (vmF_lt' _ _) (by
    rw [bv_vmF, bv_vmF, bv_vmF, MatP_mulT, Matrix.vecMul_vecMul])

theorem vmF_IDT {v : ℕ} (hv : v < 1024) : vmF 10 IDT v = v :=
  bv_inj (vmF_lt' _ _) hv (by rw [bv_vmF, MatP_IDT, Matrix.vecMul_one])

theorem vmF_zero' (P : ℕ) : vmF 10 P 0 = 0 :=
  bv_inj (vmF_lt' _ _) (by norm_num) (by rw [bv_vmF, bv_zero, Matrix.zero_vecMul])

theorem vmF_gray (P : ℕ) {l u : ℕ} (hl : l < 10) (hu : u < 2 ^ l) :
    vmF 10 P (2 ^ l + u) = rowT P l ^^^ vmF 10 P u :=
  bv_inj (vmF_lt' _ _) (Nat.xor_lt_two_pow (n := 10) (rowT_lt P l) (vmF_lt' P u)) (by
    rw [bv_vmF, bv_two_pow_add hu, Matrix.add_vecMul, bv_xor, bv_vmF,
      bv_two_pow_vecMul ⟨l, hl⟩, bv_rowT P ⟨l, hl⟩])

theorem MatP_eq_of_vmF {P P' : ℕ} (h : ∀ v < 1024, vmF 10 P v = vmF 10 P' v) :
    MatP 10 P = MatP 10 P' := by
  funext i
  have hi : 2 ^ i.val < 1024 := by
    have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) i.isLt
    simpa using this
  have e := congrArg bv (h _ hi)
  rw [bv_vmF, bv_vmF, bv_two_pow_vecMul, bv_two_pow_vecMul] at e
  exact e

section Bits

variable {g : ℕ → M22}

theorem comm_bitProd {x : M22} : ∀ n, (∀ i < n, x * g i = g i * x) → ∀ v,
    x * bitProd g n v = bitProd g n v * x
  | 0, _, _ => by simp [bitProd]
  | n + 1, h, v => by
    simp only [bitProd]
    have hn : x * (if v.testBit n then g n else 1) = (if v.testBit n then g n else 1) * x := by
      split
      · exact h n (by omega)
      · rw [one_mul, mul_one]
    rw [← mul_assoc, comm_bitProd n (fun i hi => h i (by omega)) v, mul_assoc, hn, mul_assoc]

theorem bitProd_xor (hsq : ∀ i < 10, g i * g i = 1)
    (hcomm : ∀ i < 10, ∀ k < 10, g i * g k = g k * g i) (a b : ℕ) :
    ∀ n ≤ 10, bitProd g n (a ^^^ b) = bitProd g n a * bitProd g n b
  | 0, _ => by simp [bitProd]
  | n + 1, hn => by
    simp only [bitProd]
    rw [bitProd_xor hsq hcomm a b n (by omega), Nat.testBit_xor]
    have hc : ∀ (c : Bool), (if c = true then g n else 1) * bitProd g n b =
        bitProd g n b * (if c = true then g n else 1) := fun c => by
      split
      · exact comm_bitProd n (fun i hi => hcomm n (by omega) i (by omega)) b
      · rw [one_mul, mul_one]
    rw [mul_assoc (bitProd g n a) (if a.testBit n = true then g n else 1), ← mul_assoc _ _
      (if b.testBit n = true then g n else 1), hc, mul_assoc, mul_assoc]
    have key : (if (a.testBit n ^^ b.testBit n) = true then g n else 1) =
        (if a.testBit n = true then g n else 1) * (if b.testBit n = true then g n else 1) := by
      cases a.testBit n <;> cases b.testBit n <;> simp [hsq n (by omega)]
    rw [key]

end Bits

@[expose] noncomputable def genJ (GJ : Nat → Nat) : Submonoid M22 :=
  Submonoid.closure (Set.range fun i : Fin 10 => MatP 22 (GJ i))

@[expose] def ActsP (jm : ℕ → M22) (t : M22) (P : ℕ) : Prop :=
  ∀ v < 1024, t * jm v = jm (vmF 10 P v) * t

section Facts

variable {G GJ JE JS JW JL MK : Nat → Nat} {PE PM PS : Nat → Nat} {PT : Nat → Nat → Nat}

local notation "jm" => bitProd (fun i => MatP 22 (GJ i)) 10

theorem acts_one : ActsP jm 1 IDT := fun v hv => by rw [vmF_IDT hv, one_mul, mul_one]

theorem acts_mul {t₁ t₂ : M22} {P₁ P₂ : ℕ} (h₁ : ActsP jm t₁ P₁) (h₂ : ActsP jm t₂ P₂) :
    ActsP jm (t₂ * t₁) (mulT P₁ P₂) := fun v hv => by
  rw [mul_assoc, h₁ v hv, ← mul_assoc, h₂ _ (vmF_lt' _ _), vmF_mulT, mul_assoc]

theorem acts_congr {t : M22} {P P' : ℕ} (e : MatP 10 P = MatP 10 P') (h : ActsP jm t P) :
    ActsP jm t P' := fun v hv => by rw [← vmF_congr e, h v hv]

theorem cancel_right {t x y : M22} (ht : t ^ 32 = 1) (h : x * t = y * t) : x = y := by
  have e : t * t ^ 31 = 1 := by rw [← pow_succ', ht]
  calc x = x * t * t ^ 31 := by rw [mul_assoc, e, mul_one]
    _ = y := by rw [h, mul_assoc, e, mul_one]

theorem cancel_left {t x y : M22} (ht : t ^ 32 = 1) (h : t * x = t * y) : x = y := by
  have e : t ^ 31 * t = 1 := by rw [← pow_succ, ht]
  calc x = t ^ 31 * t * x := by rw [e, one_mul]
    _ = y := by rw [mul_assoc, h, ← mul_assoc, e, one_mul]

variable (hgen : jGenK GJ = true) (henum : jEnumK GJ JE JS = true)

include hgen henum in
theorem jm_xor {a b : ℕ} : jm (a ^^^ b) = jm a * jm b :=
  bitProd_xor (jGen_sound hgen).1 (jGen_sound hgen).2 a b 10 le_rfl

include hgen henum in
theorem jm_bij : Set.BijOn jm (Set.Iio 1024) (genJ GJ) := by
  refine ⟨fun v _ => ?_, fun a ha b hb e => (jEnum_sound henum).2 a ha b hb ?_, ?_⟩
  · have key : ∀ n ≤ 10, bitProd (fun i => MatP 22 (GJ i)) n v ∈ genJ GJ := by
      intro n
      induction n with
      | zero => intro _; exact (genJ GJ).one_mem
      | succ n ih =>
        intro hn
        simp only [bitProd]
        refine (genJ GJ).mul_mem (ih (by omega)) ?_
        split
        · exact Submonoid.subset_closure ⟨⟨n, by omega⟩, rfl⟩
        · exact (genJ GJ).one_mem
    exact key 10 le_rfl
  · rw [((jEnum_sound henum).1 a ha).2, ((jEnum_sound henum).1 b hb).2]
    exact e
  · intro x hx
    change x ∈ (genJ GJ : Set M22) at hx
    unfold genJ at hx
    induction hx using Submonoid.closure_induction with
    | mem y hy =>
      obtain ⟨⟨i, hi⟩, rfl⟩ := hy
      refine ⟨2 ^ i, ?_, ?_⟩
      · have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) hi
        simpa using this
      · have e := bitProd_gray (fun i => MatP 22 (GJ i)) hi (Nat.two_pow_pos i)
        rw [Nat.add_zero, bitProd_zero, one_mul] at e
        exact e
    | one => exact ⟨0, by simp, bitProd_zero _ 10⟩
    | mul y z _ _ hy hz =>
      obtain ⟨a, ha, rfl⟩ := hy
      obtain ⟨b, hb, rfl⟩ := hz
      refine ⟨a ^^^ b, ?_, jm_xor hgen henum⟩
      exact Nat.xor_lt_two_pow (n := 10) ha hb

variable (hin : jInTK G GJ JW JL = true) (hco : coordAllK G GJ JE MK = true)

include hin in
theorem genJ_le : genJ GJ ≤ genMon G := by
  unfold genJ
  rw [Submonoid.closure_le]
  rintro _ ⟨⟨i, hi⟩, rfl⟩
  exact jInT_sound hin i hi

include hgen henum hco in
theorem acts_gen {k : ℕ} (hk : k < 5) : ActsP jm (MatP 22 (G k)) (MK k) := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  intro hv
  rcases Nat.eq_zero_or_pos v with rfl | hv0
  · rw [vmF_zero', bitProd_zero, one_mul, mul_one]
  have hl1 : 2 ^ v.log2 ≤ v := Nat.log2_self_le (by omega)
  have hl2 : v < 2 ^ (v.log2 + 1) := Nat.lt_log2_self
  have hi : v.log2 < 10 := by
    by_contra hc
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.not_lt.1 hc)
    omega
  have hu : v - 2 ^ v.log2 < 2 ^ v.log2 := by rw [pow_succ] at hl2; omega
  have e2 : v = 2 ^ v.log2 + (v - 2 ^ v.log2) := by omega
  generalize v - 2 ^ v.log2 = u at hu e2
  generalize v.log2 = l at hi hu e2
  subst e2
  have hc := coord_sound hco k hk l hi
  rw [((jEnum_sound henum).1 _ (rowT_lt _ _)).2] at hc
  rw [bitProd_gray _ hi hu, vmF_gray _ hi hu, ← mul_assoc, ih u (by omega) (by omega), mul_assoc,
    hc, ← mul_assoc, ← jm_xor hgen henum, Nat.xor_comm]

variable (hpow : ∀ x ∈ genMon G, x ^ 32 = 1)

include hgen henum hco in
theorem acts_all : ∀ t ∈ genMon G, ∃ P, MatP 10 P ∈ genT MK ∧ ActsP jm t P := by
  intro t ht
  unfold genMon at ht
  induction ht using Submonoid.closure_induction with
  | mem y hy =>
    obtain ⟨⟨k, hk⟩, rfl⟩ := hy
    exact ⟨MK k, genT_mem MK hk, acts_gen hgen henum hco hk⟩
  | one => exact ⟨IDT, by rw [MatP_IDT]; exact (genT MK).one_mem, acts_one⟩
  | mul y z _ _ hy hz =>
    obtain ⟨P, hP, hy⟩ := hy
    obtain ⟨Q, hQ, hz⟩ := hz
    have h := acts_mul hz hy
    exact ⟨mulT Q P, by rw [MatP_mulT]; exact (genT MK).mul_mem hQ hP, h⟩

include hgen henum hco in
theorem acts_surj : ∀ X ∈ genT MK, ∃ P, MatP 10 P = X ∧ ∃ t ∈ genMon G, ActsP jm t P := by
  intro X hX
  unfold genT at hX
  induction hX using Submonoid.closure_induction with
  | mem y hy =>
    obtain ⟨⟨k, hk⟩, rfl⟩ := hy
    exact ⟨MK k, rfl, _, gen_mem G hk, acts_gen hgen henum hco hk⟩
  | one => exact ⟨IDT, MatP_IDT, 1, (genMon G).one_mem, acts_one⟩
  | mul y z _ _ hy hz =>
    obtain ⟨P, rfl, s, hs, hy⟩ := hy
    obtain ⟨Q, rfl, t, ht, hz⟩ := hz
    exact ⟨mulT P Q, MatP_mulT P Q, t * s, (genMon G).mul_mem ht hs, acts_mul hy hz⟩

include henum in
theorem acts_unique {t : M22} (ht : t ^ 32 = 1) {P P' : ℕ} (h : ActsP jm t P)
    (h' : ActsP jm t P') : MatP 10 P = MatP 10 P' := by
  refine MatP_eq_of_vmF fun v hv => ?_
  have e : jm (vmF 10 P v) = jm (vmF 10 P' v) := cancel_right ht (by rw [← h v hv, ← h' v hv])
  rw [((jEnum_sound henum).1 _ (vmF_lt' P v)).2.symm, ((jEnum_sound henum).1 _
    (vmF_lt' P' v)).2.symm] at e
  exact (jEnum_sound henum).2 _ (vmF_lt' P v) _ (vmF_lt' P' v) e

@[expose] def centJ (G GJ : Nat → Nat) : Set M22 :=
  {t | t ∈ genMon G ∧ ∀ v < 1024, t * bitProd (fun i => MatP 22 (GJ i)) 10 v =
    bitProd (fun i => MatP 22 (GJ i)) 10 v * t}

theorem acts_of_centJ {t : M22} (h : t ∈ centJ G GJ) : ActsP jm t IDT := fun v hv => by
  rw [vmF_IDT hv]
  exact h.2 v hv

include hgen henum hin in
theorem genJ_sub_centJ : (genJ GJ : Set M22) ⊆ centJ G GJ := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (jm_bij hgen henum).2.2 hx
  refine ⟨genJ_le hin ((jm_bij hgen henum).1 ha), fun v _ => ?_⟩
  rw [← jm_xor hgen henum, ← jm_xor hgen henum, Nat.xor_comm]

include hgen henum in
theorem card_genJ : Nat.card (genJ GJ : Set M22) = 1024 := by
  have e := (jm_bij hgen henum).image_eq
  have hI : Set.Iio (1024 : ℕ) = ((Finset.range 1024 : Finset ℕ) : Set ℕ) := by
    ext
    simp
  rw [Nat.card_coe_set_eq, ← e, (jm_bij hgen henum).2.1.ncard_image, hI,
    Set.ncard_coe_finset, Finset.card_range]

include hgen henum hin in
theorem le_card_centJ : 1024 ≤ Nat.card (centJ G GJ) := by
  have h := Set.ncard_le_ncard (genJ_sub_centJ hgen henum hin) (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, card_genJ hgen henum] at h
  exact h

include hgen henum hco hpow in
theorem card_mul_le : Nat.card (genT MK) * Nat.card (centJ G GJ) ≤ Nat.card (genMon G) := by
  classical
  have hs := acts_surj (G := G) hgen henum hco
  choose P hP σ hσ hact using hs
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun p : genT MK × centJ G GJ =>
    (⟨σ p.1 p.1.2 * p.2, (genMon G).mul_mem (hσ _ _) p.2.2.1⟩ : genMon G)) ?_
  rintro ⟨⟨X, hX⟩, ⟨k, hk⟩⟩ ⟨⟨X', hX'⟩, ⟨k', hk'⟩⟩ e
  have e' : σ X hX * k = σ X' hX' * k' := Subtype.mk.inj e
  · have a1 := acts_mul (acts_of_centJ hk) (hact X hX)
    have a2 := acts_mul (acts_of_centJ hk') (hact X' hX')
    rw [← e'] at a2
    have hm := acts_unique henum ((genMon G).mul_mem (hσ X hX) hk.1 |> hpow _) a1 a2
    rw [MatP_mulT, MatP_mulT, MatP_IDT, one_mul, one_mul, hP, hP] at hm
    subst hm
    have : k = k' := cancel_left (hpow _ (hσ X hX)) e'
    subst this
    rfl

include hgen henum hin hco hpow in
theorem card_T (hR : TreeI PE PM PS PT MK) : 2 ^ 18 ≤ Nat.card (genMon G) := by
  have h1 := treeI_card hR
  have h2 := le_card_centJ hgen henum hin
  have h3 := card_mul_le (MK := MK) hgen henum hco hpow
  calc 2 ^ 18 = 256 * 1024 := by norm_num
    _ ≤ Nat.card (genT MK) * Nat.card (centJ G GJ) := Nat.mul_le_mul h1 h2
    _ ≤ _ := h3

include hgen henum hin hco hpow in
theorem small_of_card (hR : TreeI PE PM PS PT MK) (hc : Nat.card (genMon G) ≤ 2 ^ 18) :
    Nat.card (genT MK) ≤ 256 ∧ centJ G GJ = genJ GJ := by
  have h1 := treeI_card hR
  have h2 := le_card_centJ hgen henum hin
  have h3 := (card_mul_le (MK := MK) hgen henum hco hpow).trans hc
  refine ⟨?_, ?_⟩
  · by_contra hn
    have : 257 * 1024 ≤ Nat.card (genT MK) * Nat.card (centJ G GJ) :=
      Nat.mul_le_mul (by omega) h2
    omega
  · have h4 : Nat.card (centJ G GJ) ≤ 1024 := by
      by_contra hn
      have : 256 * 1025 ≤ Nat.card (genT MK) * Nat.card (centJ G GJ) :=
        Nat.mul_le_mul h1 (by omega)
      omega
    refine (Set.eq_of_subset_of_ncard_le (genJ_sub_centJ hgen henum hin) ?_ (Set.toFinite _)).symm
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, card_genJ hgen henum]
    exact h4

include hgen henum hin hco hpow in
theorem cent_le (hR : TreeI PE PM PS PT MK) (hc : Nat.card (genMon G) ≤ 2 ^ 18) {t : M22}
    (ht : t ∈ genMon G) (hJ : ∀ x ∈ genJ GJ, t * x = x * t) : t ∈ genJ GJ := by
  have e := (small_of_card hgen henum hin hco hpow hR hc).2
  have : t ∈ centJ G GJ := ⟨ht, fun v hv => hJ _ ((jm_bij hgen henum).1 hv)⟩
  rw [e] at this
  exact this

include hgen henum hco in
theorem normalizes {t : M22} (ht : t ∈ genMon G) {x : M22} (hx : x ∈ genJ GJ) :
    ∃ y ∈ genJ GJ, t * x = y * t := by
  obtain ⟨P, -, hP⟩ := acts_all (MK := MK) hgen henum hco t ht
  obtain ⟨v, hv, rfl⟩ := (jm_bij hgen henum).2.2 hx
  exact ⟨_, (jm_bij hgen henum).1 (vmF_lt' P v), hP v hv⟩

variable {SM EL INV CM RC : Nat → Nat} {EX MR : Nat → Nat → Nat} {NS NI : Nat}

include hgen henum hin hco hpow in
theorem ea_unique (hR : TreeI PE PM PS PT MK) (hI : invAllK PE INV NI = true)
    (hT : ∀ q < NI, tabRowK PE INV MR CM q = true) (h0 : SM 0 = 1) (hNS : 0 < NS)
    (hS : ∀ i < NS, setK PE SM EL INV CM RC EX MR NS NI i = true)
    (hc : Nat.card (genMon G) ≤ 2 ^ 18) (A : Set M22) (hAT : A ⊆ genMon G) (h1 : 1 ∈ A)
    (hmul : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ A) (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hsq : ∀ x ∈ A, x * x = 1) (hA : Nat.card A = 1024) : A = genJ GJ := by
  classical
  obtain ⟨hgT, hK⟩ := small_of_card hgen henum hin hco hpow hR hc
  have hp : ∀ a ∈ A, a ^ 32 = 1 := fun a ha => hpow a (hAT ha)
  let B : Set M10 := {X | ∃ a ∈ A, ∃ P, MatP 10 P = X ∧ ActsP jm a P}
  have hall := acts_all (MK := MK) hgen henum hco
  have hBT : ∀ X ∈ B, X ∈ genT MK := by
    rintro X ⟨a, ha, P, rfl, hP⟩
    obtain ⟨Q, hQ, hQa⟩ := hall a (hAT ha)
    rw [acts_unique henum (hp a ha) hP hQa]
    exact hQ
  have hB1 : (1 : M10) ∈ B := ⟨1, h1, IDT, MatP_IDT, acts_one⟩
  have hBmul : ∀ x ∈ B, ∀ y ∈ B, x * y ∈ B := by
    rintro _ ⟨a, ha, P, rfl, hP⟩ _ ⟨b, hb, Q, rfl, hQ⟩
    exact ⟨b * a, hmul b hb a ha, mulT P Q, MatP_mulT P Q, acts_mul hP hQ⟩
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    rintro _ ⟨a, ha, P, rfl, hP⟩ _ ⟨b, hb, Q, rfl, hQ⟩
    have e1 := acts_mul hP hQ
    have e2 := acts_mul hQ hP
    rw [hcomm a ha b hb] at e2
    rw [← MatP_mulT, ← MatP_mulT]
    exact acts_unique henum (hp _ (hmul b hb a ha)) e1 e2
  have hBsq : ∀ x ∈ B, x * x = 1 := by
    rintro _ ⟨a, ha, P, rfl, hP⟩
    have e1 := acts_mul hP hP
    rw [hsq a ha] at e1
    rw [← MatP_mulT, ← MatP_IDT]
    exact acts_unique henum (by rw [one_pow]) e1 acts_one
  have htriv : ∀ a ∈ A, ∀ P, MatP 10 P = 1 → ActsP jm a P → a ∈ (genJ GJ : Set M22) := by
    intro a ha P hP1 hP
    have h' := acts_congr (hP1.trans MatP_IDT.symm) hP
    have : a ∈ centJ G GJ := ⟨hAT ha, fun v hv => by rw [h' v hv, vmF_IDT hv]⟩
    rwa [hK] at this
  have hJc : Nat.card (genJ GJ : Set M22) = 1024 := card_genJ hgen henum
  by_cases hne : B = {1}
  ·
    have hsub : A ⊆ (genJ GJ : Set M22) := by
      intro a ha
      obtain ⟨P, -, hP⟩ := hall a (hAT ha)
      have hmem : MatP 10 P ∈ B := ⟨a, ha, P, rfl, hP⟩
      rw [hne] at hmem
      exact htriv a ha P hmem hP
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hA]
    exact hJc.le
  · exfalso
    have hX : ∀ x ∈ B, ∃ s < 256, MatP 10 (PE s) = x := fun x hx =>
      treeI_surj hR hgT x (hBT x hx)
    have hb := ea_bound hR hI hT h0 hNS hS B hX hB1 hBmul hBcomm hBsq hne
    choose base hbA hbP using fun (X : M10) (hX : X ∈ B) => hX
    choose PA hPA hPAa using fun (a : M22) (ha : a ∈ A) => hall a (hAT ha)
    have hXB : ∀ a (ha : a ∈ A), MatP 10 (PA a ha) ∈ B := fun a ha => ⟨a, ha, _, rfl, hPAa a ha⟩
    have hw : ∀ a (ha : a ∈ A), ∃ v < 1024, jm v = base _ (hXB a ha) * a := by
      intro a ha
      obtain ⟨Q, hQ, hQa⟩ := hbP _ (hXB a ha)
      have hwA := hmul _ (hbA _ (hXB a ha)) a ha
      have e := acts_mul (hPAa a ha) hQa
      have hm : MatP 10 (mulT (PA a ha) Q) = 1 := by
        rw [MatP_mulT, hQ]
        exact hBsq _ (hXB a ha)
      obtain ⟨v, hv, e'⟩ := (jm_bij hgen henum).2.2 (htriv _ hwA _ hm e)
      exact ⟨v, hv, e'⟩
    choose vA hvA hvAe using hw
    have hfix : ∀ a (ha : a ∈ A), vA a ha ∈ fixSet PE fun s => MatP 10 (PE s) ∈ B := by
      intro a ha
      refine mem_fixSet.2 ⟨hvA a ha, fun s _ hs => ?_⟩
      obtain ⟨a', ha', P', hP', hP'a⟩ := hs
      have hwA := hmul _ (hbA _ (hXB a ha)) a ha
      have e1 : a' * jm (vA a ha) = jm (vA a ha) * a' := by
        rw [hvAe a ha]
        exact hcomm a' ha' _ hwA
      rw [hP'a _ (hvA a ha)] at e1
      have e2 := cancel_right (hp a' ha') e1
      rw [((jEnum_sound henum).1 _ (vmF_lt' _ _)).2.symm,
        ((jEnum_sound henum).1 _ (hvA a ha)).2.symm] at e2
      have e3 := (jEnum_sound henum).2 _ (vmF_lt' _ _) _ (hvA a ha) e2
      rw [vmF_congr hP'.symm]
      exact e3
    let F : A → B × (fixSet PE fun s => MatP 10 (PE s) ∈ B) := fun a =>
      (⟨_, hXB a.1 a.2⟩, ⟨vA a.1 a.2, hfix a.1 a.2⟩)
    have hF : Function.Injective F := by
      rintro ⟨a, ha⟩ ⟨a', ha'⟩ e
      simp only [F, Prod.mk.injEq, Subtype.mk.injEq] at e
      obtain ⟨e1, e2⟩ := e
      have e3 : base _ (hXB a ha) * a = base _ (hXB a' ha') * a' := by
        rw [← hvAe, ← hvAe, e2]
      have e4 : base _ (hXB a ha) = base _ (hXB a' ha') := by
        congr 1
      rw [e4] at e3
      exact Subtype.ext (cancel_left (hp _ (hbA _ (hXB a' ha'))) e3)
    have hle := Nat.card_le_card_of_injective F hF
    rw [Nat.card_prod, hA, Nat.card_eq_fintype_card (α := (fixSet PE fun s => MatP 10 (PE s) ∈ B)),
      Fintype.card_coe] at hle
    omega

end Facts

end CFSG.KC.Co2J

end
