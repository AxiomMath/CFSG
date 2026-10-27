module

public import Certificates.Data.Kernel.Co2Fuse
public import CFSG.Certificates.Kernel.Co2Cls.Sound
public import CFSG.Certificates.Kernel.Co2Cls.Glue
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.Kernel.BSeed.Sound
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs
public import CFSG.Perm.ChainSpec

set_option exponentiation.threshold 600

public section

namespace CFSG.KC.Co2Fuse

open CFSG.KC.Loop CFSG.KC.F2W CFSG.KC.Co2InvS CFSG.KC.Co2Cls CFSG.KC.Co2Syl CFSG.KC.TabMatGrp
  CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.Sporadic.SmallF2.Native

local notation "M22" => Matrix (Fin 22) (Fin 22) (ZMod 2)

theorem ech22L_ge {fromK : Bool} {Q k : Nat} (hk : 22 ≤ k) :
    ech22L fromK Q k = ech22L fromK Q 22 := by
  have e : ∀ k', ech22L fromK Q k' = Nat.blt 0 (eLoopL fromK k' 22 Q 0 (Nat.shiftLeft 1 40)) :=
    fun _ => rfl
  rw [e, e, eLoopL_eq, eLoopL_eq]
  congr 1
  refine List.foldl_ext _ _ _ fun st l hl => ?_
  have hl' : l < 22 := List.mem_range.1 hl
  have h1 : Nat.ble k (0 + l) = Nat.ble 22 (0 + l) := by
    rw [Bool.eq_iff_iff, Nat.ble_eq, Nat.ble_eq]
    omega
  have h2 : Nat.blt (0 + l) k = Nat.blt (0 + l) 22 := by
    rw [Bool.eq_iff_iff, Nat.blt_eq, Nat.blt_eq]
    omega
  unfold CFSG.KC.BM.eBody
  rw [h1, h2]

theorem rankL_min {M P Q k : Nat} (h : rankL M P Q k = true) : (MatP 22 M).rank = min k 22 := by
  rcases Nat.le_total k 22 with hk | hk
  · rw [Nat.min_eq_left hk]
    exact rankL_sound hk h
  · rw [Nat.min_eq_right hk]
    refine rankL_sound (P := P) (Q := Q) le_rfl ?_
    unfold rankL at h ⊢
    rwa [ech22L_ge hk, ech22L_ge hk] at h

theorem MatP_nxor (A B : Nat) : MatP 22 (Nat.xor A B) = MatP 22 A + MatP 22 B :=
  MatP_xor A B

theorem rkS_sound {M c : Nat} (h : rkS M c = true) : (MatP 22 M).rank = min (kS c) 22 :=
  rankL_min h

@[expose] def labT (κ : ℕ × ℕ × ℕ) : ℕ :=
  if κ.1 = 6 then 1 else if κ.1 = 8 then 2 else
    if κ.1 = 10 then (if κ.2.1 = 10 ∧ κ.2.2 = 3 then 4 else 3) else 5

@[expose] noncomputable def labM (r y : M22) : ℕ :=
  if y * y = 1 ∧ y ≠ 1 then labT (kappa r y) else 0

theorem beq_dec (a b : Nat) : Nat.beq a b = decide (a = b) := by
  by_cases h : a = b
  · subst h
    rw [Nat.beq_refl, decide_eq_true rfl]
  · rw [beq_false h, decide_eq_false h]

theorem orF_eq (a b : Bool) : orF a b = (a || b) := by
  cases a <;> rfl

theorem min22 {a n : Nat} (hn : n < 22) : min a 22 = n ↔ a = n := by
  constructor
  · intro h
    rcases Nat.le_total a 22 with h' | h'
    · rwa [Nat.min_eq_left h'] at h
    · rw [Nat.min_eq_right h'] at h
      omega
  · rintro rfl
    exact Nat.min_eq_left (by omega)

theorem lab10_sound {CA : Nat → Nat} {R Y s : Nat} (h : lab10 CA R Y s ≠ 5) :
    lab10 CA R Y s = if (MatP 22 Y * MatP 22 R + 1).rank = 10 ∧
      ((MatP 22 R + 1) * (MatP 22 Y + 1)).rank = 3 then 4 else 3 := by
  unfold lab10 at h ⊢
  simp only [strictN_eq', selN_eq, andK_eq, beq_dec, Nat.add_eq] at h ⊢
  by_cases hr : (rkS (Nat.xor (mulV Y R) IDP) (CA (s + 1)) &&
      rkS (mulV (Nat.xor R IDP) (Nat.xor Y IDP)) (CA (s + 2))) = true
  · rw [if_pos hr]
    rw [Bool.and_eq_true] at hr
    have h1 := rkS_sound hr.1
    have h2 := rkS_sound hr.2
    rw [MatP_nxor, MatP_mulV, MatP_IDP] at h1
    rw [MatP_mulV, MatP_nxor, MatP_nxor, MatP_IDP] at h2
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    split_ifs <;> omega
  · rw [if_neg hr] at h
    exact absurd rfl h

theorem labY_sound {CA : Nat → Nat} {R Y s : Nat} (hY : Y < 2 ^ 484) (h : labY CA R Y s ≠ 5) :
    labY CA R Y s = labM (MatP 22 R) (MatP 22 Y) := by
  unfold labY at h ⊢
  simp only [strictN_eq', selN_eq, beq_dec] at h ⊢
  unfold labM
  by_cases hi : involK Y = true
  · rw [if_pos hi] at h ⊢
    rw [if_pos ((involK_iff hY).1 hi)]
    by_cases hr : rkS (Nat.xor Y IDP) (CA s) = true
    · rw [if_pos hr] at h ⊢
      have hk := rkS_sound hr
      rw [MatP_nxor, MatP_IDP] at hk
      unfold labT kappa
      simp only [decide_eq_true_eq] at h ⊢
      split_ifs at h ⊢ <;>
        first
        | omega
        | (rw [lab10_sound h, if_pos ‹_›])
        | (rw [lab10_sound h, if_neg ‹_›])
    · rw [if_neg hr] at h
      exact absurd rfl h
  · rw [if_neg hi]
    rw [if_neg fun e => hi ((involK_iff hY).2 e)]

@[expose] def pairJ (j lY lZ : ℕ) : Prop :=
  (j = 0 ∧ lY = 3 ∧ lZ = 4) ∨ (j = 1 ∧ lY = 3 ∧ (lZ = 2 ∨ lZ = 4)) ∨
    (j = 2 ∧ (lY = 2 ∨ lY = 4) ∧ lZ = 3)

instance (j lY lZ : ℕ) : Decidable (pairJ j lY lZ) := by
  unfold pairJ
  infer_instance

@[expose] noncomputable def hitJ (j : ℕ) (r s x : M22) : ℕ :=
  if labM r x = 1 ∧ pairJ j (labM r (x * r)) (labM r (x * s)) then 1 else 0

@[expose] noncomputable def hitR (CF : Nat → Nat) (R S N j k : ℕ) : ℕ :=
  if k < N then hitJ j (MatP 22 R) (MatP 22 S) (MatP 22 (elemAt CF k)) else 0

theorem tripC_eq (lY lZ : Nat) : tripC lY lZ = if lY = 5 ∨ lZ = 5 ∨ (lY = 4 ∧ lZ = 3) then BADF
    else (if lY = 3 ∧ lZ = 4 then 1 else 0) + 256 * (if lY = 3 ∧ (lZ = 2 ∨ lZ = 4) then 1 else 0) +
      65536 * (if (lY = 2 ∨ lY = 4) ∧ lZ = 3 then 1 else 0) := by
  unfold tripC
  simp only [selN_eq, orF_eq, andK_eq, beq_dec, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  by_cases h : lY = 5 ∨ lZ = 5 ∨ (lY = 4 ∧ lZ = 3)
  · rw [if_pos (by tauto), if_pos h]
  · rw [if_neg (by tauto), if_neg h]
    simp only [Nat.add_eq]
    split_ifs <;> omega

theorem labM_one_iff {r x : M22} : labM r x = 1 ↔ (x * x = 1 ∧ x ≠ 1) ∧ (x + 1).rank = 6 := by
  unfold labM labT kappa
  by_cases hi : x * x = 1 ∧ x ≠ 1
  · rw [if_pos hi]
    simp only
    split_ifs <;> simp_all
  · rw [if_neg hi]
    simp [hi]

theorem contribF_sound {CF PT CI CA : Nat → Nat} {R S N k : Nat}
    (h : contribF CF PT CI CA R S N k < BADF) :
    contribF CF PT CI CA R S N k =
        hitR CF R S N 0 k + 256 * hitR CF R S N 1 k + 65536 * hitR CF R S N 2 k ∧
      (k < N → ¬ (labM (MatP 22 R) (MatP 22 (elemAt CF k)) = 1 ∧
        labM (MatP 22 R) (MatP 22 (elemAt CF k) * MatP 22 R) = 4 ∧
        labM (MatP 22 R) (MatP 22 (elemAt CF k) * MatP 22 S) = 3)) := by
  unfold hitR
  unfold contribF at h ⊢
  simp only [selN_eq, strictN_eq'] at h ⊢
  by_cases hk : k < N
  swap
  · rw [if_neg (by simpa using hk)]
    simp [hk]
  rw [if_pos (by simpa using hk)] at h ⊢
  simp only [if_pos hk, hk, forall_const]
  set X := elemAt CF k with hX
  have hXl : X < 2 ^ 484 := elemAt_lt CF k
  by_cases hi : involK X = true
  swap
  · rw [if_neg hi]
    have h0 : ∀ y, labM y (MatP 22 X) ≠ 1 := fun y e =>
      hi ((involK_iff hXl).2 (labM_one_iff.1 e).1)
    simp [hitJ, h0]
  rw [if_pos hi] at h ⊢
  by_cases hr : rkS (Nat.xor X IDP) (CI (PT k)) = true
  swap
  · rw [if_neg hr] at h
    exact absurd h (lt_irrefl _)
  rw [if_pos hr] at h ⊢
  have hrk := rkS_sound hr
  rw [MatP_nxor, MatP_IDP] at hrk
  simp only [beq_dec] at h ⊢
  by_cases h6 : kS (CI (PT k)) = 6
  swap
  · rw [if_neg (by simpa using h6)]
    have h0 : ∀ y, labM y (MatP 22 X) ≠ 1 := fun y e => by
      have := (labM_one_iff.1 e).2
      rw [hrk] at this
      exact h6 ((min22 (by norm_num)).1 this)
    simp [hitJ, h0]
  rw [if_pos (by simpa using h6)] at h ⊢
  have hA : labM (MatP 22 R) (MatP 22 X) = 1 :=
    labM_one_iff.2 ⟨(involK_iff hXl).1 hi, by rw [hrk]; exact (min22 (by norm_num)).2 h6⟩
  unfold contribA at h ⊢
  simp only [strictN_eq', Nat.mul_eq, Nat.add_eq] at h ⊢
  rw [tripC_eq] at h ⊢
  set lY := labY CA R (mulV X R) (6 * aS (CI (PT k)))
  set lZ := labY CA R (mulV X S) (6 * aS (CI (PT k)) + 3)
  by_cases hb : lY = 5 ∨ lZ = 5 ∨ (lY = 4 ∧ lZ = 3)
  · rw [if_pos hb] at h
    exact absurd h (lt_irrefl _)
  rw [if_neg hb]
  have eY : lY = labM (MatP 22 R) (MatP 22 X * MatP 22 R) := by
    rw [← MatP_mulV]
    exact labY_sound (mulV_lt _ _) (fun e => hb (Or.inl e))
  have eZ : lZ = labM (MatP 22 R) (MatP 22 X * MatP 22 S) := by
    rw [← MatP_mulV]
    exact labY_sound (mulV_lt _ _) (fun e => hb (Or.inr (Or.inl e)))
  refine ⟨?_, fun e => hb (Or.inr (Or.inr ⟨eY.trans e.2.1, eZ.trans e.2.2⟩))⟩
  have hJ : ∀ j, hitJ j (MatP 22 R) (MatP 22 S) (MatP 22 X) = if pairJ j lY lZ then 1 else 0 := by
    intro j
    unfold hitJ
    rw [← eY, ← eZ]
    simp only [hA, true_and]
  have p0 : pairJ 0 lY lZ ↔ lY = 3 ∧ lZ = 4 := by simp [pairJ]
  have p1 : pairJ 1 lY lZ ↔ lY = 3 ∧ (lZ = 2 ∨ lZ = 4) := by simp [pairJ]
  have p2 : pairJ 2 lY lZ ↔ (lY = 2 ∨ lY = 4) ∧ lZ = 3 := by simp [pairJ]
  rw [hJ 0, hJ 1, hJ 2]
  simp only [p0, p1, p2, ↓reduceIte]

theorem fuseSum_eq (CF PT CI CA : Nat → Nat) (R S N b : Nat) :
    fuseSum CF PT CI CA R S N b = ∑ i ∈ Finset.range 64, contribF CF PT CI CA R S N (64 * b + i) :=
  recSum (fun i => contribF CF PT CI CA R S N (64 * b + i)) 64

theorem cntAt_lt (CNT : Nat → Nat) (b : Nat) : cntAt CNT b < BADF := by
  unfold cntAt BADF
  change (_ >>> _) &&& (2 ^ 24 - 1) < _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)

theorem hitR_le (CF : Nat → Nat) (R S N j k : Nat) : hitR CF R S N j k ≤ 1 := by
  unfold hitR hitJ
  split_ifs <;> omega

theorem hitR_ge {CF : Nat → Nat} {R S N j k : Nat} (hk : N ≤ k) : hitR CF R S N j k = 0 := by
  unfold hitR
  exact if_neg (by omega)

theorem fuseB_sound {CF PT CI CA CNT : Nat → Nat} {R S N b : Nat}
    (h : fuseB CF PT CI CA R S CNT N b = true) :
    cntAt CNT b = (∑ i ∈ Finset.range 64, hitR CF R S N 0 (64 * b + i)) +
        256 * (∑ i ∈ Finset.range 64, hitR CF R S N 1 (64 * b + i)) +
        65536 * (∑ i ∈ Finset.range 64, hitR CF R S N 2 (64 * b + i)) ∧
      ∀ i < 64, 64 * b + i < N →
        ¬ (labM (MatP 22 R) (MatP 22 (elemAt CF (64 * b + i))) = 1 ∧
          labM (MatP 22 R) (MatP 22 (elemAt CF (64 * b + i)) * MatP 22 R) = 4 ∧
          labM (MatP 22 R) (MatP 22 (elemAt CF (64 * b + i)) * MatP 22 S) = 3) := by
  unfold fuseB at h
  have hs := Nat.eq_of_beq_eq_true h
  rw [fuseSum_eq] at hs
  have hlt : ∀ i ∈ Finset.range 64, contribF CF PT CI CA R S N (64 * b + i) < BADF := by
    intro i hi
    have := Finset.single_le_sum (f := fun i => contribF CF PT CI CA R S N (64 * b + i))
      (fun _ _ => Nat.zero_le _) hi
    exact lt_of_le_of_lt (this.trans (le_of_eq hs)) (cntAt_lt CNT b)
  refine ⟨?_, fun i hi hN => (contribF_sound (hlt i (Finset.mem_range.2 hi))).2 hN⟩
  rw [← hs, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i hi => (contribF_sound (hlt i hi)).1

theorem fuse_total {CF PT CI CA CNT : Nat → Nat} {R S N hi : Nat} (hN : N ≤ 4096 * hi)
    (h : ∀ b < 64 * hi, fuseB CF PT CI CA R S CNT N b = true) :
    (∀ j < 3, cntTotal CNT j hi = ∑ k ∈ Finset.range N, hitR CF R S N j k) ∧
      ∀ k < N, ¬ (labM (MatP 22 R) (MatP 22 (elemAt CF k)) = 1 ∧
        labM (MatP 22 R) (MatP 22 (elemAt CF k) * MatP 22 R) = 4 ∧
        labM (MatP 22 R) (MatP 22 (elemAt CF k) * MatP 22 S) = 3) := by
  refine ⟨fun j hj => ?_, fun k hk => ?_⟩
  · have hle : ∀ j b, ∑ i ∈ Finset.range 64, hitR CF R S N j (64 * b + i) ≤ 64 := fun j b =>
      (Finset.sum_le_sum fun i _ => hitR_le CF R S N j (64 * b + i)).trans (by simp)
    have tail : ∑ k ∈ Finset.range (64 * (64 * hi)), hitR CF R S N j k =
        ∑ k ∈ Finset.range N, hitR CF R S N j k := by
      have hm : 64 * (64 * hi) = N + (64 * (64 * hi) - N) := by omega
      rw [hm, Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range (64 * (64 * hi) - N))
        (f := fun k => hitR CF R S N j (N + k)) (fun k _ => hitR_ge (by omega)), add_zero]
    have key : cntTotal CNT j hi =
        ∑ b ∈ Finset.range (64 * hi), cntAt CNT b / 2 ^ (8 * j) % 256 := by
      unfold cntTotal
      exact (sumBelow_eq' _ hi _ (le_refl (64 * hi))).trans
        (Finset.sum_congr rfl fun b _ => fld_byte _ _)
    rw [key, ← tail, ← sum_blocks (hitR CF R S N j) (64 * hi)]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [(fuseB_sound (h b (Finset.mem_range.1 hb))).1]
    have h0 := hle 0 b
    have h1 := hle 1 b
    have h2 := hle 2 b
    interval_cases j
    · simp only [Nat.mul_zero, pow_zero, Nat.div_one]
      omega
    · rw [(by norm_num : (2 : Nat) ^ (8 * 1) = 256)]
      omega
    · rw [(by norm_num : (2 : Nat) ^ (8 * 2) = 65536)]
      omega
  · have hb := (fuseB_sound (h (k / 64) (by omega))).2 (k % 64) (Nat.mod_lt _ (by norm_num))
      (by rw [Nat.div_add_mod]; exact hk)
    rwa [Nat.div_add_mod] at hb

section Count

variable {CF G : Nat → Nat} {N : Nat}

theorem fuse_card (hR : TreeRecs CF G N) (hc : Nat.card (genMon G) ≤ N) (R S j : Nat) :
    Nat.card {x : M22 // x ∈ genMon G ∧ labM (MatP 22 R) x = 1 ∧
        pairJ j (labM (MatP 22 R) (x * MatP 22 R)) (labM (MatP 22 R) (x * MatP 22 S))} =
      ∑ k ∈ Finset.range N, hitR CF R S N j k := by
  classical
  let f : Fin N → genMon G := fun k => ⟨MatP 22 (elemAt CF k), tree_mem hR k k.2⟩
  have hf : Function.Injective f := fun a b e =>
    Fin.ext (tree_inj hR a a.2 b b.2 (congrArg Subtype.val e))
  let e := Equiv.ofBijective f (hf.bijective_of_nat_card_le (by simpa using hc))
  let Q : M22 → Prop := fun x => labM (MatP 22 R) x = 1 ∧
    pairJ j (labM (MatP 22 R) (x * MatP 22 R)) (labM (MatP 22 R) (x * MatP 22 S))
  have he : ∀ k : Fin N, ((e k : genMon G) : M22) = MatP 22 (elemAt CF k) := fun _ => rfl
  have h0 : Nat.card {x : M22 // x ∈ genMon G ∧ Q x} = Nat.card {y : genMon G // Q y} :=
    Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ genMon G) Q).symm
  have h1 : Nat.card {y : genMon G // Q y} =
      Nat.card {k : Fin N // Q (MatP 22 (elemAt CF k))} :=
    Nat.card_congr (e.subtypeEquiv (p := fun k : Fin N => Q (MatP 22 (elemAt CF k)))
      (q := fun y : genMon G => Q y) fun k => by rw [he]).symm
  change Nat.card {x : M22 // x ∈ genMon G ∧ Q x} = _
  rw [h0, h1, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Finset.sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold hitR
  rw [if_pos k.isLt]
  unfold hitJ
  exact if_congr Iff.rfl rfl rfl

theorem fuse_none (hR : TreeRecs CF G N) (hc : Nat.card (genMon G) ≤ N) {R S : Nat}
    (h : ∀ k < N, ¬ (labM (MatP 22 R) (MatP 22 (elemAt CF k)) = 1 ∧
      labM (MatP 22 R) (MatP 22 (elemAt CF k) * MatP 22 R) = 4 ∧
      labM (MatP 22 R) (MatP 22 (elemAt CF k) * MatP 22 S) = 3)) :
    ∀ x ∈ genMon G, ¬ (labM (MatP 22 R) x = 1 ∧ labM (MatP 22 R) (x * MatP 22 R) = 4 ∧
      labM (MatP 22 R) (x * MatP 22 S) = 3) := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := tree_surj hR hc x hx
  exact h k hk

end Count

theorem conj_eq_one {u : M22ˣ} {a : M22} : (u : M22) * a * ((u⁻¹ : M22ˣ) : M22) = 1 ↔ a = 1 := by
  constructor
  · intro h
    calc a = ((u⁻¹ : M22ˣ) : M22) * ((u : M22) * a * ((u⁻¹ : M22ˣ) : M22)) * (u : M22) := by
          simp [mul_assoc]
      _ = 1 := by rw [h, mul_one, Units.inv_mul]
  · rintro rfl
    rw [mul_one, Units.mul_inv]

theorem labM_conj {r g x y : M22} (hg : IsUnit g) (hr : g * r = r * g) (h : g * x = y * g) :
    labM r y = labM r x := by
  obtain ⟨u, rfl⟩ := hg
  have hy : y = (u : M22) * x * ((u⁻¹ : M22ˣ) : M22) := by
    rw [h, mul_assoc, Units.mul_inv, mul_one]
  have hyy : y * y = (u : M22) * (x * x) * ((u⁻¹ : M22ˣ) : M22) := by
    rw [hy]
    simp only [mul_assoc]
    rw [← mul_assoc ((u⁻¹ : M22ˣ) : M22) (u : M22), Units.inv_mul, one_mul]
  have hinv : (y * y = 1 ∧ y ≠ 1) ↔ (x * x = 1 ∧ x ≠ 1) := by
    rw [hyy, conj_eq_one, hy, ne_eq, conj_eq_one]
  unfold labM
  rw [kappa_conj u.isUnit hr h]
  by_cases hx : x * x = 1 ∧ x ≠ 1
  · rw [if_pos hx, if_pos (hinv.2 hx)]
  · rw [if_neg hx, if_neg (fun e => hx (hinv.1 e))]

theorem labM_iff {r : M22} {C : Set M22} (hU : ∀ g ∈ C, IsUnit g) (hr : ∀ g ∈ C, g * r = r * g)
    {reps : ℕ → M22} {L : ℕ → ℕ} (hL : ∀ i < 10, labM r (reps i) = L i)
    (hcen : ∀ x ∈ C, x * x = 1 → x ≠ 1 → ∃ i < 10, ∃ g ∈ C, g * reps i = x * g)
    {V : Set ℕ} (hV : 0 ∉ V) {x : M22} (hx : x ∈ C) :
    (∃ c < 10, L c ∈ V ∧ ∃ g ∈ C, g * reps c = x * g) ↔ labM r x ∈ V := by
  constructor
  · rintro ⟨c, hc, hcV, g, hg, e⟩
    rw [labM_conj (hU g hg) (hr g hg) e, hL c hc]
    exact hcV
  · intro hxV
    have hi : x * x = 1 ∧ x ≠ 1 := by
      by_contra hn
      unfold labM at hxV
      rw [if_neg hn] at hxV
      exact hV hxV
    obtain ⟨i, hi10, g, hg, e⟩ := hcen x hx hi.1 hi.2
    refine ⟨i, hi10, ?_, g, hg, e⟩
    rw [← hL i hi10, ← labM_conj (hU g hg) (hr g hg) e]
    exact hxV

end CFSG.KC.Co2Fuse

end
