module

public import CFSG.Certificates.Kernel.KStep.Tau
public import Certificates.Data.Kernel.KDenseP.TauInvStep
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Ring.Finset

public section

namespace CFSG.KC.KStep

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP
open CFSG.Monster.AxisCount CFSG.Monster.B.Rep4371.Native CFSG.KC.MonsterConv.Perm

@[expose] noncomputable def tauInvG (O : POps) (F : Fix) (X A W : Nat) : Nat × Nat × Nat :=
  (fun L Xp Xq =>
    (fun d2 U =>
      (Nat.lor (O.neg SX F.sgOddUp (Nat.land (Nat.shiftRight W (nat_lit 65536)) L))
        (Nat.lor (Nat.land (O.half SX (nat_lit 3) (wht6G O
            (O.net SX (nat_lit 17) F.pi6 (O.neg SX F.doct X)))) (O.rep SX regOct))
          (Nat.lor (O.expand (nat_lit 114688) (Nat.land (O.add SA A d2) (O.rep SA upA)))
            (O.expand (nat_lit 115712) (Nat.land (O.add SA A (O.neg SA upA d2)) (O.rep SA upA))))),
       Nat.lor (Nat.land A (O.rep SA diagA)) (Nat.lor U (transpG O U)),
       Nat.lor (O.neg SX F.sgWLo (Nat.land X L))
         (Nat.shiftLeft (O.neg SX F.sgWUp (Nat.land W L)) (nat_lit 65536))))
      (O.half SA (nat_lit 1) (O.add SA Xp Xq))
      (Nat.land (O.half SA (nat_lit 1) (O.add SA Xp (O.neg SA upA Xq))) (O.rep SA upA)))
    (O.rep SX lo16) (O.compact (nat_lit 114688) X) (O.compact (nat_lit 115712) X)

theorem tauInvStepN_eq (n lg : ℕ) (F : Fix) (X A W : Nat) :
    tauInvStepN n lg F X A W = tauInvG (opsN n lg) F X A W :=
  rfl

namespace TauInvAux

open TauAux

theorem sg_cycle_bit (y : ℕ) :
    (rowF gH 2048).testBit y = ((rowF gU 2048).testBit y ^^ (rowF gL 2048).testBit y) := by
  rw [testBit_rowF gH_lt', testBit_rowF gU_lt', testBit_rowF gL_lt',
    show gH (y / 32) = gU (y / 32) ^^^ gL (y / 32) from rfl, Nat.testBit_xor]
  cases (decide (y / 32 < 2048) && decide (y % 32 < 24)) <;> simp

@[expose] noncomputable def octNeg (q c : ℕ) : Bool :=
  Bool.xor (POCT.testBit q) (Nat.testBit (popcT (nat_lit 6) (Nat.land (Bool.rec (motive := fun _ => ℕ) q
    (Nat.xor q (nat_lit 63)) (Nat.beq (parT (nat_lit 6) q) (nat_lit 1))) c)) (nat_lit 0))

@[expose] noncomputable def octRowM (q : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun c acc => Nat.lor acc (Nat.shiftLeft (octNeg q c).toNat c)) 64

@[expose] noncomputable def octColM (d : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun c acc => Nat.lor acc (Nat.shiftLeft (octNeg c d).toNat c)) 64

@[expose] noncomputable def nlo (O : POps) (m x : ℕ) : ℕ := O.neg SX m (Nat.land x (O.rep SX lo16))

@[expose] noncomputable def nhi (O : POps) (m x : ℕ) : ℕ :=
  O.neg SX m (Nat.land (Nat.shiftRight x (nat_lit 65536)) (O.rep SX lo16))

@[expose] noncomputable def dd2i (O : POps) (X : ℕ) : ℕ :=
  O.half SA (nat_lit 1) (O.add SA (O.compact (nat_lit 114688) X) (O.compact (nat_lit 115712) X))

@[expose] noncomputable def UUi (O : POps) (X : ℕ) : ℕ := Nat.land (dd2 O X) (O.rep SA upA)

@[expose] noncomputable def T3i (O : POps) (X A : ℕ) : ℕ :=
  O.expand 114688 (Nat.land (O.add SA A (dd2i O X)) (O.rep SA upA))

@[expose] noncomputable def T4i (O : POps) (X A : ℕ) : ℕ :=
  O.expand 115712 (Nat.land (O.add SA A (O.neg SA upA (dd2i O X))) (O.rep SA upA))

@[expose] noncomputable def octI (O : POps) (F : Fix) (X : ℕ) : ℕ :=
  Nat.land (O.half SX (nat_lit 3) (wht6G O (O.net SX (nat_lit 17) F.pi6 (O.neg SX F.doct X))))
    (O.rep SX regOct)

@[expose] noncomputable def ANg (O : POps) (A U : ℕ) : ℕ :=
  Nat.lor (Nat.land A (O.rep SA diagA)) (Nat.lor U (transpG O U))

theorem tauInvG_eq (O : POps) (F : Fix) (X A W : ℕ) : tauInvG O F X A W =
    (Nat.lor (nhi O F.sgOddUp W) (Nat.lor (octI O F X) (Nat.lor (T3i O X A) (T4i O X A))),
     ANg O A (UUi O X),
     Nat.lor (nlo O F.sgWLo X) (Nat.shiftLeft (nlo O F.sgWUp W) (nat_lit 65536))) := rfl

variable {np : ℕ} {O : POps}

section Lo

variable (hO : PLaw np O) {g : ℕ → ℕ} (hg : ∀ t < 2048, g t < 2 ^ 24) {x : ℕ} (hx : Bd np SX x)
include hO hg hx

theorem nlo_bd : Bd np SX (nlo O (rowF g 2048) x) := hO.neg_bd (rowF_lt hg) (bdL hx)

theorem nlo_res {p : ℕ} (hp : p < 65536) : resPN np SX (nlo O (rowF g 2048) x) p =
    if (rowF g 2048).testBit p then -resPN np SX x p else resPN np SX x p := by
  unfold nlo
  rw [hO.neg_res (rowF_lt hg) (bdL hx) (by rw [SX_v]; omega),
    res_land_rep' hO lo16_lt (by rw [SX_v]; omega), lo16_bit, decide_eq_true hp, if_pos rfl]

theorem nlo_zero {p : ℕ} (hp : p < SX) (hp' : 65536 ≤ p) : Zero np SX (nlo O (rowF g 2048) x) p :=
  hO.neg_zero (rowF_lt hg) (bdL hx) hp (rowF_hi hg hp')
    (zero_land_rep hO lo16_lt hp (by rw [lo16_bit, decide_eq_false (by omega)]))

theorem nhi_bd : Bd np SX (nhi O (rowF g 2048) x) :=
  hO.neg_bd (rowF_lt hg) (bdL (lt_of_le_of_lt (Nat.shiftRight_le x 65536) hx))

theorem nhi_res {p : ℕ} (hp : p < 65536) : resPN np SX (nhi O (rowF g 2048) x) p =
    if (rowF g 2048).testBit p then -resPN np SX x (p + 65536) else resPN np SX x (p + 65536) := by
  have hs : Bd np SX (Nat.shiftRight x (nat_lit 65536)) := lt_of_le_of_lt (Nat.shiftRight_le x 65536) hx
  unfold nhi
  rw [hO.neg_res (rowF_lt hg) (bdL hs) (by rw [SX_v]; omega)]
  have e := res_shr_land hO (o := 65536) (m := lo16) (x := x) (S := SX) (by rw [SX_v]; omega)
    lo16_lt' hx (p := p) (by rw [SX_v]; omega)
  rw [lo16_bit, decide_eq_true hp, if_pos rfl] at e
  change resPN np SX ((x >>> 65536) &&& O.rep SX lo16) p = _ at e
  rw [show Nat.land (Nat.shiftRight x (nat_lit 65536)) (O.rep SX lo16) =
    (x >>> 65536) &&& O.rep SX lo16 from rfl, e]

theorem nhi_zero {p : ℕ} (hp : p < SX) (hp' : 65536 ≤ p) : Zero np SX (nhi O (rowF g 2048) x) p :=
  hO.neg_zero (rowF_lt hg) (bdL (lt_of_le_of_lt (Nat.shiftRight_le x 65536) hx)) hp (rowF_hi hg hp')
    (zero_land_rep hO lo16_lt hp (by rw [lo16_bit, decide_eq_false (by omega)]))

theorem nlo_hs : ∀ b < np, ∀ q < SX, SX - 65536 ≤ q →
    (nlo O (rowF g 2048) x).testBit (b * SX + q) = false := fun b hb q hq hq' =>
  nlo_zero hO hg hx hq (by rw [SX_v] at hq'; omega) b hb

theorem nloS_bd : Bd np SX (Nat.shiftLeft (nlo O (rowF g 2048) x) (nat_lit 65536)) :=
  bd_shl (nlo_bd hO hg hx) (nlo_hs hO hg hx)

theorem nloS_res {p : ℕ} (hp : p < SX) :
    resPN np SX (Nat.shiftLeft (nlo O (rowF g 2048) x) (nat_lit 65536)) p =
      if 65536 ≤ p then resPN np SX (nlo O (rowF g 2048) x) (p - 65536) else 0 :=
  res_shl (nlo_bd hO hg hx) (nlo_hs hO hg hx) hp

theorem nloS_zero {p : ℕ} (hp : p < 65536) :
    Zero np SX (Nat.shiftLeft (nlo O (rowF g 2048) x) (nat_lit 65536)) p :=
  zero_shl (S := SX) (o := 65536) hp (by rw [SX_v]; omega) (nlo_hs hO hg hx)

end Lo

section Pair

variable (hO : PLaw np O) {X A : ℕ} (hX : Bd np SX X) (hA : Bd np SA A)
include hO

theorem dd2i_bd : Bd np SA (dd2i O X) :=
  hO.half_bd (by decide) (by decide) (hO.add_bd hO.compact_bd hO.compact_bd)

include hX in
theorem dd2i_res {q : ℕ} (hq : q < SA) : resPN np SA (dd2i O X) q =
    hN np * (resPN np SX X (114688 + q) + resPN np SX X (115712 + q)) := by
  unfold dd2i
  rw [hO.half_res (by decide) (by decide) (hO.add_bd hO.compact_bd hO.compact_bd) hq,
    hO.add_res hO.compact_bd hO.compact_bd hq, compact_res' hO (by decide) hq hX,
    compact_res' hO (by decide) hq hX, pow_one]

theorem UUi_bd : Bd np SA (UUi O X) := bdL (dd2_bd hO)

include hX in
theorem UUi_res {q : ℕ} (hq : q < SA) : resPN np SA (UUi O X) q = if upA.testBit q then
    hN np * (resPN np SX X (114688 + q) - resPN np SX X (115712 + q)) else 0 := by
  unfold UUi
  rw [res_land_rep' hO upA_lt hq, dd2_res hO hX hq]
  cases upA.testBit q <;> simp [sub_eq_add_neg]

theorem UUi_zero {q : ℕ} (hq : q < SA) (hu : upA.testBit q = false) : Zero np SA (UUi O X) q :=
  zero_land_rep hO upA_lt hq hu

include hA

theorem I3i_bd : Bd np SA (Nat.land (O.add SA A (dd2i O X)) (O.rep SA upA)) :=
  bdL (hO.add_bd hA (dd2i_bd hO))

theorem I4i_bd : Bd np SA (Nat.land (O.add SA A (O.neg SA upA (dd2i O X))) (O.rep SA upA)) :=
  bdL (hO.add_bd hA (hO.neg_bd upA_lt (dd2i_bd hO)))

theorem T3i_bd : Bd np SX (T3i O X A) := hO.expand_bd (by decide) (I3i_bd hO hA)

theorem T4i_bd : Bd np SX (T4i O X A) := hO.expand_bd (by decide) (I4i_bd hO hA)

theorem T3i_res {p : ℕ} (h1 : 114688 ≤ p) (h2 : p < 115712) (hu : upA.testBit (p - 114688) = true) :
    resPN np SX (T3i O X A) p = resPN np SA A (p - 114688) + resPN np SA (dd2i O X) (p - 114688) := by
  unfold T3i
  rw [hO.expand_res (by decide) (I3i_bd hO hA) (by rw [SX_v]; omega), if_pos (by rw [SA_v]; omega),
    res_land_rep' hO upA_lt (by rw [SA_v]; omega), hu, if_pos rfl,
    hO.add_res hA (dd2i_bd hO) (by rw [SA_v]; omega)]

theorem T4i_res {p : ℕ} (h1 : 115712 ≤ p) (h2 : p < 116736) (hu : upA.testBit (p - 115712) = true) :
    resPN np SX (T4i O X A) p = resPN np SA A (p - 115712) - resPN np SA (dd2i O X) (p - 115712) := by
  unfold T4i
  rw [hO.expand_res (by decide) (I4i_bd hO hA) (by rw [SX_v]; omega), if_pos (by rw [SA_v]; omega),
    res_land_rep' hO upA_lt (by rw [SA_v]; omega), hu, if_pos rfl,
    hO.add_res hA (hO.neg_bd upA_lt (dd2i_bd hO)) (by rw [SA_v]; omega),
    hO.neg_res upA_lt (dd2i_bd hO) (by rw [SA_v]; omega), hu, if_pos rfl, sub_eq_add_neg]

theorem T3i_zero {p : ℕ} (hp : p < SX)
    (h : ¬ (114688 ≤ p ∧ p < 115712 ∧ upA.testBit (p - 114688) = true)) :
    Zero np SX (T3i O X A) p := by
  unfold T3i
  refine hO.expand_zero (by decide) (I3i_bd hO hA) hp fun hw => ?_
  rw [SA_v] at hw
  exact zero_land_rep hO upA_lt (by rw [SA_v]; omega) (by
    cases e : upA.testBit (p - 114688)
    · rfl
    · exact absurd ⟨hw.1, by omega, e⟩ h)

theorem T4i_zero {p : ℕ} (hp : p < SX)
    (h : ¬ (115712 ≤ p ∧ p < 116736 ∧ upA.testBit (p - 115712) = true)) :
    Zero np SX (T4i O X A) p := by
  unfold T4i
  refine hO.expand_zero (by decide) (I4i_bd hO hA) hp fun hw => ?_
  rw [SA_v] at hw
  exact zero_land_rep hO upA_lt (by rw [SA_v]; omega) (by
    cases e : upA.testBit (p - 115712)
    · rfl
    · exact absurd ⟨hw.1, by omega, e⟩ h)

end Pair

theorem Kz_symm : ∀ a < 64, ∀ b < 64, Kz 6 a b = Kz 6 b a := by decide +kernel

theorem phi6_invol : ∀ c < 64, phi6 (phi6 c) = c := by decide +kernel

section Oct

variable (hO : PLaw np O) {F : Fix} (h6 : pi6OK F = true) (hm : tauMasksOK F = true) {X : ℕ}
  (hX : Bd np SX X)
include hO h6 hm hX

theorem octI_bd : Bd np SX (octI O F X) := by
  obtain ⟨hk, -⟩ := Benes.andB_true h6
  unfold octI
  rw [(masks_spec hm).1]
  exact bdL (hO.half_bd (by decide) (by decide) (Hn_bd hO 6 le_rfl _
    (hO.net_bd (k := 17) SX_eq hk (hO.neg_bd doct_lt hX))))

theorem octI_zero {p : ℕ} (hp : p < SX) (hr : ¬ (65536 ≤ p ∧ p < 114112)) :
    Zero np SX (octI O F X) p := by
  have hro : regOct.testBit p = false := by
    rw [← Bool.not_eq_true, CFSG.KC.KDense.InitAux.testBit_regOct]
    exact hr
  exact zero_land_rep hO regOct_lt hp hro

theorem octI_res {B q : ℕ} (hB1 : 1024 ≤ B) (hB2 : B < 1783) (hq : q < 64) :
    resPN np SX (octI O F X) (64 * B + q) = hN np ^ 3 * ∑ c ∈ Finset.range 64,
      ((if POCT.testBit c then -Kz 6 (phi6 c) q else Kz 6 (phi6 c) q : ℤ) : ZMod (2 ^ np - 1)) *
        resPN np SX X (64 * B + c) := by
  obtain ⟨hk, -⟩ := Benes.andB_true h6
  have hpS : 64 * B + q < SX := by change _ < 131072; omega
  have hy := hO.net_bd (k := 17) SX_eq hk (hO.neg_bd doct_lt hX)
  unfold octI
  rw [(masks_spec hm).1, res_land_rep' hO regOct_lt hpS,
    (CFSG.KC.KDense.InitAux.testBit_regOct _).mpr ⟨by omega, by omega⟩, if_pos rfl, wht6G_eq,
    hO.half_res (by decide) (by decide) (Hn_bd hO 6 le_rfl _ hy) hpS,
    Hn_res hO 6 le_rfl _ hy B hB1 hB2 q hq]
  congr 1
  rw [Finset.sum_congr rfl fun c hc => by
    have hc' := Finset.mem_range.1 hc
    have hf := phi6_lt hc'
    have hcS : 64 * B + c < SX := by change _ < 131072; omega
    rw [hO.net_res (k := 17) SX_eq hk (hO.neg_bd doct_lt hX) hcS, pi6_perm h6 hcS,
      phi_blk hB1 hB2 hc', hO.neg_res doct_lt hX (by change _ < 131072; omega), doct_bit,
      decide_eq_true (by omega), Bool.true_and, show (64 * B + phi6 c) % 64 = phi6 c by omega]]
  refine Finset.sum_nbij' phi6 phi6 (fun c hc => Finset.mem_range.2 (phi6_lt (Finset.mem_range.1 hc)))
    (fun c hc => Finset.mem_range.2 (phi6_lt (Finset.mem_range.1 hc)))
    (fun c hc => phi6_invol c (Finset.mem_range.1 hc))
    (fun c hc => phi6_invol c (Finset.mem_range.1 hc)) (fun c hc => ?_)
  have hc' := Finset.mem_range.1 hc
  rw [phi6_invol c hc', Kz_symm q hq c hc']
  split_ifs <;> push_cast <;> ring

end Oct

@[expose] noncomputable def octMI (q c : ℕ) : ℤ := if POCT.testBit q then -Kz 6 (phi6 q) c else Kz 6 (phi6 q) c

theorem octMI_neg : ∀ q < 64, ∀ c < 64, octMI q c = if octNeg q c then -1 else 1 := by decide +kernel

theorem octRow_bit : ∀ q < 64, ∀ c < 64, (octRowM q).testBit c = octNeg q c := by decide +kernel

theorem octCol_bit : ∀ d < 64, ∀ c < 64, (octColM d).testBit c = octNeg c d := by decide +kernel

theorem oct_pc : ∀ q < 64, ∀ d < 64,
    popcT 64 (Nat.xor (octRowM q) (octColM d)) = if octNeg d q then 36 else 28 := by decide +kernel

theorem bitN_tb (a k : ℕ) : bitN a k = (a.testBit k).toNat := by
  have h : bitN a k = a / 2 ^ k % 2 := by
    change (a >>> k) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [h, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (a / 2 ^ k) with h0 | h1
  · simp [h0]
  · simp [h1]

theorem popcT_sumB (a : ℕ) : ∀ k, popcT k a = ∑ i ∈ Finset.range k, (a.testBit i).toNat
  | 0 => rfl
  | k + 1 => by
    rw [Finset.sum_range_succ, ← popcT_sumB a k, ← bitN_tb]
    rfl

theorem octMI_sq {n l : ℕ} (hn : n < 64) (hl : l < 64) :
    ∑ m ∈ Finset.range 64, octMI n m * octMI m l = 8 * octMI l n := by
  have key : ∀ m ∈ Finset.range 64, octMI n m * octMI m l =
      1 - 2 * (((Nat.xor (octRowM n) (octColM l)).testBit m).toNat : ℤ) := fun m hm => by
    have hm' := Finset.mem_range.1 hm
    change _ = 1 - 2 * (((octRowM n ^^^ octColM l).testBit m).toNat : ℤ)
    rw [octMI_neg n hn m hm', octMI_neg m hm' l hl, Nat.testBit_xor, octRow_bit n hn m hm',
      octCol_bit l hl m hm']
    cases octNeg n m <;> cases octNeg m l <;> decide
  have hs : ∑ m ∈ Finset.range 64, (((Nat.xor (octRowM n) (octColM l)).testBit m).toNat : ℤ) =
      (popcT 64 (Nat.xor (octRowM n) (octColM l)) : ℤ) := by
    rw [popcT_sumB]
    push_cast
    rfl
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, ← Finset.mul_sum, hs, oct_pc n hn l hl,
    octMI_neg l hl n hn]
  cases octNeg l n <;> norm_num

section NewA

variable (hO : PLaw np O) {A U : ℕ} (hA : Bd np SA A) (hU : Bd np SA U)
  (hUz : ∀ q < SA, upA.testBit q = false → Zero np SA U q)
include hO hA hU hUz

theorem ANg_bd : Bd np SA (ANg O A U) :=
  bd_lor (bdL hA) (bd_lor hU (by rw [transpG_eq]; exact Tn_bd hO 5 le_rfl _ hU))

theorem ANg_diag {i : ℕ} (hi : i < 24) :
    resPN np SA (ANg O A U) (32 * i + i) = resPN np SA A (32 * i + i) := by
  have hq : 32 * i + i < SA := by rw [SA_v]; omega
  have hu : upA.testBit (32 * i + i) = false := by
    rw [CFSG.KC.KDense.InitAux.upA_bits _ (by omega)]
    simp only [decide_eq_false_iff_not]
    omega
  have e1 : (32 * i + i) / 32 = i := by omega
  have e2 : (32 * i + i) % 32 = i := by omega
  have hd : diagA.testBit (32 * i + i) = true := by
    rw [diagA_bits (32 * i + i) (by omega), e1, e2]
    simp only [decide_eq_true_eq]
    exact ⟨trivial, hi⟩
  unfold ANg
  rw [res_lor_l hq (zero_lor (hUz _ hq hu) (transp_zero hO (by omega) (by
    rw [e1, e2]
    exact hUz _ hq hu))), res_land_rep' hO diagA_lt hq, hd, if_pos rfl]

theorem ANg_up {i j : ℕ} (hij : i < j) (hj : j < 24) :
    resPN np SA (ANg O A U) (32 * i + j) = resPN np SA U (32 * i + j) := by
  have hq : 32 * i + j < SA := by rw [SA_v]; omega
  have hq' : 32 * j + i < SA := by rw [SA_v]; omega
  have e1 : (32 * i + j) / 32 = i := by omega
  have e2 : (32 * i + j) % 32 = j := by omega
  have e3 : (32 * j + i) / 32 = j := by omega
  have e4 : (32 * j + i) % 32 = i := by omega
  have hu : upA.testBit (32 * j + i) = false := by
    rw [CFSG.KC.KDense.InitAux.upA_bits _ (by omega), e3, e4]
    simp only [decide_eq_false_iff_not]
    omega
  have hd : diagA.testBit (32 * i + j) = false := by
    rw [diagA_bits (32 * i + j) (by omega), e1, e2]
    simp only [decide_eq_false_iff_not]
    omega
  unfold ANg
  rw [res_lor_r hq (zero_land_rep hO diagA_lt hq hd),
    res_lor_l hq (transp_zero hO (by omega) (by rw [e1, e2]; exact hUz _ hq' hu))]

theorem ANg_low {i j : ℕ} (hij : j < i) (hi : i < 24) :
    resPN np SA (ANg O A U) (32 * i + j) = resPN np SA U (32 * j + i) := by
  have hq : 32 * i + j < SA := by rw [SA_v]; omega
  have e1 : (32 * i + j) / 32 = i := by omega
  have e2 : (32 * i + j) % 32 = j := by omega
  have hu : upA.testBit (32 * i + j) = false := by
    rw [CFSG.KC.KDense.InitAux.upA_bits _ (by omega), e1, e2]
    simp only [decide_eq_false_iff_not]
    omega
  have hd : diagA.testBit (32 * i + j) = false := by
    rw [diagA_bits (32 * i + j) (by omega), e1, e2]
    simp only [decide_eq_false_iff_not]
    omega
  unfold ANg
  rw [res_lor_r hq (zero_land_rep hO diagA_lt hq hd),
    res_lor_r hq (hUz _ hq hu), transp_res hO (by omega), e1, e2]

theorem ANg_zero {p : ℕ} (hp : p < SA) (h : 24 ≤ p % 32 ∨ 24 ≤ p / 32) :
    resPN np SA (ANg O A U) p = 0 := by
  have hpS := hp
  rw [SA_v] at hp
  have d1 : diagA.testBit p = false := by
    rw [diagA_bits _ hp]
    simp only [decide_eq_false_iff_not]
    omega
  have u1 : upA.testBit p = false := by
    rw [CFSG.KC.KDense.InitAux.upA_bits _ hp]
    simp only [decide_eq_false_iff_not]
    omega
  have e3 : (32 * (p % 32) + p / 32) / 32 = p % 32 := by omega
  have e4 : (32 * (p % 32) + p / 32) % 32 = p / 32 := by omega
  have hp'' : 32 * (p % 32) + p / 32 < 1024 := by omega
  have hp' : 32 * (p % 32) + p / 32 < SA := hp''
  have u2 : upA.testBit (32 * (p % 32) + p / 32) = false := by
    rw [CFSG.KC.KDense.InitAux.upA_bits _ hp'', e3, e4]
    simp only [decide_eq_false_iff_not]
    omega
  unfold ANg
  exact res_of_zero (zero_lor (zero_land_rep hO diagA_lt hpS d1)
    (zero_lor (hUz _ hpS u1) (transp_zero hO hp (hUz _ hp' u2))))

end NewA

theorem octComp2 {K n : ℕ} (hn : n < 64) (h : ZMod K) (r : ℕ → ZMod K) :
    ∑ m ∈ Finset.range 64, ((octMI n m : ℤ) : ZMod K) *
      (h * ∑ l ∈ Finset.range 64, ((octMI m l : ℤ) : ZMod K) * r l) =
    h * 8 * ∑ l ∈ Finset.range 64, ((octMI l n : ℤ) : ZMod K) * r l := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hc : ∑ m ∈ Finset.range 64, ((octMI n m : ℤ) : ZMod K) * ((octMI m l : ℤ) : ZMod K) =
      8 * ((octMI l n : ℤ) : ZMod K) := by
    have := congrArg (Int.cast : ℤ → ZMod K) (octMI_sq hn (Finset.mem_range.1 hl))
    push_cast at this
    exact this
  rw [show ∑ m ∈ Finset.range 64, ((octMI n m : ℤ) : ZMod K) * (h * (((octMI m l : ℤ) : ZMod K) * r l)) =
      h * r l * ∑ m ∈ Finset.range 64, ((octMI n m : ℤ) : ZMod K) * ((octMI m l : ℤ) : ZMod K) by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring, hc]
  ring

section NewI

variable (hO : PLaw np O) {F : Fix} (h6 : pi6OK F = true) (hm : tauMasksOK F = true) {X A W : ℕ}
  (hX : Bd np SX X) (hA : Bd np SA A) (hW : Bd np SX W)
include hO h6 hm hX hA hW

local notation "XI" => Nat.lor (nhi O (rowF gU 2048) W) (Nat.lor (octI O F X)
  (Nat.lor (T3i O X A) (T4i O X A)))

theorem XI_bd : Bd np SX XI :=
  bd_lor (nhi_bd hO gU_lt' hW) (bd_lor (octI_bd hO h6 hm hX) (bd_lor (T3i_bd hO hA) (T4i_bd hO hA)))

theorem XI_lo {p : ℕ} (hp : p < 65536) : resPN np SX XI p = resPN np SX (nhi O (rowF gU 2048) W) p := by
  have hpS : p < SX := by rw [SX_v]; omega
  exact res_lor_l hpS (zero_lor (octI_zero hO h6 hm hX hpS (by omega))
    (zero_lor (T3i_zero hO hA hpS (by omega)) (T4i_zero hO hA hpS (by omega))))

theorem XI_oct {p : ℕ} (h1 : 65536 ≤ p) (h2 : p < 114112) :
    resPN np SX XI p = resPN np SX (octI O F X) p := by
  have hpS : p < SX := by rw [SX_v]; omega
  rw [res_lor_r hpS (nhi_zero hO gU_lt' hW hpS h1)]
  exact res_lor_l hpS (zero_lor (T3i_zero hO hA hpS (by omega)) (T4i_zero hO hA hpS (by omega)))

theorem XI_B {p : ℕ} (h1 : 114688 ≤ p) (h2 : p < 115712) :
    resPN np SX XI p = resPN np SX (T3i O X A) p := by
  have hpS : p < SX := by rw [SX_v]; omega
  rw [res_lor_r hpS (nhi_zero hO gU_lt' hW hpS (by omega)),
    res_lor_r hpS (octI_zero hO h6 hm hX hpS (by omega))]
  exact res_lor_l hpS (T4i_zero hO hA hpS (by omega))

theorem XI_C {p : ℕ} (h1 : 115712 ≤ p) (h2 : p < 116736) :
    resPN np SX XI p = resPN np SX (T4i O X A) p := by
  have hpS : p < SX := by rw [SX_v]; omega
  rw [res_lor_r hpS (nhi_zero hO gU_lt' hW hpS (by omega)),
    res_lor_r hpS (octI_zero hO h6 hm hX hpS (by omega))]
  exact res_lor_r hpS (T3i_zero hO hA hpS (by omega))

theorem XI_zero {p : ℕ} (hp : p < SX) (h0 : 65536 ≤ p) (h1 : ¬ (65536 ≤ p ∧ p < 114112))
    (h3 : ¬ (114688 ≤ p ∧ p < 115712 ∧ upA.testBit (p - 114688) = true))
    (h4 : ¬ (115712 ≤ p ∧ p < 116736 ∧ upA.testBit (p - 115712) = true)) :
    resPN np SX XI p = 0 :=
  res_of_zero (zero_lor (nhi_zero hO gU_lt' hW hp h0) (zero_lor (octI_zero hO h6 hm hX hp h1)
    (zero_lor (T3i_zero hO hA hp h3) (T4i_zero hO hA hp h4))))

local notation "WI" => Nat.lor (nlo O (rowF gL 2048) X)
  (Nat.shiftLeft (nlo O (rowF gH 2048) W) (nat_lit 65536))

theorem WI_bd : Bd np SX WI := bd_lor (nlo_bd hO gL_lt' hX) (nloS_bd hO gH_lt' hW)

theorem WI_lo {p : ℕ} (hp : p < 65536) : resPN np SX WI p = resPN np SX (nlo O (rowF gL 2048) X) p :=
  res_lor_l (by rw [SX_v]; omega) (nloS_zero hO gH_lt' hW hp)

theorem WI_hi {p : ℕ} (hp : p < SX) (h : 65536 ≤ p) :
    resPN np SX WI p = resPN np SX (nlo O (rowF gH 2048) W) (p - 65536) := by
  rw [res_lor_r hp (nlo_zero hO gL_lt' hX hp h), nloS_res hO gH_lt' hW hp, if_pos h]

end NewI

end TauInvAux

theorem tauInv_sound {np : ℕ} {O : POps} (hO : PLaw np O) (hnp : 2 ≤ np) {F : Fix}
    (h6 : pi6OK F = true) (hm : tauMasksOK F = true) {v : Native.DVec} {t : St}
    (ht : RepN np v t) (f : Bool) :
    RepN np (Native.applyGen (Native.mkCtx ()) .tau (Native.applyGen (Native.mkCtx ()) .tau v))
      (f, tauInvG O F t.2.1 t.2.2.1 t.2.2.2) := by
  open TauAux TauInvAux CFSG.KC.KDense.InitAux in
  obtain ⟨f0, X, A, W⟩ := t
  obtain ⟨hX1, hX2, hXb, hA1, hA2, hAb, hW1, hW2, hWb⟩ := ht
  dsimp only at hX1 hX2 hXb hA1 hA2 hAb hW1 hW2 hWb
  change Bd np SX X at hXb
  change Bd np SA A at hAb
  change Bd np SX W at hWb
  have h2 := h2_of (np := np) (by omega)
  have c8 : hN np ^ 3 * 8 = 1 := by linear_combination (4 * hN np ^ 2 + 2 * hN np + 1) * h2
  have c64 : hN np ^ 6 * 64 = 1 := by linear_combination (hN np ^ 3 * 8 + 1) * c8
  have c32 : hN np ^ 6 * 32 = hN np := by linear_combination hN np * c64 - 32 * hN np ^ 6 * h2
  have hnat1 : ∀ k < 196884, resN np (Native.applyGen (Native.mkCtx ()) .tau v) k =
      hN np ^ 3 * tsum (resN np v) k := fun k hk => applyTau_res h2 _ v hk
  have hnat2 : ∀ k < 196884, resN np (Native.applyGen (Native.mkCtx ()) .tau
      (Native.applyGen (Native.mkCtx ()) .tau v)) k =
      hN np ^ 3 * tsum (resN np (Native.applyGen (Native.mkCtx ()) .tau v)) k :=
    fun k hk => applyTau_res h2 _ _ hk
  have hU := UUi_bd hO (X := X)
  have hUz : ∀ q < SA, upA.testBit q = false → Zero np SA (UUi O X) q := fun q hq hu => UUi_zero hO hq hu
  rw [tauInvG_eq, (masks_spec hm).2.1, (masks_spec hm).2.2.1, (masks_spec hm).2.2.2]
  refine ⟨fun q hq => ?_, fun p hp hq => ?_, XI_bd hO h6 hm hXb hAb hWb, fun i hi j hj => ?_,
    fun p hp hq => ANg_zero hO hAb hU hUz hp hq, ANg_bd hO hAb hU hUz, fun r hr j hj => ?_,
    fun p hp hq => ?_, WI_bd hO h6 hm hXb hAb hWb⟩
  ·
    rw [hnat2 _ (by omega)]
    rcases Nat.lt_or_ge q 552 with h1 | h1
    · obtain ⟨tp, htp, rfl | rfl⟩ : ∃ tp, tp < 276 ∧ (q = 2 * tp ∨ q = 2 * tp + 1) :=
        ⟨q / 2, by omega, by omega⟩
      all_goals
        obtain ⟨o1, o2⟩ := pairTab_ok tp htp
        have hpi := pairTab_idx2 tp htp
        have ex := xposK_even htp
        have ex1 := xposK_odd' htp
        generalize (Native.pairTab ())[tp]! = ij at o1 o2 hpi ex ex1
        obtain ⟨i, j⟩ := ij
        dsimp only at o1 o2 hpi ex ex1
        have e1 : (32 * i + j) / 32 = i := by omega
        have e2 : (32 * i + j) % 32 = j := by omega
        have hua : upA.testBit (32 * i + j) = true := by
          rw [upA_bits _ (by omega), e1, e2]
          simp only [decide_eq_true_eq]
          omega
        have hxa : resPN np SX X (114688 + (32 * i + j)) = resN np v (300 + 2 * tp) := by
          rw [← Nat.add_assoc, ← ex]
          exact hX1 _ (by omega)
        have hxb : resPN np SX X (115712 + (32 * i + j)) = resN np v (300 + 2 * tp + 1) := by
          rw [← Nat.add_assoc, ← ex1, hX1 _ (by omega)]
          rfl
        have haa : resPN np SA A (32 * i + j) = resN np v (24 + tp) := by
          rw [hA1 i (by omega) j o2, aIdx_pair o1, hpi]
        have hd := dd2i_res hO hXb (q := 32 * i + j) (by rw [SA_v]; omega)
        rw [hxa, hxb] at hd
        have s3 : 114688 + 32 * i + j - 114688 = 32 * i + j := by
          rw [Nat.add_assoc, Nat.add_sub_cancel_left]
        have s4 : 115712 + 32 * i + j - 115712 = 32 * i + j := by
          rw [Nat.add_assoc, Nat.add_sub_cancel_left]
        have hua3 : upA.testBit (114688 + 32 * i + j - 114688) = true := by rw [s3]; exact hua
        have hua4 : upA.testBit (115712 + 32 * i + j - 115712) = true := by rw [s4]; exact hua
      · rw [ex, XI_B hO h6 hm hXb hAb hWb (by omega) (by omega),
          T3i_res hO hAb (by omega) (by omega) hua3, s3, haa, hd, tsum_pairX _ htp,
          hnat1 (24 + tp) (by omega), hnat1 (300 + 2 * tp) (by omega),
          hnat1 (300 + 2 * tp + 1) (by omega), tsum_pairA _ htp, tsum_pairX _ htp, tsum_pairX1 _ htp]
        linear_combination (-(resN np v (24 + tp))) * c64 -
          (resN np v (300 + 2 * tp) + resN np v (300 + 2 * tp + 1)) * c32
      · rw [ex1, XI_C hO h6 hm hXb hAb hWb (by omega) (by omega),
          T4i_res hO hAb (by omega) (by omega) hua4, s4, haa, hd,
          show 300 + (2 * tp + 1) = 300 + 2 * tp + 1 by omega, tsum_pairX1 _ htp,
          hnat1 (24 + tp) (by omega), hnat1 (300 + 2 * tp) (by omega),
          hnat1 (300 + 2 * tp + 1) (by omega), tsum_pairA _ htp, tsum_pairX _ htp, tsum_pairX1 _ htp]
        linear_combination (-(resN np v (24 + tp))) * c64 +
          (resN np v (300 + 2 * tp) + resN np v (300 + 2 * tp + 1)) * c32
    rcases Nat.lt_or_ge q 49704 with h2' | h2'
    · obtain ⟨t, i, ht, hi, rfl⟩ : ∃ t i, t < 2048 ∧ i < 24 ∧ q = 552 + 24 * t + i :=
        ⟨(q - 552) / 24, (q - 552) % 24, by omega, by omega, by omega⟩
      rw [xposK_oddc ht hi, XI_lo hO h6 hm hXb hAb hWb (by omega), nhi_res hO gU_lt' hWb (by omega),
        rowF_lo (g := gU) gU_lt' ht hi, gU_bit ht i,
        show 32 * t + i + 65536 = 32 * (2048 + t) + i by omega, hW1 (2048 + t) (by omega) i hi,
        show 300 + (552 + 24 * t + i) = 852 + 24 * t + i by omega, tsum_odd _ ht hi,
        hnat1 (98580 + 24 * t + i) (by omega), tsum_Wlo _ ht hi, tb_w ht, tb_pb ht]
      push_cast [sgn_cast]
      cases (wordN (2 * t)).testBit i <;> cases pN (2 * t)
      · simp only [Bool.false_eq_true, if_false]
        linear_combination (-(resN np v (98580 + 24 * (2048 + t) + i))) * c64
      · simp only [Bool.false_eq_true, if_false, if_true]
        linear_combination (-(resN np v (98580 + 24 * (2048 + t) + i))) * c64
      · simp only [Bool.false_eq_true, if_false, if_true]
        linear_combination (resN np v (98580 + 24 * (2048 + t) + i)) * c64
      · simp only [if_true]
        linear_combination (resN np v (98580 + 24 * (2048 + t) + i)) * c64
    · obtain ⟨o, n, ho, hn, rfl⟩ : ∃ o n, o < 759 ∧ n < 64 ∧ q = 49704 + 64 * o + n :=
        ⟨(q - 49704) / 64, (q - 49704) % 64, by omega, by omega, by omega⟩
      rw [xposK_oct ho hn, XI_oct hO h6 hm hXb hAb hWb (by omega) (by omega),
        octI_res hO h6 hm hXb (by omega) (by omega) hn,
        show 300 + (49704 + 64 * o + n) = 50004 + 64 * o + n by omega, tsum_oct _ ho hn]
      have hL : ∀ c ∈ Finset.range 64, ((if POCT.testBit c then -Kz 6 (phi6 c) n else Kz 6 (phi6 c) n : ℤ) :
          ZMod (2 ^ np - 1)) * resPN np SX X (64 * (1024 + o) + c) =
          ((octMI c n : ℤ) : ZMod (2 ^ np - 1)) * resN np v (50004 + 64 * o + c) := fun c hc => by
        have hx := hX1 (49704 + 64 * o + c) (by simp only [Finset.mem_range] at hc; omega)
        rw [xposK_oct ho (Finset.mem_range.1 hc),
          show 300 + (49704 + 64 * o + c) = 50004 + 64 * o + c by omega] at hx
        rw [hx]
        rfl
      have hR : ∀ m ∈ Finset.range 64, ((tb.S[m * 64 + n]! : ℤ) : ZMod (2 ^ np - 1)) *
          resN np (Native.applyGen (Native.mkCtx ()) .tau v) (50004 + 64 * o + m) =
          ((octMI n m : ℤ) : ZMod (2 ^ np - 1)) * (hN np ^ 3 * ∑ l ∈ Finset.range 64,
            ((octMI m l : ℤ) : ZMod (2 ^ np - 1)) * resN np v (50004 + 64 * o + l)) := fun m hm' => by
        have hm2 := Finset.mem_range.1 hm'
        have hS : ∀ a < 64, ∀ b < 64, (tb.S[a * 64 + b]! : ℤ) = octMI b a := fun a ha b hb => by
          rw [tb_S (by omega), show (a * 64 + b) / 64 = a by omega, show (a * 64 + b) % 64 = b by omega,
            evenTab_get a ha, evenTab_get b hb, ← oct_matrix b hb a ha]
          rfl
        rw [hnat1 _ (by omega), tsum_oct _ ho hm2, hS m hm2 n hn,
          Finset.sum_congr rfl fun l hl => by rw [hS l (Finset.mem_range.1 hl) m hm2]]
      rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR, octComp2 hn]
      generalize (∑ l ∈ Finset.range 64, ((octMI l n : ℤ) : ZMod (2 ^ np - 1)) *
        resN np v (50004 + 64 * o + l)) = S
      linear_combination (-(hN np ^ 3 * S)) * c8
  ·
    have hv : validX.testBit p = false := by
      cases h : validX.testBit p
      · rfl
      · obtain ⟨q, hq', e⟩ := xposK_of_mem h
        exact absurd e (hq q hq')
    have hvx := testBit_validX p
    rw [hv] at hvx
    simp only [Bool.false_eq_true, false_iff] at hvx
    rcases Nat.lt_or_ge p 65536 with h1 | h1
    · rw [XI_lo hO h6 hm hXb hAb hWb h1, nhi_res hO gU_lt' hWb h1,
        hW2 (p + 65536) (by rw [SX_v]; omega) (by omega)]
      split_ifs <;> simp
    · refine XI_zero hO h6 hm hXb hAb hWb hp h1 (fun h => hvx (Or.inr (Or.inl h))) ?_ ?_
      · rintro ⟨a, b, c⟩
        rw [upA_bits _ (by omega)] at c
        simp only [decide_eq_true_eq] at c
        exact hvx (Or.inr (Or.inr (Or.inl ⟨a, by omega, c.1, c.2⟩)))
      · rintro ⟨a, b, c⟩
        rw [upA_bits _ (by omega)] at c
        simp only [decide_eq_true_eq] at c
        exact hvx (Or.inr (Or.inr (Or.inr ⟨a, by omega, c.1, c.2⟩)))
  ·
    rw [hnat2 _ (by have := aIdx_lt i hi j hj; omega)]
    rcases lt_trichotomy i j with hij | rfl | hij
    · obtain ⟨htp, hpt⟩ := pairTab_idx i hi j hj hij
      have ex := xposK_even htp
      have ex1 := xposK_odd' htp
      rw [hpt] at ex ex1
      dsimp only at ex ex1
      have e1 : (32 * i + j) / 32 = i := by omega
      have e2 : (32 * i + j) % 32 = j := by omega
      have hua : upA.testBit (32 * i + j) = true := by
        rw [upA_bits _ (by omega), e1, e2]
        simp only [decide_eq_true_eq]
        omega
      rw [ANg_up hO hAb hU hUz hij hj, UUi_res hO hXb (by rw [SA_v]; omega), hua, if_pos rfl,
        ← Nat.add_assoc, ← Nat.add_assoc, ← ex, ← ex1, hX1 _ (by omega), hX1 _ (by omega),
        aIdx_pair hij, tsum_pairA _ htp, show 300 + (2 * Native.pairIdx i j + 1) =
          300 + 2 * Native.pairIdx i j + 1 by omega,
        hnat1 (300 + 2 * Native.pairIdx i j) (by omega),
        hnat1 (300 + 2 * Native.pairIdx i j + 1) (by omega), tsum_pairX _ htp, tsum_pairX1 _ htp]
      linear_combination (-(resN np v (300 + 2 * Native.pairIdx i j) -
        resN np v (300 + 2 * Native.pairIdx i j + 1))) * c32
    · rw [ANg_diag hO hAb hU hUz hi, hA1 i hi i hi, show Native.aIdx i i = i by simp [Native.aIdx],
        tsum_diag _ hi, hnat1 i (by omega), tsum_diag _ hi]
      linear_combination (-(resN np v i)) * c64
    · obtain ⟨htp, hpt⟩ := pairTab_idx j hj i hi hij
      have ex := xposK_even htp
      have ex1 := xposK_odd' htp
      rw [hpt] at ex ex1
      dsimp only at ex ex1
      have e1 : (32 * j + i) / 32 = j := by omega
      have e2 : (32 * j + i) % 32 = i := by omega
      have hua : upA.testBit (32 * j + i) = true := by
        rw [upA_bits _ (by omega), e1, e2]
        simp only [decide_eq_true_eq]
        omega
      rw [ANg_low hO hAb hU hUz hij hi, UUi_res hO hXb (by rw [SA_v]; omega), hua, if_pos rfl,
        ← Nat.add_assoc, ← Nat.add_assoc, ← ex, ← ex1, hX1 _ (by omega), hX1 _ (by omega),
        CFSG.KC.KDenseP.ListAux.aIdx_comm i hi j hj, aIdx_pair hij, tsum_pairA _ htp,
        show 300 + (2 * Native.pairIdx j i + 1) = 300 + 2 * Native.pairIdx j i + 1 by omega,
        hnat1 (300 + 2 * Native.pairIdx j i) (by omega),
        hnat1 (300 + 2 * Native.pairIdx j i + 1) (by omega), tsum_pairX _ htp, tsum_pairX1 _ htp]
      linear_combination (-(resN np v (300 + 2 * Native.pairIdx j i) -
        resN np v (300 + 2 * Native.pairIdx j i + 1))) * c32
  ·
    rw [hnat2 _ (by omega)]
    rcases Nat.lt_or_ge r 2048 with hr' | hr'
    · have hx := hX1 (552 + 24 * r + j) (by omega)
      rw [xposK_oddc hr' hj, show 300 + (552 + 24 * r + j) = 852 + 24 * r + j by omega] at hx
      rw [WI_lo hO h6 hm hXb hAb hWb (by omega), nlo_res hO gL_lt' hXb (by omega),
        rowF_lo (g := gL) gL_lt' hr' hj, gL_bit hr' hj, hx,
        tsum_Wlo _ hr' hj, hnat1 (98580 + 24 * (2048 + r) + j) (by omega), tsum_Whi _ hr' hj,
        tb_w hr', tb_pb hr']
      push_cast [sgn_cast]
      cases (wordN (2 * r)).testBit j <;> cases pN (2 * r)
      · simp only [Bool.false_eq_true, if_false]
        linear_combination (-(resN np v (852 + 24 * r + j))) * c64
      · simp only [Bool.false_eq_true, if_false, if_true]
        linear_combination (resN np v (852 + 24 * r + j)) * c64
      · simp only [Bool.false_eq_true, if_false, if_true]
        linear_combination (-(resN np v (852 + 24 * r + j))) * c64
      · simp only [if_true]
        linear_combination (resN np v (852 + 24 * r + j)) * c64
    · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 2048 ∧ r = 2048 + t := ⟨r - 2048, by omega, by omega⟩
      rw [WI_hi hO h6 hm hXb hAb hWb (by rw [SX_v]; omega) (by omega),
        show 32 * (2048 + t) + j - 65536 = 32 * t + j by omega, nlo_res hO gH_lt' hWb (by omega),
        rowF_lo (g := gH) gH_lt' ht hj, gH_bit ht hj, hW1 t (by omega) j hj,
        tsum_Whi _ ht hj, hnat1 (852 + 24 * t + j) (by omega), tsum_odd _ ht hj, tb_w ht, tb_pb ht]
      push_cast [sgn_cast]
      cases (wordN (2 * t)).testBit j <;> cases pN (2 * t)
      · simp only [Bool.false_eq_true, if_false, Bool.xor_false]
        linear_combination (-(resN np v (98580 + 24 * t + j))) * c64
      · simp only [Bool.false_eq_true, if_false, if_true, Bool.false_xor]
        linear_combination (resN np v (98580 + 24 * t + j)) * c64
      · simp only [Bool.false_eq_true, if_false, if_true, Bool.xor_false]
        linear_combination (resN np v (98580 + 24 * t + j)) * c64
      · simp only [if_true, Bool.xor_self, Bool.false_eq_true, if_false]
        linear_combination (-(resN np v (98580 + 24 * t + j))) * c64
  ·
    rcases Nat.lt_or_ge p 65536 with h1 | h1
    · have hv : validX.testBit p = false := by
        cases h : validX.testBit p
        · rfl
        · rw [testBit_validX] at h
          omega
      rw [WI_lo hO h6 hm hXb hAb hWb h1, nlo_res hO gL_lt' hXb h1,
        hX2 p (by rw [SX_v]; omega) (not_xpos hv)]
      split_ifs <;> simp
    · rw [WI_hi hO h6 hm hXb hAb hWb hp h1, nlo_res hO gH_lt' hWb (by rw [SX_v] at hp; omega),
        hW2 (p - 65536) (by rw [SX_v] at hp ⊢; omega) (by omega)]
      split_ifs <;> simp

end CFSG.KC.KStep

end
