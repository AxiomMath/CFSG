module

public import CFSG.GF2Type.SmithTypeE.DMod.Code
public import CFSG.Open.TimmesfeldLargeExtraspecialMilestoneDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.DMod

open CFSG.SmithD6

abbrev V12 := (Fin 6 → ZMod 2) × (Fin 6 → ZMod 2)

abbrev q12 : V12 → ZMod 2 := CFSG.Open.timmesfeldPlusForm 6

@[expose] def B12 (x y : V12) : ZMod 2 := ∑ i, (x.1 i * y.2 i + y.1 i * x.2 i)

theorem q12_apply (x : V12) : q12 x = ∑ i, x.1 i * x.2 i := rfl

@[expose] def dec12 (x : Nat) : V12 :=
  (fun i => if x.testBit i.val then 1 else 0, fun i => if x.testBit (6 + i.val) then 1 else 0)

theorem dec12_xor (a b : Nat) : dec12 (a ^^^ b) = dec12 a + dec12 b := by
  refine Prod.ext (funext fun m => ?_) (funext fun m => ?_)
  · show bit ((a ^^^ b).testBit m.val) = bit (a.testBit m.val) + bit (b.testBit m.val)
    rw [Nat.testBit_xor, bit_xor]
  · show bit ((a ^^^ b).testBit (6 + m.val)) =
      bit (a.testBit (6 + m.val)) + bit (b.testBit (6 + m.val))
    rw [Nat.testBit_xor, bit_xor]

theorem dec12_zero : dec12 0 = 0 := by
  refine Prod.ext (funext fun m => ?_) (funext fun m => ?_) <;> simp [dec12]

theorem bit_inj : ∀ x y : Bool, bit x = bit y → x = y := by decide

theorem eq_of_dec12_eq {a b : Nat} (ha : a < 4096) (hb : b < 4096) (h : dec12 a = dec12 b) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 6
  · have h1 : bit (a.testBit i) = bit (b.testBit i) := congrFun (congrArg Prod.fst h) ⟨i, hi⟩
    exact bit_inj _ _ h1
  · by_cases hi' : i < 12
    · have h2 : bit (a.testBit (6 + (i - 6))) = bit (b.testBit (6 + (i - 6))) :=
        congrFun (congrArg Prod.snd h) ⟨i - 6, by omega⟩
      rw [show 6 + (i - 6) = i by omega] at h2
      exact bit_inj _ _ h2
    · have h12 : (4096 : Nat) ≤ 2 ^ i := by
        calc (4096 : Nat) = 2 ^ 12 := by norm_num
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha h12),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hb h12)]

theorem dec12_surj (v : V12) : ∃ c < 4096, dec12 c = v := by
  have hf : Function.Injective (fun n : Fin 4096 => dec12 n.val) := by
    intro m n hmn
    exact Fin.ext (eq_of_dec12_eq m.isLt n.isLt hmn)
  have hcard : Fintype.card (Fin 4096) = Fintype.card V12 := by
    simp [Fintype.card_prod, Fintype.card_fun, ZMod.card]
  obtain ⟨n, hn⟩ := ((Fintype.bijective_iff_injective_and_card
    (fun n : Fin 4096 => dec12 n.val)).2 ⟨hf, hcard⟩).2 v
  exact ⟨n.val, n.isLt, hn⟩

@[expose] noncomputable def enc12 (v : V12) : Nat := Classical.choose (dec12_surj v)

theorem enc12_lt (v : V12) : enc12 v < 4096 := (Classical.choose_spec (dec12_surj v)).1

theorem dec12_enc12 (v : V12) : dec12 (enc12 v) = v := (Classical.choose_spec (dec12_surj v)).2

theorem enc12_dec12 {c : Nat} (hc : c < 4096) : enc12 (dec12 c) = c :=
  eq_of_dec12_eq (enc12_lt _) hc (dec12_enc12 _)

theorem par6_eq_fold : ∀ x : Fin 64,
    par6 x.val = (List.range 6).foldl (fun acc k => acc ^^ x.val.testBit k) false := by
  decide

theorem bit_par6 {x : Nat} (hx : x < 64) :
    bit (par6 x) = ∑ k ∈ Finset.range 6, bit (x.testBit k) := by
  have h : par6 x = (List.range 6).foldl (fun acc k => acc ^^ x.testBit k) false :=
    par6_eq_fold ⟨x, hx⟩
  rw [h]
  exact bit_foldl (fun k => x.testBit k) 6

theorem bit_par6_pair (x y : Nat) :
    bit (par6 ((x &&& 63) &&& (y >>> 6))) =
      ∑ k ∈ Finset.range 6, bit (x.testBit k) * bit (y.testBit (6 + k)) := by
  have hm : (x &&& 63) &&& (y >>> 6) < 64 :=
    Nat.lt_of_le_of_lt Nat.and_le_left (Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num))
  rw [bit_par6 hm]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk6 : k < 6 := Finset.mem_range.1 hk
  have h63 : ∀ j < 6, (63 : Nat).testBit j = true := by decide
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight, h63 k hk6, Bool.and_true,
    bit_and]

theorem q12_dec12 (c : Nat) : q12 (dec12 c) = bit (qf c) := by
  unfold qf
  rw [bit_par6_pair c c]
  exact Fin.sum_univ_eq_sum_range (fun k => bit (c.testBit k) * bit (c.testBit (6 + k))) 6

theorem B12_dec12 (a b : Nat) : B12 (dec12 a) (dec12 b) = bit (bf a b) := by
  unfold bf
  rw [bit_xor, bit_par6_pair a b, bit_par6_pair b a, ← Finset.sum_add_distrib]
  exact Fin.sum_univ_eq_sum_range (fun k => bit (a.testBit k) * bit (b.testBit (6 + k)) +
    bit (b.testBit k) * bit (a.testBit (6 + k))) 6

theorem zmod2_mul_self (d : ZMod 2) : d * d = d := by
  revert d
  decide

theorem B12_comm (x y : V12) : B12 x y = B12 y x := by
  unfold B12
  exact Finset.sum_congr rfl fun i _ => add_comm _ _

theorem B12_self (x : V12) : B12 x x = 0 := by
  have key : ∀ a b : ZMod 2, a * b + a * b = 0 := by decide
  unfold B12
  exact Finset.sum_eq_zero fun i _ => key _ _

theorem B12_add_left (x x' y : V12) : B12 (x + x') y = B12 x y + B12 x' y := by
  simp only [B12, Prod.fst_add, Prod.snd_add, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem B12_add_right (x y y' : V12) : B12 x (y + y') = B12 x y + B12 x y' := by
  simp only [B12, Prod.fst_add, Prod.snd_add, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem B12_smul_left (c : ZMod 2) (x y : V12) : B12 (c • x) y = c * B12 x y := by
  simp only [B12, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem B12_smul_right (c : ZMod 2) (x y : V12) : B12 x (c • y) = c * B12 x y := by
  simp only [B12, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem B12_zero_right (x : V12) : B12 x 0 = 0 := by
  simp [B12]

theorem q12_add (x y : V12) : q12 (x + y) = q12 x + q12 y + B12 x y := by
  simp only [q12_apply, B12, Prod.fst_add, Prod.snd_add, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem q12_smul (c : ZMod 2) (x : V12) : q12 (c • x) = c * q12 x := by
  simp only [q12_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    linear_combination (x.1 i * x.2 i) * zmod2_mul_self c

theorem B12_nondegenerate {x : V12} (h : ∀ y, B12 x y = 0) : x = 0 := by
  have h2 : ∀ i, x.2 i = 0 := by
    intro i
    simpa [B12, Pi.single_apply] using h (Pi.single i 1, 0)
  have h1 : ∀ i, x.1 i = 0 := by
    intro i
    simpa [B12, Pi.single_apply] using h (0, Pi.single i 1)
  exact Prod.ext (funext h1) (funext h2)

@[expose] noncomputable def B12L : LinearMap.BilinForm (ZMod 2) V12 :=
  LinearMap.mk₂ (ZMod 2) B12 B12_add_left B12_smul_left B12_add_right B12_smul_right

theorem B12L_apply (x y : V12) : B12L x y = B12 x y := rfl

theorem polar_q12 (x y : V12) : QuadraticMap.polar q12 x y = B12 x y := by
  simp only [QuadraticMap.polar, q12_add]
  ring

@[expose] noncomputable def Q12 : QuadraticForm (ZMod 2) V12 :=
  QuadraticMap.ofPolar q12
    (fun a x => by rw [q12_smul, smul_eq_mul, zmod2_mul_self])
    (fun x x' y => by simp only [polar_q12, B12_add_left])
    (fun a x y => by simp only [polar_q12, B12_smul_left, smul_eq_mul])

theorem Q12_apply (x : V12) : Q12 x = q12 x := rfl

theorem polar_Q12 (x y : V12) : QuadraticMap.polar Q12 x y = B12 x y := by
  simp only [QuadraticMap.polar, Q12_apply, q12_add]
  ring

theorem Q12_polarBilin_nondegenerate : Q12.polarBilin.Nondegenerate := by
  have hB : ∀ x y : V12, Q12.polarBilin x y = B12 x y := fun x y => by
    rw [QuadraticMap.polarBilin_apply_apply, polar_Q12]
  unfold LinearMap.Nondegenerate LinearMap.SeparatingLeft LinearMap.SeparatingRight
  refine ⟨fun x hx => B12_nondegenerate fun y => ?_, fun y hy => B12_nondegenerate fun x => ?_⟩
  · rw [← hB]
    exact hx y
  · rw [B12_comm, ← hB]
    exact hy x

end CFSG.GF2Type.SmithTypeE.DMod
