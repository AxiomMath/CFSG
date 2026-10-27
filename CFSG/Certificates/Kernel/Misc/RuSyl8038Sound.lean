module

public import Certificates.Data.Kernel.Misc.RuSyl8038
public import CFSG.Certificates.Kernel.B45PermSound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness

public section

namespace CFSG.KC.RuSyl8038

open CFSG.KC.Enum CFSG.KC.PkPow CFSG.KS CFSG.KS.Raw.Orb CFSG.Quasithin.B45Exc.Tab
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open scoped commutatorElement

section Group

variable {G : Type*} [Group G]

theorem zpow_red {g : G} (hg : g ^ 3 = 1) (m : ℤ) :
    ∃ a : ℕ, a < 3 ∧ (a : ℤ) = m % 3 ∧ g ^ m = g ^ a := by
  have e : ((m % 3).toNat : ℤ) = m % ((3 : ℕ) : ℤ) := by omega
  refine ⟨(m % 3).toNat, by omega, by omega, ?_⟩
  rw [zpow_eq_zpow_emod' m hg, ← e, zpow_natCast]

theorem nf_injective {x y z : G} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz : z ^ 3 = 1)
    (hzy : Commute z y)
    (hnf : ∀ i j k : ℕ, i < 3 → j < 3 → k < 3 → x ^ i * y ^ j * z ^ k = 1 →
      i = 0 ∧ j = 0 ∧ k = 0) :
    Function.Injective fun t : Fin 3 × Fin 3 × Fin 3 =>
      x ^ (t.1 : ℕ) * y ^ (t.2.1 : ℕ) * z ^ (t.2.2 : ℕ) := by
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ e
  simp only at e
  have e2 : x ^ (-((i' : ℕ) : ℤ)) * (x ^ (i : ℕ) * y ^ (j : ℕ) * z ^ (k : ℕ)) *
      z ^ (-((k' : ℕ) : ℤ)) * y ^ (-((j' : ℕ) : ℤ)) = 1 := by
    rw [e]
    group
  have e3 : x ^ (-((i' : ℕ) : ℤ)) * (x ^ (i : ℕ) * y ^ (j : ℕ) * z ^ (k : ℕ)) *
      z ^ (-((k' : ℕ) : ℤ)) * y ^ (-((j' : ℕ) : ℤ)) =
      x ^ (((i : ℕ) : ℤ) - (i' : ℕ)) * y ^ ((j : ℕ) : ℤ) *
        (z ^ (((k : ℕ) : ℤ) - (k' : ℕ)) * y ^ (-((j' : ℕ) : ℤ))) := by
    group
  have hc : Commute (z ^ (((k : ℕ) : ℤ) - (k' : ℕ))) (y ^ (-((j' : ℕ) : ℤ))) :=
    (hzy.zpow_left _).zpow_right _
  rw [e3, hc.eq] at e2
  have key : x ^ (((i : ℕ) : ℤ) - (i' : ℕ)) * y ^ (((j : ℕ) : ℤ) - (j' : ℕ)) *
      z ^ (((k : ℕ) : ℤ) - (k' : ℕ)) = 1 := by
    calc _ = x ^ (((i : ℕ) : ℤ) - (i' : ℕ)) * y ^ ((j : ℕ) : ℤ) *
          (y ^ (-((j' : ℕ) : ℤ)) * z ^ (((k : ℕ) : ℤ) - (k' : ℕ))) := by group
      _ = 1 := e2
  obtain ⟨a, ha, ha', hxa⟩ := zpow_red hx (((i : ℕ) : ℤ) - (i' : ℕ))
  obtain ⟨b, hb, hb', hyb⟩ := zpow_red hy (((j : ℕ) : ℤ) - (j' : ℕ))
  obtain ⟨c, hc3, hc', hzc⟩ := zpow_red hz (((k : ℕ) : ℤ) - (k' : ℕ))
  rw [hxa, hyb, hzc] at key
  obtain ⟨rfl, rfl, rfl⟩ := hnf a b c ha hb hc3 key
  have li := i.isLt
  have li' := i'.isLt
  have lj := j.isLt
  have lj' := j'.isLt
  have lk := k.isLt
  have lk' := k'.isLt
  have e1 : i = i' := Fin.ext (by omega)
  have e2 : j = j' := Fin.ext (by omega)
  have e3 : k = k' := Fin.ext (by omega)
  rw [e1, e2, e3]

theorem card_closure_eq_27 {x y : G} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (hnf : ∀ i j k : ℕ, i < 3 → j < 3 → k < 3 → x ^ i * y ^ j * ⁅x, y⁆ ^ k = 1 →
      i = 0 ∧ j = 0 ∧ k = 0) :
    Nat.card (Subgroup.closure ({x, y} : Set G)) = 27 := by
  have hz : ⁅x, y⁆ ^ 3 = 1 := by
    rw [CFSG.SectionRank.LocalWitness.commutator_pow_eq hzx, hx, commutatorElement_one_left]
  have h := CFSG.SectionRank.LocalWitness.card_closure_eq_cube (by norm_num) hx hy hzx hzy
    (nf_injective hx hy hz hzy hnf)
  rw [h]
  norm_num

end Group

abbrev Pm := Equiv.Perm (Fin 4060)

theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem sN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem bA {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> simp_all

theorem bI {c : Bool} (h : bIf(c, false, true) = true) : c = false := by
  cases c <;> simp_all

theorem prep_pc {p q : Nat} {g h : Pm} (hp : PRep 4060 12 p g) (hq : PRep 4060 12 q h) :
    PRep 4060 12 (pc p q) (g * h) :=
  prep_pcomp (by norm_num) hp hq

theorem prep_id : PRep 4060 12 (pidn 4060 12) 1 := prep_pidn (by norm_num) (by norm_num)

theorem prep_pow {Y : Nat} {y : Pm} (hY : PRep 4060 12 Y y) :
    ∀ e, PRep 4060 12 (ppw 4060 12 Y e) (y ^ e)
  | 0 => by
    rw [pow_zero]
    exact prep_id
  | e + 1 => by
    have r : ppw 4060 12 Y (e + 1) =
        strictN (ppw 4060 12 Y e) (fun q => pcomp 4060 12 (mask 12) Y q) := rfl
    rw [r, sN, pow_succ']
    exact prep_pcomp (by norm_num) hY (prep_pow hY e)

theorem eq_of_beq {A B : Nat} {a b : Pm} (hA : PRep 4060 12 A a) (hB : PRep 4060 12 B b)
    (h : Nat.beq A B = true) : a = b := by
  rw [Nat.eq_of_beq_eq_true h] at hA
  exact Equiv.ext fun x => Fin.ext ((hA x).symm.trans (hB x))

theorem ncard_eq {A : Nat} {a : Pm} (hA : PRep 4060 12 A a) :
    {p : Fin 4060 | a p = p}.ncard = nfix 4060 12 A := by
  rw [CFSG.KC.B45P.nfix_eq, fixCountA_eq (rep_unpack hA), ← Set.ncard_coe_finset]
  congr 1
  ext p
  simp [fixFinset]

theorem nz7_sound {A : Nat} {a : Pm} (hA : PRep 4060 12 A a) (h : nz7 A = true) :
    ¬ 7 ∣ {p : Fin 4060 | a p = p}.ncard := by
  unfold nz7 at h
  have h1 := Nat.ne_of_beq_eq_false (bI h)
  rw [ncard_eq hA]
  exact fun hd => h1 (Nat.mod_eq_zero_of_dvd hd)

theorem row_sound {A Z Z2 : Nat} {a z : Pm} (hA : PRep 4060 12 A a) (hZ : PRep 4060 12 Z z)
    (hZ2 : PRep 4060 12 Z2 (z * z)) (h : row A Z Z2 = true) :
    ∀ k < 3, ¬ 7 ∣ {p : Fin 4060 | (a * z ^ k) p = p}.ncard := by
  unfold row at h
  obtain ⟨h0, h12⟩ := bA h
  obtain ⟨h1, h2⟩ := bA h12
  intro k hk
  interval_cases k
  · rw [pow_zero, mul_one]
    exact nz7_sound hA h0
  · rw [pow_one]
    exact nz7_sound (prep_pc hA hZ) h1
  · rw [pow_two]
    exact nz7_sound (prep_pc hA hZ2) h2

theorem wchk_sound {W I : Nat} {w : Pm} (hW : PRep 4060 12 W w) (hI : PRep 4060 12 I 1)
    (h : wchk W I = true) : w ^ 7 = 1 ∧ ∀ p, w p ≠ p := by
  unfold wchk at h
  rw [sB] at h
  obtain ⟨h1, h2⟩ := bA h
  refine ⟨eq_of_beq (prep_pow hW 7) hI h1, fun p hp => ?_⟩
  have h0 : {q : Fin 4060 | w q = q}.ncard = 0 := by
    rw [ncard_eq hW]
    exact Nat.eq_of_beq_eq_true h2
  rw [Set.ncard_eq_zero] at h0
  have hm : p ∈ {q : Fin 4060 | w q = q} := hp
  rw [h0] at hm
  simp at hm

theorem core8038_sound {U H HI W : Nat} {u h h' w : Pm} (hU : PRep 4060 12 U u)
    (hH : PRep 4060 12 H h) (hHI : PRep 4060 12 HI h') (hW : PRep 4060 12 W w)
    (hc : core8038 U H HI W = true) :
    (u ^ 4) ^ 3 = 1 ∧ (h * u ^ 4 * h') ^ 3 = 1 ∧
      Commute ⁅u ^ 4, h * u ^ 4 * h'⁆ (u ^ 4) ∧
      Commute ⁅u ^ 4, h * u ^ 4 * h'⁆ (h * u ^ 4 * h') ∧
      (∀ i j k : ℕ, i < 3 → j < 3 → k < 3 → (i = 0 → j = 0 → k ≠ 0) →
        ¬ 7 ∣ {p : Fin 4060 |
          ((u ^ 4) ^ i * (h * u ^ 4 * h') ^ j * ⁅u ^ 4, h * u ^ 4 * h'⁆ ^ k) p = p}.ncard) ∧
      w ^ 7 = 1 ∧ ∀ p, w p ≠ p := by
  set x := u ^ 4 with hxdef
  set y := h * x * h' with hydef
  have hX : PRep 4060 12 (ppw 4060 12 U 4) x := prep_pow hU 4
  have hY : PRep 4060 12 (pc (pc H (ppw 4060 12 U 4)) HI) y := prep_pc (prep_pc hH hX) hHI
  have hX2 := prep_pc hX hX
  have hY2 := prep_pc hY hY
  unfold core8038 at hc
  simp only [sB] at hc
  obtain ⟨h1, hc⟩ := bA hc
  obtain ⟨h2, hc⟩ := bA hc
  obtain ⟨h3, hc⟩ := bA hc
  obtain ⟨h4, hc⟩ := bA hc
  obtain ⟨hz1, hc⟩ := bA hc
  obtain ⟨hz2, hc⟩ := bA hc
  obtain ⟨r10, hc⟩ := bA hc
  obtain ⟨r20, hc⟩ := bA hc
  obtain ⟨r01, hc⟩ := bA hc
  obtain ⟨r02, hc⟩ := bA hc
  obtain ⟨r11, hc⟩ := bA hc
  obtain ⟨r12, hc⟩ := bA hc
  obtain ⟨r21, hc⟩ := bA hc
  obtain ⟨r22, hw⟩ := bA hc
  have hx3 : x ^ 3 = 1 := by
    rw [pow_three]
    exact eq_of_beq (prep_pc hX hX2) prep_id h1
  have hy3 : y ^ 3 = 1 := by
    rw [pow_three]
    exact eq_of_beq (prep_pc hY hY2) prep_id h2
  have hxi : x⁻¹ = x * x := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_three', hx3]
  have hyi : y⁻¹ = y * y := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_three', hy3]
  have hZ : PRep 4060 12 (pc (pc (pc (ppw 4060 12 U 4) (pc (pc H (ppw 4060 12 U 4)) HI))
      (pc (ppw 4060 12 U 4) (ppw 4060 12 U 4)))
      (pc (pc (pc H (ppw 4060 12 U 4)) HI) (pc (pc H (ppw 4060 12 U 4)) HI))) ⁅x, y⁆ := by
    rw [commutatorElement_def, hxi, hyi]
    exact prep_pc (prep_pc (prep_pc hX hY) hX2) hY2
  have hZ2 := prep_pc hZ hZ
  have hzx : Commute ⁅x, y⁆ x := eq_of_beq (prep_pc hZ hX) (prep_pc hX hZ) h3
  have hzy : Commute ⁅x, y⁆ y := eq_of_beq (prep_pc hZ hY) (prep_pc hY hZ) h4
  refine ⟨hx3, hy3, hzx, hzy, fun i j k hi hj hk hne => ?_, wchk_sound hW prep_id hw⟩
  interval_cases i <;> interval_cases j
  · have hk0 : k ≠ 0 := hne rfl rfl
    interval_cases k
    · exact absurd rfl hk0
    · rw [pow_zero, pow_zero, one_mul, one_mul, pow_one]
      exact nz7_sound hZ hz1
    · rw [pow_zero, pow_zero, one_mul, one_mul, pow_two]
      exact nz7_sound hZ2 hz2
  · rw [pow_zero, one_mul, pow_one]
    exact row_sound hY hZ hZ2 r01 k hk
  · rw [pow_zero, one_mul, pow_two]
    exact row_sound hY2 hZ hZ2 r02 k hk
  · rw [pow_zero, mul_one, pow_one]
    exact row_sound hX hZ hZ2 r10 k hk
  · rw [pow_one, pow_one]
    exact row_sound (prep_pc hX hY) hZ hZ2 r11 k hk
  · rw [pow_one, pow_two]
    exact row_sound (prep_pc hX hY2) hZ hZ2 r12 k hk
  · rw [pow_zero, mul_one, pow_two]
    exact row_sound hX2 hZ hZ2 r20 k hk
  · rw [pow_one, pow_two]
    exact row_sound (prep_pc hX2 hY) hZ hZ2 r21 k hk
  · rw [pow_two, pow_two]
    exact row_sound (prep_pc hX2 hY2) hZ hZ2 r22 k hk

end CFSG.KC.RuSyl8038

end
