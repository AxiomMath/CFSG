module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.LinearAlgebra.Defs
public import Mathlib.GroupTheory.Nilpotent
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open CFSG.EvenSporadicStandard.HNRecog.HaradaLA

private theorem v6_add_self (v : V6) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

private theorem v6_neg (v : V6) : -v = v := by
  funext i
  exact CharTwo.neg_eq (v i)

private theorem v6_eq_of_add_eq_zero {a b : V6} (h : a + b = 0) : a = b := by
  calc a = a + 0 := (add_zero a).symm
    _ = a + (b + b) := by rw [v6_add_self b, add_zero]
    _ = (a + b) + b := by rw [add_assoc]
    _ = 0 + b := by rw [h]
    _ = b := zero_add b

private theorem bil_zero_right (x : V6) : bil x 0 = 0 := by simp [bil]

private theorem bil_zero_left (x : V6) : bil 0 x = 0 := by simp [bil]

theorem V6_fixed_zv_perp {g : Equiv.Perm V6} (hg : IsAddPerm g) (h5 : g ^ 5 = 1) (h1 : g ≠ 1)
    {zv vv : V6} (hz : g zv = zv) (hv : g vv = vv) (hzv : bil vv zv = 1) {u : V6}
    (hu : bil u zv = 0) (hgu : g u + u = 0 ∨ g u + u = zv) : u = 0 ∨ u = zv := by
  classical
  let S : AddSubgroup V6 :=
    { carrier := {x | g x = x}
      add_mem' := by
        intro x y hx hy
        have hx' : g x = x := hx
        have hy' : g y = y := hy
        show g (x + y) = x + y
        rw [hg x y, hx', hy']
      zero_mem' := by
        show g 0 = 0
        have h := hg 0 0
        simp only [zero_add] at h
        exact h.trans (v6_add_self (g 0))
      neg_mem' := by
        intro x hx
        have hx' : g x = x := hx
        show g (-x) = -x
        rw [v6_neg x]
        exact hx' }
  have hcardV : Nat.card V6 = 64 := by
    rw [Nat.card_eq_fintype_card]
    simp [V6, Fintype.card_fun, ZMod.card]
  have hcardVf : Fintype.card V6 = 64 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcardV
  let f : Function.End V6 := fun x => g x
  have hf5 : f ^ 5 ^ 1 = 1 := by
    rw [pow_one]
    change (g : V6 → V6) ^[5] = id
    have h := congrArg (fun p : Equiv.Perm V6 => (p : V6 → V6)) h5
    rwa [Equiv.Perm.coe_pow, Equiv.Perm.coe_one] at h
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 5) (n := 1) hf5
  have hfixed : Nat.card S = Fintype.card f.fixedPoints := by
    have he : S ≃ f.fixedPoints :=
      { toFun := fun x => ⟨(x : V6), x.2⟩
        invFun := fun x => ⟨(x : V6), x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (Nat.card_congr he).trans Nat.card_eq_fintype_card
  have hmodS : 64 ≡ Nat.card S [MOD 5] := by
    have h := hmod
    rw [hcardVf, ← hfixed] at h
    exact h
  have hdvd : Nat.card S ∣ 64 := by
    have h := AddSubgroup.card_addSubgroup_dvd_card S
    rwa [hcardV] at h
  have hdvd' : Nat.card S ∣ 2 ^ 6 := by
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num]
    exact hdvd
  obtain ⟨k, hk, hkS⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd'
  have hmod' : (2 : ℕ) ^ 6 ≡ 2 ^ k [MOD 5] := by
    have h := hmodS
    rw [← show (2 : ℕ) ^ 6 = 64 by norm_num, hkS] at h
    exact h
  have hk26 : k = 2 ∨ k = 6 := by
    interval_cases k
    · norm_num at hmod'
    · norm_num at hmod'
    · left; rfl
    · norm_num at hmod'
    · norm_num at hmod'
    · norm_num at hmod'
    · right; rfl
  have hcardS2 : Nat.card S = 4 ∨ Nat.card S = 64 := by
    rcases hk26 with rfl | rfl
    · left; rw [hkS]; norm_num
    · right; rw [hkS]; norm_num
  have hne64 : Nat.card S ≠ 64 := by
    intro h64
    have htop : S = ⊤ := AddSubgroup.eq_top_of_card_eq S (by rw [h64, hcardV])
    have hg1 : g = 1 :=
      Equiv.ext fun x => by
        have hx : x ∈ S := by
          rw [htop]
          exact AddSubgroup.mem_top x
        show g x = x
        exact hx
    exact h1 hg1
  have hcardS : Nat.card S = 4 := hcardS2.resolve_right hne64
  have hzv_ne_zero : zv ≠ 0 := by
    intro h
    have hb : bil vv zv = 0 := by rw [h, bil_zero_right]
    rw [hzv] at hb
    exact one_ne_zero hb
  have hvv_ne_zero : vv ≠ 0 := by
    intro h
    rw [h, bil_zero_left] at hzv
    exact zero_ne_one hzv
  have hvv_ne_zv : vv ≠ zv := by
    intro h
    rw [h, bil_self] at hzv
    exact zero_ne_one hzv
  have hzvv_ne_zero : zv + vv ≠ 0 := by
    intro h
    have hzv_eq : zv = vv := v6_eq_of_add_eq_zero h
    rw [hzv_eq, bil_self] at hzv
    exact zero_ne_one hzv
  have hzvv_ne_zv : zv + vv ≠ zv := by
    intro h
    have hvv0 : vv = 0 := by
      have h' : zv + vv = zv + 0 := by rw [add_zero]; exact h
      exact add_left_cancel h'
    exact hvv_ne_zero hvv0
  have hzvv_ne_vv : zv + vv ≠ vv := by
    intro h
    have hzv0 : zv = 0 := by
      have h' : zv + vv = 0 + vv := by rw [zero_add]; exact h
      exact add_right_cancel h'
    exact hzv_ne_zero hzv0
  have hTcard : ({0, zv, vv, zv + vv} : Finset V6).card = 4 := by
    have h1 : (0 : V6) ∉ ({zv, vv, zv + vv} : Finset V6) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hzv_ne_zero.symm, hvv_ne_zero.symm, hzvv_ne_zero.symm⟩
    have h2 : zv ∉ ({vv, zv + vv} : Finset V6) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hvv_ne_zv.symm, hzvv_ne_zv.symm⟩
    have h3 : vv ∉ ({zv + vv} : Finset V6) := by
      simp only [Finset.mem_singleton]
      exact hzvv_ne_vv.symm
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
        Finset.card_insert_of_notMem h3, Finset.card_singleton]
  have hFcard : (Finset.univ.filter (fun x : V6 => g x = x)).card = Nat.card S := by
    have he : S ≃ {x : V6 // g x = x} :=
      { toFun := fun x => ⟨(x : V6), x.2⟩
        invFun := fun x => ⟨(x : V6), x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have h1 : Nat.card S = Fintype.card {x : V6 // g x = x} :=
      (Nat.card_congr he).trans Nat.card_eq_fintype_card
    have h2 : Fintype.card {x : V6 // g x = x} =
        (Finset.univ.filter (fun x : V6 => g x = x)).card :=
      Fintype.card_subtype (fun x : V6 => g x = x)
    exact h2.symm.trans h1.symm
  have hTF : ({0, zv, vv, zv + vv} : Finset V6) ⊆
      Finset.univ.filter (fun x : V6 => g x = x) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h
    · rw [h]; exact AddSubgroup.zero_mem S
    · rw [h]; exact hz
    · rw [h]; exact hv
    · rw [h, hg zv vv, hz, hv]
  have hFTeq : Finset.univ.filter (fun x : V6 => g x = x) =
      ({0, zv, vv, zv + vv} : Finset V6) := by
    have hcard_eq : (Finset.univ.filter (fun x : V6 => g x = x)).card =
        ({0, zv, vv, zv + vv} : Finset V6).card := by
      rw [hFcard, hcardS, hTcard]
    have hcardle : (Finset.univ.filter (fun x : V6 => g x = x)).card ≤
        ({0, zv, vv, zv + vv} : Finset V6).card := le_of_eq hcard_eq
    exact (Finset.eq_of_subset_of_card_le hTF hcardle).symm
  have hmemT : ∀ {x : V6}, g x = x → x ∈ ({0, zv, vv, zv + vv} : Finset V6) := by
    intro x hx
    have hxF : x ∈ Finset.univ.filter (fun y : V6 => g y = y) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hx
    rwa [hFTeq] at hxF
  rcases hgu with h0 | hzcase
  · have hgu_eq : g u = u := v6_eq_of_add_eq_zero h0
    have hmem := hmemT hgu_eq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      rw [h] at hu
      rw [hzv] at hu
      exact one_ne_zero hu
    · exfalso
      rw [h] at hu
      rw [bil_add_left, bil_self, zero_add, hzv] at hu
      exact one_ne_zero hu
  · exfalso
    have hgu_eq : g u = u + zv := by
      calc g u = g u + 0 := (add_zero _).symm
        _ = g u + (u + u) := by rw [v6_add_self u, add_zero]
        _ = (g u + u) + u := by rw [add_assoc]
        _ = zv + u := by rw [hzcase]
        _ = u + zv := by rw [add_comm]
    have hg2 : (g ^ 2) u = u := by
      have h1 : g (g u) = u := by
        rw [hgu_eq, hg u zv, hz, hgu_eq, add_assoc, v6_add_self, add_zero]
      rw [pow_two, Equiv.Perm.mul_apply]
      exact h1
    have hg22 : ((g ^ 2) ^ 2) u = u := by
      have hstep : ((g ^ 2) ^ 2) u = (g ^ 2) ((g ^ 2) u) := by
        rw [pow_two, Equiv.Perm.mul_apply]
      rw [hstep, hg2, hg2]
    have h5decomp : g ^ 5 = g * (g ^ 2) ^ 2 := by
      rw [show (5 : ℕ) = 1 + 2 * 2 by norm_num, pow_add, pow_one, pow_mul]
    have hgu_eq_u : g u = u := by
      have h : (g ^ 5) u = g u := by
        rw [h5decomp, Equiv.Perm.mul_apply, hg22]
      rw [← h, h5]
      rfl
    have hz0 : zv = 0 := by
      rw [← hzcase, hgu_eq_u, v6_add_self]
    exact hzv_ne_zero hz0

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
