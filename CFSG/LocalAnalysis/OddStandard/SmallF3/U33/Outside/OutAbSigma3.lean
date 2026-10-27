module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutFpf
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutDefs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup

variable {T : Type} [Group T] [Finite T] {ρ x : MulAut T}

private theorem rho_cube (hρ : ρ ^ 3 = 1) (g : T) : ρ (ρ (ρ g)) = g := by
  have h := congrArg (fun f : MulAut T => f g) hρ
  simpa [pow_succ, MulAut.mul_apply] using h

private theorem rho_inv_apply (hρ : ρ ^ 3 = 1) (g : T) : ρ⁻¹ g = ρ (ρ g) := by
  have h2 : ρ * ρ ^ 2 = 1 := by
    have h := hρ
    rw [pow_three] at h
    simpa [pow_two] using h
  have hρinv : ρ⁻¹ = ρ ^ 2 := inv_eq_of_mul_eq_one_right h2
  rw [hρinv, pow_two, MulAut.mul_apply]

private theorem apply_apply_self (hx : x * x = 1) (g : T) : x (x g) = g := by
  have h := congrArg (fun f : MulAut T => f g) hx
  simpa [MulAut.mul_apply] using h

private theorem apply_rho (hxρ : x * ρ * x⁻¹ = ρ⁻¹) (g : T) :
    x (ρ g) = ρ⁻¹ (x g) := by
  have h : x * ρ = ρ⁻¹ * x := by
    calc x * ρ = x * ρ * x⁻¹ * x := by rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = ρ⁻¹ * x := by rw [hxρ]
  have h' := congrArg (fun f : MulAut T => f g) h
  simpa [MulAut.mul_apply] using h'

private theorem mul_comm_of_mem_exp2 (N : Subgroup T) (hN2 : ∀ n ∈ N, n * n = 1)
    {a b : T} (ha : a ∈ N) (hb : b ∈ N) : a * b = b * a := by
  have hab : a * b ∈ N := mul_mem ha hb
  have h1 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hN2 (a * b) hab)
  have h2 : (a * b)⁻¹ = b⁻¹ * a⁻¹ := mul_inv_rev a b
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hN2 a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hN2 b hb)
  rw [h1, hb', ha'] at h2
  exact h2

private theorem rho_inv_eq_mul_rho (N : Subgroup T) (hN2 : ∀ n ∈ N, n * n = 1)
    (hNρ : ∀ n ∈ N, ρ n ∈ N) (hρ : ρ ^ 3 = 1)
    (hfpf : ∀ g : T, ρ g = g → g = 1) {b : T} (hb : b ∈ N) :
    ρ⁻¹ b = b * ρ b := by
  have hbρ : ρ b ∈ N := hNρ b hb
  have hbb : b * ρ b ∈ N := mul_mem hb hbρ
  have hburn : b * ρ b * ρ (ρ b) = 1 := forall_mul_rho_rho_sq ρ hρ hfpf b
  have h1 : ρ (ρ b) = (b * ρ b)⁻¹ := (inv_eq_of_mul_eq_one_right hburn).symm
  have h2 : (b * ρ b)⁻¹ = b * ρ b := inv_eq_of_mul_eq_one_right (hN2 (b * ρ b) hbb)
  rw [rho_inv_apply hρ b, h1, h2]

theorem eq_one_of_fix_eq_rho (hρ : ρ ^ 3 = 1) (hfpf : ∀ g : T, ρ g = g → g = 1)
    (hx : x * x = 1) (hxρ : x * ρ * x⁻¹ = ρ⁻¹) {a b : T} (ha : x a = a) (hb : x b = b)
    (hab : a = ρ b) : a = 1 := by
  have h1 : a = ρ⁻¹ b := by
    calc a = x a := ha.symm
      _ = x (ρ b) := by rw [hab]
      _ = ρ⁻¹ (x b) := apply_rho hxρ b
      _ = ρ⁻¹ b := by rw [hb]
  have h2 : ρ b = ρ⁻¹ b := hab.symm.trans h1
  have hρinvb : ρ (ρ⁻¹ b) = b := by
    calc ρ (ρ⁻¹ b) = (ρ * ρ⁻¹) b := by rw [MulAut.mul_apply]
      _ = (1 : MulAut T) b := by rw [mul_inv_cancel]
      _ = b := rfl
  have h3 : ρ (ρ b) = b := by
    calc ρ (ρ b) = ρ (ρ⁻¹ b) := by rw [h2]
      _ = b := hρinvb
  have h4 : ρ (ρ (ρ b)) = ρ b := by rw [h3]
  have h5 : b = ρ b := by
    rw [rho_cube hρ b] at h4
    exact h4
  have hb1 : b = 1 := hfpf b h5.symm
  calc a = ρ b := hab
    _ = ρ 1 := by rw [hb1]
    _ = 1 := map_one ρ

theorem exists_decomp_fix (N : Subgroup T) (hN2 : ∀ n ∈ N, n * n = 1)
    (hNρ : ∀ n ∈ N, ρ n ∈ N) (hNx : ∀ n ∈ N, x n ∈ N) (hρ : ρ ^ 3 = 1)
    (hfpf : ∀ g : T, ρ g = g → g = 1) (hx : x * x = 1) (hxρ : x * ρ * x⁻¹ = ρ⁻¹) {n : T}
    (hn : n ∈ N) : ∃ a b : T, a ∈ N ∧ b ∈ N ∧ x a = a ∧ x b = b ∧ n = a * ρ b := by
  have hxn : x n ∈ N := hNx n hn
  have hbN : n * x n ∈ N := mul_mem hn hxn
  have hρbN : ρ (n * x n) ∈ N := hNρ (n * x n) hbN
  have haN : n * ρ (n * x n) ∈ N := mul_mem hn hρbN
  refine ⟨n * ρ (n * x n), n * x n, haN, hbN, ?_, ?_, ?_⟩
  · have hb_fix : x (n * x n) = n * x n := by
      calc x (n * x n) = x n * x (x n) := map_mul x n (x n)
        _ = x n * n := by rw [apply_apply_self hx n]
        _ = n * x n := mul_comm_of_mem_exp2 N hN2 hxn hn
    have hb_inv : ρ⁻¹ (n * x n) = (n * x n) * ρ (n * x n) :=
      rho_inv_eq_mul_rho N hN2 hNρ hρ hfpf hbN
    have hxn_n : x n * n = n * x n := mul_comm_of_mem_exp2 N hN2 hxn hn
    have hxn2 : x n * x n = 1 := hN2 (x n) hxn
    calc x (n * ρ (n * x n)) = x n * x (ρ (n * x n)) := map_mul x n (ρ (n * x n))
      _ = x n * ρ⁻¹ (x (n * x n)) := by rw [apply_rho hxρ (n * x n)]
      _ = x n * ρ⁻¹ (n * x n) := by rw [hb_fix]
      _ = x n * ((n * x n) * ρ (n * x n)) := by rw [hb_inv]
      _ = n * ρ (n * x n) := by
        calc x n * ((n * x n) * ρ (n * x n))
            = (x n * n) * x n * ρ (n * x n) := by group
          _ = (n * x n) * x n * ρ (n * x n) := by rw [hxn_n]
          _ = n * (x n * x n) * ρ (n * x n) := by group
          _ = n * 1 * ρ (n * x n) := by rw [hxn2]
          _ = n * ρ (n * x n) := by group
  · calc x (n * x n) = x n * x (x n) := map_mul x n (x n)
      _ = x n * n := by rw [apply_apply_self hx n]
      _ = n * x n := mul_comm_of_mem_exp2 N hN2 hxn hn
  · rw [mul_assoc, hN2 (ρ (n * x n)) hρbN, mul_one]

theorem card_eq_sq_fix (N : Subgroup T) (hN2 : ∀ n ∈ N, n * n = 1)
    (hNρ : ∀ n ∈ N, ρ n ∈ N) (hNx : ∀ n ∈ N, x n ∈ N) (hρ : ρ ^ 3 = 1)
    (hfpf : ∀ g : T, ρ g = g → g = 1) (hx : x * x = 1) (hxρ : x * ρ * x⁻¹ = ρ⁻¹) :
    Nat.card N = Nat.card ↥(N ⊓ fixSub x) ^ 2 := by
  classical
  let C : Subgroup T := N ⊓ fixSub x
  have hmemC : ∀ t : T, t ∈ C ↔ t ∈ N ∧ x t = t := by
    intro t
    simp [C, Subgroup.mem_inf]
  change Nat.card N = Nat.card ↥C ^ 2
  let f : (↥C × ↥C) → ↥N := fun p =>
    ⟨p.1.1 * ρ p.2.1,
      mul_mem ((hmemC p.1.1).mp p.1.2).1 (hNρ p.2.1 ((hmemC p.2.1).mp p.2.2).1)⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ hpq
    have hval : a * ρ b = a' * ρ b' := congrArg Subtype.val hpq
    have hax : x a = a := ((hmemC a).mp ha).2
    have hbx : x b = b := ((hmemC b).mp hb).2
    have ha'x : x a' = a' := ((hmemC a').mp ha').2
    have hb'x : x b' = b' := ((hmemC b').mp hb').2
    have hkey : a'⁻¹ * a = ρ (b' * b⁻¹) := by
      calc a'⁻¹ * a = a'⁻¹ * (a * ρ b) * (ρ b)⁻¹ := by group
        _ = a'⁻¹ * (a' * ρ b') * (ρ b)⁻¹ := by rw [hval]
        _ = ρ b' * (ρ b)⁻¹ := by group
        _ = ρ (b' * b⁻¹) := by rw [map_mul, map_inv]
    have hafix : x (a'⁻¹ * a) = a'⁻¹ * a := by
      rw [map_mul, map_inv, ha'x, hax]
    have hbfix : x (b' * b⁻¹) = b' * b⁻¹ := by
      rw [map_mul, map_inv, hb'x, hbx]
    have hone : a'⁻¹ * a = 1 :=
      eq_one_of_fix_eq_rho hρ hfpf hx hxρ hafix hbfix hkey
    have haeq : a = a' := (inv_mul_eq_one.mp hone).symm
    have hb_eq : b = b' := by
      have hρone : ρ (b' * b⁻¹) = 1 := by rw [← hkey, hone]
      have hb'eq : b' = b := mul_inv_eq_one.mp (ρ.injective (by rw [hρone, map_one]))
      exact hb'eq.symm
    exact Prod.ext (Subtype.ext haeq) (Subtype.ext hb_eq)
  have hsurj : Function.Surjective f := by
    intro n
    obtain ⟨a, b, haN, hbN, hax, hbx, hnab⟩ :=
      exists_decomp_fix N hN2 hNρ hNx hρ hfpf hx hxρ n.2
    refine ⟨(⟨a, (hmemC a).mpr ⟨haN, hax⟩⟩, ⟨b, (hmemC b).mpr ⟨hbN, hbx⟩⟩), ?_⟩
    exact Subtype.ext hnab.symm
  have hcard : Nat.card ↥N = Nat.card (↥C × ↥C) :=
    (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm
  rw [hcard, Nat.card_prod, sq]

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
