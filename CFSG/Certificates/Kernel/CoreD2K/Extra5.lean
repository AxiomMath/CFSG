module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.KD.CoreD2K

variable {X : Type*} [Group X] {z x y : X} {t : ℕ}

theorem y_mul_x_pow (hzx : z * x = x * z) (hyx : y * x = x * y * z ^ t) :
    ∀ b : ℕ, y * x ^ b = x ^ b * y * z ^ (t * b)
  | 0 => by simp
  | b + 1 => by
    have hc : z ^ (t * b) * x = x * z ^ (t * b) := ((Commute.pow_left hzx (t * b)).eq)
    calc y * x ^ (b + 1) = (y * x ^ b) * x := by rw [pow_succ, mul_assoc]
      _ = x ^ b * y * (z ^ (t * b) * x) := by rw [y_mul_x_pow hzx hyx b]; simp only [mul_assoc]
      _ = x ^ b * (y * x) * z ^ (t * b) := by rw [hc]; simp only [mul_assoc]
      _ = x ^ b * (x * y * z ^ t) * z ^ (t * b) := by rw [hyx]
      _ = x ^ (b + 1) * y * z ^ (t * (b + 1)) := by
        rw [pow_succ, Nat.mul_succ, pow_add]
        simp only [mul_assoc]
        rw [(Commute.pow_pow (Commute.refl z) t (t * b)).eq]

@[expose] def NF (z x y g : X) : Prop := ∃ a b c : ℕ, g = z ^ a * x ^ b * y ^ c

theorem nf_z_mul {g : X} (hg : NF z x y g) : NF z x y (z * g) := by
  obtain ⟨a, b, c, rfl⟩ := hg
  exact ⟨a + 1, b, c, by rw [pow_succ']; simp only [mul_assoc]⟩

theorem nf_x_mul (hzx : z * x = x * z) {g : X} (hg : NF z x y g) : NF z x y (x * g) := by
  obtain ⟨a, b, c, rfl⟩ := hg
  have hc : x * z ^ a = z ^ a * x := ((Commute.pow_left hzx a).eq).symm
  refine ⟨a, b + 1, c, ?_⟩
  calc x * (z ^ a * x ^ b * y ^ c) = (x * z ^ a) * x ^ b * y ^ c := by simp only [mul_assoc]
    _ = z ^ a * x ^ (b + 1) * y ^ c := by rw [hc, pow_succ']; simp only [mul_assoc]

theorem nf_y_mul (hzx : z * x = x * z) (hzy : z * y = y * z) (hyx : y * x = x * y * z ^ t)
    {g : X} (hg : NF z x y g) : NF z x y (y * g) := by
  obtain ⟨a, b, c, rfl⟩ := hg
  have hc : y * z ^ a = z ^ a * y := ((Commute.pow_left hzy a).eq).symm
  have hcy : z ^ (t * b) * y ^ (c + 1) = y ^ (c + 1) * z ^ (t * b) :=
    (Commute.pow_pow hzy (t * b) (c + 1)).eq
  have hcx : z ^ (t * b) * x ^ b = x ^ b * z ^ (t * b) := (Commute.pow_pow hzx (t * b) b).eq
  refine ⟨a + t * b, b, c + 1, ?_⟩
  calc y * (z ^ a * x ^ b * y ^ c) = z ^ a * (y * x ^ b) * y ^ c := by
        rw [← mul_assoc, ← mul_assoc, hc]; simp only [mul_assoc]
    _ = z ^ a * (x ^ b * y * z ^ (t * b)) * y ^ c := by rw [y_mul_x_pow hzx hyx b]
    _ = z ^ a * x ^ b * (y * (z ^ (t * b) * y ^ c)) := by simp only [mul_assoc]
    _ = z ^ a * x ^ b * (y * (y ^ c * z ^ (t * b))) := by
        rw [(Commute.pow_pow hzy (t * b) c).eq]
    _ = z ^ a * (x ^ b * (y ^ (c + 1) * z ^ (t * b))) := by rw [pow_succ']; simp only [mul_assoc]
    _ = z ^ a * (x ^ b * (z ^ (t * b) * y ^ (c + 1))) := by rw [hcy]
    _ = z ^ a * (z ^ (t * b) * x ^ b) * y ^ (c + 1) := by rw [hcx]; simp only [mul_assoc]
    _ = z ^ (a + t * b) * x ^ b * y ^ (c + 1) := by rw [pow_add z a (t * b)]; simp only [mul_assoc]

theorem nf_pow_mul {u : X} (hu : ∀ g, NF z x y g → NF z x y (u * g)) :
    ∀ (m : ℕ) {g : X}, NF z x y g → NF z x y (u ^ m * g)
  | 0, _, hg => by rw [pow_zero, one_mul]; exact hg
  | m + 1, _, hg => by rw [pow_succ', mul_assoc]; exact hu _ (nf_pow_mul hu m hg)

theorem nf_mul (hzx : z * x = x * z) (hzy : z * y = y * z) (hyx : y * x = x * y * z ^ t)
    {g h : X} (hg : NF z x y g) (hh : NF z x y h) : NF z x y (g * h) := by
  obtain ⟨a, b, c, rfl⟩ := hg
  rw [mul_assoc, mul_assoc]
  exact nf_pow_mul (fun _ h => nf_z_mul h) a
    (nf_pow_mul (fun _ h => nf_x_mul hzx h) b (nf_pow_mul (fun _ h => nf_y_mul hzx hzy hyx h) c hh))

theorem nf_one : NF z x y (1 : X) := ⟨0, 0, 0, by simp⟩

theorem inv_pow_of_pow_five {u : X} (hu : u ^ 5 = 1) (m : ℕ) : (u ^ m)⁻¹ = u ^ (4 * m) := by
  have e : m + 4 * m = 5 * m := by omega
  rw [inv_eq_iff_mul_eq_one, ← pow_add, e, pow_mul, hu, one_pow]

theorem nf_inv (hzx : z * x = x * z) (hzy : z * y = y * z) (hyx : y * x = x * y * z ^ t)
    (hz : z ^ 5 = 1) (hx : x ^ 5 = 1) (hy : y ^ 5 = 1) {g : X} (hg : NF z x y g) :
    NF z x y g⁻¹ := by
  obtain ⟨a, b, c, rfl⟩ := hg
  rw [mul_inv_rev, mul_inv_rev, inv_pow_of_pow_five hz, inv_pow_of_pow_five hx,
    inv_pow_of_pow_five hy, ← mul_one (z ^ (4 * a))]
  exact nf_pow_mul (fun _ h => nf_y_mul hzx hzy hyx h) (4 * c)
    (nf_pow_mul (fun _ h => nf_x_mul hzx h) (4 * b)
      (nf_pow_mul (fun _ h => nf_z_mul h) (4 * a) nf_one))

theorem pow_five_mod {u : X} (hu : u ^ 5 = 1) (m : ℕ) : u ^ m = u ^ (m % 5) := by
  conv_lhs => rw [← Nat.div_add_mod m 5, pow_add, pow_mul, hu, one_pow, one_mul]

@[expose] def nfk (z x y : X) (k : ℕ) : X := z ^ (k / 25) * x ^ (k / 5 % 5) * y ^ (k % 5)

theorem exists_nf_of_mem (hzx : z * x = x * z) (hzy : z * y = y * z)
    (hyx : y * x = x * y * z ^ t) (hz : z ^ 5 = 1) (hx : x ^ 5 = 1) (hy : y ^ 5 = 1)
    {S : Set X} (hS : ∀ s ∈ S, NF z x y s) {g : X} (hg : g ∈ Subgroup.closure S) :
    ∃ k < 125, g = nfk z x y k := by
  have hN : NF z x y g := by
    induction hg using Subgroup.closure_induction with
    | mem s hs => exact hS s hs
    | one => exact nf_one
    | mul _ _ _ _ h1 h2 => exact nf_mul hzx hzy hyx h1 h2
    | inv _ _ h => exact nf_inv hzx hzy hyx hz hx hy h
  obtain ⟨a, b, c, rfl⟩ := hN
  refine ⟨25 * (a % 5) + 5 * (b % 5) + c % 5, by omega, ?_⟩
  unfold nfk
  have e1 : (25 * (a % 5) + 5 * (b % 5) + c % 5) / 25 = a % 5 := by omega
  have e2 : (25 * (a % 5) + 5 * (b % 5) + c % 5) / 5 % 5 = b % 5 := by omega
  have e3 : (25 * (a % 5) + 5 * (b % 5) + c % 5) % 5 = c % 5 := by omega
  rw [e1, e2, e3, ← pow_five_mod hz, ← pow_five_mod hx, ← pow_five_mod hy]

theorem card_eq_of_nf (hzx : z * x = x * z) (hzy : z * y = y * z)
    (hyx : y * x = x * y * z ^ t) (hz : z ^ 5 = 1) (hx : x ^ 5 = 1) (hy : y ^ 5 = 1)
    {S : Set X} (hS : ∀ s ∈ S, NF z x y s) (hzS : z ∈ Subgroup.closure S)
    (hxS : x ∈ Subgroup.closure S) (hyS : y ∈ Subgroup.closure S)
    (hinj : ∀ k < 125, ∀ k' < 125, nfk z x y k = nfk z x y k' → k = k') :
    Nat.card (Subgroup.closure S) = 125 := by
  set E := Subgroup.closure S
  have hmem : ∀ k, nfk z x y k ∈ E := fun k =>
    E.mul_mem (E.mul_mem (E.pow_mem hzS _) (E.pow_mem hxS _)) (E.pow_mem hyS _)
  let f : Fin 125 → E := fun k => ⟨nfk z x y k.val, hmem k.val⟩
  have hfi : Function.Injective f := fun k k' h =>
    Fin.ext (hinj k.val k.isLt k'.val k'.isLt (congrArg Subtype.val h))
  have hfs : Function.Surjective f := fun g => by
    obtain ⟨k, hk, e⟩ := exists_nf_of_mem hzx hzy hyx hz hx hy hS g.2
    exact ⟨⟨k, hk⟩, Subtype.ext e.symm⟩
  have := Nat.card_eq_of_bijective f ⟨hfi, hfs⟩
  rw [← this, Nat.card_eq_fintype_card, Fintype.card_fin]

end CFSG.KD.CoreD2K

end
