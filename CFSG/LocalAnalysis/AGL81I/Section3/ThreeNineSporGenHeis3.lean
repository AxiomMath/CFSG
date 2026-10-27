module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenTh

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis

open CFSG.Open
open CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThFive (centGen_eq_top_of_map isElemAbelian_map
  card_map)

@[ext] structure Heis where
  a : ZMod 3
  b : ZMod 3
  c : ZMod 3
deriving DecidableEq

namespace Heis

def equivProd : Heis ≃ ZMod 3 × ZMod 3 × ZMod 3 where
  toFun u := (u.a, u.b, u.c)
  invFun v := ⟨v.1, v.2.1, v.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Heis := Fintype.ofEquiv _ equivProd.symm

instance : Mul Heis := ⟨fun u v => ⟨u.a + v.a, u.b + v.b, u.c + v.c - v.a * u.b⟩⟩
instance : One Heis := ⟨⟨0, 0, 0⟩⟩
instance : Inv Heis := ⟨fun u => ⟨-u.a, -u.b, -u.c - u.a * u.b⟩⟩

@[simp] theorem mul_a (u v : Heis) : (u * v).a = u.a + v.a := rfl
@[simp] theorem mul_b (u v : Heis) : (u * v).b = u.b + v.b := rfl
@[simp] theorem mul_c (u v : Heis) : (u * v).c = u.c + v.c - v.a * u.b := rfl
@[simp] theorem one_a : (1 : Heis).a = 0 := rfl
@[simp] theorem one_b : (1 : Heis).b = 0 := rfl
@[simp] theorem one_c : (1 : Heis).c = 0 := rfl
@[simp] theorem inv_a (u : Heis) : u⁻¹.a = -u.a := rfl
@[simp] theorem inv_b (u : Heis) : u⁻¹.b = -u.b := rfl
@[simp] theorem inv_c (u : Heis) : u⁻¹.c = -u.c - u.a * u.b := rfl

instance : Group Heis where
  mul_assoc u v w := by ext <;> simp <;> ring
  one_mul u := by ext <;> simp
  mul_one u := by ext <;> simp
  inv_mul_cancel u := by
    ext <;> simp
    ring

theorem card : Nat.card Heis = 27 := by
  rw [Nat.card_congr equivProd]
  simp

theorem mul_comm_iff (u v : Heis) : u * v = v * u ↔ v.a * u.b = u.a * v.b := by
  constructor
  · intro h
    have := congrArg Heis.c h
    simp only [mul_c] at this
    linear_combination -this
  · intro h
    ext
    · simp [add_comm]
    · simp [add_comm]
    · simp only [mul_c]
      linear_combination -h

theorem exists_smul_of_cross : ∀ a b a' b' : ZMod 3, (a ≠ 0 ∨ b ≠ 0) → a' * b = a * b' →
    ∃ s : ZMod 3, a' = s * a ∧ b' = s * b := by
  decide

theorem pow_three (u : Heis) : u ^ 3 = 1 := by
  ext <;> simp only [pow_succ, pow_zero, mul_a, mul_b, mul_c, one_a, one_b, one_c] <;> ring_nf <;>
    reduce_mod_char

theorem smul_inj : ∀ a b s s' : ZMod 3, (a ≠ 0 ∨ b ≠ 0) → s * a = s' * a → s * b = s' * b →
    s = s' := by
  decide

theorem ne_one_of_ne_zero (u : Heis) (hu : u.a ≠ 0 ∨ u.b ≠ 0) : u ≠ 1 := by
  rintro rfl
  simp at hu

@[simp] theorem pow_a (u : Heis) (n : ℕ) : (u ^ n).a = n * u.a := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_a, ih]; push_cast; ring

@[simp] theorem pow_b (u : Heis) (n : ℕ) : (u ^ n).b = n * u.b := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_b, ih]; push_cast; ring

end Heis

section Model

variable {G : Type*} [Group G] {x y z : G}

theorem pow_mod_three {g : G} (hg : g ^ 3 = 1) (n : ℕ) : g ^ n = g ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hg, one_pow, one_mul]

theorem pow_eq_pow_of_cast {g : G} (hg : g ^ 3 = 1) {m n : ℕ} (h : (m : ZMod 3) = n) :
    g ^ m = g ^ n := by
  rw [pow_mod_three hg m, pow_mod_three hg n, (ZMod.natCast_eq_natCast_iff' m n 3).mp h]

@[expose] def nf (x y z : G) (u : Heis) : G := x ^ u.a.val * y ^ u.b.val * z ^ u.c.val

variable (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz : z ^ 3 = 1) (hzx : z * x = x * z)
  (hzy : z * y = y * z) (hxy : x * y = y * z * x)

include hz hzx hxy in
theorem y_mul_x : y * x = x * y * z ^ 2 := by
  have h : x * y * z ^ 2 = y * x := by
    rw [hxy]
    calc y * z * x * z ^ 2 = y * (z * x) * z ^ 2 := by group
      _ = y * (x * z) * z ^ 2 := by rw [hzx]
      _ = y * x * z ^ 3 := by group
      _ = y * x := by rw [hz, mul_one]
  exact h.symm

include hz hzx hxy in
theorem y_mul_x_pow (m : ℕ) : y * x ^ m = x ^ m * y * z ^ (2 * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hc : Commute (z ^ (2 * m)) x := Commute.pow_left hzx _
    calc y * x ^ (m + 1) = y * x ^ m * x := by rw [pow_succ, mul_assoc]
      _ = x ^ m * y * (z ^ (2 * m) * x) := by rw [ih]; group
      _ = x ^ m * y * (x * z ^ (2 * m)) := by rw [hc.eq]
      _ = x ^ m * (y * x) * z ^ (2 * m) := by group
      _ = x ^ m * (x * y * z ^ 2) * z ^ (2 * m) := by rw [y_mul_x hz hzx hxy]
      _ = x ^ (m + 1) * y * z ^ (2 * (m + 1)) := by
        rw [pow_succ x m, show 2 * (m + 1) = 2 + 2 * m by ring, pow_add]; group

include hz hzx hzy hxy in
theorem y_pow_mul_x_pow (n m : ℕ) : y ^ n * x ^ m = x ^ m * y ^ n * z ^ (2 * n * m) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : Commute (z ^ (2 * m)) (y ^ n) := Commute.pow_pow hzy _ _
    calc y ^ (n + 1) * x ^ m = y * (y ^ n * x ^ m) := by rw [pow_succ', mul_assoc]
      _ = y * x ^ m * y ^ n * z ^ (2 * n * m) := by rw [ih]; group
      _ = x ^ m * y * (z ^ (2 * m) * y ^ n) * z ^ (2 * n * m) := by
        rw [y_mul_x_pow hz hzx hxy m]; group
      _ = x ^ m * y * (y ^ n * z ^ (2 * m)) * z ^ (2 * n * m) := by rw [hc.eq]
      _ = x ^ m * y ^ (n + 1) * z ^ (2 * (n + 1) * m) := by
        rw [pow_succ' y n, show 2 * (n + 1) * m = 2 * m + 2 * n * m by ring, pow_add]; group

include hx hy hz hzx hzy hxy in
theorem nf_mul (u v : Heis) : nf x y z (u * v) = nf x y z u * nf x y z v := by
  have hzxc : ∀ k m : ℕ, z ^ k * x ^ m = x ^ m * z ^ k := fun k m => (Commute.pow_pow hzx k m).eq
  have hzyc : ∀ k m : ℕ, z ^ k * y ^ m = y ^ m * z ^ k := fun k m => (Commute.pow_pow hzy k m).eq
  have ea : x ^ (u * v).a.val = x ^ (u.a.val + v.a.val) :=
    pow_eq_pow_of_cast hx (by simp)
  have eb : y ^ (u * v).b.val = y ^ (u.b.val + v.b.val) :=
    pow_eq_pow_of_cast hy (by simp)
  have ec : z ^ (u * v).c.val = z ^ (2 * u.b.val * v.a.val + u.c.val + v.c.val) := by
    refine pow_eq_pow_of_cast hz ?_
    have h2 : (2 : ZMod 3) = -1 := by decide
    simp only [Heis.mul_c, ZMod.natCast_val, ZMod.cast_id', id, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, h2]
    ring
  simp only [nf]
  rw [ea, eb, ec, pow_add, pow_add, pow_add, pow_add]
  set A := u.a.val
  set A' := v.a.val
  set B := u.b.val
  set B' := v.b.val
  set C := u.c.val
  set C' := v.c.val
  have E1 := hzxc C A'
  have E2 := y_pow_mul_x_pow hz hzx hzy hxy B A'
  have E3 := hzyc C B'
  have E4 := hzyc (2 * B * A') B'
  symm
  calc x ^ A * y ^ B * z ^ C * (x ^ A' * y ^ B' * z ^ C')
      = x ^ A * y ^ B * (z ^ C * x ^ A') * y ^ B' * z ^ C' := by group
    _ = x ^ A * (y ^ B * x ^ A') * (z ^ C * y ^ B') * z ^ C' := by rw [E1]; group
    _ = x ^ A * x ^ A' * y ^ B * (z ^ (2 * B * A') * y ^ B') * z ^ C * z ^ C' := by
        rw [E2, E3]; group
    _ = x ^ A * x ^ A' * (y ^ B * y ^ B') * (z ^ (2 * B * A') * z ^ C * z ^ C') := by
        rw [E4]; group

end Model

section Model2

variable {G : Type*} [Group G] {x y z : G}
  (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz : z ^ 3 = 1) (hzx : z * x = x * z)
  (hzy : z * y = y * z) (hxy : x * y = y * z * x)

@[expose] def nfHom : Heis →* G where
  toFun := nf x y z
  map_one' := by simp [nf]
  map_mul' := nf_mul hx hy hz hzx hzy hxy

include hxy in
theorem z_mem_closure : z ∈ Subgroup.closure ({x, y} : Set G) := by
  have hz' : z = y⁻¹ * (x * y) * x⁻¹ := by rw [hxy]; group
  rw [hz']
  have hx' : x ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hy' : y ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  exact mul_mem (mul_mem (inv_mem hy') (mul_mem hx' hy')) (inv_mem hx')

theorem range_nfHom :
    (nfHom hx hy hz hzx hzy hxy).range = Subgroup.closure ({x, y} : Set G) := by
  have hx' : x ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hy' : y ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    exact mul_mem (mul_mem (pow_mem hx' _) (pow_mem hy' _)) (pow_mem (z_mem_closure hxy) _)
  · rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact ⟨⟨1, 0, 0⟩, by simp [nfHom, nf, ZMod.val_one]⟩
    · exact ⟨⟨0, 1, 0⟩, by simp [nfHom, nf, ZMod.val_one]⟩

theorem nfHom_apply (u : Heis) : nfHom hx hy hz hzx hzy hxy u = nf x y z u := rfl

include hx hy hz hzx hzy hxy in
theorem card_closure (hz1 : z ≠ 1) [Finite G] :
    Nat.card (Subgroup.closure ({x, y} : Set G)) = 27 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hd : Nat.card (Subgroup.closure ({x, y} : Set G)) ∣ 3 ^ 3 := by
    rw [← range_nfHom hx hy hz hzx hzy hxy]
    exact (Subgroup.card_range_dvd _).trans (by rw [Heis.card]; norm_num)
  set P := Subgroup.closure ({x, y} : Set G)
  obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hd
  have hx' : x ∈ P := Subgroup.subset_closure (by simp)
  have hy' : y ∈ P := Subgroup.subset_closure (by simp)
  have hnc : (⟨x, hx'⟩ : P) * ⟨y, hy'⟩ ≠ ⟨y, hy'⟩ * ⟨x, hx'⟩ := by
    intro h
    have h' : x * y = y * x := congrArg Subtype.val h
    have h2 : y * z * x = y * 1 * x := by rw [← hxy, h', mul_one]
    exact hz1 (mul_left_cancel (mul_right_cancel h2))
  interval_cases k
  · exfalso
    have : Subsingleton P := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact hnc (Subsingleton.elim _ _)
  · exfalso
    have : Fact (Nat.card P).Prime := ⟨by rw [hcard]; norm_num⟩
    have := isCyclic_of_prime_card (α := P) rfl
    exact hnc (IsCyclic.commGroup.mul_comm _ _)
  · exfalso
    exact hnc (IsPGroup.commutative_of_card_eq_prime_sq (p := 3) hcard _ _)
  · simpa using hcard

include hx hy hz hzx hzy hxy in
theorem nfHom_injective (hz1 : z ≠ 1) [Finite G] :
    Function.Injective (nfHom hx hy hz hzx hzy hxy) := by
  set f := nfHom hx hy hz hzx hzy hxy
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, range_nfHom,
    card_closure hx hy hz hzx hzy hxy hz1, Heis.card] at h1
  have hk : Nat.card f.ker = 1 := by omega
  rw [← MonoidHom.ker_eq_bot_iff]
  exact Subgroup.card_eq_one.mp hk

@[expose] noncomputable def lineSet (x y z : G) (u : Heis) : Finset G :=
  open Classical in
  Finset.univ.image fun st : ZMod 3 × ZMod 3 => nf x y z ⟨st.1 * u.a, st.1 * u.b, st.2⟩

theorem card_lineSet_le (u : Heis) : (lineSet x y z u).card ≤ 9 := by
  classical
  refine (Finset.card_image_le).trans ?_
  simp [Finset.card_univ, ZMod.card]

include hx hy hz hzx hzy hxy in
theorem card_lineSet (hz1 : z ≠ 1) [Finite G] (u : Heis) (hu : u.a ≠ 0 ∨ u.b ≠ 0) :
    (lineSet x y z u).card = 9 := by
  classical
  unfold lineSet
  rw [Finset.card_image_of_injective]
  · simp [Finset.card_univ, ZMod.card]
  · rintro ⟨s, t⟩ ⟨s', t'⟩ h
    have h' := nfHom_injective hx hy hz hzx hzy hxy hz1 h
    have ha : s * u.a = s' * u.a := congrArg Heis.a h'
    have hb : s * u.b = s' * u.b := congrArg Heis.b h'
    have hc : t = t' := congrArg Heis.c h'
    exact Prod.ext (Heis.smul_inj _ _ _ _ hu ha hb) hc

include hx hy hz hzx hzy hxy in
theorem mem_lineSet_of_commute (hz1 : z ≠ 1) [Finite G] (u : Heis) (hu : u.a ≠ 0 ∨ u.b ≠ 0)
    {g : G} (hg : g ∈ Subgroup.closure ({x, y} : Set G)) (hc : g * nf x y z u = nf x y z u * g) :
    g ∈ lineSet x y z u := by
  classical
  rw [← range_nfHom hx hy hz hzx hzy hxy] at hg
  obtain ⟨v, rfl⟩ := hg
  have hvu : v * u = u * v := by
    apply nfHom_injective hx hy hz hzx hzy hxy hz1
    simpa [map_mul, nfHom_apply] using hc
  rw [Heis.mul_comm_iff] at hvu
  obtain ⟨s, hs1, hs2⟩ := Heis.exists_smul_of_cross u.a u.b v.a v.b hu hvu.symm
  refine Finset.mem_image.mpr ⟨(s, v.c), Finset.mem_univ _, ?_⟩
  show nf x y z ⟨s * u.a, s * u.b, v.c⟩ = nfHom hx hy hz hzx hzy hxy v
  rw [nfHom_apply]
  congr 1
  ext <;> simp [hs1, hs2]

include hx hy hz hzx hzy hxy in
theorem coe_eq_lineSet (hz1 : z ≠ 1) [Finite G] (B : Subgroup G)
    (hBP : B ≤ Subgroup.closure ({x, y} : Set G)) (hBc : IsMulCommutative B) (hB : Nat.card B = 9)
    (u : Heis) (hu : u.a ≠ 0 ∨ u.b ≠ 0) (huB : nf x y z u ∈ B) :
    (B : Set G) = (lineSet x y z u : Set G) := by
  have hsub : (B : Set G) ⊆ (lineSet x y z u : Set G) := by
    intro g hg
    have hc : g * nf x y z u = nf x y z u * g :=
      congrArg Subtype.val (hBc.is_comm.comm ⟨g, hg⟩ ⟨_, huB⟩)
    exact mem_lineSet_of_commute hx hy hz hzx hzy hxy hz1 u hu (hBP hg) hc
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
  change _ ≤ Nat.card B
  rw [hB]
  exact card_lineSet_le u

end Model2

section Lines

variable {G : Type*} [Group G] [Finite G] {x y z : G}
  (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz : z ^ 3 = 1) (hzx : z * x = x * z)
  (hzy : z * y = y * z) (hxy : x * y = y * z * x) (hz1 : z ≠ 1)

omit [Finite G] in
include hx hy hz hzx hzy hxy in
theorem z_mul_nf (u : Heis) : z * nf x y z u = nf x y z u * z := by
  have h : nf x y z ⟨0, 0, 1⟩ = z := by simp [nf, ZMod.val_one]
  have hc : (⟨0, 0, 1⟩ : Heis) * u = u * ⟨0, 0, 1⟩ := (Heis.mul_comm_iff _ _).mpr (by simp)
  have := congrArg (nfHom hx hy hz hzx hzy hxy) hc
  simpa only [map_mul, nfHom_apply, h] using this

omit [Finite G] in
include hx hy hz hzx hzy hxy in
theorem isMulCommutative_closure (u : Heis) :
    IsMulCommutative (Subgroup.closure ({z, nf x y z u} : Set G)) := by
  let := Subgroup.closureCommGroupOfComm (k := ({z, nf x y z u} : Set G)) (by
    rintro a (rfl | rfl) b (rfl | rfl) _
    · exact Commute.refl _
    · exact z_mul_nf hx hy hz hzx hzy hxy u
    · exact (z_mul_nf hx hy hz hzx hzy hxy u).symm
    · exact Commute.refl _)
  exact ⟨⟨mul_comm⟩⟩

omit [Finite G] in
include hxy in
theorem closure_le (u : Heis) :
    Subgroup.closure ({z, nf x y z u} : Set G) ≤ Subgroup.closure ({x, y} : Set G) := by
  have hx' : x ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hy' : y ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  rw [Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact z_mem_closure hxy
  · exact mul_mem (mul_mem (pow_mem hx' _) (pow_mem hy' _)) (pow_mem (z_mem_closure hxy) _)

include hx hy hz hzx hzy hxy hz1 in
theorem coe_closure_eq_lineSet (u : Heis) (hu : u.a ≠ 0 ∨ u.b ≠ 0) :
    (Subgroup.closure ({z, nf x y z u} : Set G) : Set G) = (lineSet x y z u : Set G) := by
  classical
  set A := Subgroup.closure ({z, nf x y z u} : Set G)
  have huA : nf x y z u ∈ A := Subgroup.subset_closure (by simp)
  have hzA : z ∈ A := Subgroup.subset_closure (by simp)
  apply Set.Subset.antisymm
  · intro g hg
    have hc : g * nf x y z u = nf x y z u * g :=
      congrArg Subtype.val
        ((isMulCommutative_closure hx hy hz hzx hzy hxy u).is_comm.comm ⟨g, hg⟩ ⟨_, huA⟩)
    exact mem_lineSet_of_commute hx hy hz hzx hzy hxy hz1 u hu (closure_le hxy u hg) hc
  · intro g hg
    obtain ⟨⟨s, t⟩, -, rfl⟩ := Finset.mem_image.mp hg
    set f := nfHom hx hy hz hzx hzy hxy
    have hd : (u ^ s.val * ⟨0, 0, t - (u ^ s.val).c⟩ : Heis) = ⟨s * u.a, s * u.b, t⟩ := by
      ext <;> simp
    have hz' : f ⟨0, 0, t - (u ^ s.val).c⟩ = z ^ (t - (u ^ s.val).c).val := by
      simp [f, nfHom_apply, nf]
    show nf x y z ⟨s * u.a, s * u.b, t⟩ ∈ A
    rw [← hd, ← nfHom_apply hx hy hz hzx hzy hxy, map_mul, map_pow, hz']
    exact mul_mem (pow_mem huA _) (pow_mem hzA _)

include hx hy hz hzx hzy hxy hz1 in
theorem card_closure_line (u : Heis) (hu : u.a ≠ 0 ∨ u.b ≠ 0) :
    Nat.card (Subgroup.closure ({z, nf x y z u} : Set G)) = 9 := by
  calc Nat.card (Subgroup.closure ({z, nf x y z u} : Set G))
      = (Subgroup.closure ({z, nf x y z u} : Set G) : Set G).ncard := Nat.card_coe_set_eq _
    _ = 9 := by
      rw [coe_closure_eq_lineSet hx hy hz hzx hzy hxy hz1 u hu, Set.ncard_coe_finset,
        card_lineSet hx hy hz hzx hzy hxy hz1 u hu]

include hx hy hz hzx hzy hxy hz1 in
theorem centGen_eq_top_of_le_closure
    (hF : ∀ u : Heis, (u.a ≠ 0 ∨ u.b ≠ 0) → ∃ t : Heis, ∃ w : G, ∃ v : Heis,
      (t.a ≠ 0 ∨ t.b ≠ 0) ∧ centGen (Subgroup.closure ({z, nf x y z t} : Set G)) = ⊤ ∧
      w * nf x y z t * w⁻¹ = nf x y z v ∧ (v.a ≠ 0 ∨ v.b ≠ 0) ∧ v.a * u.b = u.a * v.b ∧
      w * z * w⁻¹ ∈ Subgroup.zpowers z)
    (A : Subgroup G) (hAP : A ≤ Subgroup.closure ({x, y} : Set G)) (hA : IsElemAbelian 3 A)
    (hAc : Nat.card A = 9) : centGen A = ⊤ := by
  classical
  set P := Subgroup.closure ({x, y} : Set G)
  have hzP : z ∈ P := z_mem_closure hxy
  obtain ⟨g, hgA, hgz⟩ : ∃ g ∈ A, g ∉ Subgroup.zpowers z := by
    by_contra hcon
    push Not at hcon
    have hle : A ≤ Subgroup.zpowers z := hcon
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hAc] at h1
    have h2 := orderOf_le_of_pow_eq_one (by norm_num) hz
    omega
  have hgP : g ∈ (nfHom hx hy hz hzx hzy hxy).range := by
    rw [range_nfHom]; exact hAP hgA
  obtain ⟨u, rfl⟩ := hgP
  have hu : u.a ≠ 0 ∨ u.b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hgz
    refine ⟨u.c.val, ?_⟩
    show z ^ ((u.c.val : ℕ) : ℤ) = x ^ u.a.val * y ^ u.b.val * z ^ u.c.val
    rw [zpow_natCast, hcon.1, hcon.2]
    simp
  have hAset := coe_eq_lineSet hx hy hz hzx hzy hxy hz1 A hAP hA.1 hAc u hu hgA
  obtain ⟨t, w, v, ht, hA₁, hwt, hv, hcross, hwz⟩ := hF u hu
  set A₁ := Subgroup.closure ({z, nf x y z t} : Set G)
  set B := A₁.map (MulAut.conj w).toMonoidHom
  have hBP : B ≤ P := by
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro s (hs | hs)
    · show w * s * w⁻¹ ∈ P
      rw [hs]
      exact (Subgroup.zpowers_le.mpr hzP) hwz
    · show w * s * w⁻¹ ∈ P
      rw [show s = nf x y z t from hs, hwt]
      have hv' : nf x y z v ∈ (nfHom hx hy hz hzx hzy hxy).range := ⟨v, rfl⟩
      rwa [range_nfHom] at hv'
  have hBab : IsElemAbelian 3 B := by
    refine isElemAbelian_map ⟨isMulCommutative_closure hx hy hz hzx hzy hxy t, fun s hs => ?_⟩
      (MulAut.conj w)
    obtain ⟨⟨a, b, c⟩, rfl⟩ : s ∈ (nfHom hx hy hz hzx hzy hxy).range := by
      rw [range_nfHom]; exact closure_le hxy t hs
    rw [← map_pow]
    rw [Heis.pow_three, map_one]
  have hBc : Nat.card B = 9 := by
    rw [card_map]; exact card_closure_line hx hy hz hzx hzy hxy hz1 t ht
  have hvB : nf x y z v ∈ B := by
    refine ⟨nf x y z t, Subgroup.subset_closure (by simp), ?_⟩
    simp [MulAut.conj_apply, hwt]
  obtain ⟨s, hs1, hs2⟩ := Heis.exists_smul_of_cross u.a u.b v.a v.b hu hcross
  have hvA : nf x y z v ∈ A := by
    have : nf x y z v = nf x y z ⟨s * u.a, s * u.b, v.c⟩ := by
      congr 1; ext <;> simp [hs1, hs2]
    rw [this]
    have hmem : nf x y z ⟨s * u.a, s * u.b, v.c⟩ ∈ (lineSet x y z u : Set G) :=
      Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(s, v.c), Finset.mem_univ _, rfl⟩)
    rw [← hAset] at hmem
    exact hmem
  have hAv := coe_eq_lineSet hx hy hz hzx hzy hxy hz1 A hAP hA.1 hAc v hv hvA
  have hBv := coe_eq_lineSet hx hy hz hzx hzy hxy hz1 B hBP hBab.1 hBc v hv hvB
  have hAB : A = B := SetLike.coe_injective (hAv.trans hBv.symm)
  rw [hAB]
  exact centGen_eq_top_of_map (MulAut.conj w) hA₁

include hx hy hz hzx hzy hxy hz1 in
theorem centGen_eq_top_of_heis (hcard : ¬ 3 ^ 4 ∣ Nat.card G)
    (hF : ∀ u : Heis, (u.a ≠ 0 ∨ u.b ≠ 0) → ∃ t : Heis, ∃ w : G, ∃ v : Heis,
      (t.a ≠ 0 ∨ t.b ≠ 0) ∧ centGen (Subgroup.closure ({z, nf x y z t} : Set G)) = ⊤ ∧
      w * nf x y z t * w⁻¹ = nf x y z v ∧ (v.a ≠ 0 ∨ v.b ≠ 0) ∧ v.a * u.b = u.a * v.b ∧
      w * z * w⁻¹ ∈ Subgroup.zpowers z)
    (A : Subgroup G) (hA : IsElemAbelian 3 A) (hAc : Nat.card A = 9) : centGen A = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set P := Subgroup.closure ({x, y} : Set G)
  have hPc : Nat.card P = 27 := card_closure hx hy hz hzx hzy hxy hz1
  have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have h3 : 3 ^ 3 ∣ Nat.card G := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hPc]; exact Subgroup.card_subgroup_dvd_card P
  have hfac : (Nat.card G).factorization 3 = 3 := by
    have hle : 3 ≤ (Nat.card G).factorization 3 :=
      ((Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hG0).mp h3)
    have hlt : ¬ 4 ≤ (Nat.card G).factorization 3 := fun h4 =>
      hcard ((Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hG0).mpr h4)
    omega
  let PS : Sylow 3 G := Sylow.ofCard P (by rw [hPc, hfac]; norm_num)
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 2) (by rw [hAc]; norm_num)
  obtain ⟨T, hAT⟩ := hAp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G PS T
  set A' := A.map (MulAut.conj g⁻¹).toMonoidHom
  have hA'P : A' ≤ P := by
    rintro _ ⟨a, ha, rfl⟩
    have haT : a ∈ ((g • PS : Sylow 3 G) : Subgroup G) := hg ▸ hAT ha
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at haT
    have hPS : ((PS : Sylow 3 G) : Subgroup G) = P := Sylow.coe_ofCard _ _
    rw [hPS] at haT
    simpa [MulAut.smul_def, MulAut.conj_apply] using haT
  have hA' : centGen A' = ⊤ :=
    centGen_eq_top_of_le_closure hx hy hz hzx hzy hxy hz1 hF A' hA'P
      (isElemAbelian_map hA (MulAut.conj g⁻¹)) (by rw [card_map, hAc])
  have hAA : A'.map (MulAut.conj g).toMonoidHom = A := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id A
    ext a
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, MonoidHom.id_apply]
    group
  rw [← hAA]
  exact centGen_eq_top_of_map (MulAut.conj g) hA'

end Lines

section Gen

variable {G : Type*} [Group G] [Finite G]

theorem centGen_eq_top_of_forall_mem [IsSimpleGroup G] {A : Subgroup G} {a₀ : G} (ha₀ : a₀ ∈ A)
    (ha₀1 : a₀ ≠ 1) {s : Set G}
    (hs : ∀ g ∈ s, g ∈ Subgroup.normalizer (A : Set G) ∨ ∃ a ∈ A, a ≠ 1 ∧ g * a = a * g)
    (hgen : Subgroup.closure s = ⊤) : centGen A = ⊤ := by
  set H := centGen A
  have hN : Subgroup.normalizer (H : Set G) = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    intro g hg
    rcases hs g hg with hn | ⟨a, ha, ha1, hga⟩
    · exact le_normalizer_centGen A hn
    · exact Subgroup.le_normalizer
        (centralizer_le_centGen ha ha1 (Subgroup.mem_centralizer_singleton_iff.mpr hga))
  have hnorm : H.Normal := Subgroup.normalizer_eq_top_iff.mp hN
  rcases hnorm.eq_bot_or_eq_top with hb | ht
  · exfalso
    have h : a₀ ∈ H :=
      centralizer_le_centGen ha₀ ha₀1 (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
    rw [hb, Subgroup.mem_bot] at h
    exact ha₀1 h
  · exact ht

end Gen

end CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis
