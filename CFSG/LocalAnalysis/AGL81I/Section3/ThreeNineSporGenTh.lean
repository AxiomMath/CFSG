module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGen
public import Certificates.Certificate1322002

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThFive

open CFSG.Open

@[ext] structure Heis where
  a : ZMod 5
  b : ZMod 5
  c : ZMod 5
deriving DecidableEq

namespace Heis

def equivProd : Heis ≃ ZMod 5 × ZMod 5 × ZMod 5 where
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
  inv_mul_cancel u := by ext <;> simp <;> ring

theorem card : Nat.card Heis = 125 := by
  rw [Nat.card_congr equivProd]
  simp [Nat.card_prod, Nat.card_zmod]

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

theorem exists_smul_of_cross : ∀ a b a' b' : ZMod 5, (a ≠ 0 ∨ b ≠ 0) → a' * b = a * b' →
    ∃ s : ZMod 5, a' = s * a ∧ b' = s * b := by
  decide

theorem pow_five (u : Heis) : u ^ 5 = 1 := by
  ext <;> simp only [pow_succ, pow_zero, mul_a, mul_b, mul_c, one_a, one_b, one_c] <;> ring_nf <;>
    reduce_mod_char

theorem smul_inj : ∀ a b s s' : ZMod 5, (a ≠ 0 ∨ b ≠ 0) → s * a = s' * a → s * b = s' * b →
    s = s' := by
  decide

end Heis

section Model

variable {G : Type*} [Group G] {x y z : G}

theorem pow_mod_five {g : G} (hg : g ^ 5 = 1) (n : ℕ) : g ^ n = g ^ (n % 5) := by
  conv_lhs => rw [← Nat.div_add_mod n 5, pow_add, pow_mul, hg, one_pow, one_mul]

theorem pow_eq_pow_of_cast {g : G} (hg : g ^ 5 = 1) {m n : ℕ} (h : (m : ZMod 5) = n) :
    g ^ m = g ^ n := by
  rw [pow_mod_five hg m, pow_mod_five hg n, (ZMod.natCast_eq_natCast_iff' m n 5).mp h]

@[expose] def nf (x y z : G) (u : Heis) : G := x ^ u.a.val * y ^ u.b.val * z ^ u.c.val

variable (hx : x ^ 5 = 1) (hy : y ^ 5 = 1) (hz : z ^ 5 = 1) (hzx : z * x = x * z)
  (hzy : z * y = y * z) (hxy : x * y = y * z * x)

include hz hzx hxy in
theorem y_mul_x : y * x = x * y * z ^ 4 := by
  have h : x * y * z ^ 4 = y * x := by
    rw [hxy]
    calc y * z * x * z ^ 4 = y * (z * x) * z ^ 4 := by group
      _ = y * (x * z) * z ^ 4 := by rw [hzx]
      _ = y * x * z ^ 5 := by group
      _ = y * x := by rw [hz, mul_one]
  exact h.symm

include hz hzx hxy in
theorem y_mul_x_pow (m : ℕ) : y * x ^ m = x ^ m * y * z ^ (4 * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hc : Commute (z ^ (4 * m)) x := Commute.pow_left hzx _
    calc y * x ^ (m + 1) = y * x ^ m * x := by rw [pow_succ, mul_assoc]
      _ = x ^ m * y * (z ^ (4 * m) * x) := by rw [ih]; group
      _ = x ^ m * y * (x * z ^ (4 * m)) := by rw [hc.eq]
      _ = x ^ m * (y * x) * z ^ (4 * m) := by group
      _ = x ^ m * (x * y * z ^ 4) * z ^ (4 * m) := by rw [y_mul_x hz hzx hxy]
      _ = x ^ (m + 1) * y * z ^ (4 * (m + 1)) := by
        rw [pow_succ x m, show 4 * (m + 1) = 4 + 4 * m by ring, pow_add]; group

include hz hzx hzy hxy in
theorem y_pow_mul_x_pow (n m : ℕ) : y ^ n * x ^ m = x ^ m * y ^ n * z ^ (4 * n * m) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : Commute (z ^ (4 * m)) (y ^ n) := Commute.pow_pow hzy _ _
    calc y ^ (n + 1) * x ^ m = y * (y ^ n * x ^ m) := by rw [pow_succ', mul_assoc]
      _ = y * x ^ m * y ^ n * z ^ (4 * n * m) := by rw [ih]; group
      _ = x ^ m * y * (z ^ (4 * m) * y ^ n) * z ^ (4 * n * m) := by
        rw [y_mul_x_pow hz hzx hxy m]; group
      _ = x ^ m * y * (y ^ n * z ^ (4 * m)) * z ^ (4 * n * m) := by rw [hc.eq]
      _ = x ^ m * y ^ (n + 1) * z ^ (4 * (n + 1) * m) := by
        rw [pow_succ' y n, show 4 * (n + 1) * m = 4 * m + 4 * n * m by ring, pow_add]; group

include hx hy hz hzx hzy hxy in
theorem nf_mul (u v : Heis) : nf x y z (u * v) = nf x y z u * nf x y z v := by
  have hzxc : ∀ k m : ℕ, z ^ k * x ^ m = x ^ m * z ^ k := fun k m => (Commute.pow_pow hzx k m).eq
  have hzyc : ∀ k m : ℕ, z ^ k * y ^ m = y ^ m * z ^ k := fun k m => (Commute.pow_pow hzy k m).eq
  have ea : x ^ (u * v).a.val = x ^ (u.a.val + v.a.val) :=
    pow_eq_pow_of_cast hx (by simp)
  have eb : y ^ (u * v).b.val = y ^ (u.b.val + v.b.val) :=
    pow_eq_pow_of_cast hy (by simp)
  have ec : z ^ (u * v).c.val = z ^ (4 * u.b.val * v.a.val + u.c.val + v.c.val) := by
    refine pow_eq_pow_of_cast hz ?_
    have h4 : (4 : ZMod 5) = -1 := by decide
    simp only [Heis.mul_c, ZMod.natCast_val, ZMod.cast_id', id, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, h4]
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
  have E4 := hzyc (4 * B * A') B'
  symm
  calc x ^ A * y ^ B * z ^ C * (x ^ A' * y ^ B' * z ^ C')
      = x ^ A * y ^ B * (z ^ C * x ^ A') * y ^ B' * z ^ C' := by group
    _ = x ^ A * (y ^ B * x ^ A') * (z ^ C * y ^ B') * z ^ C' := by rw [E1]; group
    _ = x ^ A * x ^ A' * y ^ B * (z ^ (4 * B * A') * y ^ B') * z ^ C * z ^ C' := by
        rw [E2, E3]; group
    _ = x ^ A * x ^ A' * (y ^ B * y ^ B') * (z ^ (4 * B * A') * z ^ C * z ^ C') := by
        rw [E4]; group

end Model

section Model2

variable {G : Type*} [Group G] {x y z : G}
  (hx : x ^ 5 = 1) (hy : y ^ 5 = 1) (hz : z ^ 5 = 1) (hzx : z * x = x * z)
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
    Nat.card (Subgroup.closure ({x, y} : Set G)) = 125 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hd : Nat.card (Subgroup.closure ({x, y} : Set G)) ∣ 5 ^ 3 := by
    rw [← range_nfHom hx hy hz hzx hzy hxy]
    exact (Subgroup.card_range_dvd _).trans (by rw [Heis.card]; norm_num)
  set P := Subgroup.closure ({x, y} : Set G)
  obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp hd
  have hx' : x ∈ P := Subgroup.subset_closure (by simp)
  have hy' : y ∈ P := Subgroup.subset_closure (by simp)
  have hnc : (⟨x, hx'⟩ : P) * ⟨y, hy'⟩ ≠ ⟨y, hy'⟩ * ⟨x, hx'⟩ := by
    intro h
    have h' : x * y = y * x := congrArg Subtype.val h
    have h2 : y * z * x = y * 1 * x := by rw [← hxy, h', mul_one]
    exact hz1 (mul_left_cancel (mul_right_cancel h2))
  interval_cases k
  · exfalso
    haveI : Subsingleton P := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact hnc (Subsingleton.elim _ _)
  · exfalso
    haveI : Fact (Nat.card P).Prime := ⟨by rw [hcard]; norm_num⟩
    haveI := isCyclic_of_prime_card (α := P) rfl
    exact hnc (IsCyclic.commGroup.mul_comm _ _)
  · exfalso
    exact hnc (IsPGroup.commutative_of_card_eq_prime_sq (p := 5) hcard _ _)
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
  Finset.univ.image fun st : ZMod 5 × ZMod 5 => nf x y z ⟨st.1 * u.a, st.1 * u.b, st.2⟩

theorem card_lineSet_le (u : Heis) : (lineSet x y z u).card ≤ 25 := by
  classical
  refine (Finset.card_image_le).trans ?_
  simp [Finset.card_univ, ZMod.card]

include hx hy hz hzx hzy hxy in
theorem card_lineSet (hz1 : z ≠ 1) [Finite G] (u : Heis) (hu : u.a ≠ 0 ∨ u.b ≠ 0) :
    (lineSet x y z u).card = 25 := by
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
    (hBP : B ≤ Subgroup.closure ({x, y} : Set G)) (hBc : IsMulCommutative B) (hB : Nat.card B = 25)
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

section Conj

variable {K K' : Type*} [Group K] [Finite K] [Group K'] [Finite K']

theorem map_centGen_le (φ : K ≃* K') (A : Subgroup K) :
    (centGen A).map φ.toMonoidHom ≤ centGen (A.map φ.toMonoidHom) := by
  rw [centGen, Subgroup.map_iSup]
  refine iSup_le fun a => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun ha => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun ha1 => ?_
  have hwa : φ.toMonoidHom a ∈ A.map φ.toMonoidHom := Subgroup.mem_map_of_mem _ ha
  have hwa1 : φ.toMonoidHom a ≠ 1 := by
    simpa using ha1
  refine le_trans ?_ (centralizer_le_centGen hwa hwa1)
  rintro _ ⟨g, hg, rfl⟩
  have hg' : g ∈ Subgroup.centralizer ({a} : Set K) := hg
  show _ ∈ Subgroup.centralizer _
  rw [Subgroup.mem_centralizer_singleton_iff] at hg' ⊢
  simp only [MulEquiv.coe_toMonoidHom]
  rw [← map_mul, ← map_mul, hg']

theorem centGen_eq_top_of_map {A : Subgroup K} (φ : K ≃* K') (h : centGen A = ⊤) :
    centGen (A.map φ.toMonoidHom) = ⊤ := by
  refine top_le_iff.mp (le_trans ?_ (map_centGen_le φ A))
  rw [h, Subgroup.map_top_of_surjective _ φ.surjective]

theorem isElemAbelian_map {p : ℕ} {A : Subgroup K} (hA : IsElemAbelian p A) (φ : K ≃* K') :
    IsElemAbelian p (A.map φ.toMonoidHom) := by
  refine ⟨⟨⟨fun ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩ => Subtype.ext ?_⟩⟩, ?_⟩
  · simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hA.2 a ha, map_one]

theorem card_map (A : Subgroup K) (φ : K ≃* K') :
    Nat.card (A.map φ.toMonoidHom) = Nat.card A :=
  Subgroup.card_map_of_injective φ.injective

theorem centGen_eq_top_of_equiv {A : Subgroup K} (φ : K ≃* K')
    (h : centGen (A.map φ.toMonoidHom) = ⊤) : centGen A = ⊤ := by
  have h2 := centGen_eq_top_of_map φ.symm h
  have hA : (A.map φ.toMonoidHom).map φ.symm.toMonoidHom = A := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id A
    ext a
    simp
  rwa [hA] at h2

end Conj

section Main

variable {G : Type*} [Group G] [Finite G] {x y z : G}
  (hx : x ^ 5 = 1) (hy : y ^ 5 = 1) (hz : z ^ 5 = 1) (hzx : z * x = x * z)
  (hzy : z * y = y * z) (hxy : x * y = y * z * x) (hz1 : z ≠ 1)

include hzy in
theorem isMulCommutative_closure_zy :
    IsMulCommutative (Subgroup.closure ({z, y} : Set G)) := by
  letI := Subgroup.closureCommGroupOfComm (k := ({z, y} : Set G)) (by
    rintro a (rfl | rfl) b (rfl | rfl) _
    · exact Commute.refl _
    · exact hzy
    · exact hzy.symm
    · exact Commute.refl _)
  exact ⟨⟨mul_comm⟩⟩

include hxy in
theorem closure_zy_le : Subgroup.closure ({z, y} : Set G) ≤ Subgroup.closure ({x, y} : Set G) := by
  rw [Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact z_mem_closure hxy
  · exact Subgroup.subset_closure (by simp)

include hx hy hz hzx hzy hxy hz1 in
theorem card_closure_zy : Nat.card (Subgroup.closure ({z, y} : Set G)) = 25 := by
  classical
  set A := Subgroup.closure ({z, y} : Set G)
  have hyA : nf x y z ⟨0, 1, 0⟩ ∈ A := by
    have : nf x y z ⟨0, 1, 0⟩ = y := by simp [nf, ZMod.val_one]
    rw [this]; exact Subgroup.subset_closure (by simp)
  have hsup : (A : Set G) ⊆ (lineSet x y z ⟨0, 1, 0⟩ : Set G) := by
    intro g hg
    have hc : g * nf x y z ⟨0, 1, 0⟩ = nf x y z ⟨0, 1, 0⟩ * g :=
      congrArg Subtype.val ((isMulCommutative_closure_zy hzy).is_comm.comm ⟨g, hg⟩ ⟨_, hyA⟩)
    exact mem_lineSet_of_commute hx hy hz hzx hzy hxy hz1 _ (Or.inr one_ne_zero)
      (closure_zy_le hxy hg) hc
  have hsub : (lineSet x y z ⟨0, 1, 0⟩ : Set G) ⊆ (A : Set G) := by
    intro g hg
    obtain ⟨⟨s, t⟩, -, rfl⟩ := Finset.mem_image.mp hg
    have hz' : z ∈ A := Subgroup.subset_closure (by simp)
    have hy' : y ∈ A := Subgroup.subset_closure (by simp)
    show x ^ (s * 0).val * y ^ (s * 1).val * z ^ t.val ∈ A
    simp only [mul_zero, ZMod.val_zero, pow_zero, one_mul]
    exact mul_mem (pow_mem hy' _) (pow_mem hz' _)
  have heq : (A : Set G) = (lineSet x y z ⟨0, 1, 0⟩ : Set G) := hsup.antisymm hsub
  calc Nat.card A = (A : Set G).ncard := Nat.card_coe_set_eq _
    _ = 25 := by
      rw [heq, Set.ncard_coe_finset, card_lineSet hx hy hz hzx hzy hxy hz1 _ (Or.inr one_ne_zero)]

include hz1 in
theorem centGen_closure_zy_eq_top [IsSimpleGroup G] {h₁ h₂ g₂ : G}
    (hN₁ : h₁ ∈ Subgroup.normalizer ((Subgroup.closure ({z, y} : Set G)) : Set G))
    (hN₂ : h₂ ∈ Subgroup.normalizer ((Subgroup.closure ({z, y} : Set G)) : Set G))
    (hF1 : g₂ * h₂ * z = z * (g₂ * h₂))
    (hgen : Subgroup.closure ({h₁, h₂, g₂} : Set G) = ⊤) :
    centGen (Subgroup.closure ({z, y} : Set G)) = ⊤ := by
  set A := Subgroup.closure ({z, y} : Set G)
  set H := centGen A
  have hzA : z ∈ A := Subgroup.subset_closure (by simp)
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ H := centralizer_le_centGen hzA hz1
  have hzH : z ∈ H := hCz (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hcH : g₂ * h₂ ∈ H := hCz (Subgroup.mem_centralizer_singleton_iff.mpr hF1)
  set N := Subgroup.normalizer (H : Set G)
  have h1N : h₁ ∈ N := le_normalizer_centGen A hN₁
  have h2N : h₂ ∈ N := le_normalizer_centGen A hN₂
  have hcN : g₂ * h₂ ∈ N := Subgroup.le_normalizer hcH
  have g2N : g₂ ∈ N := by
    have : g₂ = g₂ * h₂ * h₂⁻¹ := by group
    rw [this]; exact mul_mem hcN (inv_mem h2N)
  have hNtop : N = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl) <;> assumption
  have hnorm : H.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
  rcases hnorm.eq_bot_or_eq_top with hb | ht
  · exfalso
    rw [hb, Subgroup.mem_bot] at hzH
    exact hz1 hzH
  · exact ht

include hx hy hz hzx hzy hxy hz1 in
theorem centGen_eq_top_of_le_closure
    (hF2 : ∀ u : Heis, (u.a ≠ 0 ∨ u.b ≠ 0) → ∃ w : G, ∃ v : Heis, w * y * w⁻¹ = nf x y z v ∧
      (v.a ≠ 0 ∨ v.b ≠ 0) ∧ v.a * u.b = u.a * v.b ∧ w * z * w⁻¹ ∈ Subgroup.zpowers z)
    (hA₁ : centGen (Subgroup.closure ({z, y} : Set G)) = ⊤)
    (A : Subgroup G) (hAP : A ≤ Subgroup.closure ({x, y} : Set G)) (hA : IsElemAbelian 5 A)
    (hAc : Nat.card A = 25) : centGen A = ⊤ := by
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
  obtain ⟨w, v, hwy, hv, hcross, hwz⟩ := hF2 u hu
  set A₁ := Subgroup.closure ({z, y} : Set G)
  set B := A₁.map (MulAut.conj w).toMonoidHom
  have hBP : B ≤ P := by
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro t (ht | ht)
    · show w * t * w⁻¹ ∈ P
      rw [ht]
      exact (Subgroup.zpowers_le.mpr hzP) hwz
    · show w * t * w⁻¹ ∈ P
      rw [show t = y from ht, hwy]
      have hv' : nf x y z v ∈ (nfHom hx hy hz hzx hzy hxy).range := ⟨v, rfl⟩
      rwa [range_nfHom] at hv'
  have hBab : IsElemAbelian 5 B := by
    refine isElemAbelian_map ⟨isMulCommutative_closure_zy hzy, fun t ht => ?_⟩ (MulAut.conj w)
    obtain ⟨⟨a, b, c⟩, rfl⟩ : t ∈ (nfHom hx hy hz hzx hzy hxy).range := by
      rw [range_nfHom]; exact closure_zy_le hxy ht
    rw [← map_pow]
    rw [Heis.pow_five, map_one]
  have hBc : Nat.card B = 25 := by
    rw [card_map]; exact card_closure_zy hx hy hz hzx hzy hxy hz1
  have hvB : nf x y z v ∈ B := by
    refine ⟨y, Subgroup.subset_closure (by simp), ?_⟩
    simp [MulAut.conj_apply, hwy]
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

end Main

section Final

variable {G : Type*} [Group G] [Finite G]

theorem conj_eq_of_mul_eq {w g t : G} (h : w * g = t * w) : w * g * w⁻¹ = t := by
  rw [h]; group

theorem mem_normalizer_of_conj_mem {s : Set G} {h : G}
    (hs : ∀ t ∈ s, h * t * h⁻¹ ∈ Subgroup.closure s) :
    h ∈ Subgroup.normalizer ((Subgroup.closure s : Subgroup G) : Set G) := by
  set A := Subgroup.closure s
  have hle : A.map (MulAut.conj h).toMonoidHom ≤ A := by
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    intro t ht
    exact hs t ht
  have heq : A.map (MulAut.conj h).toMonoidHom = A :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_map])
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    exact hle ⟨n, hn, rfl⟩
  · intro hn
    rw [← heq] at hn
    obtain ⟨m, hm, hmn⟩ := hn
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hmn
    have : m = n := by
      have := congrArg (fun t => h⁻¹ * t * h) hmn
      simpa [mul_assoc] using this
    rwa [← this]

variable {x y z h₁ h₂ g₂ : G}
  (hx : x ^ 5 = 1) (hy : y ^ 5 = 1) (hz : z ^ 5 = 1) (hzx : z * x = x * z)
  (hzy : z * y = y * z) (hxy : x * y = y * z * x) (hz1 : z ≠ 1)

include hx hy hz hzx hzy hxy hz1 in
theorem centGen_eq_top_of_heisData [IsSimpleGroup G] (hcard : ¬ 5 ^ 4 ∣ Nat.card G)
    (hN₁ : ∀ t ∈ ({z, y} : Set G), h₁ * t * h₁⁻¹ ∈ Subgroup.closure ({z, y} : Set G))
    (hN₂ : ∀ t ∈ ({z, y} : Set G), h₂ * t * h₂⁻¹ ∈ Subgroup.closure ({z, y} : Set G))
    (hF1 : g₂ * h₂ * z = z * (g₂ * h₂))
    (hF2 : ∀ u : Heis, (u.a ≠ 0 ∨ u.b ≠ 0) → ∃ w : G, ∃ v : Heis, w * y * w⁻¹ = nf x y z v ∧
      (v.a ≠ 0 ∨ v.b ≠ 0) ∧ v.a * u.b = u.a * v.b ∧ w * z * w⁻¹ ∈ Subgroup.zpowers z)
    (hgen : Subgroup.closure ({h₁, h₂, g₂} : Set G) = ⊤)
    (A : Subgroup G) (hA : IsElemAbelian 5 A) (hAc : Nat.card A = 25) : centGen A = ⊤ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hA₁ := centGen_closure_zy_eq_top hz1 (mem_normalizer_of_conj_mem hN₁)
    (mem_normalizer_of_conj_mem hN₂) hF1 hgen
  set P := Subgroup.closure ({x, y} : Set G)
  have hPc : Nat.card P = 125 := card_closure hx hy hz hzx hzy hxy hz1
  have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have h3 : 5 ^ 3 ∣ Nat.card G := by
    rw [show (5 : ℕ) ^ 3 = 125 by norm_num, ← hPc]; exact Subgroup.card_subgroup_dvd_card P
  have hfac : (Nat.card G).factorization 5 = 3 := by
    have hle : 3 ≤ (Nat.card G).factorization 5 :=
      ((Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hG0).mp h3)
    have hlt : ¬ 4 ≤ (Nat.card G).factorization 5 := fun h4 =>
      hcard ((Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hG0).mpr h4)
    omega
  let PS : Sylow 5 G := Sylow.ofCard P (by rw [hPc, hfac]; norm_num)
  have hAp : IsPGroup 5 A := IsPGroup.of_card (n := 2) (by rw [hAc]; norm_num)
  obtain ⟨T, hAT⟩ := hAp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G PS T
  set A' := A.map (MulAut.conj g⁻¹).toMonoidHom
  have hA'P : A' ≤ P := by
    rintro _ ⟨a, ha, rfl⟩
    have haT : a ∈ ((g • PS : Sylow 5 G) : Subgroup G) := hg ▸ hAT ha
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at haT
    have hPS : ((PS : Sylow 5 G) : Subgroup G) = P := Sylow.coe_ofCard _ _
    rw [hPS] at haT
    simpa [MulAut.smul_def, MulAut.conj_apply] using haT
  have hA' : centGen A' = ⊤ :=
    centGen_eq_top_of_le_closure hx hy hz hzx hzy hxy hz1 hF2 hA₁ A' hA'P
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


include hx hy hz hzx hzy hxy hz1 in
theorem centGen_eq_top_of_thFacts [IsSimpleGroup G] (hcard : ¬ 5 ^ 4 ∣ Nat.card G)
    (e12 : h₁ * z = y ^ 3 * h₁) (e13 : h₁ * y = z ^ 2 * h₁) (e14 : h₂ * z = z ^ 3 * h₂)
    (e15 : h₂ * y = y ^ 4 * z * h₂) (hF1 : g₂ * h₂ * z = z * (g₂ * h₂))
    (e17 : h₂ * g₂ * y = x ^ 2 * z * (h₂ * g₂)) (e18 : h₂ * g₂ * z = z * (h₂ * g₂))
    (e19 : h₂ * g₂ ^ 3 * y = x ^ 4 * y ^ 4 * (h₂ * g₂ ^ 3))
    (e20 : h₂ * g₂ ^ 3 * z = z ^ 4 * (h₂ * g₂ ^ 3))
    (e21 : g₂ ^ 3 * y = x ^ 2 * y ^ 4 * z ^ 4 * g₂ ^ 3) (e22 : g₂ ^ 3 * z = z ^ 3 * g₂ ^ 3)
    (e23 : g₂ ^ 2 * y = x ^ 2 * y * z ^ 2 * g₂ ^ 2) (e24 : g₂ ^ 2 * z = z ^ 4 * g₂ ^ 2)
    (e25 : g₂ * y = x * y ^ 4 * z ^ 2 * g₂) (e26 : g₂ * z = z ^ 2 * g₂)
    (hgen : Subgroup.closure ({h₁, h₂, g₂} : Set G) = ⊤)
    (A : Subgroup G) (hA : IsElemAbelian 5 A) (hAc : Nat.card A = 25) : centGen A = ⊤ := by
  have hzS : z ∈ Subgroup.closure ({z, y} : Set _) := Subgroup.subset_closure (by simp)
  have hyS : y ∈ Subgroup.closure ({z, y} : Set _) := Subgroup.subset_closure (by simp)
  have hN₁ : ∀ t ∈ ({z, y} : Set _), h₁ * t * h₁⁻¹ ∈ Subgroup.closure ({z, y} : Set _) := by
    rintro t (ht | ht) <;> rw [show t = _ from ht]
    · rw [conj_eq_of_mul_eq e12]; exact pow_mem hyS _
    · rw [conj_eq_of_mul_eq e13]; exact pow_mem hzS _
  have hN₂ : ∀ t ∈ ({z, y} : Set _), h₂ * t * h₂⁻¹ ∈ Subgroup.closure ({z, y} : Set _) := by
    rintro t (ht | ht) <;> rw [show t = _ from ht]
    · rw [conj_eq_of_mul_eq e14]; exact pow_mem hzS _
    · rw [conj_eq_of_mul_eq e15]; exact mul_mem (pow_mem hyS _) hzS
  have hzp : ∀ k : ℕ, z ^ k ∈ Subgroup.zpowers z := fun k => pow_mem (Subgroup.mem_zpowers z) k
  have key : ∀ a b : ZMod 5, (a ≠ 0 ∨ b ≠ 0) → (0 * b = a * 4 ∨ 2 * b = a * 0 ∨ 4 * b = a * 4 ∨
      2 * b = a * 4 ∨ 2 * b = a * 1 ∨ 1 * b = a * 4) := by decide
  have hF2 : ∀ u : Heis, (u.a ≠ 0 ∨ u.b ≠ 0) → ∃ w, ∃ v : Heis, w * y * w⁻¹ = nf x y z v ∧
      (v.a ≠ 0 ∨ v.b ≠ 0) ∧ v.a * u.b = u.a * v.b ∧ w * z * w⁻¹ ∈ Subgroup.zpowers z := by
    intro u hu
    rcases key u.a u.b hu with h | h | h | h | h | h
    · refine ⟨h₂, ⟨0, 4, 1⟩, ?_, by decide, h, ?_⟩
      · rw [conj_eq_of_mul_eq e15]; show _ = x ^ 0 * y ^ 4 * z ^ 1; simp
      · rw [conj_eq_of_mul_eq e14]; exact hzp 3
    · refine ⟨h₂ * g₂, ⟨2, 0, 1⟩, ?_, by decide, h, ?_⟩
      · rw [conj_eq_of_mul_eq e17]; show _ = x ^ 2 * y ^ 0 * z ^ 1; simp
      · rw [conj_eq_of_mul_eq e18]; exact Subgroup.mem_zpowers z
    · refine ⟨h₂ * g₂ ^ 3, ⟨4, 4, 0⟩, ?_, by decide, h, ?_⟩
      · rw [conj_eq_of_mul_eq e19]; show _ = x ^ 4 * y ^ 4 * z ^ 0; simp
      · rw [conj_eq_of_mul_eq e20]; exact hzp 4
    · refine ⟨g₂ ^ 3, ⟨2, 4, 4⟩, ?_, by decide, h, ?_⟩
      · rw [conj_eq_of_mul_eq e21]; show _ = x ^ 2 * y ^ 4 * z ^ 4; rfl
      · rw [conj_eq_of_mul_eq e22]; exact hzp 3
    · refine ⟨g₂ ^ 2, ⟨2, 1, 2⟩, ?_, by decide, h, ?_⟩
      · rw [conj_eq_of_mul_eq e23]; show _ = x ^ 2 * y ^ 1 * z ^ 2; simp
      · rw [conj_eq_of_mul_eq e24]; exact hzp 4
    · refine ⟨g₂, ⟨1, 4, 2⟩, ?_, by decide, h, ?_⟩
      · rw [conj_eq_of_mul_eq e25]; show _ = x ^ 1 * y ^ 4 * z ^ 2; simp
      · rw [conj_eq_of_mul_eq e26]; exact hzp 2
  exact centGen_eq_top_of_heisData hx hy hz hzx hzy hxy hz1 hcard hN₁ hN₂ hF1 hF2 hgen A hA hAc

end Final

section Concrete

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.RankThree.Asc83Table
  CFSG.Blueprint CFSG.SectionRank.LocalWitness

theorem centGen_Th_five_of_check
    (hC : seedCertCheck (ops2 248) NativeSporadic.ThSeed1 NativeSporadic.ThSeed2 thLineCert = true)
    [Finite (NativeSporadic.Carrier .Th)] [IsSimpleGroup (NativeSporadic.Carrier .Th)]
    (hcard : ¬ 5 ^ 4 ∣ Nat.card (NativeSporadic.Carrier .Th))
    (A : Subgroup (NativeSporadic.Carrier .Th))
    (hA : IsElemAbelian 5 A) (hAc : Nat.card A = 25) : centGen A = ⊤ := by
  haveI : Finite NativeSporadic.Th := ‹Finite (NativeSporadic.Carrier .Th)›
  haveI : IsSimpleGroup NativeSporadic.Th := ‹IsSimpleGroup (NativeSporadic.Carrier .Th)›
  unfold seedCertCheck at hC
  simp only [Bool.and_eq_true] at hC
  obtain ⟨⟨hM, hAeq⟩, hBeq⟩ := hC
  let Sp := spec2 248
  set x := regUnit Sp hM 94
  set y := regUnit Sp hM 105
  set z := regUnit Sp hM 110
  set h₁ := regUnit Sp hM 82
  set h₂ := regUnit Sp hM 84
  set g₂ := regUnit Sp hM 25
  have hx : x ^ 5 = 1 := regUnit_pow Sp hM (mem_facts 5 rfl)
  have hy : y ^ 5 = 1 := regUnit_pow Sp hM (mem_facts 6 rfl)
  have hz : z ^ 5 = 1 := regUnit_pow Sp hM (mem_facts 7 rfl)
  have hz1 : z ≠ 1 := by
    have := regUnit_ne Sp hM (mem_facts 8 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
    simpa [wordUnit_cons, wordUnit_nil] using this
  have hxy : x * y = y * z * x := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, mul_one, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 9 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have hzx : z * x = x * z := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, mul_one, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 10 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have hzy : z * y = y * z := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, mul_one, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 11 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e12 : h₁ * z = y ^ 3 * h₁ := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, mul_one, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 12 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e13 : h₁ * y = z ^ 2 * h₁ := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, mul_one, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 13 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e14 : h₂ * z = z ^ 3 * h₂ := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, mul_one, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 14 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e15 : h₂ * y = y ^ 4 * z * h₂ := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, mul_one, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 15 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have hF1 : g₂ * h₂ * z = z * (g₂ * h₂) := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, mul_one, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 16 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e17 : h₂ * g₂ * y = x ^ 2 * z * (h₂ * g₂) := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, mul_one, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 17 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e18 : h₂ * g₂ * z = z * (h₂ * g₂) := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, mul_one, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 18 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e19 : h₂ * g₂ ^ 3 * y = x ^ 4 * y ^ 4 * (h₂ * g₂ ^ 3) := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, mul_one, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 19 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e20 : h₂ * g₂ ^ 3 * z = z ^ 4 * (h₂ * g₂ ^ 3) := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, mul_one, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 20 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e21 : g₂ ^ 3 * y = x ^ 2 * y ^ 4 * z ^ 4 * g₂ ^ 3 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, mul_one, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 21 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e22 : g₂ ^ 3 * z = z ^ 3 * g₂ ^ 3 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, mul_one, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 22 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e23 : g₂ ^ 2 * y = x ^ 2 * y * z ^ 2 * g₂ ^ 2 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, mul_one, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 23 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e24 : g₂ ^ 2 * z = z ^ 4 * g₂ ^ 2 := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, mul_one, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 24 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e25 : g₂ * y = x * y ^ 4 * z ^ 2 * g₂ := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, mul_one, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 25 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have e26 : g₂ * z = z ^ 2 * g₂ := by
    simpa only [wordUnit_cons, wordUnit_nil, pow_one, mul_one, mul_assoc] using
      regUnit_eq Sp hM (mem_facts 26 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
  have hrA : 0 < thLineCert.nregs := by decide
  have hrB : 1 < thLineCert.nregs := by decide
  have hvalA : valHom (certMonoid 2 248 NativeSporadic.ThSeed1 NativeSporadic.ThSeed2)
      (regUnit Sp hM 0) = NativeSporadic.decode 2 248 1 NativeSporadic.ThSeed1 := by
    rw [val_regUnit Sp hM (mem_facts 0 rfl),
      Sp.toMat_eq (reg_ok Sp hM hrA).1 (Sp.decode_wf _) hAeq, Sp.toMat_decode]
  have hvalB : valHom (certMonoid 2 248 NativeSporadic.ThSeed1 NativeSporadic.ThSeed2)
      (regUnit Sp hM 1) = NativeSporadic.decode 2 248 1 NativeSporadic.ThSeed2 := by
    rw [val_regUnit Sp hM (mem_facts 1 rfl),
      Sp.toMat_eq (reg_ok Sp hM hrB).1 (Sp.decode_wf _) hBeq, Sp.toMat_decode]
  have htop := CFSG.RankThree.PartOne.CTP.Fus.closure_pair_units_eq_top
    (certMonoid 2 248 NativeSporadic.ThSeed1 NativeSporadic.ThSeed2) rfl
    (regUnit Sp hM 0) (regUnit Sp hM 1) hvalA hvalB
  have hgen : Subgroup.closure ({h₁, h₂, g₂} : Set _) = ⊤ := by
    set T := Subgroup.closure ({h₁, h₂, g₂} : Set (certMonoid 2 248 NativeSporadic.ThSeed1
      NativeSporadic.ThSeed2)ˣ)
    have hreg : ∀ q : ℕ × ℕ, (q.1 = 82 ∨ q.1 = 84 ∨ q.1 = 25) → regUnit Sp hM q.1 ∈ T := by
      rintro q (h | h | h) <;> rw [h] <;> exact Subgroup.subset_closure (by simp [h₁, h₂, g₂])
    have hA0 := regUnit_eq Sp hM (mem_facts 27 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
    have hB0 := regUnit_eq Sp hM (mem_facts 28 rfl) (hasOrd_of_bool rfl) (hasOrd_of_bool rfl)
    rw [wordUnit_cons, wordUnit_nil, pow_one, mul_one] at hA0 hB0
    rw [eq_top_iff, ← htop, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · rw [hA0]
      exact CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup Sp hM T _
        fun q hq => hreg q (by revert q hq; decide)
    · rw [hB0]
      exact CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup Sp hM T _
        fun q hq => hreg q (by revert q hq; decide)
  exact centGen_eq_top_of_thFacts hx hy hz hzx hzy hxy hz1 hcard e12 e13 e14 e15 hF1 e17 e18 e19 e20
    e21 e22 e23 e24 e25 e26 hgen A hA hAc

end Concrete

section Wrapper

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
  CFSG.RankThree.Asc83Table CFSG.Blueprint TauCeti

set_option linter.unusedSectionVars false

theorem sporadicCentGen_Th_five_of_check
    (hC : seedCertCheck (ops2 248) NativeSporadic.ThSeed1 NativeSporadic.ThSeed2 thLineCert = true) :
    SporadicCentGen 5 .Th := by
  intro L _ _ ⟨e⟩ A hA hAc
  have hf := CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.carrierFacts_of_ne_M .Th
    (by decide)
  haveI : Finite (NativeSporadic.Carrier .Th) := hf.1
  haveI : IsSimpleGroup (NativeSporadic.Carrier .Th) := hf.2.1
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Th
  let ψ : L ≃* NativeSporadic.Carrier .Th := e.trans f.symm
  have hcard : ¬ 5 ^ 4 ∣ Nat.card (NativeSporadic.Carrier .Th) := by
    rw [CFSG.AGLEmbeddingD2.card_carrier_eq_d2SporadicOrder .Th (by decide)]
    norm_num [CFSG.AGLEmbeddingD2.d2SporadicOrder]
  refine centGen_eq_top_of_equiv ψ ?_
  exact centGen_Th_five_of_check hC hcard _ (isElemAbelian_map hA ψ)
    (by rw [card_map, hAc]; norm_num)

theorem sporadicCentGen_Th_five : SporadicCentGen 5 .Th :=
  sporadicCentGen_Th_five_of_check Certificates.certificate1322002

end Wrapper

section Assembly

open TauCeti

set_option linter.unusedSectionVars false

theorem sporadicGen24_12Five_of_M13
    (hM13 : SporadicCentGen 13 .M) :
    CFSG.LocalAnalysis.AGL81I.Section3.SporadicGen24_12Five :=
  sporadicGen24_12Five_of_inputs sporadicCentGen_Th_five hM13

end Assembly

end CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThFive

