module

public import CFSG.CGT.Stroth77.Stroth34Coord

public section

namespace CFSG.CGT.Stroth77

section Torus

variable {k : Fin 3 → ℕ}

theorem val_add_mod_two {e : ℕ} (he : 1 ≤ e) (a b : ZMod (2 ^ e)) :
    (a + b).val % 2 = (a.val + b.val) % 2 := by
  haveI : NeZero (2 ^ e) := ⟨by positivity⟩
  rw [ZMod.val_add, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))]

theorem nsmul_eq_mod_two {A : Type*} [AddCommGroup A] {w : A} (hw : w + w = 0) (m : ℕ) :
    m • w = (m % 2) • w := by
  conv_lhs => rw [← Nat.mod_add_div m 2]
  rw [add_nsmul, two_mul, add_nsmul, ← nsmul_add, hw, nsmul_zero, add_zero]

theorem zsmul_eq_self_of_odd {A : Type*} [AddCommGroup A] {w : A} (hw : w + w = 0) {α : ℤ}
    (hα : Odd α) : α • w = w := by
  obtain ⟨j, rfl⟩ := hα
  rw [add_zsmul, one_zsmul, two_mul, add_zsmul, ← zsmul_add, hw, zsmul_zero, zero_add]

theorem val_zsmul_odd_mod_two {e : ℕ} (he : 1 ≤ e) {α : ℤ} (hα : Odd α) (a : ZMod (2 ^ e)) :
    (α • a).val % 2 = a.val % 2 := by
  obtain ⟨j, rfl⟩ := hα
  rw [add_zsmul, one_zsmul, two_mul, add_zsmul, val_add_mod_two he, Nat.add_mod,
    val_add_mod_two he]
  omega

theorem nsmul_eq_of_mod_two {A : Type*} [AddCommGroup A] {w : A} (hw : w + w = 0) {m m' : ℕ}
    (h : m % 2 = m' % 2) : m • w = m' • w := by
  rw [nsmul_eq_mod_two hw m, nsmul_eq_mod_two hw m', h]

@[expose] def nuMap (w x : Torus k) : Torus k := x + (x 0).val • w

theorem nuMap_apply_zero {w : Torus k} (hw0 : w 0 = 0) (x : Torus k) : (nuMap w x) 0 = x 0 := by
  simp [nuMap, hw0]

theorem nuMap_nuMap {w w' : Torus k} (hw0' : w' 0 = 0) (x : Torus k) :
    nuMap w (nuMap w' x) = nuMap (w + w') x := by
  rw [nuMap, nuMap_apply_zero hw0', nuMap, nuMap, nsmul_add]
  abel

theorem nuMap_zero (x : Torus k) : nuMap 0 x = x := by simp [nuMap]

theorem nuMap_eq_self_iff {w : Torus k} (hw : w + w = 0) (hw' : w ≠ 0) (x : Torus k) :
    nuMap w x = x ↔ (x 0).val % 2 = 0 := by
  unfold nuMap
  rw [add_eq_left, nsmul_eq_mod_two hw]
  rcases Nat.mod_two_eq_zero_or_one (x 0).val with h | h <;> rw [h] <;> simp [hw']

theorem gen_zero_val (hk : 1 ≤ k 0) : ((gen k 0) 0).val = 1 := by
  haveI : Fact (1 < 2 ^ k 0) := ⟨Nat.one_lt_two_pow (by omega)⟩
  simp [gen, ZMod.val_one]

theorem nuMap_gen_zero (hk : 1 ≤ k 0) (w : Torus k) : nuMap w (gen k 0) = gen k 0 + w := by
  rw [nuMap, gen_zero_val hk, one_nsmul]

theorem nuMap_injective (hk : 1 ≤ k 0) {w w' : Torus k} (h : ∀ x, nuMap w x = nuMap w' x) :
    w = w' := by
  have := h (gen k 0)
  rwa [nuMap_gen_zero hk, nuMap_gen_zero hk, add_right_inj] at this

theorem val_neg_mod_two {e : ℕ} (he : 1 ≤ e) (a : ZMod (2 ^ e)) : (-a).val % 2 = a.val % 2 := by
  have h := val_add_mod_two he a (-a)
  rw [add_neg_cancel, ZMod.val_zero] at h
  omega

theorem commutator_mul_of_commute {G : Type*} [Group G] {e f r r' : G} (hre : Commute r e)
    (hrf : Commute r f) (hr'e : Commute r' e) (hr'f : Commute r' f) (hrr' : Commute r r') :
    (e * r)⁻¹ * (f * r')⁻¹ * (e * r) * (f * r') = e⁻¹ * f⁻¹ * e * f := by
  have h1 : Commute r' (f⁻¹ * e * f) := (hr'f.inv_right.mul_right hr'e).mul_right hr'f
  have h2 : Commute r (e⁻¹ * f⁻¹ * e * f) :=
    ((hre.inv_right.mul_right hrf.inv_right).mul_right hre).mul_right hrf
  calc (e * r)⁻¹ * (f * r')⁻¹ * (e * r) * (f * r')
      = r⁻¹ * e⁻¹ * r'⁻¹ * f⁻¹ * e * (r * f) * r' := by group
    _ = r⁻¹ * e⁻¹ * r'⁻¹ * f⁻¹ * e * (f * r) * r' := by rw [hrf.eq]
    _ = r⁻¹ * e⁻¹ * r'⁻¹ * f⁻¹ * e * f * (r * r') := by group
    _ = r⁻¹ * e⁻¹ * r'⁻¹ * f⁻¹ * e * f * (r' * r) := by rw [hrr'.eq]
    _ = r⁻¹ * (e⁻¹ * (r'⁻¹ * (f⁻¹ * e * f) * r')) * r := by group
    _ = r⁻¹ * (e⁻¹ * f⁻¹ * e * f) * r := by rw [h1.inv_mul_cancel]; group
    _ = e⁻¹ * f⁻¹ * e * f := h2.inv_mul_cancel

theorem val_mod_two_eq_zero_of_add_self {e : ℕ} (he : 2 ≤ e) {z : ZMod (2 ^ e)} (h : z + z = 0) :
    z.val % 2 = 0 := by
  haveI : NeZero (2 ^ e) := ⟨by positivity⟩
  have h1 := congrArg ZMod.val h
  rw [ZMod.val_add, ZMod.val_zero] at h1
  have h2 : 2 ^ e ∣ z.val + z.val := Nat.dvd_of_mod_eq_zero h1
  have h4 : 4 ∣ 2 ^ e := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ∣ 2 ^ e := pow_dvd_pow 2 he
  have := dvd_trans h4 h2
  omega

end Torus

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {τ : StrothTypeIndex}
  (dD : StrothWeakTypeData D τ)

@[expose] noncomputable def ofT (x : Torus τ.k) : G := ((Additive.toMul (dD.e.symm x) : D) : G)

theorem ofT_mem (x : Torus τ.k) : dD.ofT x ∈ D := (Additive.toMul (dD.e.symm x)).2

theorem crdT_ofT (x : Torus τ.k) : crdT dD.e (dD.ofT x) = x := by
  rw [crdT_of_mem dD.e (dD.ofT_mem x)]
  simp [ofT]

theorem ofT_crdT {d : G} (hd : d ∈ D) : dD.ofT (crdT dD.e d) = d := by
  rw [crdT_of_mem dD.e hd]
  simp [ofT]

theorem ofT_add (x y : Torus τ.k) : dD.ofT (x + y) = dD.ofT x * dD.ofT y := by
  simp [ofT]

theorem ofT_zero : dD.ofT 0 = 1 := by simp [ofT]

theorem ofT_zsmul (i : ℤ) (x : Torus τ.k) : dD.ofT (i • x) = dD.ofT x ^ i := by
  unfold ofT
  rw [map_zsmul, toMul_zsmul, Subgroup.coe_zpow]

@[expose] noncomputable def thetaT {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) :
    Torus τ.k →+ Torus τ.k where
  toFun x := crdT dD.e (g⁻¹ * dD.ofT x * g)
  map_zero' := by rw [ofT_zero, mul_one, inv_mul_cancel, crdT_one]
  map_add' x y := by
    have hx := (Subgroup.mem_normalizer_iff''.mp hg _).mp (dD.ofT_mem x)
    have hy := (Subgroup.mem_normalizer_iff''.mp hg _).mp (dD.ofT_mem y)
    rw [ofT_add, ← crdT_mul dD.e hx hy]
    congr 1
    group

theorem thetaT_apply {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) (x : Torus τ.k) :
    dD.thetaT hg x = crdT dD.e (g⁻¹ * dD.ofT x * g) := rfl

theorem thetaT_crdT {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) {d : G} (hd : d ∈ D) :
    dD.thetaT hg (crdT dD.e d) = crdT dD.e (g⁻¹ * d * g) := by
  rw [thetaT_apply, ofT_crdT dD hd]

theorem thetaT_mul {g h : G} (hg : g ∈ Subgroup.normalizer (D : Set G))
    (hh : h ∈ Subgroup.normalizer (D : Set G)) (x : Torus τ.k) :
    dD.thetaT (mul_mem hg hh) x = dD.thetaT hh (dD.thetaT hg x) := by
  have hx := (Subgroup.mem_normalizer_iff''.mp hg _).mp (dD.ofT_mem x)
  rw [thetaT_apply, thetaT_apply, thetaT_apply, ofT_crdT dD hx]
  congr 1
  group

theorem thetaT_of_mem_centralizer {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G))
    (hc : g ∈ Subgroup.centralizer (D : Set G)) (x : Torus τ.k) : dD.thetaT hg x = x := by
  rw [thetaT_apply, mul_assoc, Subgroup.mem_centralizer_iff.mp hc _ (dD.ofT_mem x),
    inv_mul_cancel_left, crdT_ofT]

theorem thetaT_of_mem {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) (hgD : g ∈ D)
    (x : Torus τ.k) : dD.thetaT hg x = x := by
  have hc : g ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (dD.isMulCommutative.is_comm.comm (⟨y, hy⟩ : D) ⟨g, hgD⟩)
  exact dD.thetaT_of_mem_centralizer hg hc x

theorem mem_centralizer_of_thetaT {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G))
    (hid : ∀ x, dD.thetaT hg x = x) : g ∈ Subgroup.centralizer (D : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hd' := (Subgroup.mem_normalizer_iff''.mp hg d).mp hd
  have e := hid (crdT dD.e d)
  rw [thetaT_crdT dD hg hd] at e
  have := crdT_inj dD.e hd' hd e
  calc d * g = g * (g⁻¹ * d * g) := by group
    _ = g * d := by rw [this]

theorem thetaT_uv (x : Torus τ.k) : dD.thetaT dD.uv_mem x = τ.action.φuv x := by
  rw [thetaT_apply, crdT_conj dD.e dD.uv_mem dD.uv_conj (dD.ofT_mem x), crdT_ofT]

theorem thetaT_t (x : Torus τ.k) : dD.thetaT dD.t_mem x = τ.action.φt x := by
  rw [thetaT_apply, crdT_conj dD.e dD.t_mem dD.t_conj (dD.ofT_mem x), crdT_ofT]

theorem thetaT_u (x : Torus τ.k) : dD.thetaT dD.u_mem x = τ.action.φu x := by
  rw [thetaT_apply, crdT_conj dD.e dD.u_mem dD.u_conj (dD.ofT_mem x), crdT_ofT]

theorem thetaT_ρ (x : Torus τ.k) : dD.thetaT dD.ρ_mem x = τ.action.φρ x := by
  rw [thetaT_apply, crdT_conj dD.e dD.ρ_mem dD.ρ_conj (dD.ofT_mem x), crdT_ofT]

theorem φρ_cube (x : Torus τ.k) : τ.action.φρ (τ.action.φρ (τ.action.φρ x)) = x :=
  DFunLike.congr_fun τ.action.rels.rho_cube x

theorem thetaT_ρ_inv (x : Torus τ.k) :
    dD.thetaT (inv_mem dD.ρ_mem) x = τ.action.φρ (τ.action.φρ x) := by
  have key := dD.thetaT_mul dD.ρ_mem (inv_mem dD.ρ_mem) (τ.action.φρ (τ.action.φρ x))
  rw [dD.thetaT_of_mem_centralizer _ (by rw [mul_inv_cancel]; exact one_mem _), thetaT_ρ,
    φρ_cube] at key
  exact key.symm

end StrothWeakTypeData

end CFSG.CGT.Stroth77
