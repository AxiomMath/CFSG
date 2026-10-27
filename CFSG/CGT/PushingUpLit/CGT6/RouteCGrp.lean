module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin

public section

namespace CFSG.CGT.PushingUpLit.CGT6.RouteC

open Subgroup

section SubnormalPCore

variable {H : Type*} [Group H]

theorem routeC_conj_mem_map_of_characteristic {X : Subgroup H} {D : Subgroup X}
    [hD : D.Characteristic] {g : H} (hg : g ∈ Subgroup.normalizer (X : Set H)) {x : H}
    (hx : x ∈ D.map X.subtype) : g * x * g⁻¹ ∈ D.map X.subtype := by
  obtain ⟨y, hy, rfl⟩ := hx
  let φ := Subgroup.normalizerMonoidHom X ⟨g, hg⟩
  have hfix : D.map φ.toMonoidHom = D := (Subgroup.characteristic_iff_map_eq.mp hD) φ
  refine ⟨φ y, ?_, ?_⟩
  · rw [← hfix]
    exact Subgroup.mem_map_of_mem _ hy
  · rw [Subgroup.coe_subtype, Subgroup.normalizerMonoidHom_apply_apply_coe]

theorem routeC_pCore_map_le_of_isSubnormal [Finite H] {p : ℕ} {X : Subgroup H}
    (hX : X.IsSubnormal) : (CFSG.pCore p X).map X.subtype ≤ CFSG.pCore p H := by
  have key : ∀ {X Y : Subgroup H}, X ≤ Y → Y ≤ Subgroup.normalizer (X : Set H) →
      (CFSG.pCore p X).map X.subtype ≤ (CFSG.pCore p Y).map Y.subtype := by
    intro X Y hXY hYN
    have hLY : (CFSG.pCore p X).map X.subtype ≤ Y := (Subgroup.map_subtype_le _).trans hXY
    have hle : ((CFSG.pCore p X).map X.subtype).subgroupOf Y ≤ CFSG.pCore p Y := by
      apply le_sSup
      refine ⟨⟨fun l hl y => ?_⟩, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hl ⊢
        simpa using routeC_conj_mem_map_of_characteristic (hYN y.2) hl
      · exact ((CFSG.pCore_isPGroup).map X.subtype).of_equiv
          (Subgroup.subgroupOfEquivOfLe hLY).symm
    calc (CFSG.pCore p X).map X.subtype
        = (((CFSG.pCore p X).map X.subtype).subgroupOf Y).map Y.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hLY).symm
      _ ≤ (CFSG.pCore p Y).map Y.subtype := Subgroup.map_mono hle
  induction hX with
  | top =>
    apply le_sSup
    refine ⟨⟨fun l hl g => routeC_conj_mem_map_of_characteristic ?_ hl⟩,
      (CFSG.pCore_isPGroup).map _⟩
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top g
  | step X Y hXY hY hN ih =>
    exact (key hXY ((Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mp hN)).trans ih

theorem routeC_le_pCore_of_isSubnormal [Finite H] {p : ℕ} {Z : Subgroup H}
    (hZ : Z.IsSubnormal) (hp : IsPGroup p ↥Z) : Z ≤ CFSG.pCore p H := by
  have htop : CFSG.pCore p Z = ⊤ :=
    le_antisymm le_top (le_sSup ⟨inferInstance, hp.of_equiv Subgroup.topEquiv.symm⟩)
  have h := routeC_pCore_map_le_of_isSubnormal (p := p) hZ
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h

end SubnormalPCore

section Kernel

variable {n : ℕ}

local notation "GLn" => (Matrix (Fin n) (Fin n) (ZMod 2))ˣ

private theorem vec_add_self' (v : Fin n → ZMod 2) : v + v = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize v i = a
  revert a
  decide

private theorem vec_eq_of_add_eq_zero' {u v : Fin n → ZMod 2} (h : u + v = 0) : u = v := by
  funext i
  have := congrFun h i
  simp only [Pi.add_apply, Pi.zero_apply] at this
  revert this
  generalize u i = a
  generalize v i = b
  revert a b
  decide

private theorem vec_add_cancel (x y z : Fin n → ZMod 2) : x + z = (x + y) + (y + z) := by
  funext i
  simp only [Pi.add_apply]
  generalize x i = a
  generalize y i = b
  generalize z i = c
  revert a b c
  decide

private theorem vec_eq_of_add_comm {x y z : Fin n → ZMod 2} (h : x + y = y + z) : x = z := by
  funext i
  have := congrFun h i
  simp only [Pi.add_apply] at this
  revert this
  generalize x i = a
  generalize y i = b
  generalize z i = c
  revert a b c
  decide

private theorem mat_ext_of_mulVec' {A B : Matrix (Fin n) (Fin n) (ZMod 2)}
    (h : ∀ x, A.mulVec x = B.mulVec x) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext h)

private theorem unit_inv_eq_of_pow_three {g : GLn} (h : g ^ 3 = 1) : g⁻¹ = g * g := by
  have : g * (g * g) = 1 := by rw [← pow_three]; exact h
  exact inv_eq_of_mul_eq_one_right this

private theorem unit_inv_eq_of_pow_two {g : GLn} (h : g ^ 2 = 1) : g⁻¹ = g := by
  have : g * g = 1 := by rw [← pow_two]; exact h
  exact inv_eq_of_mul_eq_one_right this

private theorem unit_mulVec_inv (a : GLn) (v : Fin n → ZMod 2) :
    (a : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
      (((a⁻¹ : GLn) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

private theorem unit_inv_mulVec (a : GLn) (v : Fin n → ZMod 2) :
    ((a⁻¹ : GLn) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
      ((a : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

private def unipW (W : Submodule (ZMod 2) (Fin n → ZMod 2)) : Subgroup GLn where
  carrier := {g | (∀ v, (g : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec v + v ∈ W) ∧
    ∀ w ∈ W, (g : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec w = w}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun v => ?_, fun w hw => ?_⟩
    · have := vec_add_cancel ((a : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
        ((b : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec v))
        ((b : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec v) v
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, this]
      exact W.add_mem (ha1 _) (hb1 v)
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hb2 w hw, ha2 w hw]
  one_mem' := by
    refine ⟨fun v => ?_, fun w hw => by simp⟩
    simp only [Units.val_one, Matrix.one_mulVec, vec_add_self']
    exact W.zero_mem
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨fun v => ?_, fun w hw => ?_⟩
    · have h1 := ha1 (((a⁻¹ : GLn) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec v)
      rw [unit_mulVec_inv, add_comm] at h1
      exact h1
    · have h1 := unit_inv_mulVec a w
      rw [ha2 w hw] at h1
      exact h1

private theorem sq_eq_one_of_mem_unipW {W : Submodule (ZMod 2) (Fin n → ZMod 2)} {g : GLn}
    (hg : g ∈ unipW W) : g * g = 1 := by
  obtain ⟨h1, h2⟩ := hg
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  apply mat_ext_of_mulVec'
  intro v
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  have h3 := h2 _ (h1 v)
  rw [Matrix.mulVec_add] at h3
  exact vec_eq_of_add_comm h3

theorem pCore_ne_bot_of_kernel (y d t : GLn) (hy3 : y ^ 3 = 1) (hd3 : d ^ 3 = 1)
    (ht2 : t ^ 2 = 1) (W : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hWy : ∀ w ∈ W, (y : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec w ∈ W)
    (hWd : ∀ w ∈ W, (d : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec w ∈ W)
    (hWt : ∀ w ∈ W, (t : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec w ∈ W)
    (k : GLn) (hk : k ∈ Subgroup.closure ({y, d, t} : Set GLn)) (hk1 : k ≠ 1)
    (hkW : ∀ v, (k : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec v + v ∈ W)
    (hkW' : ∀ w ∈ W, (k : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec w = w) :
    CFSG.pCore 2 ↥(Subgroup.closure ({y, d, t} : Set GLn)) ≠ ⊥ := by
  set G := Subgroup.closure ({y, d, t} : Set GLn) with hG
  have hinv : ∀ g ∈ G, (∀ w ∈ W, (g : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec w ∈ W) ∧
      (∀ w ∈ W, ((g⁻¹ : GLn) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec w ∈ W) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl | rfl
      · refine ⟨hWy, fun w hw => ?_⟩
        rw [unit_inv_eq_of_pow_three hy3, Units.val_mul, ← Matrix.mulVec_mulVec]
        exact hWy _ (hWy _ hw)
      · refine ⟨hWd, fun w hw => ?_⟩
        rw [unit_inv_eq_of_pow_three hd3, Units.val_mul, ← Matrix.mulVec_mulVec]
        exact hWd _ (hWd _ hw)
      · refine ⟨hWt, fun w hw => ?_⟩
        rw [unit_inv_eq_of_pow_two ht2]
        exact hWt w hw
    | one => exact ⟨fun w hw => by simpa using hw, fun w hw => by simpa using hw⟩
    | mul a b _ _ ha hb =>
      refine ⟨fun w hw => ?_, fun w hw => ?_⟩
      · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
        exact ha.1 _ (hb.1 w hw)
      · rw [mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
        exact hb.2 _ (ha.2 w hw)
    | inv a _ ha => exact ⟨ha.2, by simpa using ha.1⟩
  have hnorm : ((unipW W).subgroupOf G).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hg1, hg2⟩ := hinv (g : GLn) g.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hx1 hx2 ⊢
    refine ⟨fun v => ?_, fun w hw => ?_⟩
    · set u := (((g : GLn)⁻¹ : GLn) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec v with hu
      have hgu : (((g : GLn) : GLn) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec u = v :=
        unit_mulVec_inv _ v
      have h1 := hg1 _ (hx1 u)
      rw [Matrix.mulVec_add, hgu] at h1
      simpa [Units.val_mul, ← Matrix.mulVec_mulVec, hu] using h1
    · have hw' := hg2 w hw
      have hx' := hx2 _ hw'
      simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
      rw [hx']
      exact unit_mulVec_inv _ w
  have hpgrp : IsPGroup 2 ↥((unipW W).subgroupOf G) := by
    intro x
    refine ⟨1, ?_⟩
    have := sq_eq_one_of_mem_unipW x.2
    apply Subtype.ext
    apply Subtype.ext
    simpa [pow_two] using this
  have hmem : (⟨k, hk⟩ : ↥G) ∈ (unipW W).subgroupOf G := by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨hkW, hkW'⟩
  intro hbot
  have hle : (unipW W).subgroupOf G ≤ CFSG.pCore 2 ↥G := le_sSup ⟨hnorm, hpgrp⟩
  have := hle hmem
  rw [hbot, Subgroup.mem_bot] at this
  exact hk1 (congrArg Subtype.val this)

theorem not_subnormal_of_word (y d t c : GLn) (hy3 : y ^ 3 = 1)
    (hty : t * y = y * t) (htG : t ∈ Subgroup.closure ({y, d, t} : Set GLn))
    (hc : c ∈ Subgroup.closure ({y, d, t} : Set GLn)) (hct : t * c = c * t) (a m : ℕ)
    (hm : m % 3 ≠ 0) (hx : (y * (c * (y * c⁻¹))) ^ a ≠ 1)
    (hxm : ((y * (c * (y * c⁻¹))) ^ a) ^ m = 1)
    (hsub : ((Subgroup.zpowers y).subgroupOf (Subgroup.closure ({y, d, t} : Set GLn) ⊓
      Subgroup.centralizer ({t} : Set GLn))).IsSubnormal) : False := by
  set G := Subgroup.closure ({y, d, t} : Set GLn) with hG
  set H := G ⊓ Subgroup.centralizer ({t} : Set GLn) with hH
  have hyG : y ∈ G := Subgroup.subset_closure (by simp)
  have hyH : y ∈ H := ⟨hyG, Subgroup.mem_centralizer_iff.mpr (by
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hty)⟩
  have hcH : c ∈ H := ⟨hc, Subgroup.mem_centralizer_iff.mpr (by
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hct)⟩
  have hp3 : IsPGroup 3 ↥((Subgroup.zpowers y).subgroupOf H) := by
    intro z
    refine ⟨1, ?_⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp z.2
    apply Subtype.ext
    apply Subtype.ext
    have : (z : H).1 = y ^ j := hj.symm
    simp only [pow_one, SubmonoidClass.coe_pow, this]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
    rfl
  have hle := routeC_le_pCore_of_isSubnormal hsub hp3
  set y' : ↥H := ⟨y, hyH⟩ with hy'
  set c' : ↥H := ⟨c, hcH⟩ with hc'
  have hy'mem : y' ∈ CFSG.pCore 3 ↥H :=
    hle (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers y))
  have hcyc : c' * y' * c'⁻¹ ∈ CFSG.pCore 3 ↥H :=
    (CFSG.pCore_normal (p := 3) (G := ↥H)).conj_mem y' hy'mem c'
  have hprod : y' * (c' * y' * c'⁻¹) ∈ CFSG.pCore 3 ↥H := Subgroup.mul_mem _ hy'mem hcyc
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 3) (G := ↥H)) ⟨_, hprod⟩
  have hk' : (y * (c * (y * c⁻¹))) ^ 3 ^ k = 1 := by
    have := congrArg (fun z : ↥(CFSG.pCore 3 ↥H) => ((z : ↥H) : GLn)) hk
    simpa [mul_assoc] using this
  set x := y * (c * (y * c⁻¹)) with hxdef
  have h1 : (x ^ a) ^ 3 ^ k = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hk', one_pow]
  have hcop : Nat.Coprime (3 ^ k) m :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega))
  have h2 : orderOf (x ^ a) ∣ Nat.gcd (3 ^ k) m :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one hxm)
  rw [hcop] at h2
  exact hx (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h2))

end Kernel

end CFSG.CGT.PushingUpLit.CGT6.RouteC
