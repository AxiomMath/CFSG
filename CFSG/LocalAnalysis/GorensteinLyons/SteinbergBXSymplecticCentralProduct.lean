module

public import CFSG.Open.GLADefs
public import CFSG.GroupTheory.SteinbergBKFrattiniElementaryKernel
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXPointwiseAutModule
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCBExponentFourLayer
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup
open scoped commutatorElement IsMulCommutative

structure CommPairHyp (P : Type*) [Group P] (z : P) : Prop where
  mem_center : z ∈ center P
  orderOf_eq : orderOf z = 2
  comm_pair : ∀ a b : P, ⁅a, b⁆ = 1 ∨ ⁅a, b⁆ = z
  sq_mem_center : ∀ a : P, a ^ 2 ∈ center P

namespace CommPairHyp

variable {P : Type*} [Group P] {z : P} (H : CommPairHyp P z)
include H

theorem z_ne_one : z ≠ 1 := by
  intro h
  have := H.orderOf_eq
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem z_mul_z : z * z = 1 := by
  rw [← pow_two, ← H.orderOf_eq, pow_orderOf_eq_one]

theorem pair_mul {x y : P} (hx : x = 1 ∨ x = z) (hy : y = 1 ∨ y = z) :
    x * y = 1 ∨ x * y = z := by
  rcases hx with h | h <;> rcases hy with h' | h' <;> rw [h, h']
  · exact Or.inl (mul_one 1)
  · exact Or.inr (one_mul z)
  · exact Or.inr (mul_one z)
  · exact Or.inl H.z_mul_z

theorem pair_inv {x : P} (hx : x = 1 ∨ x = z) : x⁻¹ = x := by
  rcases hx with h | h <;> rw [h]
  · exact inv_one
  · exact inv_eq_of_mul_eq_one_right H.z_mul_z

theorem zlog_one : zlog z 1 = 0 := by
  rw [zlog, ite_eq_right (Ne.symm H.z_ne_one)]

omit [Group P] H in
theorem zlog_self : zlog z z = 1 := by
  rw [zlog, ite_eq_left rfl]

theorem eq_zpow_zlog {x : P} (hx : x = 1 ∨ x = z) : x = z ^ (zlog z x).val := by
  rcases hx with h | h <;> rw [h]
  · rw [H.zlog_one, ZMod.val_zero, pow_zero]
  · rw [zlog_self]; exact (pow_one z).symm

theorem zlog_mul {x y : P} (hx : x = 1 ∨ x = z) (hy : y = 1 ∨ y = z) :
    zlog z (x * y) = zlog z x + zlog z y := by
  rcases hx with h | h <;> rcases hy with h' | h' <;> rw [h, h']
  · rw [mul_one, H.zlog_one, add_zero]
  · rw [one_mul, H.zlog_one, zero_add]
  · rw [mul_one, H.zlog_one, add_zero]
  · rw [H.z_mul_z, H.zlog_one, zlog_self]; decide

theorem zlog_eq_zero_iff {x : P} (hx : x = 1 ∨ x = z) : zlog z x = 0 ↔ x = 1 := by
  rcases hx with h | h <;> rw [h]
  · simp [H.zlog_one]
  · rw [zlog_self]; simp [H.z_ne_one]

theorem zlog_eq_one_iff {x : P} (hx : x = 1 ∨ x = z) : zlog z x = 1 ↔ x = z := by
  rcases hx with h | h <;> rw [h]
  · rw [H.zlog_one]; simp [Ne.symm H.z_ne_one]
  · rw [zlog_self]; simp

theorem comm_center (a b : P) : ⁅a, b⁆ ∈ center P := by
  rcases H.comm_pair a b with h | h <;> rw [h]
  · exact one_mem _
  · exact H.mem_center

theorem comm_mul_left (a a' b : P) : ⁅a * a', b⁆ = ⁅a, b⁆ * ⁅a', b⁆ := by
  rw [commutatorElement_mul_left_of_mem_center (H.comm_center a' b)]
  exact (mem_center_iff.mp (H.comm_center a' b) _).symm

theorem comm_mul_right (a b b' : P) : ⁅a, b * b'⁆ = ⁅a, b⁆ * ⁅a, b'⁆ := by
  have h1 : ⁅a, b * b'⁆ = ⁅b * b', a⁆⁻¹ := by rw [commutatorElement_inv]
  rw [h1, H.comm_mul_left, mul_inv_rev, commutatorElement_inv, commutatorElement_inv]
  exact mem_center_iff.mp (H.comm_center a b) _

theorem comm_symm (a b : P) : ⁅b, a⁆ = ⁅a, b⁆ := by
  rw [← commutatorElement_inv, H.pair_inv (H.comm_pair a b)]

theorem comm_inv_left (a b : P) : ⁅a⁻¹, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_inv_left_of_mem_center (H.comm_center a b), H.pair_inv (H.comm_pair a b)]

theorem comm_inv_right (a b : P) : ⁅a, b⁻¹⁆ = ⁅a, b⁆ := by
  rw [← H.comm_symm, H.comm_inv_left, H.comm_symm]

theorem inv_comm_eq (a b : P) : a⁻¹ * b⁻¹ * a * b = ⁅a, b⁆ := by
  have : a⁻¹ * b⁻¹ * a * b = ⁅a⁻¹, b⁻¹⁆ := by
    rw [commutatorElement_def, inv_inv, inv_inv]
  rw [this, H.comm_inv_left, H.comm_inv_right]

omit H in
theorem comm_of_mem_center_right (a : P) {t : P} (ht : t ∈ center P) : ⁅a, t⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp ht a)

theorem comm_mul_center_left (a b : P) {t : P} (ht : t ∈ center P) : ⁅a * t, b⁆ = ⁅a, b⁆ := by
  rw [H.comm_mul_left, H.comm_symm b t, comm_of_mem_center_right b ht, mul_one]

theorem comm_mul_center_right (a b : P) {t : P} (ht : t ∈ center P) : ⁅a, b * t⁆ = ⁅a, b⁆ := by
  rw [H.comm_mul_right, comm_of_mem_center_right a ht, mul_one]

theorem sq_mul (a b : P) : (a * b) ^ 2 = ⁅b, a⁆ * a ^ 2 * b ^ 2 := by
  have hc := mem_center_iff.mp (H.comm_center b a) a
  calc (a * b) ^ 2 = a * (b * a * b⁻¹ * a⁻¹) * a * b * b := by rw [pow_two]; group
    _ = a * ⁅b, a⁆ * a * b * b := by rw [commutatorElement_def]
    _ = ⁅b, a⁆ * a * a * b * b := by rw [hc]
    _ = ⁅b, a⁆ * a ^ 2 * b ^ 2 := by rw [pow_two, pow_two]; simp only [mul_assoc]

end CommPairHyp

section Recognition

variable {G : Type*} [Group G]

theorem mk_mem_zpowers_iff {E : Subgroup G} {z x : G} (hzE : z ∈ E) (hx : x ∈ E) :
    (⟨x, hx⟩ : E) ∈ zpowers (⟨z, hzE⟩ : E) ↔ x ∈ zpowers z := by
  simp only [mem_zpowers_iff, Subtype.ext_iff, coe_zpow]

theorem isExtraspecialPGroup_two_of_forall {E : Subgroup G} [Finite E] (hE : IsPGroup 2 E)
    {z : G} (hzE : z ∈ E) (hz : orderOf z = 2)
    (hcen : ∀ x ∈ E, (∀ y ∈ E, x * y = y * x) ↔ x ∈ zpowers z)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ zpowers z) (hsq : ∀ x ∈ E, x ^ 2 ∈ zpowers z)
    (hnab : ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x) :
    IsExtraspecialPGroup 2 E ∧ (center E).map E.subtype = zpowers z := by
  set z' : E := ⟨z, hzE⟩ with hz'
  have commutatorElement_mem : ∀ {a b : G}, a ∈ E → b ∈ E → ⁅a, b⁆ ∈ E := fun ha hb => by
    rw [commutatorElement_def]
    exact E.mul_mem (E.mul_mem (E.mul_mem ha hb) (E.inv_mem ha)) (E.inv_mem hb)
  have hcenter : center E = zpowers z' := by
    ext ⟨x, hx⟩
    rw [mem_center_iff, mk_mem_zpowers_iff hzE hx, ← hcen x hx]
    constructor
    · intro h y hy
      exact (congrArg Subtype.val (h ⟨y, hy⟩)).symm
    · intro h g
      exact Subtype.ext (h g g.2).symm
  have hmap : (center E).map E.subtype = zpowers z := by
    rw [hcenter, MonoidHom.map_zpowers]
    rfl
  have hzc : zpowers z' ≤ center E := hcenter.ge
  have : (zpowers z').Normal := normal_of_le_center hzc
  have hcommE : commutator E = zpowers z' := by
    apply le_antisymm
    · rw [_root_.commutator_def, commutator_le]
      rintro ⟨x, hx⟩ - ⟨y, hy⟩ -
      have h1 := hcomm x hx y hy
      rw [← mk_mem_zpowers_iff hzE (show ⁅x, y⁆ ∈ E from commutatorElement_mem hx hy)] at h1
      exact h1
    · obtain ⟨x, hx, y, hy, hxy⟩ := hnab
      have hxy' : ⁅x, y⁆ = z := by
        rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hz (hcomm x hx y hy) with h | h
        · exact absurd (commutatorElement_eq_one_iff_mul_comm.mp h) hxy
        · exact h
      rw [zpowers_le]
      have : z' = ⁅(⟨x, hx⟩ : E), ⟨y, hy⟩⁆ := Subtype.ext hxy'.symm
      rw [this]
      exact commutator_mem_commutator (mem_top _) (mem_top _)
  have hfr := (CFSG.GroupTheory.frattini_elementary_quotient (p := 2) hE).2.1
  have hcommle : commutator E ≤ frattini E := by
    rw [_root_.commutator_def, commutator_le]
    intro a _ b _
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (frattini E) ⁅a, b⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hfr.is_comm.comm _ _
  have hquot : CFSG.IsElementaryAbelian 2 (E ⧸ zpowers z') :=
    { toIsMulCommutative := ⟨⟨fun u v => by
        induction u using QuotientGroup.induction_on with | H x =>
        induction v using QuotientGroup.induction_on with | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have e : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
          simp only [commutatorElement_def, inv_inv]; group
        rw [e]
        have h1 := hcomm _ (inv_mem y.2) _ (inv_mem x.2)
        rw [← mk_mem_zpowers_iff hzE (commutatorElement_mem (inv_mem y.2) (inv_mem x.2))] at h1
        exact h1⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun u => by
        induction u using QuotientGroup.induction_on with | H x =>
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
        have h1 := hsq x x.2
        rw [← mk_mem_zpowers_iff hzE (pow_mem x.2 2)] at h1
        exact h1 }
  have hfrle : frattini E ≤ zpowers z' :=
    (CFSG.GroupTheory.SteinbergBK.frattini_elementary_quotient_kernel.{_, 0} (p := 2)).1 _ hquot
  refine ⟨⟨hE, by rw [hcommE, hcenter], ?_, ?_⟩, hmap⟩
  · rw [hcenter]
    exact le_antisymm hfrle (hcommE ▸ hcommle)
  · rw [hcenter, Nat.card_zpowers, hz', Subgroup.orderOf_mk, hz]

end Recognition


section Form

variable {P : Type*} [Group P]

@[expose] noncomputable def commVal (z : P) (u v : P ⧸ center P) : ZMod 2 :=
  zlog z ⁅Quotient.out u, Quotient.out v⁆

namespace CommPairHyp

variable {z : P} (H : CommPairHyp P z)
include H

theorem commVal_mk (x y : P) :
    commVal z (x : P ⧸ center P) (y : P ⧸ center P) = zlog z ⁅x, y⁆ := by
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul (center P) x
  obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul (center P) y
  rw [commVal, hs, ht, H.comm_mul_center_left _ _ s.2, H.comm_mul_center_right _ _ t.2]

theorem commVal_mul_left (u u' v : P ⧸ center P) :
    commVal z (u * u') v = commVal z u v + commVal z u' v := by
  induction u using QuotientGroup.induction_on with | H x =>
  induction u' using QuotientGroup.induction_on with | H x' =>
  induction v using QuotientGroup.induction_on with | H y =>
  rw [← QuotientGroup.mk_mul, H.commVal_mk, H.commVal_mk, H.commVal_mk, H.comm_mul_left,
    H.zlog_mul (H.comm_pair _ _) (H.comm_pair _ _)]

theorem commVal_mul_right (u v v' : P ⧸ center P) :
    commVal z u (v * v') = commVal z u v + commVal z u v' := by
  induction u using QuotientGroup.induction_on with | H x =>
  induction v using QuotientGroup.induction_on with | H y =>
  induction v' using QuotientGroup.induction_on with | H y' =>
  rw [← QuotientGroup.mk_mul, H.commVal_mk, H.commVal_mk, H.commVal_mk, H.comm_mul_right,
    H.zlog_mul (H.comm_pair _ _) (H.comm_pair _ _)]

theorem commVal_self (u : P ⧸ center P) : commVal z u u = 0 := by
  induction u using QuotientGroup.induction_on with | H x =>
  rw [H.commVal_mk, commutatorElement_self, H.zlog_one]

theorem commVal_comm (u v : P ⧸ center P) : commVal z u v = commVal z v u := by
  induction u using QuotientGroup.induction_on with | H x =>
  induction v using QuotientGroup.induction_on with | H y =>
  rw [H.commVal_mk, H.commVal_mk, H.comm_symm]

theorem commVal_eq_zero_iff (x y : P) :
    commVal z (x : P ⧸ center P) (y : P ⧸ center P) = 0 ↔ x * y = y * x := by
  rw [H.commVal_mk, H.zlog_eq_zero_iff (H.comm_pair x y), commutatorElement_eq_one_iff_mul_comm]

theorem commutatorElement_eq_zpow (x y : P) :
    ⁅x, y⁆ = z ^ (commVal z (x : P ⧸ center P) (y : P ⧸ center P)).val := by
  rw [H.commVal_mk]
  exact H.eq_zpow_zlog (H.comm_pair x y)

theorem eq_one_of_forall_commVal_eq_zero {u : P ⧸ center P} (h : ∀ v, commVal z u v = 0) :
    u = 1 := by
  induction u using QuotientGroup.induction_on with | H x =>
  rw [QuotientGroup.eq_one_iff, mem_center_iff]
  intro g
  exact ((H.commVal_eq_zero_iff x g).mp (h g)).symm

theorem isElementaryAbelian_quotient : CFSG.IsElementaryAbelian 2 (P ⧸ center P) :=
  { toIsMulCommutative := ⟨⟨fun u v => by
      induction u using QuotientGroup.induction_on with | H x =>
      induction v using QuotientGroup.induction_on with | H y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have e : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
        simp only [commutatorElement_def, inv_inv]; group
      rw [e]
      exact H.comm_center _ _⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun u => by
      induction u using QuotientGroup.induction_on with | H x =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact H.sq_mem_center x }

variable [CFSG.IsElementaryAbelian 2 (P ⧸ center P)]

@[expose] noncomputable def commAdd :
    Additive (P ⧸ center P) →+ Additive (P ⧸ center P) →+ ZMod 2 :=
  AddMonoidHom.mk' (fun u => AddMonoidHom.mk' (fun v => commVal z u.toMul v.toMul)
    fun _ _ => H.commVal_mul_right _ _ _) fun _ _ =>
      AddMonoidHom.ext fun _ => H.commVal_mul_left _ _ _

@[expose] noncomputable def commForm : LinearMap.BilinForm (ZMod 2) (Additive (P ⧸ center P)) :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := fun u => AddMonoidHom.toZModLinearMap 2 (H.commAdd u)
      map_zero' := by ext v; simp
      map_add' := fun _ _ => by ext v; simp }

theorem commForm_apply (u v : Additive (P ⧸ center P)) :
    H.commForm u v = commVal z u.toMul v.toMul :=
  rfl

theorem commForm_isAlt : H.commForm.IsAlt := fun _ => H.commVal_self _

theorem commForm_nondegenerate : H.commForm.Nondegenerate := by
  refine ⟨fun u hu => ?_, fun v hv => ?_⟩
  · exact toMul_eq_one.mp (H.eq_one_of_forall_commVal_eq_zero fun w => hu (Additive.ofMul w))
  · refine toMul_eq_one.mp (H.eq_one_of_forall_commVal_eq_zero fun w => ?_)
    rw [H.commVal_comm]
    exact hv (Additive.ofMul w)

theorem commForm_comm (u v : Additive (P ⧸ center P)) : H.commForm u v = H.commForm v u :=
  H.commVal_comm _ _

end CommPairHyp

end Form

section SymplecticMatrix

variable {m : ℕ}

theorem J_inl_inl (i j : Fin m) : Matrix.J (Fin m) (ZMod 2) (Sum.inl i) (Sum.inl j) = 0 := by
  simp [Matrix.J]

theorem J_inr_inr (i j : Fin m) : Matrix.J (Fin m) (ZMod 2) (Sum.inr i) (Sum.inr j) = 0 := by
  simp [Matrix.J]

theorem J_inl_inr (i j : Fin m) :
    Matrix.J (Fin m) (ZMod 2) (Sum.inl i) (Sum.inr j) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h; simp [Matrix.J]
  · simp [Matrix.J, h]

theorem J_inr_inl (i j : Fin m) :
    Matrix.J (Fin m) (ZMod 2) (Sum.inr i) (Sum.inl j) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h; simp [Matrix.J]
  · simp [Matrix.J, h]

end SymplecticMatrix


section TypeLevel

variable {P : Type*} [Group P]

theorem mem_zpowers_of_sq_eq_one [Finite P] (hcyc : IsCyclic (center P)) {z : P}
    (hzc : z ∈ center P) (hz : orderOf z = 2) {y : P} (hyc : y ∈ center P) (hy : y ^ 2 = 1) :
    y ∈ zpowers z :=
  mem_of_pow_eq_one_of_isCyclic hcyc (zpowers_le.mpr hzc) two_pos
    (by rw [Nat.card_zpowers, hz]) hyc hy

theorem sq_mem_center_and_comm_mem_center [Finite P] (hP : IsPGroup 2 P)
    (hΦ : frattini P ≤ center P) :
    (∀ x : P, x ^ 2 ∈ center P) ∧ ∀ x y : P, ⁅x, y⁆ ∈ center P := by
  obtain ⟨-, hcomm, hpow, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient (p := 2) hP
  refine ⟨fun x => hΦ ?_, fun x y => hΦ ?_⟩
  · rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hpow _
  · rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (frattini P) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.is_comm.comm _ _

theorem exists_commPairHyp [Finite P] [Nontrivial P] (hP : IsPGroup 2 P)
    (hcyc : IsCyclic (center P)) (hΦ : frattini P ≤ center P) :
    ∃ z : P, CommPairHyp P z ∧ ∀ y ∈ center P, y ^ 2 = 1 → y ∈ zpowers z := by
  have : Nontrivial (center P) := hP.center_nontrivial
  obtain ⟨n, hn0, hn⟩ := (hP.to_subgroup (center P)).nontrivial_iff_card.mp inferInstance
  obtain ⟨⟨z, hzc⟩, hz⟩ :=
    exists_prime_orderOf_dvd_card' (G := center P) 2 (hn ▸ dvd_pow_self 2 hn0.ne')
  rw [Subgroup.orderOf_mk] at hz
  obtain ⟨hsq, hcomm⟩ := sq_mem_center_and_comm_mem_center hP hΦ
  have huniq : ∀ y ∈ center P, y ^ 2 = 1 → y ∈ zpowers z := fun y hyc hy =>
    mem_zpowers_of_sq_eq_one hcyc hzc hz hyc hy
  refine ⟨z, ⟨hzc, hz, fun a b => ?_, hsq⟩, huniq⟩
  apply eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hz
  apply huniq _ (hcomm a b)
  rw [← commutatorElement_pow_left_of_mem_center (hcomm a b)]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hsq a) b).symm

structure IsCentralFactor (E : Subgroup P) (z : P) (w : ℕ) : Prop where
  extraspecial : IsExtraspecialPGroup 2 E
  card : Nat.card E = 2 ^ (1 + 2 * w)
  sup_center : E ⊔ center P = ⊤
  inf_center : E ⊓ center P = zpowers z
  center_eq : (center E).map E.subtype = zpowers z
  pow_four : ∀ e ∈ E, e ^ 4 = 1

theorem isCentralFactor_of [Finite P] (hP : IsPGroup 2 P) {z : P} (H : CommPairHyp P z)
    {w : ℕ} (hV : Nat.card (P ⧸ center P) = 2 ^ (2 * w)) {E : Subgroup P} (hzE : z ∈ E)
    (hsup : E ⊔ center P = ⊤) (hinf : E ⊓ center P = zpowers z)
    (hcen : ∀ x ∈ E, (∀ y ∈ E, x * y = y * x) → x ∈ center P)
    (hsq : ∀ x ∈ E, x ^ 2 ∈ zpowers z) (hnab : ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x) :
    IsCentralFactor E z w := by
  have hzc : zpowers z ≤ center P := hinf ▸ inf_le_right
  have hcen' : ∀ x ∈ E, (∀ y ∈ E, x * y = y * x) ↔ x ∈ zpowers z := by
    intro x hx
    refine ⟨fun h => hinf ▸ mem_inf.mpr ⟨hx, hcen x hx h⟩, fun h y _ => ?_⟩
    exact (mem_center_iff.mp (hzc h) y).symm
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ zpowers z := by
    intro x _ y _
    rcases H.comm_pair x y with h | h <;> rw [h]
    · exact one_mem _
    · exact mem_zpowers z
  obtain ⟨hext, hmap⟩ := isExtraspecialPGroup_two_of_forall (hP.to_subgroup E) hzE H.orderOf_eq
    hcen' hcomm hsq hnab
  refine ⟨hext, ?_, hsup, hinf, hmap, fun e he => ?_⟩
  · have h1 := relIndex_mul_card (center P) E
    rw [← relIndex_sup_right, hsup, relIndex_top_right, index_eq_card, hV, inf_comm, hinf,
      Nat.card_zpowers, H.orderOf_eq] at h1
    rw [← h1, pow_add, pow_one, mul_comm]
  · rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two H.orderOf_eq (hsq e he) with h | h
    · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, one_pow]
    · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, ← H.orderOf_eq, pow_orderOf_eq_one]

theorem isCentralFactor_top [Finite P] (hP : IsPGroup 2 P) {z : P} (H : CommPairHyp P z)
    {w : ℕ} (hV : Nat.card (P ⧸ center P) = 2 ^ (2 * w)) (h2 : Nat.card (center P) = 2)
    (hnab : ∃ x y : P, x * y ≠ y * x) : IsCentralFactor ⊤ z w := by
  have hZ : zpowers z = center P :=
    eq_of_le_of_card_ge (zpowers_le.mpr H.mem_center) (by rw [Nat.card_zpowers, H.orderOf_eq, h2])
  obtain ⟨x, y, hxy⟩ := hnab
  refine isCentralFactor_of hP H hV (mem_top z) (top_sup_eq _) (by rw [top_inf_eq, hZ])
    (fun x _ h => mem_center_iff.mpr fun g => (h g (mem_top g)).symm)
    (fun x _ => hZ ▸ H.sq_mem_center x) ⟨x, mem_top x, y, mem_top y, hxy⟩

namespace CommPairHyp

variable {z : P} (H : CommPairHyp P z)
include H

theorem exists_symplectic_basis [Finite P] [CFSG.IsElementaryAbelian 2 (P ⧸ center P)] :
    ∃ (m : ℕ) (bs : Module.Basis (Fin m ⊕ Fin m) (ZMod 2) (Additive (P ⧸ center P))),
      Nat.card (P ⧸ center P) = 2 ^ (2 * m) ∧
        ∀ i j, H.commForm (bs i) (bs j) = Matrix.J (Fin m) (ZMod 2) i j := by
  have : Module.Finite (ZMod 2) (Additive (P ⧸ center P)) := Module.Finite.of_finite
  obtain ⟨m, bs, hbs⟩ := LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J (K := ZMod 2)
    H.commForm_isAlt H.commForm_nondegenerate
  refine ⟨m, bs, ?_, fun i j => by rw [← hbs, LinearMap.BilinForm.toMatrix_apply]⟩
  change Nat.card (Additive (P ⧸ center P)) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    Module.finrank_eq_card_basis bs, Fintype.card_sum, Fintype.card_fin, two_mul]

end CommPairHyp

end TypeLevel


section Squares

variable {P : Type*} [Group P]

@[expose] def centerSq (P : Type*) [Group P] : Subgroup P where
  carrier := {y | ∃ t ∈ center P, y = t ^ 2}
  one_mem' := ⟨1, one_mem _, (one_pow 2).symm⟩
  mul_mem' := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact ⟨s * t, mul_mem hs ht, (Commute.mul_pow (mem_center_iff.mp ht s) 2).symm⟩
  inv_mem' := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨s⁻¹, inv_mem hs, (inv_pow s 2).symm⟩

theorem mem_centerSq_iff {y : P} : y ∈ centerSq P ↔ ∃ t ∈ center P, y = t ^ 2 :=
  Iff.rfl

theorem mul_mem_centerSq_of_notMem (hcyc : IsCyclic (center P)) {s t : P} (hs : s ∈ center P)
    (ht : t ∈ center P) (hs' : s ∉ centerSq P) (ht' : t ∉ centerSq P) :
    s * t ∈ centerSq P := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hodd : ∀ {u : P}, u ∈ center P → u ∉ centerSq P → ∃ j : ℤ, u = (g : P) ^ (2 * j + 1) := by
    intro u hu hu'
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hg ⟨u, hu⟩)
    have hi' : (g : P) ^ i = u := by rw [← coe_zpow, hi]
    obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' i
    · exfalso
      apply hu'
      refine ⟨(g : P) ^ j, zpow_mem g.2 j, ?_⟩
      rw [← hi', mul_comm, zpow_mul, zpow_two, pow_two]
    · exact ⟨j, hi'.symm⟩
  obtain ⟨j, rfl⟩ := hodd hs hs'
  obtain ⟨k, rfl⟩ := hodd ht ht'
  refine ⟨(g : P) ^ (j + k + 1), zpow_mem g.2 _, ?_⟩
  rw [← zpow_add, show 2 * j + 1 + (2 * k + 1) = (j + k + 1) * 2 by ring, zpow_mul, zpow_two,
    pow_two]

theorem mem_centerSq_of_four_le [Finite P] (hP : IsPGroup 2 P) (hcyc : IsCyclic (center P))
    {z : P} (hzc : z ∈ center P) (hz : orderOf z = 2) (h4 : 4 ≤ Nat.card (center P)) :
    z ∈ centerSq P := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf g = Nat.card (center P) := orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hP.to_subgroup (center P))
  have hk2 : 2 ≤ k := by
    by_contra h
    have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdvd : 2 ^ (k - 2) ∣ orderOf g := by
    rw [hord, hk]; exact Nat.pow_dvd_pow 2 (Nat.sub_le k 2)
  have hc4 : orderOf (g ^ 2 ^ (k - 2)) = 4 := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hord, hk,
      Nat.pow_div (Nat.sub_le k 2) two_pos, show k - (k - 2) = 2 by omega]
    norm_num
  have hc2 : orderOf ((g ^ 2 ^ (k - 2)) ^ 2) = 2 := by
    rw [orderOf_pow_of_dvd two_ne_zero (by rw [hc4]; norm_num), hc4]
  set c : center P := g ^ 2 ^ (k - 2) with hc
  have h1 : (c ^ 2) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (c ^ 2)
    rwa [hc2] at this
  have hsq1 : ((c : P) ^ 2) ^ 2 = 1 := by
    simpa only [Subgroup.coe_pow, OneMemClass.coe_one] using congrArg Subtype.val h1
  have hmem := mem_zpowers_of_sq_eq_one hcyc hzc hz (pow_mem c.2 2) hsq1
  rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hz hmem with h | h
  · exfalso
    have h' : c ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, h, OneMemClass.coe_one])
    rw [h', orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  · exact ⟨c, c.2, h.symm⟩

end Squares


section SquareFunctional

variable {P : Type*} [Group P]

namespace CommPairHyp

variable {z : P} (H : CommPairHyp P z)
include H

theorem sq_mem_centerSq [Finite P] [CFSG.IsElementaryAbelian 2 (P ⧸ center P)]
    (hP : IsPGroup 2 P)
    (hsymp : ∀ A : Subgroup P, A.Characteristic → IsMulCommutative A → IsCyclic A)
    (hcyc : IsCyclic (center P)) (h4 : 4 ≤ Nat.card (center P)) (x : P) :
    x ^ 2 ∈ centerSq P := by
  classical
  have hzS2 : z ∈ centerSq P := mem_centerSq_of_four_le hP hcyc H.mem_center H.orderOf_eq h4
  have hpairS2 : ∀ a b : P, ⁅a, b⁆ ∈ centerSq P := fun a b => by
    rcases H.comm_pair a b with h | h <;> rw [h]
    · exact one_mem _
    · exact hzS2
  obtain ⟨S, hS⟩ : ∃ S : Subgroup P, ∀ y, y ∈ S ↔ y ^ 2 ∈ centerSq P :=
    ⟨{ carrier := {y | y ^ 2 ∈ centerSq P}
       one_mem' := by
         show (1 : P) ^ 2 ∈ centerSq P
         rw [one_pow]; exact one_mem _
       mul_mem' := fun {a b} ha hb => by
         show (a * b) ^ 2 ∈ centerSq P
         rw [H.sq_mul]
         exact mul_mem (mul_mem (hpairS2 b a) ha) hb
       inv_mem' := fun {a} ha => by
         show a⁻¹ ^ 2 ∈ centerSq P
         rw [inv_pow]; exact inv_mem ha }, fun _ => Iff.rfl⟩
  have hcenS : ∀ t ∈ center P, t ∈ S := fun t ht => (hS t).mpr ⟨t, ht, rfl⟩
  have hpar : ∀ a b : P, a ∉ S → b ∉ S → a * b ∈ S := by
    intro a b ha hb
    rw [hS] at ha hb ⊢
    rw [H.sq_mul, mul_assoc]
    exact mul_mem (hpairS2 b a) (mul_mem_centerSq_of_notMem hcyc (H.sq_mem_center a)
      (H.sq_mem_center b) ha hb)
  by_contra hx0
  have hx0S : x ∉ S := fun h => hx0 ((hS x).mp h)
  let φf : Additive (P ⧸ center P) → ZMod 2 := fun u =>
    if Quotient.out (Additive.toMul u) ∈ S then 0 else 1
  have hφmk : ∀ y : P, φf (Additive.ofMul (y : P ⧸ center P)) = if y ∈ S then 0 else 1 := by
    intro y
    obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul (center P) y
    simp only [φf, toMul_ofMul, hs, S.mul_mem_cancel_right (hcenS s s.2)]
  have hadd : ∀ a b : P, (if a * b ∈ S then (0 : ZMod 2) else 1) =
      (if a ∈ S then 0 else 1) + (if b ∈ S then 0 else 1) := by
    intro a b
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
    · simp [ha, hb, mul_mem ha hb]
    · have : a * b ∉ S := fun h => hb ((S.mul_mem_cancel_left ha).mp h)
      simp [ha, hb, this]
    · have : a * b ∉ S := fun h => ha ((S.mul_mem_cancel_right hb).mp h)
      simp [ha, hb, this]
    · simp only [ha, hb, hpar a b ha hb, ite_true, ite_false]
      decide
  have hsurj : ∀ u : Additive (P ⧸ center P), ∃ y : P, u = Additive.ofMul (y : P ⧸ center P) := by
    intro u
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (Additive.toMul u)
    exact ⟨y, by rw [hy]; rfl⟩
  have hφadd : ∀ u v, φf (u + v) = φf u + φf v := by
    intro u v
    obtain ⟨a, rfl⟩ := hsurj u
    obtain ⟨b, rfl⟩ := hsurj v
    rw [show Additive.ofMul (a : P ⧸ center P) + Additive.ofMul (b : P ⧸ center P) =
      Additive.ofMul ((a * b : P) : P ⧸ center P) from rfl, hφmk, hφmk, hφmk]
    exact hadd a b
  have : Module.Finite (ZMod 2) (Additive (P ⧸ center P)) := Module.Finite.of_finite
  let φl : Module.Dual (ZMod 2) (Additive (P ⧸ center P)) :=
    AddMonoidHom.toZModLinearMap 2 (AddMonoidHom.mk' φf hφadd)
  set u := (H.commForm.toDual H.commForm_nondegenerate).symm φl with hu
  have huv : ∀ v, H.commForm u v = φf v := by
    intro v
    rw [← LinearMap.BilinForm.toDual_def H.commForm_nondegenerate, hu,
      LinearEquiv.apply_symm_apply]
    rfl
  obtain ⟨x₁, hx₁⟩ := hsurj u
  have hx₁S : x₁ ∈ S := by
    have h1 := huv u
    rw [H.commForm_isAlt.self_eq_zero, hx₁, hφmk] at h1
    by_contra h
    rw [ite_eq_right h] at h1
    exact zero_ne_one h1
  have hx₁C : ∀ y ∈ S, y * x₁ = x₁ * y := by
    intro y hy
    have h1 := huv (Additive.ofMul (y : P ⧸ center P))
    rw [hφmk, ite_eq_left hy, hx₁, commForm_apply, toMul_ofMul, toMul_ofMul,
      H.commVal_eq_zero_iff] at h1
    exact h1.symm
  have hx₁Z : x₁ ∉ center P := by
    intro h
    have h1 := huv (Additive.ofMul (x : P ⧸ center P))
    have hu0 : u = 0 := by
      rw [hx₁]
      exact (QuotientGroup.eq_one_iff x₁).mpr h
    rw [hu0, LinearMap.map_zero₂, hφmk, ite_eq_right hx0S] at h1
    exact zero_ne_one h1
  set C : Subgroup P := S ⊓ centralizer (S : Set P) with hC
  have hσS : ∀ σ : P ≃* P, ∀ y ∈ S, σ y ∈ S := by
    intro σ y hy
    rw [hS] at hy ⊢
    obtain ⟨t, ht, hyt⟩ := hy
    have hσt : σ t ∈ center P := by
      rw [mem_center_iff]
      intro g
      have h1 := mem_center_iff.mp ht (σ.symm g)
      calc g * σ t = σ (σ.symm g * t) := by rw [map_mul, MulEquiv.apply_symm_apply]
        _ = σ (t * σ.symm g) := by rw [h1]
        _ = σ t * g := by rw [map_mul, MulEquiv.apply_symm_apply]
    exact ⟨σ t, hσt, by rw [← map_pow, hyt, map_pow]⟩
  have hCchar : C.Characteristic := by
    rw [characteristic_iff_map_le]
    rintro σ _ ⟨c, hc, rfl⟩
    obtain ⟨hcS, hcC⟩ := mem_inf.mp hc
    refine mem_inf.mpr ⟨hσS σ c hcS, ?_⟩
    rw [mem_centralizer_iff]
    intro y hy
    have h1 := mem_centralizer_iff.mp hcC _ (hσS σ.symm y hy)
    change y * σ c = σ c * y
    calc y * σ c = σ (σ.symm y * c) := by rw [map_mul, MulEquiv.apply_symm_apply]
      _ = σ (c * σ.symm y) := by rw [h1]
      _ = σ c * y := by rw [map_mul, MulEquiv.apply_symm_apply]
  have hCcomm : IsMulCommutative C := ⟨⟨fun a b => Subtype.ext
    (mem_centralizer_iff.mp (mem_inf.mp b.2).2 a (mem_inf.mp a.2).1)⟩⟩
  have hCcyc := hsymp C hCchar hCcomm
  have hcenC : ∀ t ∈ center P, t ∈ C := fun t ht =>
    mem_inf.mpr ⟨hcenS t ht, mem_centralizer_iff.mpr fun g _ => mem_center_iff.mp ht g⟩
  obtain ⟨t, ht, hxt⟩ := (hS x₁).mp hx₁S
  have hvC : x₁ * t⁻¹ ∈ C :=
    mul_mem (mem_inf.mpr ⟨hx₁S, mem_centralizer_iff.mpr hx₁C⟩) (hcenC _ (inv_mem ht))
  have hv2 : (x₁ * t⁻¹) ^ 2 = 1 := by
    rw [(Commute.mul_pow (mem_center_iff.mp (inv_mem ht) x₁) 2), hxt, inv_pow, mul_inv_cancel]
  have hvz := mem_of_pow_eq_one_of_isCyclic hCcyc (zpowers_le.mpr (hcenC z H.mem_center))
    two_pos (by rw [Nat.card_zpowers, H.orderOf_eq]) hvC hv2
  have hvZ : x₁ * t⁻¹ ∈ center P := (zpowers_le.mpr H.mem_center) hvz
  exact hx₁Z (by simpa using mul_mem hvZ ht)

end CommPairHyp

end SquareFunctional


section QuadZero

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {m : ℕ}

@[expose] noncomputable def quadZero (B : LinearMap.BilinForm (ZMod 2) M)
    (bs : Module.Basis (Fin m ⊕ Fin m) (ZMod 2) M) (v : M) : ZMod 2 :=
  ∑ i, B v (bs (Sum.inr i)) * B v (bs (Sum.inl i))

variable {B : LinearMap.BilinForm (ZMod 2) M} {bs : Module.Basis (Fin m ⊕ Fin m) (ZMod 2) M}

theorem apply_eq_sum_of_J (hJ : ∀ i j, B (bs i) (bs j) = Matrix.J (Fin m) (ZMod 2) i j)
    (u v : M) : B u v =
      ∑ i, (B u (bs (Sum.inr i)) * B v (bs (Sum.inl i)) +
        B u (bs (Sum.inl i)) * B v (bs (Sum.inr i))) := by
  set B' : LinearMap.BilinForm (ZMod 2) M := ∑ i,
    ((B.flip (bs (Sum.inr i))).smulRight (B.flip (bs (Sum.inl i))) +
      (B.flip (bs (Sum.inl i))).smulRight (B.flip (bs (Sum.inr i)))) with hB'
  have happ : ∀ u v, B' u v = ∑ i, (B u (bs (Sum.inr i)) * B v (bs (Sum.inl i)) +
      B u (bs (Sum.inl i)) * B v (bs (Sum.inr i))) := by
    intro u v
    simp only [hB', LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
      LinearMap.smul_apply, LinearMap.BilinForm.flip_apply, smul_eq_mul]
  have hBB' : B = B' := by
    refine LinearMap.BilinForm.ext_basis bs fun k l => ?_
    rw [happ]
    simp only [hJ]
    rcases k with k | k <;> rcases l with l | l
    · simp [J_inl_inl, J_inl_inr]
    · rw [J_inl_inr]
      simp only [J_inl_inr, J_inr_inl, J_inl_inl, J_inr_inr, mul_zero, add_zero, ite_mul,
        one_mul, zero_mul]
      by_cases h : k = l
      · subst h; simp
      · simp [h, Ne.symm h]
    · rw [J_inr_inl]
      simp only [J_inl_inr, J_inr_inl, J_inl_inl, J_inr_inr, zero_mul, zero_add, ite_mul,
        one_mul, zero_mul]
      by_cases h : k = l
      · subst h; simp
      · simp [h, Ne.symm h]
    · simp [J_inr_inr, J_inr_inl]
  rw [show B u v = B' u v from congrArg (fun F : LinearMap.BilinForm (ZMod 2) M => F u v) hBB']
  exact happ u v

theorem quadZero_add (hJ : ∀ i j, B (bs i) (bs j) = Matrix.J (Fin m) (ZMod 2) i j) (u v : M) :
    quadZero B bs (u + v) = quadZero B bs u + quadZero B bs v + B u v := by
  rw [apply_eq_sum_of_J hJ u v]
  simp only [quadZero, map_add, LinearMap.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem quadZero_basis (hJ : ∀ i j, B (bs i) (bs j) = Matrix.J (Fin m) (ZMod 2) i j)
    (k : Fin m ⊕ Fin m) : quadZero B bs (bs k) = 0 := by
  rcases k with k | k
  · simp [quadZero, hJ, J_inl_inl]
  · simp [quadZero, hJ, J_inr_inr]

theorem quadZero_zero : quadZero B bs 0 = 0 := by
  simp [quadZero]

theorem quadZero_neg (v : M) : quadZero B bs (-v) = quadZero B bs v := by
  simp [quadZero]

end QuadZero


section Generators

variable {P : Type*} [Group P]

namespace CommPairHyp

variable {z : P} (H : CommPairHyp P z)
include H

theorem exists_central_factor_generators [Finite P] [CFSG.IsElementaryAbelian 2 (P ⧸ center P)]
    (hP : IsPGroup 2 P)
    (hsymp : ∀ A : Subgroup P, A.Characteristic → IsMulCommutative A → IsCyclic A)
    (hcyc : IsCyclic (center P)) (h4 : 4 ≤ Nat.card (center P)) {m : ℕ} (hm : 1 ≤ m)
    (bs : Module.Basis (Fin m ⊕ Fin m) (ZMod 2) (Additive (P ⧸ center P)))
    (hV : Nat.card (P ⧸ center P) = 2 ^ (2 * m))
    (hJ : ∀ i j, H.commForm (bs i) (bs j) = Matrix.J (Fin m) (ZMod 2) i j) :
    ∃ a c : Fin m → P, (∀ i, a i ^ 2 = 1) ∧ (∀ i, c i ^ 2 = 1) ∧ (∀ i, ⁅a i, c i⁆ = z) ∧
      (∀ i j, i ≠ j → ⁅a i, a j⁆ = 1 ∧ ⁅a i, c j⁆ = 1 ∧ ⁅c i, c j⁆ = 1) ∧
      IsCentralFactor (closure (Set.range a ∪ Set.range c)) z m := by
  classical
  have hlift : ∀ k, ∃ y : P, Additive.ofMul (y : P ⧸ center P) = bs k ∧ y ^ 2 = 1 := by
    intro k
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul (bs k))
    obtain ⟨t, ht, hxt⟩ := H.sq_mem_centerSq hP hsymp hcyc h4 x
    refine ⟨x * t⁻¹, ?_, ?_⟩
    · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff t⁻¹).mpr (inv_mem ht), mul_one, hx]
      rfl
    · rw [Commute.mul_pow (mem_center_iff.mp (inv_mem ht) x) 2, hxt, inv_pow, mul_inv_cancel]
  choose ℓ hℓ hℓ2 using hlift
  set a : Fin m → P := fun i => ℓ (Sum.inl i) with ha
  set c : Fin m → P := fun i => ℓ (Sum.inr i) with hc
  have hcomm : ∀ k l, ⁅ℓ k, ℓ l⁆ = z ^ (Matrix.J (Fin m) (ZMod 2) k l).val := by
    intro k l
    rw [H.commutatorElement_eq_zpow, ← hJ, ← hℓ k, ← hℓ l]
    rfl
  set E : Subgroup P := closure (Set.range a ∪ Set.range c) with hE
  have hℓE : ∀ k, ℓ k ∈ E := by
    rintro (i | i)
    · exact subset_closure (Or.inl ⟨i, rfl⟩)
    · exact subset_closure (Or.inr ⟨i, rfl⟩)
  have hgen : ∀ g ∈ Set.range a ∪ Set.range c, ∃ k, ℓ k = g := by
    rintro g (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨Sum.inl i, rfl⟩
    · exact ⟨Sum.inr i, rfl⟩
  have hmemc : ∀ {x y : P}, x ∈ E → y ∈ E → ⁅x, y⁆ ∈ E := fun hx hy => by
    rw [commutatorElement_def]
    exact E.mul_mem (E.mul_mem (E.mul_mem hx hy) (E.inv_mem hx)) (E.inv_mem hy)
  set i₀ : Fin m := ⟨0, hm⟩
  have hac : ⁅a i₀, c i₀⁆ = z := by
    rw [ha, hc, hcomm, J_inl_inr, ite_eq_left rfl]
    exact pow_one z
  have hzE : z ∈ E := hac ▸ hmemc (hℓE _) (hℓE _)
  set q := quadZero H.commForm bs with hq
  have hpair2 : ∀ {x : P}, x ^ 2 ∈ zpowers z → x ^ 2 = 1 ∨ x ^ 2 = z := fun h =>
    eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two H.orderOf_eq h
  have hpairmem : ∀ {y : P}, y = 1 ∨ y = z → y ∈ zpowers z := by
    intro y hy
    rcases hy with h | h <;> rw [h]
    · exact one_mem _
    · exact mem_zpowers z
  have hkey : ∀ x ∈ E, x ^ 2 ∈ zpowers z ∧
      zlog z (x ^ 2) = q (Additive.ofMul (x : P ⧸ center P)) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hgen x hx
      rw [hℓ2 k, hℓ k, hq, quadZero_basis hJ, H.zlog_one]
      exact ⟨one_mem _, rfl⟩
    | one =>
      rw [one_pow, QuotientGroup.mk_one, ofMul_one, hq, quadZero_zero, H.zlog_one]
      exact ⟨one_mem _, rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨hx2, hxq⟩ := hx
      obtain ⟨hy2, hyq⟩ := hy
      have hc2 := H.comm_pair y x
      have hp1 := H.pair_mul hc2 (hpair2 hx2)
      refine ⟨by rw [H.sq_mul]; exact hpairmem (H.pair_mul hp1 (hpair2 hy2)), ?_⟩
      rw [H.sq_mul, H.zlog_mul hp1 (hpair2 hy2), H.zlog_mul hc2 (hpair2 hx2), hxq, hyq,
        QuotientGroup.mk_mul, ofMul_mul, hq, quadZero_add hJ, ← hq, ← H.commVal_mk,
        H.commVal_comm, commForm_apply, toMul_ofMul, toMul_ofMul]
      ring
    | inv x _ hx =>
      obtain ⟨hx2, hxq⟩ := hx
      have hinv2 : x⁻¹ ^ 2 = x ^ 2 := by rw [inv_pow, H.pair_inv (hpair2 hx2)]
      rw [hinv2, QuotientGroup.mk_inv, ofMul_inv, hq, quadZero_neg, ← hq]
      exact ⟨hx2, hxq⟩
  have huniq : ∀ y ∈ center P, y ^ 2 = 1 → y ∈ zpowers z := fun y hyc hy =>
    mem_zpowers_of_sq_eq_one hcyc H.mem_center H.orderOf_eq hyc hy
  have hinf : E ⊓ center P = zpowers z := by
    apply le_antisymm
    · intro t ht
      obtain ⟨htE, htc⟩ := mem_inf.mp ht
      obtain ⟨h2, hqt⟩ := hkey t htE
      rw [(QuotientGroup.eq_one_iff t).mpr htc, ofMul_one, hq, quadZero_zero] at hqt
      exact huniq t htc ((H.zlog_eq_zero_iff (hpair2 h2)).mp hqt)
    · exact le_inf (zpowers_le.mpr hzE) (zpowers_le.mpr H.mem_center)
  have hsup : E ⊔ center P = ⊤ := by
    have hmap : E.map (QuotientGroup.mk' (center P)) = ⊤ := by
      rw [eq_top_iff]
      intro v _
      have hv : Additive.ofMul v ∈ Submodule.span (ZMod 2) (Set.range bs) := by
        rw [bs.span_eq]; exact Submodule.mem_top
      have key : ∀ w ∈ Submodule.span (ZMod 2) (Set.range bs),
          Additive.toMul w ∈ E.map (QuotientGroup.mk' (center P)) := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨k, rfl⟩ := hw
          rw [← hℓ k]
          exact mem_map_of_mem _ (hℓE k)
        | zero => exact one_mem _
        | add w w' _ _ hw hw' => exact mul_mem hw hw'
        | smul r w _ hw =>
          rw [← ZMod.natCast_zmod_val r, Nat.cast_smul_eq_nsmul (ZMod 2), toMul_nsmul]
          exact pow_mem hw _
      exact key _ hv
    have h1 := comap_map_eq (QuotientGroup.mk' (center P)) E
    rw [hmap, comap_top, QuotientGroup.ker_mk'] at h1
    exact h1.symm
  have hcen : ∀ x ∈ E, (∀ y ∈ E, x * y = y * x) → x ∈ center P := by
    intro x _ h
    have hB0 : H.commForm (Additive.ofMul (x : P ⧸ center P)) = 0 := by
      refine bs.ext fun k => ?_
      rw [LinearMap.zero_apply, ← hℓ k, commForm_apply, toMul_ofMul, toMul_ofMul,
        H.commVal_eq_zero_iff]
      exact h _ (hℓE k)
    have h0 : Additive.ofMul (x : P ⧸ center P) = 0 :=
      H.commForm_nondegenerate.1 _ fun n => by rw [hB0]; rfl
    exact (QuotientGroup.eq_one_iff x).mp h0
  have hnab : ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x := by
    refine ⟨a i₀, hℓE _, c i₀, hℓE _, fun h => H.z_ne_one ?_⟩
    rw [← hac, commutatorElement_eq_one_iff_mul_comm]
    exact h
  refine ⟨a, c, fun i => hℓ2 _, fun i => hℓ2 _, fun i => ?_, fun i j hij => ?_,
    isCentralFactor_of hP H hV hzE hsup hinf hcen (fun x hx => (hkey x hx).1) hnab⟩
  · rw [ha, hc, hcomm, J_inl_inr, ite_eq_left rfl]
    exact pow_one z
  · refine ⟨?_, ?_, ?_⟩
    · rw [ha, hcomm, J_inl_inl, ZMod.val_zero, pow_zero]
    · rw [ha, hc, hcomm, J_inl_inr, ite_eq_right hij, ZMod.val_zero, pow_zero]
    · rw [hc, hcomm, J_inr_inr, ZMod.val_zero, pow_zero]

end CommPairHyp

end Generators


section Main

variable {P : Type*} [Group P]

theorem symplectic_central_frattini_aux [Finite P] [Nontrivial P] (hP : IsPGroup 2 P)
    (hsymp : ∀ A : Subgroup P, A.Characteristic → IsMulCommutative A → IsCyclic A)
    (hΦ : frattini P ≤ center P) :
    IsCyclic (center P) ∧ ∃ z : P, z ∈ center P ∧ orderOf z = 2 ∧
      (∀ x ∈ center P, orderOf x = 2 → x = z) ∧
      ((∀ x y : P, x * y = y * x) → center P = ⊤) ∧
      ((∃ x y : P, x * y ≠ y * x) →
        ∃ w : ℕ, 1 ≤ w ∧ CFSG.IsElementaryAbelian 2 (P ⧸ center P) ∧
          Nat.card (P ⧸ center P) = 2 ^ (2 * w) ∧
          (∀ u v t : P ⧸ center P, commVal z (u * v) t = commVal z u t + commVal z v t) ∧
          (∀ u v t : P ⧸ center P, commVal z u (v * t) = commVal z u v + commVal z u t) ∧
          (∀ u : P ⧸ center P, commVal z u u = 0) ∧
          (∀ u : P ⧸ center P, (∀ v, commVal z u v = 0) → u = 1) ∧
          (∀ x y : P,
            x⁻¹ * y⁻¹ * x * y = z ^ (commVal z (x : P ⧸ center P) (y : P ⧸ center P)).val) ∧
          (∃ E : Subgroup P, IsCentralFactor E z w) ∧
          (Nat.card (center P) = 2 → IsCentralFactor ⊤ z w) ∧
          (4 ≤ Nat.card (center P) → ∃ a c : Fin w → P, (∀ i, a i ^ 2 = 1) ∧
            (∀ i, c i ^ 2 = 1) ∧ (∀ i, ⁅a i, c i⁆ = z) ∧
            (∀ i j, i ≠ j → ⁅a i, a j⁆ = 1 ∧ ⁅a i, c j⁆ = 1 ∧ ⁅c i, c j⁆ = 1) ∧
            IsCentralFactor (closure (Set.range a ∪ Set.range c)) z w)) := by
  have hcyc : IsCyclic (center P) := hsymp (center P) inferInstance inferInstance
  obtain ⟨z, H, huniq⟩ := exists_commPairHyp hP hcyc hΦ
  refine ⟨hcyc, z, H.mem_center, H.orderOf_eq, fun x hx hx2 => ?_,
    fun hab => eq_top_iff.mpr fun x _ => mem_center_iff.mpr fun g => hab g x, fun hnab => ?_⟩
  · have hx' := huniq x hx (by rw [← hx2]; exact pow_orderOf_eq_one x)
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two H.orderOf_eq hx' with h | h
    · rw [h, orderOf_one] at hx2
      exact absurd hx2 (by norm_num)
    · exact h
  have hV := H.isElementaryAbelian_quotient
  obtain ⟨m, bs, hcard, hJ⟩ := H.exists_symplectic_basis
  have hm : 1 ≤ m := by
    by_contra h0
    rw [show m = 0 by omega, mul_zero, pow_zero] at hcard
    have htop : center P = ⊤ := index_eq_one.mp (by rw [index_eq_card, hcard])
    obtain ⟨x, y, hxy⟩ := hnab
    exact hxy (mem_center_iff.mp (htop ▸ mem_top y) x)
  have hZ : Nat.card (center P) = 2 ∨ 4 ≤ Nat.card (center P) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hP.to_subgroup (center P))
    have h1 : 1 < Nat.card (center P) :=
      Finite.one_lt_card_iff_nontrivial.mpr hP.center_nontrivial
    rw [hk] at h1 ⊢
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · norm_num at h1
      · left; rfl
    · right
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  have htop := fun h2 => isCentralFactor_top hP H hcard h2 hnab
  have hgen := fun h4 => H.exists_central_factor_generators hP hsymp hcyc h4 hm bs hcard hJ
  refine ⟨m, hm, hV, hcard, H.commVal_mul_left, H.commVal_mul_right, H.commVal_self,
    fun u hu => H.eq_one_of_forall_commVal_eq_zero hu,
    fun x y => by rw [H.inv_comm_eq]; exact H.commutatorElement_eq_zpow x y, ?_, htop, hgen⟩
  rcases hZ with h | h
  · exact ⟨⊤, htop h⟩
  · obtain ⟨a, c, -, -, -, -, hE⟩ := hgen h
    exact ⟨_, hE⟩

end Main

section Ambient

variable {G : Type*} [Group G]

theorem isExtraspecialPGroup_congr_mulEquiv {p : ℕ} {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : IsExtraspecialPGroup p A) : IsExtraspecialPGroup p B := by
  obtain ⟨hp, hcomm, hfrat, hcard⟩ := h
  have hc : (commutator A).map e.toMonoidHom = commutator B := by
    rw [_root_.commutator_def, _root_.commutator_def, map_commutator,
      map_top_of_surjective _ e.surjective]
  have hf : (frattini A).map e.toMonoidHom = frattini B :=
    OrderIso.map_radical (MulEquiv.mapSubgroup e)
  have hz : (center A).map e.toMonoidHom = center B := map_center_eq e
  refine ⟨hp.of_equiv e, ?_, ?_, ?_⟩
  · rw [← hc, hcomm, hz]
  · rw [← hf, hfrat, hz]
  · rw [← hz, card_map_of_injective e.injective, hcard]

@[expose] def IsExtraspecialCentralFactor (D E : Subgroup G) (z : G) (w : ℕ) : Prop :=
  E ≤ D ∧ IsExtraspecialPGroup 2 E ∧ Nat.card E = 2 ^ (1 + 2 * w) ∧
    E ⊔ (center D).map D.subtype = D ∧ ⁅E, (center D).map D.subtype⁆ = ⊥ ∧
    E ⊓ (center D).map D.subtype = zpowers z ∧ (center E).map E.subtype = zpowers z ∧
    ∀ e ∈ E, e ^ 4 = 1

theorem IsCentralFactor.map_subtype {D : Subgroup G} {E : Subgroup D} {z : D} {w : ℕ}
    (h : IsCentralFactor E z w) :
    IsExtraspecialCentralFactor D (E.map D.subtype) (z : G) w := by
  set φ := E.equivMapOfInjective D.subtype D.subtype_injective with hφ
  have hE' : ⁅E, center D⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro e _
    rw [mem_centralizer_iff]
    intro t ht
    exact (mem_center_iff.mp ht e).symm
  refine ⟨map_subtype_le E, isExtraspecialPGroup_congr_mulEquiv φ h.extraspecial, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [card_map_of_injective D.subtype_injective, h.card]
  · rw [← Subgroup.map_sup, h.sup_center, ← MonoidHom.range_eq_map, range_subtype]
  · rw [← map_commutator, hE', Subgroup.map_bot]
  · rw [← map_inf_eq _ _ _ D.subtype_injective, h.inf_center, MonoidHom.map_zpowers]
    rfl
  · have hc : center (E.map D.subtype) = (center E).map φ.toMonoidHom := (map_center_eq φ).symm
    have hcomp : (E.map D.subtype).subtype.comp φ.toMonoidHom = D.subtype.comp E.subtype := by
      ext x
      rfl
    rw [hc, map_map, hcomp, ← map_map, h.center_eq, MonoidHom.map_zpowers]
    rfl
  · rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, h.pow_four e he, OneMemClass.coe_one]

theorem symplectic_central_frattini_central_product {D : Subgroup G} [Finite D] (hD : D ≠ ⊥)
    (hDs : CFSG.Open.GLASymplecticType D) (hΦ : frattini D ≤ center D) :
    IsCyclic ((center D).map D.subtype) ∧
      ∃ z ∈ (center D).map D.subtype, orderOf z = 2 ∧
        (∀ x ∈ (center D).map D.subtype, orderOf x = 2 → x = z) ∧
        ((∀ x ∈ D, ∀ y ∈ D, x * y = y * x) → D = (center D).map D.subtype) ∧
        ((∃ x ∈ D, ∃ y ∈ D, x * y ≠ y * x) →
          ∃ w : ℕ, 1 ≤ w ∧ CFSG.IsElementaryAbelian 2 (D ⧸ center D) ∧
            Nat.card (D ⧸ center D) = 2 ^ (2 * w) ∧
            (∀ w' : ℕ, Nat.card (D ⧸ center D) = 2 ^ (2 * w') → w' = w) ∧
            ∃ b : D ⧸ center D → D ⧸ center D → ZMod 2,
              (∀ u v t, b (u * v) t = b u t + b v t) ∧ (∀ u v t, b u (v * t) = b u v + b u t) ∧
              (∀ u, b u u = 0) ∧ (∀ u, (∀ v, b u v = 0) → u = 1) ∧
              (∀ x y : D, (x : G)⁻¹ * (y : G)⁻¹ * x * y =
                z ^ (b (x : D ⧸ center D) (y : D ⧸ center D)).val) ∧
              (∃ E : Subgroup G, IsExtraspecialCentralFactor D E z w) ∧
              (Nat.card ((center D).map D.subtype) = 2 → IsExtraspecialCentralFactor D D z w) ∧
              (4 ≤ Nat.card ((center D).map D.subtype) →
                ∃ a c : Fin w → G, (∀ i, a i ^ 2 = 1) ∧ (∀ i, c i ^ 2 = 1) ∧
                  (∀ i, (a i)⁻¹ * (c i)⁻¹ * a i * c i = z) ∧
                  (∀ i j, i ≠ j → ⁅a i, a j⁆ = 1 ∧ ⁅a i, c j⁆ = 1 ∧ ⁅c i, c j⁆ = 1) ∧
                  IsExtraspecialCentralFactor D (closure (Set.range a ∪ Set.range c)) z w)) := by
  have : Nontrivial D := (nontrivial_iff_ne_bot D).mpr hD
  obtain ⟨hcyc, z, hzc, hz, huniq, hab, hnab⟩ :=
    symplectic_central_frattini_aux hDs.1 hDs.2 hΦ
  have hZcard : Nat.card ((center D).map D.subtype) = Nat.card (center D) :=
    card_map_of_injective D.subtype_injective
  have hmapD : (⊤ : Subgroup D).map D.subtype = D := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  refine ⟨((center D).equivMapOfInjective D.subtype D.subtype_injective).isCyclic.mp hcyc,
    z, ⟨z, hzc, rfl⟩, by rw [Subgroup.orderOf_coe, hz], ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ hx2
    rw [Subgroup.coe_subtype, Subgroup.orderOf_coe] at hx2
    rw [Subgroup.coe_subtype, huniq x hx hx2]
  · intro h
    have htop := hab fun x y => Subtype.ext (h x x.2 y y.2)
    rw [htop, hmapD]
  · rintro ⟨x, hx, y, hy, hxy⟩
    obtain ⟨w, hw, hV, hcard, hb1, hb2, hb3, hb4, hb5, ⟨E, hE⟩, htop, hgen⟩ :=
      hnab ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩
    refine ⟨w, hw, hV, hcard, fun w' hw' => ?_, commVal z, hb1, hb2, hb3, hb4, fun x y => ?_,
      ⟨_, hE.map_subtype⟩, fun h2 => ?_, fun h4 => ?_⟩
    · rw [hcard] at hw'
      have := Nat.pow_right_injective (le_refl 2) hw'
      omega
    · rw [← Subgroup.coe_inv, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
        ← Subgroup.coe_mul, hb5 x y, Subgroup.coe_pow]
    · have := (htop (hZcard ▸ h2)).map_subtype
      rwa [hmapD] at this
    · obtain ⟨a, c, ha, hc, hac, hij, hEac⟩ := hgen (hZcard ▸ h4)
      have hcl : (closure (Set.range a ∪ Set.range c)).map D.subtype =
          closure (Set.range (fun i => (a i : G)) ∪ Set.range (fun i => (c i : G))) := by
        rw [MonoidHom.map_closure, Set.image_union, ← Set.range_comp, ← Set.range_comp]
        rfl
      refine ⟨fun i => a i, fun i => c i, fun i => ?_, fun i => ?_, fun i => ?_,
        fun i j hne => ?_, hcl ▸ hEac.map_subtype⟩
      · rw [← Subgroup.coe_pow, ha i, OneMemClass.coe_one]
      · rw [← Subgroup.coe_pow, hc i, OneMemClass.coe_one]
      · have hai : (a i)⁻¹ = a i := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact ha i)
        have hci : (c i)⁻¹ = c i := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hc i)
        have h1 : (a i)⁻¹ * (c i)⁻¹ * a i * c i = z := by
          rw [← hac i, commutatorElement_def, hai, hci]
        show ((a i : G))⁻¹ * ((c i : G))⁻¹ * (a i : G) * (c i : G) = (z : G)
        rw [← Subgroup.coe_inv, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
          ← Subgroup.coe_mul, h1]
      · obtain ⟨h1, h2, h3⟩ := hij i j hne
        have hcomm : ∀ {u v : D}, ⁅u, v⁆ = 1 → ⁅(u : G), (v : G)⁆ = 1 := fun {u v} h => by
          have := congrArg D.subtype h
          rwa [map_commutatorElement, map_one] at this
        exact ⟨hcomm h1, hcomm h2, hcomm h3⟩

end Ambient

end CFSG.LocalAnalysis.GorensteinLyons
