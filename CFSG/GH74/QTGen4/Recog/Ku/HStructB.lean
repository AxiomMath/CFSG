module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.GH74.QTGen4.Ku

open scoped commutatorElement
open scoped IsMulCommutative

open Classical in
@[expose] noncomputable def sgn {Q : Type*} [Group Q] (c : Q) : ZMod 2 := if c = 1 then 0 else 1

structure KuZCore (Q : Type*) [Group Q] (z : Q) : Prop where
  z_ne : z ≠ 1
  z_sq : z * z = 1
  center_eq : Subgroup.center Q = Subgroup.zpowers z
  comm_mem : ∀ a b : Q, ⁅a, b⁆ ∈ Subgroup.center Q
  sq_mem : ∀ a : Q, a ^ 2 ∈ Subgroup.center Q

namespace KuZCore

variable {Q : Type*} [Group Q] {z : Q}

theorem mem_zpowers_cases (h : z * z = 1) {c : Q} (hc : c ∈ Subgroup.zpowers z) :
    c = 1 ∨ c = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have hz2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact h
  have hk : z ^ k = z ^ (k % 2) := by
    have hk2 : k = k % 2 + 2 * (k / 2) := by omega
    conv_lhs => rw [hk2]
    rw [zpow_add, zpow_mul, hz2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [hk, h0, zpow_zero]
  · right
    rw [hk, h1, zpow_one]

theorem sgn_one : sgn (1 : Q) = 0 := by
  simp [sgn]

theorem sgn_z (C : KuZCore Q z) : sgn z = 1 := by
  simp [sgn, C.z_ne]

theorem sgn_mul (C : KuZCore Q z) {c d : Q} (hc : c = 1 ∨ c = z) (hd : d = 1 ∨ d = z) :
    sgn (c * d) = sgn c + sgn d := by
  rcases hc with hc | hc <;> rcases hd with hd | hd
  · rw [hc, hd, one_mul, sgn_one, add_zero]
  · rw [hc, hd, one_mul, sgn_one, sgn_z C, zero_add]
  · rw [hc, hd, mul_one, sgn_one, sgn_z C, add_zero]
  · rw [hc, hd, C.z_sq, sgn_one, sgn_z C]
    decide

theorem sgn_eq_zero (C : KuZCore Q z) {c : Q} (hc : c = 1 ∨ c = z) :
    sgn c = 0 ↔ c = 1 := by
  rcases hc with hc | hc
  · simp [hc, sgn_one]
  · rw [hc, sgn_z C]
    exact ⟨fun h => absurd h (by decide), fun h => absurd h C.z_ne⟩

theorem comm_pair (C : KuZCore Q z) (a b : Q) : ⁅a, b⁆ = 1 ∨ ⁅a, b⁆ = z :=
  mem_zpowers_cases C.z_sq (by rw [← C.center_eq]; exact C.comm_mem a b)

theorem comm_symm (C : KuZCore Q z) (a b : Q) : ⁅b, a⁆ = ⁅a, b⁆ := by
  rw [← commutatorElement_inv]
  rcases C.comm_pair a b with h | h
  · rw [h, inv_one]
  · rw [h, inv_eq_of_mul_eq_one_right C.z_sq]

@[expose] noncomputable def pairQ (a b : Q) : ZMod 2 := sgn ⁅a, b⁆

theorem pairQ_symm (C : KuZCore Q z) (a b : Q) : pairQ a b = pairQ b a := by
  unfold pairQ
  rw [C.comm_symm a b]

theorem pairQ_mul_left (C : KuZCore Q z) (a a' b : Q) :
    pairQ (a * a') b = pairQ a b + pairQ a' b := by
  have hc : ∀ g : Q, g * ⁅a', b⁆ = ⁅a', b⁆ * g := Subgroup.mem_center_iff.mp (C.comm_mem a' b)
  have h1 : a * ⁅a', b⁆ = ⁅a', b⁆ * a := hc a
  have e : ⁅a * a', b⁆ = ⁅a', b⁆ * ⁅a, b⁆ := by
    calc ⁅a * a', b⁆ = (a * ⁅a', b⁆) * (b * a⁻¹ * b⁻¹) := by
          simp only [commutatorElement_def]; group
      _ = (⁅a', b⁆ * a) * (b * a⁻¹ * b⁻¹) := by rw [h1]
      _ = ⁅a', b⁆ * ⁅a, b⁆ := by simp only [commutatorElement_def]; group
  unfold pairQ
  rw [e, C.sgn_mul (C.comm_pair a' b) (C.comm_pair a b), add_comm]

theorem pairQ_mul_right (C : KuZCore Q z) (a b b' : Q) :
    pairQ a (b * b') = pairQ a b + pairQ a b' := by
  rw [C.pairQ_symm a (b * b'), C.pairQ_mul_left b b' a, C.pairQ_symm b a, C.pairQ_symm b' a]

theorem pairQ_center_left (_C : KuZCore Q z) {c : Q} (hc : c ∈ Subgroup.center Q) (b : Q) :
    pairQ c b = 0 := by
  unfold pairQ
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hc b).symm, sgn_one]

theorem pairQ_center_right (C : KuZCore Q z) {c : Q} (hc : c ∈ Subgroup.center Q) (a : Q) :
    pairQ a c = 0 :=
  (C.pairQ_symm a c).trans (C.pairQ_center_left hc a)

theorem pairQ_mul_center_left (C : KuZCore Q z) (a b : Q) {c : Q} (hc : c ∈ Subgroup.center Q) :
    pairQ (a * c) b = pairQ a b := by
  rw [C.pairQ_mul_left, C.pairQ_center_left hc, add_zero]

theorem pairQ_mul_center_right (C : KuZCore Q z) (a b : Q) {c : Q} (hc : c ∈ Subgroup.center Q) :
    pairQ a (b * c) = pairQ a b := by
  rw [C.pairQ_mul_right, C.pairQ_center_right hc, add_zero]

@[expose] noncomputable def pairV (u v : Q ⧸ Subgroup.center Q) : ZMod 2 :=
  pairQ (Quotient.out u) (Quotient.out v)

theorem pairV_mk (C : KuZCore Q z) (x y : Q) :
    pairV (x : Q ⧸ Subgroup.center Q) (y : Q ⧸ Subgroup.center Q) = pairQ x y := by
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center Q) x
  obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center Q) y
  unfold pairV
  rw [hs, ht, C.pairQ_mul_center_left _ _ s.2, C.pairQ_mul_center_right _ _ t.2]

theorem pairV_comm (C : KuZCore Q z) (u v : Q ⧸ Subgroup.center Q) : pairV u v = pairV v u :=
  C.pairQ_symm _ _

theorem pairV_mul_left (C : KuZCore Q z) (u u' v : Q ⧸ Subgroup.center Q) :
    pairV (u * u') v = pairV u v + pairV u' v := by
  induction u using QuotientGroup.induction_on with | H x =>
  induction u' using QuotientGroup.induction_on with | H x' =>
  induction v using QuotientGroup.induction_on with | H y =>
  rw [← QuotientGroup.mk_mul, C.pairV_mk, C.pairV_mk, C.pairV_mk, C.pairQ_mul_left]

theorem pairV_mul_right (C : KuZCore Q z) (u v v' : Q ⧸ Subgroup.center Q) :
    pairV u (v * v') = pairV u v + pairV u v' := by
  induction u using QuotientGroup.induction_on with | H x =>
  induction v using QuotientGroup.induction_on with | H y =>
  induction v' using QuotientGroup.induction_on with | H y' =>
  rw [← QuotientGroup.mk_mul, C.pairV_mk, C.pairV_mk, C.pairV_mk, C.pairQ_mul_right]

theorem pairV_one_left (C : KuZCore Q z) (v : Q ⧸ Subgroup.center Q) : pairV 1 v = 0 := by
  have h := C.pairV_mul_left 1 1 v
  rw [mul_one] at h
  have h' : pairV 1 v + 0 = pairV 1 v + pairV 1 v := by rw [add_zero]; exact h
  exact (add_left_cancel h').symm

theorem eq_one_of_forall_pairV_eq_zero (C : KuZCore Q z) {u : Q ⧸ Subgroup.center Q}
    (h : ∀ v, pairV u v = 0) : u = 1 := by
  induction u using QuotientGroup.induction_on with | H x =>
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
  intro g
  have hg := h (g : Q ⧸ Subgroup.center Q)
  rw [C.pairV_mk] at hg
  have h1 : ⁅x, g⁆ = 1 := (sgn_eq_zero C (C.comm_pair x g)).mp hg
  exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

@[expose] noncomputable def commAdd (C : KuZCore Q z)
    [CFSG.IsElementaryAbelian 2 (Q ⧸ Subgroup.center Q)] :
    Additive (Q ⧸ Subgroup.center Q) →+ Additive (Q ⧸ Subgroup.center Q) →+ ZMod 2 :=
  AddMonoidHom.mk'
    (fun u => AddMonoidHom.mk' (fun v => pairV u.toMul v.toMul)
      (fun a b => C.pairV_mul_right u.toMul a.toMul b.toMul))
    (fun a b => AddMonoidHom.ext fun v => C.pairV_mul_left a.toMul b.toMul v.toMul)

@[expose] noncomputable def commForm (C : KuZCore Q z)
    [CFSG.IsElementaryAbelian 2 (Q ⧸ Subgroup.center Q)] :
    LinearMap.BilinForm (ZMod 2) (Additive (Q ⧸ Subgroup.center Q)) :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := fun u => AddMonoidHom.toZModLinearMap 2 (C.commAdd u)
      map_zero' := by ext v; exact C.pairV_one_left _
      map_add' := fun a b => by ext v; exact C.pairV_mul_left a.toMul b.toMul v.toMul }

theorem commForm_apply (C : KuZCore Q z) [CFSG.IsElementaryAbelian 2 (Q ⧸ Subgroup.center Q)]
    (u v : Additive (Q ⧸ Subgroup.center Q)) :
    C.commForm u v = pairV u.toMul v.toMul :=
  rfl

theorem commForm_nondegenerate (C : KuZCore Q z)
    [CFSG.IsElementaryAbelian 2 (Q ⧸ Subgroup.center Q)] : C.commForm.Nondegenerate := by
  refine ⟨fun u hu => ?_, fun v hv => ?_⟩
  · refine toMul_eq_one.mp (C.eq_one_of_forall_pairV_eq_zero fun w => ?_)
    have h := hu (Additive.ofMul w)
    rw [commForm_apply] at h
    exact h
  · refine toMul_eq_one.mp (C.eq_one_of_forall_pairV_eq_zero fun w => ?_)
    have h := hv (Additive.ofMul w)
    rw [commForm_apply] at h
    rw [C.pairV_comm]
    exact h

theorem exists_pair_eq (C : KuZCore Q z) [Finite Q]
    [CFSG.IsElementaryAbelian 2 (Q ⧸ Subgroup.center Q)]
    (χ : Q → ZMod 2) (hmul : ∀ a b, χ (a * b) = χ a + χ b)
    (hcen : ∀ c ∈ Subgroup.center Q, χ c = 0) :
    ∃ u : Q, ∀ v : Q, pairQ u v = χ v := by
  have : Module.Finite (ZMod 2) (Additive (Q ⧸ Subgroup.center Q)) := Module.Finite.of_finite
  have hout : ∀ x : Q, χ (Quotient.out (x : Q ⧸ Subgroup.center Q)) = χ x := by
    intro x
    obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center Q) x
    rw [hs, hmul, hcen s s.2, add_zero]
  have hmulQ : ∀ u v : Q ⧸ Subgroup.center Q,
      χ (Quotient.out (u * v)) = χ (Quotient.out u) + χ (Quotient.out v) := by
    intro u v
    induction u using QuotientGroup.induction_on with | H x =>
    induction v using QuotientGroup.induction_on with | H y =>
    rw [← QuotientGroup.mk_mul, hout, hout, hout, hmul]
  let Fv : Additive (Q ⧸ Subgroup.center Q) →+ ZMod 2 :=
    AddMonoidHom.mk' (fun u => χ (Quotient.out u.toMul)) (fun a b => hmulQ a.toMul b.toMul)
  let L : Additive (Q ⧸ Subgroup.center Q) →ₗ[ZMod 2] ZMod 2 :=
    AddMonoidHom.toZModLinearMap 2 Fv
  have hB : LinearMap.BilinForm.Nondegenerate (C.commForm) := C.commForm_nondegenerate
  let Lm : Module.Dual (ZMod 2) (Additive (Q ⧸ Subgroup.center Q)) := L
  let e := LinearMap.BilinForm.toDual (K := ZMod 2) (V := Additive (Q ⧸ Subgroup.center Q))
    (B := C.commForm) hB
  let u0 := e.symm Lm
  refine ⟨Quotient.out u0.toMul, fun v => ?_⟩
  have hq : ((Quotient.out u0.toMul : Q) : Q ⧸ Subgroup.center Q) = u0.toMul :=
    QuotientGroup.out_eq' _
  have h1 : C.commForm u0 (Additive.ofMul (v : Q ⧸ Subgroup.center Q)) =
      Lm (Additive.ofMul (v : Q ⧸ Subgroup.center Q)) :=
    LinearMap.BilinForm.apply_toDual_symm_apply (B := C.commForm) (hB := hB) Lm _
  calc pairQ (Quotient.out u0.toMul) v
      = pairV ((Quotient.out u0.toMul : Q) : Q ⧸ Subgroup.center Q) (v : Q ⧸ Subgroup.center Q) :=
        (C.pairV_mk _ _).symm
    _ = pairV u0.toMul (v : Q ⧸ Subgroup.center Q) := by rw [hq]
    _ = C.commForm u0 (Additive.ofMul (v : Q ⧸ Subgroup.center Q)) := rfl
    _ = Lm (Additive.ofMul (v : Q ⧸ Subgroup.center Q)) := h1
    _ = χ v := hout v

end KuZCore

theorem sgn_one_gen {Q : Type*} [Group Q] : sgn (1 : Q) = 0 := by
  simp [sgn]

theorem sgn_z_gen {Q : Type*} [Group Q] {z : Q} (hz : z ≠ 1) : sgn z = 1 := by
  simp [sgn, hz]

theorem sgn_eq_zero_iff_gen {Q : Type*} [Group Q] {c : Q} : sgn c = 0 ↔ c = 1 := by
  by_cases hc : c = 1
  · simp [sgn, hc]
  · simp [sgn, hc]

theorem sgn_inj_of {Q : Type*} [Group Q] {z c d : Q} (hz : z ≠ 1)
    (hc : c = 1 ∨ c = z) (hd : d = 1 ∨ d = z) (h : sgn c = sgn d) : c = d := by
  rcases hc with hc | hc <;> rcases hd with hd | hd
  · rw [hc, hd]
  · have e1 : sgn c = 0 := by rw [hc]; exact sgn_one_gen
    have e2 : sgn d = 1 := by rw [hd]; exact sgn_z_gen hz
    have h01 : (0 : ZMod 2) = 1 := by rw [← e1, h, e2]
    exact absurd h01 (by decide)
  · have e1 : sgn d = 0 := by rw [hd]; exact sgn_one_gen
    have e2 : sgn c = 1 := by rw [hc]; exact sgn_z_gen hz
    have h01 : (0 : ZMod 2) = 1 := by rw [← e1, ← h, e2]
    exact absurd h01 (by decide)
  · rw [hc, hd]

theorem sgn_mul_of {Q : Type*} [Group Q] {z c d : Q} (hz : z ≠ 1) (hz2 : z * z = 1)
    (hc : c = 1 ∨ c = z) (hd : d = 1 ∨ d = z) : sgn (c * d) = sgn c + sgn d := by
  rcases hc with hc | hc <;> rcases hd with hd | hd
  · rw [hc, hd, one_mul, sgn_one_gen, add_zero]
  · rw [hc, hd, one_mul, sgn_one_gen, sgn_z_gen hz, zero_add]
  · rw [hc, hd, mul_one, sgn_one_gen, sgn_z_gen hz, add_zero]
  · rw [hc, hd, hz2, sgn_one_gen, sgn_z_gen hz]
    decide

theorem sgn_coe {Q : Type*} [Group Q] (S : Subgroup Q) (w : S) : sgn (w : Q) = sgn w := by
  by_cases hw : w = 1
  · simp [sgn, hw]
  · have h' : (w : Q) ≠ 1 := fun h => hw (Subtype.ext h)
    simp [sgn, hw, h']

theorem comm_mem_of_quot_comm {Q : Type*} [Group Q]
    (hcomm : ∀ u v : Q ⧸ Subgroup.center Q, u * v = v * u) (a b : Q) :
    ⁅a, b⁆ ∈ Subgroup.center Q := by
  have h : ((a * b : Q) : Q ⧸ Subgroup.center Q) = ((b * a : Q) : Q ⧸ Subgroup.center Q) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact hcomm _ _
  have hk : ((a * b)⁻¹ * (b * a)) ∈ Subgroup.center Q := QuotientGroup.eq.mp h
  have hK : ((a * b)⁻¹ * (b * a))⁻¹ ∈ Subgroup.center Q := (Subgroup.center Q).inv_mem hk
  have e1 : ⁅a, b⁆ = (a * b) * (((a * b)⁻¹ * (b * a))⁻¹ * (a * b)⁻¹) := by
    simp only [commutatorElement_def]
    group
  have e2 : (a * b) * ((a * b)⁻¹ * (b * a))⁻¹ = ((a * b)⁻¹ * (b * a))⁻¹ * (a * b) :=
    (Subgroup.mem_center_iff.mp hK) (a * b)
  have e3 : ⁅a, b⁆ = ((a * b)⁻¹ * (b * a))⁻¹ := by
    rw [e1, ← mul_assoc, e2, mul_assoc, mul_inv_cancel, mul_one]
  rw [e3]
  exact hK

theorem sq_mem_of_quot_sq {Q : Type*} [Group Q]
    (hsq : ∀ u : Q ⧸ Subgroup.center Q, u ^ 2 = 1) (a : Q) : a ^ 2 ∈ Subgroup.center Q := by
  have h := hsq (a : Q ⧸ Subgroup.center Q)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h
  exact h

end CFSG.GH74.QTGen4.Ku
