module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big5
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big6
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big7

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W CFSG.GorensteinWalter
open CFSG.Blueprint

section PairInGamma

variable {F : Type} [Field F] [Finite F]

theorem orderOf_gD_one (x : Fˣ) : orderOf (gD x (1 : F ≃+* F)) = orderOf x := by
  let φ : Fˣ →* PGammaL2 F :=
    { toFun := fun x => gD x 1
      map_one' := gD_one_one
      map_mul' := fun x y => by rw [gD_mul_gD, autU_one_aut, one_mul] }
  have hφ : Function.Injective φ := fun x y h => (gD_eq_iff.mp h).1
  exact orderOf_injective φ hφ x

theorem gD_conj_gD_one (x y : Fˣ) (σ : F ≃+* F) :
    gD y σ * gD x 1 * (gD y σ)⁻¹ = gD (autU σ x) 1 := by
  rw [gD_inv, gD_mul_gD, gD_mul_gD, mul_one, autU_inv, autU_aut_inv, mul_inv_cancel, gD_eq_iff]
  refine ⟨?_, rfl⟩
  rw [mul_assoc, mul_comm (autU σ x) y⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]

theorem gA_conj_gD_one (x y : Fˣ) (σ : F ≃+* F) :
    gA y σ * gD x 1 * (gA y σ)⁻¹ = gD (autU σ x)⁻¹ 1 := by
  rw [gA_inv, gA_mul_gD, gA_mul_gA, mul_one, autU_aut_inv, mul_inv_cancel, gD_eq_iff]
  refine ⟨?_, rfl⟩
  rw [mul_assoc, mul_comm (autU σ x)⁻¹ y⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]

theorem gD_mul_self (x : Fˣ) (σ : F ≃+* F) (hσ : σ * σ = 1) :
    gD x σ * gD x σ = gD (x * autU σ x) 1 := by
  rw [gD_mul_gD, hσ]

theorem gA_mul_self (x : Fˣ) (σ : F ≃+* F) (hσ : σ * σ = 1) :
    gA x σ * gA x σ = gD (x * (autU σ x)⁻¹) 1 := by
  rw [gA_mul_gA, hσ]

theorem false_of_quat_pair_right_one (h2 : (2 : F) ≠ 0) {A B : PGammaL2 F} (hA : IsMon A)
    (hB : IsMon B) (hAr : A.right = 1) (hBr : B.right = 1) (hA2 : A * A ≠ 1)
    (hBA : B * A * B⁻¹ = A⁻¹) (hBB : B * B = ubar F) : False := by
  rcases hA with ⟨x, hx⟩ | ⟨x, hx⟩
  · rw [hAr] at hx
    rcases hB with ⟨y, hy⟩ | ⟨y, hy⟩
    · rw [hBr] at hy
      have hcomm : B * A = A * B := by
        rw [hx, hy, gD_mul_gD, gD_mul_gD]
        refine gD_eq_iff.mpr ⟨?_, rfl⟩
        rw [autU_one_aut x, autU_one_aut y]
        exact mul_comm y x
      have hBA' : B * A * B⁻¹ = A := by rw [hcomm]; group
      rw [hBA'] at hBA
      exact hA2 (inv_eq_iff_mul_eq_one.mp hBA.symm)
    · rw [hBr] at hy
      have hBB1 : B * B = 1 := by
        rw [hy, gA_mul_gA, autU_one_aut, mul_inv_cancel, one_mul, gD_one_one]
      rw [hBB1] at hBB
      exact ubar_ne_one h2 hBB.symm
  · rw [hAr] at hx
    have hAA : A * A = 1 := by
      rw [hx, gA_mul_gA, autU_one_aut, mul_inv_cancel, one_mul, gD_one_one]
    exact hA2 hAA

theorem quat_pair_shape (h2 : (2 : F) ≠ 0) {r : ℕ} (hr : 4 ≤ r) {σ₀ : F ≃+* F}
    (hσ₀ : ∀ σ : F ≃+* F, σ * σ = 1 → σ = 1 ∨ σ = σ₀) {A B : PGammaL2 F} (hA : IsMon A)
    (hB : IsMon B) (hAo : orderOf A = 2 ^ (r - 1)) (hAr : A.right * A.right = 1)
    (hBr : B.right * B.right = 1) (hBA : B * A * B⁻¹ = A⁻¹) (hBB : B * B = ubar F) :
    ∃ x₀ y : Fˣ, orderOf x₀ = 2 ^ (r - 1) ∧ A = gD x₀ 1 ∧
      ((B = gD y σ₀ ∧ autU σ₀ x₀ = x₀⁻¹ ∧ y * autU σ₀ y = -1) ∨
        (B = gA y σ₀ ∧ autU σ₀ x₀ = x₀ ∧ y * (autU σ₀ y)⁻¹ = -1)) := by
  have h8 : 8 ≤ 2 ^ (r - 1) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow2 : 2 < 2 ^ (r - 1) := by omega
  have hpow4 : 4 < 2 ^ (r - 1) := by omega
  have hA2 : A * A ≠ 1 := by
    have h : A ^ 2 ≠ 1 :=
      pow_ne_one_of_lt_orderOf (n := 2) (by norm_num) (by rw [hAo]; exact hpow2)
    rwa [sq] at h
  have hA4 : (A * A) * (A * A) ≠ 1 := by
    have h : A ^ 4 ≠ 1 :=
      pow_ne_one_of_lt_orderOf (n := 4) (by norm_num) (by rw [hAo]; exact hpow4)
    have h44 : (A * A) * (A * A) = A ^ 4 := by
      rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]
    rwa [h44]
  rcases hσ₀ A.right hAr with hs | hs <;> rcases hσ₀ B.right hBr with ht | ht
  · exfalso
    exact false_of_quat_pair_right_one h2 hA hB hs ht hA2 hBA hBB
  · rcases hA with ⟨x, hx⟩ | ⟨x, hx⟩
    · rw [hs] at hx
      rcases hB with ⟨y, hy⟩ | ⟨y, hy⟩
      · rw [ht] at hy
        refine ⟨x, y, ?_, hx, Or.inl ⟨hy, ?_, ?_⟩⟩
        · rw [← orderOf_gD_one x, ← hx, hAo]
        · have h := hBA
          rw [hy, hx, gD_conj_gD_one, gD_inv, inv_one, autU_one_aut] at h
          exact (gD_eq_iff.mp h).1
        · have h := hBB
          rw [hy, gD_mul_self y σ₀ (by rw [← ht]; exact hBr), ubar_eq] at h
          exact (gD_eq_iff.mp h).1
      · rw [ht] at hy
        refine ⟨x, y, ?_, hx, Or.inr ⟨hy, ?_, ?_⟩⟩
        · rw [← orderOf_gD_one x, ← hx, hAo]
        · have h := hBA
          rw [hy, hx, gA_conj_gD_one, gD_inv, inv_one, autU_one_aut] at h
          exact inv_inj.mp (gD_eq_iff.mp h).1
        · have h := hBB
          rw [hy, gA_mul_self y σ₀ (by rw [← ht]; exact hBr), ubar_eq] at h
          exact (gD_eq_iff.mp h).1
    · rw [hs] at hx
      exfalso
      exact hA2 (by
        rw [hx, gA_mul_gA, autU_one_aut, mul_inv_cancel, one_mul, gD_one_one])
  · have hA'r : (A * A).right = 1 := by rw [SemidirectProduct.mul_right, hAr]
    have hBA' : B * (A * A) * B⁻¹ = (A * A)⁻¹ := by
      have h1 : B * (A * A) * B⁻¹ = (B * A * B⁻¹) * (B * A * B⁻¹) := by group
      rw [h1, hBA]; group
    exfalso
    exact false_of_quat_pair_right_one h2 (isMon_mul hA hA) hB hA'r ht hA4 hBA' hBB
  · have hσσ : σ₀ * σ₀ = 1 := by rw [← ht]; exact hBr
    have hA'r : (A * A).right = 1 := by rw [SemidirectProduct.mul_right, hAr]
    have hB'r : (B * A).right = 1 := by rw [SemidirectProduct.mul_right, ht, hs]; exact hσσ
    have hBA' : (B * A) * (A * A) * (B * A)⁻¹ = (A * A)⁻¹ := by
      have h1 : (B * A) * (A * A) * (B * A)⁻¹ = (B * A * B⁻¹) * (B * A * B⁻¹) := by group
      rw [h1, hBA]; group
    have hBB' : (B * A) * (B * A) = ubar F := by
      have hcomm : A * ubar F = ubar F * A := (isMon_iff_comm_ubar h2).mp hA
      have h1 : (B * A) * (B * A) = (B * A * B⁻¹) * (B * B) * A := by group
      rw [h1, hBA, hBB]
      calc A⁻¹ * ubar F * A = A⁻¹ * (ubar F * A) := by rw [mul_assoc]
        _ = A⁻¹ * (A * ubar F) := by rw [← hcomm]
        _ = ubar F := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    exfalso
    exact false_of_quat_pair_right_one h2 (isMon_mul hA hA) (isMon_mul hB hA) hA'r hB'r hA4
      hBA' hBB'

end PairInGamma

section QEmb

variable {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F] {Q : Subgroup X} {r : ℕ}
  (E : PGamEmb X F) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2)))

@[expose] noncomputable def qEmb : QuaternionGroup (2 ^ (r - 2)) →* PGammaL2 F :=
  E.ρ.comp (MulAut.conj.comp (Q.subtype.comp e.symm.toMonoidHom))

theorem qEmb_apply (g : QuaternionGroup (2 ^ (r - 2))) :
    qEmb E e g = E.ρ (MulAut.conj ((e.symm g : ↥Q) : X)) := rfl

theorem qEmb_injective : Function.Injective (qEmb E e) :=
  E.inj.comp (E.conjInj.comp (Subtype.val_injective.comp e.symm.injective))

theorem orderOf_qEmb (g : QuaternionGroup (2 ^ (r - 2))) : orderOf (qEmb E e g) = orderOf g :=
  orderOf_injective (qEmb E e) (qEmb_injective E e) g

theorem qEmb_a_two_pow (hz : E.ρ (MulAut.conj (quatInvolution r e)) =
    SemidirectProduct.inl (pD (-1))) :
    qEmb E e (QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2)))) = ubar F := by
  rw [qEmb_apply]
  change E.ρ (MulAut.conj (quatInvolution r e)) = ubar F
  rw [hz, inl_pD_eq, ubar_eq]

theorem qEmb_comm_ubar (hr : 4 ≤ r) (hz : E.ρ (MulAut.conj (quatInvolution r e)) =
    SemidirectProduct.inl (pD (-1))) (g : QuaternionGroup (2 ^ (r - 2))) :
    qEmb E e g * ubar F = ubar F * qEmb E e g := by
  haveI : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hg : g * QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2))) =
      QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2))) * g :=
    quaternion_a_central (N := 2 ^ (r - 2)) g
  have h := congrArg (qEmb E e) hg
  simp only [map_mul] at h
  rwa [qEmb_a_two_pow E e hz] at h

theorem qEmb_isMon (h2 : (2 : F) ≠ 0) (hr : 4 ≤ r) (hz : E.ρ (MulAut.conj (quatInvolution r e)) =
    SemidirectProduct.inl (pD (-1))) (g : QuaternionGroup (2 ^ (r - 2))) :
    IsMon (qEmb E e g) :=
  (isMon_iff_comm_ubar h2).mpr (qEmb_comm_ubar E e hr hz g)

theorem qEmb_right_sq (hidx : (genFittingFStar X).index ≤ 2) (g : QuaternionGroup (2 ^ (r - 2))) :
    (qEmb E e g).right * (qEmb E e g).right = 1 := by
  rw [qEmb_apply]
  exact E.right_sq hidx _

variable {p f : ℕ}

theorem quat_structure [Fact p.Prime] (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (h4 : 4 ≤ p ^ f)
    (hidx : (genFittingFStar X).index ≤ 2) (hr : 4 ≤ r)
    (hz : E.ρ (MulAut.conj (quatInvolution r e)) = SemidirectProduct.inl (pD (-1)))
    {σ₀ : F ≃+* F} (hσ₀1 : σ₀ ≠ 1) (hσ₀2 : σ₀ * σ₀ = 1) :
    ∃ x₀ y : Fˣ, orderOf x₀ = 2 ^ (r - 1) ∧ qEmb E e (QuaternionGroup.a 1) = gD x₀ 1 ∧
      ((qEmb E e (QuaternionGroup.xa 0) = gD y σ₀ ∧ autU σ₀ x₀ = x₀⁻¹ ∧
          y * autU σ₀ y = -1) ∨
        (qEmb E e (QuaternionGroup.xa 0) = gA y σ₀ ∧ autU σ₀ x₀ = x₀ ∧
          y * (autU σ₀ y)⁻¹ = -1)) := by
  haveI : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have h2 : (2 : F) ≠ 0 := (field_facts (Fact.out : p.Prime) hp2 hF h4).2
  have hσ : ∀ σ : F ≃+* F, σ * σ = 1 → σ = 1 ∨ σ = σ₀ :=
    fun σ hσ => ringAut_sq_eq_one hF hp2 h4 hσ₀1 hσ₀2 hσ
  have hAo : orderOf (qEmb E e (QuaternionGroup.a 1)) = 2 ^ (r - 1) := by
    rw [orderOf_qEmb E e, QuaternionGroup.orderOf_a_one]
    rw [show r - 1 = (r - 2) + 1 by omega, pow_succ]
    ring
  have hqba : qEmb E e (QuaternionGroup.xa 0) * qEmb E e (QuaternionGroup.a 1) *
      (qEmb E e (QuaternionGroup.xa 0))⁻¹ = (qEmb E e (QuaternionGroup.a 1))⁻¹ := by
    have hq : (QuaternionGroup.xa 0 * QuaternionGroup.a 1 *
        (QuaternionGroup.xa 0)⁻¹ : QuaternionGroup (2 ^ (r - 2))) = (QuaternionGroup.a 1)⁻¹ := by
      have hN : (((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2))) +
          ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2)))) = 0 := by
        rw [← Nat.cast_add]
        convert ZMod.natCast_self (2 * 2 ^ (r - 2)) using 1
        ring
      have hinv_a : (QuaternionGroup.a (1 : ZMod (2 * 2 ^ (r - 2))) :
          QuaternionGroup (2 ^ (r - 2)))⁻¹ = QuaternionGroup.a (-1) := by
        apply inv_eq_of_mul_eq_one_right
        rw [QuaternionGroup.a_mul_a, add_neg_cancel]
        rfl
      have hinv_xa : (QuaternionGroup.xa (0 : ZMod (2 * 2 ^ (r - 2))) :
          QuaternionGroup (2 ^ (r - 2)))⁻¹ =
          QuaternionGroup.xa ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2))) := by
        apply inv_eq_of_mul_eq_one_right
        rw [QuaternionGroup.xa_mul_xa, sub_zero, hN]
        rfl
      rw [hinv_xa, QuaternionGroup.xa_mul_a, QuaternionGroup.xa_mul_xa, hinv_a]
      congr 1
      rw [zero_add]
      linear_combination hN
    calc qEmb E e (QuaternionGroup.xa 0) * qEmb E e (QuaternionGroup.a 1) *
            (qEmb E e (QuaternionGroup.xa 0))⁻¹
        = qEmb E e (QuaternionGroup.xa 0 * QuaternionGroup.a 1 *
            (QuaternionGroup.xa 0)⁻¹) := by rw [← map_mul, ← map_inv, ← map_mul]
      _ = qEmb E e ((QuaternionGroup.a 1)⁻¹) := by rw [hq]
      _ = (qEmb E e (QuaternionGroup.a 1))⁻¹ := by rw [map_inv]
  have hqbb : qEmb E e (QuaternionGroup.xa 0) * qEmb E e (QuaternionGroup.xa 0) = ubar F := by
    rw [← map_mul]
    have hxx : (QuaternionGroup.xa 0 * QuaternionGroup.xa 0 : QuaternionGroup (2 ^ (r - 2))) =
        QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2))) := by
      rw [QuaternionGroup.xa_mul_xa]
      congr 1
      ring
    rw [hxx, qEmb_a_two_pow E e hz]
  obtain ⟨x₀, y, hx₀ord, hA, hB⟩ := quat_pair_shape h2 hr hσ
    (qEmb_isMon E e h2 hr hz (QuaternionGroup.a 1))
    (qEmb_isMon E e h2 hr hz (QuaternionGroup.xa 0))
    hAo
    (qEmb_right_sq E e hidx (QuaternionGroup.a 1))
    (qEmb_right_sq E e hidx (QuaternionGroup.xa 0))
    hqba hqbb
  exact ⟨x₀, y, hx₀ord, hA, hB⟩

end QEmb

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
