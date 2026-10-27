module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResHH
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL2Cent

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResHH

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
  CFSG.LocalAnalysis.ComponentInitial

theorem hhobsAt_alt7 {Y : Type} [Group Y] (e : Y ≃* alternatingGroup (Fin 7)) (b : MulAut Y)
    (hb : orderOf b = 3) : HHObsAt 3 2 Y b :=
  hhobsAt_of_perm (Or.inr rfl) e b
    (σ := autTransport (by norm_num : 5 ≤ 7) (by norm_num) e b)
    (by rw [MulEquiv.orderOf_eq]; exact hb)
    (fun y => autTransport_apply (by norm_num) (by norm_num) e b y)

variable {F : Type} [Field F] [Finite F] {Y : Type} [Group Y]

theorem inner_of_orderOf_three (hF : Nat.card F = 9) (e : Y ≃* L2 F) {b : MulAut Y}
    (hb : orderOf b = 3) : ∃ y : Y, orderOf y = 3 ∧ b = MulAut.conj y := by
  set Φ := pgammaAut e with hΦ
  set x := Φ.symm b with hx
  have hx3 : orderOf x = 3 := by rw [hx, MulEquiv.orderOf_eq, hb]
  have hr : x.right = 1 := by
    have h1 : orderOf x.right ∣ 3 := hx3 ▸ orderOf_map_dvd SemidirectProduct.rightHom x
    have h2 : orderOf x.right ∣ 2 := by
      have hcard := (card_ringAut_and_isCyclic Nat.prime_three F
        (show Nat.card F = 3 ^ 2 by rw [hF]; norm_num)).1
      have h0 := orderOf_dvd_natCard x.right
      rwa [hcard] at h0
    have : orderOf x.right = 1 := Nat.eq_one_of_dvd_coprimes (by norm_num) h1 h2
    exact orderOf_eq_one_iff.mp this
  have hxl : x = SemidirectProduct.inl x.left := by
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x, hr, map_one, mul_one]
  have hodd : IsOddPrimePower (Nat.card F) := ⟨3, 2, Nat.prime_three, by decide, by norm_num, hF⟩
  have hidx := pgl2_psl2Range_index_eq_two F hodd
  have hg3 : x.left ^ 3 = 1 := by
    have h1 : orderOf (SemidirectProduct.inl x.left : PGammaL2 F) = orderOf x.left :=
      orderOf_injective SemidirectProduct.inl SemidirectProduct.inl_injective x.left
    rw [← hxl, hx3] at h1
    have h2 := pow_orderOf_eq_one x.left
    rwa [← h1] at h2
  obtain ⟨s, hs⟩ : x.left ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2)
      (R := F)).range := by
    have h2 := Subgroup.sq_mem_of_index_two hidx x.left
    have : x.left = (x.left ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, hg3, one_mul]
    rw [this]
    exact Subgroup.sq_mem_of_index_two hidx _
  set y : Y := (toPSL e).symm s with hy
  have hby : b = MulAut.conj y := by
    have h1 : Φ x = b := by rw [hx, MulEquiv.apply_symm_apply]
    rw [← h1, hxl, ← hs, hΦ, pgammaAut_inl]
    have h2 := L2Borel.innDiagHom_toPGL_toPSL e y
    rw [hy, MulEquiv.apply_symm_apply] at h2
    exact h2
  refine ⟨y, ?_, hby⟩
  rw [← hb, hby]
  exact (orderOf_injective _ (conj_injective_of_L2 e) y).symm

theorem hhobsAt_l2_nine (hF : Nat.card F = 9) (e : Y ≃* L2 F) {b : MulAut Y}
    (hb : orderOf b = 3) : HHObsAt 3 2 Y b := by
  obtain ⟨y, hy3, rfl⟩ := inner_of_orderOf_three hF e hb
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨eA⟩ := unique_field_nine_projective_linear_alternating_six_isomorphism F
    (by rw [← Nat.card_eq_fintype_card, hF])
  set e₆ : Y ≃* alternatingGroup (Fin 6) := (toPSL e).trans eA with he₆
  refine hhobsAt_of_perm (Or.inl rfl) e₆ (MulAut.conj y)
    (σ := ((e₆ y : alternatingGroup (Fin 6)) : Perm (Fin 6))) ?_ (fun x => ?_)
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hy3]
  · rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
    rfl

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResHH
