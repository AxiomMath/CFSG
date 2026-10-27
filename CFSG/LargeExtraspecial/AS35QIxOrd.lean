module

public import CFSG.LargeExtraspecial.AS35QIxLift
public import CFSG.LargeExtraspecial.AS35QThGrp
public import CFSG.LargeExtraspecial.AS35QThTheta
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QIx

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
  CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.Blueprint.Fischer (K)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace IxLift

variable (T : IxLift S)


@[expose] noncomputable def Yh : G := T.g * T.Zh * T.g⁻¹

theorem inv_conj_z : T.g⁻¹ * S.z * T.g = T.g * S.z * T.g⁻¹ := by
  calc T.g⁻¹ * S.z * T.g = T.g⁻¹ * (T.g * (T.g * S.z * T.g⁻¹) * T.g⁻¹) * T.g := by
        rw [T.hswap]
    _ = T.g * S.z * T.g⁻¹ := by group

theorem Yh_mem_M : T.Yh ∈ S.M := by
  rw [S.mem_M_iff]
  have h1 := T.inv_conj_z
  calc T.g * T.Zh * T.g⁻¹ * S.z = T.g * (T.Zh * (T.g⁻¹ * S.z * T.g)) * T.g⁻¹ := by group
    _ = T.g * (T.Zh * (T.g * S.z * T.g⁻¹)) * T.g⁻¹ := by rw [h1]
    _ = T.g * (T.g * S.z * T.g⁻¹ * T.Zh) * T.g⁻¹ := by rw [T.hZt]
    _ = T.g * (T.g⁻¹ * S.z * T.g * T.Zh) * T.g⁻¹ := by rw [h1]
    _ = S.z * (T.g * T.Zh * T.g⁻¹) := by group

theorem Yh_comm_t : T.Yh * (T.g * S.z * T.g⁻¹) = T.g * S.z * T.g⁻¹ * T.Yh := by
  have hZz : T.Zh * S.z = S.z * T.Zh := S.z_comm T.hZhM
  calc T.g * T.Zh * T.g⁻¹ * (T.g * S.z * T.g⁻¹) = T.g * (T.Zh * S.z) * T.g⁻¹ := by group
    _ = T.g * (S.z * T.Zh) * T.g⁻¹ := by rw [hZz]
    _ = T.g * S.z * T.g⁻¹ * (T.g * T.Zh * T.g⁻¹) := by group

theorem gg_mem_M : T.g * T.g ∈ S.M := by
  rw [S.mem_M_iff]
  have h := T.hswap
  calc T.g * T.g * S.z = T.g * (T.g * S.z * T.g⁻¹) * T.g⁻¹ * (T.g * T.g) := by group
    _ = S.z * (T.g * T.g) := by rw [h]

@[expose] noncomputable def y : S.O := S.ρ ⟨T.Yh, T.Yh_mem_M⟩

theorem y_comm_t : T.y * S.ρ ⟨_, T.hgM⟩ = S.ρ ⟨_, T.hgM⟩ * T.y := by
  rw [y, ← map_mul, ← map_mul]
  exact congrArg S.ρ (Subtype.ext T.Yh_comm_t)

theorem y_pow_three : T.y ^ 3 = 1 := by
  rw [y, ← map_pow]
  have e : (⟨T.Yh, T.Yh_mem_M⟩ : S.M) ^ 3 = 1 := by
    apply Subtype.ext
    change (T.g * T.Zh * T.g⁻¹) ^ 3 = 1
    rw [← MulAut.conj_apply, ← map_pow, T.hZ3, map_one]
  rw [e, map_one]

theorem mem_commSpace_of_forall (hS : S.SixHyp)
    (hall : ∀ p ∈ S.PbarAsc T.g, T.y * p = p * T.y) {v : S.Qt}
    (hv : v ∈ fixSpace (S.rhoL T.hgM)) :
    (T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) v + v ∈ commSpace (S.rhoL T.hgM) := by
  obtain ⟨c, hc, rfl⟩ := S.exists_cl v
  set t := T.g * S.z * T.g⁻¹ with ht
  have hct : t * c * t⁻¹ = c := S.conj_eq_of_cl_conj_eq hS.sixFour hS.weak T.hgD T.hgM hc (by
    rw [← S.rhoL_cl T.hgM hc]
    exact mem_fixSpace.mp hv)
  have hct' : c * t = t * c := by
    calc c * t = t * c * t⁻¹ * t := by rw [hct]
      _ = t * c := by group
  set p := T.g * c * T.g⁻¹ with hp
  have hpQa : p ∈ S.Qa T.g := by
    rw [S.mem_Qa_iff_inv_conj_mem, show T.g⁻¹ * p * T.g = c by rw [hp]; group]
    exact hc
  have h1 := T.inv_conj_z
  have hpM : p ∈ S.M := by
    rw [S.mem_M_iff]
    calc T.g * c * T.g⁻¹ * S.z = T.g * (c * (T.g⁻¹ * S.z * T.g)) * T.g⁻¹ := by group
      _ = T.g * (c * t) * T.g⁻¹ := by rw [h1]
      _ = T.g * (t * c) * T.g⁻¹ := by rw [hct']
      _ = T.g * (T.g⁻¹ * S.z * T.g * c) * T.g⁻¹ := by rw [h1]
      _ = S.z * (T.g * c * T.g⁻¹) := by group
  have hpP : S.ρ ⟨p, hpM⟩ ∈ S.PbarAsc T.g :=
    ⟨⟨p, hpM⟩, Subgroup.mem_subgroupOf.mpr ⟨hpQa, hpM⟩, rfl⟩
  have hyp := hall _ hpP
  have hYM := T.Yh_mem_M
  have hwM : T.Yh * p * T.Yh⁻¹ * p⁻¹ ∈ S.M :=
    S.M.mul_mem (S.M.mul_mem (S.M.mul_mem hYM hpM) (S.M.inv_mem hYM)) (S.M.inv_mem hpM)
  have hwQ : T.Yh * p * T.Yh⁻¹ * p⁻¹ ∈ S.QG := by
    have e : (⟨_, hwM⟩ : S.M) = ⟨T.Yh, hYM⟩ * ⟨p, hpM⟩ * (⟨T.Yh, hYM⟩ : S.M)⁻¹ *
        (⟨p, hpM⟩ : S.M)⁻¹ := rfl
    refine (S.ρ_eq_one_iff ⟨_, hwM⟩).mp ?_
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
    change T.y * S.ρ ⟨p, hpM⟩ * T.y⁻¹ * (S.ρ ⟨p, hpM⟩)⁻¹ = 1
    rw [hyp]
    group
  set w' := T.Zh * c * T.Zh⁻¹ * c⁻¹ with hw'
  have hw'Q : w' ∈ S.QG := S.QG.mul_mem (S.conj_mem_QG T.hZhM hc) (S.QG.inv_mem hc)
  have hw'Qa : w' ∈ S.Qa T.g := by
    rw [S.mem_Qa_iff_inv_conj_mem]
    have := S.conj_mem_QG (S.M.inv_mem T.gg_mem_M) hwQ
    rwa [show (T.g * T.g)⁻¹ * (T.Yh * p * T.Yh⁻¹ * p⁻¹) * (T.g * T.g)⁻¹⁻¹ =
      T.g⁻¹ * w' * T.g by rw [Yh, hp, hw']; group] at this
  have hcomm := S.cl_mem_commSpace_of_commute hS.sixFour hS.weak T.hgD T.hgM hw'Q
    (S.commute_of_mem_inf_Qa_J hS T.hgD rfl (mem_inf.mpr ⟨hw'Q, hw'Qa⟩))
  rwa [hw', S.cl_mul (S.conj_mem_QG T.hZhM hc) (S.QG.inv_mem hc), S.cl_inv hc,
    ← S.rhoL_cl T.hZhM hc, T.rhoL_Zh] at hcomm

theorem exists_not_commute (hS : S.SixHyp) :
    ∃ p ∈ S.PbarAsc T.g, T.y * p ≠ p * T.y := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  by_contra hall
  push Not at hall
  obtain ⟨hA, -, -⟩ := S.fiveOne_two hS.sixFour hS.weak T.hgD T.hgM
  have hc2 : finrank (ZMod 2) (commSpace (S.rhoL T.hgM)) = 2 := hA.2.2.2.1
  have hsum := finrank_commSpace_add_finrank_fixSpace (S.rhoL T.hgM)
  rw [S.finrank_Qt_eq_two_mul_width, T.hw] at hsum
  set f : fixSpace (S.rhoL T.hgM) →ₗ[ZMod 2] commSpace (S.rhoL T.hgM) :=
    LinearMap.codRestrict (commSpace (S.rhoL T.hgM))
      (((T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap + LinearMap.id).domRestrict
        (fixSpace (S.rhoL T.hgM)))
      (fun v => T.mem_commSpace_of_forall hS hall v.2) with hf
  have hfi : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h0 : (T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) v + v = 0 := congrArg Subtype.val hv
    have h1 : (T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
      calc (T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = (T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) v + v + v := by
            rw [add_assoc, AS35QTh.add_self_V, add_zero]
        _ = v := by rw [h0, zero_add]
    exact Subtype.ext (T.zeta_fix h1)
  have := LinearMap.finrank_le_finrank_of_injective hfi
  omega

theorem y_not_mem (hS : S.SixHyp) : T.y ∉ T.X := by
  intro hy
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (T.hCt _ hy T.y_comm_t)
  obtain ⟨p, hp, hne⟩ := T.exists_not_commute hS
  apply hne
  rw [← hk]
  exact (Commute.zpow_left (T.pbar_comm_zeta hS hp).symm k).eq

theorem y_mem_Mbar : T.y ∈ S.Mbar := ⟨_, rfl⟩

theorem y_comm_zeta : T.y * T.ζ = T.ζ * T.y :=
  T.comm_zeta_of_pow_three T.y_mem_Mbar T.y_pow_three

@[expose] noncomputable def Mbar0 : Subgroup S.O := S.Mbar ⊓ centralizer {T.ζ}

theorem mem_Mbar0 {σ : S.O} : σ ∈ T.Mbar0 ↔ σ ∈ S.Mbar ∧ σ * T.ζ = T.ζ * σ := by
  rw [Mbar0, mem_inf, mem_centralizer_singleton_iff]

theorem le_card_Mbar0 (hS : S.SixHyp) : 648 ≤ Nat.card T.Mbar0 := by
  have := AS35QTh.finite_O S
  obtain ⟨-, -, hcard, -⟩ := S14.asc512PbarStmt G S hS T.g T.hgD T.hgM
  rw [T.hw] at hcard
  refine AS35QTh.le_card_of_normal (X := T.X) (P := S.PbarAsc T.g) (y := T.y)
    (fun x hx => T.mem_Mbar0.mpr ⟨T.hXM hx, (T.hζc x hx).symm⟩)
    (fun m hm x hx => T.hXn m (T.mem_Mbar0.mp hm).1 x hx) T.hX27
    (fun p hp => T.mem_Mbar0.mpr ⟨Subgroup.map_le_range _ _ hp, T.pbar_comm_zeta hS hp⟩)
    (by rw [hcard]; norm_num) (T.mem_Mbar0.mpr ⟨T.y_mem_Mbar, T.y_comm_zeta⟩) (T.y_not_mem hS)
    T.y_pow_three

theorem card_centralizer_le : Nat.card (centralizer {T.ζ} : Subgroup S.O) ≤ 648 :=
  T.hl.card_le _ fun σ hσ v => by
    have h := mem_centralizer_singleton_iff.mp hσ
    exact congrArg (fun s : S.O => (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v) h

theorem Mbar0_eq (hS : S.SixHyp) : T.Mbar0 = centralizer {T.ζ} := by
  have := AS35QTh.finite_O S
  exact Subgroup.eq_of_le_of_card_ge inf_le_right
    ((T.card_centralizer_le).trans (T.le_card_Mbar0 hS))

theorem card_Mbar0 (hS : S.SixHyp) : Nat.card T.Mbar0 = 648 :=
  le_antisymm (by rw [T.Mbar0_eq hS]; exact T.card_centralizer_le) (T.le_card_Mbar0 hS)

theorem mem_Mbar_of_comm (hS : S.SixHyp) {σ : S.O} (hσ : σ * T.ζ = T.ζ * σ) : σ ∈ S.Mbar := by
  have h : σ ∈ T.Mbar0 := by
    rw [T.Mbar0_eq hS]
    exact mem_centralizer_singleton_iff.mpr hσ
  exact (T.mem_Mbar0.mp h).1

end IxLift

end CFSG.LargeExtraspecial.AS35QIx
