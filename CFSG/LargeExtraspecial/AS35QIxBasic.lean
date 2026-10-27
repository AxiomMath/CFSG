module

public import CFSG.LargeExtraspecial.AS35QIxCo
public import CFSG.LargeExtraspecial.AS35QIxInvol

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QIx

open Subgroup Module QuadraticMap CFSG.Fischer.Classification.Unitary
  CFSG.ClassicalGroups.Unitary CFSG.RankThree.OrthogonalInvolutions
open CFSG.Blueprint.Fischer (K)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem coe_mul_self {σ : S.O} (h : σ * σ = 1) :
    (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) * (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1 :=
  congrArg Subtype.val h

theorem coe_ne_one {σ : S.O} (h : σ ≠ 1) : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠ 1 :=
  fun h' => h (Subtype.ext h')

namespace IxSetup

variable (T : IxSetup S)

include T in
theorem finrank_Qt : finrank (ZMod 2) S.Qt = 6 := by
  rw [S.finrank_Qt_eq_two_mul_width, T.hw]

theorem zeta_fix {v : S.Qt} (h : (T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) : v = 0 :=
  eq_zero_of_zeta_eq T.hζ2 h

include T in
theorem zGen_eq_top (hS : S.SixHyp) : S.zGen = ⊤ :=
  S.zGen_eq_top_of_fixSpace hS fun _ hv => T.zeta_fix (hv T.ζ (T.hXM T.hζX))

include T in
theorem isSimpleGroup (hS : S.SixHyp) : IsSimpleGroup G := by
  have : IsSimpleGroup S.zGen := hS.simple
  exact (Subgroup.topEquiv.symm.trans
    (MulEquiv.subgroupCongr (T.zGen_eq_top hS).symm)).isSimpleGroup

theorem zeta_mem_Mbar : T.ζ ∈ S.Mbar := T.hXM T.hζX

theorem conj_zeta {m : S.O} (hm : m ∈ S.Mbar) :
    m * T.ζ * m⁻¹ = T.ζ ∨ m * T.ζ * m⁻¹ = T.ζ⁻¹ := by
  have h1 : m * T.ζ * m⁻¹ ∈ T.X := T.hXn m hm T.ζ T.hζX
  have h2 : ∀ x ∈ T.X, m * T.ζ * m⁻¹ * x = x * (m * T.ζ * m⁻¹) := by
    intro x hx
    have hx' : m⁻¹ * x * m⁻¹⁻¹ ∈ T.X := T.hXn m⁻¹ (inv_mem hm) x hx
    have hc := T.hζc _ hx'
    rw [inv_inv] at hx' hc
    calc m * T.ζ * m⁻¹ * x = m * (T.ζ * (m⁻¹ * x * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * x * m) * T.ζ) * m⁻¹ := by rw [hc]
      _ = x * (m * T.ζ * m⁻¹) := by group
  rcases AS35V.eq_one_or_eq_or_eq_inv_of_mem_zpowers T.hζ3 (T.hcen _ h1 h2) with h | h | h
  · exfalso
    apply T.hζ1
    calc T.ζ = m⁻¹ * (m * T.ζ * m⁻¹) * m := by group
      _ = 1 := by rw [h]; group
  · exact Or.inl h
  · exact Or.inr h

theorem comm_of_conj_eq {m : S.O} (h : m * T.ζ * m⁻¹ = T.ζ) : m * T.ζ = T.ζ * m := by
  calc m * T.ζ = m * T.ζ * m⁻¹ * m := by group
    _ = T.ζ * m := by rw [h]

theorem zeta_ne_inv : T.ζ ≠ T.ζ⁻¹ := by
  intro h
  apply T.hζ1
  have h2 : T.ζ * T.ζ = 1 := by
    calc T.ζ * T.ζ = T.ζ * T.ζ⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel _
  calc T.ζ = T.ζ ^ 3 * (T.ζ * T.ζ)⁻¹ := by group
    _ = 1 := by rw [T.hζ3, h2]; group

theorem conj_inv_of_not_comm {m : S.O} (hm : m ∈ S.Mbar) (h : m * T.ζ ≠ T.ζ * m) :
    m * T.ζ * m⁻¹ = T.ζ⁻¹ :=
  (T.conj_zeta hm).resolve_left fun h' => h (T.comm_of_conj_eq h')

theorem comm_zeta_of_pow_three {m : S.O} (hm : m ∈ S.Mbar) (h3 : m ^ 3 = 1) :
    m * T.ζ = T.ζ * m := by
  by_contra hne
  have h1 : MulAut.conj m T.ζ = T.ζ⁻¹ := T.conj_inv_of_not_comm hm hne
  have h3c : MulAut.conj (m ^ 3) T.ζ = T.ζ := by rw [h3, map_one]; rfl
  rw [map_pow, pow_three, MulAut.mul_apply, MulAut.mul_apply, h1, map_inv, h1, inv_inv,
    h1] at h3c
  exact T.zeta_ne_inv h3c.symm

theorem comm_of_inv_of_inv {m m' : S.O} (hm : m * T.ζ * m⁻¹ = T.ζ⁻¹)
    (hm' : m' * T.ζ * m'⁻¹ = T.ζ⁻¹) : (m * m') * T.ζ = T.ζ * (m * m') := by
  refine T.comm_of_conj_eq ?_
  calc m * m' * T.ζ * (m * m')⁻¹ = m * (m' * T.ζ * m'⁻¹) * m⁻¹ := by group
    _ = (m * T.ζ * m⁻¹)⁻¹ := by rw [hm']; group
    _ = T.ζ := by rw [hm, inv_inv]

theorem tb_comm_zeta : T.tb * T.ζ = T.ζ * T.tb := T.zeta_comm_tb.symm

theorem pbarFacts (hS : S.SixHyp) : AS35V.PbarFacts S T.tb (S.PbarAsc T.g) :=
  AS35V.pbarFacts_of_asc512 S14.asc512PbarStmt hS T.hgD T.hgM

theorem pbar_comm_zeta (hS : S.SixHyp) {p : S.O} (hp : p ∈ S.PbarAsc T.g) :
    p * T.ζ = T.ζ * p := by
  have hpM : p ∈ S.Mbar := Subgroup.map_le_range _ _ hp
  refine (T.pbarFacts hS).commute_of_normalizes T.zeta_mem_Mbar T.zeta_comm_tb T.hζ3
    (fun p' hp' => ?_) hp
  rcases T.conj_zeta (Subgroup.map_le_range _ _ hp') with h | h
  · rw [h]
    exact mem_zpowers _
  · rw [h]
    exact inv_mem (mem_zpowers _)

theorem apply_comm_of_comm {σ : S.O} (h : σ * T.ζ = T.ζ * σ) (v : S.Qt) :
    (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      (T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) :=
  congrArg (fun r : S.O => (r : S.Qt ≃ₗ[ZMod 2] S.Qt) v) h

theorem qζ (v : S.Qt) : S.q ((T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = S.q v :=
  AS35QTh.q_apply T.ζ v

theorem isTypeA_O {σ : S.O} (hσ : σ * T.ζ = T.ζ * σ) (hσσ : σ * σ = 1) (hσ1 : σ ≠ 1) :
    IsTypeA S.q (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 :=
  isTypeA_two_of_comm S.q_nondegenerate T.finrank_Qt T.hζ2 T.qζ σ.2 (coe_mul_self hσσ)
    (T.apply_comm_of_comm hσ) (coe_ne_one hσ1)

theorem eq_of_commute_O {σ τ : S.O} (hσ : σ * T.ζ = T.ζ * σ) (hτ : τ * T.ζ = T.ζ * τ)
    (hσσ : σ * σ = 1) (hττ : τ * τ = 1) (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1) (hστ : σ * τ = τ * σ) :
    σ = τ :=
  Subtype.ext (eq_of_commute_of_comm S.q_nondegenerate T.finrank_Qt T.hζ2 T.qζ σ.2 τ.2
    (coe_mul_self hσσ) (coe_mul_self hττ) (T.apply_comm_of_comm hσ)
    (T.apply_comm_of_comm hτ) (coe_ne_one hσ1) (coe_ne_one hτ1) (congrArg Subtype.val hστ))

theorem eq_or_of_commute_O {σ τ : S.O} (hσ : σ * T.ζ = T.ζ * σ) (hτ : τ * T.ζ = T.ζ * τ)
    (hσσ : σ * σ = 1) (hττ : τ * τ = 1) (hστ : σ * τ = τ * σ) : σ = τ ∨ σ = 1 ∨ τ = 1 := by
  by_cases hσ1 : σ = 1
  · exact Or.inr (Or.inl hσ1)
  by_cases hτ1 : τ = 1
  · exact Or.inr (Or.inr hτ1)
  exact Or.inl (T.eq_of_commute_O hσ hτ hσσ hττ hσ1 hτ1 hστ)

theorem commSpace_eq_span_O {σ : S.O} (hσ : σ * T.ζ = T.ζ * σ) (hσσ : σ * σ = 1) {a : S.Qt}
    (ha : a ∈ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)) (ha0 : a ≠ 0) :
    commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      Submodule.span (ZMod 2) {a, (T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) a} :=
  commSpace_eq_span_of_comm S.q_nondegenerate T.finrank_Qt T.hζ2 T.qζ σ.2
    (coe_mul_self hσσ) (T.apply_comm_of_comm hσ) ha ha0

@[expose] def t : G := T.g * S.z * T.g⁻¹

theorem t_def : T.t = T.g * S.z * T.g⁻¹ := rfl

theorem t_mem_DSet : T.t ∈ S.DSet := T.hgD

theorem t_mul_self : T.t * T.t = 1 := S.mul_self_of_isConj (S.isConj_of_mem_ESet T.hgD.1)

theorem t_mem_M : T.t ∈ S.M := T.hgM

theorem tb_eq : T.tb = S.ρ ⟨T.t, T.t_mem_M⟩ := rfl

theorem t_comm_z : T.t * S.z = S.z * T.t := S.mem_M_iff.mp T.hgM

theorem t_ne_z : T.t ≠ S.z := S.ne_z_of_mem_ESet T.hgD.1

theorem not_isConj_zt : ¬ IsConj S.z (S.z * T.t) := T.hgD.2

theorem g_inv_z : T.g⁻¹ * S.z * T.g = T.t := by
  rw [t_def]
  calc T.g⁻¹ * S.z * T.g = T.g⁻¹ * (T.g * (T.g * S.z * T.g⁻¹) * T.g⁻¹) * T.g := by
        rw [T.hswap]
    _ = T.g * S.z * T.g⁻¹ := by group

theorem g_inv_t : T.g⁻¹ * T.t * T.g = S.z := by
  rw [t_def]
  group

theorem g_t : T.g * T.t * T.g⁻¹ = S.z := T.hswap

theorem g_z : T.g * S.z * T.g⁻¹ = T.t := rfl

end IxSetup

end CFSG.LargeExtraspecial.AS35QIx
