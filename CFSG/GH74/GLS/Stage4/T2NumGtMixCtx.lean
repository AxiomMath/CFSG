module

public import CFSG.GH74.GLS.Stage4.T2Ctx
public import CFSG.GH74.GLS.Stage4.T2NumGtMixDefs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4
  CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

theorem t2Ctx_ofW
    {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z t : G}
    {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) {N : T2N1 G} {u : G}
    (hLoc : Ch6Loc5W N u) (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂) (hq₁ : N.q₁ = q₁)
    (hq₂ : N.q₂ = q₂) : T2Ctx z K₁ K₂ N.S := by
  subst hz hK₁ hK₂ hq₁ hq₂
  obtain ⟨q₁, q₂, z, S, K₁, K₂, H, X₁, X₁', X₂, X₂', w₁, w₂⟩ := N
  have hK₁eq : K₁ = X₁ ⊔ X₁' := hLoc.K₁_eq
  have hK₂eq : K₂ = X₂ ⊔ X₂' := hLoc.K₂_eq
  have hzz : z * z = 1 := t2C_zz hSet
  have hz1 : z ≠ 1 := t2C_z_ne hSet
  have hgen₁ := t2C_gen_odd hLoc.q₁_odd hK₁eq hLoc.X₁_exp hLoc.X₁'_exp
  have hgen₂ := t2C_gen_odd hLoc.q₂_odd hK₂eq hLoc.X₂_exp hLoc.X₂'_exp
  have hC : T2Comp z K₁ K₂ := t2C_comp_of hSet hgen₁ hgen₂
  have hSctx : T2SCtx z K₁ K₂ S :=
    ⟨hLoc.S_pGroup, hLoc.S_sylow, hLoc.z_mem_S, hLoc.z_cent_S, hLoc.S_idx⟩
  have hSC₁ : S ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G)) :=
    le_oPrimeResidualOf_centralizer hSctx.S2 hSctx.Sz
  refine ⟨hzz, hz1, hC, hSctx,
    t2C_K_normal hSet hK₁eq hK₂eq hLoc.X₁_exp hLoc.X₁'_exp hLoc.X₂_exp hLoc.X₂'_exp, hSC₁, ?_,
    Subgroup.map_subtype_le _, fun c hc x hx => t2C_oPrimeResidualOf_conj 2 hc hx,
    t2C_ZS hSet hRem hC hSctx⟩
  refine sup_eq_of_relIndex_two le_sup_left (sup_le hSet.le_residual hSC₁) hSet.index_two ?_
  intro hle
  have hSK : S ≤ K₁ ⊔ K₂ := le_trans le_sup_right hle
  have h1 : (S ⊓ (K₁ ⊔ K₂)).relIndex S = 1 := by
    rw [Subgroup.relIndex_eq_one]
    exact fun x hx => ⟨hx, hSK hx⟩
  have h2 := hSctx.SK
  rw [h1] at h2
  exact absurd h2 (by norm_num)

end CFSG.GH74.GLS.Stage4.Rest
