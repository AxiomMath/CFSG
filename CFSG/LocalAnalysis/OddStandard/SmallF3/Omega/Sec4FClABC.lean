module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FClStruct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FClC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FClB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem conjugate_one_eq (H : Subgroup G) : CFSG.conjugate H 1 = H := by
  ext x
  rw [mem_conjugate_iff]
  simp

theorem sec4FCl_claims_B_C1 [Finite G] (h36 : Asc82Lemma36) (h43 : Asc82Lemma43)
    (hf43c : Asc82Fact43Class) {t : G} {L S : Subgroup G} {z : G} (hctx : Sec4Ctx G t L S z)
    {g : G} (hgc : g⁻¹ * t * g ∈ centralizer ({t} : Set G))
    (hg6 : InducesTypeSome L (g⁻¹ * t * g) 7 1 6 1) :
    InducesTypeSome (CFSG.conjugate L g) t 7 1 6 1 ∧
      L ⊓ centralizer ({g⁻¹ * t * g} : Set G) ≤
        (L ⊓ CFSG.conjugate L g) ⊔ Sec4FOdd L := by
  have hL : IsOmega7Group L := sec4_isOmega7Group hctx.toSec4Setting
  have hs2 : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
    have h : orderOf (g⁻¹ * t * g) = 2 := by
      rw [orderOf_conjugate_eq, hctx.involution]
    have h1 := pow_orderOf_eq_one (g⁻¹ * t * g)
    rwa [h, pow_two] at h1
  have hts : t * (g⁻¹ * t * g) = (g⁻¹ * t * g) * t :=
    (Subgroup.mem_centralizer_singleton_iff.mp hgc).symm
  obtain ⟨X, w, hXc, hXl, hwL, hws, hw4, hle⟩ := sec4FCl_structure hL hs2 hg6
  have hXF : InFStar X := sec4FCl_inFStar_of_l43 hXc.isQuasisimple hXl
  have hXL' : X ≤ CFSG.conjugate L g :=
    sec4FCl_component_le h36 hctx.toSec4Setting.toSec3SettingLB
      (hctx.conjugate g).toSec4Setting.toSec3SettingLB hts hXc hXF
  have hwL' : w ∈ CFSG.conjugate L g :=
    sec4FCl_w_mem_conjugate h43 hf43c hctx hgc hg6 hwL hws hw4
  refine ⟨sec4FCl_claimB h36 hctx hgc hXc hXl hXL', ?_⟩
  have hXL : X ≤ L ⊓ CFSG.conjugate L g := le_inf (hXc.le.trans inf_le_left) hXL'
  have h1 : X ⊔ Subgroup.zpowers w ≤ (L ⊓ CFSG.conjugate L g) ⊔ Sec4FOdd L :=
    le_trans (sup_le hXL (Subgroup.zpowers_le.mpr ⟨hwL, hwL'⟩)) le_sup_left
  have h2 : Sec4FOdd L ≤ (L ⊓ CFSG.conjugate L g) ⊔ Sec4FOdd L := le_sup_right
  exact hle.trans (sup_le h1 h2)

theorem asc82ClaimsABC_of (h36 : Asc82Lemma36) (h43 : Asc82Lemma43)
    (hf43c : Asc82Fact43Class) : Asc82ClaimsABC := by
  intro G _ _ t L S z hctx g hgc hg6
  obtain ⟨hB, hC1⟩ := sec4FCl_claims_B_C1 h36 h43 hf43c hctx hgc hg6
  refine ⟨hB, hC1, ?_⟩
  have hgc' : (g⁻¹)⁻¹ * (g⁻¹ * t * g) * g⁻¹ ∈ centralizer ({g⁻¹ * t * g} : Set G) := by
    rw [show (g⁻¹)⁻¹ * (g⁻¹ * t * g) * g⁻¹ = t by group,
      Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hgc).symm
  have hg6' : InducesTypeSome (CFSG.conjugate L g)
      ((g⁻¹)⁻¹ * (g⁻¹ * t * g) * g⁻¹) 7 1 6 1 := by
    rw [show (g⁻¹)⁻¹ * (g⁻¹ * t * g) * g⁻¹ = t by group]
    exact hB
  have hkey := (sec4FCl_claims_B_C1 (g := g⁻¹) h36 h43 hf43c (hctx.conjugate g) hgc'
    hg6').2
  have hconj : CFSG.conjugate (CFSG.conjugate L g) g⁻¹ = L := by
    rw [sec4F_conjugate_conjugate, mul_inv_cancel, conjugate_one_eq]
  rw [show (g⁻¹)⁻¹ * (g⁻¹ * t * g) * g⁻¹ = t by group, hconj] at hkey
  rw [show CFSG.conjugate L g ⊓ L = L ⊓ CFSG.conjugate L g from inf_comm _ _] at hkey
  exact hkey

end CFSG.OddStandard.SmallF3.Omega
