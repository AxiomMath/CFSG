module

public import CFSG.GH74.GLS.Stage2.Local.P34Bar
public import CFSG.GH74.GLS.Stage2.Local.Basic
public import CFSG.GH74.GLS.Stage2.Local.Concl

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

omit [Finite G] in
theorem z_mem_of_cen_le {H : Subgroup G} (hCH : Cen z ≤ H) : z ∈ H :=
  hCH (Subgroup.mem_centralizer_singleton_iff.mpr rfl)

theorem centralizer_le_of_all_conj (hctx : Stage2Ctx G z k S) {H : Subgroup G} (hCH : Cen z ≤ H)
    (hall : ∀ x y : HBar H, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    {t : G} (htH : t ∈ H) (ht : orderOf t = 2) : centralizer ({t} : Set G) ≤ H := by
  have hzH : z ∈ H := z_mem_of_cen_le hCH
  have hz := hctx.orderOf_z
  have hord : ∀ {w : G} (hw : w ∈ H), orderOf w = 2 → orderOf (⟨w, hw⟩ : ↥H) = 2 := by
    intro w hw h
    rw [← h]
    exact (Subgroup.orderOf_coe (⟨w, hw⟩ : ↥H)).symm
  have h1 : IsConj (⟨t, htH⟩ : ↥H) ⟨z, hzH⟩ := by
    refine isConj_of_mk_isConj H (hord htH ht) (hord hzH hz) (hall _ _ ?_ ?_)
    · exact orderOf_mk_eq_two H (hord htH ht)
    · exact orderOf_mk_eq_two H (hord hzH hz)
  obtain ⟨c, hc⟩ := isConj_iff.1 h1
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have hct : (c : G) * t * (c : G)⁻¹ = z := congrArg Subtype.val hc
  have hcg : (c : G) * g * (c : G)⁻¹ ∈ Cen z := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hct]
    calc (c : G) * g * (c : G)⁻¹ * ((c : G) * t * (c : G)⁻¹) = (c : G) * (g * t) * (c : G)⁻¹ := by group
      _ = (c : G) * (t * g) * (c : G)⁻¹ := by rw [hg]
      _ = (c : G) * t * (c : G)⁻¹ * ((c : G) * g * (c : G)⁻¹) := by group
  have hcgH : (c : G) * g * (c : G)⁻¹ ∈ H := hCH hcg
  have hg' : g = (c : G)⁻¹ * ((c : G) * g * (c : G)⁻¹) * (c : G) := by group
  rw [hg']
  exact H.mul_mem (H.mul_mem (H.inv_mem c.2) hcgH) c.2

theorem hasTwoInvolutionClasses (hctx : Stage2Ctx G z k S) {H : Subgroup G} (hH : H ≠ ⊤)
    (hCH : Cen z ≤ H) : HasTwoInvolutionClasses (HBar H) := by
  by_contra hno
  have hall : ∀ x y : HBar H, orderOf x = 2 → orderOf y = 2 → IsConj x y := by
    intro x y hx hy
    by_contra hxy
    exact hno ⟨x, y, hx, hy, hxy⟩
  have hzH : z ∈ H := z_mem_of_cen_le hCH
  exact not_exists_stronglyEmbedded hctx.std
    (exists_stronglyEmbedded_of_closed hctx.std.kps.1 hH hctx.orderOf_z hzH
      (fun t htH ht => centralizer_le_of_all_conj hctx hCH hall htH ht))

end CFSG.GH74.GLS.Stage2.Local.P34
