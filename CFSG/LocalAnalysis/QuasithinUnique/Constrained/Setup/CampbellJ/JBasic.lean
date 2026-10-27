module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellStruct2
import CFSG.Quasithin.Background.SimsD1Two

public section

namespace CFSG.QuasithinUnique.Setup.CampbellJ

open CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k]
  {S : Sylow 2 G} {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k}
  {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

private theorem aimg_normal_of_normal {S₀ Y : Subgroup G} [Y.Normal]
    (α : S₀ ≃* S₀) {s x : G} (hs : s ∈ S₀) (hx : x ∈ aimg S₀ α Y) :
    s * x * s⁻¹ ∈ aimg S₀ α Y := by
  obtain ⟨y, hy, hyx⟩ := mem_aimg.mp hx
  refine mem_aimg.mpr ⟨α.symm ⟨s, hs⟩ * y * (α.symm ⟨s, hs⟩)⁻¹, ?_, ?_⟩
  · have hconj := (inferInstance : Y.Normal).conj_mem (y : G) hy ((α.symm ⟨s, hs⟩ : S₀) : G)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hconj
  · have h1 : α (α.symm ⟨s, hs⟩ * y * (α.symm ⟨s, hs⟩)⁻¹) =
        ⟨s, hs⟩ * α y * ⟨s, hs⟩⁻¹ := by
      rw [map_mul, map_mul, map_inv, α.apply_symm_apply]
    rw [h1]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hyx]

theorem isMaxElemAbelian_JS_iff (A : Subgroup G) :
    CFSG.Quasithin.IsMaxElemAbelian (CFSG.Quasithin.thompsonJ (S : Subgroup G)) A ↔
      CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G) A :=
  CFSG.Quasithin.SimsD1.isMaxElemAbelian_iff_of_thompsonJ_le
    (S := (S : Subgroup G)) (R := CFSG.Quasithin.thompsonJ (S : Subgroup G))
    le_rfl (thompsonJ_le_self' _) A

theorem Fcore_le_JS (h : IsSeed S ρ (Ecore G) ψ) :
    Fcore G ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G) :=
  Fcore_le_thompsonJ.trans h.thompsonJ_core_le_thompsonJ_sylow

theorem Vmod_le_JS (h : IsSeed S ρ (Ecore G) ψ) :
    Vmod G ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G) :=
  (Vmod_le_Ecore.trans h.Ecore_le_Fcore).trans (Fcore_le_JS h)

theorem Zfix_le_JS (h : IsSeed S ρ (Ecore G) ψ) :
    Zfix S ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G) :=
  IsSeed.Zfix_le_Vmod.trans (Vmod_le_JS h)

theorem JS_map_eq (h : IsSeed S ρ (Ecore G) ψ) :
    (CFSG.Quasithin.thompsonJ (S : Subgroup G)).map ρ = (S : Subgroup G).map ρ := by
  obtain ⟨A, hA, hAQ⟩ := h.exists_max_outside
  refine le_antisymm (Subgroup.map_mono (thompsonJ_le_self' _)) ?_
  rw [← (h.max_outside hA hAQ).1]
  exact Subgroup.map_mono (maxElem_le_thompsonJ hA)

theorem aimgJ_Fcore_normal (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) {s x : G}
    (hs : s ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G))
    (hx : x ∈ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) :
    s * x * s⁻¹ ∈ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) :=
  aimg_normal_of_normal (S₀ := CFSG.Quasithin.thompsonJ (S : Subgroup G)) (Y := Fcore G) α hs hx

theorem aimgJ_Zfix_central
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) {s z : G}
    (hs : s ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G))
    (hz : z ∈ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S)) : s * z = z * s := by
  obtain ⟨y, hy, hyx⟩ := mem_aimg.mp hz
  have h1 : ((α.symm ⟨s, hs⟩ : ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) * (y : G) =
      (y : G) * ((α.symm ⟨s, hs⟩ : ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) :=
    IsSeed.Zfix_central hy (thompsonJ_le_self' _ (α.symm ⟨s, hs⟩).2)
  have h2 : α.symm ⟨s, hs⟩ * y = y * α.symm ⟨s, hs⟩ := Subtype.ext h1
  have h3 : α (α.symm ⟨s, hs⟩) * α y = α y * α (α.symm ⟨s, hs⟩) := by
    rw [← map_mul, ← map_mul, h2]
  rw [α.apply_symm_apply] at h3
  rw [← hyx]
  exact congrArg Subtype.val h3

theorem mem_Fcore_of_JS_central_involution (h : IsSeed S ρ (Ecore G) ψ) {s : G}
    (hs : s ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G))
    (hc : ∀ t ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G), s * t = t * s) (hs2 : s ^ 2 = 1) :
    s ∈ Fcore G := by
  have key : ∀ A : Subgroup G, CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G) A → s ∈ A := by
    intro A hA
    have hAS : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G) A := h.max_core_facts.1 A hA
    exact maxElem_mem_of_centralizer hAS (thompsonJ_le_self' _ hs)
      (Subgroup.mem_centralizer_iff.mpr fun a ha => (hc a (maxElem_le_thompsonJ hAS ha)).symm) hs2
  refine mem_Fcore_iff.mpr ⟨?_, key⟩
  obtain ⟨A₀, hA₀⟩ := exists_maxElem (CFSG.pCore 2 G)
  exact hA₀.1 (key A₀ hA₀)

end CFSG.QuasithinUnique.Setup.CampbellJ

end
