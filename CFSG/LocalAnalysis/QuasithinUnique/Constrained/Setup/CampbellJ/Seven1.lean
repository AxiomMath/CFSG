module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Defs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.JLocalAimg
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.ThmB52
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellDouble

public section

namespace CFSG.QuasithinUnique.Setup.CampbellJ

open CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}
  {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))}
  {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} {A : Subgroup G} {g : G}

private theorem B0J_eq_BoneP_Seven1 (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G)
    {A : Subgroup G} (hA : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G) A) :
    B0J S α A = CFSG.Quasithin.BoneP
      (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) A := by
  have hFaJ := aimgJ_Fcore_le_thompsonJ_core h α hV
  have hFFa : ∀ x ∈ Fcore G,
      ∀ w ∈ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G), x * w = w * x :=
    fun x hx w hw => (Fcore_commute_thompsonJ_core hx (hFaJ hw)).symm
  apply le_antisymm
  · refine sup_le (sup_le (PartnerCoreJ.Fcore_le_BoneP h (partnerCoreJ_aimg h α)
      (aimgJ_Fcore_le_core h α hV) A) le_sup_left) ?_
    rintro x ⟨hxA, hxc⟩
    have hxF : x ∈ A ⊓ Subgroup.centralizer (Fcore G : Set G) :=
      ⟨hxA, Subgroup.mem_centralizer_iff.mpr fun f hf =>
        Subgroup.mem_centralizer_iff.mp hxc f (Subgroup.mem_sup_left hf)⟩
    rw [h.inf_centralizer_Fcore hA] at hxF
    apply Subgroup.mem_sup_right
    refine ⟨Subgroup.mem_sup_left hxF, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    exact Subgroup.mem_centralizer_iff.mp hxc w (Subgroup.mem_sup_right hw)
  · have hle1 : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≤
        Fcore G ⊔ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) := le_sup_right
    refine sup_le (hle1.trans le_sup_left) (fun u hu => ?_)
    obtain ⟨huB, huc⟩ := hu
    have hFB0 : Fcore G ≤ B0J S α A := le_sup_left.trans le_sup_left
    have hcommAF : ∀ x ∈ A ⊓ CFSG.pCore 2 G, ∀ y ∈ Fcore G, x * y = y * x := by
      intro x hx y hy
      have : x ∈ A ⊓ Subgroup.centralizer (Fcore G : Set G) := by
        rw [h.inf_centralizer_Fcore hA]; exact hx
      exact (Subgroup.mem_centralizer_iff.mp this.2 y hy).symm
    obtain ⟨a, ha, f, hf, rfl⟩ := mem_sup_of_commute hcommAF huB
    have hac : a ∈ Subgroup.centralizer ((Fcore G ⊔
        aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) : Subgroup G) : Set G) := by
      refine mem_centralizer_sup (fun x hx => (hcommAF a ha x hx).symm) (fun w hw => ?_)
      have h1 := Subgroup.mem_centralizer_iff.mp huc w hw
      have h2 := hFFa f hf w hw
      calc w * a = w * (a * f) * f⁻¹ := by group
        _ = (a * f) * w * f⁻¹ := by rw [h1]
        _ = a * (f * w) * f⁻¹ := by group
        _ = a * (w * f) * f⁻¹ := by rw [h2]
        _ = a * w := by group
    exact mul_mem (Subgroup.mem_sup_right
      (⟨ha.1, hac⟩ : a ∈ A ⊓ Subgroup.centralizer ((Fcore G ⊔
        aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) : Subgroup G) : Set G)))
      (hFB0 hf)

theorem DoubleSetupJ.facts71 (c : DoubleSetupJ S ρ ψ Λ α A g) :
    (∀ β ∈ Λ, aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) β (Fcore G) ≤ CFSG.pCore 2 G) ∧
    CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G) (B0J S α A) ∧
    CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G) (BbJ S α A g) ∧
    ⁅A, B0J S α A⁆ ≤ Zfix S ⊔
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) := by
  have hFQ : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≤ CFSG.pCore 2 G :=
    aimgJ_Fcore_le_core c.seed α (c.lam.vmod α c.hαΛ)
  have hV' : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Vmod G) ≤
      CFSG.pCore 2 G :=
    c.lam.vmod α.symm (by rw [← MulAut.inv_def]; exact Λ.inv_mem c.hαΛ)
  have hB0Q : CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G) (B0J S α A) := by
    rw [B0J_eq_BoneP_Seven1 c.seed α (c.lam.vmod α c.hαΛ) c.hA]
    exact (PartnerCoreJ.BoneP_isMax c.seed (partnerCoreJ_aimg c.seed α) hFQ c.hA).2.2
  have hcomm : ⁅A, B0J S α A⁆ ≤ Zfix S ⊔
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) := by
    rw [B0J_eq_BoneP_Seven1 c.seed α (c.lam.vmod α c.hαΛ) c.hA]
    exact PartnerCoreJ.commutator_A_BoneP_le c.seed (partnerCoreJ_aimg c.seed α) c.hA c.hAQ
  have hA' : CFSG.Quasithin.IsMaxElemAbelian
      (cj (CFSG.Quasithin.thompsonJ (S : Subgroup G)) g) (B0J S α A) :=
    (isMaxElemAbelian_cj_thompsonJ_iff (S := S) g).mpr
      (c.seed.isMaxElemAbelian_cj_of_core hB0Q g)
  have h1 := isMaxElemAbelian_tr_Fcore_supJ c.seed α.symm g hA'
  have hBbQ : BbJ S α A g ≤ CFSG.pCore 2 G :=
    sup_le (cj_le_core (aimgJ_Fcore_le_core c.seed α.symm hV') g)
      ((inf_le_left : B0J S α A ⊓
        Subgroup.centralizer ((PminusJ S α g : Subgroup G) : Set G) ≤ B0J S α A).trans hB0Q.1)
  have hBb' : CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G) (BbJ S α A g) :=
    isMaxElemAbelian_core_of_le_cj (core_le_sylow S)
      ((isMaxElemAbelian_cj_thompsonJ_iff (S := S) g).mp h1) hBbQ
  exact ⟨fun β hβ => aimgJ_Fcore_le_core c.seed β (c.lam.vmod β hβ), hB0Q, hBb', hcomm⟩

end CFSG.QuasithinUnique.Setup.CampbellJ

end
