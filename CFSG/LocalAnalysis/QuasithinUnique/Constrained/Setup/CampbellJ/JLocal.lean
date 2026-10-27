module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Defs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.JBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion

public section

namespace CFSG.QuasithinUnique.Setup.CampbellJ

open CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

section Transfer

theorem adm_thompsonJ_iff {Y : Subgroup G} :
    Adm (CFSG.Quasithin.thompsonJ (S : Subgroup G)) Y ↔ Adm (S : Subgroup G) Y := by
  constructor <;> intro h
  · obtain ⟨A, hA, hYA⟩ := h
    exact ⟨A, (isMaxElemAbelian_JS_iff (S := S) A).mp hA, hYA⟩
  · obtain ⟨A, hA, hYA⟩ := h
    exact ⟨A, (isMaxElemAbelian_JS_iff (S := S) A).mpr hA, hYA⟩

theorem isMaxElemAbelian_cj_thompsonJ_iff (g : G) {A : Subgroup G} :
    CFSG.Quasithin.IsMaxElemAbelian (cj (CFSG.Quasithin.thompsonJ (S : Subgroup G)) g) A ↔
      CFSG.Quasithin.IsMaxElemAbelian (cj (S : Subgroup G) g) A := by
  constructor
  · intro hA
    have h1 := isMaxElemAbelian_cj g⁻¹ hA
    rw [cj_inv_cj] at h1
    have h2 := (isMaxElemAbelian_JS_iff (S := S) (cj A g⁻¹)).mp h1
    have h3 := isMaxElemAbelian_cj g h2
    rwa [cj_cj_inv] at h3
  · intro hA
    have h1 := isMaxElemAbelian_cj g⁻¹ hA
    rw [cj_inv_cj] at h1
    have h2 := (isMaxElemAbelian_JS_iff (S := S) (cj A g⁻¹)).mpr h1
    have h3 := isMaxElemAbelian_cj g h2
    rwa [cj_cj_inv] at h3

theorem adm_cj_thompsonJ_iff (g : G) {Y : Subgroup G} :
    Adm (cj (CFSG.Quasithin.thompsonJ (S : Subgroup G)) g) Y ↔ Adm (cj (S : Subgroup G) g) Y := by
  constructor <;> intro h
  · obtain ⟨A, hA, hYA⟩ := h
    exact ⟨A, (isMaxElemAbelian_cj_thompsonJ_iff (S := S) g (A := A)).mp hA, hYA⟩
  · obtain ⟨A, hA, hYA⟩ := h
    exact ⟨A, (isMaxElemAbelian_cj_thompsonJ_iff (S := S) g (A := A)).mpr hA, hYA⟩

end Transfer

namespace PartnerCoreJ

variable {P Fp Zp : Subgroup G}

theorem adm (hp : PartnerCoreJ P Fp Zp) : Adm P Fp := by
  obtain ⟨A, hA⟩ := exists_maxElem P
  exact ⟨_, hp.sup_max A hA, le_sup_left⟩

theorem isElemAbelian_fp (hp : PartnerCoreJ P Fp Zp) : CFSG.Open.IsElemAbelian 2 Fp :=
  hp.adm.isElemAbelian

theorem zp_le_fp (hp : PartnerCoreJ P Fp Zp) : Zp ≤ Fp := by
  rw [← hp.commJ, Subgroup.commutator_le]
  intro j hj f hf
  have h1 := hp.normal j hj f hf
  rw [commutatorElement_def]
  exact mul_mem h1 (inv_mem hf)

theorem fp_le_thompsonJ (hp : PartnerCoreJ P Fp Zp) : Fp ≤ CFSG.Quasithin.thompsonJ P := by
  obtain ⟨A, hA, hFA⟩ := hp.adm
  exact hFA.trans (maxElem_le_thompsonJ hA)

theorem zp_le_thompsonJ (hp : PartnerCoreJ P Fp Zp) : Zp ≤ CFSG.Quasithin.thompsonJ P := by
  rw [← hp.commJ, Subgroup.commutator_le]
  intro j hj f hf
  have hfJ : f ∈ CFSG.Quasithin.thompsonJ P := hp.fp_le_thompsonJ hf
  rw [commutatorElement_def]
  exact mul_mem (hp.fp_le_thompsonJ (hp.normal j hj f hf)) (inv_mem hfJ)

theorem isElemAbelian_zp (hp : PartnerCoreJ P Fp Zp) : CFSG.Open.IsElemAbelian 2 Zp :=
  isElemAbelian_mono hp.isElemAbelian_fp hp.zp_le_fp

theorem commA_le (hp : PartnerCoreJ P Fp Zp) {A : Subgroup G}
    (hA : CFSG.Quasithin.IsMaxElemAbelian P A) : ⁅A, Fp⁆ ≤ Zp := by
  rcases hp.commA A hA with h | h
  · rw [h]; exact bot_le
  · exact h.le

theorem sup_max_cj (hp : PartnerCoreJ P Fp Zp) (g : G) {A' : Subgroup G}
    (hA' : CFSG.Quasithin.IsMaxElemAbelian (cj P g) A') :
    CFSG.Quasithin.IsMaxElemAbelian (cj P g)
      (cj Fp g ⊔ (A' ⊓ Subgroup.centralizer ((cj Fp g : Subgroup G) : Set G))) := by
  have hA : CFSG.Quasithin.IsMaxElemAbelian P (cj A' g⁻¹) := by
    have := isMaxElemAbelian_cj g⁻¹ hA'
    rwa [cj_inv_cj] at this
  have h1 := isMaxElemAbelian_cj g (hp.sup_max _ hA)
  rw [cj_sup, cj_inf, ← centralizer_cj, cj_cj_inv] at h1
  exact h1

theorem commA_cj (hp : PartnerCoreJ P Fp Zp) (g : G) {A' : Subgroup G}
    (hA' : CFSG.Quasithin.IsMaxElemAbelian (cj P g) A') :
    ⁅A', cj Fp g⁆ = ⊥ ∨ ⁅A', cj Fp g⁆ = cj Zp g := by
  have hA : CFSG.Quasithin.IsMaxElemAbelian P (cj A' g⁻¹) := by
    have := isMaxElemAbelian_cj g⁻¹ hA'
    rwa [cj_inv_cj] at this
  have h2 : cj ⁅cj A' g⁻¹, Fp⁆ g = ⁅A', cj Fp g⁆ := by
    rw [cj_commutator, cj_cj_inv]
  rcases hp.commA _ hA with h1 | h1
  · left; rw [← h2, h1, cj_bot]
  · right; rw [← h2, h1]

theorem zp_le_Fcore (h : IsSeed S ρ (Ecore G) ψ) (hp : PartnerCoreJ (S : Subgroup G) Fp Zp) :
    Zp ≤ Fcore G := fun z hz =>
  mem_Fcore_of_JS_central_involution h (hp.zp_le_thompsonJ hz)
    (fun t ht => (hp.zcentral t ht z hz).symm)
    ((isElemAbelian_iff.mp hp.isElemAbelian_zp).2 z hz)

theorem fp_le_thompsonJ_core (h : IsSeed S ρ (Ecore G) ψ)
    (hp : PartnerCoreJ (S : Subgroup G) Fp Zp) (hFQ : Fp ≤ CFSG.pCore 2 G) :
    Fp ≤ CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) := by
  obtain ⟨A, hA, hle⟩ := h.adm_core_of_adm hp.adm hFQ
  exact hle.trans (maxElem_le_thompsonJ hA)

end PartnerCoreJ

end CFSG.QuasithinUnique.Setup.CampbellJ

end
