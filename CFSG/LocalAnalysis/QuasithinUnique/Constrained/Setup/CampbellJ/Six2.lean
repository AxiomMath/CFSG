module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Defs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.JBasic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.ThmB
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Six1
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellDihedral

public section

namespace CFSG.QuasithinUnique.Setup.CampbellJ

open CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

private theorem inf_centralizer_Hone_le_center_Six2 (h : IsSeed S ρ (Ecore G) ψ) :
    Vmod G ⊓ Subgroup.centralizer (Hone S : Set G) ≤ Subgroup.center G := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Hone S ⊔ CFSG.pCore 2 G := by rw [h.Hone_sup_core]; trivial
  obtain ⟨j, hj, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  have h1 : j * z = z * j := Subgroup.mem_centralizer_iff.mp hz.2 j hj
  have h2 : q * z = z * q := Ecore_commute_core hq (Vmod_le_Ecore hz.1)
  calc j * q * z = j * (q * z) := by group
    _ = j * (z * q) := by rw [h2]
    _ = (j * z) * q := by group
    _ = (z * j) * q := by rw [h1]
    _ = z * (j * q) := by group

private theorem aimg_Fcore_le_WJ_Six2 (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) :
    aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≤ WJ S α := by
  intro x hx
  unfold WJ
  exact Subgroup.mem_iSup_of_mem (1 : G)
    (Subgroup.mem_iSup_of_mem (one_mem (Hone S)) (by rwa [cj_one]))

private theorem WJ_subgroupOf_normal_Six2 (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G) :
    ((WJ S α).subgroupOf (CFSG.Quasithin.thompsonJ (S : Subgroup G))).Normal := by
  refine ⟨fun w hw t => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hw ⊢
  have ht : (t : G) ∈ Hone S := Subgroup.le_normalClosure t.2
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
    (WJ_facts h α hV hF).2.1 (t : G) ht (w : G) hw

private theorem sq_mem_of_mem_aimg_symm_WJ_Six2 (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G) :
    ∀ w ∈ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (WJ S α),
      w ^ 2 ∈ Zfix S := by
  intro w hw
  obtain ⟨y, hy, rfl⟩ := mem_aimg.mp hw
  have h2 : ((y ^ 2 : ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) ∈
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) := by
    simpa using (WJ_facts h α hV hF).2.2.2 y hy
  obtain ⟨z₁, hz₁, hz₁y⟩ := mem_aimg.mp h2
  have h4 : α z₁ = y ^ 2 := Subtype.ext hz₁y
  have h5 : α.symm (y ^ 2) = z₁ := by rw [← h4, α.symm_apply_apply]
  have h6 : ((α.symm y : ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) ^ 2 =
      ((α.symm (y ^ 2) : ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) := by
    rw [map_pow]; rfl
  rw [h6, h5]
  exact hz₁

section Aux

variable (h : IsSeed S ρ (Ecore G) ψ)
  (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
  (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G)
  (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G)
include h α hV hF

private theorem dihedral_vsq_Six2 {u v : G}
    {y₁ : ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))}
    (hy₁ : (y₁ : G) ∈ cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) u)
    (hv₁ : ((α.symm y₁ : ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) = v) :
    v * v = 1 := by
  have hel : CFSG.Open.IsElemAbelian 2
      (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) u) :=
    isElemAbelian_cj (isElemAbelian_aimg α isElemAbelian_Vmod) u
  have hy₁2 : (y₁ : G) ^ 2 = 1 := (isElemAbelian_iff.mp hel).2 y₁ hy₁
  rw [← hv₁]
  have h1 : y₁ * y₁ = 1 := Subtype.ext (by simpa [pow_two] using hy₁2)
  have h' : α.symm y₁ * α.symm y₁ = 1 := by rw [← map_mul, h1, map_one]
  exact congrArg Subtype.val h'

private theorem dihedral_yW_Six2 {v hh : G}
    (hvT : v ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G)) (hv2 : v * v = 1)
    (hhW : hh ∈ WJ S α) : v * hh * v * hh ∈ WJ S α := by
  have hWhH : ∀ u ∈ Hone S, ∀ w ∈ WJ S α, u * w * u⁻¹ ∈ WJ S α :=
    (WJ_facts h α hV hF).2.1
  have hvH : v ∈ Hone S := Subgroup.le_normalClosure hvT
  have h1 := hWhH v hvH hh hhW
  rw [inv_eq_of_mul_eq_one_right hv2] at h1
  exact (WJ S α).mul_mem h1 hhW

private theorem dihedral_yW'_Six2 {u v hh : G} (hu : u ∈ Hone S)
    {y₁ : ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))}
    (hy₁ : (y₁ : G) ∈ cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) u)
    (hv₁ : ((α.symm y₁ : ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) = v)
    (hhW : hh ∈ WJ S α) (hh2 : hh ^ 2 = 1) :
    v * hh * v * hh ∈
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (WJ S α) := by
  have hWfacts := WJ_facts h α hV hF
  have hWhH : ∀ u ∈ Hone S, ∀ w ∈ WJ S α, u * w * u⁻¹ ∈ WJ S α := hWfacts.2.1
  have hWleT : WJ S α ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G) :=
    hWfacts.1.trans h.thompsonJ_core_le_thompsonJ_sylow
  have hFaW : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≤ WJ S α :=
    aimg_Fcore_le_WJ_Six2 h α
  have hVaFa : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) :=
    aimg_mono (Vmod_le_Ecore.trans h.Ecore_le_Fcore)
  have hvT : v ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G) := by
    rw [← hv₁]; exact (α.symm y₁).2
  have hy₁W : (y₁ : G) ∈ WJ S α := by
    have h1 : u * (y₁ : G) * u⁻¹ ∈
        aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) := mem_cj.mp hy₁
    have h2 : u * (y₁ : G) * u⁻¹ ∈ WJ S α := hFaW (hVaFa h1)
    have h3 := hWhH u⁻¹ ((Hone S).inv_mem hu) (u * (y₁ : G) * u⁻¹) h2
    have h4 : u⁻¹ * (u * (y₁ : G) * u⁻¹) * (u⁻¹)⁻¹ = (y₁ : G) := by group
    rwa [h4] at h3
  have hvW' : v ∈ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (WJ S α) :=
    mem_aimg.mpr ⟨y₁, hy₁W, hv₁⟩
  have hhT : hh ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G) := hWleT hhW
  have hn0 : ((WJ S α).subgroupOf (CFSG.Quasithin.thompsonJ (S : Subgroup G))).Normal :=
    WJ_subgroupOf_normal_Six2 h α hV hF
  have hn1 : ((aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
      (WJ S α)).subgroupOf (CFSG.Quasithin.thompsonJ (S : Subgroup G))).Normal :=
    normal_subgroupOf_aimg (α := α.symm) hWleT hn0
  have h1 := mem_conj_of_normal_subgroupOf hn1 hhT hvW' hvT
  rw [inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hh2)] at h1
  have h2 : v * hh * v * hh = v * (hh * v * hh) := by simp only [mul_assoc]
  rw [h2]
  exact Subgroup.mul_mem _ hvW' h1

private theorem dihedral_z0a_Six2 {v hh : G} (hyW : v * hh * v * hh ∈ WJ S α) :
    (v * hh * v * hh) * (v * hh * v * hh) ∈
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) := by
  have := (WJ_facts h α hV hF).2.2.2 (v * hh * v * hh) hyW
  rwa [pow_two] at this

private theorem dihedral_z0Z_Six2 {v hh : G}
    (hyW' : v * hh * v * hh ∈
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (WJ S α)) :
    (v * hh * v * hh) * (v * hh * v * hh) ∈ Zfix S := by
  have := sq_mem_of_mem_aimg_symm_WJ_Six2 h α hV hF (v * hh * v * hh) hyW'
  rwa [pow_two] at this

private theorem dihedral_z0c_Six2 {u v hh : G} (hu : u ∈ Hone S)
    (hz0a : (v * hh * v * hh) * (v * hh * v * hh) ∈
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S))
    (hz0Z : (v * hh * v * hh) * (v * hh * v * hh) ∈ Zfix S) :
    (v * hh * v * hh) * (v * hh * v * hh) ∈ Subgroup.center G := by
  have hcent : (v * hh * v * hh) * (v * hh * v * hh) ∈
      Subgroup.centralizer (Hone S : Set G) := (aimgJ_Zfix_le_center_Hone h α hV hF hz0a).2
  exact inf_centralizer_Hone_le_center_Six2 h ⟨IsSeed.Zfix_le_Vmod hz0Z, hcent⟩

private theorem dihedral_z0ne_Six2 {v hh : G}
    (hne : ¬ hh * (v⁻¹ * hh * v) = (v⁻¹ * hh * v) * hh)
    (hv2 : v * v = 1) (hh2 : hh ^ 2 = 1) :
    (v * hh * v * hh) * (v * hh * v * hh) ≠ 1 := by
  intro h1
  apply hne
  have e := dihedral_commutator hv2 (by rw [← pow_two]; exact hh2)
  rw [h1, inv_one] at e
  calc hh * (v⁻¹ * hh * v)
      = (hh * (v⁻¹ * hh * v) * hh⁻¹ * (v⁻¹ * hh * v)⁻¹) *
          ((v⁻¹ * hh * v) * hh) := by group
    _ = (v⁻¹ * hh * v) * hh := by rw [e, one_mul]

private theorem dihedral_theta_prep_Six2 {u v hh : G} (hu : u ∈ Hone S)
    {y₁ : ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))}
    (hy₁ : (y₁ : G) ∈ cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) u)
    (hv₁ : ((α.symm y₁ : ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) = v)
    (hv2 : v * v = 1) (hh2 : hh ^ 2 = 1)
    (hyW' : v * hh * v * hh ∈
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (WJ S α))
    (hz0Z : (v * hh * v * hh) * (v * hh * v * hh) ∈ Zfix S)
    (hyT : v * hh * v * hh ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G))
    (hz0T : (v * hh * v * hh) * (v * hh * v * hh) ∈
      CFSG.Quasithin.thompsonJ (S : Subgroup G)) :
    ((⟨v * hh * v * hh, hyT⟩ : ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) * α.symm y₁ *
        ((⟨v * hh * v * hh, hyT⟩ :
          ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))))⁻¹ * (α.symm y₁)⁻¹ =
        ⟨(v * hh * v * hh) * (v * hh * v * hh), hz0T⟩) ∧
    ((α (α.symm y₁) : ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) ∈
      cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) u ∧
    ((α ⟨(v * hh * v * hh) * (v * hh * v * hh), hz0T⟩ :
        ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) ∈
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) ∧
    ((α ⟨v * hh * v * hh, hyT⟩ :
        ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) ∈ WJ S α := by
  have hh2' : hh * hh = 1 := by rw [← pow_two]; exact hh2
  have hcommyv := dihedral_identities hv2 hh2'
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hv₁]
    exact hcommyv
  · rw [α.apply_symm_apply]; exact hy₁
  · exact mem_aimg_of_mem (y := ⟨(v * hh * v * hh) * (v * hh * v * hh), hz0T⟩) hz0Z
  · obtain ⟨y₂, hy₂, hy₂e⟩ := mem_aimg.mp hyW'
    have hy2 : (⟨v * hh * v * hh, hyT⟩ :
        ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) = α.symm y₂ :=
      Subtype.ext hy₂e.symm
    rw [hy2, α.apply_symm_apply]
    exact hy₂

private theorem dihedral_hc_Six2 {u v hh : G} (hu : u ∈ Hone S)
    (hz0T : (v * hh * v * hh) * (v * hh * v * hh) ∈
      CFSG.Quasithin.thompsonJ (S : Subgroup G))
    (hcZ : ((α ⟨(v * hh * v * hh) * (v * hh * v * hh), hz0T⟩ :
        ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) ∈
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S)) :
    (u⁻¹)⁻¹ * ((α ⟨(v * hh * v * hh) * (v * hh * v * hh), hz0T⟩ :
        ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) * u⁻¹ =
      ((α ⟨(v * hh * v * hh) * (v * hh * v * hh), hz0T⟩ :
        ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) := by
  have hcomm : u * ((α ⟨(v * hh * v * hh) * (v * hh * v * hh), hz0T⟩ :
        ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) =
      ((α ⟨(v * hh * v * hh) * (v * hh * v * hh), hz0T⟩ :
        ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) * u :=
    Subgroup.mem_centralizer_iff.mp (aimgJ_Zfix_le_center_Hone h α hV hF hcZ).2 u hu
  have hz : u * ((α ⟨(v * hh * v * hh) * (v * hh * v * hh), hz0T⟩ :
        ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) * u⁻¹ =
      ((α ⟨(v * hh * v * hh) * (v * hh * v * hh), hz0T⟩ :
        ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) := by
    rw [hcomm]; group
  simpa using hz

private theorem dihedral_theta_Six2 {u v hh : G} (hu : u ∈ Hone S)
    {y₁ : ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))}
    (hyT : v * hh * v * hh ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G))
    (hz0T : (v * hh * v * hh) * (v * hh * v * hh) ∈
      CFSG.Quasithin.thompsonJ (S : Subgroup G))
    (hrel : (⟨v * hh * v * hh, hyT⟩ : ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) *
        α.symm y₁ * ((⟨v * hh * v * hh, hyT⟩ :
          ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))))⁻¹ * (α.symm y₁)⁻¹ =
        ⟨(v * hh * v * hh) * (v * hh * v * hh), hz0T⟩)
    (hbV : ((α (α.symm y₁) : ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) ∈
      cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) u)
    (hcZ : ((α ⟨(v * hh * v * hh) * (v * hh * v * hh), hz0T⟩ :
        ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) ∈
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S))
    (haW : ((α ⟨v * hh * v * hh, hyT⟩ :
        ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) ∈ WJ S α) :
    ∃ s v' : G, s ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G) ∧ v' ∈ Vmod G ∧
      s * v' * s⁻¹ * v'⁻¹ = (v * hh * v * hh) * (v * hh * v * hh) := by
  have hWfacts := WJ_facts h α hV hF
  have hWhH : ∀ u ∈ Hone S, ∀ w ∈ WJ S α, u * w * u⁻¹ ∈ WJ S α := hWfacts.2.1
  have hWleT : WJ S α ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G) :=
    hWfacts.1.trans h.thompsonJ_core_le_thompsonJ_sylow
  have ha'' : (u⁻¹)⁻¹ * ((α ⟨v * hh * v * hh, hyT⟩ :
        ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) * u⁻¹ ∈
      CFSG.Quasithin.thompsonJ (S : Subgroup G) := by
    have h1 := hWhH u hu _ haW
    simpa using hWleT h1
  have hb'' : (u⁻¹)⁻¹ * ((α (α.symm y₁) :
        ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) * u⁻¹ ∈
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) := by
    have h1 := mem_cj.mp hbV
    simpa using h1
  have hb'T : (u⁻¹)⁻¹ * ((α (α.symm y₁) :
        ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) * u⁻¹ ∈
      CFSG.Quasithin.thompsonJ (S : Subgroup G) := aimg_le hb''
  have hc' := dihedral_hc_Six2 h α hV hF hu hz0T hcZ
  have hθ := theta_transport (S₀ := CFSG.Quasithin.thompsonJ (S : Subgroup G))
    α u⁻¹ hrel ha'' hb'T hc'
  have hv''V : ((α.symm ⟨(u⁻¹)⁻¹ * ((α (α.symm y₁) :
        ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) * u⁻¹, hb'T⟩ :
        ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) ∈ Vmod G :=
    (mem_aimg_symm_iff hb'T).mp hb''
  have hcen := congrArg Subtype.val hθ
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hcen
  exact ⟨_, _, (α.symm ⟨(u⁻¹)⁻¹ * ((α ⟨v * hh * v * hh, hyT⟩ :
      ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) * u⁻¹, ha''⟩).2, hv''V, hcen⟩

private theorem dihedral_final_Six2 {s v' z : G} (hs : s ∈ (S : Subgroup G))
    (hv : v' ∈ Vmod G) (hz : z ∈ Subgroup.center G)
    (hsv : s * v' * s⁻¹ * v'⁻¹ = z) (hz1 : z ≠ 1) : False := by
  have h1 := h.commutator_eq_one_of_central hs hv (by rw [hsv]; exact hz)
  rw [hsv] at h1
  exact hz1 h1

end Aux

theorem dihedral_commuteJ (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G)
    {u : G} (hu : u ∈ Hone S) {v : G}
    (hv : v ∈ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
      (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) u))
    {hh : G} (hhW : hh ∈ WJ S α) (hh2 : hh ^ 2 = 1) :
    hh * (v⁻¹ * hh * v) = (v⁻¹ * hh * v) * hh := by
  by_contra hne
  obtain ⟨y₁, hy₁, hv₁⟩ := mem_aimg.mp hv
  have hvT : v ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G) := aimg_le hv
  have hv2 : v * v = 1 := dihedral_vsq_Six2 h α hV hF hy₁ hv₁
  have hyW : v * hh * v * hh ∈ WJ S α := dihedral_yW_Six2 h α hV hF hvT hv2 hhW
  have hyW' : v * hh * v * hh ∈
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (WJ S α) :=
    dihedral_yW'_Six2 h α hV hF hu hy₁ hv₁ hhW hh2
  have hz0a : (v * hh * v * hh) * (v * hh * v * hh) ∈
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) :=
    dihedral_z0a_Six2 h α hV hF hyW
  have hz0Z : (v * hh * v * hh) * (v * hh * v * hh) ∈ Zfix S :=
    dihedral_z0Z_Six2 h α hV hF hyW'
  have hz0c : (v * hh * v * hh) * (v * hh * v * hh) ∈ Subgroup.center G :=
    dihedral_z0c_Six2 h α hV hF hu hz0a hz0Z
  have hz0ne : (v * hh * v * hh) * (v * hh * v * hh) ≠ 1 :=
    dihedral_z0ne_Six2 h α hV hF hne hv2 hh2
  have hWleT : WJ S α ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G) :=
    (WJ_facts h α hV hF).1.trans h.thompsonJ_core_le_thompsonJ_sylow
  have hyT : v * hh * v * hh ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G) := hWleT hyW
  have hz0T : (v * hh * v * hh) * (v * hh * v * hh) ∈
      CFSG.Quasithin.thompsonJ (S : Subgroup G) := Zfix_le_JS h hz0Z
  obtain ⟨hrel, hbV, hcZ, haW⟩ :=
    dihedral_theta_prep_Six2 h α hV hF hu hy₁ hv₁ hv2 hh2 hyW' hz0Z hyT hz0T
  obtain ⟨s, v', hsT, hv'V, hsv⟩ :=
    dihedral_theta_Six2 h α hV hF hu hyT hz0T hrel hbV hcZ haW
  exact dihedral_final_Six2 h α hV hF (thompsonJ_le_self' (S : Subgroup G) hsT)
    hv'V hz0c hsv hz0ne

end CFSG.QuasithinUnique.Setup.CampbellJ

end
