module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellCentrality

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2
open scoped LinearAlgebra.Projectivization

section Dihedral

variable {G : Type*} [Group G]

theorem normal_of_le_center' {N : Subgroup G} (h : N ≤ Subgroup.center G) : N.Normal :=
  ⟨fun n hn g => by
    have := Subgroup.mem_center_iff.mp (h hn) g
    have e : g * n * g⁻¹ = n := by rw [this]; group
    rw [e]; exact hn⟩

theorem cj_eq_of_le_center {N : Subgroup G} (h : N ≤ Subgroup.center G) (g : G) :
    cj N g = N := by
  have := normal_of_le_center' h
  exact cj_eq_self_of_normal

@[expose] def Wnc (S : Sylow 2 G) (α : (S : Subgroup G) ≃* (S : Subgroup G)) : Subgroup G :=
  Subgroup.normalClosure ((aimg (S : Subgroup G) α (Fcore G) : Subgroup G) : Set G)

instance Wnc_normal {S : Sylow 2 G} {α : (S : Subgroup G) ≃* (S : Subgroup G)} :
    (Wnc S α).Normal := by
  unfold Wnc; infer_instance

theorem aimg_Fcore_le_Wnc {S : Sylow 2 G} (α : (S : Subgroup G) ≃* (S : Subgroup G)) :
    aimg (S : Subgroup G) α (Fcore G) ≤ Wnc S α := Subgroup.le_normalClosure

theorem Wnc_eq_iSup {S : Sylow 2 G} (α : (S : Subgroup G) ≃* (S : Subgroup G)) :
    Wnc S α = ⨆ g : G, cj (aimg (S : Subgroup G) α (Fcore G)) g := by
  unfold Wnc; rw [iSup_cj_eq_normalClosure]


theorem dihedral_identities {v hh : G} (hv2 : v * v = 1) (hh2 : hh * hh = 1) :
    (v * hh * v * hh) * v * (v * hh * v * hh)⁻¹ * v⁻¹ = (v * hh * v * hh) * (v * hh * v * hh) := by
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hh' : hh⁻¹ = hh := inv_eq_of_mul_eq_one_right hh2
  simp only [mul_inv_rev, hv', hh', mul_assoc, hv2, mul_one]

theorem dihedral_commutator {v hh : G} (hv2 : v * v = 1) (hh2 : hh * hh = 1) :
    hh * (v⁻¹ * hh * v) * hh⁻¹ * (v⁻¹ * hh * v)⁻¹ =
      ((v * hh * v * hh) * (v * hh * v * hh))⁻¹ := by
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hh' : hh⁻¹ = hh := inv_eq_of_mul_eq_one_right hh2
  simp only [mul_inv_rev, hv', hh', mul_assoc]

theorem central_conj_eq {z : G} (hz : z ∈ Subgroup.center G) (u : G) : u⁻¹ * z * u = z := by
  have := Subgroup.mem_center_iff.mp hz u
  calc u⁻¹ * z * u = u⁻¹ * (z * u) := by group
    _ = u⁻¹ * (u * z) := by rw [this]
    _ = z := by group

theorem theta_transport {S₀ : Subgroup G} (α : S₀ ≃* S₀) (u : G) {y v z : S₀}
    (hyvz : y * v * y⁻¹ * v⁻¹ = z)
    (ha : u⁻¹ * ((α y : S₀) : G) * u ∈ S₀) (hb : u⁻¹ * ((α v : S₀) : G) * u ∈ S₀)
    (hc : u⁻¹ * ((α z : S₀) : G) * u = ((α z : S₀) : G)) :
    α.symm ⟨u⁻¹ * ((α y : S₀) : G) * u, ha⟩ * α.symm ⟨u⁻¹ * ((α v : S₀) : G) * u, hb⟩ *
      (α.symm ⟨u⁻¹ * ((α y : S₀) : G) * u, ha⟩)⁻¹ *
      (α.symm ⟨u⁻¹ * ((α v : S₀) : G) * u, hb⟩)⁻¹ = z := by
  apply α.injective
  simp only [map_mul, map_inv, α.apply_symm_apply]
  apply Subtype.ext
  have h1 := congrArg α hyvz
  simp only [map_mul, map_inv] at h1
  have h2 := congrArg Subtype.val h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
  show u⁻¹ * ((α y : S₀) : G) * u * (u⁻¹ * ((α v : S₀) : G) * u) *
      (u⁻¹ * ((α y : S₀) : G) * u)⁻¹ * (u⁻¹ * ((α v : S₀) : G) * u)⁻¹ = ((α z : S₀) : G)
  calc _ = u⁻¹ * (((α y : S₀) : G) * ((α v : S₀) : G) * ((α y : S₀) : G)⁻¹ *
        ((α v : S₀) : G)⁻¹) * u := by group
    _ = u⁻¹ * ((α z : S₀) : G) * u := by rw [h2]
    _ = ((α z : S₀) : G) := hc

section Seed

variable {k : Type*} [Field k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

namespace IsNatBase

variable [Finite G] [Finite k]

theorem commutator_eq_one_of_central (h : IsNatBase S ρ (Ecore G) ψ) {s v : G}
    (hs : s ∈ (S : Subgroup G)) (hv : v ∈ Vmod G)
    (hc : s * v * s⁻¹ * v⁻¹ ∈ Subgroup.center G) : s * v * s⁻¹ * v⁻¹ = 1 := by
  by_cases hsQ : s ∈ CFSG.pCore 2 G
  · have := Ecore_commute_core hsQ (Vmod_le_Ecore hv)
    rw [this]; group
  · obtain ⟨ℓ, hℓ⟩ := h.exists_rootGrp_eq
    set e : Ecore G := ⟨v, Vmod_le_Ecore hv⟩ with he
    set e' : Ecore G := ⟨s * v * s⁻¹, (inferInstance : (Ecore G).Normal).conj_mem v
      (Vmod_le_Ecore hv) s⟩ with he'
    have hψ1 : ψ (e' * e⁻¹) = 1 := h.ψ_eq_one_iff.mpr (by simpa [he, he'] using hc)
    have h2 : ψ e' = ψ e := by
      rw [map_mul, map_inv] at hψ1
      exact mul_inv_eq_one.mp hψ1
    have h3 := h.ψ_equiv s e e' rfl
    rw [h2] at h3
    have hfix : ρ s • Multiplicative.toAdd (ψ e) = Multiplicative.toAdd (ψ e) := by
      rw [Matrix.SpecialLinearGroup.smul_def]; exact h3.symm
    have hu : ρ s ∈ rootGrp ℓ := by rw [← hℓ]; exact ⟨s, hs, rfl⟩
    have hne := h.ne_one_of_mem_sylow_of_not_mem_core hs hsQ
    have hmem := (smul_eq_self_iff_mem_of_mem_rootGrp hu hne _).mp hfix
    have hT1 := (h.natural_module_facts hℓ).1 s hs hsQ e hv
    have : s * v * s⁻¹ = v := hT1.mpr hmem
    rw [this]; group

end IsNatBase

namespace IsSeed

variable [Finite G] [Finite k]

variable (h : IsSeed S ρ (Ecore G) ψ)
include h

theorem aimg_Zfix_le_center (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (S : Subgroup G) α (Fcore G) ≠ Fcore G) :
    aimg (S : Subgroup G) α (Zfix S) ≤ Subgroup.center G := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  have hZ := h.contained_translate_fixed_space_centrality α hV hF hz
  have hg : g ∈ Hone S ⊔ CFSG.pCore 2 G := by rw [h.Hone_sup_core]; trivial
  obtain ⟨j, hj, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  have h1 : j * z = z * j := Subgroup.mem_centralizer_iff.mp hZ.2 j hj
  have h2 : q * z = z * q := aimg_Zfix_central α (core_le_sylow S hq) hz
  calc j * q * z = j * (q * z) := by group
    _ = j * (z * q) := by rw [h2]
    _ = (j * z) * q := by group
    _ = (z * j) * q := by rw [h1]
    _ = z * (j * q) := by group

theorem Wnc_le_thompsonJ_core (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G) :
    Wnc S α ≤ thompsonJ (CFSG.pCore 2 G) :=
  Subgroup.normalClosure_le_normal fun _ hx => h.aimg_Fcore_le_thompsonJ_core α hV hx

theorem Wnc_le_sylow (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G) :
    Wnc S α ≤ (S : Subgroup G) :=
  (h.Wnc_le_thompsonJ_core α hV).trans (thompsonJ_le_self' _ |>.trans (core_le_sylow S))

theorem aimg_Zfix_le_Wnc (α : (S : Subgroup G) ≃* (S : Subgroup G)) :
    aimg (S : Subgroup G) α (Zfix S) ≤ Wnc S α :=
  (aimg_mono (h.Zfix_le_Fcore)).trans (aimg_Fcore_le_Wnc α)

theorem commutator_Fa_Wnc_le (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G) :
    ⁅aimg (S : Subgroup G) α (Fcore G), Wnc S α⁆ ≤ aimg (S : Subgroup G) α (Zfix S) := by
  have hWT : Wnc S α ≤ thompsonJ (S : Subgroup G) :=
    (h.Wnc_le_thompsonJ_core α hV).trans h.thompsonJ_core_le_thompsonJ_sylow
  calc ⁅aimg (S : Subgroup G) α (Fcore G), Wnc S α⁆
      ≤ ⁅aimg (S : Subgroup G) α (Fcore G), thompsonJ (S : Subgroup G)⁆ :=
        Subgroup.commutator_mono le_rfl hWT
    _ = ⁅thompsonJ (S : Subgroup G), aimg (S : Subgroup G) α (Fcore G)⁆ :=
        Subgroup.commutator_comm _ _
    _ = aimg (S : Subgroup G) α (Zfix S) := h.commutator_thompsonJ_aimg_Fcore α

theorem commutator_cj_Fa_Wnc_le (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (S : Subgroup G) α (Fcore G) ≠ Fcore G) (g : G) :
    ⁅cj (aimg (S : Subgroup G) α (Fcore G)) g, Wnc S α⁆ ≤ aimg (S : Subgroup G) α (Zfix S) := by
  have hZc := h.aimg_Zfix_le_center α hV hF
  have e : ⁅cj (aimg (S : Subgroup G) α (Fcore G)) g, Wnc S α⁆ =
      cj ⁅aimg (S : Subgroup G) α (Fcore G), Wnc S α⁆ g := by
    rw [cj_commutator, cj_eq_self_of_normal (Y := Wnc S α)]
  rw [e]
  calc cj ⁅aimg (S : Subgroup G) α (Fcore G), Wnc S α⁆ g
      ≤ cj (aimg (S : Subgroup G) α (Zfix S)) g := cj_mono (h.commutator_Fa_Wnc_le α hV)
    _ = aimg (S : Subgroup G) α (Zfix S) := cj_eq_of_le_center hZc g

theorem commutator_Wnc_Wnc_le (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (S : Subgroup G) α (Fcore G) ≠ Fcore G) :
    ⁅Wnc S α, Wnc S α⁆ ≤ aimg (S : Subgroup G) α (Zfix S) := by
  have := normal_of_le_center' (h.aimg_Zfix_le_center α hV hF)
  have h2 : ⁅Wnc S α, ⨆ g : G, cj (aimg (S : Subgroup G) α (Fcore G)) g⁆ ≤
      aimg (S : Subgroup G) α (Zfix S) :=
    commutator_iSup_le_normal _ (fun g => by
      rw [Subgroup.commutator_comm]; exact h.commutator_cj_Fa_Wnc_le α hV hF g)
  rwa [← Wnc_eq_iSup α] at h2

theorem sq_mem_of_mem_Wnc (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (S : Subgroup G) α (Fcore G) ≠ Fcore G) {w : G} (hw : w ∈ Wnc S α) :
    w ^ 2 ∈ aimg (S : Subgroup G) α (Zfix S) := by
  have hZc := h.aimg_Zfix_le_center α hV hF
  have hcomm := h.commutator_Wnc_Wnc_le α hV hF
  have hW : w ∈ (⨆ g : G, cj (aimg (S : Subgroup G) α (Fcore G)) g : Subgroup G) := by
    rwa [Wnc_eq_iSup α] at hw
  have key : w ∈ Wnc S α ∧ w ^ 2 ∈ aimg (S : Subgroup G) α (Zfix S) := by
    refine Subgroup.iSup_induction (fun g : G => cj (aimg (S : Subgroup G) α (Fcore G)) g)
      (C := fun w => w ∈ Wnc S α ∧ w ^ 2 ∈ aimg (S : Subgroup G) α (Zfix S)) hW ?_ ?_ ?_
    · intro g x hx
      refine ⟨?_, ?_⟩
      · have : x ∈ ⨆ g : G, cj (aimg (S : Subgroup G) α (Fcore G)) g :=
          Subgroup.mem_iSup_of_mem g hx
        rwa [← Wnc_eq_iSup α] at this
      · have hel := isElemAbelian_cj (isElemAbelian_aimg α (isElemAbelian_Fcore (G := G))) g
        rw [(isElemAbelian_iff.mp hel).2 x hx]
        exact one_mem _
    · exact ⟨one_mem _, by simp⟩
    · rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
      refine ⟨mul_mem ha hb, ?_⟩
      have hcmem : b⁻¹ * a⁻¹ * b * a ∈ aimg (S : Subgroup G) α (Zfix S) := by
        have := hcomm (Subgroup.commutator_mem_commutator ((Wnc S α).inv_mem hb)
          ((Wnc S α).inv_mem ha))
        simpa [commutatorElement_def] using this
      have hcc : b * (b⁻¹ * a⁻¹ * b * a) = (b⁻¹ * a⁻¹ * b * a) * b :=
        Subgroup.mem_center_iff.mp (hZc hcmem) b
      have e1 : b * a = a * b * (b⁻¹ * a⁻¹ * b * a) := by group
      have : (a * b) ^ 2 = a ^ 2 * b ^ 2 * (b⁻¹ * a⁻¹ * b * a) := by
        calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
          _ = a * (a * b * (b⁻¹ * a⁻¹ * b * a)) * b := by rw [e1]
          _ = a ^ 2 * (b * ((b⁻¹ * a⁻¹ * b * a) * b)) := by group
          _ = a ^ 2 * (b * (b * (b⁻¹ * a⁻¹ * b * a))) := by rw [← hcc]
          _ = a ^ 2 * b ^ 2 * (b⁻¹ * a⁻¹ * b * a) := by group
      rw [this]
      exact mul_mem (mul_mem ha2 hb2) hcmem
  exact key.2

theorem aimg_symm_Wnc_mem_normal (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G) {s x : G}
    (hs : s ∈ (S : Subgroup G)) (hx : x ∈ aimg (S : Subgroup G) α.symm (Wnc S α)) :
    s * x * s⁻¹ ∈ aimg (S : Subgroup G) α.symm (Wnc S α) :=
  mem_conj_of_normal_subgroupOf (normal_subgroupOf_aimg (h.Wnc_le_sylow α hV) inferInstance)
    hs hx (aimg_le hx)

theorem aimg_symm_Wnc_commutator_le (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (S : Subgroup G) α (Fcore G) ≠ Fcore G) :
    ⁅aimg (S : Subgroup G) α.symm (Wnc S α), aimg (S : Subgroup G) α.symm (Wnc S α)⁆ ≤
      Zfix S := by
  have hWS := h.Wnc_le_sylow α hV
  have h1 := aimg_commutator (S := (S : Subgroup G)) (α := α.symm) hWS hWS
  rw [← h1]
  have := aimg_mono (S := (S : Subgroup G)) (α := α.symm) (h.commutator_Wnc_Wnc_le α hV hF)
  rwa [aimg_symm_aimg Zfix_le_sylow] at this

theorem sq_mem_of_mem_aimg_symm_Wnc (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (S : Subgroup G) α (Fcore G) ≠ Fcore G) {w : G}
    (hw : w ∈ aimg (S : Subgroup G) α.symm (Wnc S α)) : w ^ 2 ∈ Zfix S := by
  obtain ⟨y, hy, rfl⟩ := mem_aimg.mp hw
  have h2 := h.sq_mem_of_mem_Wnc α hV hF hy
  have h3 : ((y ^ 2 : (S : Subgroup G)) : G) ∈ aimg (S : Subgroup G) α (Zfix S) := by
    simpa using h2
  obtain ⟨z₁, hz₁, hz₁y⟩ := mem_aimg.mp h3
  have h4 : α z₁ = y ^ 2 := Subtype.ext hz₁y
  have h5 : α.symm (y ^ 2) = z₁ := by rw [← h4, α.symm_apply_apply]
  have h6 : ((α.symm y : (S : Subgroup G)) : G) ^ 2 =
      ((α.symm (y ^ 2) : (S : Subgroup G)) : G) := by
    rw [map_pow]; rfl
  rw [h6, h5]
  exact hz₁

theorem Vmod_le_Wnc_of_aimg (α : (S : Subgroup G) ≃* (S : Subgroup G)) :
    aimg (S : Subgroup G) α (Vmod G) ≤ Wnc S α :=
  (aimg_mono (Vmod_le_Ecore.trans h.Ecore_le_Fcore)).trans (aimg_Fcore_le_Wnc α)

theorem dihedral_commute (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (S : Subgroup G) α (Fcore G) ≠ Fcore G) (u : G) {v : G}
    (hv : v ∈ aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Vmod G)) u⁻¹))
    {hh : G} (hhW : hh ∈ Wnc S α) (hh2 : hh ^ 2 = 1) :
    hh * (v⁻¹ * hh * v) = (v⁻¹ * hh * v) * hh := by
  by_contra hne
  have hZc := h.aimg_Zfix_le_center α hV hF
  obtain ⟨y₁, hy₁, hv₁⟩ := mem_aimg.mp hv
  have hvS : v ∈ (S : Subgroup G) := by rw [← hv₁]; exact (α.symm y₁).2
  have hhS : hh ∈ (S : Subgroup G) := h.Wnc_le_sylow α hV hhW
  have hel : CFSG.Open.IsElemAbelian 2 (cj (aimg (S : Subgroup G) α (Vmod G)) u⁻¹) :=
    isElemAbelian_cj (isElemAbelian_aimg α isElemAbelian_Vmod) _
  have hy₁2 : (y₁ : G) ^ 2 = 1 := (isElemAbelian_iff.mp hel).2 y₁ hy₁
  have hv2 : v * v = 1 := by
    rw [← hv₁]
    have h1 : y₁ * y₁ = 1 := Subtype.ext (by simpa [pow_two] using hy₁2)
    have h' : α.symm y₁ * α.symm y₁ = 1 := by rw [← map_mul, h1, map_one]
    exact congrArg Subtype.val h'
  have hh2' : hh * hh = 1 := by rw [← pow_two]; exact hh2
  have hy₁W : (y₁ : G) ∈ Wnc S α := by
    have h1 : u⁻¹ * (y₁ : G) * u⁻¹⁻¹ ∈ aimg (S : Subgroup G) α (Vmod G) := mem_cj.mp hy₁
    have h2 : u⁻¹ * (y₁ : G) * u⁻¹⁻¹ ∈ Wnc S α := h.Vmod_le_Wnc_of_aimg α h1
    have := (inferInstance : (Wnc S α).Normal).conj_mem _ h2 u
    simpa [mul_assoc] using this
  have hvW' : v ∈ aimg (S : Subgroup G) α.symm (Wnc S α) := mem_aimg.mpr ⟨y₁, hy₁W, hv₁⟩
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hh' : hh⁻¹ = hh := inv_eq_of_mul_eq_one_right hh2'
  have hyW : v * hh * v * hh ∈ Wnc S α := by
    have := (inferInstance : (Wnc S α).Normal).conj_mem hh hhW v
    rw [hv'] at this
    exact (Wnc S α).mul_mem this hhW
  have hyW' : v * hh * v * hh ∈ aimg (S : Subgroup G) α.symm (Wnc S α) := by
    have h1 := h.aimg_symm_Wnc_mem_normal α hV hhS hvW'
    rw [hh'] at h1
    have h2 : v * hh * v * hh = v * (hh * v * hh) := by simp only [mul_assoc]
    rw [h2]
    exact Subgroup.mul_mem _ hvW' h1
  have hz0a : (v * hh * v * hh) * (v * hh * v * hh) ∈ aimg (S : Subgroup G) α (Zfix S) := by
    have := h.sq_mem_of_mem_Wnc α hV hF hyW
    rwa [pow_two] at this
  have hz0Z : (v * hh * v * hh) * (v * hh * v * hh) ∈ Zfix S := by
    have := h.sq_mem_of_mem_aimg_symm_Wnc α hV hF hyW'
    rwa [pow_two] at this
  have hz0ne : (v * hh * v * hh) * (v * hh * v * hh) ≠ 1 := by
    intro h1
    apply hne
    have e := dihedral_commutator hv2 hh2'
    rw [h1, inv_one] at e
    calc hh * (v⁻¹ * hh * v)
        = (hh * (v⁻¹ * hh * v) * hh⁻¹ * (v⁻¹ * hh * v)⁻¹) * ((v⁻¹ * hh * v) * hh) := by group
      _ = (v⁻¹ * hh * v) * hh := by rw [e, one_mul]
  have hcommyv := dihedral_identities hv2 hh2'
  have hyS : v * hh * v * hh ∈ (S : Subgroup G) := aimg_le hyW'
  have hz0S : (v * hh * v * hh) * (v * hh * v * hh) ∈ (S : Subgroup G) := Zfix_le_sylow hz0Z
  have hrel : (⟨v * hh * v * hh, hyS⟩ : (S : Subgroup G)) * α.symm y₁ *
      (⟨v * hh * v * hh, hyS⟩ : (S : Subgroup G))⁻¹ * (α.symm y₁)⁻¹ =
      ⟨(v * hh * v * hh) * (v * hh * v * hh), hz0S⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hv₁]
    exact hcommyv
  have haW : ((α ⟨v * hh * v * hh, hyS⟩ : (S : Subgroup G)) : G) ∈ Wnc S α := by
    obtain ⟨y₂, hy₂, hy₂e⟩ := mem_aimg.mp hyW'
    have : (⟨v * hh * v * hh, hyS⟩ : (S : Subgroup G)) = α.symm y₂ := Subtype.ext hy₂e.symm
    rw [this, α.apply_symm_apply]
    exact hy₂
  have hbV : ((α (α.symm y₁) : (S : Subgroup G)) : G) ∈
      cj (aimg (S : Subgroup G) α (Vmod G)) u⁻¹ := by
    rw [α.apply_symm_apply]; exact hy₁
  have hcZ : ((α ⟨(v * hh * v * hh) * (v * hh * v * hh), hz0S⟩ : (S : Subgroup G)) : G) ∈
      aimg (S : Subgroup G) α (Zfix S) :=
    mem_aimg_of_mem (y := ⟨(v * hh * v * hh) * (v * hh * v * hh), hz0S⟩) hz0Z
  have ha' : u⁻¹ * ((α ⟨v * hh * v * hh, hyS⟩ : (S : Subgroup G)) : G) * u ∈
      (S : Subgroup G) := by
    have h1 := (inferInstance : (Wnc S α).Normal).conj_mem _ haW u⁻¹
    exact h.Wnc_le_sylow α hV (by simpa using h1)
  have hb' : u⁻¹ * ((α (α.symm y₁) : (S : Subgroup G)) : G) * u ∈
      aimg (S : Subgroup G) α (Vmod G) := by
    have := mem_cj.mp hbV
    simpa using this
  have hb'S : u⁻¹ * ((α (α.symm y₁) : (S : Subgroup G)) : G) * u ∈ (S : Subgroup G) :=
    aimg_le hb'
  have hc' : u⁻¹ * ((α ⟨(v * hh * v * hh) * (v * hh * v * hh), hz0S⟩ : (S : Subgroup G)) : G) * u =
      ((α ⟨(v * hh * v * hh) * (v * hh * v * hh), hz0S⟩ : (S : Subgroup G)) : G) := by
    exact central_conj_eq (hZc hcZ) u
  have hθ := theta_transport α u hrel ha' hb'S hc'
  have hv''V : ((α.symm ⟨u⁻¹ * ((α (α.symm y₁) : (S : Subgroup G)) : G) * u, hb'S⟩ :
      (S : Subgroup G)) : G) ∈ Vmod G := (mem_aimg_symm_iff hb'S).mp hb'
  have hcen := congrArg Subtype.val hθ
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hcen
  have h1 := h.commutator_eq_one_of_central
    (α.symm ⟨u⁻¹ * ((α ⟨v * hh * v * hh, hyS⟩ : (S : Subgroup G)) : G) * u, ha'⟩).2 hv''V
    (by rw [hcen]; exact hZc hz0a)
  rw [hcen] at h1
  exact hz0ne h1

theorem dihedral_translated_module_obstruction (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (S : Subgroup G) α (Fcore G) ≠ Fcore G) :
    aimg (S : Subgroup G) α (Zfix S) ≤ Subgroup.center G ∧
    aimg (S : Subgroup G) α (Zfix S) ≤ Wnc S α ∧
    Wnc S α ≤ thompsonJ (CFSG.pCore 2 G) ∧ (Wnc S α).Normal ∧
    (⁅Wnc S α, Wnc S α⁆ ≤ aimg (S : Subgroup G) α (Zfix S) ∧
      ∀ w ∈ Wnc S α, w ^ 2 ∈ aimg (S : Subgroup G) α (Zfix S)) ∧
    ((aimg (S : Subgroup G) α.symm (Wnc S α)).subgroupOf (S : Subgroup G)).Normal ∧
    (⁅aimg (S : Subgroup G) α.symm (Wnc S α), aimg (S : Subgroup G) α.symm (Wnc S α)⁆ ≤ Zfix S ∧
      ∀ w ∈ aimg (S : Subgroup G) α.symm (Wnc S α), w ^ 2 ∈ Zfix S) ∧
    ∀ u : G, ∀ v ∈ aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Vmod G)) u⁻¹),
      ∀ hh ∈ Wnc S α, hh ^ 2 = 1 → hh * (v⁻¹ * hh * v) = (v⁻¹ * hh * v) * hh :=
  ⟨h.aimg_Zfix_le_center α hV hF, h.aimg_Zfix_le_Wnc α, h.Wnc_le_thompsonJ_core α hV, inferInstance,
    ⟨h.commutator_Wnc_Wnc_le α hV hF, fun _ hw => h.sq_mem_of_mem_Wnc α hV hF hw⟩,
    normal_subgroupOf_aimg (h.Wnc_le_sylow α hV) inferInstance,
    ⟨h.aimg_symm_Wnc_commutator_le α hV hF, fun _ hw => h.sq_mem_of_mem_aimg_symm_Wnc α hV hF hw⟩,
    fun u _ hv _ hhW hh2 => h.dihedral_commute α hV hF u hv hhW hh2⟩

end IsSeed

end Seed

end Dihedral

end CFSG.QuasithinUnique.Setup.Campbell
