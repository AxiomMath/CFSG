module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv
public import CFSG.GH74.GLS.Stage1.Thm4.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Lh : Type} [Group Lh] {z : G}

theorem isRigidOfType_cmap {K : Subgroup G} (h : IsRigidOfType Lh z K) {c : G}
    (hc : c ∈ centralizer ({z} : Set G)) : IsRigidOfType Lh z (cmap c K) := by
  obtain ⟨h1, ⟨e⟩⟩ := h
  have h2 := isPRigid_cmap h1 c
  rw [conj_fix_of_mem_centralizer hc] at h2
  obtain ⟨e'⟩ := nonempty_quot_cmap c K
  exact ⟨h2, ⟨e'.trans e⟩⟩

theorem cmap_mem_rigidSet_iff {K : Subgroup G} {c : G} (hc : c ∈ centralizer ({z} : Set G)) :
    cmap c K ∈ RigidSet Lh z ↔ K ∈ RigidSet Lh z := by
  constructor
  · intro h
    have := isRigidOfType_cmap h (inv_mem hc)
    rwa [cmap_inv_cancel] at this
  · intro h
    exact isRigidOfType_cmap h hc

theorem NormsAll.conj {t c : G} (hc : c ∈ centralizer ({z} : Set G)) (h : NormsAll Lh z t) :
    NormsAll Lh z (c * t * c⁻¹) := by
  intro K hK
  have hK' : cmap c⁻¹ K ∈ RigidSet Lh z := (cmap_mem_rigidSet_iff (inv_mem hc)).2 hK
  have hn := (Subgroup.mem_normalizer_iff.1 (h _ hK'))
  refine Subgroup.mem_normalizer_iff.2 fun x => ?_
  have := hn (c⁻¹ * x * c)
  simp only [mem_cmap, inv_inv] at this
  have e1 : c * (c⁻¹ * x * c) * c⁻¹ = x := by group
  have e2 : c * (t * (c⁻¹ * x * c) * t⁻¹) * c⁻¹ = c * t * c⁻¹ * x * (c * t * c⁻¹)⁻¹ := by group
  rwa [e1, e2] at this

theorem Good92.conj {t : G} {K : Subgroup G} (h : Good92 G Lh z t K) {c : G}
    (hc : c ∈ centralizer ({z} : Set G)) :
    Good92 G Lh z (c * t * c⁻¹) (cmap c K) where
  z_ord := h.z_ord
  t_ord := by
    have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective t
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    rw [this]; exact h.t_ord
  t_cen := by
    have hcz' : c⁻¹ * z * c = z := by
      simpa using conj_fix_of_mem_centralizer (inv_mem hc)
    have htz : t * z = z * t := Subgroup.mem_centralizer_singleton_iff.mp h.t_cen
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc c * t * c⁻¹ * z = c * t * (c⁻¹ * z * c) * c⁻¹ := by group
      _ = c * t * z * c⁻¹ := by rw [hcz']
      _ = c * (t * z) * c⁻¹ := by group
      _ = c * (z * t) * c⁻¹ := by rw [htz]
      _ = (c * z * c⁻¹) * (c * t * c⁻¹) := by group
      _ = z * (c * t * c⁻¹) := by rw [conj_fix_of_mem_centralizer hc]
  K_rigid := isRigidOfType_cmap h.K_rigid hc
  z_mem := by
    have hcz' : c⁻¹ * z * c = z := by
      simpa using conj_fix_of_mem_centralizer (inv_mem hc)
    rw [mem_cmap, hcz']
    exact h.z_mem
  t_conj := by
    obtain ⟨g₀, hg₀⟩ := h.t_conj
    refine ⟨c * g₀, ?_⟩
    have : (c * g₀)⁻¹ * (c * t * c⁻¹) * (c * g₀) = g₀⁻¹ * t * g₀ := by group
    rwa [this]
  comm_eq := by
    have e : zpowers (c * t * c⁻¹) = (zpowers t).map (MulAut.conj c).toMonoidHom := by
      rw [MonoidHom.map_zpowers]; rfl
    rw [e, ← Subgroup.map_commutator, h.comm_eq]
  comm_nle := by
    have e : zpowers (c * t * c⁻¹) = (zpowers t).map (MulAut.conj c).toMonoidHom := by
      rw [MonoidHom.map_zpowers]; rfl
    rw [e, ← Subgroup.map_commutator, pPrimeCoreOf_cmap]
    intro hle
    exact h.comm_nle ((Subgroup.map_le_map_iff_of_injective (MulAut.conj c).injective).1 hle)

end CFSG.GH74.GLS.Stage1.Thm4
