module

public import CFSG.GH74.GLS.Stage1.Thm4.Defs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv

public section

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4 CFSG.GH74.GLS.Stage1.Thm3.Sec4

variable {Q : Type} [Group Q] {G : Type} [Group G] [Finite G]

theorem isRigidOfType_conj {z : G} {K : Subgroup G} (h : IsRigidOfType Q z K) (g : G) :
    IsRigidOfType Q (g * z * g⁻¹) (cmap g K) := by
  obtain ⟨e⟩ := h.2
  obtain ⟨e'⟩ := nonempty_quot_cmap g K
  exact ⟨isPRigid_cmap h.1 g, ⟨e'.trans e⟩⟩

theorem rigidSet_conj {z : G} (g : G) :
    RigidSet Q (g * z * g⁻¹) = cmap g '' RigidSet Q z := by
  ext K
  constructor
  · intro hK
    change IsRigidOfType Q (g * z * g⁻¹) K at hK
    refine ⟨cmap g⁻¹ K, ?_, cmap_cancel g K⟩
    have h := isRigidOfType_conj hK g⁻¹
    rwa [show g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹ = z by group] at h
  · rintro ⟨K', hK', rfl⟩
    change IsRigidOfType Q z K' at hK'
    exact isRigidOfType_conj hK' g

theorem ncard_rigidSet_conj {z : G} (g : G) :
    (RigidSet Q (g * z * g⁻¹)).ncard = (RigidSet Q z).ncard := by
  rw [rigidSet_conj]
  exact Set.ncard_image_of_injective _
    (Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective)

theorem kz_conj {z : G} (g : G) :
    Kz Q (g * z * g⁻¹) = cmap g (Kz Q z) := by
  unfold Kz
  rw [rigidSet_conj, sSup_image]
  exact ((Subgroup.gc_map_comap (MulAut.conj g).toMonoidHom).l_sSup).symm

omit [Finite G] in
theorem kz_le_centralizer {z : G} :
    Kz Q z ≤ centralizer ({z} : Set G) := by
  unfold Kz
  exact sSup_le fun K hK => hK.1.1.2.2.1

theorem centralizer_le_normalizer_kz {z : G} :
    centralizer ({z} : Set G) ≤ normalizer (Kz Q z : Set G) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hcz : c * z * c⁻¹ = z := conj_fix_of_mem_centralizer hc
  have h := kz_conj (Q := Q) (z := z) c
  rw [hcz] at h
  exact h.symm

omit [Finite G] in
theorem kz_eq_of_rigidSet_subsingleton {z : G}
    (hs : (RigidSet Q z).Subsingleton) {K : Subgroup G} (hK : K ∈ RigidSet Q z) :
    Kz Q z = K := by
  unfold Kz
  rw [hs.eq_singleton_of_mem hK]
  exact sSup_singleton

theorem centralizer_le_normalizer_of_rigidSet_subsingleton {z : G}
    (hs : (RigidSet Q z).Subsingleton) {K : Subgroup G} (hK : K ∈ RigidSet Q z) :
    centralizer ({z} : Set G) ≤ normalizer (K : Set G) := by
  rw [← kz_eq_of_rigidSet_subsingleton (Q := Q) (z := z) hs hK]
  exact centralizer_le_normalizer_kz (Q := Q) (z := z)

theorem rigidSet_subsingleton_of_global_max_one {z : G}
    (hz : (RigidSet Q z).ncard = 1)
    (hmax : ∀ s : G, orderOf s = 2 →
      (RigidSet Q s).ncard ≤ (RigidSet Q z).ncard) :
    ∀ s : G, orderOf s = 2 → (RigidSet Q s).Subsingleton := by
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  intro s hs
  have hle : (RigidSet Q s).ncard ≤ 1 := by
    simpa [hz] using hmax s hs
  exact Set.ncard_le_one_iff_subsingleton.mp hle

end CFSG.GH74.GLS.NT44
