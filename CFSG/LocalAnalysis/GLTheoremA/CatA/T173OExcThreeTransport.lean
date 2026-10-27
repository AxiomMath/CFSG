module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

section Transport

variable {G H : Type} [Group G] [Group H]

theorem map_map_symm_subgroupOf_eq {M : Subgroup G} (e : H ≃* ↥M) {A : Subgroup G} (hA : A ≤ M) :
    ((A.subgroupOf M).map e.symm.toMonoidHom).map (M.subtype.comp e.toMonoidHom) = A := by
  rw [Subgroup.map_map]
  have hcomp : (M.subtype.comp e.toMonoidHom).comp e.symm.toMonoidHom = M.subtype := by
    ext x
    simp
  rw [hcomp, Subgroup.map_subgroupOf_eq_of_le hA]

theorem inf_centralizer_map_symm_eq {M : Subgroup G} (e : H ≃* ↥M) {A K : Subgroup G} {d : G}
    (hAM : A ≤ M) (hKM : K ≤ M) (hdM : d ∈ M)
    (h : A ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers d) :
    (A.subgroupOf M).map e.symm.toMonoidHom ⊓
        Subgroup.centralizer (((K.subgroupOf M).map e.symm.toMonoidHom : Subgroup H) : Set H) =
      Subgroup.zpowers (e.symm ⟨d, hdM⟩) := by
  have hmemA : ∀ x : H, x ∈ (A.subgroupOf M).map e.symm.toMonoidHom ↔ (e x : G) ∈ A := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using (Subgroup.mem_subgroupOf.mp hy : (y : G) ∈ A)
    · intro hx
      refine ⟨⟨(e x : G), hAM hx⟩, Subgroup.mem_subgroupOf.mpr hx, ?_⟩
      apply e.injective
      simp
  have hmemC : ∀ x : H, x ∈ Subgroup.centralizer
        (((K.subgroupOf M).map e.symm.toMonoidHom : Subgroup H) : Set H) ↔
      (e x : G) ∈ Subgroup.centralizer (K : Set G) := by
    intro x
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hx k hk
      have hk' : (⟨k, hKM hk⟩ : ↥M) ∈ K.subgroupOf M := Subgroup.mem_subgroupOf.mpr hk
      have hcomm := hx (e.symm ⟨k, hKM hk⟩) ⟨⟨k, hKM hk⟩, hk', by simp⟩
      have hcomm' := congrArg e hcomm
      simp only [map_mul, MulEquiv.apply_symm_apply] at hcomm'
      simpa using congrArg Subtype.val hcomm'
    · rintro hx h ⟨k, hk, rfl⟩
      have hkG : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
      change e.symm ⟨k, hKM hkG⟩ * x = x * e.symm ⟨k, hKM hkG⟩
      apply e.injective
      have hstep : (⟨k, hKM hkG⟩ : ↥M) * e x = e x * ⟨k, hKM hkG⟩ :=
        Subtype.ext (hx (k : G) hkG)
      calc e (e.symm ⟨k, hKM hkG⟩ * x)
          = (⟨k, hKM hkG⟩ : ↥M) * e x := by rw [map_mul, MulEquiv.apply_symm_apply]
        _ = e x * ⟨k, hKM hkG⟩ := hstep
        _ = e (x * e.symm ⟨k, hKM hkG⟩) := by rw [map_mul, MulEquiv.apply_symm_apply]
  ext x
  have hz : ∀ n : ℤ, d ^ n = (e x : G) ↔ (e.symm ⟨d, hdM⟩) ^ n = x := by
    intro n
    constructor
    · intro hn
      have hn' : (⟨d, hdM⟩ : ↥M) ^ n = e x := Subtype.ext (by simpa using hn)
      apply e.injective
      rw [map_zpow, MulEquiv.apply_symm_apply, hn']
    · intro hn
      have hn' : (⟨d, hdM⟩ : ↥M) ^ n = e x := by
        have h := congrArg e hn
        rwa [map_zpow, MulEquiv.apply_symm_apply] at h
      exact congrArg Subtype.val hn'
  rw [Subgroup.mem_inf, hmemA x, hmemC x]
  have hiff : ((e x : G) ∈ A ∧ (e x : G) ∈ Subgroup.centralizer (K : Set G)) ↔
      (e x : G) ∈ Subgroup.zpowers d := by
    rw [← Subgroup.mem_inf, h]
  rw [hiff, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  exact exists_congr hz

theorem exists_twoGroup_decomp_map {ι : H →* G} (hι : Function.Injective ι) {A' K' : Subgroup H}
    (h : ∃ T : Subgroup H, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ K' ∧
      A' = (A' ⊓ K') ⊔ (A' ⊓ Subgroup.normalizer (T : Set H))) :
    ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ K'.map ι ∧
      A'.map ι = (A'.map ι ⊓ K'.map ι) ⊔ (A'.map ι ⊓ Subgroup.normalizer (T : Set G)) := by
  obtain ⟨T, hTne, hT2, hTK, hA⟩ := h
  refine ⟨T.map ι, ?_, hT2.map ι, Subgroup.map_mono hTK, ?_⟩
  · intro hbot
    exact hTne ((Subgroup.map_eq_bot_iff_of_injective (H := T) hι).mp hbot)
  · have hmap : A'.map ι =
        (A' ⊓ K').map ι ⊔ (A' ⊓ Subgroup.normalizer (T : Set H)).map ι := by
      conv_lhs => rw [hA, Subgroup.map_sup]
    refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
    calc A'.map ι = (A' ⊓ K').map ι ⊔ (A' ⊓ Subgroup.normalizer (T : Set H)).map ι := hmap
      _ ≤ (A'.map ι ⊓ K'.map ι) ⊔ (A'.map ι ⊓ Subgroup.normalizer (T.map ι : Set G)) := by
          refine sup_le ?_ ?_
          · exact (le_inf (Subgroup.map_mono inf_le_left)
              (Subgroup.map_mono inf_le_right)).trans le_sup_left
          · exact (le_inf (Subgroup.map_mono inf_le_left)
              ((Subgroup.map_mono inf_le_right).trans (Subgroup.le_normalizer_map ι))).trans
              le_sup_right

end Transport

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
