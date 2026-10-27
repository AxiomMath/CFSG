module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddCtrlDefs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddCtrlSuzModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddCtrlSuzUnique

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.GSThmB.CF23L34

theorem suzTwoBFusionGeneration_holds :
    SuzTwoBFusionGeneration := by
  intro S _ hS x hx hxC L hL hLperf hLcard h hh hh2 hh1
  obtain ⟨f, hfx⟩ := exists_mulEquiv_suzM_apply_eq_suzInv_zero hS hx hxC
  let φ : S →* Equiv.Perm (Fin 1782) := suzM.subtype.comp f.toMonoidHom
  have hφ_inj : Function.Injective φ := by
    intro a b hab
    exact f.injective (Subtype.ext hab)
  have hφ_range : φ.range = suzM := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      exact (f s).2
    · intro hz
      exact ⟨f.symm ⟨z, hz⟩, by simp [φ]⟩
  have hφ_x : φ x = suzInv 0 := by
    simp [φ, hfx]
  let L₀ : Subgroup S := suzL.comap φ
  have hL₀_le : L₀ ≤ centralizer ({x} : Set S) := by
    intro s hs
    have hmem : φ s ∈ suzL := Subgroup.mem_comap.1 hs
    have hcent : φ s ∈ centralizer ({suzInv 0} : Set (Equiv.Perm (Fin 1782))) :=
      (suzL_le_centM hmem).1
    have hcomm : φ s * suzInv 0 = suzInv 0 * φ s :=
      Subgroup.mem_centralizer_singleton_iff.1 hcent
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hφ_inj
    rw [map_mul, map_mul, hφ_x]
    exact hcomm
  have hmap₀ : L₀.map φ = suzL := by
    show (suzL.comap φ).map φ = suzL
    exact Subgroup.map_comap_eq_self (f := φ) (H := suzL)
      (by rw [hφ_range]; intro y hy; exact (suzL_le_centM hy).2)
  have hcard₀ : Nat.card L₀ = 20160 := by
    calc Nat.card L₀ = Nat.card (L₀.map φ) :=
        (Subgroup.card_map_of_injective (f := φ) hφ_inj).symm
      _ = Nat.card suzL := by rw [hmap₀]
      _ = 20160 := card_suzL
  have hcomm_suzL : ⁅suzL, suzL⁆ = suzL := by
    have hsimple : IsSimpleGroup ↥suzL := isSimpleGroup_suzL
    have hnc : ¬ IsMulCommutative ↥suzL := by
      intro hcomm
      have hp := (@Group.is_simple_iff_prime_card ↥suzL _ hcomm).1 hsimple
      rw [card_suzL] at hp
      norm_num at hp
    exact Subgroup.isPerfect_iff.1
      (@TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative ↥suzL _ hsimple hnc)
  have hperf₀ : ⁅L₀, L₀⁆ = L₀ := by
    apply Subgroup.map_injective hφ_inj
    rw [Subgroup.map_commutator, hmap₀, hcomm_suzL]
  have hL_eq : L = L₀ :=
    eq_of_perfect_of_card_eq_of_isSporadic_suz hS hx hxC hL hL₀_le hLperf hperf₀ hLcard hcard₀
  have hh₀ : h ∈ L₀ := hL_eq ▸ hh
  have hφh_mem : φ h ∈ suzL := Subgroup.mem_comap.1 hh₀
  have hφh_sq : φ h * φ h = 1 := by
    rw [← map_mul, hh2, map_one]
  have hφh_ne : φ h ≠ 1 := by
    intro h1
    exact hh1 (hφ_inj (h1.trans (map_one φ).symm))
  obtain ⟨a', ha'M, hconj, hsup⟩ :=
    exists_conj_sup_eq_suzM_of_mem_suzL hφh_mem hφh_sq hφh_ne
  let a : S := f.symm ⟨a', ha'M⟩
  have hφa : φ a = a' := by
    simp [φ, a]
  have hmapL : L.map φ = suzL := by
    rw [hL_eq, hmap₀]
  refine ⟨a, ?_, ?_⟩
  · apply hφ_inj
    calc φ (a * x * a⁻¹) = φ a * φ x * (φ a)⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = a' * suzInv 0 * a'⁻¹ := by rw [hφa, hφ_x]
      _ = suzInv 0 * φ h := hconj
      _ = φ (x * h) := by rw [map_mul, hφ_x]
  · apply Subgroup.map_injective hφ_inj
    rw [Subgroup.map_sup, Subgroup.map_map_conj, hmapL, hφa, hsup, Subgroup.map_top, hφ_range]

end CFSG.ComponentClassification.GrSLit.L34Sec5S
