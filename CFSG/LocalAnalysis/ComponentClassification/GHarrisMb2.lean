module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisMb1
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisYb11
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisYb12

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.TwoGroups
  CFSG.GH74.GLS.Bg.TwoGroups.L23

theorem SCert.SE.card_UT3 : Fintype.card (UT3 F4c) = 64 := by decide

section Ybar

variable {Y : Type} [Group Y] [Finite Y]

namespace GHSylow

variable (D : GHSylow Y)

theorem card_sylowXt (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y) :
    Nat.card ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt) = 64 := by
  rw [Nat.card_congr (D.tUT hO hz).toEquiv, Nat.card_eq_fintype_card, SE.card_UT3]

theorem Et_ne_sylowXt (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y) :
    D.Et ≠ ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt) := by
  intro h
  have h16 := (D.card_Et_Ft hO hz).1
  rw [h, D.card_sylowXt hO hz] at h16
  norm_num at h16


theorem prop38B_of (hC : GorensteinHaradaThmCInput) (hO : pPrimeCore 2 Y = ⊥)
    (hz : ∀ y : Y, y * D.z = D.z * y)
    (hB : pCore 2 D.Xt = ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt)) :
    (((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt).index = 1 ∨
        ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt).index = 3) ∧
      D.Et.Normal ∧ D.Ft.Normal ∧
      centralizer (((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt) : Set D.Xt) ≤
        ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt) := by
  rcases D.prop38_Xt hC hO hz with ⟨-, h⟩ | ⟨hA, -⟩
  · exact h
  · exact absurd (hA.symm.trans hB) (D.Et_ne_sylowXt hO hz)

theorem prop38A_of (hC : GorensteinHaradaThmCInput) (hO : pPrimeCore 2 Y = ⊥)
    (hz : ∀ y : Y, y * D.z = D.z * y)
    (hA : pCore 2 D.Xt ≠ ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt)) :
    letI : (pCore 2 D.Xt).Normal := pCore_normal
    pCore 2 D.Xt = D.Et ∧ centralizer (D.Et : Set D.Xt) ≤ D.Et ∧
      Nonempty (D.Xt ⧸ pCore 2 D.Xt ≃* alternatingGroup (Fin 5)) ∧
      ∀ u ∈ D.Et, ∀ v ∈ D.Et, u ≠ 1 → v ≠ 1 → ∃ g : D.Xt, g⁻¹ * u * g = v := by
  rcases D.prop38_Xt hC hO hz with ⟨hB, -⟩ | h
  · exact absurd hB hA
  · exact h

theorem E_normal_Y (hC : GorensteinHaradaThmCInput) (hO : pPrimeCore 2 Y = ⊥)
    (hz : ∀ y : Y, y * D.z = D.z * y) : D.E.Normal := by
  by_cases hB : pCore 2 D.Xt = ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt)
  · exact D.E_normal_of hO hz (D.prop38B_of hC hO hz hB).2.1
  · obtain ⟨hEt, -⟩ := D.prop38A_of hC hO hz hB
    have hn : (pCore 2 D.Xt).Normal := pCore_normal
    rw [hEt] at hn
    exact D.E_normal_of hO hz hn

end GHSylow

end Ybar

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

theorem barS_mem_toMb_E_iff {w : G} (hw : w ∈ (D.S : Subgroup G)) :
    D.barS ⟨w, hw⟩ ∈ D.toMb.E ↔ w ∈ D.E := by
  constructor
  · rintro ⟨e, he, heq⟩
    have h := D.barS_injective (a₁ := ⟨D.toG e, D.toG_mem e⟩) (a₂ := ⟨w, hw⟩) heq
    obtain rfl : D.toG e = w := congrArg Subtype.val h
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, rfl⟩

theorem barS_mem_toMb_F_iff {w : G} (hw : w ∈ (D.S : Subgroup G)) :
    D.barS ⟨w, hw⟩ ∈ D.toMb.F ↔ w ∈ D.F := by
  constructor
  · rintro ⟨e, he, heq⟩
    have h := D.barS_injective (a₁ := ⟨D.toG e, D.toG_mem e⟩) (a₂ := ⟨w, hw⟩) heq
    obtain rfl : D.toG e = w := congrArg Subtype.val h
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, rfl⟩

omit [Finite G] in
theorem piM_conj {g u : G} (hg : g ∈ D.M) (hu : u ∈ D.M) :
    (D.piM ⟨g, hg⟩)⁻¹ * D.piM ⟨u, hu⟩ * D.piM ⟨g, hg⟩ =
      D.piM ⟨g⁻¹ * u * g, mul_mem (mul_mem (inv_mem hg) hu) hg⟩ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem conj_mem_of_normal_image {K : Subgroup G} (hKS : K ≤ (D.S : Subgroup G))
    (hK : ∀ w (hw : w ∈ (D.S : Subgroup G)), w ∈ K → ∀ c : D.Mb,
      ∃ w' : G, ∃ hw' : w' ∈ (D.S : Subgroup G), w' ∈ K ∧ c * D.barS ⟨w, hw⟩ * c⁻¹ =
        D.barS ⟨w', hw'⟩)
    {g u : G} (hg : g ∈ D.M) (hu : u ∈ K) (hS : g⁻¹ * u * g ∈ (D.S : Subgroup G)) :
    g⁻¹ * u * g ∈ K := by
  obtain ⟨w', hw', hw'K, heq⟩ := hK u (hKS hu) hu (D.piM ⟨g, hg⟩)⁻¹
  rw [inv_inv, D.piM_conj hg (D.S_le_M (hKS hu))] at heq
  have h := D.barS_injective (a₁ := ⟨g⁻¹ * u * g, hS⟩) (a₂ := ⟨w', hw'⟩) heq
  have h' : g⁻¹ * u * g = w' := congrArg Subtype.val h
  rw [h']
  exact hw'K


theorem conj_mem_E_of_M (hC : GorensteinHaradaThmCInput) {g u : G} (hg : g ∈ D.M)
    (hu : u ∈ D.E) (hS : g⁻¹ * u * g ∈ (D.S : Subgroup G)) : g⁻¹ * u * g ∈ D.E := by
  have hE := D.toMb.E_normal_Y hC D.pPrimeCore_Mb D.z_comm_Mb
  refine D.conj_mem_of_normal_image D.E_le_S (fun w hw hwK c => ?_) hg hu hS
  have h1 := hE.conj_mem _ ((D.barS_mem_toMb_E_iff hw).mpr hwK) c
  obtain ⟨e, he, heq⟩ := h1
  exact ⟨D.toG e, D.toG_mem e, ⟨e, he, rfl⟩, heq.symm⟩

abbrev caseB : Prop :=
  pCore 2 D.toMb.Xt =
    ((D.toMb.sylowXt D.pPrimeCore_Mb D.z_comm_Mb : Sylow 2 D.toMb.Xt) : Subgroup D.toMb.Xt)

theorem conj_mem_F_of_M (hC : GorensteinHaradaThmCInput) (hB : D.caseB) {g u : G}
    (hg : g ∈ D.M) (hu : u ∈ D.F) (hS : g⁻¹ * u * g ∈ (D.S : Subgroup G)) :
    g⁻¹ * u * g ∈ D.F := by
  have hF := D.toMb.F_normal_of D.pPrimeCore_Mb D.z_comm_Mb
    (D.toMb.prop38B_of hC D.pPrimeCore_Mb D.z_comm_Mb hB).2.2.1
  refine D.conj_mem_of_normal_image D.F_le_S (fun w hw hwK c => ?_) hg hu hS
  have h1 := hF.conj_mem _ ((D.barS_mem_toMb_F_iff hw).mpr hwK) c
  obtain ⟨e, he, heq⟩ := h1
  exact ⟨D.toG e, D.toG_mem e, ⟨e, he, rfl⟩, heq.symm⟩

end GHSylow

end CFSG.ComponentClassification.GHarris
