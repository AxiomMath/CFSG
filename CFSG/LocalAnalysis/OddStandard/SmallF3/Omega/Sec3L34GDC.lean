module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GHyp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GPocketP
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GConj

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem l34g_direct_closure [Finite G] (hKB : Asc82FactPocketLift) (hA : L34GLemmaA G) {r v u : G}
    {D I : Subgroup G} (hr : orderOf r = 2) (hv : orderOf v = 2) (hrv : r * v = v * r)
    (hDv : IsComponentIn D (centralizer ({v} : Set G))) (hDF : InFStar D) (huD : u ∈ D)
    (hDI4 : IsI4PlusIn D u) (hI : IsComponentIn I (centralizer ({u} : Set G))) (hIF : InFStar I)
    (hIv : CFSG.conjugate I v = I) (hDI : CFSG.conjugate D r ≤ I) : False := by
  have hu : orderOf u = 2 := hDI4.1
  set v₂ : G := r⁻¹ * u * r with hv₂def
  set D₂ : Subgroup G := CFSG.conjugate I r with hD₂def
  have hv₂ : orderOf v₂ = 2 := by
    have h' := MulEquiv.orderOf_eq (MulAut.conj r⁻¹) u
    rw [MulAut.conj_apply, inv_inv, hu] at h'
    simpa [hv₂def] using h'
  have hD₂ : IsComponentIn D₂ (centralizer ({v₂} : Set G)) := by
    have h' := l34g_isComponentIn_conjugate_centralizer hI r
    rw [hD₂def, hv₂def]
    exact h'
  have hD₂F : InFStar D₂ := by
    rw [hD₂def]
    exact hIF.conjugate r
  have hDle : D ≤ D₂ := by
    intro d hd
    rw [hD₂def, sec63P_mem_conjugate_iff]
    exact hDI (sec63P_conj_mem_conjugate hr hd)
  have hvNorm : v ∈ normalizer (D₂ : Set G) := by
    refine sec63P_conjugate_eq_iff.mp ?_
    have h' : CFSG.conjugate (CFSG.conjugate I r) v = CFSG.conjugate I r := by
      rw [l34g_conjugate_conjugate, hrv, ← l34g_conjugate_conjugate, hIv]
    rwa [hD₂def]
  have hD' : IsComponentIn D (D₂ ⊓ centralizer ({v} : Set G)) :=
    hDv.mono (le_inf hDle hDv.1) inf_le_right
  obtain ⟨hu₂, B, hB⟩ := hKB G D₂ hD₂F v hv hvNorm D hD' u huD hDI4
  have hdat : Sec3PocketData v₂ D₂ u B :=
    l34g_pocketData_of_pocketIn hv₂ hD₂ hD₂F hu₂ hB
  have hv₂mem : v₂ ∈ I := by
    refine hDI ?_
    rw [sec63P_mem_conjugate_iff]
    rw [show r * v₂ * r⁻¹ = u by rw [hv₂def]; group]
    exact huD
  exact hA v₂ u D₂ B hdat (Subgroup.mem_sup_left (le_fstarLayer hI hIF hv₂mem))

end CFSG.OddStandard.SmallF3.Omega
