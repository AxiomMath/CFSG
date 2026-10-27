module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GPocketP
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GDiag
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GT
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTrans

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec3_pocket_level_step {G : Type} [Group G] [Finite G] (hKA : Asc82FactPocketComp)
    (hKB : Asc82FactPocketLift) (hLB : AschLBalance G) (hA2 : AschA2 G) {x y : G}
    {X K : Subgroup G} (hD : Sec3PocketData x X y K) {v : G} (hv : orderOf v = 2)
    (hvx : v * x = x * v) (hvy : v * y = y * v) (hvK : K ≤ centralizer ({v} : Set G))
    (hvc : ∀ c ∈ centralizer (X : Set G), v ≠ y * c) :
    ∃ D : Subgroup G, IsComponentIn D (centralizer ({v} : Set G)) ∧ InFStar D ∧
      ((CFSG.conjugate D x = D ∧ ∃ K' : Subgroup G, Sec3PocketData v D y K') ∨
        (CFSG.conjugate D x ≠ D ∧ ∃ u₁ ∈ D, ∃ K₁ : Subgroup G,
          y = u₁ * (x * u₁ * x⁻¹) ∧ Sec3PocketData v D u₁ K₁)) := by
  have hx : orderOf x = 2 := hD.involution_x
  have hxv : x * v = v * x := hvx.symm
  obtain ⟨J, hJX, hJF, hyJ, hJ4⟩ := hKA G X hD.inFStar y K hD.involution_y
    (l34g_sl23PocketIn_of_data hD) v hv (l34g_normalizes_of_data hD hvx hvy) hvK hvc
  have hJ : IsComponentIn J (centralizer ({x, v} : Set G)) := by
    rw [centralizer_pair_eq_inf]
    exact sec63P_isComponentIn_of_subnormal hD.component.1 hD.component.2.2 hJX
  have hJcx : J ≤ centralizer ({x} : Set G) := (hJX.le.trans inf_le_left).trans hD.component.1
  obtain ⟨D, hDv, hJD⟩ := hLB x v hx hv hxv J hJ
  have hDF : InFStar D := hA2 x v hx hv hxv J D hJ hDv hJD hJF
  refine ⟨D, hDv, hDF, ?_⟩
  have hxC : x ∈ centralizer ({v} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hxv
  by_cases hDx : CFSG.conjugate D x = D
  ·
    refine Or.inl ⟨hDx, ?_⟩
    have hJle : J ≤ D := by
      have := hJD
      rwa [hDx, sup_idem] at this
    have hJD' : IsComponentIn J (D ⊓ centralizer ({x} : Set G)) := by
      refine hJ.mono (le_inf hJle hJcx) ?_
      rw [centralizer_pair_eq_inf]
      exact (inf_le_inf_right _ hDv.1).trans (inf_comm _ _).le
    obtain ⟨-, B, hB⟩ := hKB G D hDF x hx (sec63P_conjugate_eq_iff.mp hDx) J hJD' y hyJ hJ4
    exact ⟨B, l34g_pocketData_of_pocketIn hv hDv hDF hD.involution_y hB⟩
  ·
    refine Or.inr ⟨hDx, ?_⟩
    have hDxv : IsComponentIn (CFSG.conjugate D x) (centralizer ({v} : Set G)) :=
      hDv.conjugate hxC
    have hcomm : ∀ a ∈ D, ∀ c ∈ CFSG.conjugate D x, a * c = c * a :=
      hDv.commute_of_ne hDxv (Ne.symm hDx)
    have hsupC : D ⊔ CFSG.conjugate D x ≤ centralizer ({v} : Set G) :=
      sup_le hDv.1 hDxv.1
    have hJW : IsComponentIn J ((D ⊔ CFSG.conjugate D x) ⊓ centralizer ({x} : Set G)) := by
      refine hJ.mono (le_inf hJD hJcx) ?_
      rw [centralizer_pair_eq_inf]
      exact (inf_le_inf_right _ hsupC).trans (inf_comm _ _).le
    have hdiag := l34g_diag_eq hx hDv.isQuasisimple hcomm hJD hJW
    obtain ⟨u₁, hu₁D, hy, hu₁⟩ := sec3_pocket_diag_transport hx hxv hDv hDF hDx hdiag hJ4
    obtain ⟨hu₁2, B, hB⟩ := hu₁
    exact ⟨u₁, hu₁D, B, hy, l34g_pocketData_of_pocketIn hv hDv hDF hu₁2 hB⟩

end CFSG.OddStandard.SmallF3.Omega
