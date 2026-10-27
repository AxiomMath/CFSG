module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Pocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Simp
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem l34g_simpleFStar_of_inFStar [Finite G] {J : Subgroup G} (hJ : InFStar J) :
    SimpleFStarQuotient (↥J ⧸ center ↥J) := by
  have hq : CFSG.IsQuasisimple ↥J := inFStar_isQuasisimple hJ
  have hJc := hJ
  unfold InFStar IsFStarGroup IsFGroup at hJc
  have hne : oddCore ↥J ≠ ⊤ := by
    intro htop
    haveI : Subsingleton (↥J ⧸ oddCore ↥J) := by
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    rcases hJc with ⟨-, hQ⟩ | ⟨-, hS⟩
    · rcases hQ with hΩ | hU
      · haveI : IsSimpleGroup (↥J ⧸ oddCore ↥J) :=
          (l34g_simple_of_simpleFStar (Or.inl hΩ)).1
        exact not_subsingleton (↥J ⧸ oddCore ↥J) inferInstance
      · obtain ⟨hcard, -⟩ := hU
        have h1 : Nat.card (center (↥J ⧸ oddCore ↥J)) = 1 := by
          rw [Nat.card_eq_one_iff_unique]
          exact ⟨inferInstance, ⟨1⟩⟩
        omega
    · haveI : IsSimpleGroup (↥J ⧸ oddCore ↥J) :=
        (l34g_simple_of_simpleFStar (Or.inr hS)).1
      exact not_subsingleton (↥J ⧸ oddCore ↥J) inferInstance
  have hOZ : oddCore ↥J ≤ center ↥J :=
    (CFSG.LocalCores.quasisimple_normal_subgroups hq inferInstance).resolve_left hne
  haveI : Group.IsPerfect ↥J := hq.1
  have hcenter : (center ↥J).map (QuotientGroup.mk' (oddCore ↥J)) =
      center (↥J ⧸ oddCore ↥J) :=
    CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel
      (QuotientGroup.mk' (oddCore ↥J)) (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact hOZ)
  have e : (↥J ⧸ center ↥J) ≃* (↥J ⧸ oddCore ↥J) ⧸ center (↥J ⧸ oddCore ↥J) :=
    (QuotientGroup.quotientQuotientEquivQuotient (oddCore ↥J) (center ↥J) hOZ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hcenter)
  rcases hJc with ⟨-, hQ⟩ | ⟨-, hS⟩
  · rcases hQ with hΩ | hU
    ·
      have hSF : SimpleFStarQuotient (↥J ⧸ oddCore ↥J) := Or.inl hΩ
      have hcQ : center (↥J ⧸ oddCore ↥J) = ⊥ := (l34g_simple_of_simpleFStar hSF).2
      have eis : (↥J ⧸ oddCore ↥J) ⧸ center (↥J ⧸ oddCore ↥J) ≃* (↥J ⧸ oddCore ↥J) :=
        (QuotientGroup.quotientMulEquivOfEq hcQ).trans QuotientGroup.quotientBot
      exact l34g_simpleFStar_of_mulEquiv (e.trans eis).symm hSF
    ·
      obtain ⟨-, hm⟩ := hU
      exact Or.inl (Or.inr (Or.inr (Or.inl (LieModel.of_mulEquiv e.symm hm))))
  ·
    have hSF : SimpleFStarQuotient (↥J ⧸ oddCore ↥J) := Or.inr hS
    have hcQ : center (↥J ⧸ oddCore ↥J) = ⊥ := (l34g_simple_of_simpleFStar hSF).2
    have eis : (↥J ⧸ oddCore ↥J) ⧸ center (↥J ⧸ oddCore ↥J) ≃* (↥J ⧸ oddCore ↥J) :=
      (QuotientGroup.quotientMulEquivOfEq hcQ).trans QuotientGroup.quotientBot
    exact l34g_simpleFStar_of_mulEquiv (e.trans eis).symm hSF

end CFSG.OddStandard.SmallF3.Omega
