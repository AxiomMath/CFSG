module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXPkLift
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXPkMap
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.Assembly.ComponentTypeDefs
import CFSG.ClassicalInvolution.Balance.Basic
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Lift

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem m6z_oddCentralCover_mk_oddCore {H : Type} [Group H] [Finite H]
    (hq : CFSG.IsQuasisimple H) :
    OddCentralCover (QuotientGroup.mk' (oddCore H)) := by
  have hker : (QuotientGroup.mk' (oddCore H)).ker = oddCore H :=
    QuotientGroup.ker_mk' (oddCore H)
  have hcen : oddCore H ≤ Subgroup.center H :=
    CFSG.ClassicalInvolution.Balance.oddCore_le_center_of_isQuasisimple
      (⟨hq.1.commutator_eq_top, hq.2.1⟩ : CFSG.Open.IsQuasisimple H)
  have hodd : Odd (Nat.card (oddCore H)) :=
    CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog.odd_card_oddCore
  exact ⟨QuotientGroup.mk'_surjective _,
    by rw [hker]; exact hcen,
    by rw [hker]; exact hodd⟩

theorem m6z_ncard_pocketed_eq [Finite G] {L : Subgroup G} (hL : IsQuasisimple ↥L) :
    {z : G | z ∈ L ∧ IsI4PlusIn L z}.ncard =
      Nat.card {x : ↥L ⧸ oddCore ↥L // IsI4PlusIn (⊤ : Subgroup (↥L ⧸ oddCore ↥L)) x} := by
  let ρ : ↥L →* (↥L ⧸ oddCore ↥L) := QuotientGroup.mk' (oddCore ↥L)
  have hcov : OddCentralCover ρ := m6z_oddCentralCover_mk_oddCore hL
  let S : Set G := {z : G | z ∈ L ∧ IsI4PlusIn L z}
  let T : Type _ := {x : ↥L ⧸ oddCore ↥L // IsI4PlusIn (⊤ : Subgroup (↥L ⧸ oddCore ↥L)) x}
  have hF : ∀ z : ↥S, IsI4PlusIn (⊤ : Subgroup (↥L ⧸ oddCore ↥L)) (ρ ⟨z.1, z.2.1⟩) := by
    intro z
    have hsub : IsI4PlusIn (L.subgroupOf L) (⟨z.1, z.2.1⟩ : ↥L) :=
      l34g_x_isI4PlusIn_subgroupOf le_rfl z.2.1 z.2.2
    have htop : IsI4PlusIn (⊤ : Subgroup ↥L) (⟨z.1, z.2.1⟩ : ↥L) := by
      rwa [Subgroup.subgroupOf_self] at hsub
    have hmap := l34g_x_isI4PlusIn_map hcov htop
    have hm : ((⊤ : Subgroup ↥L).map ρ) = ⊤ :=
      Subgroup.map_top_of_surjective ρ hcov.surjective
    rwa [hm] at hmap
  let F : ↥S → T := fun z => ⟨ρ ⟨z.1, z.2.1⟩, hF z⟩
  have hinj : Function.Injective F := by
    intro z z' hzz'
    have hρ : ρ ⟨z.1, z.2.1⟩ = ρ ⟨z'.1, z'.2.1⟩ :=
      congrArg (fun y : T => (y : ↥L ⧸ oddCore ↥L)) hzz'
    have hz2 : (⟨z.1, z.2.1⟩ : ↥L) * ⟨z.1, z.2.1⟩ = 1 := by
      apply Subtype.ext
      change z.1 * z.1 = 1
      rw [← pow_two, ← z.2.2.1]
      exact pow_orderOf_eq_one z.1
    have hz2' : (⟨z'.1, z'.2.1⟩ : ↥L) * ⟨z'.1, z'.2.1⟩ = 1 := by
      apply Subtype.ext
      change z'.1 * z'.1 = 1
      rw [← pow_two, ← z'.2.2.1]
      exact pow_orderOf_eq_one z'.1
    have heq := hcov.eq_of_mul_self_eq_one hz2 hz2' hρ
    exact Subtype.ext (congrArg (fun y : ↥L => (y : G)) heq)
  have hsurj : Function.Surjective F := by
    intro x
    have hx2 : x.1 * x.1 = 1 := by
      rw [← pow_two, ← x.2.1]
      exact pow_orderOf_eq_one x.1
    obtain ⟨w, hww, hwρ⟩ := hcov.exists_mul_self_eq_one_lift hx2
    have hItop : IsI4PlusIn (⊤ : Subgroup ↥L) w :=
      l34g_x_isI4PlusIn_top_of_cover hcov hww (by rw [hwρ]; exact x.2)
    have hIL : IsI4PlusIn L (w : G) := isI4PlusIn_of_top w.2 hItop
    refine ⟨⟨(w : G), ⟨w.2, hIL⟩⟩, ?_⟩
    apply Subtype.ext
    change ρ w = x.1
    exact hwρ
  have hcard : Nat.card ↥S = Nat.card T := Nat.card_eq_of_bijective F ⟨hinj, hsurj⟩
  rw [← Nat.card_coe_set_eq]
  exact hcard

end CFSG.OddStandard.SmallF3.Omega
