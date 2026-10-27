module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Open.GoldschmidtStronglyClosedAbelianMilestoneDefs
public import CFSG.Open.TimmesfeldLargeExtraspecialMilestoneDefs
public import CFSG.Open.SignalizerFunctorDefs
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.GroupTheory.Fitting.SelfCentralizingComponent

public section

namespace CFSG.Adapters

open CFSG.Open

variable (G : Type*) [Group G]

theorem goldschmidtLayer_eq_componentClassification :
    goldschmidtLayer G = CFSG.ComponentClassification.Layer.subgroup G :=
  rfl

theorem goldschmidtLayer_eq_foundations : goldschmidtLayer G = CFSG.layer G :=
  (CFSG.layer_eq_componentClassification G).symm

theorem timmesfeldFitting_eq_foundations : timmesfeldFitting G = CFSG.fittingSubgroup G :=
  rfl

theorem timmesfeldLayer_eq_componentClassification :
    timmesfeldLayer G = CFSG.ComponentClassification.Layer.subgroup G :=
  rfl

theorem timmesfeldLayer_eq_foundations : timmesfeldLayer G = CFSG.layer G :=
  (CFSG.layer_eq_componentClassification G).symm

theorem timmesfeldFStar_eq_componentClassification :
    timmesfeldFStar G = CFSG.ComponentClassification.GeneralizedFitting.subgroup G :=
  rfl

theorem timmesfeldFStar_eq_foundations : timmesfeldFStar G = CFSG.generalizedFitting G :=
  (CFSG.generalizedFitting_eq_componentClassification G).symm

theorem centralizer_timmesfeldFStar_le [Finite G] :
    Subgroup.centralizer (timmesfeldFStar G : Set G) ≤ timmesfeldFStar G :=
  CFSG.ComponentClassification.GeneralizedFitting.centralizer_le G

theorem signalizerGeneralizedFitting_eq_componentClassification :
    signalizerGeneralizedFitting G = CFSG.ComponentClassification.GeneralizedFitting.subgroup G :=
  rfl

theorem signalizerGeneralizedFitting_eq_foundations :
    signalizerGeneralizedFitting G = CFSG.generalizedFitting G :=
  (CFSG.generalizedFitting_eq_componentClassification G).symm

theorem centralizer_signalizerGeneralizedFitting_le [Finite G] :
    Subgroup.centralizer (signalizerGeneralizedFitting G : Set G) ≤ signalizerGeneralizedFitting G :=
  CFSG.ComponentClassification.GeneralizedFitting.centralizer_le G

theorem centralizer_generalizedFitting_le_fittingSubgroup [Finite G] :
    Subgroup.centralizer (CFSG.generalizedFitting G : Set G) ≤ CFSG.fittingSubgroup G := by
  rw [CFSG.generalizedFitting_eq_componentClassification]
  exact CFSG.ComponentClassification.GeneralizedFitting.centralizer_le_fitting G

theorem generalizedFitting_eq_of_normal_simple_of_centralizer_eq_bot {G : Type*} [Group G]
    [Finite G] (N : Subgroup G) [N.Normal] [IsSimpleGroup N] (hnc : ∃ x y : N, x * y ≠ y * x)
    (hC : Subgroup.centralizer (N : Set G) = ⊥) : CFSG.generalizedFitting G = N :=
  CFSG.generalizedFitting_eq_of_isComponent_of_centralizer_eq_bot N
    ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1,
      (inferInstance : N.Normal).isSubnormal⟩ hC

theorem generalizedFitting_eq_top_of_isSimpleGroup [Finite G] [IsSimpleGroup G] :
    CFSG.generalizedFitting G = ⊤ := by
  have hN : (CFSG.generalizedFitting G).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  rcases hN.eq_bot_or_eq_top with h | h
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (1 : G)
    have h1 := CFSG.centralizer_generalizedFitting_le G
    rw [h] at h1
    have hxc : x ∈ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hm
      rw [hm, one_mul, mul_one]
    exact hx (Subgroup.mem_bot.mp (h1 hxc))
  · exact h

theorem centralizer_generalizedFitting_eq_bot_of_isSimpleGroup [Finite G]
    (hF : IsSimpleGroup (CFSG.generalizedFitting G))
    (hnab : ∃ a b : CFSG.generalizedFitting G, a * b ≠ b * a) :
    Subgroup.centralizer (CFSG.generalizedFitting G : Set G) = ⊥ := by
  set F := CFSG.generalizedFitting G
  have hle : Subgroup.centralizer (F : Set G) ≤ F := CFSG.centralizer_generalizedFitting_le G
  have hcenter : Subgroup.center F = ⊥ := by
    rcases hF.eq_bot_or_eq_top_of_normal (Subgroup.center F) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnab
      exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a) hab
  rw [eq_bot_iff]
  intro x hx
  have hxF := hle hx
  have : (⟨x, hxF⟩ : F) ∈ Subgroup.center F := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx g g.2)
  rw [hcenter, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val this

end CFSG.Adapters
