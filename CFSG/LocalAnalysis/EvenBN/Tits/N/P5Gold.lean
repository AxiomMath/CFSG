module

public import CFSG.Goldschmidt.OddCore
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Gold

open Subgroup CFSG.Open CFSG.Goldschmidt

variable {X : Type} [Group X] [Finite X]

abbrev nc (A : Subgroup X) : Subgroup X := normalClosure (A : Set X)

abbrev Mbar (A : Subgroup X) : Type := ↥(nc A) ⧸ goldschmidtOddCore ↥(nc A)

abbrev proj (A : Subgroup X) : ↥(nc A) →* Mbar A :=
  QuotientGroup.mk' (goldschmidtOddCore ↥(nc A))

@[expose] def Abar (A : Subgroup X) : Subgroup (Mbar A) := (A.subgroupOf (nc A)).map (proj A)

@[expose] def Sbar (S A : Subgroup X) : Subgroup (Mbar A) := (S.subgroupOf (nc A)).map (proj A)

theorem unpack (hTop : TopStatement) (S : Sylow 2 X) {A : Subgroup X} (hAS : A ≤ S)
    (hab : IsMulCommutative A)
    (hcl : ∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ A) :
    pCore 2 (Mbar A) ⊔ goldschmidtLayer (Mbar A) = ⊤ ∧
    Abar A = pCore 2 (Mbar A) ⊔ closure {t | t ∈ Sbar (S : Subgroup X) A ⊓ goldschmidtLayer (Mbar A) ∧
      t ^ 2 = 1} ∧
    ∀ K : Subgroup (Mbar A), IsComponentOf K ⊤ → goldschmidtSimpleType (K ⧸ center K) :=
  milestone_of_topStatement hTop X S A hAS hab hcl

theorem oddCore_Mbar (A : Subgroup X) : goldschmidtOddCore (Mbar A) = ⊥ :=
  goldschmidtOddCore_quotient_eq_bot _

theorem R_le_Abar (hTop : TopStatement) (S : Sylow 2 X) {A : Subgroup X} (hAS : A ≤ S)
    (hab : IsMulCommutative A)
    (hcl : ∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ A) :
    pCore 2 (Mbar A) ≤ Abar A := by
  rw [(unpack hTop S hAS hab hcl).2.1]
  exact le_sup_left

theorem map_oddCore_le (A : Subgroup X) :
    (goldschmidtOddCore ↥(nc A)).map (nc A).subtype ≤ goldschmidtOddCore X := by
  rw [goldschmidtOddCore_eq_pPrimeCore, goldschmidtOddCore_eq_pPrimeCore]
  exact CFSG.Walter.map_pPrimeCore_le_of_isSubnormal (Subgroup.Normal.isSubnormal
    (Subgroup.normalClosure_normal))

theorem normal_of_layer_bot (hTop : TopStatement) (S : Sylow 2 X) {A : Subgroup X} (hAS : A ≤ S)
    (hab : IsMulCommutative A)
    (hcl : ∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ A)
    (hbot : goldschmidtLayer (Mbar A) = ⊥) :
    Abar A = ⊤ ∧ nc A ≤ A ⊔ goldschmidtOddCore X ∧ (A ⊔ goldschmidtOddCore X).Normal := by
  obtain ⟨h1, h2, -⟩ := unpack hTop S hAS hab hcl
  rw [hbot, sup_bot_eq] at h1
  have hT : {t | t ∈ Sbar (S : Subgroup X) A ⊓ (⊥ : Subgroup (Mbar A)) ∧ t ^ 2 = 1} ⊆ {1} := by
    rintro t ⟨ht, -⟩
    exact (Subgroup.mem_bot.1 ht.2)
  have hAbar : Abar A = ⊤ := by
    rw [h2, hbot, h1]
    exact top_sup_eq _
  have hle : nc A ≤ A ⊔ goldschmidtOddCore X := by
    intro m hm
    have hmem : proj A ⟨m, hm⟩ ∈ Abar A := by rw [hAbar]; trivial
    obtain ⟨a, ha, hae⟩ := hmem
    have ham : (a : X) ∈ A := Subgroup.mem_subgroupOf.1 ha
    have hker : a⁻¹ * (⟨m, hm⟩ : ↥(nc A)) ∈ goldschmidtOddCore ↥(nc A) := by
      rw [← QuotientGroup.eq]
      exact hae
    have hprod : (⟨m, hm⟩ : ↥(nc A)) = a * (a⁻¹ * (⟨m, hm⟩ : ↥(nc A))) := by group
    have hm' : m = (a : X) * ((a⁻¹ * (⟨m, hm⟩ : ↥(nc A)) : ↥(nc A)) : X) := by
      have := congrArg (fun y : ↥(nc A) => (y : X)) hprod
      simpa using this
    rw [hm']
    exact Subgroup.mul_mem_sup ham (map_oddCore_le A ⟨_, hker, rfl⟩)
  refine ⟨hAbar, hle, ?_⟩
  have heq : A ⊔ goldschmidtOddCore X = nc A ⊔ goldschmidtOddCore X :=
    le_antisymm (sup_le_sup_right Subgroup.le_normalClosure _) (sup_le hle le_sup_right)
  rw [heq]
  exact inferInstance

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Gold
