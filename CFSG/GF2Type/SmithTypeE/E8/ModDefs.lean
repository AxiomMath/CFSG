module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.E7Rep
public import CFSG.LocalAnalysis.SeitzReduction.EPilotFusionEntrywise
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots
public import CFSG.LargeExtraspecial.S14Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S14
open CFSG.LieType.Chevalley (parabolicRadical)
open CFSG.LieType.Steinberg.Minuscule (e7Data)
open CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors (e7Rep56 e7Y56 e7n6)
open CFSG.SeitzReduction (highRoot)
open CFSG.SeitzReduction.EPilot (pinnedElt)

noncomputable abbrev QA : Subgroup (ModGL .E7 (ZMod 2)) :=
  parabolicRadical .E7 (ZMod 2) {i | i ≠ e7n6}

@[expose] def weightVec : Set (Fin e7Data.d →₀ ZMod 2) :=
  Set.range fun g : ↥(adjointGroup .E7 (ZMod 2)) => e7Rep56 (ZMod 2) g e7Y56

@[expose] def collSpace (w : Fin e7Data.d →₀ ZMod 2) : Set (Fin e7Data.d →₀ ZMod 2) :=
  {u | ∃ g : ↥(adjointGroup .E7 (ZMod 2)), e7Rep56 (ZMod 2) g e7Y56 = w ∧
    ∀ q : ↥(adjointGroup .E7 (ZMod 2)), (q : ModGL .E7 (ZMod 2)) ∈ QA →
      e7Rep56 (ZMod 2) q (e7Rep56 (ZMod 2) g⁻¹ u) - e7Rep56 (ZMod 2) g⁻¹ u ∈
        Submodule.span (ZMod 2) {e7Y56}}

variable {G : Type} [Group G] [Finite G]

@[expose] def SmithE8Equiv (S : Setting G) (φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2))
    (ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))) : Prop :=
  ∀ (m : S.Mbar) (v : S.Qt),
    φ (((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = e7Rep56 (ZMod 2) (ψ m) (φ v)

@[expose] def SmithE8Clauses123 (S : Setting G) (φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2))
    (ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))) : Prop :=
  SmithE8Equiv S φ ψ ∧
  (∀ c : G, IsConj S.z c → c ∈ S.QG → c ≠ S.z → φ (S.cl c) ∈ weightVec) ∧
  (∀ w ∈ weightVec, ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ φ (S.cl c) = w) ∧
  (∀ h b : G, h * S.z * h⁻¹ ∈ S.QG → h * S.z * h⁻¹ ≠ S.z → IsConj S.z b → b ∈ S.QG →
    b ≠ S.z → (b ∈ S.Qa h ↔ φ (S.cl b) ∈ collSpace (φ (S.cl (h * S.z * h⁻¹)))))

@[expose] def SmithE8Clause4 (S : Setting G) (ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))) : Prop :=
  ∀ (x : G) (hx : x ∈ S.M), IsConj S.z x → x ∉ S.QG →
    IsConj (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)) (ψ ⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩)

@[expose] def SmithE8Module : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 28 →
    LieModel S.Mbar .E7 0 2 1 →
      ∃ φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2),
        (∀ c : G, IsConj S.z c → c ∈ S.QG → c ≠ S.z → φ (S.cl c) ∈ weightVec) ∧
        (∀ w ∈ weightVec, ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ φ (S.cl c) = w) ∧
        (∀ h b : G, h * S.z * h⁻¹ ∈ S.QG → h * S.z * h⁻¹ ≠ S.z → IsConj S.z b → b ∈ S.QG →
          b ≠ S.z → (b ∈ S.Qa h ↔ φ (S.cl b) ∈ collSpace (φ (S.cl (h * S.z * h⁻¹))))) ∧
        (∀ x : G, IsConj S.z x → x ∈ S.M → x ∉ S.QG →
          ∃ g : ↥(adjointGroup .E7 (ZMod 2)),
            IsConj (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)) g ∧ ∀ y ∈ S.QG,
              φ (S.cl (x * y * x⁻¹)) = e7Rep56 (ZMod 2) g (φ (S.cl y)))

@[expose] def SmithE8Model : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 28 →
    LieModel S.Mbar .E7 0 2 1 →
      ∃ (φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2))
        (ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))),
        SmithE8Clauses123 S φ ψ ∧ SmithE8Clause4 S ψ

@[expose] def SmithE8Compat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 28 →
    LieModel S.Mbar .E7 0 2 1 →
      ∃ (φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2))
        (ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))),
        SmithE8Clauses123 S φ ψ ∧ SmithE8Clause4 S ψ ∧
        (∀ r : ↥(adjointGroup .E7 (ZMod 2)),
          IsConj (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)) r →
            ∃ (x : G) (hx : x ∈ S.M), IsConj S.z x ∧ x ∉ S.QG ∧
              ψ ⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ = r)

theorem smithE8Module_of_model (h : SmithE8Model) : SmithE8Module := by
  intro G _ _ _ S hw hU
  obtain ⟨φ, ψ, ⟨hE, h1, h2, h3⟩, h4⟩ := h G S hw hU
  refine ⟨φ, h1, h2, h3, fun x hxc hxM hxQ => ⟨ψ ⟨S.ρ ⟨x, hxM⟩, ⟨⟨x, hxM⟩, rfl⟩⟩,
    h4 x hxM hxc hxQ, fun y hy => ?_⟩⟩
  have e := hE ⟨S.ρ ⟨x, hxM⟩, ⟨⟨x, hxM⟩, rfl⟩⟩ (S.cl y)
  rw [← e]
  exact congrArg φ (S.ρ_cl ⟨x, hxM⟩ hy).symm

theorem smithE8Model_of_compat (h : SmithE8Compat) : SmithE8Model := by
  intro G _ _ _ S hw hU
  obtain ⟨φ, ψ, h123, h4, -⟩ := h G S hw hU
  exact ⟨φ, ψ, h123, h4⟩

end CFSG.GF2Type.SmithTypeE.E8
