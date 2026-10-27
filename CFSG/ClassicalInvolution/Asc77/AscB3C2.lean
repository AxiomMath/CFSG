module

public import CFSG.ClassicalInvolution.Asc77.AscB3C1
public import CFSG.ClassicalInvolution.Asc77.AscR31Recog
public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace B3C

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)

local notation "Sp₄" F => CFSG.Assembly.LowTwoRank.StatedSp 2 F

@[expose] def SymplecticPhanPair (F : Type) [Field F] (h2 : (2 : F) ≠ 0) {X : Type} [Group X]
    (W U V : Subgroup X) : Prop :=
  ∃ (θ : (Sp₄ F) →* X) (c : Sp₄ F), θ.range = W ∧
    θ.ker ≤ Subgroup.center (Sp₄ F) ∧
    Function.Injective (θ.comp ((MulAut.conj c⁻¹).toMonoidHom.comp (longBlock F 2 1))) ∧
    ((longBlock F 2 1).range.map (MulAut.conj c⁻¹).toMonoidHom).map θ = U ∧
    ((twShort h2).range.map (MulAut.conj c⁻¹).toMonoidHom).map θ = V

variable (p f : ℕ) [Fact p.Prime]

section CIT40


@[expose] def PhanB3Recognition : Prop :=
  p ^ f % 4 = 3 → ∀ hp2 : p ≠ 2, 5 ≤ p ^ f → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (Ω : Set (Subgroup G)), ConjInvariant Ω → ∀ U : Fin 3 → Subgroup G, U 0 ∈ Ω →
      (∀ J ∈ Ω, ∃ g : G, J = conjSub g (U 0)) → Commutes (U 0) (U 2) →
      (∃ W₁, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W₁ (U 0) (U 1)) →
      (∃ W₂, SymplecticPhanPair (GaloisField p f) (ModelFacts.two_ne_zero_galoisField f hp2) W₂
        (U 1) (U 2)) → ⨆ k, U k = ⊤ →
        ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaOdd ∧ D.rank i = 3

@[expose] def C23_phanChainB3 : Prop :=
  p ^ f % 4 = 3 → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G) (hs : Hyp23Setting p f Ω K K' z),
      Hyp23bData Ω K K' W z u e g →
        (alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥ ∧ rLayer Ω e ⊔ rLayer Ω u = ⊤) →
        LayerOrthType p f Ω e 6 (piSign p f) → LayerOrthType p f Ω u 5 true →
          ∃ U : Fin 3 → Subgroup G, U 0 ∈ Ω ∧ Commutes (U 0) (U 2) ∧
            (∃ W₁, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W₁ (U 0) (U 1)) ∧
            (∃ W₂, SymplecticPhanPair (GaloisField p f)
              (ModelFacts.two_ne_zero_galoisField f hs.stand.odd) W₂ (U 1) (U 2)) ∧
            ⨆ k, U k = ⊤

variable {p f}

theorem c23_recogB3_of_phan (hP : PhanB3Recognition p f) (hC : C23_phanChainB3 p f) :
    R31.C23_recogB3 p f := by
  intro hq G _ _ _ Ω K K' W z u e g hs hd hα hE hY
  have hΩ := hs.stand.hyp.conjInvariant
  obtain ⟨U, hU0, hc02, hp01, hp12, hgen⟩ := hC hq G Ω K K' W z u e g hs hd hα hE hY
  have hcls : ∀ J ∈ Ω, ∃ g : G, J = conjSub g (U 0) := by
    intro J hJ
    obtain ⟨g, hg⟩ := (hs.stand.of_mem hU0).trans J hJ
    exact ⟨g, hg.symm⟩
  exact hP hq hs.stand.odd hs.stand.five G Ω hΩ U hU0 hcls hc02 hp01 hp12 hgen

end CIT40

end B3C

end CFSG.ClassicalInvolution.Asc77
