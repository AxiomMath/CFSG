module

public import CFSG.ClassicalInvolution.Q3.Q3AM289S4Stmt
public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LX
public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LExist
public import CFSG.ClassicalInvolution.Asc77.AscT8X4
public import CFSG.ClassicalInvolution.Asc77.AscT8YA3
public import CFSG.ClassicalInvolution.Q3.Q3AMPspLeaves
public import CFSG.ClassicalInvolution.Q3.Q3AMTri
public import CFSG.ClassicalInvolution.Q3.Q3T8B10
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T01
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T02
public import CFSG.ClassicalInvolution.Q3.Q3T8P26TH01

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM.S4L

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1


theorem shape_of_layerKind {X : Type} [Group X] {c : CompData} {Φ : Set (Subgroup X)} {zb : X}
    (hL : Q3AM.S4LayerKind c Φ zb) :
    ∃ ψ : c.G →* X, Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center c.G ∧
      (∀ L ∈ Φ, ∃ R ∈ c.fund, L = R.map ψ) ∧ (∃ R ∈ c.fund, R.map ψ ∈ Φ) ∧
      (∀ L ∈ Φ, Nat.card L = 24) ∧ (∃ f ∈ Subgroup.center c.G, ψ f = zb) := by
  obtain ⟨ι, -, D, i₁, hall, hk, f, hf, hfz⟩ := hL
  have key : ∃ ψ : (D.kind i₁).G →* X, Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center (D.kind i₁).G ∧
      (∀ L ∈ Φ, ∃ R ∈ (D.kind i₁).fund, L = R.map ψ) ∧ (∃ R ∈ (D.kind i₁).fund, R.map ψ ∈ Φ) ∧
      (∀ L ∈ Φ, Nat.card L = 24) ∧ (∃ f ∈ Subgroup.center (D.kind i₁).G, ψ f = zb) := by
    refine ⟨D.hom i₁, ?_, D.ker_le_center i₁, ?_, D.meets i₁, D.card_eq, ⟨f, hf, hfz⟩⟩
    · have h1 := D.generate
      have h2 : ⨆ i, (D.hom i).range = (D.hom i₁).range := by
        apply le_antisymm
        · exact iSup_le fun i => by rw [hall i]
        · exact le_iSup (fun i => (D.hom i).range) i₁
      rw [h2] at h1
      exact MonoidHom.range_eq_top.mp h1
    · intro L hL
      obtain ⟨i, R, hR, hLR⟩ := D.fundamental L hL
      obtain rfl := hall i
      exact ⟨R, hR, hLR⟩
  rw [hk] at key
  exact key

@[expose] def ModelPkg (c : CompData) : Prop :=
  Finite c.G ∧ ⁅(⊤ : Subgroup c.G), (⊤ : Subgroup c.G)⁆ = ⊤ ∧
    (∀ R ∈ c.fund, ∀ R' ∈ c.fund, ∃ g : c.G, R' = conjSub g R) ∧
    (∀ R ∈ c.fund, Nonempty (R ≃* SL(2, 𝔽₃))) ∧
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module 𝔽₃ V) (_ : FiniteDimensional 𝔽₃ V)
      (Q : QuadraticForm 𝔽₃ V) (θ : c.G →* (V ≃ₗ[𝔽₃] V)) (z₀ : c.G),
        CoverData Q θ c.fund z₀ ∧ VFrames Q ∧
          ∀ F₁ F₂ : Frame Q, F₂.La (-1) = LinearEquiv.neg 𝔽₃ * F₁.La (-1) → False

theorem s4LinkModelLeafAt_of_pkg {c : CompData} (hpkg : ModelPkg c) : Q3AM.S4LinkModelLeafAt c := by
  intro X _ _ Φ zb hΦ hL hP A hA a ha
  obtain ⟨hfin, hperf, hsingle, hsl2, V, _, _, _, Q, θ, z₀, D, hV, hopp⟩ := hpkg
  obtain ⟨ψ, hψs, hψk, hΦF, hmeets, hcard, hzb⟩ := shape_of_layerKind hL
  have hzbc := hL.zb_mem_center
  have htrans := trans_of_cover ψ hΦF hsingle
  obtain ⟨A₀, hA₀, a₀, ha₀, hF⟩ := exists_frameAt_of_cover ψ hψs hψk hperf D hV hopp hsl2 hsingle hΦ
    hΦF hmeets hcard hzb hP
  exact Q3AM.s4Frame_of_exists hzbc hΦ htrans hA₀ ha₀ hF hA ha

end CFSG.ClassicalInvolution.Q3.Q3AM.S4L
