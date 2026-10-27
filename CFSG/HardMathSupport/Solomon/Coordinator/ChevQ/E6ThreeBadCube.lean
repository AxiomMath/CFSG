module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCoreAssembly
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofWeylWord
public import CFSG.Monster.B.E6.StdF4RadicalRoots

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.ComponentClassification.CatLeafProof (weylWordElt)

theorem map_congr_map_congr_map_congr {X : Type*} [Group X] (E : Subgroup (MulAut X))
    (φ₁ φ₂ φ₃ : MulAut X) :
    ((E.map (MulAut.congr φ₁).toMonoidHom).map (MulAut.congr φ₂).toMonoidHom).map
        (MulAut.congr φ₃).toMonoidHom = E.map (MulAut.congr (φ₃ * φ₂ * φ₁)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

@[expose] def e6D0Char {K : Type} [Field K] (ω : Kˣ) : Fin Tag.E6.rank → Kˣ :=
  ![1, ω, 1, 1, ω, ω]

@[expose] def e6BadWord : List (Fin Tag.E6.rank) :=
  [2, 0, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4]


@[expose] def e6BadX (K : Type) [Field K] (c : Kˣ) : MulAut (adjointGroup Tag.E6 K) :=
  MulAut.conj (weylWordElt .E6 K e6BadWord) * rootDiagAutHom .E6 K ![1, 1, c, 1, 1, 1]

@[expose] def e6BadCube (K : Type) [Field K] (ω c : Kˣ) :
    Subgroup (MulAut (adjointGroup Tag.E6 K)) :=
  Subgroup.closure {MulAut.conj (e6LineElt ω), rootDiagAutHom .E6 K (e6D0Char ω), e6BadX K c}

@[expose] def E6ThreeNotAll24NF : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 3 ∣ Nat.card K - 1 → Nat.card K ≠ 4 →
    ∀ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      E ≤ e6Inndiag K → ¬ E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) →
      ¬ E6NormalizesR K E → ¬ E6InnerAll24 K E →
      ∃ (ω c : Kˣ) (φ : MulAut (adjointGroup Tag.E6 K)), ω ^ 3 = 1 ∧ ω ≠ 1 ∧
        E.map (MulAut.congr φ).toMonoidHom = e6BadCube K ω c

@[expose] def E6NotAll24Census : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 3 ∣ Nat.card K - 1 → Nat.card K ≠ 4 →
    ∀ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      E ≤ e6Inndiag K → ¬ E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) →
      ¬ E6NormalizesR K E → ¬ E6InnerAll24 K E →
      ∃ s u : adjointGroup Tag.E6 K, MulAut.conj s ∈ E ∧ MulAut.conj u ∈ E ∧
        MulAut.conj u ∉ Subgroup.zpowers (MulAut.conj s) ∧
        Module.finrank K (LinearMap.ker
          (((s : ModGL .E6 K) : Module.End K (RootModule .E6 K)) - 1)) = 24 ∧
        ∀ k : ℕ, k < 3 → Module.finrank K (LinearMap.ker
          ((((s ^ k * u : adjointGroup Tag.E6 K) : ModGL .E6 K) :
            Module.End K (RootModule .E6 K)) - 1)) = 30

@[expose] def E6ThreeNotAll24NFA : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 3 ∣ Nat.card K - 1 → Nat.card K ≠ 4 →
    ∀ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      E ≤ e6Inndiag K → ¬ E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) →
      ¬ E6NormalizesR K E → ¬ E6InnerAll24 K E →
      ∃ ω : Kˣ, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ ∃ φ ∈ e6Inndiag K,
        MulAut.conj (e6LineElt ω) ∈ E.map (MulAut.congr φ).toMonoidHom ∧
        rootDiagAutHom .E6 K (e6D0Char ω) ∈ E.map (MulAut.congr φ).toMonoidHom

@[expose] def E6ThreeNotAll24NFB1 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 3 ∣ Nat.card K - 1 → Nat.card K ≠ 4 →
    ∀ ω : Kˣ, ω ^ 3 = 1 → ω ≠ 1 →
    ∀ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      E ≤ e6Inndiag K → ¬ E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) →
      ¬ E6NormalizesR K E → MulAut.conj (e6LineElt ω) ∈ E →
      rootDiagAutHom .E6 K (e6D0Char ω) ∈ E →
      ∃ φ ∈ e6Inndiag K, ∃ (ν : List (Fin Tag.E6.rank)) (a : Fin Tag.E6.rank → Kˣ),
        MulAut.conj (e6LineElt ω) ∈ E.map (MulAut.congr φ).toMonoidHom ∧
        rootDiagAutHom .E6 K (e6D0Char ω) ∈ E.map (MulAut.congr φ).toMonoidHom ∧
        MulAut.conj (weylWordElt .E6 K ν) * rootDiagAutHom .E6 K a ∈
          E.map (MulAut.congr φ).toMonoidHom ∧
        MulAut.conj (weylWordElt .E6 K ν) * rootDiagAutHom .E6 K a ∉
          CFSG.Fischer.innerAut (adjointGroup Tag.E6 K)

@[expose] def E6ThreeNotAll24NFB2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 3 ∣ Nat.card K - 1 → Nat.card K ≠ 4 →
    ∀ ω : Kˣ, ω ^ 3 = 1 → ω ≠ 1 →
    ∀ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      E ≤ e6Inndiag K → ¬ E6NormalizesR K E → MulAut.conj (e6LineElt ω) ∈ E →
      rootDiagAutHom .E6 K (e6D0Char ω) ∈ E →
      ∀ (ν : List (Fin Tag.E6.rank)) (a : Fin Tag.E6.rank → Kˣ),
        MulAut.conj (weylWordElt .E6 K ν) * rootDiagAutHom .E6 K a ∈ E →
        MulAut.conj (weylWordElt .E6 K ν) * rootDiagAutHom .E6 K a ∉
          CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) →
        ∃ (c : Kˣ) (φ : MulAut (adjointGroup Tag.E6 K)),
          E.map (MulAut.congr φ).toMonoidHom = e6BadCube K ω c

theorem e6Cube_map_congr {K : Type} [Field K] [Finite K] {φ : MulAut (adjointGroup Tag.E6 K)}
    (hφ : φ ∈ e6Inndiag K) {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 3) (hED : E ≤ e6Inndiag K)
    (hEi : ¬ E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K)) (hER : ¬ E6NormalizesR K E) :
    IsElemAbelian 3 (E.map (MulAut.congr φ).toMonoidHom) ∧
      Nat.card (E.map (MulAut.congr φ).toMonoidHom) = 3 ^ 3 ∧
      E.map (MulAut.congr φ).toMonoidHom ≤ e6Inndiag K ∧
      ¬ E.map (MulAut.congr φ).toMonoidHom ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) ∧
      ¬ E6NormalizesR K (E.map (MulAut.congr φ).toMonoidHom) := by
  refine ⟨hE.map _, ?_, ?_, ?_, fun h => hER (e6NormalizesR_of_map_congr φ h)⟩
  · rw [Subgroup.card_map_of_injective (MulAut.congr φ).injective, hEc]
  · rintro _ ⟨ε, hε, rfl⟩
    rw [congr_toMonoidHom_apply]
    exact mul_mem (mul_mem hφ (hED hε)) (inv_mem hφ)
  · intro h
    apply hEi
    intro ε hε
    have h1 := h ⟨ε, hε, rfl⟩
    rw [congr_toMonoidHom_apply] at h1
    have h2 := CFSG.Fischer.innerAut_normal.conj_mem _ h1 φ⁻¹
    rwa [inv_inv, show φ⁻¹ * (φ * ε * φ⁻¹) * φ = ε by group] at h2

theorem e6ThreeNotAll24NF_of_parts (hA : E6ThreeNotAll24NFA) (hB1 : E6ThreeNotAll24NFB1)
    (hB2 : E6ThreeNotAll24NFB2) : E6ThreeNotAll24NF := by
  intro K _ _ hK3 hK hK4 E hE hEc hED hEi hER hA24
  obtain ⟨ω, h3, h1, φ₁, hφ₁, hh₁, hd₁⟩ := hA K hK3 hK hK4 E hE hEc hED hEi hER hA24
  obtain ⟨hE₁, hEc₁, hED₁, hEi₁, hER₁⟩ := e6Cube_map_congr hφ₁ hE hEc hED hEi hER
  obtain ⟨φ₂, hφ₂, ν, a, hh₂, hd₂, hX, hXi⟩ :=
    hB1 K hK3 hK hK4 ω h3 h1 _ hE₁ hEc₁ hED₁ hEi₁ hER₁ hh₁ hd₁
  obtain ⟨hE₂, hEc₂, hED₂, -, hER₂⟩ := e6Cube_map_congr hφ₂ hE₁ hEc₁ hED₁ hEi₁ hER₁
  obtain ⟨c, φ₃, hc⟩ := hB2 K hK3 hK hK4 ω h3 h1 _ hE₂ hEc₂ hED₂ hER₂ hh₂ hd₂ ν a hX hXi
  exact ⟨ω, c, φ₃ * φ₂ * φ₁, h3, h1, by rw [← map_congr_map_congr_map_congr, hc]⟩

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
