module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangRankOne
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangSylow
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Classical

set_option linter.unusedSectionVars false


theorem component_of_rankOneCentralizers {τ : Tag} {X K₂ : Type} [Field X] [Finite X]
    [Field K₂] [Algebra X K₂] {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card X + 1)
    (hinj : ∀ α, IsRoot τ α → Function.Injective (rootSL2 τ K₂ α))
    {Γ E : Subgroup (ModGL τ K₂)}
    (hEmem : ∀ h, h ∈ E ↔ h ∈ torusGroup τ K₂ ∧ h ^ p = 1)
    (hEle : E ≤ torusGroup τ K₂ ⊓ Γ)
    (hρ : ∀ α, IsRoot τ α → ∃ P : GL (Fin 2) K₂,
      (rootRankOneGroup τ K₂ α ⊓ Γ).comap (rootSL2 τ K₂ α) =
        (Matrix.SpecialLinearGroup.map (algebraMap X K₂)).range.map (conjSL P) ∧
      CFSG.IsQuasisimple ↥(rootRankOneGroup τ K₂ α ⊓ Γ))
    (hcent : ∀ a : Fin τ.rank → K₂ˣ, rootDiagUnit τ a ∈ torusGroup τ K₂ ⊓ Γ →
      orderOf (rootDiagUnit τ a) = p → rootCharKernel a ≠ ∅ →
        ∃ α, IsRoot τ α ∧ rootCharKernel a = {α, -α} ∧
          ⁅Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}, Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}⁆ =
            rootRankOneGroup τ K₂ α ⊓ Γ) :
    ∀ β : Fin τ.rank → ℤ, IsRoot τ β → ∀ a : Fin τ.rank → K₂ˣ,
      rootDiagUnit τ a ∈ E → rootDiagUnit τ a ≠ 1 → rootChar a β = 1 →
      ∃ L : Subgroup (ModGL τ K₂), rootRankOneGroup τ K₂ β ⊓ Γ ≤ L ∧
        L ≤ Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} ∧ CFSG.IsQuasisimple L ∧
        (L.subgroupOf (Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a})).IsSubnormal ∧
        ¬ Nat.Coprime p (Nat.card L) := by
  have : Fact p.Prime := ⟨hp⟩
  intro β hβ a hdE hd1 hχ
  obtain ⟨-, hdp⟩ := (hEmem _).1 hdE
  have hord : orderOf (rootDiagUnit τ a) = p := orderOf_eq_prime hdp hd1
  have hker : rootCharKernel a ≠ ∅ := Set.nonempty_iff_ne_empty.1 ⟨β, hβ, hχ⟩
  obtain ⟨α, hα, hkerα, hcomm⟩ := hcent a (hEle hdE) hord hker
  have hβα : β = α ∨ β = -α := by
    have : β ∈ rootCharKernel a := ⟨hβ, hχ⟩
    rw [hkerα] at this
    simpa using this
  have hRβ : rootRankOneGroup τ K₂ β = rootRankOneGroup τ K₂ α := by
    rcases hβα with rfl | rfl
    · rfl
    · exact CFSG.RankThree.PartOne.KE.rootRankOneGroup_neg hα
  obtain ⟨P, hP, hq⟩ := hρ α hα
  refine ⟨rootRankOneGroup τ K₂ α ⊓ Γ, by rw [hRβ], ?_, hq, ?_, ?_⟩
  · rw [← hcomm]
    exact commutator_self_le _
  · rw [← hcomm]
    exact isSubnormal_commutator_subgroupOf _
  · rw [← Nat.Prime.dvd_iff_not_coprime hp]
    exact dvd_card_of_comap_eq_conj (hinj α hα) inf_le_left P hP hpq

theorem isLangFrame_of_rankOneCentralizers {τ : Tag} {X K₂ : Type} [Field X] [Finite X]
    [Field K₂] [Algebra X K₂] [Finite K₂] {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card X + 1)
    (hinj : ∀ α, IsRoot τ α → Function.Injective (rootSL2 τ K₂ α))
    {Γ E : Subgroup (ModGL τ K₂)} (S₀ : Sylow p ↥Γ)
    (hS₀ : (S₀ : Subgroup ↥Γ) ≤ (torusGroup τ K₂ ⊓ Γ).subgroupOf Γ)
    (hEmem : ∀ h, h ∈ E ↔ h ∈ torusGroup τ K₂ ∧ h ^ p = 1)
    (hEle : E ≤ torusGroup τ K₂ ⊓ Γ)
    (hgen : ⨆ β : {β : Fin τ.rank → ℤ // IsRoot τ β}, rootRankOneGroup τ K₂ β.1 ⊓ Γ = Γ)
    (hρ : ∀ α, IsRoot τ α → ∃ P : GL (Fin 2) K₂,
      (rootRankOneGroup τ K₂ α ⊓ Γ).comap (rootSL2 τ K₂ α) =
        (Matrix.SpecialLinearGroup.map (algebraMap X K₂)).range.map (conjSL P) ∧
      CFSG.IsQuasisimple ↥(rootRankOneGroup τ K₂ α ⊓ Γ))
    (hcent : ∀ a : Fin τ.rank → K₂ˣ, rootDiagUnit τ a ∈ torusGroup τ K₂ ⊓ Γ →
      orderOf (rootDiagUnit τ a) = p → rootCharKernel a ≠ ∅ →
        ∃ α, IsRoot τ α ∧ rootCharKernel a = {α, -α} ∧
          ⁅Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}, Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}⁆ =
            rootRankOneGroup τ K₂ α ⊓ Γ) :
    IsLangFrame τ K₂ p Γ E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL τ K₂) := finite_modGL
  refine ⟨fun x hx => (hEle hx).1, fun x hx => (hEle hx).2, ?_, hgen, ?_⟩
  · intro F hFΓ hFp _
    exact exists_conj_le_of_sylow_torsion_modGL S₀ hS₀
      (fun x hx hxp => (hEmem x).2 ⟨hx.1, hxp⟩) hFΓ hFp
  · exact component_of_rankOneCentralizers hp hpq hinj hEmem hEle hρ hcent

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
