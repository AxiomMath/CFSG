module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodRoot

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Commute

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem noFrobeniusInner_of_q_eq_two (S : LangSetup τ L p) (hq : S.D.q = 2)
    (D₁ : Subgroup (ModGL τ L)) : NoFrobeniusInner S D₁ := by
  intro r f j _ hr hqf hj0 hjf z _
  have hr2 := hr.two_le
  have hf2 : f < 2 := by
    by_contra hcon
    have h1 : r ^ 2 ≤ r ^ f := Nat.pow_le_pow_right hr.pos (not_lt.1 hcon)
    rw [← hqf, hq] at h1
    nlinarith
  omega

theorem centralizerTrivial_of_simple (S : LangSetup τ L p) (D₁ : Subgroup (ModGL τ L))
    (h : ∀ z : ModGL τ L, (∀ x ∈ rigidTestSet S D₁, Commute z x) →
      ∀ i : Fin τ.rank, ∀ x ∈ rootRankOneGroup τ L (Pi.single i 1), Commute z x) :
    CentralizerTrivial S D₁ := by
  intro z hzC hcomm
  have hle := commute_adjointGroup_of_simple (h z hcomm)
  have hcent : (⟨z, hzC⟩ : adjointGroup τ L) ∈ Subgroup.center (adjointGroup τ L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hle g g.2).eq.symm
  rw [center_adjointGroup_eq_bot_field, Subgroup.mem_bot] at hcent
  exact congrArg Subtype.val hcent

theorem pinnedX_mem_rootRankOneGroup {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hγ : γ = β ∨ γ = -β) (s : L) : pinnedX τ L γ s ∈ rootRankOneGroup τ L β := by
  rw [rootRankOneGroup_eq_rootSpan_pair hβ]
  exact pinnedX_mem_rootSpan (by rcases hγ with rfl | rfl <;> simp) s

theorem commute_rankOne_of_pinnedX_pm {z : ModGL τ L} {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (h₁ : ∀ s : L, Commute z (pinnedX τ L β s)) (h₂ : ∀ s : L, Commute z (pinnedX τ L (-β) s)) :
    ∀ x ∈ rootRankOneGroup τ L β, Commute z x := by
  intro x hx
  rw [rootRankOneGroup_eq_rootSpan_pair hβ] at hx
  have hle : rootSpan τ L {β, -β} ≤ Subgroup.centralizer {z} := by
    refine iSup₂_le fun γ hγ => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨s, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hγ with rfl | hγ
    · exact (h₁ s).eq.symm
    · rw [Set.mem_singleton_iff.1 hγ]
      exact (h₂ s).eq.symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm

theorem commute_pinnedX_add_of_commutator (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {z : ModGL τ L} {α β₀ : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ₀ : IsRoot τ β₀)
    (hne : α ≠ β₀) (hne' : α ≠ -β₀) (hsum : IsRoot τ (α + β₀))
    {R : ModGL τ L} (hR : ∀ s : L, Commute (pinnedX τ L α s) R) {c₀ : L} (hc₀ : c₀ ≠ 0)
    (hzα : ∀ s : L, Commute z (pinnedX τ L α s))
    (hzn : Commute z (pinnedX τ L β₀ c₀ * R)) :
    ∀ s : L, Commute z (pinnedX τ L (α + β₀) s) := by
  obtain ⟨hC, -⟩ := simply_laced_root_commutator_unit τ hτ hα hβ₀ hne hne'
  obtain ⟨hε, hform⟩ := hC hsum
  intro s
  set ε : L := ((commConst τ α β₀ (1, 1) : ℤ) : L) with hεdef
  have hε0 : ε ≠ 0 := by
    rcases hε with h | h <;> simp [hεdef, h]
  set a : L := s * (ε * c₀)⁻¹ with ha
  have hεa : ε * a * c₀ = s := by
    rw [ha]
    field_simp
  have hcomm : ⁅pinnedX τ L α a, pinnedX τ L β₀ c₀⁆ = pinnedX τ L (α + β₀) s := by
    rw [hform L a c₀, hεa]
  have hA : Commute z (pinnedX τ L α a) := hzα a
  have hcomm2 : Commute z ⁅pinnedX τ L α a, pinnedX τ L β₀ c₀ * R⁆ := by
    rw [commutatorElement_def]
    exact ((hA.mul_right hzn).mul_right hA.inv_right).mul_right hzn.inv_right
  have hRA : R * (pinnedX τ L α a)⁻¹ = (pinnedX τ L α a)⁻¹ * R := ((hR a).inv_left).eq.symm
  have hred : ⁅pinnedX τ L α a, pinnedX τ L β₀ c₀ * R⁆ = ⁅pinnedX τ L α a, pinnedX τ L β₀ c₀⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc pinnedX τ L α a * (pinnedX τ L β₀ c₀ * R) * (pinnedX τ L α a)⁻¹ *
          (pinnedX τ L β₀ c₀ * R)⁻¹
        = pinnedX τ L α a * pinnedX τ L β₀ c₀ * (R * (pinnedX τ L α a)⁻¹) * R⁻¹ *
          (pinnedX τ L β₀ c₀)⁻¹ := by group
      _ = pinnedX τ L α a * pinnedX τ L β₀ c₀ * ((pinnedX τ L α a)⁻¹ * R) * R⁻¹ *
          (pinnedX τ L β₀ c₀)⁻¹ := by rw [hRA]
      _ = pinnedX τ L α a * pinnedX τ L β₀ c₀ * (pinnedX τ L α a)⁻¹ *
          (pinnedX τ L β₀ c₀)⁻¹ := by group
  rw [hred, hcomm] at hcomm2
  exact hcomm2

theorem commute_pinnedX_of_not_root (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β)
    (hsum : ¬ IsRoot τ (α + β)) (s t : L) : Commute (pinnedX τ L α s) (pinnedX τ L β t) := by
  obtain ⟨-, hcomm⟩ := simply_laced_root_commutator_unit τ hτ hα hβ hne hne'
  exact hcomm hsum L _ (Subgroup.subset_closure ⟨s, rfl⟩) _ (Subgroup.subset_closure ⟨t, rfl⟩)

end Commute

end CFSG.HardMathSupport.Timmesfeld.LangTorus
