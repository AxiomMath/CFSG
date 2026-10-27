module

public import CFSG.LieType.Chevalley.EvenE7E8AutomorphismNormalForm
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Inner

theorem ringEquiv_subsingleton (K : Type) [Field K] (hK : Nat.card K = 2) :
    Subsingleton (K ≃+* K) := by
  obtain ⟨a, b, hab, hS⟩ := Nat.card_eq_two_iff.1 hK
  have hmem : ∀ x : K, x = a ∨ x = b := fun x => by
    have : x ∈ ({a, b} : Set K) := by rw [hS]; exact Set.mem_univ x
    simpa using this
  have h01 : ∀ x : K, x = 0 ∨ x = 1 := by
    intro x
    by_contra hne
    push Not at hne
    obtain ⟨hx0, hx1⟩ := hne
    have h01' : (0 : K) ≠ 1 := zero_ne_one
    rcases hmem 0 with h0 | h0 <;> rcases hmem 1 with h1 | h1 <;> rcases hmem x with hx | hx
    all_goals first
      | exact h01' (h0.trans h1.symm)
      | exact hx0 (hx.trans h0.symm)
      | exact hx1 (hx.trans h1.symm)
  refine ⟨fun σ τ => ?_⟩
  ext x
  rcases h01 x with rfl | rfl <;> simp

theorem mulAut_mem_range_conj_E78
    {τ : Tag}
    (hτ : τ = .E7 ∨ τ = .E8) (K : Type) [Field K] (hK : Nat.card K = 2)
    (α : MulAut (adjointGroup τ K)) :
    α ∈ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range := by
  obtain ⟨-, Θ, -, -, hker, -⟩ := even_E7_E8_exact_inner_field_automorphism_normal_form
    (f := 1) le_rfl K (by rw [hK]; norm_num) τ hτ
  haveI := ringEquiv_subsingleton K hK
  have : α ∈ Θ.ker := by
    rw [MonoidHom.mem_ker]
    exact Subsingleton.elim _ _
  rwa [hker] at this

theorem mulAut_mem_range_conj_of_equiv {C₀ C₁ : Type*} [Group C₀] [Group C₁] (e : C₀ ≃* C₁)
    (h : ∀ α : MulAut C₁, α ∈ (MulAut.conj : C₁ →* MulAut C₁).range) (α : MulAut C₀) :
    α ∈ (MulAut.conj : C₀ →* MulAut C₀).range := by
  obtain ⟨g, hg⟩ := h (e.symm.trans (α.trans e))
  refine ⟨e.symm g, ?_⟩
  ext y
  have h1 : (MulAut.conj g) (e y) = e (α y) := by
    have := congrArg (fun β : MulAut C₁ => β (e y)) hg
    simpa using this
  have h2 : α y = e.symm ((MulAut.conj g) (e y)) := by
    rw [h1]
    simp
  rw [h2]
  simp [MulAut.conj_apply]

theorem conj_injective_of_equiv {C₀ C₁ : Type*} [Group C₀] [Group C₁] (e : C₀ ≃* C₁)
    (hZ : Subgroup.center C₁ = ⊥) :
    Function.Injective (MulAut.conj : C₀ →* MulAut C₀) := by
  have hZ₀ : Subgroup.center C₀ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : e x ∈ Subgroup.center C₁ := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := Subgroup.mem_center_iff.1 hx (e.symm y)
      have h2 := congrArg e this
      simpa using h2
    rw [hZ, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (e.injective (by simpa using this))
  intro x y hxy
  have hxy' : (MulAut.conj x : MulAut C₀) = MulAut.conj y := hxy
  have h3 : ∀ z, x * z * x⁻¹ = y * z * y⁻¹ := fun z => by
    have := congrArg (fun β : MulAut C₀ => β z) hxy'
    simpa using this
  have hc : y⁻¹ * x ∈ Subgroup.center C₀ := by
    rw [Subgroup.mem_center_iff]
    intro z
    calc z * (y⁻¹ * x) = y⁻¹ * (y * z * y⁻¹) * x := by group
      _ = y⁻¹ * (x * z * x⁻¹) * x := by rw [h3 z]
      _ = y⁻¹ * x * z := by group
  rw [hZ₀, Subgroup.mem_bot] at hc
  exact inv_mul_eq_one.1 hc |>.symm

end Inner

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc

end
