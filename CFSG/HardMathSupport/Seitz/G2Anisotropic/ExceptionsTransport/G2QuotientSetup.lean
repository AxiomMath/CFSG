module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.G2Rows
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.ClassTwoQuotient

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  RootOps
open scoped commutatorElement

@[expose] def IsQRoot (γ : Fin Tag.G2.rank → ℤ) : Prop := γ = gA ∨ γ = gU ∨ γ = gV ∨ γ = gB ∨ γ = gC

section Setup

variable
  {K : Type} [Field K]

@[expose] def genSet (K : Type) [Field K] : Set (ModGL .G2 K) :=
  {g | ∃ γ, IsQRoot γ ∧ ∃ c : K, g = pinnedX .G2 K γ c}

@[expose] def Qg (K : Type) [Field K] : Subgroup (ModGL .G2 K) := Subgroup.closure (genSet K)

@[expose] def Zg (K : Type) [Field K] : Subgroup (ModGL .G2 K) :=
  Subgroup.closure {g | ∃ c : K, g = pinnedX .G2 K gC c}

theorem mem_Zg {g : ModGL .G2 K} : g ∈ Zg K ↔ ∃ c : K, g = pinnedX .G2 K gC c := by
  constructor
  · intro hg
    unfold Zg at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨0, (pinnedX_zero .G2 K gC).symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := hy
      exact ⟨c + d, (pinnedX_add .G2 K gC c d).symm⟩
    | inv x _ hx =>
      obtain ⟨c, rfl⟩ := hx
      exact ⟨-c, pinnedX_neg .G2 K gC c⟩
  · rintro ⟨c, rfl⟩
    exact Subgroup.subset_closure ⟨c, rfl⟩

theorem X_mem_Zg (c : K) : pinnedX .G2 K gC c ∈ Zg K := mem_Zg.2 ⟨c, rfl⟩

theorem X_mem_Qg {γ : Fin Tag.G2.rank → ℤ} (hγ : IsQRoot γ) (c : K) :
    pinnedX .G2 K γ c ∈ Qg K := Subgroup.subset_closure ⟨γ, hγ, c, rfl⟩

theorem commute_same (γ : Fin Tag.G2.rank → ℤ) (s t : K) :
    Commute (pinnedX .G2 K γ s) (pinnedX .G2 K γ t) := by
  show pinnedX .G2 K γ s * pinnedX .G2 K γ t = pinnedX .G2 K γ t * pinnedX .G2 K γ s
  rw [← pinnedX_add .G2 K γ s t, ← pinnedX_add .G2 K γ t s, add_comm]

theorem commutator_inv_mem {g h : ModGL .G2 K} (hgh : g * h * g⁻¹ * h⁻¹ ∈ Zg K) :
    h * g * h⁻¹ * g⁻¹ ∈ Zg K := by
  have e : h * g * h⁻¹ * g⁻¹ = (g * h * g⁻¹ * h⁻¹)⁻¹ := by group
  rw [e]
  exact (Zg K).inv_mem hgh

theorem commutator_one_mem {g h : ModGL .G2 K} (hgh : Commute g h) :
    g * h * g⁻¹ * h⁻¹ ∈ Zg K := by
  have : g * h * g⁻¹ * h⁻¹ = 1 := by
    rw [hgh.eq]; simp [mul_assoc]
  rw [this]; exact (Zg K).one_mem

theorem commute_X_c {γ : Fin Tag.G2.rank → ℤ} (hγ : IsQRoot γ) (s t : K) :
    Commute (pinnedX .G2 K γ s) (pinnedX .G2 K gC t) := by
  rcases hγ with rfl | rfl | rfl | rfl | rfl
  exacts [commute_a_c s t, commute_u_c s t, commute_v_c s t, commute_b_c s t, commute_same gC s t]

theorem gen_comm_mem {γ δ : Fin Tag.G2.rank → ℤ} (hγ : IsQRoot γ) (hδ : IsQRoot δ) (s t : K) :
    pinnedX .G2 K γ s * pinnedX .G2 K δ t * (pinnedX .G2 K γ s)⁻¹ * (pinnedX .G2 K δ t)⁻¹ ∈
      Zg K := by
  rcases hγ with rfl | rfl | rfl | rfl | rfl <;> rcases hδ with rfl | rfl | rfl | rfl | rfl
  · exact commutator_one_mem (commute_same _ s t)
  · exact commutator_one_mem (commute_a_u s t)
  · exact commutator_one_mem (commute_a_v s t)
  · rw [← commutatorElement_def, comm_a_b]; exact X_mem_Zg _
  · exact commutator_one_mem (commute_a_c s t)
  · exact commutator_one_mem (commute_a_u t s).symm
  · exact commutator_one_mem (commute_same _ s t)
  · obtain ⟨ε, -, h⟩ := comm_u_v_signed
    rw [← commutatorElement_def, h s t]; exact X_mem_Zg _
  · exact commutator_one_mem (commute_u_b s t)
  · exact commutator_one_mem (commute_u_c s t)
  · exact commutator_one_mem (commute_a_v t s).symm
  · obtain ⟨ε, -, h⟩ := comm_u_v_signed
    exact commutator_inv_mem (by rw [← commutatorElement_def, h t s]; exact X_mem_Zg _)
  · exact commutator_one_mem (commute_same _ s t)
  · exact commutator_one_mem (commute_v_b s t)
  · exact commutator_one_mem (commute_v_c s t)
  · exact commutator_inv_mem (by rw [← commutatorElement_def, comm_a_b]; exact X_mem_Zg _)
  · exact commutator_one_mem (commute_u_b t s).symm
  · exact commutator_one_mem (commute_v_b t s).symm
  · exact commutator_one_mem (commute_same _ s t)
  · exact commutator_one_mem (commute_b_c s t)
  · exact commutator_one_mem (commute_a_c t s).symm
  · exact commutator_one_mem (commute_u_c t s).symm
  · exact commutator_one_mem (commute_v_c t s).symm
  · exact commutator_one_mem (commute_b_c t s).symm
  · exact commutator_one_mem (commute_same _ s t)

theorem classTwoG2 : ClassTwo (Qg K) (Zg K) where
  le := Subgroup.closure_mono (fun g ⟨c, hc⟩ =>
    ⟨gC, Or.inr (Or.inr (Or.inr (Or.inr rfl))), c, hc⟩)
  central := central_closure (S := genSet K) (Z := Zg K) (fun s ⟨γ, hγ, c, hs⟩ z hz => by
    obtain ⟨t, rfl⟩ := mem_Zg.1 hz
    rw [hs]
    exact (commute_X_c hγ c t).eq)
  comm := comm_mem_closure (S := genSet K) (fun s ⟨γ, hγ, c, hs⟩ z hz => by
    obtain ⟨t, rfl⟩ := mem_Zg.1 hz
    rw [hs]
    exact (commute_X_c hγ c t).eq)
    (fun s ⟨γ, hγ, c, hs⟩ s' ⟨δ, hδ, d, hs'⟩ => by
      rw [hs, hs']
      exact gen_comm_mem hγ hδ c d)

end Setup

end CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport
