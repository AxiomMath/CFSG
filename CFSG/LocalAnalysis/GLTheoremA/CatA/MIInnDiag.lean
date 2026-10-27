module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.MICore
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA


namespace MI

open CFSG.Assembly CFSG.StandardType CFSG.Open

theorem marking_transport_family {X : Type} [Group X] {ι : Type} (rel : ι → X → X → Prop)
    (S : Set ι) (hS : S.Finite) {P : LargeEvenMarkProp X}
    (h₁ : ∀ i ∈ S, CFSG.Assembly.LargeEvenMarking X fun _ _ _ I _ θ =>
      ∃ φ ∈ I, LargeEvenInduces θ (rel i) φ)
    (h₂ : CFSG.Assembly.LargeEvenMarking X P) :
    CFSG.Assembly.LargeEvenMarking X fun lab R _ I F θ =>
      P lab R I F θ ∧ ∀ i ∈ S, ∃ φ ∈ I, LargeEvenInduces θ (rel i) φ := by
  revert h₁
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    intro _
    exact Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP, by simp⟩) h₂
  | @insert a s has hs ih =>
    intro h₁
    have ih' := ih fun i hi => h₁ i (Set.mem_insert_of_mem a hi)
    have := marking_transport (rel a) (h₁ a (Set.mem_insert a s)) ih'
    refine Canonical.largeEvenMarking_mono (fun lab R _ I F θ ⟨⟨hP, hall⟩, φ, hφ, hind⟩ => ?_) this
    refine ⟨hP, ?_⟩
    intro i hi
    rcases Set.mem_insert_iff.1 hi with rfl | hi'
    · exact ⟨φ, hφ, hind⟩
    · exact hall i hi'

end MI

open CFSG.Assembly CFSG.StandardType CFSG.Open in
theorem innDiagIndepAt_holds (G : Type) [Group G] [Finite G] : InnDiagIndepAt G := by
  intro B K P hB hP
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := by
    obtain ⟨-, -, -, R, _, I, F, θ, -, -, hB1⟩ := Canonical.largeEvenMarking_exists hB
    exact hB1.1
  have hb : ∀ b ∈ (B : Set G), CFSG.Assembly.LargeEvenMarking ↥K
      fun _ _ _ I _ θ => ∃ φ ∈ I, LargeEvenInduces θ
        (fun l l' : ↥K => (l' : G) = b⁻¹ * l * b) φ :=
    fun b hb => Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.2 b hb) hB
  have := MI.marking_transport_family (fun (b : G) (l l' : ↥K) => (l' : G) = b⁻¹ * l * b)
    (B : Set G) (Set.toFinite _) hb hP
  exact Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ ⟨hPθ, hall⟩ => ⟨hPθ, hBN, hall⟩) this

end CFSG.LocalAnalysis.GLTheoremA
