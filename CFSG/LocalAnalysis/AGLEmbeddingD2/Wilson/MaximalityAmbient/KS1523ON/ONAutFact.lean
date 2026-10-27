module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON.AutFact
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON.CentralizerM
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONAut.Defs
public import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofHJList
public import CFSG.Sporadic.Schreier.SteinbergBIONOuterTwo
public import CFSG.Sporadic.ON

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.Blueprint.NativeSporadic

theorem conj_injective_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) : Function.Injective (MulAut.conj : G →* MulAut G) := by
  have hZ : Subgroup.center G = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).2
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgZ : g ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro h
    have h2 : g * h * g⁻¹ = h := by
      have := congrArg (fun φ : MulAut G => φ h) hg
      simpa only [MulAut.conj_apply, MulAut.one_apply] using this
    calc h * g = g * h * g⁻¹ * g := by rw [h2]
      _ = g * h := by group
  rw [hZ] at hgZ
  exact Subgroup.mem_bot.1 hgZ

theorem nonabelian_of_simple_card {G : Type*} [Group G] [IsSimpleGroup G]
    (hcard : Nat.card G = 460815505920) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have hprime := @IsSimpleGroup.prime_card _ ⟨fun a b => hc a b⟩ _
  rw [hcard] at hprime
  exact absurd hprime (by norm_num)

section Main

set_option linter.unusedSectionVars false


theorem onAutFact_generic {G : Type} [Group G] (e : G ≃* ON)
    (hI1 : ∀ E : Subgroup G, CFSG.Assembly.IsElemAbelian 2 E → Nat.card E ≤ 8)
    (hI3 : ∀ τ : MulAut G, τ ^ 2 = 1 → τ ∉ inner G → ∀ E : Subgroup G, Nat.card E = 9 →
      (∀ g ∈ E, τ g = g) → False)
    (R : Subgroup (MulAut G)) (X : Subgroup G) (hR : IsPGroup 2 R)
    (hS : ((∃ (_ : Fact (Nat.Prime 7))
        (f : ↥X →* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)),
        Function.Surjective f) ∨
      ∃ f : ↥X →* alternatingGroup (Fin 7), Function.Surjective f))
    (hnorm : ∀ x ∈ X, MulAut.conj x ∈ Subgroup.normalizer (R : Set (MulAut G))) : R = ⊥ := by
  have hcardG : Nat.card G = 460815505920 := by
    rw [Nat.card_congr e.toEquiv]; exact CFSG.Sporadic.ON.card_ON
  have hfin : Finite G := Nat.finite_of_card_ne_zero (by rw [hcardG]; norm_num)
  have hsG : IsSimpleGroup G := by
    exact @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.ON.isSimpleGroup_ON e
  have hinj : Function.Injective (MulAut.conj : G →* MulAut G) :=
    conj_injective_of_simple (nonabelian_of_simple_card hcardG)
  have hout : Nat.card (Outer G) ∣ 2 :=
    CFSG.Sporadic.SteinbergBI.cti_on_outer_order_divides_two ⟨e⟩
  rcases hS with ⟨hp7, f, hf⟩ | ⟨f, hf⟩
  · have hcardS : Nat.card (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) = 1876896 :=
      CFSG.RankThree.PartTwo.Sec15.Proof1515.card_projSL_three_seven
    have hfinS : Finite (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) :=
      Nat.finite_of_card_ne_zero (by rw [hcardS]; norm_num)
    have hsS : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) :=
      CFSG.RankThree.PartTwo.Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field _
    refine eq_bot_of_normalized hinj hout hI1 hI3 (S := CFSG.Assembly.RankThreeEven.projSL 3
      (GaloisField 7 1)) (by rw [hcardS]; norm_num) (by rw [hcardS]; norm_num) ?_ R X hR f hf hnorm
    intro t ht W _ _ ψ hψ hψC g hg
    exact not_dvd_of_centralizer e ht ψ hψ hψC g hg (by rw [hcardS]; norm_num)
  · have hsS : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    refine eq_bot_of_normalized hinj hout hI1 hI3 (S := alternatingGroup (Fin 7))
      (by rw [card_alt7]; norm_num) (by rw [card_alt7]; norm_num) ?_ R X hR f hf hnorm
    intro t ht W _ _ ψ hψ hψC g hg
    exact no_surj_alt7_of_centralizer e ht ψ hψ hψC g hg

theorem onAutFact_of_inputs
    (hI1 : ∀ E : Subgroup ON, CFSG.Assembly.IsElemAbelian 2 E → Nat.card E ≤ 8)
    (hI3 : ∀ τ : MulAut ON, τ ^ 2 = 1 → (¬ ∃ g : ON, τ = MulAut.conj g) →
      ∀ E : Subgroup ON, Nat.card E = 9 → (∀ g ∈ E, τ g = g) → False) :
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONAut.ONAutFact := by
  intro R X hR hS hnorm
  refine onAutFact_generic (G := ON) (by with_reducible_and_instances exact MulEquiv.refl _) hI1 ?_ R X hR hS hnorm
  intro τ hτ hnin E hE hfix
  exact hI3 τ hτ (fun ⟨g, hg⟩ => hnin ⟨g, hg.symm⟩) E hE hfix

end Main

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON
