module

public import CFSG.ClassicalInvolution.Balance.ToralBalanceCover
public import CFSG.LieType.Chevalley.OddTwistedE6InnerInvolutionComponents
public import CFSG.LieType.Chevalley.OddE6AllInvolutionComponents
public import CFSG.LieType.Chevalley.OddE7AllInvolutionComponents
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.LieType.Chevalley.OddTrialityAllInvolutionComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieG2F4E8
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBInvolution
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBIndexTwo
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedReverse
public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourWitnesses

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ComponentClassification.FixedCommutingProduct
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.Universal.Spin CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionFixedComponents
open scoped commutatorElement

theorem involutionFixedB_of_coordinate_model {G M : Type} [Group G] [Finite G] [Group M]
    [Finite M] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (ψ : G ≃* M)
    (hfixed : ∀ α : MulAut M, α * α = 1 → α ≠ 1 → ∀ r : ℕ, r.Prime →
      ∀ L : Subgroup (fixedSubgroup α), CFSG.IsPComponent r L → CFSG.IsQuasisimple L) :
    InvolutionFixedB G := by
  have : IsSimpleGroup M := ψ.symm.isSimpleGroup
  have hnonabM : ∃ a b : M, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨ψ a, ψ b, fun h => hab (ψ.injective (by rw [map_mul, map_mul, h]))⟩
  exact InvolutionFixedB.of_mulEquiv ψ
    (fun α hα => CatalogueBOrthogonalIndexTwoB.fixed_twoComponents_of_simple_model hnonabM hfixed
      α hα)

theorem exists_coordinate_model_of_orthogonal {G : Type} [Group G] (t : StatedLieTag)
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) (n p f : ℕ) (hp : p ≠ 2)
    (hmodel : StatedClassicalModel G t n p f) :
    ∃ (d : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (Q : QuadraticForm K (Fin d → K)),
      Nonempty (G ≃* matrixProjectiveDerived Q) ∧
      ∀ α : MulAut (matrixProjectiveDerived Q), α * α = 1 → α ≠ 1 →
        ∀ r : ℕ, r.Prime → ∀ L : Subgroup (fixedSubgroup α),
          CFSG.IsPComponent r L → CFSG.IsQuasisimple L := by
  have hfix := odd_orthogonal_involution_fixed_p_components t ht hp hmodel
  rcases ht with rfl | rfl | rfl
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmodel
    exact ⟨_, K, inferInstance, inferInstance, coordinateQuadOdd n K,
      ⟨coordinateOddWitnessEquiv K e⟩, hfix K hK e⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmodel
    exact ⟨_, K, inferInstance, inferInstance, coordinateQuadPlus n K,
      ⟨coordinatePlusWitnessEquiv K e⟩, hfix K hK e⟩
  · obtain ⟨hadm, K, _, _, hK, b, c, hbc, ⟨e⟩⟩ := hmodel
    have hn : 1 ≤ n := by have := hadm.2.2; omega
    exact ⟨_, K, inferInstance, inferInstance, coordinateQuadMinus n K hn b c,
      ⟨coordinateMinusWitnessEquiv K hn b c e⟩, hfix hn K hK b c hbc e⟩

theorem involutionFixedB_of_statedClassicalModel {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {t : StatedLieTag} {n p f : ℕ} (hp : p ≠ 2)
    (hn : t = .PSL → 3 ≤ n) (hmodel : StatedClassicalModel G t n p f) : InvolutionFixedB G := by
  have : Fact p.Prime := ⟨hmodel.1.1⟩
  have horth : ∀ t : StatedLieTag, (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) →
      StatedClassicalModel G t n p f → InvolutionFixedB G := by
    intro t ht hm
    obtain ⟨d, K, _, _, Q, ⟨ψ⟩, hfixed⟩ := exists_coordinate_model_of_orthogonal t ht n p f hp hm
    have : Finite (matrixProjectiveDerived Q) := Finite.of_equiv _ ψ.toEquiv
    exact involutionFixedB_of_coordinate_model hnonab ψ hfixed
  cases t with
  | PSL =>
    obtain ⟨-, ⟨θ⟩⟩ := ClassicalModelStatedBridge.classicalModel_psl_of_stated hmodel
    let ψ := θ.trans (LinearFieldFour.pslModelEquivProjectiveSL n p f)
    have : Finite (LinearFlag.projectiveSL n (GaloisField p f)) := Finite.of_equiv _ ψ.toEquiv
    have hchar : ringChar (GaloisField p f) ≠ 2 := by
      rw [ringChar.eq (GaloisField p f) p]
      exact hp
    exact involutionFixedB_of_coordinate_model hnonab ψ fun α hsq hα r hr L hL =>
      CatalogueBLinearHigherB.odd_higher_linear_involution_fixed_p_components n
        (GaloisField p f) hchar (hn rfl) α hα (by rw [sq]; exact hsq) r hr L hL
  | PSU =>
    obtain ⟨⟨-, hf, hn3, -⟩, ⟨θ⟩⟩ := ClassicalModelStatedBridge.classicalModel_psu_of_stated hmodel
    let h := CatalogueBUnitaryB.galoisField_unitaryFieldData p f hf
    let ψ : G ≃* unitaryPSU h n :=
      (θ.trans (ClassicalModelStatedBridge.psuModelEquiv n p f)).trans
        (unitaryPSUEquiv h (by omega : 1 ≤ n)).symm
    have : Finite (unitaryPSU h n) := Finite.of_equiv _ ψ.toEquiv
    exact involutionFixedB_of_coordinate_model hnonab ψ fun α hsq hα r hr L hL =>
      CatalogueBUnitaryB.odd_unitary_involution_fixed_p_components h hp hn3 α
        (orderOf_eq_prime (by rw [pow_two]; exact hsq) hα) r hr L hL
  | PSp =>
    obtain ⟨⟨-, hf, hn2, -⟩, ⟨θ⟩⟩ := ClassicalModelStatedBridge.classicalModel_psp_of_stated hmodel
    let ψ : G ≃* StatedProj (StatedSp n (GaloisField p f)) :=
      θ.trans (ClassicalModelStatedBridge.pspModelEquiv n p f)
    have : Finite (StatedProj (StatedSp n (GaloisField p f))) := Finite.of_equiv _ ψ.toEquiv
    have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
    exact involutionFixedB_of_coordinate_model hnonab ψ fun α h2 h1 =>
      CatalogueBSymplecticB.odd_symplectic_involution_fixed_p_components p f Fact.out hp hf
        (GaloisField p f) hcard n hn2 α h2 h1
  | POmegaOdd => exact horth _ (.inl rfl) hmodel
  | POmegaPlus => exact horth _ (.inr (.inl rfl)) hmodel
  | POmegaMinus => exact horth _ (.inr (.inr rfl)) hmodel
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits =>
    exact hmodel.2.elim

theorem involutionFixedB_of_chevalleyExceptionalModel {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {t : StatedLieTag} {p f : ℕ}
    (hp2 : p ≠ 2) (hmodel : ChevalleyExceptionalModel G t p f) : InvolutionFixedB G := by
  have hp : p.Prime := hmodel.1.1
  have hf : 1 ≤ f := hmodel.1.2.1
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hadj : ∀ τ : Tag, UntwistedChevalleyModel G τ (p ^ f) →
      (∀ (K : Type) [Field K] [Finite K], Odd (Nat.card K) → ∀ α : MulAut (adjointGroup τ K),
        α ^ 2 = 1 → ∀ r : ℕ, r.Prime →
        ∀ L : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ K))),
          CFSG.IsPComponent r L → CFSG.IsQuasisimple L) → InvolutionFixedB G := by
    intro τ hm hfix
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ hm
    have hKodd := CatalogueBOddLie.odd_card_of_card_eq_odd_prime_pow hp hp2 hK
    have : Finite (adjointGroup τ K) := Finite.of_equiv _ e.toEquiv
    exact involutionFixedB_of_coordinate_model hnonab e fun α h2 _ r hr L hL =>
      hfix K hKodd α (by rw [pow_two]; exact h2) r hr L hL
  cases t with
  | G2 =>
    exact hadj .G2 hmodel.2 fun K _ _ hK α hα r hr L hL =>
      LieType.AlgebraicGroups.odd_G2_F4_E8_all_involution_fixed_p_components .G2 (.inl rfl) K hK
        α hα r hr L hL
  | F4 =>
    exact hadj .F4 hmodel.2 fun K _ _ hK α hα r hr L hL =>
      LieType.AlgebraicGroups.odd_G2_F4_E8_all_involution_fixed_p_components .F4
        (.inr (.inl rfl)) K hK α hα r hr L hL
  | E8 =>
    exact hadj .E8 hmodel.2 fun K _ _ hK α hα r hr L hL =>
      LieType.AlgebraicGroups.odd_G2_F4_E8_all_involution_fixed_p_components .E8
        (.inr (.inr rfl)) K hK α hα r hr L hL
  | E6 =>
    exact hadj .E6 hmodel.2 fun K _ _ hK α hα r hr L hL =>
      odd_E6_all_involution_fixed_p_components K hK α hα r hr L hL
  | E7 =>
    exact hadj .E7 hmodel.2 fun K _ _ hK α hα r hr L hL =>
      LieType.AlgebraicGroups.odd_E7_all_involution_fixed_p_components K hK α hα r hr L hL
  | trialityD4 =>
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 hp hf hmodel.2
    have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Finite.of_equiv _ e.toEquiv
    exact involutionFixedB_of_coordinate_model hnonab e fun α h2 _ r hr L hL =>
      odd_triality_all_involution_fixed_p_components hp hp2 hf K hK σ hσ α
        (by rw [pow_two]; exact h2) r hr L hL
  | twistedE6 =>
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card TwistTag.E6 hp hf hmodel.2
    have : Finite (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := Finite.of_equiv _ e.toEquiv
    exact involutionFixedB_of_coordinate_model hnonab e fun α h2 _ r hr L hL =>
      odd_twisted_E6_all_involution_fixed_p_components hp hf hodd K hK σ hσ α
        (by rw [pow_two]; exact h2) r hr L hL
  | PSL | PSU | PSp | POmegaOdd | POmegaPlus | POmegaMinus | twistedB2 | twistedG2 | twistedF4
  | Tits => exact hmodel.2.elim

theorem involutionFixedB_of_lieModel {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {t : StatedLieTag} {n p f : ℕ} (hp : p ≠ 2)
    (hn : t = .PSL → 3 ≤ n) (ht : t ∈ classicalTags ∨ t ∈ chevalleyExceptionalTags)
    (hmodel : LieModel G t n p f) : InvolutionFixedB G := by
  rcases hmodel with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, htr, -⟩ | ⟨-, htb, -⟩
  · exact involutionFixedB_of_statedClassicalModel hnonab hp hn h
  · exact involutionFixedB_of_chevalleyExceptionalModel hnonab hp h
  · exfalso
    rcases ht with ht | ht <;>
      simp [classicalTags, chevalleyExceptionalTags, reeTitsTags] at ht htr <;>
      rcases htr with h | h | h <;> subst h <;> simp at ht
  · exfalso
    subst htb
    rcases ht with ht | ht <;> simp [classicalTags, chevalleyExceptionalTags] at ht

theorem involutionCentralizerB_of_statedClassicalModel {X : Type} [Group X] [Finite X]
    {L : Subgroup X} [IsSimpleGroup (↥L ⧸ Subgroup.center ↥L)]
    (hnonab : ∃ a b : ↥L ⧸ Subgroup.center ↥L, a * b ≠ b * a) {t : StatedLieTag} {n p f : ℕ}
    (hp : p ≠ 2) (hn : t = .PSL → 3 ≤ n)
    (hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) t n p f) :
    InvolutionCentralizerB L :=
  involutionCentralizerB_of_involutionFixedB
    (involutionFixedB_of_statedClassicalModel hnonab hp hn hmodel)

theorem exists_not_comm_of_isQuasisimple {L : Type*} [Group L] (hL : CFSG.Open.IsQuasisimple L) :
    ∃ a b : L ⧸ Subgroup.center L, a * b ≠ b * a := by
  obtain ⟨hperf, hsimple⟩ := hL
  by_contra hcomm
  push Not at hcomm
  have hle : commutator L ≤ Subgroup.center L := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    have h : (QuotientGroup.mk' (Subgroup.center L)) ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm _ _
    exact (QuotientGroup.eq_one_iff _).mp h
  rw [hperf, top_le_iff] at hle
  have : Subsingleton (L ⧸ Subgroup.center L) := ⟨fun a b => by
    induction a using QuotientGroup.induction_on with | H x =>
    induction b using QuotientGroup.induction_on with | H y =>
    refine QuotientGroup.eq.mpr ?_
    rw [hle]
    exact Subgroup.mem_top _⟩
  exact not_subsingleton _ this

theorem involutionCentralizerB_of_lieModel {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hL : CFSG.Open.IsQuasisimple ↥L) {t : StatedLieTag} {n p f : ℕ} (hp : p ≠ 2)
    (hn : t = .PSL → 3 ≤ n) (ht : t ∈ classicalTags ∨ t ∈ chevalleyExceptionalTags)
    (hmodel : LieModel (↥L ⧸ Subgroup.center ↥L) t n p f) : InvolutionCentralizerB L := by
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2
  exact involutionCentralizerB_of_involutionFixedB
    (involutionFixedB_of_lieModel (exists_not_comm_of_isQuasisimple hL) hp hn ht hmodel)

end CFSG.ClassicalInvolution.Balance
