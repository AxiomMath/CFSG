module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcPlumb
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Bridge
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.ExcCommon
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Basic
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType.RecipeExcLang

namespace Up34Chev2

section Conj

set_option linter.unusedSectionVars false


theorem noL34Layer_conj_adjoint_two {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hI : Char2Hrat τ .inner) (hS : Char2Hrat τ .suN) (hD : Char2Hrat τ .twoD)
    (hE : Char2Hrat τ .exc) {F : Type} [Field F] [Finite F] {f : ℕ} (hf : 1 ≤ f)
    (hF : Nat.card F = 2 ^ f) (y : ↥(adjointGroup τ F))
    (hy3 : (MulAut.conj y : MulAut ↥(adjointGroup τ F)) ^ 3 = 1)
    (hy1 : (MulAut.conj y : MulAut ↥(adjointGroup τ F)) ≠ 1) :
    NoL34Layer (MulAut.conj y : MulAut ↥(adjointGroup τ F)) := by
  have hZ : Subgroup.center ↥(adjointGroup τ F) = ⊥ := center_adjointGroup_eq_bot
  have hy3' : y ^ 3 = 1 := by
    have h1 : (MulAut.conj (y ^ 3) : MulAut ↥(adjointGroup τ F)) = MulAut.conj 1 := by
      rw [map_pow, map_one]
      exact hy3
    have h2 : y ^ 3 ∈ Subgroup.center ↥(adjointGroup τ F) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := DFunLike.congr_fun h1 g
      simp only [MulAut.conj_apply, MulAut.one_apply, inv_one, mul_one, one_mul] at this
      calc g * y ^ 3 = y ^ 3 * g * (y ^ 3)⁻¹ * y ^ 3 := by rw [this]
        _ = y ^ 3 * g := by group
    rwa [hZ, Subgroup.mem_bot] at h2
  have hyL : baseChangeGL (algebraMap F (AlgebraicClosure F)) (y : ModGL τ F) ∈
      adjointGroup τ (AlgebraicClosure F) :=
    baseChange_mem_adjointGroup_of_mem_inndiag (adjointGroup_le_inndiagGroup y.2)
  refine noL34Layer_exc_inner_untw_two hτ hI hS hD hE hf hF (MulAut.conj y) (y : ModGL τ F) hyL
    (fun c => by simp [MulAut.conj_apply]) ?_ ?_
  · change ((y : ModGL τ F)) ^ 3 = 1
    rw [← Subgroup.coe_pow, hy3']
    rfl
  · intro h1
    apply hy1
    have : y = 1 := Subtype.ext h1
    rw [this, map_one]

theorem not_up34Pumpup_of_equiv_adjoint_two {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hI : Char2Hrat τ .inner) (hS : Char2Hrat τ .suN) (hD : Char2Hrat τ .twoD)
    (hE : Char2Hrat τ .exc) {S : Type} [Group S] [Finite S] {F : Type} [Field F] [Finite F]
    {f : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f) (θ : S ≃* ↥(adjointGroup τ F)) (x : S) :
    ¬ Up34Pumpup S (MulAut.conj x) := by
  intro hp
  have hp' := hp.of_congr θ
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj] at hp'
  obtain ⟨hy3, hy1, hno⟩ := (up34Pumpup_iff _).1 hp'
  exact hno (noL34Layer_conj_adjoint_two hτ hI hS hD hE hf hF (θ x) hy3 hy1)

end Conj

section Family

set_option linter.unusedSectionVars false


theorem up34C2Inn_F4_of_kinds (hI : Char2Hrat Tag.F4 .inner) (hS : Char2Hrat Tag.F4 .suN)
    (hD : Char2Hrat Tag.F4 .twoD) (hE : Char2Hrat Tag.F4 .exc) : Up34Chev2Inn FamF4 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ x
  cases d with
  | F4 q =>
    have hq2 : q.p = 2 := hc
    have hm := blueprintLieModel_F4 q hv e
    have hU : UntwistedChevalleyModel S .F4 (q.p ^ q.exponent) := by
      rcases hm with ⟨ht', -⟩ | ⟨-, -, hE'⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
      · exact absurd ht' (by decide)
      · exact hE'.2
      · exact absurd ht' (by decide)
      · exact absurd ht' (by decide)
    obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
    rw [hq2] at hFcard
    exact not_up34Pumpup_of_equiv_adjoint_two (Or.inl rfl) hI hS hD hE q.exponent_pos hFcard θ x
  | _ => exact hF.elim

theorem up34C2Inn_E7_of_kinds (hI : Char2Hrat Tag.E7 .inner) (hS : Char2Hrat Tag.E7 .suN)
    (hD : Char2Hrat Tag.E7 .twoD) (hE : Char2Hrat Tag.E7 .exc) : Up34Chev2Inn FamE7 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ x
  cases d with
  | E7 q =>
    have hq2 : q.p = 2 := hc
    have hm := blueprintLieModel_E7 q hv e
    have hU : UntwistedChevalleyModel S .E7 (q.p ^ q.exponent) := by
      rcases hm with ⟨ht', -⟩ | ⟨-, -, hE'⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
      · exact absurd ht' (by decide)
      · exact hE'.2
      · exact absurd ht' (by decide)
      · exact absurd ht' (by decide)
    obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
    rw [hq2] at hFcard
    exact not_up34Pumpup_of_equiv_adjoint_two (Or.inr (Or.inr (Or.inl rfl))) hI hS hD hE
      q.exponent_pos hFcard θ x
  | _ => exact hF.elim

theorem up34C2Inn_E8_of_kinds (hI : Char2Hrat Tag.E8 .inner) (hS : Char2Hrat Tag.E8 .suN)
    (hD : Char2Hrat Tag.E8 .twoD) (hE : Char2Hrat Tag.E8 .exc) : Up34Chev2Inn FamE8 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ x
  cases d with
  | E8 q =>
    have hq2 : q.p = 2 := hc
    have hm := blueprintLieModel_E8 q hv e
    have hU : UntwistedChevalleyModel S .E8 (q.p ^ q.exponent) := by
      rcases hm with ⟨ht', -⟩ | ⟨-, -, hE'⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
      · exact absurd ht' (by decide)
      · exact hE'.2
      · exact absurd ht' (by decide)
      · exact absurd ht' (by decide)
    obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
    rw [hq2] at hFcard
    exact not_up34Pumpup_of_equiv_adjoint_two (Or.inr (Or.inr (Or.inr rfl))) hI hS hD hE
      q.exponent_pos hFcard θ x
  | _ => exact hF.elim

end Family

end Up34Chev2

end CFSG.HardMathSupport.Dickson.Sec6
