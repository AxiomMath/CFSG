module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CatTw
public import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Glue
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4FieldInner
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Duality
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4T

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Lang.D4Three

set_option linter.unusedSectionVars false


theorem d4Graph_zero' {K : Type} [Field K] [Finite K] : d4Graph K 0 = 1 :=
  MulEquiv.ext fun h => Subtype.ext (by
    rw [coe_d4Graph, pow_zero, one_mul, inv_one, mul_one]; rfl)

theorem eq_zero_or_one_of_card_two'' {F : Type} [Field F] (hF : Nat.card F = 2) (c : F) :
    c = 0 ∨ c = 1 := by
  by_contra! h
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (0 : F)).mp hF
  exact h.2 ((hy c h.1).trans (hy 1 one_ne_zero).symm)

theorem outer_card_dvd
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    (α : MulAut ↥(adjointGroup Tag.D4 F)) (hα : α ^ 3 = 1)
    (hout : ∀ h : adjointGroup Tag.D4 F, MulAut.conj h ≠ α) :
    Nat.card ↥(fixSubgroup α) ∣ CFSG.Open.ordTrialityD4 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : ringChar F ≠ 3 := by
    have : Fintype F := Fintype.ofFinite F
    have hF2 : CharP F 2 := charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)
    rw [ringChar.eq F 2]
    norm_num
  obtain ⟨g, a, σ, ε, hε, hσ3, hαeq⟩ := exists_cube_normal_form_sigma α hα
  have hσ1 : σ = 1 := RingEquiv.ext fun x => by
    rcases eq_zero_or_one_of_card_two'' hF x with rfl | rfl <;> simp
  subst hσ1
  have key : ∀ ε : ℕ, (ε = 1 ∨ ε = 2) →
      α = MulAut.conj g * (exactNormalAut Tag.D4 F a 1 0 * d4Graph F ε) →
      Nat.card ↥(fixSubgroup α) ∣ CFSG.Open.ordTrialityD4 2 := by
    intro ε hε' hαe
    obtain ⟨K₃, _, _, Fr, hK₃, hFr, φ, hφ3, hφout, ⟨e⟩⟩ :=
      D4Dual.exists_dual_fixEquiv (ℓ := 2) (f := 1) le_rfl F (by rw [hF]; norm_num) α hα g a hε' hαe
    have hq : Nat.card ↥(fixSubgroup α) ∣
        Nat.card ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) := by
      rw [Nat.card_congr e.toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    let q' : TauCeti.PrimePower := ⟨2, 1, Nat.prime_two, one_pos⟩
    have hv' := TauCeti.LieTypeIndex.valid_trialityD4 q'
    have hq'card : q'.card = 2 := by simp [q', TauCeti.PrimePower.card_def]
    obtain ⟨eY⟩ := catEquiv_trialityD4_of_field q' hv' K₃ (by rw [hq'card]; simpa using hK₃) Fr
      (fun c => by rw [hq'card]; simpa using hFr c)
    have hY : Nat.card ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) =
        CFSG.Open.ordTrialityD4 2 := by
      rw [← Nat.card_congr eY.toEquiv,
        CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_trialityD4_carrier q' hv', hq'card]
    rw [hY] at hq
    exact hq
  interval_cases ε
  · exfalso
    have hα' : α = MulAut.conj g * exactNormalAut Tag.D4 F a 1 0 := by
      rw [hαeq, d4Graph_zero', mul_one]
    rw [hα'] at hα
    obtain ⟨h, hh⟩ := d4_inner_of_diag hchar g a hα
    exact hout h (by rw [hα', hh])
  · exact key 1 (Or.inl rfl) hαeq
  · exact key 2 (Or.inr rfl) hαeq

end CFSG.LocalAnalysis.GLTheoremA.D4T
