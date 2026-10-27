module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePropC
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormF4
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormE6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormE7
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormE8
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormRee
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormTwE6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormD4

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.C

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

theorem not_SL_of_PSL_center {R : Type*} [Group R] [Finite R] {F F' : Type*} [Field F]
    [Field F'] [Finite F'] (hF : ringChar F ≠ 2) (e : R ≃* SL(2, F))
    (e' : R ⧸ pPrimeCore 2 R ≃* PSL(2, F')) : False := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  set z := e.symm (-1) with hz
  have hzc : z ∈ center R := by
    rw [mem_center_iff]
    intro g
    apply e.injective
    rw [map_mul, map_mul, hz, MulEquiv.apply_symm_apply]
    simp
  have hz1 : z ≠ 1 := by
    intro h1
    have h1' : (-1 : SL(2, F)) = 1 := by rw [← e.apply_symm_apply (-1), ← hz, h1, map_one]
    have h00 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h1'
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h00
    exact h2 (by linear_combination -h00)
  have hz2 : z ^ 2 = 1 := by rw [hz, ← map_pow, neg_one_sq, map_one]
  have hzO := not_mem_pPrimeCore_of_orderOf (orderOf_eq_prime hz2 hz1)
  have hc : e' (QuotientGroup.mk z) ∈ center PSL(2, F') := by
    rw [mem_center_iff]
    intro g
    obtain ⟨r, hr⟩ := QuotientGroup.mk_surjective (e'.symm g)
    have hg : g = e' (QuotientGroup.mk r) := by rw [hr, MulEquiv.apply_symm_apply]
    rw [hg, ← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      mem_center_iff.1 hzc r]
  rw [GorensteinWalter.psl2_center_eq_bot, mem_bot, map_eq_one_iff _ e'.injective,
    QuotientGroup.eq_one_iff] at hc
  exact hzO hc

theorem not_card_dvd_of_PSL_SL {R₁ R₂ : Type*} [Group R₁] [Group R₂] [Finite R₁] [Finite R₂]
    {F : Type*} [Field F] [Finite F] (hF : ringChar F ≠ 2)
    (e₁ : R₁ ⧸ pPrimeCore 2 R₁ ≃* PSL(2, F)) (e₂ : R₂ ⧸ pPrimeCore 2 R₂ ≃* SL(2, F)) :
    ¬ Nat.card R₂ ∣ Nat.card R₁ := by
  intro hdvd
  have h1 := card_eq_card_pPrimeCore_mul (R := R₁)
  have h2 := card_eq_card_pPrimeCore_mul (R := R₂)
  rw [Nat.card_congr e₁.toEquiv] at h1
  rw [Nat.card_congr e₂.toEquiv, ← card_PSL_mul_two hF] at h2
  rw [h1, h2] at hdvd
  have hpos : 0 < Nat.card PSL(2, F) := Nat.card_pos
  have h3 : Nat.card (pPrimeCore 2 R₂) * 2 ∣ Nat.card (pPrimeCore 2 R₁) := by
    refine Nat.dvd_of_mul_dvd_mul_left hpos ?_
    convert hdvd using 1 <;> ring
  exact (Nat.not_even_iff_odd.2 (odd_card_pPrimeCore (R := R₁)))
    (even_iff_two_dvd.2 ((dvd_mul_left 2 _).trans h3))

theorem false_of_slComponentForm {F : Type} [Field F] (hF : ringChar F ≠ 2) {H : Type} [Group H]
    [Finite H] (hq : ∀ L : Subgroup H, IsPComponent 2 L → IsQuasisimple L)
    (hform : SLComponentForm F H) {R₁ R₂ : Subgroup H} (hR₁ : IsPComponent 2 R₁)
    (hR₂ : IsPComponent 2 R₂) {F' : Type} [Field F'] [Finite F'] (hF' : ringChar F' ≠ 2)
    (e₁ : R₁ ⧸ pPrimeCore 2 R₁ ≃* PSL(2, F')) (e₂ : R₂ ⧸ pPrimeCore 2 R₂ ≃* SL(2, F')) :
    False := by
  have hc : ∀ {R : Subgroup H}, IsPComponent 2 R → IsComponent R := fun {R} hR =>
    ⟨hq R hR, by obtain ⟨_, _, h, _⟩ := hR; exact h⟩
  have hndvd := not_card_dvd_of_PSL_SL hF' e₁ e₂
  by_cases hSL : Nonempty (R₂ ≃* SL(2, F))
  · obtain ⟨f₂⟩ := hSL
    rcases hform R₁ (hc hR₁) with hf₁ | ⟨hdvd, -⟩
    · obtain ⟨f₁⟩ := hf₁
      exact hndvd (dvd_of_eq ((Nat.card_congr f₂.toEquiv).trans (Nat.card_congr f₁.toEquiv).symm))
    · exact hndvd (by rw [Nat.card_congr f₂.toEquiv]; exact hdvd)
  · rcases hform R₁ (hc hR₁) with hf₁ | ⟨-, hall⟩
    · obtain ⟨f₁⟩ := hf₁
      exact not_SL_of_PSL_center hF f₁ e₁
    · obtain ⟨f⟩ := hall R₂ (hc hR₂) hSL
      exact hndvd (dvd_of_eq (Nat.card_congr f.toEquiv).symm)

theorem fixedSubgroup_conj {G : Type*} [Group G] (x : G) :
    fixedSubgroup (MulAut.conj x) = centralizer ({x} : Set G) := by
  ext g
  rw [mem_centralizer_singleton_iff]
  change MulAut.conj x g = g ↔ _
  rw [MulAut.conj_apply]
  constructor
  · intro h
    calc g * x = x * g * x⁻¹ * x := by rw [h]
      _ = x * g := by group
  · intro h
    rw [← h, mul_inv_cancel_right]

theorem orderOf_conj_eq_two {G : Type*} [Group G] {x : G} (hx : orderOf x = 2)
    (hxZ : x ∉ center G) : orderOf (MulAut.conj x) = 2 := by
  have h2 : MulAut.conj x ^ 2 = 1 := by rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  refine orderOf_eq_prime h2 fun h1 => hxZ ?_
  rw [mem_center_iff]
  intro g
  have h3 : x * g * x⁻¹ = g := by
    have := congrArg (fun φ : MulAut G => φ g) h1
    simpa [MulAut.conj_apply] using this
  calc g * x = x * g * x⁻¹ * x := by rw [h3]
    _ = x * g := by group

theorem false_of_conj_slForm {F : Type} [Field F] (hF : ringChar F ≠ 2) {K : Type} [Group K]
    [Finite K] {x : K}
    (hq : ∀ L : Subgroup (fixedSubgroup (MulAut.conj x)), IsPComponent 2 L → IsQuasisimple L)
    (hsl : SLComponentForm F (fixedSubgroup (MulAut.conj x))) {R₁ R₂ : Subgroup K} {p n : ℕ}
    [Fact p.Prime] (hC : PropCData x R₁ R₂ p n) : False := by
  let Θ : centralizer ({x} : Set K) ≃* fixedSubgroup (MulAut.conj x) :=
    MulEquiv.subgroupCongr (fixedSubgroup_conj x).symm
  have hq' : ∀ L : Subgroup (centralizer ({x} : Set K)), IsPComponent 2 L → IsQuasisimple L := by
    intro L hL
    have hL' := ((LocalAnalysis.ComponentInitial.p_component_isomorphism_transport 2
      Nat.prime_two Θ).1 L).1 hL
    exact LocalCores.isQuasisimple_of_mulEquiv (L.equivMapOfInjective _ Θ.injective).symm
      (hq _ hL')
  obtain ⟨e₁⟩ := hC.iso₁
  obtain ⟨e₂⟩ := hC.iso₂
  exact false_of_slComponentForm hF hq' (slComponentForm_of_mulEquiv Θ hsl) hC.comp₁ hC.comp₂
    (ringChar_galoisField_ne_two hC.p_ne_two)
    ((quotientPPrimeCoreEquiv (Subgroup.subgroupOfEquivOfLe hC.le₁)).trans e₁)
    ((quotientPPrimeCoreEquiv (Subgroup.subgroupOfEquivOfLe hC.le₂)).trans e₂)

theorem false_of_untwisted_slForm {τ : Tag} (hform : OddExcInnerDiagSLForm τ) {K : Type}
    [Group K] [Finite K] {p' f' : ℕ} (hp' : p'.Prime) (hp2' : p' ≠ 2)
    (hm : UntwistedChevalleyModel K τ (p' ^ f')) {x : K} {R₁ R₂ : Subgroup K} {p n : ℕ}
    [Fact p.Prime] (hC : PropCData x R₁ R₂ p n) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ hm
  have hf : 1 ≤ f' := (one_le_and_three_le_of_card hp' hp2' hF).1
  have : CharP F p' :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp' hf hF
  have hF2 : ringChar F ≠ 2 := by rw [ringChar.eq F p']; exact hp2'
  have hC' := hC.map e
  have hyZ : e x ∉ center (adjointGroup τ F) := by
    rw [center_adjointGroup_eq_bot, mem_bot]
    intro h1
    have := hC'.orderOf_eq
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have hβg : ∀ h : adjointGroup τ F, (MulAut.conj (e x) h : ModGL τ F) =
      (e x : ModGL τ F) * rootDiagUnit τ 1 * (h : ModGL τ F) * (rootDiagUnit τ 1)⁻¹ *
        (e x : ModGL τ F)⁻¹ := by
    intro h
    rw [rootDiagUnit_one, mul_one, inv_one, mul_one, MulAut.conj_apply]
    rfl
  obtain ⟨hq, hsl⟩ := hform F p' f' hp' hp2' hF (MulAut.conj (e x)) (e x) 1 hβg
    (orderOf_conj_eq_two hC'.orderOf_eq hyZ)
  exact false_of_conj_slForm hF2 hq hsl hC'

theorem false_of_propCData_untwisted {K : Type} [Group K] [Finite K] {τ : StatedLieTag}
    {n' p' f' : ℕ} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hp2' : p' ≠ 2)
    (hL : LieModel K τ n' p' f') {x : K} {R₁ R₂ : Subgroup K} {p n : ℕ} [Fact p.Prime]
    (hC : PropCData x R₁ R₂ p n) : False := by
  rcases hτ with rfl | rfl | rfl | rfl
  · have hm := GH74.chevalleyExceptionalModel_of_lieModel (by decide) hL
    exact false_of_untwisted_slForm oddExcInnerDiagSLForm_F4 hm.1.1 hp2'
      (hm.2 : UntwistedChevalleyModel K .F4 (p' ^ f')) hC
  · have hm := GH74.chevalleyExceptionalModel_of_lieModel (by decide) hL
    exact false_of_untwisted_slForm oddExcInnerDiagSLForm_E6 hm.1.1 hp2'
      (hm.2 : UntwistedChevalleyModel K .E6 (p' ^ f')) hC
  · have hm := GH74.chevalleyExceptionalModel_of_lieModel (by decide) hL
    exact false_of_untwisted_slForm oddExcInnerDiagSLForm_E7 hm.1.1 hp2'
      (hm.2 : UntwistedChevalleyModel K .E7 (p' ^ f')) hC
  · have hm := GH74.chevalleyExceptionalModel_of_lieModel (by decide) hL
    exact false_of_untwisted_slForm oddExcInnerDiagSLForm_E8 hm.1.1 hp2'
      (hm.2 : UntwistedChevalleyModel K .E8 (p' ^ f')) hC

theorem false_of_propCData_ree {K : Type} [Group K] [Finite K] {n' p' f' : ℕ}
    (hL : LieModel K .twistedG2 n' p' f') {x : K} {R₁ R₂ : Subgroup K} {p n : ℕ} [Fact p.Prime]
    (hC : PropCData x R₁ R₂ p n) : False :=
  (oddReeInvolutionSLForm_holds K n' p' f' hL x hC.orderOf_eq R₂ hC.le₂ hC.comp₂).2.2 hC.mem

theorem false_of_propCData_twisted {K : Type} [Group K] [Finite K] (hsimple : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) {τ : StatedLieTag} {n' p' f' : ℕ}
    (hτ : τ = .twistedE6 ∨ τ = .trialityD4) (hp2' : p' ≠ 2) (hL : LieModel K τ n' p' f')
    {x : K} {R₁ R₂ : Subgroup K} {p n : ℕ} [Fact p.Prime] (hC : PropCData x R₁ R₂ p n) :
    False := by
  have hxZ : x ∉ center K := by
    intro hx
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) with h | h
    · rw [h, mem_bot] at hx
      have := hC.orderOf_eq
      rw [hx, orderOf_one] at this
      exact absurd this (by norm_num)
    · obtain ⟨a, b, hab⟩ := hnab
      exact hab ((mem_center_iff.1 (h ▸ mem_top b)) a)
  have hαo := orderOf_conj_eq_two hC.orderOf_eq hxZ
  have hn0 : n' = 0 := by
    rcases hL with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · rcases hτ with rfl | rfl <;> exact absurd h (by decide)
    · exact h
    · exact h
    · exact h
  subst hn0
  rcases hτ with rfl | rfl
  · have hm := GH74.chevalleyExceptionalModel_of_lieModel (by decide) hL
    have : Fact p'.Prime := ⟨hm.1.1⟩
    have hf : f' ≠ 0 := by have := hm.1.2.1; omega
    obtain ⟨hq, hsl⟩ := oddTwistedE6InnerSLForm_holds K p' f' hm.1.1 hp2' hm.1 hL
      (MulAut.conj x) hαo ⟨x, rfl⟩
    exact false_of_conj_slForm (ringChar_galoisField_ne_two hp2') hq
      (hsl (GaloisField p' f') (GaloisField.card p' f' hf)) hC
  · have hm := GH74.chevalleyExceptionalModel_of_lieModel (by decide) hL
    have : Fact p'.Prime := ⟨hm.1.1⟩
    have hf : f' ≠ 0 := by have := hm.1.2.1; omega
    obtain ⟨hq, hsl⟩ := oddTrialityInnerSLForm_holds K p' f' hm.1.1 hp2' hm.1 hL
      (MulAut.conj x) hαo ⟨x, rfl⟩
    exact false_of_conj_slForm (ringChar_galoisField_ne_two hp2') hq
      (hsl (GaloisField p' f') (GaloisField.card p' f' hf)) hC

theorem burgoyneExcPropCTwistedInput_holds :
    ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
      ∀ (τ : StatedLieTag) (n' p' f' : ℕ), (τ = .twistedE6 ∨ τ = .trialityD4) → p' ≠ 2 →
        LieModel K τ n' p' f' →
      ∀ x : K, orderOf x = 2 → ∀ R₁ R₂ : Subgroup K,
        R₁ ≤ centralizer ({x} : Set K) → IsPComponent 2 (R₁.subgroupOf (centralizer ({x} : Set K))) →
        R₂ ≤ centralizer ({x} : Set K) → IsPComponent 2 (R₂.subgroupOf (centralizer ({x} : Set K))) →
      ∀ (p n : ℕ) [Fact p.Prime], p ≠ 2 → 0 < n →
        Nonempty (R₁ ⧸ pPrimeCore 2 R₁ ≃* PSL(2, GaloisField p n)) →
        Nonempty (R₂ ⧸ pPrimeCore 2 R₂ ≃* SL(2, GaloisField p n)) → x ∈ R₂ → False := by
  intro K _ _ hsimple hnab τ n' p' f' hτ hp2' hL x hx R₁ R₂ hR₁ hR₁c hR₂ hR₂c p n _ hp2 hn
    he₁ he₂ hmem
  exact false_of_propCData_twisted hsimple hnab hτ hp2' hL
    ⟨hp2, hn, hx, hR₁, hR₁c, hR₂, hR₂c, he₁, he₂, hmem⟩

theorem burgoyneExcPropCInput_of_twisted :
    BurgoyneExcPropCInput := by
  have hTw := burgoyneExcPropCTwistedInput_holds
  intro K _ _ hsimple hnab τ n' p' f' hτ hG2 hp2' hL x hx R₁ R₂ hR₁ hR₁c hR₂ hR₂c p n _ hp2 hn
    he₁ he₂ hmem
  have hC : PropCData x R₁ R₂ p n := ⟨hp2, hn, hx, hR₁, hR₁c, hR₂, hR₂c, he₁, he₂, hmem⟩
  have hcases : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .twistedE6 ∨ τ = .trialityD4 ∨
      τ = .twistedG2 := by
    revert hτ hG2
    cases τ <;> decide
  rcases hcases with h | h | h | h | h | h | h
  · exact false_of_propCData_untwisted (Or.inl h) hp2' hL hC
  · exact false_of_propCData_untwisted (Or.inr (Or.inl h)) hp2' hL hC
  · exact false_of_propCData_untwisted (Or.inr (Or.inr (Or.inl h))) hp2' hL hC
  · exact false_of_propCData_untwisted (Or.inr (Or.inr (Or.inr h))) hp2' hL hC
  · exact hTw K hsimple hnab τ n' p' f' (Or.inl h) hp2' hL x hx R₁ R₂ hR₁ hR₁c hR₂ hR₂c p n hp2 hn
      he₁ he₂ hmem
  · exact hTw K hsimple hnab τ n' p' f' (Or.inr h) hp2' hL x hx R₁ R₂ hR₁ hR₁c hR₂ hR₂c p n hp2 hn
      he₁ he₂ hmem
  · subst h
    exact false_of_propCData_ree hL hC

theorem burgoyneExcPropCInput_holds : BurgoyneExcPropCInput :=
  burgoyneExcPropCInput_of_twisted

end CFSG.ComponentClassification.Burgoyne.C

namespace CFSG.ComponentClassification.Burgoyne

open CFSG.ComponentClassification.TBLit

theorem burgoynePropC_holds : BurgoynePropC :=
  burgoynePropC_of_input C.burgoyneExcPropCInput_holds

end CFSG.ComponentClassification.Burgoyne
