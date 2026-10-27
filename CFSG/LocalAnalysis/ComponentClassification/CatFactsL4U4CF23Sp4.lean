module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CF23Sp4Lin
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorSp
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Base

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open Subgroup Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RestrictedStd
open LinearMap (BilinForm)
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open CFSG.ComponentClassification.CatalogueBSymplecticB
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OddClassSelector

namespace Sp4

theorem card_mul_two_of_lieModel {Y : Type} [Group Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : LieModel Y .PSL 2 p f) : Nat.card Y * 2 = p ^ f * ((p ^ f) ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_mul_two_of_statedClassicalModel_psl_two_odd hp hp2 (hm.statedClassicalModel (by decide))

theorem eq_of_mul_sq_sub_one_eq {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : a * (a ^ 2 - 1) = b * (b ^ 2 - 1)) : a = b := by
  have key : ∀ m n : ℕ, 1 ≤ m → m < n → m * (m ^ 2 - 1) < n * (n ^ 2 - 1) := by
    intro m n hm hmn
    have h1 : m ^ 2 - 1 ≤ n ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hmn.le 2) 1
    have h2 : 0 < n ^ 2 - 1 := by
      have : 2 ≤ n := by omega
      have : 4 ≤ n ^ 2 := by nlinarith
      omega
    calc m * (m ^ 2 - 1) ≤ m * (n ^ 2 - 1) := Nat.mul_le_mul_left m h1
      _ < n * (n ^ 2 - 1) := Nat.mul_lt_mul_of_pos_right hmn h2
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (key a b ha hab).ne
  · exact hab
  · exact absurd h (key b a hb hab).ne'

theorem mul_sq_sub_one_ne_5040 (Q : ℕ) : Q * (Q ^ 2 - 1) ≠ 5040 := by
  intro h
  rcases Nat.lt_or_ge Q 18 with hQ | hQ
  · have h1 : Q * (Q ^ 2 - 1) ≤ 17 * (17 ^ 2 - 1) :=
      Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right (Nat.pow_le_pow_left (by omega) 2) 1)
    norm_num at h1
    omega
  · have h1 : 18 * (18 ^ 2 - 1) ≤ Q * (Q ^ 2 - 1) :=
      Nat.mul_le_mul hQ (Nat.sub_le_sub_right (Nat.pow_le_pow_left hQ 2) 1)
    norm_num at h1
    omega

theorem even_card_of_isQuasisimple {Q : Type*} [Group Q] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) : Even (Nat.card Q) := by
  obtain ⟨-, hs, hnab⟩ := hQ
  have heven := (SimpleEvenOrder.nonabelian_simple_even hnab).1
  obtain ⟨k, hk⟩ := Subgroup.card_quotient_dvd_card (center Q)
  rw [hk]
  exact heven.mul_right k

theorem center_eq_bot_of_simple {X : Type*} [Group X] (hXq : CFSG.IsQuasisimple X)
    [IsSimpleGroup X] : center X = ⊥ := by
  rcases (center X).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hXq.2.2
    have h1 : ∀ c : X ⧸ center X, c = 1 := fun c => by
      induction c using QuotientGroup.induction_on with
      | H x => exact (QuotientGroup.eq_one_iff x).mpr (h ▸ mem_top x)
    exact hab (by rw [h1 a, h1 b])

theorem lieModel_of_card {X : Type} [Group X] [Finite X] {ℓ e : ℕ} (hℓ : ℓ.Prime)
    (he : 1 ≤ e) (hXq : CFSG.IsQuasisimple X) (hs : IsSimpleGroup X)
    (hc : Nat.card X * 2 = (ℓ ^ e) ^ 2 * (((ℓ ^ e) ^ 2) ^ 2 - 1))
    (hsm : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        LieModel (X ⧸ center X) .PSL 2 p f) ∨
      Nonempty (X ⧸ center X ≃* alternatingGroup (Fin 7))) :
    LieModel (X ⧸ center X) .PSL 2 ℓ (2 * e) := by
  have hZ : center X = ⊥ := center_eq_bot_of_simple hXq
  have hcq : Nat.card (X ⧸ center X) = Nat.card X := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center X)
    have h2 : Nat.card (center X) = 1 := by rw [hZ, Subgroup.card_bot]
    rw [h2, mul_one] at h1
    exact h1.symm
  rcases hsm with ⟨p, f, hp, hp2, hf, -, hm⟩ | ⟨⟨e7⟩⟩
  · have h1 := card_mul_two_of_lieModel hp hp2 hm
    rw [hcq, hc] at h1
    have hQ : (ℓ ^ e) ^ 2 = p ^ f :=
      eq_of_mul_sq_sub_one_eq (pow_pos (pow_pos hℓ.pos e) 2) (pow_pos hp.pos f) h1
    rw [← pow_mul, mul_comm e 2] at hQ
    obtain ⟨hpl, hfe⟩ := Nat.Prime.pow_inj hℓ hp (show ℓ ^ (2 * e - 1 + 1) = p ^ (f - 1 + 1) by
      rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel hf]
      exact hQ)
    have hf2 : f = 2 * e := by omega
    rw [hpl, ← hf2]
    exact hm
  · exfalso
    have h1 : Nat.card X = 2520 := by
      rw [← hcq, Nat.card_congr e7.toEquiv, card_alternatingGroup_seven]
    rw [h1] at hc
    exact mul_sq_sub_one_ne_5040 _ hc.symm

end Sp4

theorem sp4_fixed_false {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ e)
    (hZ : center (StatedProj (StatedSp 2 K)) = ⊥)
    {α : MulAut (StatedProj (StatedSp 2 K))} (hα2 : α * α = 1) (hα1 : α ≠ 1)
    {X : Subgroup (StatedProj (StatedSp 2 K))}
    (hX : CFSG.Assembly.IsComponentOf X (fixedSubgroup α)) (hnt : NoTightWitness X)
    (hsm : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        LieModel (↥X ⧸ center ↥X) .PSL 2 p f) ∨
      Nonempty (↥X ⧸ center ↥X ≃* alternatingGroup (Fin 7)))
    (hZX : Odd (Nat.card (center ↥X)))
    (hexc : ¬ LieModel (↥X ⧸ center ↥X) .PSL 2 ℓ (2 * e)) : False := by
  classical
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ he hK
  have hchar : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have hXq : CFSG.IsQuasisimple X :=
    (AssemblyBPredicates.isQuasisimple_iff_native _).mp hX.2.2
  obtain ⟨Am, τσ, hα, hσ2, hdd, -, -⟩ :=
    (odd_symplectic_automorphism_semilinear_representation hchar le_rfl).2.2 α hα2 hα1
  by_cases hσ : τσ = 1
  · subst hσ
    have hX₁ := (isComponentOf_iff_isComponent_subgroupOf hX.1).mp hX
    have hXP : CFSG.IsPComponent 2 (X.subgroupOf (CatFactsSp4.fixOf α)) :=
      CatFactsSp4.isPComponent_two_of_quasisimple' hX.1 hXq hX₁.2
        (Sp4.even_card_of_isQuasisimple hXq)
    obtain ⟨hs, hc⟩ := sp4_linear hℓ hℓ2 he hK hZ hα2 hα1 Am hα hdd hXq hX.1 hXP hnt hZX
    exact hexc (Sp4.lieModel_of_card hℓ he hXq hs hc hsm)
  · obtain ⟨dd, hdd⟩ := hdd
    have hr1 : 1 ≤ 2 := by norm_num
    have hsX : SmallSource X := smallSource_of_cf23 hsm hZX
    set μ := multiplierUnit Am with hμdef
    have hμ := multiplierUnit_spec Am
    let e' := projectiveStatedEquiv (K := K) hr1
    have hBalt := SymplecticFlag.pairedSympForm_isAlt (K := K) (r := 2)
    have hBnd := SymplecticFlag.pairedSympForm_nondegenerate (K := K) (r := 2)
    have hdim := SymplecticFlag.finrank_standard (K := K) (r := 2)
    have hsX' : SmallSource (X.map e'.toMonoidHom) :=
      smallSource_of_mulEquiv (X.equivMapOfInjective _ e'.injective) hsX
    have hint : ∀ x, e' (α x) = projectiveSemilinearConjugation (pairedSympForm K 2) τσ
        (semilinearCoordMap (Am : GL (Fin 2 ⊕ Fin 2) K) τσ) μ (semilinearCoordMap_smul _ τσ)
        (semilinearCoordMap_form _ τσ μ hμ) (e' x) := by
      intro x
      rw [hα]
      exact projectiveStatedEquiv_conjAut_fieldAut hr1 Am τσ μ hμ x
    have hX' : CFSG.Assembly.IsComponentOf (X.map e'.toMonoidHom)
        (fixedSubgroup (projectiveSemilinearConjugation (pairedSympForm K 2) τσ
          (semilinearCoordMap (Am : GL (Fin 2 ⊕ Fin 2) K) τσ) μ (semilinearCoordMap_smul _ τσ)
          (semilinearCoordMap_form _ τσ μ hμ))) := by
      rw [← map_fixedSubgroup_of_comm e' _ _ hint]
      exact SymmetricLocal.isComponentOf_map_of_injective _ e'.injective hX
    have hsquare := semilinearCoordMap_sq (Am : GL (Fin 2 ⊕ Fin 2) K) τσ hσ2 dd hdd
    have hinv : ∀ x, (semilinearCoordMap (Am : GL (Fin 2 ⊕ Fin 2) K) τσ).symm
        ((semilinearCoordMap (Am : GL (Fin 2 ⊕ Fin 2) K) τσ).symm x) = (dd : K)⁻¹ • x :=
      fun x => by
        rw [AddEquiv.symm_apply_eq, AddEquiv.symm_apply_eq, hsquare, smul_smul,
          mul_inv_cancel₀ (Units.ne_zero dd), one_smul]
    have hφφ : ∀ g, semilinearConjugation (pairedSympForm K 2) τσ
        (semilinearCoordMap (Am : GL (Fin 2 ⊕ Fin 2) K) τσ) μ (semilinearCoordMap_smul _ τσ)
          (semilinearCoordMap_form _ τσ μ hμ) (semilinearConjugation (pairedSympForm K 2) τσ
            (semilinearCoordMap (Am : GL (Fin 2 ⊕ Fin 2) K) τσ) μ (semilinearCoordMap_smul _ τσ)
            (semilinearCoordMap_form _ τσ μ hμ) g) = g := by
      intro g
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      rw [semilinearConjugation_apply, semilinearConjugation_apply, hinv, map_smul, hsquare,
        smul_smul, mul_inv_cancel₀ (Units.ne_zero dd), one_smul]
    obtain ⟨Y, hY, ⟨σY, -, hσYk, -⟩, -⟩ := central_lift (scalarSigns (pairedSympForm K 2))
      (scalarSigns_central _) _ (semilinear_scalarSigns_invariant _ τσ _ μ _ _) hφφ hX'
    rw [fixed_semilinearConjugation_eq] at hY
    exact sp_field_false hℓ hℓ2 he hK le_rfl hdim hBalt hBnd τσ hσ2 hσ _ μ dd
      (semilinearCoordMap_smul _ τσ) (semilinearCoordMap_form _ τσ μ hμ) hsquare hY σY hσYk hsX'

theorem sp4_socle_false {A : Type} [Group A] {W : Subgroup A} [W.Normal]
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a}))
    (hstd : CFSG.IsStandardSubgroup L)
    (hsm : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        LieModel (↥L ⧸ center ↥L) .PSL 2 p f) ∨
      Nonempty (↥L ⧸ center ↥L ≃* alternatingGroup (Fin 7)))
    (hZL : Odd (Nat.card (center ↥L))) {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hexc : ¬ LieModel (↥L ⧸ center ↥L) .PSL 2 ℓ (2 * e))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ e)
    (θ : W ≃* StatedProj (StatedSp 2 K)) : False := by
  have h3 : 3 ≤ Nat.card K := by
    rw [hK]
    have := hℓ.two_le
    exact le_trans (by omega) (Nat.le_self_pow (by omega) ℓ)
  have : IsSimpleGroup (StatedProj (StatedSp 2 K)) := by
    refine CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num) ?_
    rcases Nat.lt_or_ge (Nat.card K) 4 with h | h
    · exact Or.inr (Or.inl ⟨by omega, le_rfl⟩)
    · exact Or.inl (Or.inr h)
  have hnab : ∃ x y : StatedProj (StatedSp 2 K), x * y ≠ y * x := by
    by_contra hc
    push Not at hc
    have hWle : W ≤ centralizer (W : Set A) := by
      intro w hw
      rw [mem_centralizer_iff]
      intro v hv
      have h1 := hc (θ ⟨v, hv⟩) (θ ⟨w, hw⟩)
      rw [← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val (θ.injective h1)
    rw [hCW] at hWle
    obtain ⟨x, hx⟩ := exists_ne (1 : StatedProj (StatedSp 2 K))
    apply hx
    have hw := hWle (θ.symm x).2
    rw [mem_bot] at hw
    have h1 : θ.symm x = 1 := Subtype.ext hw
    rw [← θ.apply_symm_apply x, h1, map_one]
  have hZ := OutcomeLocal.center_eq_bot_of_isSimpleGroup hnab
  obtain ⟨ρ, X, hinj, hinn, hX, hLX, ⟨eLX⟩⟩ := fixed_component_of_socle hCW θ hZ hLCW
  have hW := noTightWitness_of_isStandardSubgroup hinj hinn (conj_injective hZ) hstd hLX
  have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  have hαα : ρ a * ρ a = 1 := by
    rw [← map_mul, ← pow_two, ha2, map_one]
  have hα1 : ρ a ≠ 1 := by
    intro h
    have h1 : orderOf (ρ a) = orderOf a := orderOf_injective ρ hinj a
    rw [h, orderOf_one, ha] at h1
    exact absurd h1 (by norm_num)
  have eZ : ↥L ⧸ center ↥L ≃* ↥X ⧸ center ↥X :=
    QuotientGroup.congr (center L) (center X) eLX (Subgroup.map_center_eq eLX)
  have hcZ : Nat.card (center L) = Nat.card (center X) :=
    Nat.card_congr (Subgroup.centerCongr eLX).toEquiv
  refine sp4_fixed_false hℓ hℓ2 he hK hZ hαα hα1 hX hW ?_ (hcZ ▸ hZL)
    (fun h => hexc (LieType.CurtisTits.lieModel_of_mulEquiv eZ.symm h))
  rcases hsm with ⟨p, f, hp, hp2, hf, h5, hm⟩ | ⟨⟨e7⟩⟩
  · exact Or.inl ⟨p, f, hp, hp2, hf, h5, LieType.CurtisTits.lieModel_of_mulEquiv eZ hm⟩
  · exact Or.inr ⟨eZ.symm.trans e7⟩

theorem cf23InnerFusionFor_PSp4 :
    CF23InnerFusionFor fun Y _ => ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      LieModel Y .PSp 2 p f := by
  intro G _ _ N hN hC hτ α J hα hJN hJα hJ hstd hsm hZ hexc
  exfalso
  obtain ⟨p, f, hp, hp2, hf, hM⟩ := hτ
  have := hN
  obtain ⟨-, K, _, _, hK, ⟨θ⟩⟩ := statedClassicalModel_of_lieModel hM
    (by simp [chevalleyExceptionalTags]) (by simp [reeTitsTags]) (by decide)
  exact sp4_socle_false hC hα (isComponentOf_of_cf23 hJN hJα hJ) hstd hsm hZ hp hp2 hf
    (fun h => hexc (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, h, Or.inr (Or.inr (Or.inr hM))⟩))) hK θ

end CFSG.ComponentClassification.GSThmB.CF23I
