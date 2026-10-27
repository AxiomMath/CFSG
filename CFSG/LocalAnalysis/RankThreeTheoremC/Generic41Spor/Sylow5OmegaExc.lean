module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5OmegaReduction
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5OmegaArith
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcToral
import CFSG.RankThree.PartOne.K133H.F4Weyl
import CFSG.RankThree.PartOne.K133H.G2Plane
import CFSG.RankThree.PartOne.KGD.D4Weyl
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5Omega

open CFSG.Open
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.RankFourTheoremC (isMulCommutative_sylow_of_surjective
  isMulCommutative_sylow_adjointGroup isMulCommutative_sylow_derivedCentralQuotient
  crossExc_not_dvd_pow_of_ne)

private theorem isMulCommutative_sylow_of_mulEquiv' {K Q : Type} [Group K] [Group Q] [Finite K]
    {p : ℕ} [Fact p.Prime] (e : K ≃* Q) (h : ∀ R : Sylow p Q, IsMulCommutative (R : Subgroup Q))
    (P : Sylow p K) : IsMulCommutative (P : Subgroup K) := by
  haveI : Finite Q := Finite.of_equiv K e.toEquiv
  exact isMulCommutative_sylow_of_surjective e.symm.toMonoidHom e.symm.surjective h P

private theorem factorization_card_eq_five {K : Type} [Group K] [Finite K] (S : Sylow 5 K)
    (hS : Nat.card S = 5 ^ 5) : (Nat.card K).factorization 5 = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h := Sylow.card_eq_multiplicity S
  rw [hS] at h
  exact (Nat.pow_right_injective (by norm_num : 2 ≤ 5) h).symm

private theorem five_not_dvd_card_weylGroup_F4 :
    ¬ 5 ∣ Nat.card (WeylGroup Tag.F4) := by
  rw [CFSG.RankThree.PartOne.K133H.card_weylGroup_F4]
  decide

section Suzuki

private local instance : DecidableEq (Equiv.Perm (Fin 3)) :=
  Fintype.decidableEqEquivFintype

private theorem certificate43_of_decide :
      ∀ s t : Equiv.Perm (Fin 3),
        (s ≠ 1 ∧ s ^ 2 = 1) → (t ≠ 1 ∧ t ^ 2 = 1) → s ≠ t →
          (s * t) ^ 3 = 1 ∧ s * t ≠ 1 := by
  decide +kernel

private theorem isMulCommutative_sylow_of_suzukiModel {K : Type} [Group K] [Finite K] {ℓ f : ℕ}
    (h : SuzukiModel K ℓ f) (S : Sylow 5 K) : IsMulCommutative (S : Subgroup K) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI := certificate43_of_decide
  obtain ⟨-, a, ha, F, _, _, hfa, hcard, ⟨e⟩⟩ := h
  have hF : Nat.card F = 2 ^ (2 * a + 1) := by rw [hcard, hfa]
  let e' : K ≃* GLASzGroup a F :=
    e.trans (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a F))
  haveI := CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.suzuki_model_oddSylow_cyclic
    a ha hF e' 5 (by norm_num) S
  infer_instance

end Suzuki

section Adjoint


private theorem five_not_dvd_card_weylGroup_G2 : ¬ 5 ∣ Nat.card (WeylGroup Tag.G2) := by
  rw [CFSG.RankThree.PartOne.K133H.card_weylGroup_G2]
  decide

private theorem isMulCommutative_sylow_of_untwisted {K : Type} [Group K] [Finite K] {τ : Tag}
    {q p : ℕ} (hp : p.Prime) (hW : ¬ p ∣ Nat.card (WeylGroup τ)) (hq : ¬ p ∣ q)
    (h : UntwistedChevalleyModel K τ q) (P : Sylow p K) : IsMulCommutative (P : Subgroup K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  have hpF : ¬ p ∣ Nat.card F := hF ▸ hq
  exact isMulCommutative_sylow_of_mulEquiv' e
    (isMulCommutative_sylow_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      (fun S => isMulCommutative_sylow_adjointGroup hp hW hpF S)) P

private theorem isMulCommutative_sylow_of_derivedCentralQuotient {K : Type} [Group K] [Finite K]
    {τ : Tag} {F : Type} [Field F] [Finite F] {H : Subgroup (ModGL τ F)}
    (hH : H ≤ adjointGroup τ F) {p : ℕ} (hp : p.Prime) (hW : ¬ p ∣ Nat.card (WeylGroup τ))
    (hpF : ¬ p ∣ Nat.card F) (e : K ≃* DerivedCentralQuotient H) (P : Sylow p K) :
    IsMulCommutative (P : Subgroup K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact isMulCommutative_sylow_of_mulEquiv' e
    (fun R => isMulCommutative_sylow_derivedCentralQuotient hH hp hW hpF R) P

private theorem isMulCommutative_sylow_of_twisted {K : Type} [Group K] [Finite K] {t : TwistTag}
    {q p : ℕ} (hp : p.Prime) (hW : ¬ p ∣ Nat.card (WeylGroup t.tag)) (hq : ¬ p ∣ q)
    (h : TwistedChevalleyModel K t q) (P : Sylow p K) : IsMulCommutative (P : Subgroup K) := by
  obtain ⟨F, _, _, hF, σ, -, ⟨e⟩⟩ := h
  have hpF : ¬ p ∣ Nat.card F := by
    rw [hF]
    exact fun hd => hq (hp.dvd_of_dvd_pow hd)
  exact isMulCommutative_sylow_of_derivedCentralQuotient inf_le_left hp hW hpF e P

private theorem isMulCommutative_sylow_of_reeTitsRelation {K : Type} [Group K] [Finite K]
    {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank)} {L : Finset (Fin τ.rank)} {ℓ f a p : ℕ}
    (hp : p.Prime) (hW : ¬ p ∣ Nat.card (WeylGroup τ)) (hq : ¬ p ∣ ℓ ^ f)
    (h : ReeTitsRelationModel K τ ρ L ℓ f a) (P : Sylow p K) :
    IsMulCommutative (P : Subgroup K) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  exact isMulCommutative_sylow_of_derivedCentralQuotient inf_le_left hp hW (hF ▸ hq) e P

private theorem exceptionalCase_of_factorization
    (hE6 : ∀ q : ℕ, ¬ 5 ∣ q → (ordE6 q).factorization 5 ≠ 5)
    (hE7 : ∀ q : ℕ, ¬ 5 ∣ q → (ordE7 q).factorization 5 ≠ 5)
    (h2E6 : ∀ q : ℕ, ¬ 5 ∣ q → (ordTwistedE6 q).factorization 5 ≠ 5) : ExceptionalCase := by
  intro K _ _ t ℓ f ht hmodel hℓ S hS
  have hℓp : ℓ.Prime := hmodel.admissible.1
  have h5q : ¬ 5 ∣ ℓ ^ f := crossExc_not_dvd_pow_of_ne Nat.prime_five hℓp hℓ
  have hv := factorization_card_eq_five S hS
  have hD4 : ¬ 5 ∣ Nat.card (WeylGroup TwistTag.D4.tag) :=
    CFSG.RankThree.PartOne.KGD.not_dvd_card_weylGroup_D4 Nat.prime_five (by norm_num)
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    obtain ⟨-, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
    exact isMulCommutative_sylow_of_untwisted Nat.prime_five five_not_dvd_card_weylGroup_G2 h5q
      hm S
  ·
    obtain ⟨-, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
    exact isMulCommutative_sylow_of_untwisted Nat.prime_five five_not_dvd_card_weylGroup_F4 h5q
      hm S
  ·
    have hc := CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional
      (hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags]))
    rw [hc] at hv
    exact absurd hv (hE6 _ h5q)
  ·
    have hc := CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional
      (hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags]))
    rw [hc] at hv
    exact absurd hv (hE7 _ h5q)
  ·
    have hc := CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional
      (hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags]))
    rw [hc] at hv
    exact absurd hv (h2E6 _ h5q)
  ·
    obtain ⟨-, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
    exact isMulCommutative_sylow_of_twisted (t := .D4) Nat.prime_five hD4 h5q hm S
  ·
    rcases hmodel with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hm⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact isMulCommutative_sylow_of_suzukiModel hm S
  ·
    obtain ⟨-, -, _, -, hm⟩ := hmodel.reeTitsModel (by simp [reeTitsTags])
    exact isMulCommutative_sylow_of_reeTitsRelation Nat.prime_five five_not_dvd_card_weylGroup_G2
      h5q hm S
  ·
    obtain ⟨-, -, _, -, hm⟩ := hmodel.reeTitsModel (by simp [reeTitsTags])
    exact isMulCommutative_sylow_of_reeTitsRelation Nat.prime_five five_not_dvd_card_weylGroup_F4
      h5q hm S
  ·
    obtain ⟨-, -, _, -, hm⟩ := hmodel.reeTitsModel (by simp [reeTitsTags])
    exact isMulCommutative_sylow_of_reeTitsRelation Nat.prime_five five_not_dvd_card_weylGroup_F4
      h5q hm S

theorem exceptionalCase_holds : ExceptionalCase :=
  exceptionalCase_of_factorization (fun _ h => factorization_ordE6_ne_five h)
    (fun _ h => factorization_ordE7_ne_five h) (fun _ h => factorization_ordTwistedE6_ne_five h)

end Adjoint

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5Omega
