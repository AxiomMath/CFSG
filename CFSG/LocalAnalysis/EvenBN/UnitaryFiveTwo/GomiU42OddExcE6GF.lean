module

public import CFSG.LieType.Chevalley.LangQuadraticFieldCosetConjugacy
import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcDiv

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem gomi_commutator_le_self {M : Type} [Group M] (H : Subgroup M) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun g hg h hh => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hg hh) (H.inv_mem hg)) (H.inv_mem hh)

theorem gomi_E6_graphField_false
    {F : Type} [Field F] [Finite F] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hF : Nat.card F = (p ^ e) ^ 2) (δ : F ≃+* F) (hδ : ∀ c, δ c = c ^ (p ^ e))
    {α : MulAut (adjointGroup TwistTag.E6.tag F)} {g : adjointGroup TwistTag.E6.tag F}
    {a : Fin TwistTag.E6.tag.rank → Fˣ}
    (hαg : ∀ h : adjointGroup TwistTag.E6.tag F, (α h : ModGL TwistTag.E6.tag F) =
      (g : ModGL TwistTag.E6.tag F) * rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 F *
        Units.map (entrywiseHom δ.toRingHom) (h : ModGL TwistTag.E6.tag F) *
          (diagramMap TwistTag.E6 F)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
            (g : ModGL TwistTag.E6.tag F)⁻¹)
    (hα : α ^ 2 = 1)
    (hdvd : Nat.card ↥(α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup TwistTag.E6.tag F))) ∣
      51840) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    (k := 2 * e) hp (by omega) (by rw [hF, ← pow_mul, mul_comm])
  obtain ⟨-, β, hβ, hβα⟩ :=
    exceptional_Lang_quadratic_field_coset_conjugacy hp he F hF δ.toRingHom hδ
  obtain ⟨-, hconj⟩ := hβα g a
  obtain ⟨ψ, -, -, ⟨e₁, -⟩, -⟩ := hconj α hαg (by rw [← sq]; exact hα)
  have hβfix : (β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup TwistTag.E6.tag F))).map
      (adjointGroup TwistTag.E6.tag F).subtype = twistedFixedGroup TwistTag.E6 F δ.toRingHom := by
    ext y
    simp only [Subgroup.mem_map, twistedFixedGroup, Subgroup.mem_inf]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u.2, ?_⟩
      change twistHom TwistTag.E6 F δ.toRingHom (u : ModGL TwistTag.E6.tag F) = u
      rw [twistHom_apply, ← hβ u]
      exact congrArg Subtype.val hu
    · rintro ⟨hyG, hyσ⟩
      refine ⟨⟨y, hyG⟩, Subtype.ext ?_, rfl⟩
      change (β ⟨y, hyG⟩ : ModGL TwistTag.E6.tag F) = y
      rw [hβ]
      change twistHom TwistTag.E6 F δ.toRingHom y = y at hyσ
      rw [twistHom_apply] at hyσ
      exact hyσ
  let e₂ : ↥(β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup TwistTag.E6.tag F))) ≃*
      ↥(twistedFixedGroup TwistTag.E6 F δ.toRingHom) :=
    (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans (MulEquiv.subgroupCongr hβfix)
  have hcard : Nat.card ↥(α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup TwistTag.E6.tag F))) =
      Nat.card ↥(twistedFixedGroup TwistTag.E6 F δ.toRingHom) :=
    Nat.card_congr (e₁.trans e₂).toEquiv
  have hmod : ChevalleyExceptionalModel
      (DerivedCentralQuotient (twistedFixedGroup TwistTag.E6 F δ.toRingHom)) .twistedE6 p e :=
    ⟨⟨hp, he, rfl⟩, F, inferInstance, inferInstance, hF, δ.toRingHom, hδ,
      ⟨MulEquiv.refl _⟩⟩
  have hord := CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional hmod
  have hpow : (p ^ e) ^ 36 ∣ Nat.card
      (DerivedCentralQuotient (twistedFixedGroup TwistTag.E6 F δ.toRingHom)) := by
    rw [hord]
    exact CFSG.EvenSmallLie.CatalogOrders.pow_dvd_ordTwistedE6 (p ^ e)
  have hdvd1 : Nat.card (DerivedCentralQuotient (twistedFixedGroup TwistTag.E6 F δ.toRingHom)) ∣
      Nat.card ↥(twistedFixedGroup TwistTag.E6 F δ.toRingHom) :=
    (Subgroup.card_quotient_dvd_card _).trans
      (Subgroup.card_dvd_of_le (gomi_commutator_le_self _))
  have h5 : (p ^ e) ^ 5 ∣ 51840 := by
    refine (pow_dvd_pow _ (by norm_num : 5 ≤ 36)).trans (hpow.trans (hdvd1.trans ?_))
    rw [← hcard]
    exact hdvd
  have hpodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  exact gomi_not_pow_five_dvd hpodd (Nat.one_lt_pow (by omega) hp.one_lt) h5

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
