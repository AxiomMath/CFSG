module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6Three
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6ThreeDiag
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6ThreeDiagTw
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUTorus
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterT
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterThree
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcTorus
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerTorus
import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterFieldAny
import CFSG.HardMathSupport.Timmesfeld.LangTorus.SubnormalTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityTw
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwoDProved
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6
open CFSG.HardMathSupport.Timmesfeld.LangTorus
  (anyKindCommuteT_holds anyKindNoFrobenius_of_outer threeBigComponents_holds langSubnormal_provedT
    langComponentsQuasisimple_inner_holdsT langComponentsQuasisimple_exc_provedT)

set_option linter.unusedSectionVars false

theorem e6IsotropicDiagBalance_holds :
    ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K → Nat.card K ≠ 2 →
      ∀ (K₁ : IntermediateField K (AlgebraicClosure K)) [Finite K₁],
        (∀ c : Kˣ, ∃ u : K₁ˣ, u ^ 3 = Units.map (algebraMap K K₁).toMonoidHom c) →
        ∀ D : Subgroup (MulAut (adjointGroup Tag.E6 K)), D ≤ e6Inndiag K → IsElemAbelian 3 D →
          Nat.card D = 3 ^ 2 →
          (∀ x y : ↥(e6Data_valid.minGroup K₁),
            (e6Isogeny K₁ x : ModGL Tag.E6 K₁) ∈
              ((D.comap (e6InndiagConj K)).map (e6InndiagGL K).subtype).map
                (baseChangeGL (algebraMap K K₁)) →
            (e6Isogeny K₁ y : ModGL Tag.E6 K₁) ∈
              ((D.comap (e6InndiagConj K)).map (e6InndiagGL K).subtype).map
                (baseChangeGL (algebraMap K K₁)) →
            x * y = y * x) →
          ∀ H : Subgroup (MulAut (adjointGroup Tag.E6 K)), innerAut (adjointGroup Tag.E6 K) ≤ H →
            localDeltaIn 3 H D = ⊥ := by
  intro K _ _ h3 h2 K₁ _ hroot D hDd hD hcard hab H hH
  have hK4 : 4 ≤ Nat.card K := four_le_of_not_three_dvd Finite.one_lt_card h3 h2
  have hinj := e6InndiagConj_injective K hK4
  have hDr : D ≤ (e6InndiagConj K).range := by
    rw [range_e6InndiagConj]
    exact hDd
  have hmap : (D.comap (e6InndiagConj K)).map (e6InndiagConj K) = D :=
    Subgroup.map_comap_eq_self hDr
  have hpow : ∀ x ∈ D.comap (e6InndiagConj K), x ^ 3 = 1 := fun x hx =>
    hinj (by rw [map_pow, map_one]; exact hD.2 _ hx)
  have hcard₀ : Nat.card (D.comap (e6InndiagConj K)) = 3 ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap, hcard]
  have hC₁ : ∀ x ∈ D.comap (e6InndiagConj K),
      baseChangeGL (algebraMap K K₁) (x : ModGL Tag.E6 K) ∈ adjointGroup Tag.E6 K₁ := fun x _ =>
    map_e6InndiagGL_le _ hroot (Subgroup.mem_map_of_mem _ x.2)
  obtain ⟨w, Fr, hFr, g0, hg0C, hg0, hmem⟩ :=
    e6IsotropicToralInndiag_of_planeToralLang e6PlaneToralLang_proved K h3 K₁
      (D.comap (e6InndiagConj K)) hpow hcard₀ hC₁ hab
  have h := e6Three_langTorusPlaneBalanceInndiag langSubnormal_provedT
    langComponentsQuasisimple_inner_holdsT langComponentsQuasisimpleT_suN_proved
    langComponentsQuasisimpleT_twoD_proved langComponentsQuasisimple_exc_provedT
    anyKindCommuteT_holds threeBigComponents_holds w K ⟨h3, h2⟩ Fr hFr g0 hg0C hg0
    (D.comap (e6InndiagConj K)) hpow (by rw [hcard₀]; norm_num) hmem H hH
  rwa [hmap] at h

theorem twistedE6IsotropicDiagBalance_holds :
    ∀ ℓ f : ℕ, ℓ.Prime → ℓ ≠ 3 → 1 ≤ f → ℓ ^ f ≠ 2 → ∀ (K : Type) [Field K] [Finite K],
      Nat.card K = (ℓ ^ f) ^ 2 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
      ∀ (K₁ : IntermediateField K (AlgebraicClosure K)) [Finite K₁],
        (∀ c : Kˣ, ∃ u : K₁ˣ, u ^ 3 = Units.map (algebraMap K K₁).toMonoidHom c) →
        ∀ D : Subgroup (MulAut (twistedE6RootGroup K σ)),
          D ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → IsElemAbelian 3 D → Nat.card D = 3 ^ 2 →
          (∀ x y : ↥(e6Data_valid.minGroup K₁),
            (e6Isogeny K₁ x : ModGL Tag.E6 K₁) ∈
              ((D.comap (twistedE6InndiagConj K σ)).map (twistedE6InndiagGL K σ).subtype).map
                (baseChangeGL (algebraMap K K₁)) →
            (e6Isogeny K₁ y : ModGL Tag.E6 K₁) ∈
              ((D.comap (twistedE6InndiagConj K σ)).map (twistedE6InndiagGL K σ).subtype).map
                (baseChangeGL (algebraMap K K₁)) →
            x * y = y * x) →
          ∀ H : Subgroup (MulAut (twistedE6RootGroup K σ)), innerAut (twistedE6RootGroup K σ) ≤ H →
            localDeltaIn 3 H D = ⊥ := by
  intro ℓ f hℓ hℓ3 hf hq2 K _ _ hK σ hσ K₁ _ hroot D hDd hD hcard hab H hH
  have h3 : ¬ 3 ∣ ℓ ^ f := fun h =>
    hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hinj := twistedE6InndiagConj_injective hℓ hf hK σ hσ
  have hDr : D ≤ (twistedE6InndiagConj K σ).range := by
    rw [range_twistedE6InndiagConj]
    exact hDd
  have hmap : (D.comap (twistedE6InndiagConj K σ)).map (twistedE6InndiagConj K σ) = D :=
    Subgroup.map_comap_eq_self hDr
  have hpow : ∀ x ∈ D.comap (twistedE6InndiagConj K σ), x ^ 3 = 1 := fun x hx =>
    hinj (by rw [map_pow, map_one]; exact hD.2 _ hx)
  have hcard₀ : Nat.card (D.comap (twistedE6InndiagConj K σ)) = 3 ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap, hcard]
  have hC₁ : ∀ x ∈ D.comap (twistedE6InndiagConj K σ),
      baseChangeGL (algebraMap K K₁) (x : ModGL TwistTag.E6.tag K) ∈ adjointGroup Tag.E6 K₁ :=
    fun x _ => map_twistedE6InndiagGL_le σ _ hroot (Subgroup.mem_map_of_mem _ x.2)
  obtain ⟨v, Fr, hFr, g0, hg0C, hg0, hmem⟩ :=
    twistedE6IsotropicToralInndiag_of_planeToralLang twistedE6PlaneToralLang_proved ℓ f hℓ hℓ3 hf
      K hK σ hσ K₁ (D.comap (twistedE6InndiagConj K σ)) hpow hcard₀ hC₁ hab
  have h := twistedE6Three_langTorusPlaneBalanceInndiag langSubnormal_provedT
    langComponentsQuasisimple_inner_holdsT langComponentsQuasisimpleT_suN_proved
    langComponentsQuasisimpleT_twoD_proved langComponentsQuasisimple_exc_provedT
    anyKindCommuteT_holds threeBigComponents_holds v ℓ f hℓ hf ⟨h3, hq2⟩ K hK σ hσ Fr hFr g0 hg0C
    hg0 (D.comap (twistedE6InndiagConj K σ)) hpow (by rw [hcard₀]; norm_num) hmem H hH
  rwa [hmap] at h

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
