module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4InnerAux.Torality
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4InnerAux.Balance

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups

set_option linter.unusedSectionVars false


theorem innerPlaneBalance_graphFixedRootGroup_D4_three (hcp : LangComponentPieces)
    (hAK : AnyKindCommute) (hAF : AnyKindNoFrobenius) (hbig : ThreeBigComponents)
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hq2 : ℓ ^ f ≠ 2)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    InnerPlaneBalance 3 (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  have hq3 : ¬ 3 ∣ ℓ ^ f := fun h =>
    hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hC : Function.Injective (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    mulAut_conj_injective_of_center_eq_bot (exceptional_fixed_center_trivial TwistTag.D4 K σ)
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hCdef
  intro E hEin hE hEc H hH
  set D₀ : Subgroup C := E.comap (MulAut.conj : C →* MulAut C) with hD₀
  have hDD : D₀.map (MulAut.conj : C →* MulAut C) = E := Subgroup.map_comap_eq_self hEin
  have hD₀c : Nat.card D₀ = 3 ^ 2 := by
    rw [← Subgroup.card_map_of_injective hC, hDD, hEc]
  have hD₀p : ∀ x ∈ D₀, x ^ 3 = 1 := fun x hx => hC (by rw [map_pow, map_one]; exact hE.2 _ hx)
  set Fr : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius (AlgebraicClosure K) ℓ f
    with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨v, g0, hg0C, hg0, hmem⟩ := triD4PlaneToralLang hℓ hℓ3 hf K hK σ hσ D₀ hD₀p hD₀c Fr hFr
  rw [← hDD]
  exact triD4Three_planeBalance_at_torus hcp hAK hAF hbig hℓ hf hq3 hq2 K hK σ hσ hFr hg0C hg0 D₀
    hD₀p (by rw [hD₀c]; norm_num) hmem hH

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
