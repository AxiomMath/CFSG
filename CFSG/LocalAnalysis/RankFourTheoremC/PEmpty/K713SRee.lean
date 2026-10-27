module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SCatalog
public import CFSG.RankThree.SteinbergR3ESuzukiFieldSplitting
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.SmallReeWard
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Sporadic.Schreier.TitsAutD

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S

open CFSG.Open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

theorem liftClause_suzuki {S : Type} [Group S] [Finite S]
    {p f : ℕ} (h : SuzukiModel S p f) : LiftClause S := by
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := h
  subst hf
  haveI : Finite (suzukiGroup a K) := Finite.of_equiv S e.toEquiv
  haveI : Finite (RingAut K) := finite_ringAut K
  refine LiftClause.of_mulEquiv e fun q hq _ _ => ?_
  obtain ⟨-, ⟨e2, he2⟩, -⟩ := CFSG.RankThree.Automorphisms.Suzuki_full_field_automorphism_splitting
    a ha K hK
  refine outLift_of_hom_surj hq (CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.szFieldAut a K)
    (fun σ hσ => CFSG.RankThree.Automorphisms.eq_one_of_szFieldAut_mem_inner ha hK hσ)
    fun α => ?_
  obtain ⟨⟨g, σ⟩, hgσ⟩ := e2.surjective α
  exact ⟨g, σ, by rw [← hgσ, he2]⟩

theorem liftClause_smallRee
    {S : Type} [Group S] [Finite S] {p f : ℕ} (h : ReeTitsModel S .twistedG2 p f) :
    LiftClause S := by
  obtain ⟨-, -, hp3, ⟨a₀, ha₀, hfa₀⟩, hiso⟩ := CFSG.LieType.Ree.small_Ree_model_Schreier S p f h
  obtain ⟨-, a, hfa, K, _, _, hK, ⟨e⟩⟩ := h
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K CFSG.LieType.Ree.ReeTag.G2.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK, hp3]
    rfl)
  obtain ⟨E⟩ := hiso a K hfa hK ⟨e⟩
  have ha : 1 ≤ a := by omega
  have hK' : Nat.card K = 3 ^ (2 * a + 1) := by rw [hK, hp3, hfa]
  haveI : Finite (CFSG.LieType.Ree.ReeTag.G2.reeGamma K a) := Finite.of_equiv S E.toEquiv
  haveI : Finite (RingAut K) := finite_ringAut K
  refine LiftClause.of_mulEquiv E fun q hq _ _ => ?_
  obtain ⟨-, -, -, ⟨R, χ, -, hχ, -, -, -⟩, -, -⟩ :=
    CFSG.LieType.Ree.small_Ree_outer_three_kernel_field_complement a ha K hK'
  refine outLift_of_hom_surj hq (CFSG.LieType.Ree.ReeTag.G2.reeGammaFieldAutHom K a)
    (fun σ hσ => ?_) fun α => ?_
  · rw [CFSG.LieType.Ree.ReeTag.reeGammaFieldAutHom_apply] at hσ
    have h1 : (QuotientGroup.mk (CFSG.LieType.Ree.ReeTag.G2.reeGammaFieldAut K a σ) :
        Outer (CFSG.LieType.Ree.ReeTag.G2.reeGamma K a)) = 1 := (QuotientGroup.eq_one_iff _).2 hσ
    rw [← hχ σ, h1, map_one]
  · obtain ⟨x, τ, hxτ⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.smallReeOuterIsField a ha K
      (hK' ▸ rfl) α
    exact ⟨x, τ, by rw [hxτ, CFSG.LieType.Ree.ReeTag.reeGammaFieldAutHom_apply]⟩

theorem liftClause_largeRee
    {S : Type} [Group S] [Finite S] {p f : ℕ} (h : ReeTitsModel S .twistedF4 p f) :
    LiftClause S := by
  obtain ⟨-, -, -, hp2, ⟨a₀, ha₀, hfa₀⟩, hiso⟩ :=
    CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier S p f h
  obtain ⟨-, a, hfa, K, _, _, hK, ⟨e⟩⟩ := h
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hp2, hfa]
  haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_of_card_eq_prime_pow (f := 2 * a + 1)
    (by
      rw [← Nat.card_eq_fintype_card, hK']
      rfl)
  obtain ⟨E⟩ := hiso a K hfa hK ⟨e⟩
  have ha : 1 ≤ a := by omega
  haveI : Finite (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) := Finite.of_equiv S E.toEquiv
  haveI : Finite (RingAut K) := finite_ringAut K
  refine LiftClause.of_mulEquiv E fun q hq _ _ => ?_
  obtain ⟨-, hnf, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK'
  refine outLift_of_hom_surj hq (CFSG.LieType.Ree.ReeTag.F4.reeGammaFieldAutHom K a)
    (fun σ hσ => ?_) fun α => ?_
  · rw [CFSG.LieType.Ree.ReeTag.reeGammaFieldAutHom_apply] at hσ
    obtain ⟨g, hg⟩ := hσ
    have h1 := (hnf (CFSG.LieType.Ree.ReeTag.F4.reeGammaFieldAut K a σ)).unique
      (y₁ := (1, σ)) (y₂ := (g, 1)) (by simp) (by
        have h1 : CFSG.LieType.Ree.ReeTag.F4.reeGammaFieldAut K a 1 = 1 := by
          rw [← CFSG.LieType.Ree.ReeTag.reeGammaFieldAutHom_apply, map_one]
        simp only [h1, mul_one]
        exact hg.symm)
    exact (Prod.mk.inj h1).2
  · obtain ⟨⟨x, τ⟩, hxτ, -⟩ := hnf α
    exact ⟨x, τ, by rw [hxτ, CFSG.LieType.Ree.ReeTag.reeGammaFieldAutHom_apply]⟩

theorem liftClause_tits
    {S : Type} [Group S] [Finite S] {p f : ℕ} (h : ReeTitsModel S .Tits p f) : LiftClause S := by
  obtain ⟨E⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv S p f h
  haveI := Finite.of_equiv S E.toEquiv
  refine LiftClause.of_mulEquiv E (liftClause_of_not_dvd fun q hq hq2 _ hd => ?_)
  rw [CFSG.Sporadic.Schreier.Tits.card_outer_titsD] at hd
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 hd)

theorem liftClause_reeTits
    {t : StatedLieTag} {p f : ℕ} (ht : t ∈ reeTitsTags) :
    FamilyLift fun S _ => ReeTitsModel S t p f := by
  intro S _ _ _ _ h
  simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · exact liftClause_smallRee h
  · exact liftClause_largeRee h
  · exact liftClause_tits h

theorem liftClause_suzuki_family {p f : ℕ} :
    FamilyLift fun S _ => SuzukiModel S p f := by
  intro S _ _ _ _ h
  exact liftClause_suzuki h

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S
