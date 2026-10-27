module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Split
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Cube
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Out
public import CFSG.ClassicalInvolution.Q3.TA3SOLG2D4

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Ree
open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

namespace Q5G2D4

theorem chevalleyExceptionalModel_of_lieModel {F : Type} [Group F]
    {t : Assembly.LowTwoRank.StatedLieTag} {p f : ℕ} (h : LieModel F t 0 p f)
    (h₁ : t ∉ classicalTags) (h₂ : t ∉ reeTitsTags) (h₃ : t ≠ .twistedB2) :
    ChevalleyExceptionalModel F t p f :=
  CFSG.Blueprint.LieModel.chevalleyExceptionalModel h (by revert h₁ h₂ h₃; cases t <;> decide)

end Q5G2D4

theorem outTwoCyclic_G2
    {X : Type} [Group X] {p f : ℕ}
    (hp2 : p ≠ 2) (h : ChevalleyExceptionalModel X .G2 p f) : Nobq.OutTwoCyclic X := by
  obtain ⟨⟨hrp, hf1, -⟩, hm⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm
  by_cases h3 : p = 3
  · subst h3
    have : CharP K ReeTag.G2.prime :=
      finite_field_prime_power_characteristic Nat.prime_three hf1 hK
    obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ := G2_three_exact_automorphism_normal_form hf1 K hK
    exact Nobq.OutTwoCyclic.of_mulEquiv e (outTwoCyclic_of_hom_cyclic Θ hker)
  · obtain ⟨-, Θ, -, -, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form hrp
      hp2 hf1 K hK .G2 (Or.inr ⟨rfl, h3⟩)
    have : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic hrp K hK).2
    exact Nobq.OutTwoCyclic.of_mulEquiv e (outTwoCyclic_of_hom_cyclic Θ hker)

theorem outTwoCyclic_trialityD4
    {X : Type} [Group X] {p f : ℕ}
    (hp2 : p ≠ 2) (h : ChevalleyExceptionalModel X .trialityD4 p f) : Nobq.OutTwoCyclic X := by
  obtain ⟨⟨hrp, hf1, -⟩, hm⟩ := h
  have hm' : TwistedChevalleyModel X .D4 (p ^ f) := hm
  obtain ⟨K, _, _, hcard, σ, hσ, ⟨e⟩⟩ := hm'
  obtain ⟨σ', hσ', -⟩ := finite_graph_field_parameter_fields .D4 hrp hf1 K hcard
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  subst hσσ'
  obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, hcyc, -, -, -, ⟨E⟩⟩ :=
    odd_triality_exact_automorphism_normal_form hrp hp2 hf1 K hcard σ' hσ'
  exact Nobq.OutTwoCyclic.of_mulEquiv (e.trans E) (outTwoCyclic_of_hom_cyclic Θ hker)

variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}

theorem TightDatum.not_fourGenerated_of_shape_cyclic4 (hD : TightDatum R S t)
    {N : Subgroup G} [N.Normal] {s : G} (hsR : s ∈ R) (hsN : s ∈ N) (hs4 : orderOf s = 4)
    (htN : t ∈ N) {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]
    (hF₁ : Odd (Nat.card F₁)) (hF₂ : Odd (Nat.card F₂)) (h4₁ : 4 ≤ Nat.card F₁)
    (h4₂ : 4 ≤ Nat.card F₂) (Sh : Shape ↥(Subgroup.centralizer ({⟨t, htN⟩} : Set N)) F₁ F₂) :
    ¬ TwoSubgroupsFourGenerated N := by
  set C := Subgroup.centralizer ({⟨t, htN⟩} : Set N)
  refine TightDatum.not_fourGenerated_of_sl2Pair_cyclic4 hD hsR hsN hs4 htN hF₁ hF₂ h4₁ h4₂
    (H₁ := Sh.I₁.map C.subtype) (H₂ := Sh.I₂.map C.subtype) (Subgroup.map_subtype_le _)
    (Subgroup.map_subtype_le _) ?_
    ((Subgroup.equivMapOfInjective _ _ C.subtype_injective).symm.trans Sh.e₁)
    ((Subgroup.equivMapOfInjective _ _ C.subtype_injective).symm.trans Sh.e₂)
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact congrArg Subtype.val (Sh.comm a ha b hb)

namespace Q5G2D4

theorem five_le {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h3 : p ^ f ≠ 3) :
    5 ≤ p ^ f := by
  obtain ⟨k, hk⟩ := (hp.odd_of_ne_two hp2).pow (n := f)
  have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
  have := hp.two_le
  omega

end Q5G2D4

theorem noQ8Datum_g2Ne3 : ∀ (F : Type) [Group F], SmallG2Ne3 F → NoQ8Datum F := by
  intro F _ hF
  obtain ⟨p, f, hp, hp2, hf, h3, hm⟩ := hF
  intro G _ _ N _ ⟨eN⟩ hC hgen R S t hD _
  have hce := Q5G2D4.chevalleyExceptionalModel_of_lieModel hm (by decide) (by decide)
    (by decide)
  obtain ⟨htN, s, hsR, hsN, hs4⟩ := TightDatum.exists_cyclic4_of_outTwoCyclic hD hC
    (Nobq.OutTwoCyclic.of_mulEquiv eN (outTwoCyclic_G2 hp2 hce))
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨eF⟩⟩ := hce
  have hmN : LieModel N .G2 0 p f :=
    Or.inr (Or.inl ⟨rfl, by decide, hadm, K, hKf, hKfin, hK, ⟨eN.trans eF⟩⟩)
  have ht : orderOf (⟨t, htN⟩ : N) = 2 := by rw [Subgroup.orderOf_mk]; exact hD.order
  obtain ⟨F', _, _, Sh, hcard, -⟩ := GH74.GLS.IVK.GHInv.exists_shape_G2 hp hp2 hmN _ ht
  obtain ⟨ho, h4⟩ := odd_four_le_of_card hp hp2 (Q5G2D4.five_le hp hp2 hf h3) le_rfl
    (hcard.trans (pow_one _).symm)
  exact TightDatum.not_fourGenerated_of_shape_cyclic4 hD hsR hsN hs4 htN ho ho h4 h4 Sh hgen

theorem smallSimpleLeaf_g2Ne3 : SmallSimpleLeaf SmallG2Ne3 :=
  smallSimpleLeaf_of_noQ8Datum noQ8Datum_g2Ne3

theorem noQ8Datum_d4Ne3 : ∀ (F : Type) [Group F], SmallD4Ne3 F → NoQ8Datum F := by
  intro F _ hF
  obtain ⟨p, f, hp, hp2, hf, h3, hm⟩ := hF
  intro G _ _ N _ ⟨eN⟩ hC hgen R S t hD _
  have hce := Q5G2D4.chevalleyExceptionalModel_of_lieModel hm (by decide) (by decide)
    (by decide)
  obtain ⟨htN, s, hsR, hsN, hs4⟩ := TightDatum.exists_cyclic4_of_outTwoCyclic hD hC
    (Nobq.OutTwoCyclic.of_mulEquiv eN (outTwoCyclic_trialityD4 hp2 hce))
  obtain ⟨hadm, K, hKf, hKfin, hK, σ, hσ, ⟨eF⟩⟩ := hce
  have hmN : LieModel N .trialityD4 0 p f :=
    Or.inr (Or.inl ⟨rfl, by decide, hadm, K, hKf, hKfin, hK, σ, hσ, ⟨eN.trans eF⟩⟩)
  have ht : orderOf (⟨t, htN⟩ : N) = 2 := by rw [Subgroup.orderOf_mk]; exact hD.order
  obtain ⟨F₁, F₂, _, _, _, _, Sh, hc₁, hc₂, -⟩ :=
    GH74.GLS.IVK.GHInv.exists_shape_D4 hp hp2 hmN _ ht
  have h5 := Q5G2D4.five_le hp hp2 hf h3
  obtain ⟨ho₁, h4₁⟩ := odd_four_le_of_card hp hp2 h5 (by norm_num) hc₁
  obtain ⟨ho₂, h4₂⟩ := odd_four_le_of_card hp hp2 h5 le_rfl (hc₂.trans (pow_one _).symm)
  exact TightDatum.not_fourGenerated_of_shape_cyclic4 hD hsR hsN hs4 htN ho₁ ho₂ h4₁ h4₂ Sh hgen

theorem smallSimpleLeaf_d4Ne3 : SmallSimpleLeaf SmallD4Ne3 :=
  smallSimpleLeaf_of_noQ8Datum noQ8Datum_d4Ne3

end CFSG.ClassicalInvolution.Q3.TA3
