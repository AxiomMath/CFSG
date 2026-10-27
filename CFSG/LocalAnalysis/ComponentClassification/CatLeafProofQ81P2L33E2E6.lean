module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E2E6Graph
public import CFSG.LieType.Chevalley.CLSEvenE6AllInvolutionFourGroup
public import CFSG.LocalAnalysis.ComponentClassification.SteinbergBNEvenInnerInvolutionOddCore

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L33.E2

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.Chevalley.E6SecondGraphFixed
open CFSG.LieType.Chevalley.EvenE6AllInvolution (mem_inner_of_conj_mul_rootDiagAut)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem E6_not_isPGroup
    {k : Type} [Field k] [Finite k] {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hF4 : InvolutionCentralizerNotTwoGroup .F4)
    (hopen : ∀ c : adjointGroup TwistTag.E6.tag k, orderOf c = 2 →
      ¬ IsPGroup 2 ↥(centralizer ({c} : Set (adjointGroup TwistTag.E6.tag k))))
    (β : MulAut (adjointGroup TwistTag.E6.tag k)) (hβ : orderOf β = 2) :
    ¬ IsPGroup 2 (↥(fixedPoints β) ⧸ pPrimeCore 2 ↥(fixedPoints β)) := by
  have : CharP k 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hk
  have := finite_modGL (τ := TwistTag.E6.tag) (K := k)
  have hβ2 : β ^ 2 = 1 := by rw [← hβ, pow_orderOf_eq_one]
  by_cases hin : β ∈ inner (adjointGroup TwistTag.E6.tag k)
  · obtain ⟨c, rfl⟩ := hin
    have hc : orderOf c = 2 := by
      rw [← orderOf_injective _
        (mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot) c]
      exact hβ
    exact inner_not_isPGroup (MulEquiv.refl _)
      (fun c hc2 hc1 => isCharacteristicP_centralizer (RootWeightDatum.ordinary Tag.E6) hc2 hc1)
      hopen c hc
  obtain ⟨-, -, hexist⟩ :=
    ordinary_E_exact_automorphism_normal_form TwistTag.E6.tag (Or.inl rfl) k
  obtain ⟨g, a, σ, ε, hexpr⟩ := hexist β
  by_cases hσ : σ = 1
  · subst hσ
    have hid : ∀ h : ModGL TwistTag.E6.tag k,
        Units.map (entrywiseHom (1 : k ≃+* k).toRingHom) h = h := fun h =>
      Units.ext (entrywise_id _)
    obtain ⟨ε, hε⟩ := ε
    have hε' : ε = 0 ∨ ε = 1 := by
      change ε < 2 at hε
      omega
    rcases hε' with rfl | rfl
    ·
      exfalso
      refine hin (mem_inner_of_conj_mul_rootDiagAut hk hf g a ?_ hβ2)
      refine MulEquiv.ext fun h => Subtype.ext ?_
      have e := hexpr h
      have hQ0 : exactQ TwistTag.E6.tag k ((⟨0, hε⟩ : Fin (exactE TwistTag.E6.tag)) : ℕ) = 1 :=
        pow_zero _
      rw [hQ0, hid, mul_one, inv_one, mul_one] at e
      rw [e, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_rootDiagAut, Subgroup.coe_inv]
      simp only [mul_assoc]
    ·
      have hQ1 : exactQ TwistTag.E6.tag k ((⟨1, hε⟩ : Fin (exactE TwistTag.E6.tag)) : ℕ) =
          diagramMap TwistTag.E6 k := pow_one _
      set M := GaloisField 2 (2 * f)
      have hM : Nat.card M = (2 ^ f) ^ 2 := by
        rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
      obtain ⟨ι⟩ := E6GraphFullCoset.nonempty_ringHom_of_card hf hk hM
      let _ : Algebra k M := ι.toAlgebra
      have hσM : ∀ c : M, iterateFrobenius M 2 f c = c ^ 2 ^ f := fun c =>
        iterateFrobenius_def (p := 2) f c
      obtain ⟨ht, η, hη, hclass, -⟩ :=
        (even_E6_graph_full_inner_diagonal_coset_exhaustion f hf).1 k hk
      obtain ⟨⟨hcan, -, -⟩, -⟩ :=
        even_E6_twisted_E6_canonical_graph_fixed_subgroup f hf k M hk hM _ hσM
      obtain ⟨-, -, -, -, ⟨e, -, -, hsec⟩, -⟩ :=
        even_E6_twisted_E6_second_graph_fixed_subgroup f hf k M hk hM _ hσM
      have hgraph : E6GraphFullCoset.IsOrdinaryDiagGraph k β := ⟨g, a, g.2, fun h => by
        have e := hexpr h
        rw [hQ1, hid] at e
        refine e.trans ?_
        group⟩
      exact graph_E6_not_isPGroup hf hk hF4 hcan e hsec hη
        ((hclass β hgraph hβ2).imp id fun ⟨φ, hφ⟩ => ⟨ht, φ, hφ⟩)
  ·
    obtain ⟨-, -, -, -, hsq, hfacts⟩ :=
      ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) k
    have hσ2 : σ ^ 2 = 1 := hsq β g a σ ε hexpr hβ2
    obtain ⟨hfe, hσc, -⟩ := hfacts 2 f Nat.prime_two hf hk σ hσ2 hσ
    obtain ⟨e, rfl⟩ : ∃ e, f = 2 * e := ⟨f / 2, (Nat.two_mul_div_two_of_even hfe).symm⟩
    have he : 1 ≤ e := by omega
    have hσe : ∀ c, σ c = c ^ 2 ^ e := fun c => by
      rw [hσc, Nat.mul_div_cancel_left e two_pos]
    have hββ : β * β = 1 := by rw [← sq]; exact hβ2
    obtain ⟨hD0, hD1⟩ :=
      even_exceptional_quadratic_field_graph_field_involution_descent he k hk σ.toRingHom hσe
    obtain ⟨hJ0, hJ1⟩ := even_E6_canonical_field_graph_field_derived_fixed_subgroups he k hk σ hσe
    obtain ⟨ε, hε⟩ := ε
    have hε' : ε = 0 ∨ ε = 1 := by
      change ε < 2 at hε
      omega
    rcases hε' with rfl | rfl
    ·
      have hQ0 : exactQ TwistTag.E6.tag k ((⟨0, hε⟩ : Fin (exactE TwistTag.E6.tag)) : ℕ) = 1 :=
        pow_zero _
      obtain ⟨β', hβ', hβα⟩ := hD0 TwistTag.E6.tag
      obtain ⟨ψ, -, hψ, -⟩ := (hβα g a).2 β (fun u => by
        have h := hexpr u
        rw [hQ0, mul_one, inv_one, mul_one] at h
        exact h) hββ
      obtain ⟨-, hJC, hder, -⟩ := hJ0
      have hβδ : diagramConjAut TwistTag.E6 k ^ 0 * entrywiseAdjointAut TwistTag.E6.tag σ = β' :=
        MulEquiv.ext fun u => Subtype.ext ((coe_entrywiseAdjointAut _ σ u).trans (hβ' u).symm)
      rw [← hβδ] at hψ
      have hk' := ExcSelector.card_fixSubfield_of_pow he hk hσe
      have : Finite (fixSubfield σ) := Subtype.finite
      refine not_isPGroup_of_derived hψ hJC hder (fixedFieldImageEquiv σ).symm
        (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6
          (fixSubfield σ)).1.commutator_eq_top ?_
      have h1 := card_sq_dvd_card_adjointGroup (K := fixSubfield σ) (τ := Tag.E6) (by decide)
      rw [hk'] at h1
      exact (dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)).trans h1
    ·
      have hQ1 : exactQ TwistTag.E6.tag k ((⟨1, hε⟩ : Fin (exactE TwistTag.E6.tag)) : ℕ) =
          diagramMap TwistTag.E6 k := pow_one _
      obtain ⟨β', hβ', hβα⟩ := hD1
      obtain ⟨ψ, -, hψ, -⟩ := (hβα g a).2 β (fun u => by
        have h := hexpr u
        rw [hQ1] at h
        exact h) hββ
      obtain ⟨-, hJC, hder, hfin, hsimp, -⟩ := hJ1
      have hβγδ : diagramConjAut TwistTag.E6 k ^ 1 * entrywiseAdjointAut TwistTag.E6.tag σ = β' :=
        MulEquiv.ext fun u => Subtype.ext (((coe_diagramConjAut TwistTag.E6 k
          (entrywiseAdjointAut TwistTag.E6.tag σ u)).trans
            (by rw [coe_entrywiseAdjointAut])).trans (hβ' u).symm)
      rw [← hβγδ] at hψ
      have hk' : Nat.card k = (2 ^ e) ^ 2 := by rw [hk, ← pow_mul, mul_comm]
      have h4 : 4 ∣ Nat.card (graphFixedRootGroup TwistTag.E6 k σ.toRingHom) := by
        rw [Timmesfeld.ExceptionalOrders.card_graphFixedRootGroup_E6_two he hk' σ.toRingHom hσe]
        exact four_dvd_ordTwistedE6 he
      exact not_isPGroup_of_derived hψ hJC hder (MulEquiv.refl _)
        (commutator_eq_top_of_simple_of_four_dvd hsimp h4) ((by norm_num : (2 : ℕ) ∣ 4).trans h4)

theorem twistedE6_not_isPGroup
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) (hF4 : InvolutionCentralizerNotTwoGroup .F4)
    (hopen : ∀ c : graphFixedRootGroup TwistTag.E6 K σ.toRingHom, orderOf c = 2 →
      ¬ IsPGroup 2 ↥(centralizer ({c} : Set (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))))
    (β : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) (hβ : orderOf β = 2) :
    ¬ IsPGroup 2 (↥(fixedPoints β) ⧸ pPrimeCore 2 ↥(fixedPoints β)) := by
  have hK' : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK'
  have := finite_modGL (τ := TwistTag.E6.tag) (K := K)
  have hσ2 : σ ^ TwistTag.E6.order = 1 := pow_eq_one_of_apply_eq_pow σ hK hσ
  have hβ2 : β ^ 2 = 1 := by rw [← hβ, pow_orderOf_eq_one]
  by_cases hin : β ∈ inner (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
  · obtain ⟨c, rfl⟩ := hin
    have hZ := exceptional_fixed_center_trivial TwistTag.E6 K σ
    have hc : orderOf c = 2 := by
      rw [← orderOf_injective _ (mulAut_conj_injective_of_center_eq_bot hZ) c]
      exact hβ
    exact inner_not_isPGroup (MulEquiv.refl _)
      (fun c hc2 hc1 => isCharacteristicP_centralizer (RootWeightDatum.fixed TwistTag.E6 σ hσ2)
        hc2 hc1) hopen c hc
  set k := GaloisField 2 f
  have hk : Nat.card k = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨ι⟩ := E6GraphFullCoset.nonempty_ringHom_of_card hf hk hK
  let _ : Algebra k K := ι.toAlgebra
  obtain ⟨ht, η, hη, -, -, hclass, -⟩ :=
    (even_E6_graph_full_inner_diagonal_coset_exhaustion f hf).2 K hK σ.toRingHom hσ
  obtain ⟨-, ⟨hcan, -, -⟩⟩ :=
    even_E6_twisted_E6_canonical_graph_fixed_subgroup f hf k K hk hK σ.toRingHom hσ
  obtain ⟨-, -, -, -, -, ⟨e, -, -, hsec⟩⟩ :=
    even_E6_twisted_E6_second_graph_fixed_subgroup f hf k K hk hK σ.toRingHom hσ
  have hout : ∀ c, β ≠ MulAut.conj c := fun c h => hin ⟨c, h.symm⟩
  exact graph_E6_not_isPGroup hf hk hF4 hcan e hsec hη
    ((hclass β hβ2 hout).imp id fun ⟨φ, hφ⟩ => ⟨ht, φ, hφ⟩)

theorem E6_model_not_isPGroup
    {Y : Type} [Group Y] [Finite Y] {t : StatedLieTag} {f : ℕ}
    (ht : t = .E6 ∨ t = .twistedE6) (hopen : InvolutionCentralizerNotTwoGroup t)
    (hF4 : InvolutionCentralizerNotTwoGroup .F4)
    (hY : ChevalleyExceptionalModel Y t 2 f) (hs : IsSimpleGroup Y)
    (a : MulAut Y) (ha : orderOf a = 2) :
    ¬ IsPGroup 2 (↥(fixedPoints a) ⧸ pPrimeCore 2 ↥(fixedPoints a)) := by
  have hopenY := hopen Y f hY hs
  obtain ⟨⟨-, hf, -⟩, hm⟩ := hY
  rcases ht with rfl | rfl
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hm
    refine Ree.not_isPGroup_of_mulEquiv e (E6_not_isPGroup hf hK hF4 ?_) a ha
    intro c hc hP
    exact hopenY (e.symm c) ((MulEquiv.orderOf_eq e.symm c).trans hc)
      (hP.of_equiv (centralizerEquiv e.symm c))
  · obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card .E6 Nat.prime_two hf hm
    refine Ree.not_isPGroup_of_mulEquiv e (twistedE6_not_isPGroup hf hK σ hσ hF4 ?_) a ha
    intro c hc hP
    exact hopenY (e.symm c) ((MulEquiv.orderOf_eq e.symm c).trans hc)
      (hP.of_equiv (centralizerEquiv e.symm c))

theorem twoNilpFor_E6
    (hE6 : InvolutionCentralizerNotTwoGroup .E6)
    (hTE6 : InvolutionCentralizerNotTwoGroup .twistedE6)
    (hF4 : InvolutionCentralizerNotTwoGroup .F4) :
    TwoNilpFor (fun Y _ => ∃ t f, (t = .E6 ∨ t = .twistedE6) ∧
      ChevalleyExceptionalModel Y t 2 f) := by
  intro Y _ _ hY hs _ a ha hP
  obtain ⟨t, f, ht, hm⟩ := hY
  have hopen : InvolutionCentralizerNotTwoGroup t := by
    rcases ht with rfl | rfl
    · exact hE6
    · exact hTE6
  exact absurd hP (E6_model_not_isPGroup ht hopen hF4 hm hs a ha)

end CFSG.ComponentClassification.HarrisLit.L33.E2
