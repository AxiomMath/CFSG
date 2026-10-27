module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294DeltaBase
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.E8
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicOuter
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExclusionsTwo
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.ReeG2Outer
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.ExcFG
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.TrialityD4
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterTwisted

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG CFSG.AGLEmbedding CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower
open CFSG.HardMathSupport.Timmesfeld.DefChar (lot_card_range_diag_outer_le_three)
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal Outer)
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

section


theorem DeltaTowerAt.of_sporadic (s : TauCeti.SporadicName) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) : DeltaTowerAt p (TauCeti.CFSGIndex.sporadic s).Group :=
  DeltaTowerAt.of_not_dvd_card_outer hp
    (CFSG.AGLEmbedding.not_dvd_card_outer_sporadic
      CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s p hp (by omega))

end

section


theorem DeltaTowerAt.of_adjointE {τ : Tag} {F : Type} [Field F] [Finite F]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    DeltaTowerAt p (adjointGroup τ F) := by
  obtain ⟨Φ, -, -, hkerΦ⟩ := exists_outer_hom_E (K := F) hτ
  have hdet : 0 < τ.cartan.det.natAbs ∧ τ.cartan.det.natAbs ≤ 3 := by
    rcases hτ with rfl | rfl | rfl
    · rw [det_cartan_E6]; decide
    · rw [det_cartan_E7]; decide
    · rw [det_cartan_E8]; decide
  have hcpos : 0 < Nat.card Φ.ker := Nat.pos_of_dvd_of_pos hkerΦ hdet.1
  have hcle : Nat.card Φ.ker ≤ 3 := (Nat.le_of_dvd hdet.1 hkerΦ).trans hdet.2
  obtain ⟨ℓ, f, hℓ, hf, hF⟩ : ∃ ℓ f : ℕ, ℓ.Prime ∧ 1 ≤ f ∧ Nat.card F = ℓ ^ f := by
    have : Fintype F := Fintype.ofFinite F
    have := Fact.mk (CharP.char_is_prime F (ringChar F))
    obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
    exact ⟨ringChar F, n, hp, n.pos, by rw [Nat.card_eq_fintype_card]; exact hn⟩
  have hcyc : IsCyclic (F ≃+* F) := CFSG.RankThree.PartOne.CTP.isCyclic_ringEquiv_of_card hℓ hf hF
  have hcomm : ∀ x y : RingAut F × Multiplicative (ZMod (exactE τ)), x * y = y * x := by
    intro x y
    refine Prod.ext ?_ (mul_comm _ _)
    exact (IsCyclic.commGroup (α := F ≃+* F)).mul_comm x.1 y.1
  exact DeltaTowerAt.of_outer_hom hcomm Φ hp (Nat.not_dvd_of_pos_of_lt hcpos (by omega))

end

section


theorem DeltaTowerAt.of_catE6 {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E6 q).Valid)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    DeltaTowerAt p (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group := by
  obtain ⟨F, _, _, ⟨e⟩⟩ := exists_mulEquiv_adjoint
    (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).e6 q hv
  exact DeltaTowerAt.of_mulEquiv e (DeltaTowerAt.of_adjointE (Or.inl rfl) hp hp5)

theorem DeltaTowerAt.of_catE7 {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E7 q).Valid)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    DeltaTowerAt p (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group := by
  obtain ⟨F, _, _, ⟨e⟩⟩ := exists_mulEquiv_adjoint
    (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).e7 q hv
  exact DeltaTowerAt.of_mulEquiv e (DeltaTowerAt.of_adjointE (Or.inr (Or.inl rfl)) hp hp5)

theorem DeltaTowerAt.of_catE8 {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E8 q).Valid)
    {p : ℕ} : DeltaTowerAt p (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group := by
  obtain ⟨F, _, _, ⟨e⟩⟩ := exists_mulEquiv_adjoint
    (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).e8 q hv
  exact DeltaTowerAt.of_mulEquiv e (DeltaTowerAt.of_outerComm (outerComm_adjoint_E8 F))

theorem DeltaTowerAt.of_catF4 {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.F4 q).Valid)
    {p : ℕ} : DeltaTowerAt p (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group := by
  obtain ⟨F, _, _, ⟨e⟩⟩ := exists_mulEquiv_adjoint
    (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).f4 q hv
  exact DeltaTowerAt.of_mulEquiv e (DeltaTowerAt.of_outerComm (outerComm_adjoint_F4 F))

theorem DeltaTowerAt.of_catG2 {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
    {p : ℕ} : DeltaTowerAt p (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_mulEquiv_adjoint_card
    (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 q hv
  have h3 : 3 ≤ Nat.card F := by
    rw [hF]
    exact (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  exact DeltaTowerAt.of_mulEquiv e (DeltaTowerAt.of_outerComm (outerComm_adjoint_G2 F h3))

theorem DeltaTowerAt.of_cat_trialityD4 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) {p : ℕ} :
    DeltaTowerAt p (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group := by
  obtain ⟨-, hm⟩ := CFSG.LieType.SeitzGeneration.chevalleyModel_cat_trialityD4 hv
  have hm' : TwistedChevalleyModel
      (CFSG.LieType.SeitzGeneration.Cat ⟨.trialityD4 q, hv⟩) .D4 (q.p ^ q.exponent) := hm
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 q.prime_p q.exponent_pos hm'
  exact DeltaTowerAt.of_mulEquiv e (DeltaTowerAt.of_outerComm
    (outerComm_graphFixedRootGroup_D4 q.prime_p q.exponent_pos K hK σ hσ))

end

section


theorem DeltaTowerAt.of_twistedE6RootGroup {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    DeltaTowerAt p (twistedE6RootGroup K σ) := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hΘker, -, -, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hinn : (twistedE6Inn K σ).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  have hcyc : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have hcomm : ∀ a b : RingAut K, a * b = b * a := fun a b =>
    (IsCyclic.commGroup (α := K ≃+* K)).mul_comm a b
  set D := Θ.ker with hD
  have hab : ∀ γ α : MulAut (twistedE6RootGroup K σ), (∃ k : ℕ, α ^ (p ^ k) = 1) →
      γ * α * γ⁻¹ * α⁻¹ ∈ D := by
    intro γ α _
    rw [hD, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hcomm (Θ γ) (Θ α)]
    group
  refine DeltaTowerAt.of_card_not_dvd hp D hab ?_
  set I := twistedE6Inn K σ with hI
  let ψ : D →* Outer (twistedE6RootGroup K σ) := (QuotientGroup.mk' I).comp D.subtype
  have hker : ψ.ker = I.subgroupOf D := by
    ext x
    simp [ψ, hI, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hψ3 := lot_card_range_diag_outer_le_three hK σ hσ
  have hrange : ψ.range ≤ ((QuotientGroup.mk' (twistedE6Inn K σ)).comp
      (compatDiagAutHom TwistTag.E6 K σ.toRingHom)).range := by
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    have hx' : x ∈ I ⊔ twistedE6Diag K σ := by rw [← hΘker]; exact hx
    obtain ⟨y, hy, z, ⟨u, rfl⟩, hyz⟩ := Subgroup.mem_sup_of_normal_left.1 hx'
    refine ⟨u, ?_⟩
    change QuotientGroup.mk' (twistedE6Inn K σ) (compatDiagAutHom TwistTag.E6 K σ.toRingHom u) =
      QuotientGroup.mk' I x
    have hy1 : QuotientGroup.mk' I y = 1 := (QuotientGroup.eq_one_iff y).2 hy
    rw [← hyz, map_mul, hy1, one_mul]
  have hfin : Finite ((QuotientGroup.mk' (twistedE6Inn K σ)).comp
      (compatDiagAutHom TwistTag.E6 K σ.toRingHom)).range := inferInstance
  haveI : Finite ψ.range := Finite.of_injective (Subgroup.inclusion hrange)
    (Subgroup.inclusion_injective hrange)
  have h1 : Nat.card (D ⧸ ψ.ker) = Nat.card ψ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
  rw [hker] at h1
  have h2 : Nat.card ψ.range ≤ 3 := (Subgroup.card_le_of_le hrange).trans hψ3
  have h3 : 0 < Nat.card ψ.range := Nat.card_pos
  change ¬ p ∣ Nat.card (D ⧸ I.subgroupOf D)
  rw [h1]
  exact Nat.not_dvd_of_pos_of_lt h3 (by omega)

end

section


theorem DeltaTowerAt.of_cat_twistedE6 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    DeltaTowerAt p (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let K := GaloisField q.p (2 * q.exponent)
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hKc : Nat.card K = (q.p ^ q.exponent) ^ TwistTag.E6.order := by
    change Nat.card (GaloisField q.p (2 * q.exponent)) = _
    rw [GaloisField.card _ _ (by have := q.exponent_pos; omega)]
    change _ = (q.p ^ q.exponent) ^ 2
    rw [← pow_mul, mul_comm]
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 q.prime_p hf K hKc
  have hK2 : Nat.card K = (q.p ^ q.exponent) ^ 2 := hKc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨eC⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p hf K hK2 σ hσ
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  obtain ⟨eB⟩ : Nonempty (DerivedCentralQuotient
      (twistedFixedGroup TwistTag.E6 K σ.toRingHom) ≃*
      TauCeti.ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) := by
    by_cases hq2 : q.p = 2
    · exact CFSG.TauCetiBridge.Even.twistedBridgeEven_twistedE6 q hv hq2 K
        (by rw [hqc]; exact hK2) σ.toRingHom (fun x => by rw [hqc]; exact hσ x)
    · exact CFSG.TauCetiBridge.Twisted.twistedBridge_twistedE6 q hv hq2 K
        (by rw [hqc]; exact hK2) σ.toRingHom (fun x => by rw [hqc]; exact hσ x)
  exact DeltaTowerAt.of_mulEquiv (eB.symm.trans eC)
    (DeltaTowerAt.of_twistedE6RootGroup q.prime_p hf hK2 σ hσ hp hp5)

end

section


theorem DeltaTowerAt.of_cat_suzuki {m : ℕ} (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) {p : ℕ} :
    DeltaTowerAt p (TauCeti.CFSGIndex.lie ⟨.suzuki m, hv⟩).Group := by
  have hS := CFSG.HardMathSupport.Cooperstein.Coordinator.suzukiModel_of_lie hv (MulEquiv.refl _)
  exact DeltaTowerAt.of_outerComm fun γ α =>
    CFSG.RankThree.PartTwo.KFacts.KP7.commutatorElement_mem_inner hS γ α

end

section


theorem DeltaTowerAt.of_cat_reeG2 {m : ℕ} (hv : (TauCeti.LieTypeIndex.reeG2 m).Valid) {p : ℕ} :
    DeltaTowerAt p (TauCeti.CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group := by
  have hiso : CFSG.RankThree.PartOne.Census3.IsoLie
      (TauCeti.CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group (.reeG2 m) := ⟨hv, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨X, _, _, _, hm1, hXcard, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.exists_reeG2_model hiso
  have hcyc := CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.isCyclic_outer_reeG2
    hm1 hXcard
  exact DeltaTowerAt.of_outerComm
    (OuterComm.of_mulEquiv e (outerComm_of_isCyclic_outer hcyc))

end

section


theorem DeltaTowerAt.of_cat_reeF4 {m : ℕ} (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid) {p : ℕ} :
    DeltaTowerAt p (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group := by
  have hm := CFSG.LieType.SeitzGeneration.reeTitsModel_cat_reeF4 hv
  have hX := CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier
    (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group 2 (2 * m + 1) hm
  obtain ⟨hadm, a, hfa, K, _, _, hK, ⟨e⟩⟩ := hm
  have hf3 : 3 ≤ 2 * m + 1 := hadm.2.2.2.2.2
  have ha : 1 ≤ a := by omega
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := hchar
  obtain ⟨E⟩ := hX.2.2.2.2.2 a K hfa hK ⟨e⟩
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  obtain ⟨-, -, -, hcyc, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK'
  exact DeltaTowerAt.of_outerComm
    (OuterComm.of_mulEquiv E (outerComm_of_isCyclic_outer hcyc))

end

section


theorem DeltaTowerAt.of_cat_tits (hv : TauCeti.LieTypeIndex.tits.Valid) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : DeltaTowerAt p (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group := by
  have hR : CFSG.Blueprint.ReeTitsModel (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group .Tits 2 1 :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.reeTitsModel_tits_of_lie hv (MulEquiv.refl _)
  have h2 : IsPGroup 2 (Outer (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group) :=
    (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier _ 2 1 hR).1
  exact DeltaTowerAt.of_isPGroup_outer Nat.prime_two hp (Ne.symm hp2) h2

end

end CFSG.LocalAnalysis.RankFourTheoremC
