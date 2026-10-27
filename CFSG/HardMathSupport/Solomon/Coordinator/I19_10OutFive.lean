module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10Red
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_6OutThree
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.DefCharExceptional
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.DefCharOrth
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Setup

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open (IsElemAbelian)
open CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)

set_option linter.unusedSectionVars false


open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag StatedProj StatedOmega
  StatedQuadOdd StatedQuadPlus StatedQuadMinus)
open Matrix Subgroup QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (orthogonal_geometry_plus_point_family_orbit)
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner
open CFSG.RankThree.PartOne.OutStructure (OutPChain OutPNice instFiniteMulAut')
open scoped Pointwise commutatorElement

section Orth

theorem i1910_meetsInnerTwo_POmegaPlus_five {T : Type} [Group T] [Finite T] {n ℓ f : ℕ}
    (hm : StatedClassicalModel T .POmegaPlus n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp5 : 5 ≤ p) : MeetsInnerTwo p T := by
  have h0 := hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  have hn : 4 ≤ n := hm.1.2.2
  have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaPlus
    (.inr (.inl rfl)) n ℓ f hm K hK (quadPlus n K) (coe_quadPlus n K) e
  have hEA := ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaPlus
    (.inr (.inl rfl)) n ℓ f hm) K hK e).1
  have horbit := orthogonal_geometry_plus_point_family_orbit hm hK e
  have hidx : (matrixProjectiveImage (coordinateQuadPlus n K)).index ≤ 3 := by
    rcases (show n = 4 ∨ 5 ≤ n by omega) with h4 | h5
    · have hst : (projectivePointFamilyAut (coordinateQuadPlus n K)).index =
          (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))
            (projectivePointFamily (coordinateQuadPlus n K))).ncard :=
        MulAction.index_stabilizer _ _
      rw [← hEA, hst]
      exact (horbit.2.2.2.2.2 h4).2
    · rw [← hEA, horbit.2.2.2.2.1 h5, Subgroup.index_top]
      norm_num
  refine MeetsInnerTwo.of_mulEquiv (coordinatePlusWitnessEquiv K e) fun X hX hcard => ?_
  exact i196_exists_inner_of_matrixProjectiveDerived_le (m := 3) _
    (coordinate_model_intrinsic_plus hm K hK e).1
    (exists_two_pow_card_abelianization (plusIndexEquiv n) (quadPlus n K) hab) hidx hp hp2 X hX.2
    (by rw [hcard]; nlinarith)

end Orth

section Families


@[expose] def i1910_OuterTwoFiveFam (k : DefCharFamily) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, k.Matches idx.1 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ p : ℕ, p.Prime → p = 5 → idx.1.characteristic = p →
        ∀ D : Subgroup (MulAut S), IsElemAbelian p D → Nat.card D = p ^ 2 →
          ∃ x ∈ D ⊓ innerAut S, x ≠ 1

theorem i1910_outerTwoFiveFamA : i1910_OuterTwoFiveFam .A := by
  intro S _ _ hS hnab idx hk hidx p hp hp5 hch D hD hcard
  obtain ⟨r, q, hrq⟩ := hk
  have hv := idx.2
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff, hrq] at hv
  have hr1 : 1 ≤ r := hv.1.1
  have hlt : p < Nat.card D := by rw [hcard]; exact lt_pow_two_of_prime hp
  have hp2 : p ≠ 2 := by omega
  by_cases hr : r = 1
  · exact outerRank_A_one idx ⟨q, hrq.trans (by rw [hr])⟩ hidx hp hp2 hch D hD hlt
  · exact outerRank_A_of_two_le idx ⟨r, q, hrq, by omega⟩ hidx hp hp2 hch D hD hlt

theorem i1910_outerTwoFiveFamC : i1910_OuterTwoFiveFam .C := by
  intro S _ _ hS hnab idx hk hidx p hp hp5 hch D hD hcard
  exact outerRank_C idx hk hidx hp hch D hD (by rw [hcard]; exact lt_pow_two_of_prime hp)

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag in
theorem i1910_outerTwoFiveFamTwistedA : i1910_OuterTwoFiveFam .twistedA := by
  intro S _ _ hS' hnab idx hidx hS p hp hp5 hch D hD hcard
  have hlt : p < Nat.card D := by rw [hcard]; exact lt_pow_two_of_prime hp
  obtain ⟨r, q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e0
  obtain ⟨⟨hℓ, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun ⟨h1, h2⟩ => hq (by rw [h1, h2])
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := r + 1) (K := K))
  let e : S ≃* primeFormP h ((1 : GL (Fin (r + 1)) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  have hpq' : p = q.p := hpq
  subst hpq'
  have hndvd : ¬ q.p ∣ q.p ^ q.exponent + 1 := by
    intro hd
    have h1 : q.p ∣ q.p ^ q.exponent := dvd_pow_self _ q.exponent_pos.ne'
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h1).1 hd))
  exact exists_inner_transport_lt e D (fun a ha => hD.2 a ha) hlt fun D' hexp hc =>
    exists_inner_of_elemAbelian_primeFormP h (n := r + 1) (by omega) hq' hp hndvd D' hexp hc

open TauCeti in
theorem i1910_outerTwoFiveFamB : i1910_OuterTwoFiveFam .B := by
  intro S _ _ _ _ idx hidx hS p hp hp5 hch D hD hcard
  obtain ⟨r, q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr hch
  subst hr
  obtain ⟨e⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  have hp2 : p ≠ 2 := by omega
  have hqp2 : q.p ≠ 2 := hpq ▸ hp2
  have hr2 : 2 ≤ r := ((LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1).1
  rcases Nat.eq_or_lt_of_le hr2 with h2 | h3
  · subst h2
    exact meetsInnerTwo_PSp_two hqp2
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e) hp hp2 D hD hcard
  · exact i196_meetsInnerTwo_POmegaOdd_one (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q
      hv hqp2 h3 e) hp hp2 D hD hcard

open TauCeti in
theorem i1910_outerTwoFiveFamD : i1910_OuterTwoFiveFam .D := by
  intro S _ _ _ _ idx hidx hS p hp hp5 hch D hD hcard
  obtain ⟨r, q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e⟩ := hS
  exact i1910_meetsInnerTwo_POmegaPlus_five
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e) hp (by omega) (by omega)
    D hD hcard

open TauCeti in
theorem i1910_outerTwoFiveFamTwistedD : i1910_OuterTwoFiveFam .twistedD := by
  intro S _ _ _ _ idx hidx hS p hp hp5 hch D hD hcard
  obtain ⟨r, q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e⟩ := hS
  exact i196_meetsInnerTwo_POmegaMinus_one
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e) hp (by omega) D hD hcard

section E

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Open

theorem i1910_outerTwoFiveFamE6 : i1910_OuterTwoFiveFam .E6 := by
  intro S _ _ _ _ idx hidx hS p hp hp5 hch D hD hcard
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  exact exists_inner_of_bridge_E_lt (Or.inl rfl) CFSG.TauCetiBridge.chevalleyBridges.e6 q hv S e0
    hp (by omega) hpq D hD (by rw [hcard]; exact lt_pow_two_of_prime hp)

theorem i1910_outerTwoFiveFamE7 : i1910_OuterTwoFiveFam .E7 := by
  intro S _ _ _ _ idx hidx hS p hp hp5 hch D hD hcard
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  exact exists_inner_of_bridge_E_lt (Or.inr (Or.inl rfl))
    CFSG.TauCetiBridge.chevalleyBridges.e7 q hv S e0 hp (by omega) hpq D hD
    (by rw [hcard]; exact lt_pow_two_of_prime hp)

theorem i1910_outerTwoFiveFamE8 : i1910_OuterTwoFiveFam .E8 := by
  intro S _ _ _ _ idx hidx hS p hp hp5 hch D hD hcard
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  exact exists_inner_of_bridge_E_lt (Or.inr (Or.inr rfl))
    CFSG.TauCetiBridge.chevalleyBridges.e8 q hv S e0 hp (by omega) hpq D hD
    (by rw [hcard]; exact lt_pow_two_of_prime hp)

end E

section F4G2

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

theorem i1910_outerTwoFiveFamF4 : i1910_OuterTwoFiveFam .F4 := by
  intro S _ _ _ _ idx hidx hS p hp hp5 hch D hD hcard
  have hp2 : p ≠ 2 := by omega
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  subst hpq
  set K := GaloisField q.p q.exponent
  have hK : Nat.card K = q.p ^ q.exponent := GaloisField.card _ _ q.exponent_pos.ne'
  have hK' : Nat.card K = q.card := by rw [hK, TauCeti.PrimePower.card_def]
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).f4 q hv K hK'
  let e : S ≃* adjointGroup .F4 K :=
    e0.trans (b.symm.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot))
  obtain ⟨-, Θ, -, -, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2
    q.exponent_pos K hK .F4 (Or.inl rfl)
  have := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  exact exists_inner_of_cyclic_quotient e Θ hker hp D hD.2
    (by rw [hcard]; exact lt_pow_two_of_prime hp)

theorem i1910_outerTwoFiveFamG2 : i1910_OuterTwoFiveFam .G2 := by
  intro S _ _ _ _ idx hidx hS p hp hp5 hch D hD hcard
  have hp2 : p ≠ 2 := by omega
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  subst hpq
  set K := GaloisField q.p q.exponent
  have hK : Nat.card K = q.p ^ q.exponent := GaloisField.card _ _ q.exponent_pos.ne'
  have hK' : Nat.card K = q.card := by rw [hK, TauCeti.PrimePower.card_def]
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 q hv K hK'
  let e : S ≃* adjointGroup .G2 K :=
    e0.trans (b.symm.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot))
  have hlt : q.p < Nat.card D := by rw [hcard]; exact lt_pow_two_of_prime hp
  have h3 : q.p ≠ 3 := by omega
  obtain ⟨-, Θ, -, -, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2
    q.exponent_pos K hK .G2 (Or.inr ⟨rfl, h3⟩)
  have := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  exact exists_inner_of_cyclic_quotient e Θ hker hp D hD.2 hlt

end F4G2

section Twisted

open CFSG.Open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem i1910_outerTwoFiveFamTrialityD4 : i1910_OuterTwoFiveFam .trialityD4 := by
  intro S _ _ _ _ idx hidx hS p hp hp5 hch D hD hcard
  have hp2 : p ≠ 2 := by omega
  have hlt : p < Nat.card D := by rw [hcard]; exact lt_pow_two_of_prime hp
  obtain ⟨q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let K := GaloisField q.p (3 * q.exponent)
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hKc : Nat.card K = (q.p ^ q.exponent) ^ TwistTag.D4.order := by
    change Nat.card (GaloisField q.p (3 * q.exponent)) = _
    rw [GaloisField.card _ _ (by have := q.exponent_pos; omega)]
    change _ = (q.p ^ q.exponent) ^ 3
    rw [← pow_mul, mul_comm]
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.D4 q.prime_p hf K hKc
  subst hpq
  have hK3 : Nat.card K = (q.p ^ q.exponent) ^ 3 := hKc
  obtain ⟨-, -, ⟨Θ, -, -, hΘker, -⟩, hcyc, -, -, -, ⟨eC⟩⟩ :=
    odd_triality_exact_automorphism_normal_form q.prime_p hp2 hf K hK3 σ hσ
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hv K
    (by rw [hqc]; exact hK3) σ.toRingHom (fun x => by rw [hqc]; exact hσ x)
  have e : S ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    e0.trans (eB.symm.trans eC)
  exact exists_inner_transport_lt e D (fun a ha => hD.2 a ha) hlt
    (fun D' hexp hc => exists_inner_of_cyclic_hom Θ hp
      (fun x hx _ => by
        have : x ∈ Θ.ker := hx
        rw [hΘker] at this
        exact this)
      D' hexp hc)

theorem i1910_outerTwoFiveFamTwistedE6 : i1910_OuterTwoFiveFam .twistedE6 := by
  intro S _ _ _ _ idx hidx hS p hp hp5 hch D hD hcard
  have hp2 : p ≠ 2 := by omega
  have hlt : p < Nat.card D := by rw [hcard]; exact lt_pow_two_of_prime hp
  obtain ⟨q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let K := GaloisField q.p (2 * q.exponent)
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hKc : Nat.card K = (q.p ^ q.exponent) ^ TwistTag.E6.order := by
    change Nat.card (GaloisField q.p (2 * q.exponent)) = _
    rw [GaloisField.card _ _ (by have := q.exponent_pos; omega)]
    change _ = (q.p ^ q.exponent) ^ 2
    rw [← pow_mul, mul_comm]
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 q.prime_p hf K hKc
  subst hpq
  have hK2 : Nat.card K = (q.p ^ q.exponent) ^ 2 := hKc
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hΘker, -, -, -⟩, -, -, -, ⟨eC⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p hf K hK2 σ hσ
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv K
    (by rw [hqc]; exact hK2) σ.toRingHom (fun x => by rw [hqc]; exact hσ x)
  have e : S ≃* graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    e0.trans (eB.symm.trans eC)
  have hcyc : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have hpK : ¬ q.p ∣ Nat.card K - 1 := by
    intro h
    have h1 : q.p ∣ Nat.card K := by
      rw [hK2]; exact dvd_pow (dvd_pow_self _ q.exponent_pos.ne') (by norm_num)
    have hpos : 1 ≤ Nat.card K := Nat.card_pos
    have h2 := (Nat.dvd_add_right h).1 (by rwa [Nat.sub_add_cancel hpos])
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  exact exists_inner_transport_lt e D (fun a ha => hD.2 a ha) hlt
    (fun D' hexp hc => exists_inner_of_cyclic_hom Θ hp
      (fun x hx hxp => by
        have : x ∈ Θ.ker := hx
        rw [hΘker] at this
        exact mem_inner_of_mem_inn_sup_diag_E6 σ hp hpK this hxp)
      D' hexp hc)

end Twisted

section Ree

open CFSG.Open CFSG.Blueprint
open CFSG.LieType.Ree (ReeTag)
open CFSG.ComponentClassification.LiteratureLocal.SmallRee (frobeniusΓ
  exists_eq_conj_mul_frobeniusΓ_pow)

theorem i1910_outerTwoFiveFamReeG2 : i1910_OuterTwoFiveFam .reeG2 := by
  intro S _ _ _ _ idx hidx hS p hp hp5 hch D hD hcard
  have hlt : p < Nat.card D := by rw [hcard]; exact lt_pow_two_of_prime hp
  obtain ⟨d, hv⟩ := idx
  obtain ⟨m, rfl⟩ := hidx
  obtain ⟨e0⟩ := hS
  have hm1 : 1 ≤ m :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField 3 (2 * m + 1)) = 3 ^ (2 * m + 1) :=
    GaloisField.card 3 (2 * m + 1) (by omega)
  have : CharP (GaloisField 3 (2 * m + 1)) ReeTag.G2.prime :=
    (inferInstance : CharP (GaloisField 3 (2 * m + 1)) 3)
  obtain ⟨b⟩ := CFSG.TauCetiBridge.reeG2Bridge m hv (GaloisField 3 (2 * m + 1)) hK
  have e1 : DerivedCentralQuotient (reeFixedGroup .G2 (GaloisField 3 (2 * m + 1)) reeG2Perm
      fun i => if i ∈ reeG2Long then 3 ^ m else 3 ^ (m + 1)) ≃*
        DerivedCentralQuotient (ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m) := by
    rw [ReeTag.reeGamma_eq_reeFixedGroup]
    exact MulEquiv.refl _
  obtain ⟨E⟩ := ReeTag.nonempty_derivedCentralQuotient_mulEquiv_reeGamma_G2
    (K := GaloisField 3 (2 * m + 1)) hm1 hK
  let e : S ≃* ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m :=
    ((e0.trans b.symm).trans e1).trans E
  exact exists_inner_transport_lt e D (fun a ha => hD.2 a ha) hlt
    (fun D' hexp hc => exists_inner_of_elemAbelian_of_outerCyclic
      (frobeniusΓ : MulAut (ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m))
      (exists_eq_conj_mul_frobeniusΓ_pow hm1 hK) hp D' hexp hc)

end Ree

theorem defCharOuterRankTwoFive_proved : DefCharOuterRankTwoFive := by
  intro S _ _ hS hnab idx hidx hch D hD hcard
  have hne : idx.1.characteristic ≠ 2 := by rw [hch]; norm_num
  obtain ⟨k, hk⟩ := exists_family_of_characteristic_ne_two idx.1 hne
  have key : ∀ {k : DefCharFamily}, i1910_OuterTwoFiveFam k → k.Matches idx.1 →
      ∃ x ∈ D ⊓ innerAut S, x ≠ 1 := fun h hk =>
    h S hS hnab idx hk hidx 5 Nat.prime_five rfl hch D hD hcard
  cases k with
  | A => exact key i1910_outerTwoFiveFamA hk
  | twistedA => exact key i1910_outerTwoFiveFamTwistedA hk
  | B => exact key i1910_outerTwoFiveFamB hk
  | C => exact key i1910_outerTwoFiveFamC hk
  | D => exact key i1910_outerTwoFiveFamD hk
  | twistedD => exact key i1910_outerTwoFiveFamTwistedD hk
  | E6 => exact key i1910_outerTwoFiveFamE6 hk
  | E7 => exact key i1910_outerTwoFiveFamE7 hk
  | E8 => exact key i1910_outerTwoFiveFamE8 hk
  | F4 => exact key i1910_outerTwoFiveFamF4 hk
  | G2 => exact key i1910_outerTwoFiveFamG2 hk
  | twistedE6 => exact key i1910_outerTwoFiveFamTwistedE6 hk
  | trialityD4 => exact key i1910_outerTwoFiveFamTrialityD4 hk
  | reeG2 => exact key i1910_outerTwoFiveFamReeG2 hk

end Families

end CFSG.HardMathSupport.Solomon.Coordinator
