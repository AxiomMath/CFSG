module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LieType.SeitzGeneration.ExcPlaneModel
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.Yardstones.Md42047359a2a.Definitions
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof

theorem not_pow_four_dvd_360 {p : ℕ} (hp : p.Prime) : ¬ p ^ 4 ∣ 360 := by
  intro h
  have hle : p ^ 4 ≤ 360 := Nat.le_of_dvd (by norm_num) h
  have hp4 : p ≤ 4 := by
    by_contra hlt
    push Not at hlt
    have : 5 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left hlt 4
    omega
  have h2 := hp.two_le
  interval_cases p
  · revert h
    decide
  · revert h
    decide
  · exact absurd hp (by norm_num)


theorem isEmpty_alt6_of_lieModel {G : Type} [Group G] {t : StatedLieTag} {p f : ℕ}
    (h : LieModel G t 0 p f) (hlarge : 4 ≤ lieSylowExponent t 0 * f) :
    IsEmpty (G ≃* alternatingGroup (Fin 6)) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨-, -, hfac⟩ := lieOrderFormulasInput G t 0 p f h.admissible h
  have hp : p.Prime := h.admissible.1
  have hcard : Nat.card G = 360 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  rw [hcard] at hfac
  have hdvd : p ^ ((360 : ℕ).factorization p) ∣ 360 := Nat.ordProj_dvd 360 p
  rw [hfac] at hdvd
  exact not_pow_four_dvd_360 hp ((pow_dvd_pow p hlarge).trans hdvd)

section Cat

open TauCeti CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.TauCetiBridge


theorem chevalleyModel_cat_twistedE6 {q : PrimePower} (hv : (LieTypeIndex.twistedE6 q).Valid) :
    ChevalleyExceptionalModel (Cat ⟨.twistedE6 q, hv⟩) .twistedE6 q.p q.exponent := by
  obtain ⟨K, _, _, hK, -⟩ := exists_field_pow q (m := TwistTag.E6.order) TwistTag.E6.order_pos
  rw [PrimePower.card_def] at hK
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 q.prime_p q.exponent_pos K hK
  have hσ'' : ∀ x, σ.toRingHom x = x ^ (q.p ^ q.exponent) := fun x => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ]
  have hσ' : ∀ x, σ.toRingHom x = x ^ q.card := fun x => by
    rw [PrimePower.card_def]
    exact hσ'' x
  obtain ⟨φ⟩ := Even.chevalleyBridgesAll.twistedE6 q hv K (by rw [PrimePower.card_def]; exact hK)
    σ.toRingHom hσ'
  exact ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, K, inferInstance, inferInstance, hK, σ.toRingHom,
    hσ'', ⟨φ.symm⟩⟩

open CFSG.Yardstones.Md42047359a2a in
theorem isEmpty_cat_alt6 (idx : ValidLieTypeIndex)
    (hfam : lieFamily idx.1 = .exceptional ∨
      (lieFamily idx.1 = .suzukiReeTits ∧ ∀ m, idx.1 ≠ .reeG2 m)) :
    IsEmpty ((CFSGIndex.lie idx).Group ≃* alternatingGroup (Fin 6)) := by
  classical
  obtain ⟨d, hv⟩ := idx
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  cases d with
  | E6 q =>
    obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
    have hZ : Subgroup.center ↥(adjointGroup .E6 K) = ⊥ := center_adjointGroup_eq_bot
    let eA : ↥(adjointGroup .E6 K) ≃* AdjointQuotient .E6 K :=
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
    have hM : LieModel (Cat ⟨.E6 q, hv⟩) .E6 0 q.p q.exponent :=
      Or.inr (Or.inl ⟨rfl, by decide, ⟨q.prime_p, q.exponent_pos, rfl⟩, K, inferInstance,
        inferInstance, by rw [hK, PrimePower.card_def], ⟨e.trans eA⟩⟩)
    exact isEmpty_alt6_of_lieModel hM (by simp [lieSylowExponent]; have := q.exponent_pos; omega)
  | E7 q =>
    obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
    have hZ : Subgroup.center ↥(adjointGroup .E7 K) = ⊥ := center_adjointGroup_eq_bot
    let eA : ↥(adjointGroup .E7 K) ≃* AdjointQuotient .E7 K :=
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
    have hM : LieModel (Cat ⟨.E7 q, hv⟩) .E7 0 q.p q.exponent :=
      Or.inr (Or.inl ⟨rfl, by decide, ⟨q.prime_p, q.exponent_pos, rfl⟩, K, inferInstance,
        inferInstance, by rw [hK, PrimePower.card_def], ⟨e.trans eA⟩⟩)
    exact isEmpty_alt6_of_lieModel hM (by simp [lieSylowExponent]; have := q.exponent_pos; omega)
  | E8 q =>
    obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
    have hZ : Subgroup.center ↥(adjointGroup .E8 K) = ⊥ := center_adjointGroup_eq_bot
    let eA : ↥(adjointGroup .E8 K) ≃* AdjointQuotient .E8 K :=
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
    have hM : LieModel (Cat ⟨.E8 q, hv⟩) .E8 0 q.p q.exponent :=
      Or.inr (Or.inl ⟨rfl, by decide, ⟨q.prime_p, q.exponent_pos, rfl⟩, K, inferInstance,
        inferInstance, by rw [hK, PrimePower.card_def], ⟨e.trans eA⟩⟩)
    exact isEmpty_alt6_of_lieModel hM (by simp [lieSylowExponent]; have := q.exponent_pos; omega)
  | F4 q =>
    obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
    have hZ : Subgroup.center ↥(adjointGroup .F4 K) = ⊥ := center_adjointGroup_eq_bot
    let eA : ↥(adjointGroup .F4 K) ≃* AdjointQuotient .F4 K :=
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
    have hM : LieModel (Cat ⟨.F4 q, hv⟩) .F4 0 q.p q.exponent :=
      Or.inr (Or.inl ⟨rfl, by decide, ⟨q.prime_p, q.exponent_pos, rfl⟩, K, inferInstance,
        inferInstance, by rw [hK, PrimePower.card_def], ⟨e.trans eA⟩⟩)
    exact isEmpty_alt6_of_lieModel hM (by simp [lieSylowExponent]; have := q.exponent_pos; omega)
  | G2 q =>
    obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.g2 q hv
    have hZ : Subgroup.center ↥(adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
    let eA : ↥(adjointGroup .G2 K) ≃* AdjointQuotient .G2 K :=
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
    have hq3 : 3 ≤ q.p ^ q.exponent := by rw [← PrimePower.card_def]; exact hr
    have hM : LieModel (Cat ⟨.G2 q, hv⟩) .G2 0 q.p q.exponent :=
      Or.inr (Or.inl ⟨rfl, by decide, ⟨q.prime_p, q.exponent_pos, rfl, hq3⟩, K, inferInstance,
        inferInstance, by rw [hK, PrimePower.card_def], ⟨e.trans eA⟩⟩)
    exact isEmpty_alt6_of_lieModel hM (by simp [lieSylowExponent]; have := q.exponent_pos; omega)
  | twistedE6 q =>
    exact isEmpty_alt6_of_lieModel (t := .twistedE6) (p := q.p) (f := q.exponent)
      (Or.inr (Or.inl ⟨rfl, by decide, chevalleyModel_cat_twistedE6 hv⟩))
      (by simp [lieSylowExponent]; have := q.exponent_pos; omega)
  | trialityD4 q =>
    exact isEmpty_alt6_of_lieModel (t := .trialityD4) (p := q.p) (f := q.exponent)
      (Or.inr (Or.inl ⟨rfl, by decide, chevalleyModel_cat_trialityD4 hv⟩))
      (by simp [lieSylowExponent]; have := q.exponent_pos; omega)
  | suzuki m =>
    have hm1 : 1 ≤ m := hr
    exact isEmpty_alt6_of_lieModel (t := .twistedB2) (p := 2) (f := 2 * m + 1)
      (Or.inr (Or.inr (Or.inr ⟨rfl, rfl,
        CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv⟩)))
      (by simp [lieSylowExponent]; omega)
  | reeG2 m => exact absurd rfl ((hfam.resolve_left (by simp [lieFamily])).2 m)
  | reeF4 m =>
    have hm1 : 1 ≤ m := hr
    exact isEmpty_alt6_of_lieModel (t := .twistedF4) (p := 2) (f := 2 * m + 1)
      (Or.inr (Or.inr (Or.inl ⟨rfl, by decide, reeTitsModel_cat_reeF4 hv⟩)))
      (by simp [lieSylowExponent]; omega)
  | tits =>
    exact isEmpty_alt6_of_lieModel (t := .Tits) (p := 2) (f := 1)
      (Or.inr (Or.inr (Or.inl ⟨rfl, by decide,
        CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨MulEquiv.refl _⟩⟩⟩)))
      (by simp [lieSylowExponent])
  | _ => simp [lieFamily] at hfam

end Cat

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
