module

public import CFSG.HardMathSupport.Dickson.Bal207.FamF42Class

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.FamF42

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

theorem isLieQuot_of_f42CompType {Y : Type} [Group Y]
    (h : F42CompType (Y ⧸ Subgroup.center Y)) :
    IsLieQuot Y (fun d => Bal207Index 3 d ∧ ¬ IsG2EightIndex d) := by
  obtain ⟨E, _, _, hE, ⟨f⟩⟩ := h
  let q : TauCeti.PrimePower := ⟨2, 1, Nat.prime_two, Nat.one_pos⟩
  have hq2 : q.card = 2 := by
    rw [TauCeti.PrimePower.card_def]
    rfl
  have hv : (TauCeti.LieTypeIndex.B 3 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    refine ⟨⟨by norm_num, fun h => absurd h.1 (by norm_num)⟩, fun h => ?_⟩
    have h3 : q.card = 3 := h.2
    rw [hq2] at h3
    exact absurd h3 (by norm_num)
  let d : TauCeti.ValidLieTypeIndex := ⟨.B 3 q, hv⟩
  let eT : d.Group ≃* StatedProj (StatedSp 3 ↥d.fixedField) :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj 3 q hv rfl le_rfl
  haveI : Finite d.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  haveI : Fintype d.fixedField := Fintype.ofFinite _
  haveI : Fintype E := Fintype.ofFinite E
  have hcard : Fintype.card E = Fintype.card d.fixedField := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      TauCeti.ValidLieTypeIndex.card_fixedField, hE]
    simp only [d, TauCeti.ValidLieTypeIndex.fieldOrder, TauCeti.LieTypeIndex.fieldOrder_B, hq2]
  let φ : E ≃+* d.fixedField := FiniteField.ringEquivOfCardEq hcard
  let e₁ := CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp φ 3)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  refine ⟨d, ⟨⟨rfl, Or.inl ⟨⟨rfl, rfl⟩, le_rfl⟩⟩, fun h => h⟩, ⟨f.trans
    ((CFSG.LieType.Universal.Symplectic.centerQuotientEquiv 3 E).trans (e₁.trans eT.symm))⟩⟩

section F4Two


theorem eq_one_of_pow_three_of_exp_two {P M : Type*} [Group P] [Group M] (Θ : P →* M)
    (hM : ∀ y : M, y ^ 2 = 1) {g : P} (hg : g ^ 3 = 1) : Θ g = 1 := by
  have h3 : Θ g ^ 3 = 1 := by rw [← map_pow, hg, map_one]
  calc Θ g = Θ g ^ 3 * (Θ g ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, hM, inv_one, one_mul]

theorem exists_conj_of_pow_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (β : MulAut ↥(adjointGroup Tag.F4 K)) (hβ : β ^ 3 = 1) :
    ∃ x : ↥(adjointGroup Tag.F4 K), MulAut.conj x = β := by
  have h2 : ∀ y : Multiplicative (ZMod (2 * 1)), y ^ 2 = 1 := by decide
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := inferInstanceAs (CharP K 2)
  obtain ⟨-, -, ⟨Θ, -, -, hΘker⟩, -⟩ :=
    even_F4_exact_automorphism_normal_form (f := 1) le_rfl K (by rw [hK]; norm_num)
  have hk : β ∈ Θ.ker := eq_one_of_pow_three_of_exp_two Θ h2 hβ
  rw [hΘker] at hk
  exact hk

theorem compShape_F4_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (β : MulAut ↥(adjointGroup Tag.F4 K)) (hβ : β ^ 3 = 1) (hβ1 : β ≠ 1) :
    CompShape F42CompType β := by
  obtain ⟨x, rfl⟩ := exists_conj_of_pow_three hK β hβ
  have hZ : Subgroup.center ↥(adjointGroup Tag.F4 K) = ⊥ := center_adjointGroup_eq_bot
  have hx3 : x ^ 3 = 1 := by
    have hc : x ^ 3 ∈ Subgroup.center ↥(adjointGroup Tag.F4 K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut ↥(adjointGroup Tag.F4 K) => φ g) hβ
      simp only [← map_pow, MulAut.conj_apply, MulAut.one_apply] at this
      calc g * x ^ 3 = x ^ 3 * g * (x ^ 3)⁻¹ * x ^ 3 := by rw [this]
        _ = x ^ 3 * g := by group
    rw [hZ] at hc
    exact hc
  have hx : orderOf x = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hx3) with h | h
    · rw [orderOf_eq_one_iff] at h
      exact absurd (by rw [h, map_one]) hβ1
    · exact h
  exact compShape_conj_F4_two hK x hx

theorem excF42_index {d : TauCeti.ValidLieTypeIndex} (hd : IsExcF42 d.1) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.F4 q).Valid),
      IsTwoPow q 1 ∧ d = ⟨.F4 q, hv⟩ := by
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | F4 q => exact ⟨q, hv, hd, rfl⟩
  | _ => exact absurd hd (by simp [IsExcF42])

theorem bal207PlusFamF42 (G : ∀ (S : Type) [Group S], MulAut S → Prop) :
    Bal207PlusFamF42 G := by
  intro X _ _ _ p K B A ctx hq hIH
  obtain ⟨d, ⟨rfl, hd⟩, ⟨f⟩⟩ := hq
  obtain ⟨q, hv, hq1, rfl⟩ := excF42_index hd
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  have hKq : Nat.card (GaloisField 2 1) = q.card := by
    rw [hK, TauCeti.PrimePower.card_def, hq1.1, hq1.2]
    norm_num
  obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_F4 q hv hq1.1 (GaloisField 2 1) hKq
  have hZ : Subgroup.center ↥(adjointGroup Tag.F4 (GaloisField 2 1)) = ⊥ :=
    center_adjointGroup_eq_bot
  let e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(adjointGroup Tag.F4 (GaloisField 2 1)) :=
    f.trans (eB.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot))
  exact bal207PlusFamClauses_of_compShape ctx hIH isoInvariant_f42CompType e
    (fun β hβ hβ1 => compShape_F4_two hK β hβ hβ1)
    (fun J hJ _ => isLieQuot_of_f42CompType hJ)

end F4Two

end CFSG.HardMathSupport.Dickson.Bal207.FamF42

end
