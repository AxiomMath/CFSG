module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz11b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1310u2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz13

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LieType.Chevalley CFSG.RankThree.Chevalley CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

set_option linter.unusedSectionVars false

theorem eq_twistedE6_two_of_rest5 {d : TauCeti.ValidLieTypeIndex} (hexc : ExcIndex 3 d.1)
    (htits : d.1 ≠ .tits) (hl28 : ¬ IsL2EightIndex d.1) (hg : ¬ Gen2318Index d.1)
    (hs6 : ¬ InputsSeitz7.IsSpTwoIndex d) (hu4 : ¬ InputsSeitz7.IsUnitaryTwoIndex d)
    (hS8 : ¬ InputsSeitz7.IsSpEightIndex d) (hU8 : ¬ InputsSeitz7.IsUnitaryEightIndex d)
    (hU38 : ¬ InputsSeitz7.IsUThreeEightIndex d) (hO2 : ¬ InputsSeitz8.IsOrthTwoIndex d)
    (hT2 : ¬ InputsSeitz8.IsTriD4TwoIndex d) (hG8 : ¬ InputsSeitz8.IsG2EightIndex d)
    (hU6 : ¬ InputsSeitz7.IsUSixIndex d) (hO8 : ¬ InputsSeitz8.IsOmegaEightTwoIndex d)
    (hD44 : ¬ IsD4FourIndex d.1) (hF2 : ¬ Bal209F4Aux.IsF4TwoIndex d.1)
    (hE4 : ¬ IsTwistedE6FourIndex d.1) (hF8 : ¬ IsF4EightIndex d.1)
    (hD8 : ¬ OuterFourAux.IsD4EightIndex d.1) (hO : ¬ InputsSeitz10.IsOrthEightIndex d)
    (hT : ¬ OuterFourInAux.IsTwE6EightIndex d.1) :
    ∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧ IsTwoPow q 1 := by
  obtain ⟨d0, hv⟩ := d
  rcases hexc with h | ⟨-, h | h | h | h | h⟩
  ·
    cases d0 with
    | B r q =>
      obtain ⟨-, ⟨hq, hr⟩ | ⟨hq, hr⟩⟩ := h
      · exact (hs6 ⟨r, q, hr, hq.1, hq.2, rfl⟩).elim
      · exact (hS8 ⟨r, q, hr, hq.1, hq.2, rfl⟩).elim
    | twistedA r q =>
      have hr2 : 2 ≤ r :=
        TauCeti.LieTypeIndex.two_le_of_twistedA_inStandardRange ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      obtain ⟨-, ⟨hq | hq, h3⟩ | ⟨hq, rfl⟩⟩ := h
      · exact (hu4 ⟨r, q, by omega, h3, hq.1, hq.2, rfl⟩).elim
      · exact (hU8 ⟨r, q, by omega, h3, hq.1, hq.2, rfl⟩).elim
      · exact (hU6 ⟨q, hq.1, Or.inl hq.2, rfl⟩).elim
    | D r q =>
      obtain ⟨-, ⟨hq | hq, -, hr⟩ | ⟨hq, rfl⟩⟩ := h
      · exact (hO2 ⟨r, q, by omega, hq.1, hq.2, Or.inl rfl⟩).elim
      · exact (hO ⟨r, q, hq.1, hq.2, Or.inl ⟨hr, rfl⟩⟩).elim
      · exact (hO8 ⟨q, hq.1, hq.2, rfl⟩).elim
    | twistedD r q =>
      obtain ⟨-, hq | hq, -, hr⟩ := h
      · exact (hO2 ⟨r, q, hr, hq.1, hq.2, Or.inr rfl⟩).elim
      · exact (hO ⟨r, q, hq.1, hq.2, Or.inr ⟨hr, rfl⟩⟩).elim
    | trialityD4 q =>
      obtain ⟨-, hq⟩ := h
      exact (hT2 ⟨q, hq.1, hq.2, rfl⟩).elim
    | G2 q =>
      obtain ⟨-, hq⟩ := h
      exact (hG8 ⟨q, hq.1, hq.2, rfl⟩).elim
    | F4 q =>
      obtain ⟨-, hq⟩ := h
      exact (hF2 hq).elim
    | tits => exact (htits rfl).elim
    | suzuki m =>
      obtain ⟨h5, -⟩ := h
      exact absurd h5 (by decide)
    | reeF4 m =>
      obtain ⟨h5, -⟩ := h
      exact absurd h5 (by decide)
    | _ => exact h.elim
  · exact (hl28 h).elim
  · exact (hg h).elim
  ·
    cases d0 with
    | twistedE6 q => exact ⟨q, rfl, h⟩
    | _ => exact h.elim
  · exact (hE4 h).elim
  ·
    rcases h with h | h | h
    · exact (hF8 h).elim
    · exact (hD44 h).elim
    · cases d0 with
      | twistedA r q =>
        obtain ⟨hq, rfl | rfl⟩ := h
        · exact (hU38 ⟨q, hq.1, hq.2, rfl⟩).elim
        · exact (hU6 ⟨q, hq.1, Or.inr hq.2, rfl⟩).elim
      | twistedE6 q => exact (hT h).elim
      | D r q => exact (hD8 h).elim
      | _ => exact h.elim

theorem exists_indexNine_of_mulEquiv {K T : Type} [Group K] [Group T] (θ : K ≃* T)
    (hT : ∀ D : Subgroup (MulAut T), IsElemAbelian 3 D →
      ∃ E : Subgroup (MulAut T), E ≤ D ∧ Nat.card D ≤ 9 * Nat.card E ∧
        ∃ V : Subgroup T, V ≠ ⊥ ∧ IsPGroup 2 ↥V ∧ ∀ φ ∈ E, ∀ v ∈ V, φ v ∈ V)
    {D : Subgroup (MulAut K)} (hD : IsElemAbelian 3 D) :
    ∃ E : Subgroup (MulAut K), E ≤ D ∧ Nat.card D ≤ 9 * Nat.card E ∧
      ∃ U : Subgroup K, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U := by
  obtain ⟨E', hE'D, hcard, V, hV0, hV2, hE'V⟩ :=
    hT (D.map (MulAut.congr θ).toMonoidHom) (CFSG.SectionRank.isElemAbelian_map hD _)
  have hED : E'.map (MulAut.congr θ).symm.toMonoidHom ≤ D := by
    rintro _ ⟨φ', hφ', rfl⟩
    obtain ⟨ψ, hψ, rfl⟩ := hE'D hφ'
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact hψ
  have h2 : Nat.card D = Nat.card (D.map (MulAut.congr θ).toMonoidHom) :=
    (Subgroup.card_map_of_injective (MulAut.congr θ).injective).symm
  have h3 : Nat.card (E'.map (MulAut.congr θ).symm.toMonoidHom) = Nat.card E' :=
    Subgroup.card_map_of_injective (MulAut.congr θ).symm.injective
  refine ⟨E'.map (MulAut.congr θ).symm.toMonoidHom, hED, ?_, V.map θ.symm.toMonoidHom, ?_, hV2.map _, ?_⟩
  · rw [h2, h3]
    exact hcard
  · intro h
    exact hV0 ((Subgroup.map_eq_bot_iff_of_injective V (f := θ.symm.toMonoidHom) θ.symm.injective).1 h)
  · rintro _ ⟨φ', hφ', rfl⟩ _ ⟨v, hv, rfl⟩
    refine ⟨φ' v, hE'V φ' hφ' v hv, ?_⟩
    simp [MulAut.congr_symm_apply]

section Main


theorem input23_19ExcThreeRest5_holds : InputsSeitz11.Input23_19ExcThreeRest5 := by
  intro X _ _ hKX hcore B hB hB4 hrk K hK haut hsmall hBN d hd hexc htits hl28 hg hs6 hu4 hS8 hU8 hU38
    hO2 hT2 hG8 hU6 hO8 hD44 hF2 hE4 hF8 hD8 hOut hT8 hsix hO hT hC
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨e⟩ := hd
  obtain ⟨d0, hv⟩ := d
  obtain ⟨q, rfl, hq⟩ : ∃ q : TauCeti.PrimePower, d0 = .twistedE6 q ∧ IsTwoPow q 1 :=
    eq_twistedE6_two_of_rest5 hexc htits hl28 hg hs6 hu4 hS8 hU8 hU38 hO2 hT2 hG8 hU6 hO8 hD44 hF2 hE4 hF8
      hD8 hO hT
  have hZ : Subgroup.center ↥K = ⊥ := by
    by_contra hZ
    exact InputsSeitz7.cen_ne_bot_of_center_ne_bot hcore hB hrk hK hZ hBN hC
  let eK : ↥K ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group := (InputsSeitz3.equivCenterQuot hZ).trans e
  obtain ⟨L, _, σ, hL, hσ, ⟨eC⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  have hq2 : q.p ^ q.exponent = 2 := by rw [hq.1, hq.2, pow_one]
  have hL4 : Nat.card L = 2 ^ 2 := by rw [hL, hq2]
  haveI : Finite L := Nat.finite_of_card_ne_zero (by rw [hL4]; norm_num)
  have hσ2 : ∀ c, σ c = c ^ 2 := fun c => by rw [hσ, hq2]
  let θ : ↥K ≃* twistedE6RootGroup L σ := eK.trans eC
  obtain ⟨E₀, hE₀el, r, hr5, hE₀c⟩ := InputsSeitz11.exists_elemAbelian_five_twE6Two hL4 σ hσ2
  have h5 : 5 ≤ CFSG.Open.pRank 3 B := by
    have h := CFSG.SectionRank.le_pRank hp.one_lt (le_top : (E₀.map θ.symm.toMonoidHom).map K.subtype ≤ ⊤)
      (CFSG.SectionRank.isElemAbelian_map (CFSG.SectionRank.isElemAbelian_map hE₀el _) _)
      (by rw [Subgroup.card_map_of_injective K.subtype_injective,
        Subgroup.card_map_of_injective θ.symm.injective, hE₀c])
    rw [hrk]
    omega
  set A := InputsSeitz3.autIm B K with hAdef
  have hAel : IsElemAbelian 3 A := InputsSeitz3.isElemAbelian_autIm hB K
  have hAc : Nat.card A = 3 ^ CFSG.Open.pRank 3 B :=
    (InputsSeitz3.card_autIm hBN hC).trans (GL83.PiGen.card_eq_pow_pRank hB)
  have hA5 : 243 ≤ Nat.card A := by
    rw [hAc]
    calc 243 = 3 ^ 5 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 B := Nat.pow_le_pow_right (by norm_num) h5
  obtain ⟨E, hEA, hEcard, U, hU0, hU2, hEU⟩ :=
    exists_indexNine_of_mulEquiv θ (Claims1310u.twE6TwoStarIndexNine_holds L σ hL4 hσ2) hAel
  have hE27 : 27 ≤ Nat.card E := by omega
  obtain ⟨F, hFE, hFc⟩ :=
    InputsSeitz10.exists_card_twentySeven_orthEight (GL83.CompFam.elem_mono hAel hEA) hE27
  exact InputsSeitz10.le_glbCore_of_e27_twoGroup (d := ⟨.twistedE6 q, hv⟩) hB hq.1 eK le_rfl hC
    (hFE.trans hEA) hFc hU0 hU2 fun φ hφ u hu => hEU φ (hFE hφ) u hu

end Main

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz13

end
