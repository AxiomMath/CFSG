module

public import CFSG.LieType.SeitzGeneration.CubeCoverField
public import CFSG.LieType.SeitzGeneration.TwE6SubfieldInndiag
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzRest5Even

public section

namespace CFSG.LieType.SeitzGeneration.CubeCoverField

open CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.GLTheoremB.MovingAround
  CFSG.LieType.SeitzGeneration.QuasiHigh5E6Cover
  CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LocalAnalysis.GLTheoremB
  CFSG.RankThree.PartOne.CTP
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest5
  CFSG.LieType.SeitzGeneration.TwE6Subfield


theorem uniSeitzPlanes_twE6_three_two_inndiag :
    Inputs2311c.UniSeitzPlanes fun d p E => p = 3 ∧
      ∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧ q.card % 3 = 2 ∧ q.card ≠ 2 ∧
        (InnerPlane d p E ∨
          (∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
            Nat.card K = (q.p ^ q.exponent) ^ 2 ∧
            (∀ c, σ c = c ^ (q.p ^ q.exponent)) ∧
            ∃ e : Cat d ≃* twistedE6RootGroup K σ,
              E.map (MulAut.congr e).toMonoidHom ≤
                twistedE6Inn K σ ⊔ twistedE6Diag K σ)) := by
  intro d p hp hp2 hpd hex E hE hc hs
  obtain ⟨hp3, q, hdq, hqmod, hqne, hcase⟩ := hs
  subst hp3
  by_cases hin : InnerPlane d 3 E
  · by_cases hn : NormalizesRSubgroup d E
    · exact Inputs2311c.uniSeitzPlanes_excParabolic d 3 hp hp2 hpd hex E hE hc
        ⟨hin, Or.inr (Or.inr ⟨q, hdq⟩), hn⟩
    · exact twE6ThreeOpenInner_holds d 3 hp hp2 hpd hex E hE hc
        ⟨hin, rfl, ⟨q, hdq, hqmod, hqne⟩, hn⟩
  · rcases hcase with h | hmodel
    · exact absurd h hin
    · by_cases hpar : Inputs2311d.IsTwE6DiagParabolicPlane d E
      · exact Inputs2311d.uniSeitzPlanes_twE6_diag_parabolic d 3 hp hp2 hpd hex E hE hc
          ⟨hin, rfl, hpar⟩
      · exact twE6ThreeOpenDiag_holds d 3 hp hp2 hpd hex E hE hc
          ⟨rfl, ⟨q, hdq, hqmod, hqne⟩, hin, ⟨q, hdq, hmodel⟩, hpar⟩

theorem twFJ_le_closure_uni_of_plane {k : Type} [Field k] [Finite k] (σ : k ≃+* k) {q : ℕ}
    (hk3 : ringChar k ≠ 3) (hσq : ∀ c, σ c = c ^ q) (hkq : Nat.card k = q ^ 2)
    (hq3 : q % 3 = 2) (hq8 : q ≠ 8)
    {η : k ≃+* k} (hη : orderOf η = 3)
    {A : Subgroup (MulAut ↥(twistedE6RootGroup k σ))}
    (hA : IsElemAbelian 3 A) (hAc : Nat.card A = 3 ^ 2)
    (hAD : A ≤ twistedE6Inn k σ ⊔ twistedE6Diag k σ)
    (hfaith : ∀ a ∈ twistedE6Inn k σ ⊔ twistedE6Diag k σ,
      (∀ y ∈ twFJ σ η, a y = y) → a = 1)
    (hAη : ∀ b ∈ A, Commute b (fieldActor (t := TwistTag.E6) σ η)) :
    twFJ σ η ≤ Subgroup.closure
      {s | s ∈ twFJ σ η ∧ (∃ n : ℕ, s ^ (ringChar k ^ n) = 1) ∧
        ∃ b ∈ A, b ≠ 1 ∧ b s = s} := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have hq2 : 2 ≤ q := by
    have h2 : 1 < Nat.card k := Finite.one_lt_card
    rw [hkq] at h2
    rcases Nat.lt_or_ge q 2 with hq | hq
    · interval_cases q <;> norm_num at h2
    · exact hq
  obtain ⟨hℓ, f, hf, hqf⟩ := prime_ringChar_and_eq_pow_of_card_sq k q hkq hq2
  subst q
  have hK2f : Nat.card k = ringChar k ^ (2 * f) := by
    rw [hkq, ← pow_mul, mul_comm]
  have hσ : ∀ c, σ c = c ^ (ringChar k ^ f) := hσq
  let qp : TauCeti.PrimePower := ⟨ringChar k, f, hℓ, by omega⟩
  have hqp : qp.card = ringChar k ^ f := TauCeti.PrimePower.card_def qp
  have hKq : Nat.card k = qp.card ^ 2 := by
    rw [hqp, hK2f, ← pow_mul, mul_comm]
  obtain ⟨q₀, hq₀p, hqq, hF⟩ :=
    exists_primePower_fixSubfield_twisted (m := 2) (by norm_num) hKq η Nat.prime_three
      (by norm_num : ¬ 3 ∣ 2) hη
  have hqq' : ringChar k ^ f = q₀.card ^ 3 := hqp ▸ hqq
  have hq₀mod : q₀.card % 3 = 2 := by
    have hcube : q₀.card ^ 3 % 3 = 2 := by
      rw [← hqq']
      exact hq3
    rw [Nat.pow_mod] at hcube
    have hlt : q₀.card % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases hmod : q₀.card % 3
    · norm_num at hcube
    · norm_num at hcube
    · rfl
  have hq₀ne2 : q₀.card ≠ 2 := by
    intro h2
    exact hq8 (by rw [hqq', h2]; norm_num)
  have hσqp : ∀ c, σ c = c ^ qp.card := by
    rw [hqp]
    exact hσ
  have hodd : Odd 3 := Nat.prime_three.odd_of_ne_two (by norm_num)
  obtain ⟨e₂⟩ := catEquiv_graphFixedRootGroup_of_data TwistTag.E6
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q₀
    (TauCeti.LieTypeIndex.valid_twistedE6 q₀) (fixSubfield η) hF (fixSubfieldRestrict σ η)
    (fixSubfieldRestrict_eq_pow_twE6 hqq hodd σ hσqp η hF)
  let e : ↥(twFJ σ η) ≃*
      Cat ⟨.twistedE6 q₀, TauCeti.LieTypeIndex.valid_twistedE6 q₀⟩ :=
    ((Subgroup.subgroupOfEquivOfLe (subfieldRootGroupImage_le_twistedE6 σ η)).trans
      (Subgroup.equivMapOfInjective _ _
        (baseChangeGL_injective (τ := TwistTag.E6.tag) _)).symm).trans e₂.symm
  let 𝒟 : Subgroup (MulAut (Cat ⟨.twistedE6 q₀,
      TauCeti.LieTypeIndex.valid_twistedE6 q₀⟩)) :=
    (twistedE6Inn (fixSubfield η) (fixSubfieldRestrict σ η) ⊔
      twistedE6Diag (fixSubfield η) (fixSubfieldRestrict σ η)).comap
        (MulAut.congr e₂).toMonoidHom
  refine le_closure_uni_fixed_of_le (p := 3) (r := ringChar k) (𝒟 := 𝒟) e ?_ hA hAc ?_
    (fun a ha hfix => hfaith a (hAD ha) hfix) ?_
  · intro P hPle hP hPc
    have hD2 : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3
        (TauCeti.LieTypeIndex.twistedE6 q₀) :=
      not_isD2SeitzException_of_chevalleyExc (isChevalleyExcIndex_twistedE6 q₀)
    have hpd : 3 ≠ (TauCeti.LieTypeIndex.twistedE6 q₀).characteristic := by
      rw [TauCeti.LieTypeIndex.characteristic_twistedE6, hq₀p]
      exact Ne.symm hk3
    have hmodel : ∃ (K : Type) (_ : Field K) (_ : Finite K) (τ : K ≃+* K),
        Nat.card K = (q₀.p ^ q₀.exponent) ^ 2 ∧
        (∀ c, τ c = c ^ (q₀.p ^ q₀.exponent)) ∧
        ∃ e' : Cat ⟨.twistedE6 q₀, TauCeti.LieTypeIndex.valid_twistedE6 q₀⟩ ≃*
            twistedE6RootGroup K τ,
          P.map (MulAut.congr e').toMonoidHom ≤ twistedE6Inn K τ ⊔ twistedE6Diag K τ := by
      refine ⟨fixSubfield η, inferInstance, inferInstance, fixSubfieldRestrict σ η, ?_, ?_,
        e₂, ?_⟩
      · simpa [TauCeti.PrimePower.card_def] using hF
      · intro c
        rw [fixSubfieldRestrict_eq_pow_twE6 hqq hodd σ hσqp η hF c,
          TauCeti.PrimePower.card_def]
      · rintro _ ⟨x, hx, rfl⟩
        have hx' := hPle hx
        rw [Subgroup.mem_comap] at hx'
        simpa only [MulAut.congr_apply] using hx'
    have h := uniSeitzPlanes_twE6_three_two_inndiag
      ⟨.twistedE6 q₀, TauCeti.LieTypeIndex.valid_twistedE6 q₀⟩ 3 Nat.prime_three
      (by norm_num) hpd hD2 P hP hPc
      ⟨rfl, q₀, rfl, hq₀mod, hq₀ne2, Or.inr hmodel⟩
    have hchar : (⟨.twistedE6 q₀, TauCeti.LieTypeIndex.valid_twistedE6 q₀⟩ :
        TauCeti.ValidLieTypeIndex).1.characteristic = ringChar k := by
      show (TauCeti.LieTypeIndex.twistedE6 q₀).characteristic = ringChar k
      rw [TauCeti.LieTypeIndex.characteristic_twistedE6, hq₀p]
    rwa [hchar] at h
  · intro a ha y hy
    exact mem_twFJ_of_commute hℓ hf hkq σ hσ Nat.prime_three (by norm_num) hη (hAη a ha) hy
  · intro a ha d hd
    let j : ↥(twistedE6RootGroup (fixSubfield η) (fixSubfieldRestrict σ η)) ≃*
        ↥(twFJ σ η) := twFJModelEquiv σ η
    have hdef : e = j.symm.trans e₂.symm := rfl
    have hej : ∀ y : ↥(twistedE6RootGroup (fixSubfield η) (fixSubfieldRestrict σ η)),
        e (j y) = e₂.symm y := fun y => by
      rw [hdef, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    have hje : ∀ y : ↥(twistedE6RootGroup (fixSubfield η) (fixSubfieldRestrict σ η)),
        j y = e.symm (e₂.symm y) := fun y => by
      rw [← hej y, MulEquiv.symm_apply_apply]
    obtain ⟨ψ, hψmem, hψprop⟩ :=
      exists_inndiag_restrict_twFJ hℓ hf hkq σ hσ hη (hAD ha) (hAη a ha)
    have hd'ψ : MulAut.congr e₂ d = ψ := by
      apply MulEquiv.ext
      intro y
      apply j.injective
      refine Subtype.ext ?_
      calc
        ((j ((MulAut.congr e₂ d) y) : twFJ σ η) : twistedE6RootGroup k σ) =
            ((e.symm (d (e₂.symm y)) : twFJ σ η) : twistedE6RootGroup k σ) := by
          rw [hje ((MulAut.congr e₂ d) y)]
          simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
        _ = ((e.symm (d (e (j y))) : twFJ σ η) : twistedE6RootGroup k σ) := by rw [hej y]
        _ = a (j y) := hd (j y) (j y).2
        _ = ((j (ψ y) : twFJ σ η) : twistedE6RootGroup k σ) := hψprop y
    rw [Subgroup.mem_comap]
    change (MulAut.congr e₂) d ∈ twistedE6Inn (fixSubfield η)
      (fixSubfieldRestrict σ η) ⊔ twistedE6Diag (fixSubfield η) (fixSubfieldRestrict σ η)
    rw [hd'ψ]
    exact hψmem

theorem seitzHyperGamma_eq_top_twE6_field_cube {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤)
    {k : Type} [Field k] [Finite k] (σ : k ≃+* k) {q : ℕ} (hk3 : ringChar k ≠ 3)
    (hσq : ∀ c, σ c = c ^ q) (hkq : Nat.card k = q ^ 2) (hq3 : q % 3 = 2) (hq8 : q ≠ 8)
    (θ : K ⧸ Subgroup.center K ≃* twistedE6RootGroup k σ) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3)
    (hED : ¬ coverImage θ E ≤ twistedE6Inn k σ ⊔ twistedE6Diag k σ) :
    seitzHyperGamma 3 E = ⊤ := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have hq2 : 2 ≤ q := by
    have h2 : 1 < Nat.card k := Finite.one_lt_card
    rw [hkq] at h2
    rcases Nat.lt_or_ge q 2 with hq | hq
    · interval_cases q <;> norm_num at h2
    · exact hq
  obtain ⟨hℓ, f, hf, hqf⟩ := prime_ringChar_and_eq_pow_of_card_sq k q hkq hq2
  subst q
  have hK2f : Nat.card k = ringChar k ^ (2 * f) := by
    rw [hkq, ← pow_mul, mul_comm]
  have hσ : ∀ c, σ c = c ^ (ringChar k ^ f) := hσq
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf k hkq σ hσ
  have : Finite (ModGL TwistTag.E6.tag k) := finite_modGL
  have : Finite ↥(twistedE6RootGroup k σ) := Subtype.finite
  have hDn : (twistedE6Inn k σ ⊔ twistedE6Diag k σ).Normal := by
    rw [← hker]
    infer_instance
  set D := twistedE6Inn k σ ⊔ twistedE6Diag k σ with hD
  have hEab : IsElemAbelian 3 (coverImage θ E) := isElemAbelian_coverImage θ hE
  have hBc : Nat.card ↥(coverImage θ E ⊓ D) = 3 ^ 2 :=
    card_inf_twistedE6Inndiag hℓ hf hkq σ hσ hEab
      (by rw [card_coverImage hperf θ E, hcard]) hED
  have hA : coverImage θ E ⊓ D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hBc
    norm_num at hBc
  refine seitzHyperGamma_eq_top_of_cover_overgroups hperf θ (p := 3) Nat.prime_three hE hcard
    hED hA ?_
  intro x hxE hxD
  obtain ⟨hηo, -, ψ, hψ⟩ := exists_conj_fieldActor_of_not_mem_twistedE6Inndiag hℓ hf k hK2f
    σ hσ Θ hΘ Nat.prime_three (by norm_num) (hEab.2 x hxE) hxD
  generalize Θ x = η at hηo hψ
  have hfaith : ∀ a ∈ D, (∀ y ∈ twFJ σ η, a y = y) → a = 1 := by
    intro a ha hfix
    obtain ⟨η', rfl⟩ := exists_fieldActor_eq_of_fix_twFJ hℓ hf hkq σ hσ η hfix
    have h1 : Θ (fieldActor σ η') = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact ha
    have h2 : Θ (fieldActor σ η') = η' :=
      hΘ _ 1 1 η' (by rw [map_one, map_one, one_mul, one_mul])
    rw [h2] at h1
    rw [h1, fieldActor_one]
  have hAD : ((coverImage θ E ⊓ D).map (MulAut.conj ψ).toMonoidHom) ≤ D := by
    rintro _ ⟨b, hb, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hDn.conj_mem b hb.2 ψ
  have hA' : IsElemAbelian 3 ((coverImage θ E ⊓ D).map (MulAut.conj ψ).toMonoidHom) :=
    (hEab.mono (inf_le_left : coverImage θ E ⊓ D ≤ coverImage θ E)).map _
  have hAc' : Nat.card ((coverImage θ E ⊓ D).map (MulAut.conj ψ).toMonoidHom) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj ψ).injective, hBc]
  have hAη : ∀ b ∈ (coverImage θ E ⊓ D).map (MulAut.conj ψ).toMonoidHom,
      Commute b (fieldActor (t := TwistTag.E6) σ η) := by
    rintro _ ⟨b, hb, rfl⟩
    have hbx : Commute b x :=
      congrArg Subtype.val (hEab.1.is_comm.comm ⟨b, hb.1⟩ ⟨x, hxE⟩)
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hψ]
    exact hbx.conj ψ
  have hplane := twFJ_le_closure_uni_of_plane σ hk3 hσ hkq hq3 hq8 hηo hA' hAc'
    hAD hfaith hAη
  have hr3 : ∀ j : ℕ, ¬ 3 ∣ ringChar k ^ j := fun j h =>
    hk3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hplane' : twFJ σ η ≤ Subgroup.closure
      {s | s ∈ twFJ σ η ∧ (∃ m : ℕ, ¬ 3 ∣ m ∧ s ^ m = 1) ∧
        ∃ b ∈ (coverImage θ E ⊓ D).map (MulAut.conj ψ).toMonoidHom, b ≠ 1 ∧ b s = s} := by
    refine hplane.trans (Subgroup.closure_mono ?_)
    rintro s ⟨hs, ⟨j, hj⟩, b, hb, hb1, hbs⟩
    exact ⟨hs, ⟨ringChar k ^ j, hr3 j, hj⟩, b, hb, hb1, hbs⟩
  haveI : D.Normal := hDn
  obtain ⟨J', hJ'x, hJ'g, hJ'f, hJ'm⟩ :=
    exists_overgroupData_of_conj_coprime (p := 3) (D := D) (E := coverImage θ E)
      hψ (twFJ_le_twR σ η) hplane' hfaith
      (fun H hH => le_fixedSubgroup_or_eq_top_of_twFJ_le hℓ hf hkq σ hσ hk3 hq8 hηo hH)
  exact ⟨J', hJ'x, hJ'g, hJ'f, hJ'm⟩

end CFSG.LieType.SeitzGeneration.CubeCoverField

end
