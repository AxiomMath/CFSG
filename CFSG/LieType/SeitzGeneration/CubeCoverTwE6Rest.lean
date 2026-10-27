module

public import CFSG.LieType.SeitzGeneration.CubeCoverTwField
public import CFSG.LieType.SeitzGeneration.CubeCoverTwE6Layer
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoMain
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoToralNeg
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoCaseI
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoFrameH0
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoCaseIProof
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoCaseIRankOne
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoCaseIRankTwo
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoCaseITau
import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Order3CaseI
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoCaseII
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoCycNonA2
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoRankTwo
import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Order3Pairs
public import CFSG.LieType.SeitzGeneration.CubeCoverE6Rest

public section

namespace CFSG.LieType.SeitzGeneration.CubeCoverE6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.QuasiHigh
  CFSG.LieType.SeitzGeneration.QuasiHigh2 CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration.CubeCoverPar
  CFSG.LieType.SeitzGeneration.CubeCoverField CFSG.LieType.SeitzGeneration.CubeCoverTwE6
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner
  CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc

section TwE6NRTwo

theorem twE6InnerNRTwo_holds : E6ThreeInner.TwE6InnerNRTwo :=
  twE6InnerNRTwo_of_cases
    (twE6ToralNegTwo_of_regularLangNeg twE6RegularLangNeg_of_cert)
    (twE6InnerA2CaseTwo_of_frameH0 twE6SylowMonoTwoAt_holds (twE6CaseIFrameH0_of_inputs
        CFSG.LieType.SeitzGeneration.ExcWideThree.e6CaseITable_holds twE6CaseI_tau
        twE6CaseI_rankOne_kind3A2 twE6CaseI_rankOne_kind2A2 twE6CaseI_rankTwo))
    (twE6InnerNoA2Two_of_cycNonA2_rankTwo twE6CaseIICycNonA2_holds
        (twE6CaseIIRankTwo_of_pairs e6Order3Pairs_holds))

end TwE6NRTwo

section NegDatum

@[expose] def CoverTwE6NegDatum : Prop :=
  ∀ (K : Type) [Group K] [Finite K], commutator K = ⊤ →
    ∀ (k : Type) [Field k] [Finite k] (σ : k ≃+* k) (q : ℕ), Nat.card k = q ^ 2 →
      (∀ c, σ c = c ^ q) → q % 3 = 2 → q ≠ 2 →
      ∀ (θ : K ⧸ Subgroup.center K ≃* twistedE6RootGroup k σ) (E : Subgroup (MulAut K)),
        IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
        E ≤ (MulAut.conj : K →* MulAut K).range →
        ¬ NormalizesRGroup (ringChar k) ((coverImage θ E).comap MulAut.conj) →
        E6ThreeInner.TwE6NegDatumDiag k σ q ((coverImage θ E).comap MulAut.conj) →
        seitzHyperGamma 3 E = ⊤

end NegDatum

section DiagNotAll24

@[expose] def CoverTwE6DiagNotAll24 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], commutator K = ⊤ →
    ∀ (k : Type) [Field k] [Finite k] (σ : k ≃+* k) (q : ℕ), Nat.card k = q ^ 2 →
      (∀ c, σ c = c ^ q) → ringChar k ≠ 3 → q % 3 = 2 → q ≠ 2 → q ≠ 8 →
      ∀ (θ : K ⧸ Subgroup.center K ≃* twistedE6RootGroup k σ) (E : Subgroup (MulAut K)),
        IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
        coverImage θ E ≤ twistedE6Inn k σ ⊔ twistedE6Diag k σ →
        ¬ coverImage θ E ≤ twistedE6Inn k σ →
        ¬ TwE6NormalizesR k σ (coverImage θ E) →
        ¬ TwE6InnerAll24 k σ (coverImage θ E) → seitzHyperGamma 3 E = ⊤

end DiagNotAll24

section Exc

theorem excIsotropic_twE6 {K : Type} [Group K] (hperf : commutator K = ⊤)
    {q : TauCeti.PrimePower} {hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid}
    (e : K ⧸ Subgroup.center K ≃* Cat ⟨.twistedE6 q, hv⟩)
    {k : Type} [Field k] [Finite k] (σ : k ≃+* k) (hk : ringChar k = q.p)
    (φ : Cat ⟨.twistedE6 q, hv⟩ ≃* twistedE6RootGroup k σ)
    {E : Subgroup (MulAut K)}
    (hin : coverImage (e.trans φ) E ≤ twistedE6Inn k σ)
    (hn : TwE6NormalizesR k σ (coverImage (e.trans φ) E)) :
    ExcIsotropic ⟨.twistedE6 q, hv⟩ E := by
  rw [TwE6NormalizesR] at hn
  obtain ⟨R, hR, hRp, hRE⟩ := hn
  have hchar : (⟨.twistedE6 q, hv⟩ : TauCeti.ValidLieTypeIndex).1.characteristic =
      ringChar k := by
    rw [TauCeti.LieTypeIndex.characteristic_twistedE6, ← hk]
  have hRp' : IsPGroup
      (⟨.twistedE6 q, hv⟩ : TauCeti.ValidLieTypeIndex).1.characteristic R := by
    rw [hchar]
    exact hRp
  refine ⟨isChevalleyExcIndex_twistedE6 q,
    (coverImage_le_range_conj_iff hperf (e.trans φ)).1 ?_,
    ⟨e, normalizesRSub_innerImage e φ hR hRp' hRE⟩⟩
  simpa [twistedE6Inn, CFSG.ComponentClassification.OuterAutomorphisms.inner] using hin

end Exc

section Giant

theorem seitzHyperGamma_eq_top_twE6_inner_cube (hN : CoverTwE6NegDatum)
    {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤)
    {k : Type} [Field k] [Finite k] {σ : k ≃+* k} {q : ℕ}
    (hk3 : ringChar k ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hkq : Nat.card k = q ^ 2)
    (hq3 : q % 3 = 2) (hq2 : q ≠ 2)
    (θ : K ⧸ Subgroup.center K ≃* twistedE6RootGroup k σ) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3)
    (hEi : E ≤ (MulAut.conj : K →* MulAut K).range)
    (hNR : ¬ TwE6NormalizesR k σ (coverImage θ E)) :
    seitzHyperGamma 3 E = ⊤ := by
  classical
  let E₀ : Subgroup (twistedE6RootGroup k σ) :=
    (coverImage θ E).comap (MulAut.conj : twistedE6RootGroup k σ →* _)
  have hinj : Function.Injective
      (MulAut.conj : twistedE6RootGroup k σ →* MulAut (twistedE6RootGroup k σ)) :=
    mulAut_conj_injective_of_center_eq_bot
      (exceptional_fixed_center_trivial TwistTag.E6 k σ)
  have hInn : coverImage θ E ≤ twistedE6Inn k σ := by
    have h := coverImage_le_range_conj θ hEi
    simpa [twistedE6Inn, CFSG.ComponentClassification.OuterAutomorphisms.inner] using h
  have hmap : E₀.map (MulAut.conj : twistedE6RootGroup k σ →* _) = coverImage θ E :=
    Subgroup.map_comap_eq_self hInn
  have hE₀ab : IsElemAbelian 3 E₀ := (isElemAbelian_coverImage θ hE).comap hinj
  have hcardE₀ : Nat.card E₀ = 3 ^ 3 := by
    have h1 : Nat.card (E₀.map (MulAut.conj : twistedE6RootGroup k σ →* _)) =
        Nat.card E₀ :=
      Subgroup.card_map_of_injective hinj
    rw [← h1, hmap, card_coverImage hperf θ E, hcard]
  have hNRg : ¬ NormalizesRGroup (ringChar k) E₀ := by
    intro h
    apply hNR
    obtain ⟨U, hU1, hUp, hUn⟩ := h
    refine ⟨U, hU1, hUp, fun ε hε => ?_⟩
    rw [← hmap] at hε
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hε
    exact hUn x hx
  rcases twE6InnerNRTwo_holds k σ q hkq hσ hq3 hq2 E₀ hE₀ab hcardE₀ hNRg with
    hAll | hNeg
  · exact seitzHyperGamma_eq_top_twE6_inner_of_all24 hperf hk3 hσ hkq hq3 hq2 θ hE hcard
      hEi rfl hAll
  · exact hN K hperf k σ q hkq hσ hq3 hq2 θ E hE hcard hEi hNRg hNeg

theorem seitzHyperGamma_eq_top_twE6_cube (hN : CoverTwE6NegDatum) (hD : CoverTwE6DiagNotAll24)
    {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤)
    {k : Type} [Field k] [Finite k] (σ : k ≃+* k) {q : ℕ}
    (hk3 : ringChar k ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hkq : Nat.card k = q ^ 2)
    (hq3 : q % 3 = 2) (hq2 : q ≠ 2)
    (θ : K ⧸ Subgroup.center K ≃* twistedE6RootGroup k σ) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3)
    (h8 : q = 8 → coverImage θ E ≤ twistedE6Inn k σ)
    (hiso : coverImage θ E ≤ twistedE6Inn k σ → ¬ TwE6NormalizesR k σ (coverImage θ E))
    (hpair : ¬ QuasiHigh2.InvP'Pair 3 E) :
    seitzHyperGamma 3 E = ⊤ := by
  by_cases hd : coverImage θ E ≤ twistedE6Inn k σ ⊔ twistedE6Diag k σ
  · by_cases hi : coverImage θ E ≤ twistedE6Inn k σ
    · have hEi : E ≤ (MulAut.conj : K →* MulAut K).range :=
        (coverImage_le_range_conj_iff hperf θ).1
          (by simpa [twistedE6Inn, CFSG.ComponentClassification.OuterAutomorphisms.inner]
            using hi)
      exact seitzHyperGamma_eq_top_twE6_inner_cube hN hperf hk3 hσ hkq hq3 hq2 θ hE hcard
        hEi (hiso hi)
    · by_cases hn : TwE6NormalizesR k σ (coverImage θ E)
      · exact absurd (invP'Pair_of_twE6Inndiag σ hk3 hσ hkq θ hE hd hn) hpair
      · by_cases hA : TwE6InnerAll24 k σ (coverImage θ E)
        · exact seitzHyperGamma_eq_top_twE6_diag_all24 hperf hk3 hσ hkq hq3 hq2 θ hE hcard
            hd hi hA
        · exact hD K hperf k σ q hkq hσ hk3 hq3 hq2 (fun hq8 => hi (h8 hq8)) θ E
            hE hcard hd hi hn hA
  · have hq8 : q ≠ 8 := fun h => hd (le_trans (h8 h) le_sup_left)
    exact seitzHyperGamma_eq_top_twE6_field_cube hperf σ hk3 hσ hkq hq3 hq8 θ hE hcard hd

theorem coverTwE6Cubes_of (hN : CoverTwE6NegDatum) (hD : CoverTwE6DiagNotAll24) :
    CoverTwE6Cubes := by
  intro p hp hp2 K _ _ hq d hd hpd hL34 hz hci hE6 E hE hcard hex hCS hX hLD hP hU hS hStd
  obtain ⟨q, hdq⟩ := hE6
  obtain ⟨dd, hv⟩ := d
  have hdd : dd = TauCeti.LieTypeIndex.twistedE6 q := hdq
  subst hdd
  obtain ⟨e⟩ := hd
  obtain ⟨hp3, h3⟩ := hci
  subst hp3
  obtain ⟨k, _, σ, hK, hσ, ⟨φ⟩⟩ := exists_catEquiv_twistedE6 q hv
  haveI : Finite k := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  have hk : ringChar k = q.p := by
    refine ringChar_eq_of_card_pow q.prime_p q.exponent_pos k ?_
    rw [hK, ← pow_mul, mul_comm]
  have hpd' : 3 ≠ q.p := by
    have h : 3 ≠ (TauCeti.LieTypeIndex.twistedE6 q).characteristic := hpd
    rwa [TauCeti.LieTypeIndex.characteristic_twistedE6] at h
  have hk3 : ringChar k ≠ 3 := by
    rw [hk]
    exact fun h => hpd' h.symm
  have hkq : Nat.card k = q.card ^ 2 := by
    rw [TauCeti.PrimePower.card_def]
    exact hK
  have hσq : ∀ c, σ c = c ^ q.card := by
    intro c
    rw [TauCeti.PrimePower.card_def]
    exact hσ c
  have hq3 : q.card % 3 = 2 := by
    have h := Nat.dvd_iff_mod_eq_zero.1 h3
    omega
  have hq2 : q.card ≠ 2 := by
    intro h2
    have hexc : ExcIndex 3 (.twistedE6 q) :=
      Or.inr ⟨rfl, Or.inr (Or.inr (Or.inl (isTwoPow_of_card_eq' (by rw [h2]; norm_num))))⟩
    have hnotsix : ¬ IsSixIndex (.twistedE6 q) := by
      rintro (h | h | h)
      · exact absurd h (by simp [IsF4EightIndex])
      · exact absurd h (by simp [IsD4FourIndex])
      · obtain ⟨hp2, hexp3⟩ := h
        rw [TauCeti.PrimePower.card_def, hp2, hexp3] at h2
        norm_num at h2
    rcases hex with h | ⟨hsix, -⟩
    · exact h hexc
    · exact hnotsix hsix
  have h8 : q.card = 8 → coverImage (e.trans φ) E ≤ twistedE6Inn k σ := by
    intro h8c
    have hsix : IsSixIndex (.twistedE6 q) :=
      Or.inr (Or.inr (isTwoPow_of_card_eq' (by rw [h8c]; norm_num)))
    have hexc : ExcIndex 3 (.twistedE6 q) :=
      Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr hsix)))⟩
    rcases hex with h | ⟨-, hEi⟩
    · exact absurd hexc h
    · have hcov := coverImage_le_range_conj (e.trans φ) hEi
      simpa [twistedE6Inn, CFSG.ComponentClassification.OuterAutomorphisms.inner] using hcov
  have hiso : coverImage (e.trans φ) E ≤ twistedE6Inn k σ →
      ¬ TwE6NormalizesR k σ (coverImage (e.trans φ) E) := by
    intro hin hn
    exact hX (excIsotropic_twE6 hq.1 e σ hk φ hin hn)
  exact seitzHyperGamma_eq_top_twE6_cube hN hD hq.1 σ hk3 hσq hkq hq3 hq2 (e.trans φ)
    hE hcard h8 hiso hP

end Giant

end CFSG.LieType.SeitzGeneration.CubeCoverE6

end
