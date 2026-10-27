module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleLang
public import CFSG.RankThree.Chevalley.G2F4FiniteFieldFixedMatrices
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtUntw

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.RankThree.Chevalley

set_option linter.unusedSectionVars false


section Setup

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

@[expose] def LangSetup.Descends : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : Algebra K L)
    (e : adjointGroup τ K ≃* S.Γ), Nat.card K = S.D.q ∧
      ∀ h : adjointGroup τ K, (e h : ModGL τ L) =
        S.D.g0⁻¹ * baseChangeGL (algebraMap K L) (h : ModGL τ K) * S.D.g0

@[expose] def LangSetup.IsAlgebraic : Prop :=
  ∀ c : L, ∃ n : ℕ, 0 < n ∧ c ^ (S.D.q ^ n) = c

theorem LangSetup.exists_frobenius_of_steinberg (h6 : τ ≠ .E6) (hD4 : τ ≠ .D4) :
    ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr) := by
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
  refine ⟨Fr, hFr, ?_⟩
  rcases hP with rfl | ⟨t, ht, rfl⟩
  · ext g : 1
    rw [hΦ]
    simp
  · exfalso
    cases t
    · exact h6 ht.symm
    · exact hD4 ht.symm

theorem LangSetup.exists_fixedField :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : Algebra K L), Nat.card K = S.D.q := by
  classical
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨hfin, hcard⟩ := ncard_pow_eq_self (L := L) r e he
  let K : Subfield L := (iterateFrobenius L r e).eqLocusField (RingHom.id L)
  have hset : (K : Set L) = {c : L | c ^ (r ^ e) = c} := by
    ext c
    change iterateFrobenius L r e c = c ↔ _
    rw [iterateFrobenius_def]
    rfl
  have hfinK : Finite K := by
    have h1 : (K : Set L).Finite := by rw [hset]; exact hfin
    exact h1.to_subtype
  refine ⟨K, inferInstance, hfinK, inferInstance, ?_⟩
  have h1 : Nat.card K = (K : Set L).ncard := Nat.card_coe_set_eq (K : Set L)
  rw [h1, hset, hcard, hq]

@[expose] noncomputable def LangDescent.mulEquiv' {D : LangDatum τ L} {p : ℕ} {C : Type} [Group C]
    {ι : C →* ModGL τ L} (h : LangDescent D p ι) (hι : Function.Injective ι) : C ≃* D.Γ :=
  (MonoidHom.ofInjective hι).trans
    ((Subgroup.equivMapOfInjective ι.range (MulAut.conj D.g0⁻¹).toMonoidHom
      (MulAut.conj D.g0⁻¹).injective).trans (MulEquiv.subgroupCongr h.Γ_eq.symm))

theorem LangDescent.coe_mulEquiv' {D : LangDatum τ L} {p : ℕ} {C : Type} [Group C]
    {ι : C →* ModGL τ L} (h : LangDescent D p ι) (hι : Function.Injective ι) (x : C) :
    ((h.mulEquiv' hι x : D.Γ) : ModGL τ L) = D.g0⁻¹ * ι x * D.g0 := by
  change (MulAut.conj D.g0⁻¹) (ι x) = _
  rw [MulAut.conj_apply, inv_inv]

theorem LangSetup.descends_of_langDescent {K : Type} [Field K] [Finite K] [Algebra K L]
    (hq : Nat.card K = S.D.q)
    (hd : LangDescent S.D p ((baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype)) :
    S.Descends := by
  have hι : Function.Injective
      ((baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype) :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  exact ⟨K, inferInstance, inferInstance, inferInstance, hd.mulEquiv' hι, hq,
    fun x => hd.coe_mulEquiv' hι x⟩

theorem LangSetup.frobenius_bijective {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) :
    Function.Bijective Fr :=
  ⟨Fr.injective, fun c => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c S.q_pos
    exact ⟨z, by rw [hFr, hz]⟩⟩

theorem LangSetup.descends_of_exact (hτ : τ = .G2 ∨ τ = .F4)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr))
    (hperf : ∀ (K : Type) [Field K] [Finite K], commutator ↥(adjointGroup τ K) = ⊤) :
    S.Descends := by
  classical
  obtain ⟨Fr, hFr, hΦ⟩ := hΦ
  obtain ⟨K, _, _, _, hK⟩ := S.exists_fixedField
  have hFrK : ∀ c, Fr c = c ^ Nat.card K := fun c => by rw [hK]; exact hFr c
  have hex := frobenius_fixed_eq_map_of_bijective (τ := τ) hτ Fr hFrK (S.frobenius_bijective hFr)
  have hfix : S.D.fix = (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
    rw [← hex]
    ext x
    rw [LangDatum.mem_fix, hΦ]
    rfl
  set ι : adjointGroup τ K →* ModGL τ L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype with hι
  have hrange : ι.range = (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
    rw [hι, MonoidHom.range_comp, Subgroup.range_subtype]
  have hfixr : S.D.fix = ι.range := hfix.trans hrange.symm
  have : Finite (ModGL τ K) := finite_modGL
  have : Finite (adjointGroup τ K) := inferInstance
  refine S.descends_of_langDescent hK ⟨?_, hfixr.ge, fun P hP _ => hfixr ▸ hP, ?_⟩
  · rw [hfixr]
    exact Finite.of_surjective ι.rangeRestrict ι.rangeRestrict_surjective
  · rw [hfixr, hrange, ← Subgroup.map_commutator,
      commutator_self_eq_of_commutator_top (hperf K)]

theorem LangSetup.descends_of_untw (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1)) (hp3 : 3 < p)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr))
    (hAlg : S.IsAlgebraic)
    (hperf : ∀ (K : Type) [Field K] [Finite K], commutator ↥(adjointGroup τ K) = ⊤) :
    S.Descends := by
  classical
  obtain ⟨Fr, hFr, hΦ⟩ := hΦ
  obtain ⟨K, _, _, _, hK⟩ := S.exists_fixedField
  have hFrK : ∀ c, Fr c = c ^ Nat.card K := fun c => by rw [hK]; exact hFr c
  have : Algebra.IsAlgebraic K L := ⟨fun c => by
    obtain ⟨n, hn, hc⟩ := hAlg c
    have hq1 : 1 < Nat.card K ^ n := by
      rw [hK]
      exact Nat.one_lt_pow hn.ne' S.hqpow.1.one_lt
    refine ⟨Polynomial.X ^ (Nat.card K ^ n) - Polynomial.X, ?_, ?_⟩
    · exact FiniteField.X_pow_card_sub_X_ne_zero K hq1
    · simp only [map_sub, map_pow, Polynomial.aeval_X]
      rw [hK, hc, sub_self]⟩
  have : IsAlgClosure K L := ⟨inferInstance, inferInstance⟩
  exact S.descends_of_langDescent hK
    (langDescent_untw d hτ hFrK S.D hΦ S.hp hp3 (hperf K))

theorem LangSetup.isAlgebraic_of_algebraic (K : Type) [Field K] [Finite K] [Algebra K L]
    [Algebra.IsAlgebraic K L] (a : ℕ) (hK : Nat.card K = S.D.q ^ a) : S.IsAlgebraic := by
  classical
  intro c
  have hint : IsIntegral K c := (Algebra.IsAlgebraic.isAlgebraic c).isIntegral
  have : FiniteDimensional K (IntermediateField.adjoin K {c}) := IntermediateField.adjoin.finiteDimensional hint
  have : Finite (IntermediateField.adjoin K {c}) := Module.finite_of_finite K
  letI : Fintype (IntermediateField.adjoin K {c}) := Fintype.ofFinite _
  letI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card (IntermediateField.adjoin K {c}) =
      Fintype.card K ^ Module.finrank K (IntermediateField.adjoin K {c}) :=
    Module.card_eq_pow_finrank
  have hpos : 0 < Module.finrank K (IntermediateField.adjoin K {c}) := Module.finrank_pos
  have hKq : Fintype.card K = S.D.q ^ a := by rw [← Nat.card_eq_fintype_card]; exact hK
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0, pow_zero] at hKq
      have : 1 < Fintype.card K := Fintype.one_lt_card
      omega
    · exact h0
  refine ⟨a * Module.finrank K (IntermediateField.adjoin K {c}), Nat.mul_pos ha hpos, ?_⟩
  have h1 := FiniteField.pow_card
    (⟨c, IntermediateField.mem_adjoin_simple_self K c⟩ : IntermediateField.adjoin K {c})
  rw [hcard, hKq, ← pow_mul] at h1
  have h2 := congrArg (fun x : IntermediateField.adjoin K {c} => (x : L)) h1
  simpa [pow_mul] using h2

end Setup

end CFSG.HardMathSupport.Timmesfeld.LangTorus
