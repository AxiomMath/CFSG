module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthPairBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlockAnDefs
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth.ResidualEichler
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpAsmAnalysis

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Polynomial Module
open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne.KCPrimary CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.AssemblyBPredicates

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}

theorem orthPairedBlockModel_holds_dvd (hp : p.Prime)
    (x y : ↥(orthDerived Q))
    (hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V))
    (hyc : (y : V ≃ₗ[K] V) ∈ isometryCentralizer Q (x : V ≃ₗ[K] V))
    (hyp : y ^ p = 1) {h : K[X]}
    (hh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap)
    (hne : h ≠ reciprocalPolynomial h)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h))
    (J : Subgroup (ProjOrthDerived Q))
    (hJeq : J = componentImage Q (x : V ≃ₗ[K] V) h)
    (hN : piOrth Q y ∈ Subgroup.normalizer (J : Set (ProjOrthDerived Q)))
    (hd : p ∣ Nat.card J) :
    Nonempty (LinBlockModel p J (piOrth Q y) hN) ∨
      MI.indAut p J (piOrth Q y) hN ∈ inner (PSimple p J) := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hQ : (QuadraticMap.polarBilin Q).Nondegenerate :=
    CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth.res_polarBilin_nondegenerate hx
  have hDnt : Nontrivial ↥(specialBlock Q (x : V ≃ₗ[K] V) h) :=
    CFSG.LocalCores.isQuasisimple_nontrivial hq
  haveI : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    haveI : Subsingleton V := hV
    haveI : Subsingleton (V ≃ₗ[K] V) :=
      ⟨fun a b => LinearEquiv.ext fun v => Subsingleton.elim _ _⟩
    haveI : Subsingleton ↥(specialBlock Q (x : V ≃ₗ[K] V) h) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    exact (not_subsingleton_iff_nontrivial.mpr hDnt) inferInstance
  have hpi : Function.Injective (piOrth Q) := piOrth_injective hQ
  have hspecΩ : specialBlock Q (x : V ≃ₗ[K] V) h ≤ orthDerived Q :=
    specialBlock_le_orthDerived_of_perfect hq.1
      ((specialBlock_le_isometryCentralizer h).trans
        (fun _ hg => (Subgroup.mem_inf.mp hg).1))
  have hycen : (y : V ≃ₗ[K] V) ∈
      Subgroup.centralizer ({(x : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V)) := by
    rw [isometryCentralizer] at hyc
    exact (Subgroup.mem_inf.mp hyc).2
  let A := primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h
  let F := AdjoinRoot h
  have ha2 : 2 ≤ A := by
    have hpos := hx.primaryMultiplicity_pos hh
    by_contra hlt
    have h1 : A = 1 := by omega
    have hbot : specialBlock Q (x : V ≃ₗ[K] V) h = ⊥ :=
      hx.specialBlock_eq_bot_of_finrank_eq_one hh h1
    haveI : Subsingleton ↥(specialBlock Q (x : V ≃ₗ[K] V) h) := by
      rw [hbot]
      infer_instance
    obtain ⟨u, v, huv⟩ := hq.2.2
    exact huv (Subsingleton.elim (u * v) (v * u))
  let eJ := orthPairedComponentEquiv hpi hspecΩ J hJeq
  let eSL := orthPairedStatedSL hx hh hne
  obtain ⟨eJp, heJp⟩ := exists_orthPaired_pSimpleEquiv (p := p) J eJ
  have hdD : p ∣ Nat.card ↥(specialBlock Q (x : V ≃ₗ[K] V) h) := by
    rw [Nat.card_congr eJ.toEquiv]
    exact hd
  obtain ⟨eP, heP⟩ := exists_orthPaired_centerQuot (p := p) (h := h) hp hq hdD
  obtain ⟨e, he⟩ := exists_orthPaired_pairedEquiv (p := p) J eJ eSL eJp heJp eP heP
  have hyval : (y : V ≃ₗ[K] V) ^ p = 1 := by
    simpa using congrArg Subtype.val hyp
  let M := orthPairedMatrix (x := x) (h := h) (y := (y : V ≃ₗ[K] V)) hycen
  let B := M⁻¹
  have hBpow : B ^ p = 1 := by
    have hMpow : M ^ p = 1 := by
      dsimp only [M]
      exact orthPairedMatrix_pow (p := p) (h := h) hycen hyval
    dsimp only [B]
    rw [inv_pow, hMpow, inv_one]
  have hBn : B ∈ Subgroup.normalizer (StatedSL A F : Set (GL (Fin A) F)) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top B
  have hBmem : ∀ m : ↥(StatedSL A F), B * (m : GL (Fin A) F) * B⁻¹ ∈ StatedSL A F :=
    fun m => (Subgroup.mem_normalizer_iff.mp hBn (m : GL (Fin A) F)).mp m.2
  have hconjSL : ∀ (d : ↥(specialBlock Q (x : V ≃ₗ[K] V) h))
      (hd' : (y : V ≃ₗ[K] V)⁻¹ * d.1 * (y : V ≃ₗ[K] V) ∈
        specialBlock Q (x : V ≃ₗ[K] V) h),
      eSL ⟨(y : V ≃ₗ[K] V)⁻¹ * d.1 * (y : V ≃ₗ[K] V), hd'⟩ =
        (⟨B * (eSL d : GL (Fin A) F) * B⁻¹, hBmem (eSL d)⟩ : StatedSL A F) := by
    intro d hd'
    apply Subtype.ext
    have h := orthPairedStatedSL_conj (p := p) hx hh hne hycen hd'
    rw [h]
    dsimp only [eSL, B, M]
    rfl
  have hconj : MulAut.congr e (MI.indAut p J (piOrth Q y) hN) =
      CFSG.StandardType.TableB.projConj (StatedSL A F) ⟨B, hBn⟩ := by
    ext z
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective
      ((LargeEvenScalars (Fin A) F).subgroupOf (StatedSL A F)) z
    exact orthPaired_equiv hpi hspecΩ J hJeq y hN hyc e eSL he B hBn hconjSL m
  by_cases hsmall : (A = 2 ∧ Nat.card F = 4) ∨ (A = 2 ∧ Nat.card F = 2) ∨
      (A = 3 ∧ Nat.card F = 2) ∨ (A = 4 ∧ Nat.card F = 2)
  · exact Or.inr (orthPaired_small_inner e B hBn hconj hsmall)
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP F 2 := by
      change CharP (AdjoinRoot h) 2
      exact charP_of_injective_algebraMap (algebraMap K (AdjoinRoot h)).injective 2
    haveI : Fintype F := Fintype.ofFinite F
    obtain ⟨k, -, hk⟩ := FiniteField.card F 2
    set k' : ℕ := (k : ℕ) with hk'
    have hcard : Nat.card F = 2 ^ k' := by
      rw [Nat.card_eq_fintype_card, hk]
    have hcharF : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have hnotSmall : A = 2 → 3 ≤ k' := by
      intro hA
      by_contra hk3
      have hk2 : k' ≤ 2 := by omega
      rcases (by omega : k' = 0 ∨ k' = 1 ∨ k' = 2) with h0 | h1 | h2
      · rw [h0, pow_zero] at hcard
        have := Finite.one_lt_card (α := F)
        omega
      · rw [h1] at hcard
        exact hsmall (Or.inr (Or.inl ⟨hA, by rw [hcard]; norm_num⟩))
      · rw [h2] at hcard
        exact hsmall (Or.inl ⟨hA, by rw [hcard]; norm_num⟩)
    have h3 : A = 3 → 2 ≤ k' := by
      intro hA
      by_contra hk2
      have hk1 : k' ≤ 1 := by omega
      rcases (by omega : k' = 0 ∨ k' = 1) with h0 | h1
      · rw [h0, pow_zero] at hcard
        have := Finite.one_lt_card (α := F)
        omega
      · rw [h1] at hcard
        exact hsmall (Or.inr (Or.inr (Or.inl ⟨hA, by rw [hcard]; norm_num⟩)))
    have h4 : A = 4 → 2 ≤ k' := by
      intro hA
      by_contra hk2
      have hk1 : k' ≤ 1 := by omega
      rcases (by omega : k' = 0 ∨ k' = 1) with h0 | h1
      · rw [h0, pow_zero] at hcard
        have := Finite.one_lt_card (α := F)
        omega
      · rw [h1] at hcard
        exact hsmall (Or.inr (Or.inr (Or.inr ⟨hA, by rw [hcard]; norm_num⟩)))
    refine Or.inl ⟨{
      a := A
      E := F
      fieldE := inferInstance
      finiteE := inferInstance
      charE := hcharF
      two_le := ha2
      k := k'
      cardE := hcard
      notSmall := hnotSmall
      h3 := h3
      h4 := h4
      B := B
      hBn := hBn
      Bpow := hBpow
      e := e
      equiv := fun m => orthPaired_equiv hpi hspecΩ J hJeq y hN hyc e eSL he B hBn hconjSL m }⟩

theorem orthPairedBlockModel_holds : OrthPairedBlockModelResidual := by
  intro K V _ _ _ _ _ _ Q p hp hp2 x y hx hyc hyp h hh hne1 hne hq J hJeq hN
  classical
  by_cases hd : p ∣ Nat.card J
  · exact orthPairedBlockModel_holds_dvd (Q := Q)
      hp x y hx hyc hyp hh hne hq J hJeq hN hd
  · haveI := subsingleton_pSimple_of_not_dvd hp hd
    exact Or.inr (mem_inner_of_subsingleton _)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
