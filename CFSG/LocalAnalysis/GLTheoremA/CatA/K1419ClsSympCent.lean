module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SemisimpleCentralizers.HeldUCDTransfer
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartOne.KC.OrthogonalCentralizerBlocks
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicFixed
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Open.StatedAPI Matrix
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LieType.SemisimpleCentralizers.Held (heldGU)

open Polynomial

open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal
private theorem spSupported_singleton_eq_bot_of_not_mem {r : ℕ} {K : Type} [Field K]
    {x : StatedSp r K} (hsq : Squarefree (minpoly K (spEnd x))) {h : K[X]}
    (hh : h ∉ primaryFactors (spEnd x)) : spSupported x {h} = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  apply spLin_injective
  apply Units.ext
  rw [map_one]
  change spEnd g = 1
  refine ext_primaryComponent hsq (f := spEnd g) (g := 1) ?_
  intro k hk v hv
  rw [Module.End.one_apply]
  exact (mem_spSupported.mp hg).2 k hk (by
    rw [Set.mem_singleton_iff]
    intro hkh
    exact hh (hkh ▸ hk)) v hv

private noncomputable def glMapEquivOfAlgEquiv {K : Type} [Field K] {R S : Type}
    [Ring R] [Ring S] [Algebra K R] [Algebra K S] (e : R ≃ₐ[K] S) (r : ℕ) :
    GL (Fin r) R ≃* GL (Fin r) S :=
  Units.mapEquiv e.mapMatrix.toMulEquiv

private noncomputable def adjoinRootAlgEquivOfNatDegreeOne {K : Type} [Field K] {h : K[X]}
    (hmon : h.Monic) (hdeg : h.natDegree = 1) : AdjoinRoot h ≃ₐ[K] K := by
  have hdeg' : h.degree = 1 :=
    (Polynomial.degree_eq_iff_natDegree_eq_of_pos (by norm_num)).2 hdeg
  haveI : Fact (Irreducible h) := ⟨hmon.irreducible_of_degree_eq_one hdeg'⟩
  have hform : h = X + C (h.coeff 0) := hmon.eq_X_add_C hdeg
  let F : AdjoinRoot h →ₐ[K] K :=
    AdjoinRoot.liftAlgHom h (Algebra.ofId K K) (-h.coeff 0) (by
      rw [hform, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C]
      simp)
  refine AlgEquiv.ofBijective F ⟨RingHom.injective F.toRingHom, ?_⟩
  have hfin : Module.finrank K (AdjoinRoot h) = 1 := by
    rw [CFSG.RankThree.PartOne.KCUnitary.finrank_adjoinRoot, hdeg]
  have hrange : LinearMap.range F.toLinearMap = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [LinearMap.finrank_range_of_inj (RingHom.injective F.toRingHom), hfin,
      Module.finrank_self]
  exact LinearMap.range_eq_top.mp hrange


private theorem reciprocalPolynomial_X_add_C_aux {K : Type} [Field K] {c : K} (hc : c ≠ 0) :
    reciprocalPolynomial (Polynomial.X + Polynomial.C c : K[X]) =
      Polynomial.X + Polynomial.C c⁻¹ := by
  have h0 : (Polynomial.X + Polynomial.C c : K[X]).coeff 0 = c := by simp
  have hX : (Polynomial.X : K[X]).reverse = 1 := by
    have := Polynomial.reverse_mul_X (1 : K[X])
    rw [one_mul] at this
    rw [this, show (1 : K[X]) = Polynomial.C 1 from Polynomial.C_1.symm, Polynomial.reverse_C]
  have h1 : (Polynomial.X + Polynomial.C c : K[X]).reverse = 1 + Polynomial.C c * Polynomial.X := by
    rw [Polynomial.reverse_add_C, hX, Polynomial.natDegree_X, pow_one]
  unfold reciprocalPolynomial
  rw [h0, h1, mul_add, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hc, Polynomial.C_1,
    one_mul, mul_one]
  ring

private theorem dvd_cyclotomic_three_of_mem {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {y : Module.End K V} (hy : y ^ 3 = 1)
    {h : K[X]} (hh : h ∈ primaryFactors y) (hne : h ≠ Polynomial.X - 1) :
    h ∣ (Polynomial.X ^ 2 + Polynomial.X + 1 : K[X]) := by
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := monic_of_mem_primaryFactors hh
  have hdvd : h ∣ (Polynomial.X ^ 3 - 1 : K[X]) :=
    ((mem_primaryFactors.mp hh).2.2).trans (minpoly.dvd K y (by
      rw [map_sub, map_pow, Polynomial.aeval_X, map_one, hy, sub_self]))
  have hfac : (Polynomial.X ^ 3 - 1 : K[X]) =
      (Polynomial.X - 1) * (Polynomial.X ^ 2 + Polynomial.X + 1) := by ring
  rw [hfac] at hdvd
  rcases hirr.prime.dvd_or_dvd hdvd with h1 | h2
  · exact absurd (eq_of_monic_of_associated hmon
      CFSG.RankThree.PartOne.KCOrthogonal.monic_X_sub_one
      (hirr.associated_of_dvd
        CFSG.RankThree.PartOne.KCOrthogonal.irreducible_X_sub_one h1)) hne
  · exact h2

private theorem eq_or_eq_reciprocal_of_pow_three {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {y : Module.End K V} (hy : y ^ 3 = 1)
    {a b : K[X]} (ha : a ∈ primaryFactors y) (hb : b ∈ primaryFactors y)
    (ha1 : a ≠ Polynomial.X - 1) (hb1 : b ≠ Polynomial.X - 1) :
    b = a ∨ b = reciprocalPolynomial a := by
  by_cases hba : b = a
  · exact Or.inl hba
  right
  have hairr := irreducible_of_mem_primaryFactors ha
  have hbirr := irreducible_of_mem_primaryFactors hb
  have hamon := monic_of_mem_primaryFactors ha
  have hbmon := monic_of_mem_primaryFactors hb
  have haΦ := dvd_cyclotomic_three_of_mem hy ha ha1
  have hbΦ := dvd_cyclotomic_three_of_mem hy hb hb1
  have hΦdeg : (Polynomial.X ^ 2 + Polynomial.X + 1 : K[X]).natDegree = 2 := by
    compute_degree!
  have hΦmon : (Polynomial.X ^ 2 + Polynomial.X + 1 : K[X]).Monic := by monicity!
  have hcop : IsCoprime a b := isCoprime_of_mem_primaryFactors ha hb (Ne.symm hba)
  have habΦ : a * b ∣ (Polynomial.X ^ 2 + Polynomial.X + 1 : K[X]) := hcop.mul_dvd haΦ hbΦ
  have hapos : 0 < a.natDegree :=
    natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hairr)
  have hbpos : 0 < b.natDegree :=
    natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hbirr)
  have hmul : (a * b).natDegree = a.natDegree + b.natDegree := Monic.natDegree_mul hamon hbmon
  have hle : (a * b).natDegree ≤ 2 := by
    have := natDegree_le_of_dvd habΦ hΦmon.ne_zero
    omega
  have hda : a.natDegree = 1 := by omega
  have hdb : b.natDegree = 1 := by omega
  have hab : a * b = Polynomial.X ^ 2 + Polynomial.X + 1 :=
    (eq_of_monic_of_dvd_of_natDegree_le (hamon.mul hbmon) hΦmon habΦ (by omega)).symm
  have hform_a : a = Polynomial.X + Polynomial.C (a.coeff 0) := hamon.eq_X_add_C hda
  have hform_b : b = Polynomial.X + Polynomial.C (b.coeff 0) := hbmon.eq_X_add_C hdb
  have h00 : a.coeff 0 * b.coeff 0 = 1 := by
    have := congrArg (fun p : K[X] => p.coeff 0) hab
    simpa [Polynomial.mul_coeff_zero] using this
  have ha0 : a.coeff 0 ≠ 0 := fun h => by simp [h] at h00
  have hb0 : b.coeff 0 = (a.coeff 0)⁻¹ := eq_inv_of_mul_eq_one_right h00
  conv_rhs => rw [hform_a, reciprocalPolynomial_X_add_C_aux ha0]
  rw [hform_b, hb0]

private theorem reciprocalPolynomial_X_sub_one_aux {K : Type} [Field K] :
    reciprocalPolynomial (Polynomial.X - 1 : K[X]) = Polynomial.X - 1 := by
  have h := reciprocalPolynomial_X_add_C_aux (K := K) (c := -1) (by norm_num)
  simpa [sub_eq_add_neg] using h

private theorem exists_nontrivial_primaryFactor {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Nontrivial V] {y : Module.End K V}
    (h3 : (3 : K) ≠ 0) (hy : y ^ 3 = 1) (hy1 : y ≠ 1) :
    ∃ h ∈ primaryFactors y, h ≠ Polynomial.X - 1 := by
  classical
  have hsqp : Squarefree (Polynomial.X ^ 3 - 1 : K[X]) := by
    have := Polynomial.separable_X_pow_sub_C (1 : K) h3 one_ne_zero
    simpa using this.squarefree
  have hsq : Squarefree (minpoly K y) :=
    squarefree_minpoly_of_aeval_eq_zero hsqp (by
      rw [map_sub, map_pow, Polynomial.aeval_X, map_one, hy, sub_self])
  have hne : minpoly K y ≠ 1 := by
    intro h1
    have hint : IsIntegral K y := Algebra.IsIntegral.isIntegral y
    have hpos := minpoly.natDegree_pos hint
    rw [h1] at hpos
    simp at hpos
  have hnonempty : (primaryFactors y).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hprod := prod_primaryFactors (x := y) hsq
    rw [hempty, Finset.prod_empty] at hprod
    exact hne hprod.symm
  by_contra hcon
  push Not at hcon
  have hS : primaryFactors y = {Polynomial.X - 1} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun b hb => hcon b hb⟩
    obtain ⟨h, hh⟩ := hnonempty
    rw [hcon h hh] at hh
    exact hh
  have hprod := prod_primaryFactors (x := y) hsq
  rw [hS, Finset.prod_singleton] at hprod
  have hy1' : y = 1 := by
    have haeval := minpoly.aeval K y
    rw [← hprod] at haeval
    have h2 : y - 1 = 0 := by simpa using haeval
    exact sub_eq_zero.mp h2
  exact hy1 hy1'


theorem k1419ClsSympCent {K : Type} [Field K] [Finite K] {n m : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (x : StatedSp m K) (hx : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ A₁ A₂ : Subgroup (StatedSp m K),
      (∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) ∧
      A₁ ⊔ A₂ = Subgroup.centralizer ({x} : Set (StatedSp m K)) ∧ x ∈ A₂ ∧
      (∃ s : ℕ, Nonempty (A₁ ≃* StatedSp s K)) ∧
      ((∃ r : ℕ, 1 ≤ r ∧ Nonempty (A₂ ≃* GL (Fin r) K)) ∨
        ∃ (r : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ : E ≃+* E)
          (hτ : ∀ y, τ (τ y) = y), 1 ≤ r ∧ Nat.card E = Nat.card K ^ 2 ∧
          (∀ y, τ y = y ^ Nat.card K) ∧ Nonempty (A₂ ≃* heldGU r E τ hτ)) := by
  classical
  have hchar : CharP K 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := n) (by rw [Fintype.card_eq_nat_card, hK])
  haveI := hchar
  have h3 : (3 : K) ≠ 0 := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have h31 : (3 : K) = 1 := by
      rw [show (3 : K) = 2 + 1 by norm_num, h2, zero_add]
    rw [h31]; exact one_ne_zero
  haveI : NeZero m := ⟨by omega⟩
  have hinj : Function.Injective (proj m K) :=
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
      (r := m) (K := K)).1
  have hordx : orderOf x = 3 := orderOf_eq_prime hx hx1
  have hpa3 : orderOf (proj m K x) = 3 := by
    have hpa : (proj m K x) ^ 3 = 1 := by rw [← map_pow, hx, map_one]
    have hpa1 : proj m K x ≠ 1 := fun h => hx1 (hinj (by rw [h, map_one]))
    exact orderOf_eq_prime hpa hpa1
  have hmain := symplectic_cross_prime_primary_centralizer_blocks (ℓ := 2) (f := n) (p := 3)
    (K := K) (r := m) Nat.prime_two hn hK Nat.prime_three (by norm_num) (by norm_num) hm
    (proj m K x) hpa3
  have hblocks : SpPrimaryBlocks 2 n 3 x (proj m K x) := hmain.2 x rfl hordx
  have hsq : Squarefree (minpoly K (spEnd x)) :=
    (altPrimaryData_spLin (K := K) (r := m) (p := 3) h3 hx).squarefree
  have hspEnd_ne : spEnd x ≠ 1 := by
    intro h
    apply hx1
    apply spLin_injective
    rw [map_one]
    apply Units.ext
    rw [Units.val_one]
    exact h
  obtain ⟨h₀, hh₀, hh₀1⟩ := exists_nontrivial_primaryFactor (K := K)
    (V := Fin m ⊕ Fin m → K) h3 (spEnd_pow hx) hspEnd_ne
  haveI : Fact (Irreducible h₀) := ⟨irreducible_of_mem_primaryFactors hh₀⟩
  have hcoeff : h₀.coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨g, hg⟩ := dvd_cyclotomic_three_of_mem (spEnd_pow hx) hh₀ hh₀1
    have := congrArg (fun p : K[X] => p.coeff 0) hg
    simp [h0, Polynomial.mul_coeff_zero] at this
  have hrec : reciprocalPolynomial (reciprocalPolynomial h₀) = h₀ :=
    reciprocalPolynomial_reciprocalPolynomial (monic_of_mem_primaryFactors hh₀) hcoeff
  have hpos_mult : 1 ≤ primaryMultiplicity (spEnd x) h₀ := by
    show 1 ≤ Module.finrank (AdjoinRoot h₀) ↥(primaryComponent (spEnd x) h₀)
    haveI : Nontrivial ↥(primaryComponent (spEnd x) h₀) :=
      Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hh₀)
    exact Module.finrank_pos
  let O₂ : Set K[X] := {h₀, reciprocalPolynomial h₀}
  have hO₂mem : O₂ ∈ reciprocalOrbits (spEnd x) := ⟨h₀, hh₀, rfl⟩
  let A₁ : Subgroup (StatedSp m K) := spSupported x {X - 1}
  let A₂ : Subgroup (StatedSp m K) := spSupported x O₂
  have hpair_eq : ∀ k ∈ primaryFactors (spEnd x), k ≠ X - 1 →
      ({k, reciprocalPolynomial k} : Set K[X]) = O₂ := by
    intro k hk hk1
    rcases eq_or_eq_reciprocal_of_pow_three (spEnd_pow hx) hh₀ hk hh₀1 hk1 with hk0 | hk0
    · rw [hk0]
    · rw [hk0, hrec, Set.pair_comm]
  have hsup : (⨆ O : reciprocalOrbits (spEnd x), spSupported x (O : Set K[X])) = A₁ ⊔ A₂ := by
    apply le_antisymm
    · refine iSup_le fun O => ?_
      obtain ⟨k, hk, hO⟩ := O.2
      rw [← hO]
      change spSupported x ({k, reciprocalPolynomial k} : Set K[X]) ≤ A₁ ⊔ A₂
      by_cases hk1 : k = X - 1
      · rw [show ({k, reciprocalPolynomial k} : Set K[X]) = {X - 1} from by
          rw [hk1, reciprocalPolynomial_X_sub_one_aux, Set.pair_eq_singleton]]
        exact le_sup_left
      · rw [hpair_eq k hk hk1]
        exact le_sup_right
    · apply sup_le
      · by_cases h1 : X - 1 ∈ primaryFactors (spEnd x)
        · exact le_iSup (fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set K[X]))
            ⟨{X - 1}, ⟨X - 1, h1, by
          show ({X - 1, reciprocalPolynomial (X - 1)} : Set K[X]) = {X - 1}
          rw [reciprocalPolynomial_X_sub_one_aux]
          exact Set.pair_eq_singleton _⟩⟩
        · rw [show A₁ = ⊥ from spSupported_singleton_eq_bot_of_not_mem hsq h1]
          exact bot_le
      · exact le_iSup (fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set K[X]))
          ⟨O₂, hO₂mem⟩
  have hcent : A₁ ⊔ A₂ = Subgroup.centralizer ({x} : Set (StatedSp m K)) :=
    hsup.symm.trans hblocks.directProduct.2.2
  have hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a := by
    by_cases h1 : X - 1 ∈ primaryFactors (spEnd x)
    · have hO₁ : ({X - 1} : Set K[X]) ∈ reciprocalOrbits (spEnd x) :=
        ⟨X - 1, h1, by
          show ({X - 1, reciprocalPolynomial (X - 1)} : Set K[X]) = {X - 1}
          rw [reciprocalPolynomial_X_sub_one_aux]
          exact Set.pair_eq_singleton _⟩
      have hne : ({X - 1} : Set K[X]) ≠ O₂ := by
        intro h
        have : h₀ ∈ ({X - 1} : Set K[X]) := by
          rw [h]; exact Or.inl rfl
        exact hh₀1 (by simpa using this)
      intro a ha b hb
      exact (hblocks.directProduct.1 {X - 1} hO₁ O₂ hO₂mem hne a ha b hb).eq
    · have hbot := spSupported_singleton_eq_bot_of_not_mem hsq h1
      intro a ha b hb
      rw [show A₁ = ⊥ from hbot, Subgroup.mem_bot] at ha
      rw [ha, one_mul, mul_one]
  have hxmem : x ∈ A₂ := by
    rw [show A₂ = spSupported x O₂ from rfl, mem_spSupported]
    refine ⟨rfl, ?_⟩
    intro k hk hkO v hv
    have hk1 : k = X - 1 := by
      by_contra hk1
      exact hkO (by rw [← hpair_eq k hk hk1]; exact Or.inl rfl)
    rw [hk1] at hv
    rw [hblocks.fixed_eq] at hv
    exact sub_eq_zero.mp (LinearMap.mem_ker.mp hv)
  refine ⟨A₁, A₂, hcomm, hcent, hxmem, ?_, ?_⟩
  ·
    by_cases h1 : X - 1 ∈ primaryFactors (spEnd x)
    · obtain ⟨φ, -⟩ := hblocks.fixedFactor h1
      have hB : ((spForm m K).restrict (primaryComponent (spEnd x) (X - 1))).IsAlt :=
        fun v => spForm_isAlt (v : Fin m ⊕ Fin m → K)
      obtain ⟨s, -, ⟨e⟩⟩ :=
        CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp
          hB hblocks.fixed_nondegenerate
      exact ⟨s, ⟨φ.trans e⟩⟩
    · have hbot := spSupported_singleton_eq_bot_of_not_mem hsq h1
      refine ⟨0, ?_⟩
      rw [show A₁ = ⊥ from hbot]
      exact ⟨MulEquiv.ofBijective (1 : (⊥ : Subgroup (StatedSp m K)) →* StatedSp 0 K)
        ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨1, Subsingleton.elim _ _⟩⟩⟩
  · by_cases hself : reciprocalPolynomial h₀ = h₀
    ·
      right
      obtain ⟨d, hd, hpd, σ, hσpow, hσne, hσσ, hσroot, hHf1, hE, hEbar,
        Hf, hHfsym, hHfsep, htrace, he, φ, hφ⟩ :=
        (hblocks.selfDual ⟨h₀, hh₀⟩ hh₀1 hself).exists_half
      have hle : h₀.natDegree ≤ 2 := by
        have hΦmon : (X ^ 2 + X + 1 : K[X]).Monic := by monicity!
        have hΦdeg : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
        have h := natDegree_le_of_dvd
          (dvd_cyclotomic_three_of_mem (spEnd_pow hx) hh₀ hh₀1) hΦmon.ne_zero
        rwa [hΦdeg] at h
      have hpos : 0 < h₀.natDegree :=
        natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible
          (irreducible_of_mem_primaryFactors hh₀))
      have hd1 : d = 1 := by
        set f := h₀.natDegree with hf
        have hf_eq : f = 2 * d := by rw [hf]; exact hd
        have hf_le : f ≤ 2 := by rw [hf]; exact hle
        have hf_pos : 0 < f := by rw [hf]; exact hpos
        omega
      let τ : AdjoinRoot h₀ ≃+* AdjoinRoot h₀ :=
        RingEquiv.ofBijective hE.bar (Function.Involutive.bijective hE.bar_bar)
      have hτ : ∀ y, τ (τ y) = y := fun y => hE.bar_bar y
      have hcardE : Nat.card (AdjoinRoot h₀) = Nat.card K ^ 2 := by
        rw [hE.card, hd1, Nat.mul_one, hK, show 2 * n = n * 2 by ring, pow_mul]
      have hpow : ∀ y, τ y = y ^ Nat.card K := by
        intro y
        change hE.bar y = y ^ Nat.card K
        rw [hEbar, hσpow, hd1, pow_one, hK]
      have hO₂eq : O₂ = {h₀} := by
        show ({h₀, reciprocalPolynomial h₀} : Set K[X]) = {h₀}
        rw [hself, Set.pair_eq_singleton]
      have hA₂eq : A₂ = spSupported x {h₀} := by
        show spSupported x O₂ = spSupported x {h₀}
        rw [hO₂eq]
      obtain ⟨e, he⟩ := he
      have hgu : Nonempty (CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup Hf ≃*
          heldGU (primaryMultiplicity (spEnd x) h₀) (AdjoinRoot h₀) τ hτ) :=
        CFSG.LieType.SemisimpleCentralizers.HeldUCD.nonempty_mulEquiv_heldGU τ hτ Hf e he
      have eφ : A₂ ≃* CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup Hf := by
        rw [hA₂eq]
        exact φ
      refine ⟨primaryMultiplicity (spEnd x) h₀, AdjoinRoot h₀, inferInstance, hE.finite,
        τ, hτ, hpos_mult, hcardE, hpow, ?_⟩
      exact ⟨eφ.trans hgu.some⟩
    ·
      left
      have hpair : reciprocalPolynomial h₀ ≠ h₀ := hself
      obtain ⟨φpair⟩ := (hblocks.paired ⟨h₀, hh₀⟩ (Ne.symm hpair)).matrixFactor
      have hle : h₀.natDegree ≤ 2 := by
        have hΦmon : (X ^ 2 + X + 1 : K[X]).Monic := by monicity!
        have hΦdeg : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
        have h := natDegree_le_of_dvd
          (dvd_cyclotomic_three_of_mem (spEnd_pow hx) hh₀ hh₀1) hΦmon.ne_zero
        rwa [hΦdeg] at h
      have hmem_rec : reciprocalPolynomial h₀ ∈ primaryFactors (spEnd x) :=
        hblocks.bijOn.1 hh₀
      have hmem_rec_ne : reciprocalPolynomial h₀ ≠ X - 1 := by
        intro h
        exact hh₀1 (by rw [← hrec, h, reciprocalPolynomial_X_sub_one_aux])
      have hΦ1 := dvd_cyclotomic_three_of_mem (spEnd_pow hx) hh₀ hh₀1
      have hΦ2 := dvd_cyclotomic_three_of_mem (spEnd_pow hx) hmem_rec hmem_rec_ne
      have hcop : IsCoprime h₀ (reciprocalPolynomial h₀) :=
        isCoprime_of_mem_primaryFactors hh₀ hmem_rec (Ne.symm hpair)
      have hdeg : h₀.natDegree = 1 := by
        have hΦmon : (X ^ 2 + X + 1 : K[X]).Monic := by monicity!
        have hΦdeg : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
        have hleprod : (h₀ * reciprocalPolynomial h₀).natDegree ≤ 2 := by
          have h := natDegree_le_of_dvd (hcop.mul_dvd hΦ1 hΦ2) hΦmon.ne_zero
          rwa [hΦdeg] at h
        have hdegrec := natDegree_reciprocalPolynomial hcoeff
        have hmul := Monic.natDegree_mul (monic_of_mem_primaryFactors hh₀)
          (monic_reciprocalPolynomial hcoeff)
        have hpos : 0 < h₀.natDegree :=
          natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible
            (irreducible_of_mem_primaryFactors hh₀))
        set g := h₀.natDegree with hg
        have hle' : 2 * g ≤ 2 := by
          rw [hmul, hdegrec] at hleprod
          omega
        omega
      have e : AdjoinRoot h₀ ≃ₐ[K] K :=
        adjoinRootAlgEquivOfNatDegreeOne (monic_of_mem_primaryFactors hh₀) hdeg
      refine ⟨primaryMultiplicity (spEnd x) h₀,
        hpos_mult, ?_⟩
      have hA₂' : A₂ = spSupported x
          ({↑(⟨h₀, hh₀⟩ : primaryFactors (spEnd x)),
            reciprocalPolynomial ↑(⟨h₀, hh₀⟩ : primaryFactors (spEnd x))} : Set K[X]) := rfl
      have eφ : A₂ ≃* GL (Fin (primaryMultiplicity (spEnd x) h₀)) (AdjoinRoot h₀) := by
        rw [hA₂']
        exact φpair
      exact ⟨eφ.trans (glMapEquivOfAlgEquiv e _)⟩


end CFSG.LocalAnalysis.GLTheoremA.K1419
