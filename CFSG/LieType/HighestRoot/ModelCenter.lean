module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieModelDefs
public import CFSG.ClassicalInvolution.ModelFacts.Models
public import CFSG.ClassicalInvolution.Q3.ModelCenterExceptional
public import CFSG.ClassicalInvolution.Q3.ModelCenterTriality

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3 CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Exceptional CFSG.LieType.TitsSimplicity
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.Blueprint.Chevalley

@[expose] def CenterPPrime (K : Type*) [Group K] (p : ℕ) : Prop :=
  ∀ z ∈ Subgroup.center K, z ^ p = 1 → z = 1

theorem CenterPPrime.of_mulEquiv {K K' : Type*} [Group K] [Group K'] {p : ℕ} (e : K ≃* K')
    (h : CenterPPrime K' p) : CenterPPrime K p := by
  intro z hz hzp
  have hz' : e z ∈ Subgroup.center K' := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hz x]
  apply e.injective
  rw [map_one]
  exact h _ hz' (by rw [← map_pow, hzp, map_one])

theorem centerPPrime_of_eq
    {t : StatedLieTag} {n p f : ℕ} {hp : p.Prime} {U : LieUniversal}
    (h : modelUniv t n p f hp = U) (hU : CenterPPrime U.K p) :
    CenterPPrime (modelUniv t n p f hp).K p := by
  subst h
  exact hU

section Field

variable {p : ℕ} [Fact p.Prime]

theorem eq_one_of_pow_eq_one_of_charP {F : Type*} [Field F] [CharP F p] {c : F}
    (h : c ^ p = 1) : c = 1 :=
  frobenius_inj F p (by rw [frobenius_def, frobenius_def, h, one_pow])

theorem eq_one_of_mem_statedScalars {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    [CharP F p] {g : GL ι F} (hg : g ∈ StatedScalars ι F) (hgp : g ^ p = 1) : g = 1 := by
  obtain ⟨u, rfl⟩ := hg
  rcases isEmpty_or_nonempty ι with hι | hι
  · ext a
    exact isEmptyElim a
  · obtain ⟨i⟩ := hι
    have h1 : Matrix.GeneralLinearGroup.scalar ι (u ^ p) = 1 := by rw [map_pow, hgp]
    have h2 : ((u ^ p : Fˣ) : F) = 1 := by
      have := congrArg (fun g : GL ι F => (g : Matrix ι ι F) i i) h1
      simpa [Matrix.diagonal_pow] using this
    have hu : u = 1 := Units.ext (eq_one_of_pow_eq_one_of_charP (by
      rw [← Units.val_pow_eq_pow_val]
      exact h2))
    rw [hu, map_one]

theorem centerPPrime_specialLinear (m : ℕ) (F : Type) [Field F] [CharP F p] :
    CenterPPrime (Matrix.SpecialLinearGroup (Fin (m + 1)) F) p := by
  intro z hz hzp
  obtain ⟨r, -, hz'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have h1 : (Matrix.scalar (Fin (m + 1)) r) ^ p = 1 := by
    rw [hz', ← Matrix.SpecialLinearGroup.coe_pow, hzp, Matrix.SpecialLinearGroup.coe_one]
  have h2 : r ^ p = 1 := by
    have := congrFun (congrFun h1 0) 0
    rw [← map_pow] at this
    simpa using this
  apply Subtype.ext
  rw [← hz', eq_one_of_pow_eq_one_of_charP h2, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem centerPPrime_statedSp (n : ℕ) (F : Type) [Field F] [CharP F p] :
    CenterPPrime (StatedSp n F) p := by
  intro z hz hzp
  rw [Symplectic.center_eq n F] at hz
  exact Subtype.ext (eq_one_of_mem_statedScalars (Subgroup.mem_subgroupOf.mp hz)
    (by rw [← Subgroup.coe_pow, hzp, Subgroup.coe_one]))

theorem centerPPrime_unitary {F : Type} [Field F] [Finite F] {f n : ℕ} [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hn : 3 ≤ n) (hnq : (n, p ^ f) ≠ (3, 2)) :
    CenterPPrime (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F p f) n) p := by
  refine CenterPPrime.of_mulEquiv (Unitary.equivStatedSU hF n) ?_
  intro z hz hzp
  rw [(Unitary.isQuasisimple_statedSU_of_card hF hn hnq).2] at hz
  exact Subtype.ext (eq_one_of_mem_statedScalars (Subgroup.mem_subgroupOf.mp hz)
    (by rw [← Subgroup.coe_pow, hzp, Subgroup.coe_one]))

theorem centerPPrime_spin {σ : Type} [Fintype σ] [DecidableEq σ] {K : Type} [Field K] [CharP K p]
    (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0) (Q : QuadraticForm K (σ → K))
    (hcen : Subgroup.center (spinGroup Q) ≤ (StatedScalars σ K).comap (spinMatrix Q))
    (hker : ∀ x : spinGroup Q, x ∈ (spinMatrix Q).ker ↔
      x = 1 ∨ (x : CliffordAlgebra Q) = -1) : CenterPPrime (spinGroup Q) p := by
  intro z hz hzp
  have h1 : spinMatrix Q z = 1 := eq_one_of_mem_statedScalars (Subgroup.mem_comap.mp (hcen hz))
    (by rw [← map_pow, hzp, map_one])
  rcases (hker z).1 h1 with h | h
  · exact h
  · exfalso
    have h3 : ((z ^ p : spinGroup Q) : CliffordAlgebra Q) = (-1) ^ p := by
      rw [SubmonoidClass.coe_pow, h]
    rw [hzp, Odd.neg_one_pow ((Fact.out : p.Prime).odd_of_ne_two hp2)] at h3
    have h4 : algebraMap K (CliffordAlgebra Q) 2 = algebraMap K (CliffordAlgebra Q) 0 := by
      rw [map_ofNat, map_zero, ← one_add_one_eq_two]
      nth_rewrite 2 [show (1 : CliffordAlgebra Q) = -1 from h3]
      exact add_neg_cancel 1
    exact h2 (algebraMap_injective' Q h4)

theorem centerPPrime_spinOdd {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F p] (hn : 3 ≤ n)
    (hp2 : p ≠ 2) (h2 : (2 : F) ≠ 0) : CenterPPrime (spinGroup (quadOdd n F)) p := by
  refine centerPPrime_spin hp2 h2 _ ?_ (mem_ker_spinMatrix_quadOdd_iff h2)
  rw [← (spinToStatedProj_quadOdd h2 hn).2.1, (spinToStatedProj_quadOdd h2 hn).2.2]

theorem centerPPrime_spinPlus {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F p] (hn : 3 ≤ n)
    (hp2 : p ≠ 2) (h2 : (2 : F) ≠ 0) : CenterPPrime (spinGroup (quadPlus n F)) p := by
  refine centerPPrime_spin hp2 h2 _ ?_ mem_ker_spinMatrix_quadPlus_iff
  rw [← (spinToStatedProj_quadPlus (K := F) hn).2.1, (spinToStatedProj_quadPlus (K := F) hn).2.2]

theorem centerPPrime_spinMinus {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F p] {b c : F}
    (hn : 4 ≤ n) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hp2 : p ≠ 2) (h2 : (2 : F) ≠ 0) :
    CenterPPrime (spinGroup (quadMinus n F b c)) p := by
  refine centerPPrime_spin hp2 h2 _ ?_ (mem_ker_spinMatrix_quadMinus_iff hirr)
  rw [← (spinToStatedProj_quadMinus hn hirr).2.1, (spinToStatedProj_quadMinus hn hirr).2.2]

omit [Fact p.Prime] in
theorem centerPPrime_adjoint
    (τ : Tag) (F : Type) [Field F] [Finite F] :
    CenterPPrime (↥(adjointGroup τ F)) p := by
  intro z hz _
  rwa [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, Subgroup.mem_bot] at hz

theorem eq_one_of_mem_iSup_torus_of_pow
    {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type)
    [Field k] [CharP k p] {g : hV.minGroup k} (hg : g ∈ ⨆ i, hV.torus k i) (hgp : g ^ p = 1) :
    g = 1 := by
  obtain ⟨μ, hμ⟩ := hV.exists_diagOp_of_mem_iSup_torus k hg
  have hμp : μ ^ p = 1 := by
    apply diagOp_injective
    rw [← diagOp_pow, ← hμ, ← endo_pow, hgp, hV.endo_one, diagOp_one]
  have hμ1 : μ = 1 := by
    funext a
    exact eq_one_of_pow_eq_one_of_charP (by simpa using congrFun hμp a)
  apply hV.endo_injective k
  rw [hμ, hμ1, diagOp_one, hV.endo_one]

theorem centerPPrime_minuscule
    {τ : Tag} {D : MinData τ} (hV : D.Valid)
    (hA : TauCeti.IsFiniteType τ.cartan) (k : Type) [Field k] [CharP k p]
    (hct : IsCTGroupDatum (coxeterMatrix (hV.minDatum hA k).isFiniteType).toCoxeterSystem
      (weylAction (hV.minDatum hA k).isFiniteType) (hV.minDatum hA k).roots
      (hV.minDatum hA k).rootGroup (hV.nm k) (hV.torus k))
    (hext : SteinbergExtras (hV.minDatum hA k) (hV.nm k) (hV.torus k))
    (hBU : BruhatExtras (hV.minDatum hA k) (hV.torus k)) :
    CenterPPrime (hV.minGroup k) p := by
  intro z hz hzp
  have h1 := (center_eq_normalCore_borel hct hext hBU) ▸ hz
  exact eq_one_of_mem_iSup_torus_of_pow hV k (normalCore_borel_le_iSup hct hBU h1) hzp

theorem centerPPrime_e6
    (k : Type) [Field k] [CharP k p] :
    CenterPPrime ↥(e6Data_valid.minGroup k) p :=
  centerPPrime_minuscule e6Data_valid isFiniteType_cartan_E6 k (e6Datum_isCTGroupDatum k)
    (e6Datum_steinbergExtras k) (e6Datum_bruhatExtras k)

theorem centerPPrime_e7
    (k : Type) [Field k] [CharP k p] :
    CenterPPrime ↥(e7Data_valid.minGroup k) p :=
  centerPPrime_minuscule e7Data_valid isFiniteType_cartan_E7 k (e7Datum_isCTGroupDatum k)
    (e7Datum_steinbergExtras k) (e7Datum_bruhatExtras k)

open CFSG.LieType.Steinberg.TwistedE6 in
theorem centerPPrime_fixedGroup
    {k : Type} [Field k] [CharP k p] (θ : k →+* k)
    (hθ : ∀ c, θ (θ c) = c) : CenterPPrime (fixedGroup k θ) p := by
  intro z hz hzp
  have hct := twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ)
  have h1 := (center_eq_normalCore_borel hct (twistedDatum_steinbergExtras θ hθ)
    (twistedDatum_bruhatExtras θ)) ▸ hz
  have hzT : z ∈ ⨆ i, hHat k θ i := normalCore_borel_le_iSup hct (twistedDatum_bruhatExtras θ) h1
  have hle : (⨆ i, hHat k θ i : Subgroup (fixedGroup k θ)) ≤
      (⨆ a, e6Data_valid.torus k a).comap (fixedGroup k θ).subtype :=
    iSup_le fun i x hx => hHatE_le_iSup_torus θ i (Subgroup.mem_subgroupOf.mp hx)
  have hzE := Subgroup.mem_comap.mp (hle hzT)
  exact Subtype.ext (eq_one_of_mem_iSup_torus_of_pow e6Data_valid k hzE
    (by rw [← Subgroup.coe_pow, hzp, Subgroup.coe_one]))

end Field

theorem modelCenterPPrime :
    ModelCenterPPrime := by
  intro t n p e hp hp2 hFT hadm
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  change CenterPPrime (modelUniv t n p e hp).K p
  cases t with
  | PSL =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
    exact centerPPrime_specialLinear m (GaloisField p e)
  | PSp => exact centerPPrime_statedSp n (GaloisField p e)
  | PSU =>
    have hf : 1 ≤ e := hadm.2.1
    have hF : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 :=
      card_galoisField_two_mul p e hf
    refine centerPPrime_of_eq (U := ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField p (2 * e)) p e) n, Unitary.rootDatum hF n⟩) ?_ ?_
    · simp only [modelUniv, lieUniversal, hf, ↓reduceDIte]
    · exact centerPPrime_unitary hF hadm.2.2.1 hadm.2.2.2
  | POmegaOdd => exact centerPPrime_spinOdd hadm.2.2.1 hp2 h2
  | POmegaPlus =>
    have hn : 3 ≤ n := by have := hadm.2.2; omega
    refine centerPPrime_of_eq (U := ⟨spinGroup (quadPlus n (GaloisField p e)),
      plusDatum n (GaloisField p e) hn⟩) ?_ ?_
    · simp only [modelUniv, lieUniversal, hn, ↓reduceDIte]
    · exact centerPPrime_spinPlus hn hp2 h2
  | POmegaMinus => exact centerPPrime_spinMinus hadm.2.2 (minusCoeffs_irr p e) hp2 h2
  | G2 => exact centerPPrime_adjoint .G2 (GaloisField p e)
  | F4 => exact centerPPrime_adjoint .F4 (GaloisField p e)
  | E6 => exact centerPPrime_e6 (GaloisField p e)
  | E7 => exact centerPPrime_e7 (GaloisField p e)
  | E8 => exact centerPPrime_adjoint .E8 (GaloisField p e)
  | twistedE6 => exact centerPPrime_fixedGroup (frobQ p e) (frobQ_frobQ p e hadm.2.1)
  | trialityD4 =>
    intro z hz hzp
    have hz2 : z ^ 2 = 1 := by simpa using centerExp_model_trialityD4 (n := n) hadm.2.1 z hz
    have hd : orderOf z ∣ Nat.gcd 2 p := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hz2)
      (orderOf_dvd_of_pow_eq_one hzp)
    have hg : Nat.gcd 2 p = 1 := by
      rw [Nat.gcd_comm, Nat.Coprime.gcd_eq_one]
      exact (Nat.coprime_primes hp Nat.prime_two).mpr hp2
    rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hd
  | twistedB2 => exact hFT.elim
  | twistedG2 => exact hFT.elim
  | twistedF4 => exact hFT.elim
  | Tits => exact hFT.elim

end CFSG.ComponentClassification.RankTwoOddLie
