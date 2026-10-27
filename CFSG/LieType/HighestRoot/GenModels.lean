module

public import CFSG.LieType.HighestRoot.Gen
public import CFSG.LieType.HighestRoot.RootsUnitary
public import CFSG.LieType.HighestRoot.GenUnitary
public import CFSG.ClassicalInvolution.ModelFacts.Models
public import CFSG.LieType.Steinberg.CentralExt.Families
public import CFSG.LieType.Steinberg.CentralExt.SpinMinus
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRootGroups
public import CFSG.LieType.Steinberg.TwistedE6.Local
public import CFSG.LieType.Steinberg.TwistedD4.Local
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2

public section

namespace CFSG.LieType.HighestRoot

open CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Universal
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.ModelFacts

section TwistedE6

open CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Minuscule.MinData.Valid CFSG.Blueprint.Chevalley

variable {k : Type} [Field k] (θ : k →+* k) {p : ℕ} [Fact p.Prime] [CharP k p]

private theorem xm_pow_e6'
    (γ : Fin (Tag.rank .E6) → ℤ) (c : k) (m : ℕ) :
    (e6Data_valid.xm k γ c) ^ m = e6Data_valid.xm k γ (m • c) := by
  induction m with
  | zero => simp [e6Data_valid.xm_zero]
  | succ m ih => rw [pow_succ, ih, ← e6Data_valid.xm_add, succ_nsmul]

theorem isPGroup_twistedE6_rootGroup
    {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β) :
    IsPGroup p (twistedRootGroup k θ β) := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨x, hx⟩
  have hpc : ∀ c : k, p • c = 0 := fun c => by
    rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  have hxp : (⟨x, hx⟩ : twistedRootGroup k θ β) ^ p = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨α₀, hα₀, hproj⟩ := exists_proj_eq hβ
    show ((x : fixedGroup k θ) : e6Data_valid.minGroup k) ^ p = 1
    by_cases hfix : rho α₀ = α₀
    · obtain ⟨c, -, hc⟩ := (mem_twistedRootGroup_iff_of_fixed θ hα₀ hproj hfix _).1 hx
      rw [hc, xm_pow_e6', hpc, e6Data_valid.xm_zero]
    · obtain ⟨c, hc⟩ := (mem_twistedRootGroup_iff_of_pair θ hα₀ hproj hfix _).1 hx
      rw [hc, ((commute_xm_rho hα₀ hfix) _ _).mul_pow, xm_pow_e6', xm_pow_e6', hpc, hpc,
        e6Data_valid.xm_zero, e6Data_valid.xm_zero, mul_one]
  have hdvd : orderOf (⟨x, hx⟩ : twistedRootGroup k θ β) ∣ p := orderOf_dvd_of_pow_eq_one hxp
  rcases (Nat.dvd_prime Fact.out).1 hdvd with h | h
  · exact ⟨0, by rw [h, pow_zero]⟩
  · exact ⟨1, by rw [h, pow_one]⟩

end TwistedE6

section TwistedD4

open CFSG.LieType.Steinberg.TwistedD4 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint

variable {K : Type} [Field K]

private theorem xPar_pow''
    {τ : Tag} {F : RootOperatorFamily τ} (γ : Fin τ.rank → ℤ) (c : K)
    (m : ℕ) : (xPar F γ c) ^ m = xPar F γ (m • c) := by
  induction m with
  | zero => simp [xPar_zero]
  | succ m ih => rw [pow_succ, ih, ← xPar_add, succ_nsmul]

theorem isPGroup_twistedD4_rootGroup
    (σ : K →+* K) (hσ : ∀ c, σ (σ (σ c)) = c) {p : ℕ}
    [Fact p.Prime] [CharP K p] {β : Fin (Tag.rank .G2) → ℤ} (hβ : IsRoot .G2 β) :
    IsPGroup p (twistedRootGroup σ β) := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨x, hx⟩
  have hpc : ∀ c : K, p • c = 0 := fun c => by
    rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  have hxp : (⟨x, hx⟩ : twistedRootGroup σ β) ^ p = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    have hg := (mem_twistedRootGroup (σ := σ)).1 hx
    obtain ⟨α, hα, hproj⟩ := exists_proj_eq hβ
    show ((x : twistedGroup σ) : adjointGroup d4 K) ^ p = 1
    by_cases hfix : rho α = α
    · obtain ⟨c, -, hc⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ hα hproj hfix _).1 hg
      rw [hc, xPar_pow'', hpc, xPar_zero]
    · obtain ⟨c, hc⟩ := (mem_twistedRootSubgroupD4_iff_of_orbit hσ hα hproj hfix _).1 hg
      have hadd : ∀ m : ℕ, xOrbit σ α c ^ m = xOrbit σ α (m • c) := fun m => by
        induction m with
        | zero => simp [xOrbit_zero]
        | succ m ih => rw [pow_succ, ih, ← xOrbit_add σ hα hfix, succ_nsmul]
      rw [hc, hadd, hpc, xOrbit_zero]
  have hdvd : orderOf (⟨x, hx⟩ : twistedRootGroup σ β) ∣ p := orderOf_dvd_of_pow_eq_one hxp
  rcases (Nat.dvd_prime Fact.out).1 hdvd with h | h
  · exact ⟨0, by rw [h, pow_zero]⟩
  · exact ⟨1, by rw [h, pow_one]⟩

end TwistedD4

theorem isPGroup_rootGroup_modelUniv
    (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) :
    ∀ γ ∈ (modelUniv t n p e hp).D.roots,
      IsPGroup p ((modelUniv t n p e hp).D.rootGroup γ) := by
  have : Fact p.Prime := ⟨hp⟩
  have he : 1 ≤ e := hadm.2.1
  cases t with
  | PSL =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
    exact fun γ hγ => isPGroup_of_isParametrization
      (SL.isParametrization (m := m) (F := GaloisField p e)) hγ
  | PSU =>
    rw [modelUniv_PSU he]
    have : Nonempty (Fin n) := ⟨⟨0, by have := hadm.2.2.1; omega⟩⟩
    exact fun γ hγ => isPGroup_rootGroup
      (BorelTits.unitaryInvolution_involutive (card_galoisField_two_mul p e he))
      (Unitary.SUExtras.toStd_ne_zero_of_mem_roots hγ)
  | PSp =>
    exact fun γ hγ => isPGroup_of_isParametrization
      (Sp.isParametrization (n := n) (F := GaloisField p e)) hγ
  | POmegaOdd =>
    exact fun γ hγ => isPGroup_of_isParametrization
      (SpinOdd.isParametrization (n := n) (K := GaloisField p e)) hγ
  | POmegaPlus =>
    have hn : 3 ≤ n := by have := hadm.2.2; omega
    rw [modelUniv_POmegaPlus hn]
    exact fun γ hγ => isPGroup_of_isParametrization
      (SpinPlus.isParametrization (K := GaloisField p e) hn) hγ
  | POmegaMinus => exact fun γ hγ => isPGroup_minusRootGroup _ hγ
  | F4 =>
    exact fun γ hγ => isPGroup_of_isParametrization
      (Adjoint.f4_isParametrization (K := GaloisField p e)) hγ
  | E8 =>
    exact fun γ hγ => isPGroup_of_isParametrization
      (Adjoint.e8_isParametrization (K := GaloisField p e)) hγ
  | G2 =>
    exact fun γ hγ => isPGroup_of_isParametrization
      (Adjoint.adjDatum_isParametrization (F := CFSG.LieType.Chevalley.rootOperatorFamily .G2)
        (K := GaloisField p e)
        (RootSystem.ofCartan (Adjoint.g2Datum (GaloisField p e)).isFiniteType
          (Adjoint.g2Datum (GaloisField p e)).divisible)
        (Adjoint.adjDatum_roots (CFSG.LieType.Chevalley.rootOperatorFamily .G2)
          (GaloisField p e))) hγ
  | E6 =>
    exact fun γ hγ => isPGroup_of_isParametrization
      (Minuscule.e6Datum_isParametrization (GaloisField p e)
        (RootSystem.ofCartan (Minuscule.e6Datum (GaloisField p e)).isFiniteType
          (Minuscule.e6Datum (GaloisField p e)).divisible) (Minuscule.roots_eq _)) hγ
  | E7 =>
    exact fun γ hγ => isPGroup_of_isParametrization
      (Minuscule.e7Datum_isParametrization (GaloisField p e)
        (RootSystem.ofCartan (Minuscule.e7Datum (GaloisField p e)).isFiniteType
          (Minuscule.e7Datum (GaloisField p e)).divisible) (Minuscule.roots_eq _)) hγ
  | twistedE6 =>
    exact fun γ hγ => isPGroup_twistedE6_rootGroup _
      (TwistedE6.isRoot_of_mem_twistedDatum_roots _ hγ)
  | trialityD4 =>
    have hcard : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
      rw [GaloisField.card p (3 * e) (by omega), ← pow_mul, mul_comm]
    have hσ := TwistedD4.sigma_three_of_card
      (σ := iterateFrobenius (GaloisField p (3 * e)) p e) (q := p ^ e) hcard
      (fun c => iterateFrobenius_def p e c)
    exact fun γ hγ => isPGroup_twistedD4_rootGroup _ hσ
      (TwistedD4.isRoot_of_mem_twistedDatum_roots _ hγ)
  | twistedB2 | twistedG2 | twistedF4 | Tits => exact absurd hfund (by simp [IsFundTag])

theorem divisible_modelUniv
    (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (h : ¬ (t = .PSU ∧ ¬ Even n)) : (modelUniv t n p e hp).D.divisible = ∅ := by
  have : Fact p.Prime := ⟨hp⟩
  have he : 1 ≤ e := hadm.2.1
  cases t with
  | PSL =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
    rfl
  | PSU =>
    rw [modelUniv_PSU he]
    exact (unitary_even (by by_contra hn; exact h ⟨rfl, hn⟩)).2
  | POmegaPlus =>
    have hn : 3 ≤ n := by have := hadm.2.2; omega
    rw [modelUniv_POmegaPlus hn]
    rfl
  | PSp | POmegaOdd | POmegaMinus | F4 | E8 | G2 | E6 | E7 | twistedE6 | trialityD4 => rfl
  | twistedB2 | twistedG2 | twistedF4 | Tits => exact absurd hfund (by simp [IsFundTag])

theorem rank_pos_modelUniv
    (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) :
    0 < (modelUniv t n p e hp).D.rank := by
  have : Fact p.Prime := ⟨hp⟩
  have he : 1 ≤ e := hadm.2.1
  by_cases h1 : t = .PSL ∧ n = 2
  · obtain ⟨rfl, rfl⟩ := h1
    show 0 < 1
    norm_num
  by_cases h2 : t = .PSU ∧ n = 3
  · obtain ⟨rfl, rfl⟩ := h2
    rw [modelUniv_PSU he]
    show 0 < 3 / 2
    norm_num
  exact lt_of_lt_of_le two_pos (two_le_rank t n p e hp hfund hadm h1 h2)

theorem highestRootGen_modelUniv
    (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) :
    HighestRootGen (modelUniv t n p e hp).D p := by
  have : Fact p.Prime := ⟨hp⟩
  have hirr := (cartanOK t n p e hp hfund hadm).irreducible
  have hX := isPGroup_rootGroup_modelUniv t n p e hp hfund hadm
  by_cases hBC : t = .PSU ∧ ¬ Even n
  · obtain ⟨rfl, hodd⟩ := hBC
    have he : 1 ≤ e := hadm.2.1
    have hn3 : 3 ≤ n := hadm.2.2.1
    revert hirr hX
    rw [modelUniv_PSU he]
    intro hirr hX
    have hF := card_galoisField_two_mul p e he
    obtain ⟨ζ, hζ⟩ := Unitary.exists_traceZero_ne_zero hF
    exact highestRootGen_of_datum (Unitary.isCTGroupDatum hF n (by omega) ζ hζ)
      (Unitary.steinbergExtras hF n (by omega) ζ hζ) (divisibleNormalizes_unitary hF n)
      (divisibleWeylMem_unitary hF n ζ) hirr hX (isHighestRoot_unitary_odd hF hodd hn3)
  · obtain ⟨_, _, hct, hext⟩ := hasBruhatDatum t n p e hp hfund hadm
    exact highestRootGen_of_divisible_eq_empty hct hext
      (divisible_modelUniv t n p e hp hfund hadm hBC) (rank_pos_modelUniv t n p e hp hfund hadm)
      hirr hX

end CFSG.LieType.HighestRoot
