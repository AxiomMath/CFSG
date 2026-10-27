module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6A5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreD5Datum
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6A4
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ CFSG.ClassicalInvolution.Upgrade
  CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn

section Setup


variable {f : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
  {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [IsAlgClosed Ω] [CharP Ω 2]
  {Fr : Ω →+* Ω}

noncomputable abbrev twE6EnnolaSetup (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (hFr : ∀ c, Fr c = c ^ (2 ^ f))
    {q : ℕ} (hq : q.Prime) (hqdvd : q ∣ 2 ^ f + 1) : LangSetup Tag.E6 Ω q :=
  (twE6EnnolaDatum (ℓ := 2) Nat.prime_two (by omega) hK hFr).toSetup q (Equiv.neg _)
    (twE6EnnolaDatum_frob (ℓ := 2) Nat.prime_two (by omega) hK hFr) hq
    (Or.inr (by
      rw [twE6EnnolaDatum_q (ℓ := 2) Nat.prime_two (by omega) hK hFr]
      have h4 : (2 : ℕ) ^ 2 ≤ 2 ^ f :=
        pow_le_pow_right₀ (by norm_num : 1 ≤ 2) (by omega : 2 ≤ f)
      simpa using h4))
    (by
      rw [twE6EnnolaDatum_q (ℓ := 2) Nat.prime_two (by omega) hK hFr]
      have hpp : IsPrimePow ((2 : ℕ) ^ f) := Nat.prime_two.isPrimePow.pow (by omega)
      exact ⟨hpp, by
        rw [Nat.cast_pow, CharP.cast_eq_zero Ω (2 : ℕ)]
        exact zero_pow (by omega)⟩)
    (by
      intro hdvd
      rw [twE6EnnolaDatum_q (ℓ := 2) Nat.prime_two (by omega) hK hFr] at hdvd
      have h1 : q ∣ 1 := by
        have := Nat.dvd_sub hqdvd hdvd
        simpa using this
      exact absurd (Nat.dvd_one.1 h1) (by have := hq.two_le; omega))
    (finite_model_twistedE6 (ℓ := 2) (σ := σ) Nat.prime_two (by omega) hK hσ hFr
      (twE6EnnolaDatum (ℓ := 2) Nat.prime_two (by omega) hK hFr) rfl)

theorem twE6EnnolaSetup_D (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (hFr : ∀ c, Fr c = c ^ (2 ^ f))
    {q : ℕ} (hq : q.Prime) (hqdvd : q ∣ 2 ^ f + 1) :
    (twE6EnnolaSetup (Fr := Fr) hf hK hσ hFr hq hqdvd).D =
      twE6EnnolaDatum (Ω := Ω) (ℓ := 2) Nat.prime_two (by omega) hK hFr :=
  rfl

theorem twE6EnnolaSetup_rho (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (hFr : ∀ c, Fr c = c ^ (2 ^ f))
    {q : ℕ} (hq : q.Prime) (hqdvd : q ∣ 2 ^ f + 1) :
    (twE6EnnolaSetup (Fr := Fr) hf hK hσ hFr hq hqdvd).ρ =
      Equiv.neg (Fin Tag.E6.rank → ℤ) :=
  rfl

theorem twE6EnnolaSetup_Gamma (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (hFr : ∀ c, Fr c = c ^ (2 ^ f))
    {q : ℕ} (hq : q.Prime) (hqdvd : q ∣ 2 ^ f + 1) :
    (twE6EnnolaSetup (Fr := Fr) hf hK hσ hFr hq hqdvd).Γ =
      ⁅thetaFixed Fr, thetaFixed Fr⁆ :=
  rfl

theorem twE6EnnolaSetup_q (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (hFr : ∀ c, Fr c = c ^ (2 ^ f))
    {q : ℕ} (hq : q.Prime) (hqdvd : q ∣ 2 ^ f + 1) :
    (twE6EnnolaSetup (Fr := Fr) hf hK hσ hFr hq hqdvd).D.q = 2 ^ f :=
  rfl

@[expose] noncomputable def twE6JStar {q : ℕ} {ζ : Ωˣ}
    (i : KernelComponent (rootCharHom (twE6omega1Tuple ζ))) : Subgroup (ModGL Tag.E6 Ω) :=
  rationalComponent (Equiv.neg (Fin Tag.E6.rank → ℤ)) ⁅thetaFixed Fr, thetaFixed Fr⁆
    (rootCharHom (twE6omega1Tuple ζ)) i

end Setup

section Strong


variable {f : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
  {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [IsAlgClosed Ω] [CharP Ω 2]
  {Fr : Ω →+* Ω}

theorem twE6_dStrongModel_omega1 (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (hFr : ∀ c, Fr c = c ^ (2 ^ f)) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hqdvd : q ∣ 2 ^ f + 1)
    {ζ : Ωˣ} (hζq : ζ ^ q = 1) (hζ1 : ζ ≠ 1)
    (i : KernelComponent (rootCharHom (twE6omega1Tuple ζ))) :
    DStrongModel (twE6JStar (Fr := Fr) (q := q) (ζ := ζ) i) 5 2 f := by
  classical
  have hker : kernelRoots (rootCharHom (twE6omega1Tuple ζ)) = twE6D5 :=
    kernelRoots_omega1 hq hζq hζ1
  have hΨ : componentRoots (rootCharHom (twE6omega1Tuple ζ)) i = twE6D5 :=
    componentRoots_eq_twE6D5 hker i
  have hc5 : compRank (componentRoots (rootCharHom (twE6omega1Tuple ζ)) i) = 5 := by
    rw [hΨ]; exact twE6D5_compRank
  have hn40 : (componentRoots (rootCharHom (twE6omega1Tuple ζ)) i).ncard = 40 := by
    rw [hΨ]; exact twE6D5_ncard
  have h5 : 5 ≤ compRank (componentRoots (rootCharHom (twE6omega1Tuple ζ)) i) := by omega
  have hn : (componentRoots (rootCharHom (twE6omega1Tuple ζ)) i).ncard =
      2 * compRank (componentRoots (rootCharHom (twE6omega1Tuple ζ)) i) *
        (compRank (componentRoots (rootCharHom (twE6omega1Tuple ζ)) i) - 1) := by
    rw [hn40, hc5]
  have hkind : twistKind (twE6EnnolaSetup (Fr := Fr) hf hK hσ hFr hq hqdvd).ρ
      (rootCharHom (twE6omega1Tuple ζ)) i = .twoD := by
    rw [twE6EnnolaSetup_rho]
    exact twistKind_ennola_D5 hq hζq hζ1 (Equiv.neg (Fin Tag.E6.rank → ℤ))
      (fun γ _ => rfl) i
  have hTor : rootDiagUnit Tag.E6 (twE6omega1Tuple ζ) ∈
      (twE6EnnolaSetup (Fr := Fr) hf hK hσ hFr hq hqdvd).D.torus := by
    rw [twE6EnnolaSetup_D]
    rw [twE6EnnolaDatum_torus (ℓ := 2) Nat.prime_two (by omega) hK hFr]
    intro j
    obtain ⟨m, hm⟩ := hqdvd
    simp only [twE6omega1Tuple]
    split_ifs with hj
    · rw [hm, pow_mul, hζq, one_pow]
    · simp
  have hTp : rootDiagUnit Tag.E6 (twE6omega1Tuple ζ) ^ q = 1 := by
    have haq : (twE6omega1Tuple ζ) ^ q = 1 := by
      funext j
      simp only [twE6omega1Tuple, Pi.pow_apply]
      split_ifs with hj
      · exact hζq
      · simp
    calc rootDiagUnit Tag.E6 (twE6omega1Tuple ζ) ^ q =
        rootDiagUnitHom Tag.E6 Ω ((twE6omega1Tuple ζ) ^ q) :=
        (map_pow (rootDiagUnitHom Tag.E6 Ω) _ q).symm
      _ = 1 := by rw [haq, map_one]
  have hpL : ((q : ℕ) : Ω) ≠ 0 := by
    intro h0
    have h2q : 2 ∣ q := (CharP.cast_eq_zero_iff Ω 2 q).1 h0
    exact hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 h2q).symm
  have hQ : (fun r q => r = 2 ∨ 5 ≤ q) (ringChar Ω)
      (twE6EnnolaSetup (Fr := Fr) hf hK hσ hFr hq hqdvd).D.q :=
    Or.inl (ringChar.eq Ω 2)
  obtain ⟨r, e, m, hr, hqe, hm5, hm, hSM⟩ :=
    strongModel_of_dClassTwistedG_E6 (S := twE6EnnolaSetup (Fr := Fr) hf hK hσ hFr hq hqdvd)
      hq hpL hTor hTp i h5 hn hkind (fun r q => r = 2 ∨ 5 ≤ q)
      (twoDChainRecogSAll_even_or_five Ω) hQ
  have hr2 : r = 2 := by rw [← hr]; exact ringChar.eq Ω 2
  have hqf : (2 : ℕ) ^ f = r ^ e := by
    rw [← hqe]
    exact twE6EnnolaSetup_q hf hK hσ hFr hq hqdvd
  have he : e = f := by
    rw [hr2] at hqf
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 2) hqf).symm
  subst hr2 he
  have hm5' : m = 5 := by rw [hm, hc5]
  subst hm5'
  exact hSM

theorem twE6_isQuasisimple_omega1 (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (hFr : ∀ c, Fr c = c ^ (2 ^ f)) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hqdvd : q ∣ 2 ^ f + 1)
    {ζ : Ωˣ} (hζq : ζ ^ q = 1) (hζ1 : ζ ≠ 1)
    (i : KernelComponent (rootCharHom (twE6omega1Tuple ζ))) :
    CFSG.IsQuasisimple ↥(twE6JStar (Fr := Fr) (q := q) (ζ := ζ) i) :=
  (twE6_dStrongModel_omega1 hf hK hσ hFr hq hq2 hqdvd hζq hζ1 i).2.1

theorem twE6_hasLabel_omega1 (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (hFr : ∀ c, Fr c = c ^ (2 ^ f)) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hqdvd : q ∣ 2 ^ f + 1)
    {ζ : Ωˣ} (hζq : ζ ^ q = 1) (hζ1 : ζ ≠ 1)
    (i : KernelComponent (rootCharHom (twE6omega1Tuple ζ))) :
    HasLabel ↥(twE6JStar (Fr := Fr) (q := q) (ζ := ζ) i) (· = ⟨.twD, 5, f⟩) := by
  have hSM := twE6_dStrongModel_omega1 hf hK hσ hFr hq hq2 hqdvd hζq hζ1 i
  exact hasLabel_of_statedClassicalModel_POmegaMinus hSM.2.1
    (statedClassicalModel_of_lieModel (t := .POmegaMinus) (n := 5) (r := 2) (e := f)
      (by decide) hSM.1)

end Strong

end CFSG.LocalAnalysis.GLTheoremA.Y10F
