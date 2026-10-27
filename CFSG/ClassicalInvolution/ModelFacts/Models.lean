module

public import CFSG.ClassicalInvolution.ModelFacts.Families
public import CFSG.ClassicalInvolution.ModelFacts.Fundamental
public import CFSG.Blueprint.Catalog
public import CFSG.LieType.CurtisTits.Spin
public import CFSG.LieType.Steinberg.G2.Extras
public import CFSG.LieType.Steinberg.TwistedD4.Datum
public import CFSG.LieType.Steinberg.TwistedD4.Perfect
public import CFSG.LieType.Steinberg.TwistedE6.Datum
public import CFSG.LieType.Steinberg.TwistedE6.Generation
public import CFSG.LieType.Steinberg.Exceptional.Universal
public import CFSG.LieType.Universal.Catalog
public import CFSG.LieType.Universal.Unitary.Extras
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import CFSG.Assembly.Subnormal
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
open scoped Matrix

@[expose] def IsFundTag : StatedLieTag → Prop
  | .PSL | .PSU | .PSp | .POmegaOdd | .POmegaPlus | .POmegaMinus
  | .G2 | .F4 | .E6 | .E7 | .E8 | .twistedE6 | .trialityD4 => True
  | _ => False

@[expose] noncomputable def modelUniv (t : StatedLieTag) (n p f : ℕ) (hp : p.Prime) :
    LieUniversal :=
  haveI : Fact p.Prime := ⟨hp⟩
  match t with
  | .G2 =>
    ⟨↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField p f)),
      CFSG.LieType.Steinberg.Adjoint.g2Datum (GaloisField p f)⟩
  | .trialityD4 =>
    ⟨↥(CFSG.LieType.Steinberg.TwistedD4.twistedGroup
        (iterateFrobenius (GaloisField p (3 * f)) p f)),
      CFSG.LieType.Steinberg.TwistedD4.twistedDatum
        (iterateFrobenius (GaloisField p (3 * f)) p f)⟩
  | _ => lieUniversal t n p f hp

variable {K : Type*} [Group K]

@[expose] def fundamentalSubgroups (t : StatedLieTag) (D : UniversalRootDatum K) :
    Set (Subgroup K) :=
  {R | ∃ (g : K) (γ : Fin D.rank → ℤ),
    (IsLongestRoot D γ ∨ (t = .G2 ∧ γ ∈ D.roots) ∨ (t = .trialityD4 ∧ γ ∈ D.roots)) ∧
    R = (D.rootGroup γ ⊔ D.rootGroup (-γ)).map (MulAut.conj g).toMonoidHom}

@[expose] def HasBruhatDatum (D : UniversalRootDatum K) : Prop :=
  ∃ (n : Fin D.rank → K) (H : Fin D.rank → Subgroup K),
    IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem (weylAction D.isFiniteType)
      D.roots D.rootGroup n H ∧ SteinbergExtras D n H

theorem two_ne_zero_galoisField {p : ℕ} [Fact p.Prime] (f : ℕ) (h : p ≠ 2) :
    (2 : GaloisField p f) ≠ 0 := by
  intro h0
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p f) p 2).1 (by exact_mod_cast h0)
  exact h ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 hdvd)

private theorem card_galoisField_mul (p f m : ℕ) [Fact p.Prime] (hf : 1 ≤ f) (hm : 1 ≤ m) :
    Nat.card (GaloisField p (m * f)) = (p ^ f) ^ m := by
  rw [GaloisField.card p (m * f) (Nat.mul_ne_zero (by omega) (by omega)), ← pow_mul, mul_comm]

theorem hasBruhatDatum (t : StatedLieTag) (n p f : ℕ) (hp : p.Prime) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p f) : HasBruhatDatum (modelUniv t n p f hp).D := by
  have : Fact p.Prime := ⟨hp⟩
  have hf : 1 ≤ f := hadm.2.1
  cases t with
  | PSL =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
    exact ⟨_, _, SpecialLinear.isCTGroupDatum m (GaloisField p f),
      SpecialLinear.steinbergExtras m (GaloisField p f)⟩
  | PSU =>
    have hn : 3 ≤ n := hadm.2.2.1
    have hF := card_galoisField_two_mul p f hf
    have e : modelUniv .PSU n p f hp =
        ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField p (2 * f)) p f) n,
          Unitary.rootDatum hF n⟩ := by
      simp only [modelUniv, lieUniversal, hf, ↓reduceDIte]
    rw [e]
    obtain ⟨ζ, hζ⟩ := Unitary.exists_traceZero_ne_zero hF
    exact ⟨_, _, Unitary.isCTGroupDatum hF n (by omega) ζ hζ,
      Unitary.steinbergExtras hF n (by omega) ζ hζ⟩
  | PSp =>
    exact ⟨_, _, Symplectic.isCTGroupDatum n (GaloisField p f),
      Symplectic.steinbergExtras n (GaloisField p f)⟩
  | POmegaOdd =>
    have hn : 3 ≤ n := hadm.2.2.1
    have h2 : (2 : GaloisField p f) ≠ 0 := two_ne_zero_galoisField f hadm.2.2.2
    exact ⟨_, _, Spin.oddDatum_isCTGroupDatum n (GaloisField p f)
        (Spin.oddDatum_iSup_eq_top n _ h2 hn), Spin.oddDatum_steinbergExtras h2⟩
  | POmegaPlus =>
    have hn : 3 ≤ n := by have := hadm.2.2; omega
    have e : modelUniv .POmegaPlus n p f hp =
        ⟨spinGroup (Spin.quadPlus n (GaloisField p f)), Spin.plusDatum n (GaloisField p f) hn⟩ := by
      simp only [modelUniv, lieUniversal, hn, ↓reduceDIte]
    rw [e]
    exact ⟨_, _, Spin.plusDatum_isCTGroupDatum hn (Spin.plusDatum_iSup_eq_top n _ hn),
      Spin.plusDatum_steinbergExtras hn⟩
  | POmegaMinus =>
    have hn : 4 ≤ n := hadm.2.2
    exact ⟨_, _, Spin.Twisted.minusDatum_isCTGroupDatum n (minusCoeffs_irr p f) hn,
      Spin.Twisted.minusDatum_steinbergExtras n (minusCoeffs_irr p f)⟩
  | F4 =>
    exact ⟨_, _, Adjoint.f4_isCTGroupDatum (GaloisField p f),
      Adjoint.f4_steinbergExtras (GaloisField p f)⟩
  | E8 =>
    exact ⟨_, _, Adjoint.e8_isCTGroupDatum (GaloisField p f),
      Adjoint.e8_steinbergExtras (GaloisField p f)⟩
  | G2 =>
    exact ⟨_, _, Adjoint.g2_isCTGroupDatum (GaloisField p f),
      Adjoint.g2_steinbergExtras (GaloisField p f)⟩
  | E6 =>
    exact ⟨_, _, Minuscule.e6Datum_isCTGroupDatum (GaloisField p f),
      Minuscule.e6Datum_steinbergExtras (GaloisField p f)⟩
  | E7 =>
    exact ⟨_, _, Minuscule.e7Datum_isCTGroupDatum (GaloisField p f),
      Minuscule.e7Datum_steinbergExtras (GaloisField p f)⟩
  | twistedE6 =>
    exact ⟨_, _, TwistedE6.twistedDatum_isCTGroupDatum (Exceptional.frobQ p f)
        (Exceptional.frobQ_frobQ p f hf)
        (TwistedE6.iSup_twistedDatum_rootGroup (Exceptional.frobQ p f)
          (Exceptional.frobQ_frobQ p f hf)),
      TwistedE6.twistedDatum_steinbergExtras (Exceptional.frobQ p f)
        (Exceptional.frobQ_frobQ p f hf)⟩
  | trialityD4 =>
    have hσ := TwistedD4.sigma_three_of_card
      (σ := iterateFrobenius (GaloisField p (3 * f)) p f) (q := p ^ f)
      (card_galoisField_mul p f 3 hf (by norm_num))
      (fun c => iterateFrobenius_def p f c)
    exact ⟨_, _, TwistedD4.twistedDatum_isCTGroupDatum _ hσ,
      TwistedD4.twistedDatum_steinbergExtras _ hσ⟩
  | twistedB2 | twistedG2 | twistedF4 | Tits => exact absurd hfund (by simp [IsFundTag])

@[expose] def IsLongNode : StatedLieTag → ℕ → ℕ → Prop
  | .PSL, _, _ => True
  | .PSU, n, k => Even n ∧ k + 1 = n / 2
  | .PSp, n, k => k + 1 = n
  | .POmegaOdd, n, k => k + 1 < n
  | .POmegaPlus, _, _ => True
  | .POmegaMinus, n, k => k + 2 < n
  | .G2, _, k => k = 0
  | .trialityD4, _, k => k = 0
  | .F4, _, k => k < 2
  | .twistedE6, _, k => k < 2
  | .E6, _, _ => True
  | .E7, _, _ => True
  | .E8, _, _ => True
  | _, _, _ => False

structure CartanOK (D : UniversalRootDatum K) : Prop where
  irreducible : IsIrreducible D.cartan
  ratio : ∀ i ∈ D.divisible, ∀ j,
    symmetrizer D.isFiniteType j < 4 * symmetrizer D.isFiniteType i

theorem modelUniv_PSU {n p f : ℕ} [hp : Fact p.Prime] (hf : 1 ≤ f) :
    modelUniv .PSU n p f hp.out =
      ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField p (2 * f)) p f) n,
        Unitary.rootDatum (card_galoisField_two_mul p f hf) n⟩ := by
  simp only [modelUniv, lieUniversal, hf, ↓reduceDIte]

theorem modelUniv_POmegaPlus {n p f : ℕ} [hp : Fact p.Prime] (hn : 3 ≤ n) :
    modelUniv .POmegaPlus n p f hp.out =
      ⟨spinGroup (Spin.quadPlus n (GaloisField p f)), Spin.plusDatum n (GaloisField p f) hn⟩ := by
  simp only [modelUniv, lieUniversal, hn, ↓reduceDIte]

theorem unitary_even {n : ℕ} (he : Even n) :
    Unitary.cartan n = Symplectic.cartanC (n / 2) ∧ Unitary.divisible n = ∅ := by
  simp [Unitary.cartan, Unitary.divisible, he]

theorem unitary_odd {n : ℕ} (he : ¬ Even n) :
    Unitary.cartan n = (Symplectic.cartanC (n / 2))ᵀ ∧
      Unitary.divisible n = {k : Fin (n / 2) | k.val + 1 = n / 2} := by
  simp [Unitary.cartan, Unitary.divisible, he]

theorem cartanOK (t : StatedLieTag) (n p f : ℕ) (hp : p.Prime) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p f) : CartanOK (modelUniv t n p f hp).D := by
  have : Fact p.Prime := ⟨hp⟩
  have hf : 1 ≤ f := hadm.2.1
  cases t with
  | PSL =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
    exact ⟨isIrreducible_A (by have := hadm.2.2.1; omega),
      fun i hi => absurd hi (Set.notMem_empty i)⟩
  | PSU =>
    have hn : 3 ≤ n := hadm.2.2.1
    rw [modelUniv_PSU hf]
    by_cases he : Even n
    · obtain ⟨hc, hd⟩ := unitary_even he
      refine ⟨?_, fun i hi => ?_⟩
      · show IsIrreducible (Unitary.cartan n)
        rw [hc]
        exact isIrreducible_cartanC (by omega)
      · exfalso
        have hi' : i ∈ Unitary.divisible n := hi
        rw [hd] at hi'
        exact Set.notMem_empty i hi'
    · obtain ⟨hc, hd⟩ := unitary_odd he
      refine ⟨?_, fun i hi j => ?_⟩
      · show IsIrreducible (Unitary.cartan n)
        rw [hc]
        exact isIrreducible_transpose_cartanC (by omega)
      · have hi' : i ∈ Unitary.divisible n := hi
        rw [hd] at hi'
        exact symmetrizer_lt_four_mul_BC (by omega) hc _ i hi' j
  | PSp =>
    exact ⟨isIrreducible_cartanC (by have := hadm.2.2.1; omega),
      fun i hi => absurd hi (Set.notMem_empty i)⟩
  | POmegaOdd =>
    exact ⟨isIrreducible_cartanB (by have := hadm.2.2.1; omega),
      fun i hi => absurd hi (Set.notMem_empty i)⟩
  | POmegaPlus =>
    have hn : 3 ≤ n := by have := hadm.2.2; omega
    rw [modelUniv_POmegaPlus hn]
    exact ⟨isIrreducible_cartanD hn, fun i hi => absurd hi (Set.notMem_empty i)⟩
  | POmegaMinus =>
    exact ⟨isIrreducible_cartanB (by have := hadm.2.2; omega),
      fun i hi => absurd hi (Set.notMem_empty i)⟩
  | F4 => exact ⟨isIrreducible_F4, fun i hi => absurd hi (Set.notMem_empty i)⟩
  | E6 => exact ⟨isIrreducible_E6, fun i hi => absurd hi (Set.notMem_empty i)⟩
  | E7 => exact ⟨isIrreducible_E7, fun i hi => absurd hi (Set.notMem_empty i)⟩
  | E8 => exact ⟨isIrreducible_E8, fun i hi => absurd hi (Set.notMem_empty i)⟩
  | G2 => exact ⟨isIrreducible_G2, fun i hi => absurd hi (Set.notMem_empty i)⟩
  | twistedE6 => exact ⟨isIrreducible_F4, fun i hi => absurd hi (Set.notMem_empty i)⟩
  | trialityD4 => exact ⟨isIrreducible_G2, fun i hi => absurd hi (Set.notMem_empty i)⟩
  | twistedB2 | twistedG2 | twistedF4 | Tits => exact absurd hfund (by simp [IsFundTag])

theorem isLongestRoot_single (t : StatedLieTag) (n p f : ℕ) (hp : p.Prime) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p f) :
    ∀ k : Fin (modelUniv t n p f hp).D.rank, IsLongNode t n k.val →
      IsLongestRoot (modelUniv t n p f hp).D (Pi.single k 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have hf : 1 ≤ f := hadm.2.1
  cases t with
  | PSL =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
    exact fun k _ => isLongest_single_A (m := m) (by have := hadm.2.2.1; omega) rfl _ k
  | PSU =>
    have hn : 3 ≤ n := hadm.2.2.1
    revert hfund
    rw [modelUniv_PSU hf]
    intro _ k hk
    obtain ⟨hc, hd⟩ := unitary_even hk.1
    show IsLongest _ (Unitary.divisible n) _
    rw [hd]
    exact isLongest_single_cartanC (by omega) hc _ hk.2
  | PSp =>
    exact fun k hk => isLongest_single_cartanC (m := n) (by have := hadm.2.2.1; omega) rfl _ hk
  | POmegaOdd =>
    exact fun k hk => isLongest_single_cartanB (m := n) (by have := hadm.2.2.1; omega) rfl _ hk
  | POmegaPlus =>
    have hn : 3 ≤ n := by have := hadm.2.2; omega
    revert hfund
    rw [modelUniv_POmegaPlus hn]
    exact fun _ k _ => isLongest_single_cartanD hn rfl _ k
  | POmegaMinus =>
    have hn : 4 ≤ n := hadm.2.2
    exact fun k hk => isLongest_single_cartanB (m := n - 1) (by omega) rfl _ (by
      have : k.val + 2 < n := hk
      change k.val + 1 < n - 1
      omega)
  | F4 => exact fun k hk => isLongest_single_F4 rfl _ hk
  | twistedE6 => exact fun k hk => isLongest_single_F4 rfl _ hk
  | G2 => exact fun k hk => isLongest_single_G2 rfl _ hk
  | trialityD4 => exact fun k hk => isLongest_single_G2 rfl _ hk
  | E6 => exact fun k _ => isLongest_single_E6 rfl _ k
  | E7 => exact fun k _ => isLongest_single_E7 rfl _ k
  | E8 => exact fun k _ => isLongest_single_E8 rfl _ k
  | twistedB2 | twistedG2 | twistedF4 | Tits => exact absurd hfund (by simp [IsFundTag])

theorem isLongestRoot_two_nsmul_single_PSU (n p f : ℕ) (hp : p.Prime)
    (hadm : StatedLieAdmissible .PSU n p f) (hodd : ¬ Even n) :
    ∀ k : Fin (modelUniv .PSU n p f hp).D.rank, k.val + 1 = n / 2 →
      IsLongestRoot (modelUniv .PSU n p f hp).D (2 • Pi.single k 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have hf : 1 ≤ f := hadm.2.1
  have hn : 3 ≤ n := hadm.2.2.1
  rw [modelUniv_PSU hf]
  intro k hk
  obtain ⟨hc, hd⟩ := unitary_odd hodd
  show IsLongest _ (Unitary.divisible n) _
  rw [hd]
  exact isLongest_two_nsmul_single_BC (by omega) hc _ hk

@[expose] def HasPartner : StatedLieTag → ℕ → Prop
  | .PSL, n => 3 ≤ n
  | .POmegaOdd, _ => True
  | .POmegaPlus, _ => True
  | .POmegaMinus, _ => True
  | .G2, _ => True
  | .trialityD4, _ => True
  | .F4, _ => True
  | .twistedE6, _ => True
  | .E6, _ => True
  | .E7, _ => True
  | .E8, _ => True
  | _, _ => False

theorem exists_longest_partner (t : StatedLieTag) (n p f : ℕ) (hp : p.Prime) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p f) (hpart : HasPartner t n) :
    ∃ γ₀ δ₀ : Fin (modelUniv t n p f hp).D.rank → ℤ, IsLongestRoot (modelUniv t n p f hp).D γ₀ ∧
      IsLongestRoot (modelUniv t n p f hp).D δ₀ ∧
      IsPartner (modelUniv t n p f hp).D.isFiniteType γ₀ δ₀ := by
  have : Fact p.Prime := ⟨hp⟩
  cases t with
  | PSL =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
    exact exists_partner_A (m := m) (by have : 3 ≤ m + 1 := hpart; omega) rfl _
  | POmegaOdd =>
    exact exists_partner_cartanB (m := n) (by have := hadm.2.2.1; omega) rfl _
  | POmegaPlus =>
    have hn : 3 ≤ n := by have := hadm.2.2; omega
    revert hfund
    rw [modelUniv_POmegaPlus hn]
    exact fun _ => exists_partner_cartanD hn rfl _
  | POmegaMinus => exact exists_partner_cartanB (m := n - 1) (by have := hadm.2.2; omega) rfl _
  | F4 => exact exists_partner_F4 rfl _
  | twistedE6 => exact exists_partner_F4 rfl _
  | G2 => exact exists_partner_G2 rfl _
  | trialityD4 => exact exists_partner_G2 rfl _
  | E6 => exact exists_partner_E6 rfl _
  | E7 => exact exists_partner_E7 rfl _
  | E8 => exact exists_partner_E8 rfl _
  | PSU | PSp | twistedB2 | twistedG2 | twistedF4 | Tits =>
    exact absurd hpart (by simp [HasPartner])

theorem map_conj_map_conj (R : Subgroup K) (g h : K) :
    (R.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      R.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem map_conj_one (R : Subgroup K) : R.map (MulAut.conj (1 : K)).toMonoidHom = R := by
  have : (MulAut.conj (1 : K)).toMonoidHom = MonoidHom.id K := by ext; simp
  rw [this, Subgroup.map_id]

theorem exists_conj_of_isLongestRoot (t : StatedLieTag) (n p f : ℕ) (hp : p.Prime)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p f)
    {γ γ' : Fin (modelUniv t n p f hp).D.rank → ℤ} (hγ : IsLongestRoot (modelUniv t n p f hp).D γ)
    (hγ' : IsLongestRoot (modelUniv t n p f hp).D γ') :
    ∃ g : (modelUniv t n p f hp).K,
      ((modelUniv t n p f hp).D.rootGroup γ ⊔ (modelUniv t n p f hp).D.rootGroup (-γ)).map
          (MulAut.conj g).toMonoidHom =
        (modelUniv t n p f hp).D.rootGroup γ' ⊔ (modelUniv t n p f hp).D.rootGroup (-γ') := by
  obtain ⟨_, _, hct, -⟩ := hasBruhatDatum t n p f hp hfund hadm
  obtain ⟨hirr, hratio⟩ := cartanOK t n p f hp hfund hadm
  exact exists_conj_of_isLongest hct hirr hratio hγ hγ'

theorem exists_conj_of_lenSq_eq (t : StatedLieTag) (n p f : ℕ) (hp : p.Prime)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p f)
    {γ γ' : Fin (modelUniv t n p f hp).D.rank → ℤ}
    (hγ : γ ∈ roots (modelUniv t n p f hp).D.isFiniteType ∅)
    (hγ' : γ' ∈ roots (modelUniv t n p f hp).D.isFiniteType ∅)
    (h : lenSq (modelUniv t n p f hp).D.isFiniteType γ =
      lenSq (modelUniv t n p f hp).D.isFiniteType γ') :
    ∃ g : (modelUniv t n p f hp).K,
      ((modelUniv t n p f hp).D.rootGroup γ ⊔ (modelUniv t n p f hp).D.rootGroup (-γ)).map
          (MulAut.conj g).toMonoidHom =
        (modelUniv t n p f hp).D.rootGroup γ' ⊔ (modelUniv t n p f hp).D.rootGroup (-γ') := by
  obtain ⟨_, _, hct, -⟩ := hasBruhatDatum t n p f hp hfund hadm
  obtain ⟨g, h1, h2⟩ := exists_map_conj_rankOne_of_lenSq_eq hct (cartanOK t n p f hp hfund hadm).1
    hγ hγ' h
  exact ⟨g, by rw [Subgroup.map_sup, h1, h2]⟩

@[expose] def FundamentalSingleClass (t : StatedLieTag) (D : UniversalRootDatum K) : Prop :=
  ∀ R ∈ fundamentalSubgroups t D, ∀ R' ∈ fundamentalSubgroups t D,
    ∃ g : K, R' = R.map (MulAut.conj g).toMonoidHom

theorem fundamentalSingleClass (t : StatedLieTag) (n p f : ℕ) (hp : p.Prime)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p f) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) : FundamentalSingleClass t (modelUniv t n p f hp).D := by
  rintro R ⟨g₁, γ, hγ, rfl⟩ R' ⟨g₂, γ', hγ', rfl⟩
  have hl : ∀ {x : Fin (modelUniv t n p f hp).D.rank → ℤ},
      (IsLongestRoot (modelUniv t n p f hp).D x ∨ (t = .G2 ∧ x ∈ (modelUniv t n p f hp).D.roots) ∨
        (t = .trialityD4 ∧ x ∈ (modelUniv t n p f hp).D.roots)) →
      IsLongestRoot (modelUniv t n p f hp).D x := by
    rintro x (h | ⟨h, -⟩ | ⟨h, -⟩)
    · exact h
    · exact absurd h hG2
    · exact absurd h hD4
  obtain ⟨h, hh⟩ := exists_conj_of_isLongestRoot t n p f hp hfund hadm (hl hγ) (hl hγ')
  refine ⟨g₂ * h * g₁⁻¹, ?_⟩
  rw [map_conj_map_conj, inv_mul_cancel_right, ← map_conj_map_conj, hh]

theorem exists_partner (t : StatedLieTag) (n p f : ℕ) (hp : p.Prime) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p f) (hpart : HasPartner t n)
    {γ : Fin (modelUniv t n p f hp).D.rank → ℤ} (hγ : IsLongestRoot (modelUniv t n p f hp).D γ) :
    ∃ δ : Fin (modelUniv t n p f hp).D.rank → ℤ, IsLongestRoot (modelUniv t n p f hp).D δ ∧
      IsPartner (modelUniv t n p f hp).D.isFiniteType γ δ := by
  obtain ⟨hirr, hratio⟩ := cartanOK t n p f hp hfund hadm
  exact exists_partner_of_exists _ hirr hratio (exists_longest_partner t n p f hp hfund hadm hpart)
    γ hγ

theorem two_le_rank (t : StatedLieTag) (n p f : ℕ) (hp : p.Prime) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p f) (h1 : ¬ (t = .PSL ∧ n = 2)) (h2 : ¬ (t = .PSU ∧ n = 3)) :
    2 ≤ (modelUniv t n p f hp).D.rank := by
  have : Fact p.Prime := ⟨hp⟩
  have hf : 1 ≤ f := hadm.2.1
  cases t with
  | PSL =>
    have hn : 2 ≤ n := hadm.2.2.1
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have : m + 1 ≠ 2 := fun h => h1 ⟨rfl, h⟩
    show 2 ≤ m
    omega
  | PSU =>
    have hn : 3 ≤ n := hadm.2.2.1
    have : n ≠ 3 := fun h => h2 ⟨rfl, h⟩
    rw [modelUniv_PSU hf]
    show 2 ≤ n / 2
    omega
  | PSp =>
    have hn : 2 ≤ n := hadm.2.2.1
    show 2 ≤ n
    omega
  | POmegaOdd =>
    have hn : 3 ≤ n := hadm.2.2.1
    show 2 ≤ n
    omega
  | POmegaPlus =>
    have hn : 3 ≤ n := by have := hadm.2.2; omega
    rw [modelUniv_POmegaPlus hn]
    show 2 ≤ n
    omega
  | POmegaMinus =>
    have hn : 4 ≤ n := hadm.2.2
    show 2 ≤ n - 1
    omega
  | F4 =>
    show 2 ≤ 4
    decide
  | E6 =>
    show 2 ≤ 6
    decide
  | E7 =>
    show 2 ≤ 7
    decide
  | E8 =>
    show 2 ≤ 8
    decide
  | G2 =>
    show 2 ≤ 2
    decide
  | twistedE6 =>
    show 2 ≤ 4
    decide
  | trialityD4 =>
    show 2 ≤ 2
    decide
  | twistedB2 | twistedG2 | twistedF4 | Tits => exact absurd hfund (by simp [IsFundTag])

theorem mem_roots_of_mem_fundamentalSubgroups {t : StatedLieTag} {D : UniversalRootDatum K}
    {R : Subgroup K} (hR : R ∈ fundamentalSubgroups t D) :
    ∃ (g : K) (γ : Fin D.rank → ℤ), γ ∈ D.roots ∧
      R = (D.rootGroup γ ⊔ D.rootGroup (-γ)).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, γ, hγ, rfl⟩ := hR
  refine ⟨g, γ, ?_, rfl⟩
  rcases hγ with hγ | ⟨-, hγ⟩ | ⟨-, hγ⟩
  exacts [hγ.mem, hγ, hγ]

theorem fundamentalSubgroups_ne_top (t : StatedLieTag) (n p f : ℕ) (hp : p.Prime)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p f) (h1 : ¬ (t = .PSL ∧ n = 2))
    (h2 : ¬ (t = .PSU ∧ n = 3)) :
    ∀ R ∈ fundamentalSubgroups t (modelUniv t n p f hp).D, R ≠ ⊤ := by
  intro R hR
  obtain ⟨g, γ, hγ, rfl⟩ := mem_roots_of_mem_fundamentalSubgroups hR
  obtain ⟨_, _, hct, hext⟩ := hasBruhatDatum t n p f hp hfund hadm
  exact map_conj_ne_top hct hext (two_le_rank t n p f hp hfund hadm h1 h2) hγ g

theorem fundamentalSubgroups_eq_top_PSL_two (p f : ℕ) (hp : p.Prime)
    (hadm : StatedLieAdmissible .PSL 2 p f) :
    ∀ R ∈ fundamentalSubgroups .PSL (modelUniv .PSL 2 p f hp).D, R = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  intro R hR
  obtain ⟨g, γ, hγ, rfl⟩ := mem_roots_of_mem_fundamentalSubgroups hR
  obtain ⟨_, _, hct, -⟩ := hasBruhatDatum .PSL 2 p f hp trivial hadm
  refine map_conj_eq_top_of_subsingleton hct (fun i j => Fin.ext ?_) rfl
    ⟨0, by show 0 < 1; decide⟩ hγ g
  have hi : i.val < 1 := i.2
  have hj : j.val < 1 := j.2
  omega

end CFSG.ClassicalInvolution.ModelFacts
