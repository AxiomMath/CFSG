module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.AbelianAmbientTauTwoFitting
import CFSG.FeitThompson.Local.TauTwoAbelianSylowPropagation
import CFSG.FeitThompson.Local.NonabelianAmbientSingleRankTwoPrime
import CFSG.FeitThompson.Local.AbelianSylowNormalPrimeCentralizerFitting
import CFSG.FeitThompson.Local.ControlledPlaneCentralizersPrimeCore
import CFSG.FeitThompson.Representations.DadeSignalizersCanonicalNormalHall
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G]

theorem coprime_of_forall_prime_not_dvd {a b : ℕ}
    (h : ∀ q : ℕ, q.Prime → q ∣ a → ¬ q ∣ b) : a.Coprime b := by
  rw [Nat.Coprime]
  by_contra hne
  have hp := Nat.minFac_prime hne
  exact h _ hp ((Nat.minFac_dvd _).trans (Nat.gcd_dvd_left a b))
    ((Nat.minFac_dvd _).trans (Nat.gcd_dvd_right a b))

theorem not_dvd_index_of_pow_factorization_dvd {X : Type*} [Group X] [Finite X] {q : ℕ}
    (hq : q.Prime) {K : Subgroup X}
    (hdvd : q ^ (Nat.card X).factorization q ∣ Nat.card ↥K) : ¬ q ∣ K.index := by
  intro hdvdidx
  have hmul : Nat.card ↥K * K.index = Nat.card X := card_mul_index _
  have hidx0 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hle : (Nat.card X).factorization q ≤ (Nat.card ↥K).factorization q :=
    (Nat.Prime.pow_dvd_iff_le_factorization hq Nat.card_pos.ne').1 hdvd
  have h1 : 0 < (K.index).factorization q :=
    Nat.Prime.factorization_pos_of_dvd hq hidx0 hdvdidx
  have hfac := Nat.factorization_mul (a := Nat.card ↥K) (b := K.index) Nat.card_pos.ne' hidx0
  rw [hmul] at hfac
  have h2 := congrArg (fun f => f q) hfac
  simp only [Finsupp.coe_add, Pi.add_apply] at h2
  omega

theorem pow_factorization_dvd_natCard_of_isHallPiSubgroup {X : Type*} [Group X] [Finite X]
    {π : Set ℕ} {K : Subgroup X} (hHall : IsHallPiSubgroup π K) {q : ℕ} (hq : q.Prime)
    (hqπ : q ∈ π) : q ^ (Nat.card X).factorization q ∣ Nat.card ↥K := by
  have hidx0 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hnd : ¬ q ∣ K.index := fun hdvd =>
    hHall.notMem_of_mem_primeFactors_index q (Nat.mem_primeFactors.2 ⟨hq, hdvd, hidx0⟩) hqπ
  have hmul : Nat.card ↥K * K.index = Nat.card X := card_mul_index _
  have hfac := Nat.factorization_mul (a := Nat.card ↥K) (b := K.index) Nat.card_pos.ne' hidx0
  rw [hmul] at hfac
  have h2 := congrArg (fun f => f q) hfac
  simp only [Finsupp.coe_add, Pi.add_apply] at h2
  rw [Nat.factorization_eq_zero_of_not_dvd hnd] at h2
  refine (Nat.Prime.pow_dvd_iff_le_factorization hq Nat.card_pos.ne').2 ?_
  omega

theorem natCard_subgroupOf_eq_natCard_of_le {H K : Subgroup G} (h : H ≤ K) :
    Nat.card ↥(H.subgroupOf K) = Nat.card ↥H :=
  Nat.card_congr (subgroupOfEquivOfLe h).toEquiv

theorem centerIn_fittingIn_eq_centreIn_mixedFitting [Finite G] (E : Subgroup G) :
    centerIn (fittingIn E) = centreIn (mixedFitting E) := by
  have h1 : fittingIn E = mixedFitting E :=
    (rfl : fittingIn E = map E.subtype (fittingRaw ↥E)).trans (mixedFitting_eq E).symm
  have h2 : centerIn (mixedFitting E) = centreIn (mixedFitting E) :=
    (rfl : centerIn (mixedFitting E)
      = map (mixedFitting E).subtype (center ↥(mixedFitting E))).trans
      (centreIn_eq_map_center _).symm
  rw [h1, h2]

theorem exists_sylow_le_centreIn_mixedFitting
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    [Finite G] (hG : IsOddOrderMinimalSimple G) {M E : Subgroup G} (hM : IsCoatom M)
    (hdecomp : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E)
    {p : ℕ} (hp : p ∈ tauTwoPrimes M) (hpab : ∀ R : Sylow p G, IsMulCommutative ↥(R : Subgroup G))
    {q : ℕ} (hq : q ∈ tauTwoPrimes M) :
    ∃ T : Sylow q G, (T : Subgroup G) ≤ centreIn (mixedFitting E) := by
  have hqp : q.Prime := prime_of_mem_tauTwoPrimes hq
  have : Fact q.Prime := ⟨hqp⟩
  have hFBG : IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  let _ : Fintype G := Fintype.ofFinite G
  have hqab : ∀ R : Sylow q G, IsMulCommutative ↥(R : Subgroup G) :=
    FBG_tau_two_ambient_abelian_propagation h₁ h₂ h₃ h₄ h₅ G hG M hM E hdecomp p hp hpab q hq
  obtain ⟨B, hBE, hBplane⟩ := exists_plane_le_of_isInternalSemidirectProduct hq hdecomp
  have hBp : IsPGroup q ↥B := IsPGroup.of_card hBplane.natCard'
  obtain ⟨T, hBT⟩ := hBp.exists_le_sylow
  refine ⟨T, ?_⟩
  have hsetup : IsAbelianAmbientSetup M q B E (T : Subgroup G) :=
    ⟨hM, hqp, notMem_sigmaPrimes_of_mem_tauTwoPrimes hq, hBE.trans hdecomp.right_le, hBplane,
      hdecomp.right_le, hdecomp, hBE, hqab T, ⟨T, rfl⟩, hBT⟩
  obtain ⟨-, -, -, -, -, hTZ⟩ :=
    FBG_abelian_ambient_tau_two_fitting h₁ h₂ h₃ h₄ G hFBG M q B E (T : Subgroup G) hsetup
  exact hTZ

theorem FBG_tau_two_full_central_hall
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FBG_tau_two_full_central_hall.{u} := by
  intro G _ _ hG M hM E hdecomp p hp hpab E₂ hE₂
  set Z : Subgroup G := centreIn (mixedFitting E) with hZdef
  have hZE : Z ≤ E := (centreIn_le _).trans (mixedFitting_le E)
  have hZab : IsMulCommutative ↥Z := isMulCommutative_centreIn _
  have hEnormZ : E ≤ normalizer ((Z : Subgroup G) : Set G) := by
    rw [hZdef, centreIn_eq]
    refine le_normalizer_inf_centralizer_self_of_le_normalizer ?_
    rw [mixedFitting_eq]
    exact le_normalizer_map_subtype_of_characteristic _ le_normalizer
  have hZnormal : (Z.subgroupOf E).Normal := (normal_subgroupOf_iff_le_normalizer hZE).2 hEnormZ
  have hZfull : ∀ q ∈ tauTwoPrimes M, q ^ (Nat.card G).factorization q ∣ Nat.card ↥Z := by
    intro q hq
    have hqp : q.Prime := prime_of_mem_tauTwoPrimes hq
    have : Fact q.Prime := ⟨hqp⟩
    obtain ⟨T, hTZ⟩ :=
      exists_sylow_le_centreIn_mixedFitting h₁ h₂ h₃ h₄ h₅ hG hM hdecomp hp hpab hq
    calc q ^ (Nat.card G).factorization q = Nat.card ↥(T : Subgroup G) :=
          T.card_eq_multiplicity.symm
      _ ∣ Nat.card ↥Z := card_dvd_of_le hTZ
  have hZGdvd : Nat.card ↥Z ∣ Nat.card G := by
    simpa using card_dvd_of_le (H := Z) (K := (⊤ : Subgroup G)) le_top
  have hEGdvd : Nat.card ↥E ∣ Nat.card G := by
    simpa using card_dvd_of_le (H := E) (K := (⊤ : Subgroup G)) le_top
  have hvZG : ∀ q : ℕ, (Nat.card ↥Z).factorization q ≤ (Nat.card G).factorization q := fun q =>
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hZGdvd q
  have hvEG : ∀ q : ℕ, (Nat.card ↥E).factorization q ≤ (Nat.card G).factorization q := fun q =>
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hEGdvd q
  have hvGZ : ∀ q ∈ tauTwoPrimes M,
      (Nat.card G).factorization q ≤ (Nat.card ↥Z).factorization q := by
    intro q hq
    exact (Nat.Prime.pow_dvd_iff_le_factorization (prime_of_mem_tauTwoPrimes hq)
      Nat.card_pos.ne').1 (hZfull q hq)
  have hvGE : ∀ q ∈ tauTwoPrimes M,
      (Nat.card G).factorization q ≤ (Nat.card ↥E).factorization q := by
    intro q hq
    refine (Nat.Prime.pow_dvd_iff_le_factorization (prime_of_mem_tauTwoPrimes hq)
      Nat.card_pos.ne').1 ((hZfull q hq).trans (card_dvd_of_le hZE))
  have hE₂E : E₂ ≤ E := hE₂.1
  have hHallE : IsHallPiSubgroup (tauTwoPrimes M) (E₂.subgroupOf E) := hE₂.2
  have hE₂π : ∀ r ∈ (Nat.card ↥E₂).primeFactors, r ∈ tauTwoPrimes M := by
    intro r hr
    refine isPiSubgroup_iff.1 hHallE.isPiSubgroup r ?_
    rwa [natCard_subgroupOf_eq_natCard_of_le hE₂E]
  have hZidx : ∀ q ∈ tauTwoPrimes M, ¬ q ∣ (Z.subgroupOf E).index := by
    intro q hq
    have hqp : q.Prime := prime_of_mem_tauTwoPrimes hq
    refine not_dvd_index_of_pow_factorization_dvd (X := ↥E) hqp ?_
    rw [natCard_subgroupOf_eq_natCard_of_le hZE]
    exact (pow_dvd_pow q ((hvEG q).trans (hvGZ q hq))).trans (Nat.ordProj_dvd _ _)
  have hE₂Z : E₂ ≤ Z := by
    have hn := hZnormal
    have hcop : (Nat.card ↥(E₂.subgroupOf E)).Coprime (Z.subgroupOf E).index := by
      refine coprime_of_forall_prime_not_dvd fun r hr hrdvd => ?_
      refine hZidx r (hE₂π r (Nat.mem_primeFactors.2 ⟨hr, ?_, Nat.card_pos.ne'⟩))
      rwa [natCard_subgroupOf_eq_natCard_of_le hE₂E] at hrdvd
    have hle : E₂.subgroupOf E ≤ Z.subgroupOf E := le_of_coprime_natCard_index hcop
    calc E₂ = map E.subtype (E₂.subgroupOf E) := (map_subgroupOf_eq_of_le hE₂E).symm
      _ ≤ map E.subtype (Z.subgroupOf E) := map_mono hle
      _ = Z := map_subgroupOf_eq_of_le hZE
  have hE₂ab : IsMulCommutative ↥E₂ := isMulCommutative_of_le hE₂Z
  have hE₂full : ∀ q ∈ tauTwoPrimes M, q ^ (Nat.card G).factorization q ∣ Nat.card ↥E₂ := by
    intro q hq
    have hqp : q.Prime := prime_of_mem_tauTwoPrimes hq
    have h1 : q ^ (Nat.card ↥E).factorization q ∣ Nat.card ↥(E₂.subgroupOf E) :=
      pow_factorization_dvd_natCard_of_isHallPiSubgroup hHallE hqp hq
    rw [natCard_subgroupOf_eq_natCard_of_le hE₂E] at h1
    exact (pow_dvd_pow q (hvGE q hq)).trans h1
  have hHallG : IsHallPiSubgroup (tauTwoPrimes M) E₂ := by
    refine ⟨isPiSubgroup_iff.2 hE₂π, fun r hr hrτ => ?_⟩
    exact not_dvd_index_of_pow_factorization_dvd (prime_of_mem_tauTwoPrimes hrτ)
      (hE₂full r hrτ) (Nat.dvd_of_mem_primeFactors hr)
  have hHallZ : IsHallPiSubgroup (tauTwoPrimes M) (E₂.subgroupOf Z) := by
    refine ⟨isPiSubgroup_iff.2 fun r hr =>
        hE₂π r (by rwa [natCard_subgroupOf_eq_natCard_of_le hE₂Z] at hr),
      fun r hr hrτ => ?_⟩
    have hrp : r.Prime := prime_of_mem_tauTwoPrimes hrτ
    refine not_dvd_index_of_pow_factorization_dvd (X := ↥Z) hrp ?_
      (Nat.dvd_of_mem_primeFactors hr)
    rw [natCard_subgroupOf_eq_natCard_of_le hE₂Z]
    exact (pow_dvd_pow r (hvZG r)).trans (hE₂full r hrτ)
  have hEnormE₂ : E ≤ normalizer ((E₂ : Subgroup G) : Set G) := by
    rw [le_normalizer_iff]
    intro g hg x hx
    have hxZ : x ∈ Z := hE₂Z hx
    have hyZ : g * x * g⁻¹ ∈ Z := (mem_normalizer_iff.1 (hEnormZ hg) x).1 hxZ
    have hord : orderOf (g * x * g⁻¹) = orderOf x := by
      have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
      simpa [MulAut.conj] using this
    have hxdvd : orderOf x ∣ Nat.card ↥E₂ := Subgroup.orderOf_dvd_natCard E₂ hx
    have hYZ : zpowers (g * x * g⁻¹) ≤ Z := (zpowers_le).2 hyZ
    have hYπ : IsPiSubgroup (tauTwoPrimes M) ((zpowers (g * x * g⁻¹)).subgroupOf Z) := by
      refine isPiSubgroup_iff.2 fun r hr => ?_
      rw [natCard_subgroupOf_eq_natCard_of_le hYZ, Nat.card_zpowers, hord] at hr
      exact hE₂π r (Nat.mem_primeFactors.2
        ⟨(Nat.mem_primeFactors.1 hr).1,
          (Nat.dvd_of_mem_primeFactors hr).trans hxdvd, Nat.card_pos.ne'⟩)
    have hle : (zpowers (g * x * g⁻¹)).subgroupOf Z ≤ E₂.subgroupOf Z :=
      hHallZ.le_of_isPiSubgroup hYπ
    have hle' : zpowers (g * x * g⁻¹) ≤ E₂ := by
      calc zpowers (g * x * g⁻¹) = map Z.subtype ((zpowers (g * x * g⁻¹)).subgroupOf Z) :=
            (map_subgroupOf_eq_of_le hYZ).symm
        _ ≤ map Z.subtype (E₂.subgroupOf Z) := map_mono hle
        _ = E₂ := map_subgroupOf_eq_of_le hE₂Z
    exact hle' (mem_zpowers _)
  exact ⟨hE₂Z.trans (le_of_eq (centerIn_fittingIn_eq_centreIn_mixedFitting E).symm), hE₂ab,
    (normal_subgroupOf_iff_le_normalizer hE₂E).2 hEnormE₂, hHallG⟩

end

end CFSG.FeitThompson.Proofs
