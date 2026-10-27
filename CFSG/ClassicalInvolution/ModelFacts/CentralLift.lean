module

public import CFSG.ClassicalInvolution.Generic.StepDefs
public import CFSG.LieType.Steinberg.CentralExt.Families
public import CFSG.LieType.Steinberg.CentralExt.SpinMinus
public import CFSG.LieType.Steinberg.CentralExt.UnitaryHigher
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover
public import CFSG.LieType.Universal.SpinOmega.Kernel
public import CFSG.LieType.Chevalley.PerfectSimpleRoot
public import CFSG.LieType.CentralExt.SL2Lift
public import CFSG.LieType.Steinberg.TwistedD4.Datum
public import CFSG.LieType.Steinberg.TwistedD4.RankOne
public import CFSG.LieType.Steinberg.TwistedD4.Perfect
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
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.ClassicalInvolution.Generic CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin

@[expose] def CentralTwoSplit (K : Type) [Group K] : Prop :=
  ∀ (E : Type) [Group E] [Finite E] (π : E →* K), Function.Surjective π →
    π.ker ≤ Subgroup.center E → IsPGroup 2 π.ker → ∃ σ : K →* E, ∀ x, π (σ x) = x

theorem centralLift_of_centralTwoSplit {p : ℕ}
    (h : p ≠ 2 → ∀ (t : StatedLieTag) (n e : ℕ) (hp : p.Prime), IsFundTag t →
      StatedLieAdmissible t n p e →
      Finite (modelUniv t n p e hp).K ∧ CentralTwoSplit (modelUniv t n p e hp).K) :
    CentralLift p := by
  intro hp2 t n e hp hFT hadm Y G _ _ _ _ _ hnab π ψ hπ hψ hperf h2 hcen hψker
  obtain ⟨hfin, hsplit⟩ := h hp2 t n e hp hFT hadm
  have : Group.IsPerfect Y := hperf
  obtain ⟨α, hα, -, -⟩ := exists_surjective_of_isPerfect hsplit hψ hπ hcen h2
  exact ⟨α, MonoidHom.ext hα⟩

section Models

variable {p e : ℕ} [Fact p.Prime]

theorem ringChar_galoisField_ne_two (hp2 : p ≠ 2) : ringChar (GaloisField p e) ≠ 2 := by
  rw [ringChar.eq (GaloisField p e) p]
  exact hp2

theorem finite_spinGroup_of_ker {σ : Type} [Fintype σ] [DecidableEq σ] {K : Type} [Field K]
    [Finite K] (Q : QuadraticForm K (σ → K)) {x : spinGroup Q}
    (hker : ((spinMatrix Q).ker : Set (spinGroup Q)) = {1, x}) : Finite (spinGroup Q) := by
  rw [MonoidHom.finite_iff_finite_ker_range (spinMatrix Q)]
  refine ⟨?_, inferInstance⟩
  have hfin : ((spinMatrix Q).ker : Set (spinGroup Q)).Finite :=
    hker ▸ (Set.finite_singleton x).insert 1
  exact hfin.to_subtype

end Models

section Splitting

variable {k : Type} [Field k] [Finite k]

theorem centralTwoSplit_specialLinear (m : ℕ) (hk : ringChar k ≠ 2) :
    CentralTwoSplit (Matrix.SpecialLinearGroup (Fin (m + 1)) k) := by
  intro E _ _ π hπ hker h2
  obtain ⟨σ, hσ, -⟩ := sl_central_two_extension_splitting m hk hπ hker h2
  exact ⟨σ, hσ⟩

theorem centralTwoSplit_statedSp (r : ℕ) (hk : ringChar k ≠ 2) :
    CentralTwoSplit (StatedSp r k) := by
  intro E _ _ π hπ hker h2
  obtain ⟨σ, hσ, -⟩ := odd_symplectic_central_two_extension_splitting hk r hπ hker h2
  exact ⟨σ, hσ⟩

theorem centralTwoSplit_spinOdd {n : ℕ} (hn : 3 ≤ n) (hk : ringChar k ≠ 2) :
    CentralTwoSplit (spinGroup (quadOdd n k)) := by
  intro E _ _ π hπ hker h2
  obtain ⟨σ, hσ, -⟩ := spinOdd_central_two_extension_splitting hn hk hπ hker h2
  exact ⟨σ, hσ⟩

theorem centralTwoSplit_spinPlus {n : ℕ} (hn : 3 ≤ n) (hk : ringChar k ≠ 2) :
    CentralTwoSplit (spinGroup (quadPlus n k)) := by
  intro E _ _ π hπ hker h2
  obtain ⟨σ, hσ, -⟩ := spinPlus_central_two_extension_splitting hn hk hπ hker h2
  exact ⟨σ, hσ⟩

theorem centralTwoSplit_spinMinus {n : ℕ} (hn : 4 ≤ n) (hk : ringChar k ≠ 2) {b c : k}
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    CentralTwoSplit (spinGroup (quadMinus n k b c)) := by
  intro E _ _ π hπ hker h2
  obtain ⟨σ, hσ, -⟩ := spinMinus_central_two_extension_splitting hn hk hirr hπ hker h2
  exact ⟨σ, hσ⟩

theorem centralTwoSplit_g2 (hk : ringChar k ≠ 2) :
    CentralTwoSplit (CFSG.Blueprint.Chevalley.adjointGroup .G2 k) := by
  intro E _ _ π hπ hker h2
  obtain ⟨σ, hσ, -⟩ := g2_central_two_extension_splitting hk hπ hker h2
  exact ⟨σ, hσ⟩

theorem centralTwoSplit_f4 (hk : ringChar k ≠ 2) :
    CentralTwoSplit (CFSG.Blueprint.Chevalley.adjointGroup .F4 k) := by
  intro E _ _ π hπ hker h2
  obtain ⟨σ, hσ, -⟩ := f4_central_two_extension_splitting hk hπ hker h2
  exact ⟨σ, hσ⟩

theorem centralTwoSplit_e8 (hk : ringChar k ≠ 2) :
    CentralTwoSplit (CFSG.Blueprint.Chevalley.adjointGroup .E8 k) := by
  intro E _ _ π hπ hker h2
  obtain ⟨σ, hσ, -⟩ := e8_central_two_extension_splitting hk hπ hker h2
  exact ⟨σ, hσ⟩

theorem centralTwoSplit_e6 (hk : ringChar k ≠ 2) :
    CentralTwoSplit (Minuscule.e6Data_valid.minGroup k) := by
  intro E _ _ π hπ hker h2
  obtain ⟨σ, hσ, -⟩ := e6_central_two_extension_splitting hk hπ hker h2
  exact ⟨σ, hσ⟩

theorem centralTwoSplit_e7 (hk : ringChar k ≠ 2) :
    CentralTwoSplit (Minuscule.e7Data_valid.minGroup k) := by
  intro E _ _ π hπ hker h2
  obtain ⟨σ, hσ, -⟩ := e7_central_two_extension_splitting hk hπ hker h2
  exact ⟨σ, hσ⟩

theorem centralTwoSplit_SU {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) {n : ℕ} (hn : 2 ≤ n) :
    CentralTwoSplit (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F p f) n) := by
  intro E _ _ π hπ hker h2
  obtain ⟨σ, hσ, -⟩ := su_central_two_extension_splitting hF hp2 hn hπ hker h2
  exact ⟨σ, hσ⟩

end Splitting

section Dispatch

variable {p : ℕ} {t : StatedLieTag} {n e : ℕ}

theorem finite_and_centralTwoSplit_modelUniv (hp2 : p ≠ 2) (hp : p.Prime) (hFT : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) (hE6 : t ≠ .twistedE6) (hD4 : t ≠ .trialityD4) :
    Finite (modelUniv t n p e hp).K ∧ CentralTwoSplit (modelUniv t n p e hp).K := by
  have : Fact p.Prime := ⟨hp⟩
  have he : 1 ≤ e := hadm.2.1
  have hk : ringChar (GaloisField p e) ≠ 2 := ringChar_galoisField_ne_two hp2
  have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  cases t with
  | PSL =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
    exact ⟨(inferInstance : Finite (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField p e))),
      centralTwoSplit_specialLinear m hk⟩
  | PSU =>
    have hn : 3 ≤ n := hadm.2.2.1
    have hcard2 : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 :=
      card_galoisField_two_mul p e he
    have h : modelUniv .PSU n p e hp =
        ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField p (2 * e)) p e) n,
          Unitary.rootDatum (card_galoisField_two_mul p e he) n⟩ := by
      simp only [modelUniv, lieUniversal, he, ↓reduceDIte]
    rw [h]
    exact ⟨inferInstance, centralTwoSplit_SU hcard2 hp2 (by omega)⟩
  | PSp =>
    exact ⟨(inferInstance : Finite (StatedSp n (GaloisField p e))), centralTwoSplit_statedSp n hk⟩
  | POmegaOdd =>
    have hn : 3 ≤ n := hadm.2.2.1
    have h2 : (2 : GaloisField p e) ≠ 0 := Ring.two_ne_zero hk
    exact ⟨finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2),
      centralTwoSplit_spinOdd hn hk⟩
  | POmegaPlus =>
    have hn : 4 ≤ n := hadm.2.2
    have : NeZero n := ⟨by omega⟩
    have h : modelUniv .POmegaPlus n p e hp =
        ⟨spinGroup (quadPlus n (GaloisField p e)),
          Spin.plusDatum n (GaloisField p e) (by omega)⟩ := by
      simp only [modelUniv, lieUniversal, show 3 ≤ n by omega, ↓reduceDIte]
    rw [h]
    exact ⟨finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus,
      centralTwoSplit_spinPlus (by omega) hk⟩
  | POmegaMinus =>
    have hn : 4 ≤ n := hadm.2.2
    exact ⟨finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus (minusCoeffs_irr p e)),
      centralTwoSplit_spinMinus hn hk (minusCoeffs_irr p e)⟩
  | G2 => exact ⟨Chevalley.generated_group_finite .G2 _, centralTwoSplit_g2 hk⟩
  | F4 => exact ⟨Chevalley.generated_group_finite .F4 _, centralTwoSplit_f4 hk⟩
  | E8 => exact ⟨Chevalley.generated_group_finite .E8 _, centralTwoSplit_e8 hk⟩
  | E6 =>
    have : Finite (Module.End (GaloisField p e) (Fin Minuscule.e6Data.d →₀ GaloisField p e)) :=
      Module.finite_of_finite (GaloisField p e)
    exact ⟨(inferInstance : Finite ↥(Minuscule.e6Data_valid.minGroup (GaloisField p e))),
      centralTwoSplit_e6 hk⟩
  | E7 =>
    have : Finite (Module.End (GaloisField p e) (Fin Minuscule.e7Data.d →₀ GaloisField p e)) :=
      Module.finite_of_finite (GaloisField p e)
    exact ⟨(inferInstance : Finite ↥(Minuscule.e7Data_valid.minGroup (GaloisField p e))),
      centralTwoSplit_e7 hk⟩
  | twistedE6 => exact absurd rfl hE6
  | trialityD4 => exact absurd rfl hD4
  | twistedB2 => exact hFT.elim
  | twistedG2 => exact hFT.elim
  | twistedF4 => exact hFT.elim
  | Tits => exact hFT.elim

end Dispatch

theorem centralLift_of_twisted {p : ℕ}
    (hE6 : p ≠ 2 → ∀ (n e : ℕ) (hp : p.Prime), StatedLieAdmissible .twistedE6 n p e →
      Finite (modelUniv .twistedE6 n p e hp).K ∧ CentralTwoSplit (modelUniv .twistedE6 n p e hp).K)
    (hD4 : p ≠ 2 → ∀ (n e : ℕ) (hp : p.Prime), StatedLieAdmissible .trialityD4 n p e →
      Finite (modelUniv .trialityD4 n p e hp).K ∧
        CentralTwoSplit (modelUniv .trialityD4 n p e hp).K) :
    CentralLift p := by
  refine centralLift_of_centralTwoSplit fun hp2 t n e hp hFT hadm => ?_
  by_cases hE : t = .twistedE6
  · subst hE
    exact hE6 hp2 n e hp hadm
  by_cases hD : t = .trialityD4
  · subst hD
    exact hD4 hp2 n e hp hadm
  exact finite_and_centralTwoSplit_modelUniv hp2 hp hFT hadm hE hD

section TwistedD4

open CFSG.LieType.Steinberg.TwistedD4 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.CurtisTits

variable {K : Type} [Field K]

theorem xPar_pow' {τ : Tag} {F : RootOperatorFamily τ} (γ : Fin τ.rank → ℤ) (c : K) (n : ℕ) :
    (xPar F γ c) ^ n = xPar F γ (n • c) := by
  induction n with
  | zero => simp [xPar_zero]
  | succ n ih => rw [pow_succ, ih, ← xPar_add, succ_nsmul]

theorem isPGroup_twistedRootGroup (σ : K →+* K) (hσ : ∀ c, σ (σ (σ c)) = c) {p : ℕ}
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
      rw [hc, xPar_pow', hpc, xPar_zero]
    · obtain ⟨c, hc⟩ := (mem_twistedRootSubgroupD4_iff_of_orbit hσ hα hproj hfix _).1 hg
      have hadd : ∀ n : ℕ, xOrbit σ α c ^ n = xOrbit σ α (n • c) := fun n => by
        induction n with
        | zero => simp [xOrbit_zero]
        | succ n ih => rw [pow_succ, ih, ← xOrbit_add σ hα hfix, succ_nsmul]
      rw [hc, hadd, hpc, xOrbit_zero]
  have hdvd : orderOf (⟨x, hx⟩ : twistedRootGroup σ β) ∣ p := orderOf_dvd_of_pow_eq_one hxp
  rcases (Nat.dvd_prime Fact.out).1 hdvd with h | h
  · exact ⟨0, by rw [h, pow_zero]⟩
  · exact ⟨1, by rw [h, pow_one]⟩

section Rank

variable (σ : K →+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

theorem rankOne_long_le_range_slLong :
    rankOne (twistedRootGroup σ) (ng 0) ≤ (slLong σ hσ).range := by
  refine sup_le (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨c, hc, hxc⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ (isRoot_single d4 (nd 2))
      proj_single_two rho_single_two _).1 ((mem_twistedRootGroup (σ := σ)).1 hx)
    exact ⟨sl2Upper ⟨c, hc⟩, Subtype.ext (by rw [slLong_val, slLongE_upper]; exact hxc.symm)⟩
  · obtain ⟨c, hc, hxc⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ (isRoot_neg_single d4 (nd 2))
      proj_neg_single_two rho_neg_single_two _).1 ((mem_twistedRootGroup (σ := σ)).1 hx)
    exact ⟨sl2Lower ⟨c, hc⟩, Subtype.ext (by rw [slLong_val, slLongE_lower]; exact hxc.symm)⟩

theorem range_slShort : (slShort σ hσ).range = (phiShortTw σ hσ).range := by
  rw [slShort, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (MulEquiv.surjective _), Subgroup.map_top]

theorem rankOne_short_le_range_slShort :
    rankOne (twistedRootGroup σ) (ng 1) ≤ (slShort σ hσ).range := by
  rw [range_slShort]
  exact rankOne_short_le_range hσ

end Rank

theorem centralTwoSplit_twistedD4 [Finite K] (σ : K →+* K) (hσ : ∀ c, σ (σ (σ c)) = c)
    (hk : ringChar K ≠ 2) : CentralTwoSplit (twistedGroup σ) := by
  intro E _ _ π hπ hker h2
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  have hX : ∀ γ ∈ (twistedDatum σ).roots,
      IsPGroup (ringChar K) ((twistedDatum σ).rootGroup γ) := fun γ hγ =>
    isPGroup_twistedRootGroup σ hσ (isRoot_of_mem_twistedDatum_roots σ hγ)
  have hkF : ringChar (fixedField σ) ≠ 2 := by
    rw [ringChar.eq (fixedField σ) (ringChar K)]
    exact hk
  have hrank : ∀ i, ∃ φ : ↥(rankOne (twistedDatum σ).rootGroup i) →* E, ∀ x, π (φ x) = x := by
    intro i
    match i with
    | ⟨0, _⟩ =>
      obtain ⟨β, hβ⟩ := CFSG.LieType.CentralExt.exists_lift hkF hπ hker h2 (slLong σ hσ)
      exact exists_lift_of_injective (slLong_injective hσ)
        (rankOne_long_le_range_slLong σ hσ) fun g => DFunLike.congr_fun hβ g
    | ⟨1, _⟩ =>
      obtain ⟨β, hβ⟩ := CFSG.LieType.CentralExt.exists_lift hk hπ hker h2 (slShort σ hσ)
      exact exists_lift_of_injective (slShort_injective hσ)
        (rankOne_short_le_range_slShort σ hσ) fun g => DFunLike.congr_fun hβ g
  obtain ⟨s, hs, -⟩ := existsUnique_section_of_rankOne_lift (twistedDatum_isCTGroupDatum σ hσ)
    (twistedDatum_steinbergExtras σ hσ) hX hπ hker (not_ringChar_dvd_card_ker hk h2) hrank
  exact ⟨s, hs⟩

end TwistedD4

theorem finite_and_centralTwoSplit_modelUniv_twistedD4 {p n e : ℕ} (hp2 : p ≠ 2) (hp : p.Prime)
    (hadm : StatedLieAdmissible .trialityD4 n p e) :
    Finite (modelUniv .trialityD4 n p e hp).K ∧
      CentralTwoSplit (modelUniv .trialityD4 n p e hp).K := by
  have : Fact p.Prime := ⟨hp⟩
  have he : 1 ≤ e := hadm.2.1
  have hK : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  have hσq : ∀ c : GaloisField p (3 * e), iterateFrobenius (GaloisField p (3 * e)) p e c =
      c ^ p ^ e := fun c => iterateFrobenius_def p e c
  have hσ := TwistedD4.sigma_three_of_card hK hσq
  have hk : ringChar (GaloisField p (3 * e)) ≠ 2 := ringChar_galoisField_ne_two hp2
  have := Chevalley.generated_group_finite TwistedD4.d4 (GaloisField p (3 * e))
  exact ⟨(inferInstance : Finite ↥(TwistedD4.twistedGroup
      (iterateFrobenius (GaloisField p (3 * e)) p e))),
    centralTwoSplit_twistedD4 _ hσ hk⟩

end CFSG.ClassicalInvolution.ModelFacts
