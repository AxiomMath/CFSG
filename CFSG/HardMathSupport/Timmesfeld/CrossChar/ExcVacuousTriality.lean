module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.LieType.Chevalley.OddTrialityAutomorphismNormalForm
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial
public import CFSG.RankThree.PartOne.K128.D4Syl
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Foundations
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Blueprint
  Polynomial
open CFSG.RankThree.Chevalley
  (exhaustionPhi exact_E_type_and_triality_cross_prime_factor_exhaustion)

@[expose] def regimeTrialityD4 (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ q : TauCeti.PrimePower, idx.1 = .trialityD4 q ∧ ¬ p ∣ q.card ^ 6 - 1

@[expose] def regimeTrialityD4Inner (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ q : TauCeti.PrimePower, idx.1 = .trialityD4 q ∧ 5 ≤ p ∧ ¬ p ∣ q.exponent

@[expose] def regimeTrialityD4Vac (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  regimeTrialityD4 idx p ∨ regimeTrialityD4Inner idx p

theorem card_le_sq_of_pow_eq_one {p a : ℕ} (hp : p.Prime)
    (H : Subgroup (Fin 2 → Multiplicative (ZMod (p ^ a)))) (hH : ∀ h ∈ H, h ^ p = 1) :
    Nat.card H ≤ p ^ 2 := by
  classical
  have : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  let _ : Fintype (Multiplicative (ZMod (p ^ a))) := Fintype.ofFinite _
  have hcyc : Nat.card {x : Multiplicative (ZMod (p ^ a)) // x ^ p = 1} ≤ p := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsCyclic.card_pow_eq_one_le hp.pos
  let ι : H → (Fin 2 → {x : Multiplicative (ZMod (p ^ a)) // x ^ p = 1}) := fun h i =>
    ⟨(h : Fin 2 → Multiplicative (ZMod (p ^ a))) i, by simpa using congrFun (hH h h.2) i⟩
  have hι : Function.Injective ι := fun x y hxy =>
    Subtype.ext (funext fun i => congrArg Subtype.val (congrFun hxy i))
  calc Nat.card H ≤ Nat.card (Fin 2 → {x : Multiplicative (ZMod (p ^ a)) // x ^ p = 1}) :=
        Nat.card_le_card_of_injective ι hι
    _ = Nat.card {x : Multiplicative (ZMod (p ^ a)) // x ^ p = 1} ^ 2 := by
        rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
    _ ≤ p ^ 2 := Nat.pow_le_pow_left hcyc 2

theorem rankLE2_of_sylowShape {T : Type} [Group T] [Finite T] {p a : ℕ} (hp : p.Prime)
    (h : CFSG.RankThree.PartOne.K1214.SylowShape p 2 a T) : RankLE2 p T := by
  intro F hF
  have : Fact p.Prime := ⟨hp⟩
  have hFp : IsPGroup p F := fun g => ⟨1, Subtype.ext (by simpa using hF.2 g g.2)⟩
  obtain ⟨S, hFS⟩ := hFp.exists_le_sylow
  obtain ⟨φ⟩ := h (S : Subgroup T) S.isPGroup' (Sylow.not_dvd_index S)
  have hcard : Nat.card ((F.subgroupOf S).map φ.toMonoidHom) = Nat.card F := by
    rw [Subgroup.card_map_of_injective φ.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFS).toEquiv
  rw [← hcard]
  refine card_le_sq_of_pow_eq_one hp _ ?_
  rintro _ ⟨r, hr, rfl⟩
  rw [← map_pow, show r ^ p = 1 from Subtype.ext (by simpa using hF.2 r.1 hr), map_one]

theorem rankLE2_of_pRank_le_one {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime)
    (h : CFSG.pRank p T ≤ 1) : RankLE2 p T :=
  (rankLE1_of_pRank hp fun _ => h).rankLE2

theorem rankLE2_of_not_dvd {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ Nat.card T) : RankLE2 p T :=
  (rankLE1_of_pRank hp fun hd => absurd hd h).rankLE2

theorem sq_sub_one_dvd_pow_six_sub_one (n : ℕ) : n ^ 2 - 1 ∣ n ^ 6 - 1 := by
  have h := Nat.sub_dvd_pow_sub_pow (n ^ 2) 1 3
  rwa [one_pow, ← pow_mul] at h

theorem dvd_phi12_of_exhaustion {p a m : ℕ} (ha : 1 ≤ a) (hnd : ¬ p ∣ a ^ 6 - 1)
    (hm : m ∈ ({1, 2, 3, 6, 12} : Finset ℕ))
    (hd : (p : ℤ) ∣ (exhaustionPhi m).eval ((a : ℕ) : ℤ)) : p ∣ a ^ 4 - a ^ 2 + 1 := by
  have h6 : ¬ (p : ℤ) ∣ (a : ℤ) ^ 6 - 1 := by
    intro h
    apply hnd
    have h61 : 1 ≤ a ^ 6 := Nat.one_le_pow _ _ ha
    have : (p : ℤ) ∣ ((a ^ 6 - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub h61]
      push_cast
      exact h
    exact Int.natCast_dvd_natCast.1 this
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · exact absurd (hd.trans ⟨((a : ℤ) + 1) * ((a : ℤ) ^ 2 + a + 1) * ((a : ℤ) ^ 2 - a + 1), by
      simp only [exhaustionPhi, eval_sub, eval_X, eval_one]; ring⟩) h6
  · exact absurd (hd.trans ⟨((a : ℤ) - 1) * ((a : ℤ) ^ 2 + a + 1) * ((a : ℤ) ^ 2 - a + 1), by
      simp only [exhaustionPhi, eval_add, eval_X, eval_one]; ring⟩) h6
  · exact absurd (hd.trans ⟨((a : ℤ) - 1) * ((a : ℤ) + 1) * ((a : ℤ) ^ 2 - a + 1), by
      simp only [exhaustionPhi, eval_add, eval_pow, eval_X, eval_one]; ring⟩) h6
  · exact absurd (hd.trans ⟨((a : ℤ) - 1) * ((a : ℤ) + 1) * ((a : ℤ) ^ 2 + a + 1), by
      simp only [exhaustionPhi, eval_add, eval_sub, eval_pow, eval_X, eval_one]; ring⟩) h6
  · have h24 : a ^ 2 ≤ a ^ 4 := Nat.pow_le_pow_right ha (by omega)
    have h1 : (p : ℤ) ∣ ((a ^ 4 - a ^ 2 + 1 : ℕ) : ℤ) := by
      rw [Nat.cast_add, Nat.cast_sub h24]
      push_cast
      simpa only [exhaustionPhi, eval_add, eval_sub, eval_pow, eval_X, eval_one] using hd
    exact Int.natCast_dvd_natCast.1 h1

section Model


theorem exists_catEquiv_trialityD4 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
      Nat.card K = (q.p ^ q.exponent) ^ 3 ∧ (∀ c, σ c = c ^ (q.p ^ q.exponent)) ∧
      (∃ Θ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* (K ≃+* K),
        Θ.ker = (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
          MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) ∧
      Nonempty (Cat ⟨.trialityD4 q, hv⟩ ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let K := GaloisField q.p (3 * q.exponent)
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hKc : Nat.card K = (q.p ^ q.exponent) ^ TwistTag.D4.order := by
    change Nat.card (GaloisField q.p (3 * q.exponent)) = _
    rw [GaloisField.card _ _ (by omega)]
    change _ = (q.p ^ q.exponent) ^ 3
    rw [← pow_mul, mul_comm]
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.D4 q.prime_p hf K hKc
  have hK3 : Nat.card K = (q.p ^ q.exponent) ^ 3 := hKc
  have hΘ : ∃ Θ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* (K ≃+* K),
      Θ.ker = (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range ∧
      Nonempty (DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 K σ.toRingHom) ≃*
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    by_cases h2 : q.p = 2
    · have hK3' : Nat.card K = (2 ^ q.exponent) ^ 3 := by rw [← h2]; exact hK3
      have hσ' : ∀ c, σ c = c ^ (2 ^ q.exponent) := by rw [← h2]; exact hσ
      obtain ⟨-, -, ⟨Θ, -, -, hΘker, -⟩, -, -, -, -, heC⟩ :=
        even_triality_exact_automorphism_normal_form hf K hK3' σ hσ'
      exact ⟨Θ, hΘker, heC⟩
    · obtain ⟨-, -, ⟨Θ, -, -, hΘker, -⟩, -, -, -, -, heC⟩ :=
        odd_triality_exact_automorphism_normal_form q.prime_p h2 hf K hK3 σ hσ
      exact ⟨Θ, hΘker, heC⟩
  obtain ⟨Θ, hΘker, ⟨eC⟩⟩ := hΘ
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hv K
    (by rw [hqc]; exact hK3) σ.toRingHom (fun x => by rw [hqc]; exact hσ x)
  exact ⟨K, inferInstance, inferInstance, σ, hK3, hσ, ⟨Θ, hΘker⟩, ⟨eB.symm.trans eC⟩⟩

theorem rankLE1_cat_trialityD4 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ≠ q.p) (hnd : ¬ p ∣ q.card ^ 6 - 1) : RankLE1 p (Cat ⟨.trialityD4 q, hv⟩) := by
  have hpq' : ¬ p ∣ q.card := not_dvd_card_of_ne hp hpq
  have hp5 : 5 ≤ p := five_le_of_not_dvd_sq_sub_one hp hp2 hpq'
    fun h => hnd (h.trans (sq_sub_one_dvd_pow_six_sub_one _))
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨e⟩⟩ := exists_catEquiv_trialityD4 q hv
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (Cat ⟨.trialityD4 q, hv⟩) := Finite.of_equiv _ e.symm.toEquiv
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  rw [hqc] at hnd
  refine RankLE1.of_mulEquiv e.symm (rankLE1_of_pRank hp fun hdvd => ?_)
  have hdvd' : p ∣ Nat.card (Cat ⟨.trialityD4 q, hv⟩) := by
    rwa [Nat.card_congr e.toEquiv]
  obtain ⟨m, hm, hd⟩ := ((exact_E_type_and_triality_cross_prime_factor_exhaustion hp (by omega)
    (Ne.symm hpq) (chevalleyModel_cat_trialityD4 hv)).1 hdvd').2.2.2.2 rfl
  exact CFSG.RankThree.PartOne.K128.pRank_le_one_D4_twelve q.prime_p q.exponent_pos K hK σ hσ
    hp hp5 (dvd_phi12_of_exhaustion (Nat.one_le_pow _ _ q.prime_p.pos) hnd hm hd)

theorem conj_injective_cat_trialityD4 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) :
    Function.Injective
      (MulAut.conj : Cat ⟨.trialityD4 q, hv⟩ →* MulAut (Cat ⟨.trialityD4 q, hv⟩)) := by
  obtain ⟨K, _, _, σ, -, -, -, ⟨e⟩⟩ := exists_catEquiv_trialityD4 q hv
  exact conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot
    (exceptional_fixed_center_trivial TwistTag.D4 K σ))

theorem crossCharFamAt_trialityD4 : CrossCharFamAt .trialityD4 regimeTrialityD4 := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, hnd⟩
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  obtain ⟨K, _, _, σ, -, -, ⟨Θ, hker⟩, ⟨e⟩⟩ := exists_catEquiv_trialityD4 q hv
  have : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  exact isLocallyBalancedAbs_of_rankLE1 e Θ hp (fun x hx _ => hker ▸ hx)
    (conj_injective_cat_trialityD4 q hv) (rankLE1_cat_trialityD4 q hv hp hp2 hpq hnd)

theorem rankLE2_cat_trialityD4 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ≠ q.p) : RankLE2 p (Cat ⟨.trialityD4 q, hv⟩) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨e⟩⟩ := exists_catEquiv_trialityD4 q hv
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (Cat ⟨.trialityD4 q, hv⟩) := Finite.of_equiv _ e.symm.toEquiv
  refine RankLE2.of_mulEquiv e.symm ?_
  by_cases hdvd : p ∣ Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
  · have hdvd' : p ∣ Nat.card (Cat ⟨.trialityD4 q, hv⟩) := by
      rwa [Nat.card_congr e.toEquiv]
    obtain ⟨m, hm, hd⟩ := ((exact_E_type_and_triality_cross_prime_factor_exhaustion hp (by omega)
      (Ne.symm hpq) (chevalleyModel_cat_trialityD4 hv)).1 hdvd').2.2.2.2 rfl
    have hq1 : 1 ≤ q.p ^ q.exponent := Nat.one_le_pow _ _ q.prime_p.pos
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    by_cases h12 : m = 12
    · subst h12
      have h24 : (q.p ^ q.exponent) ^ 2 ≤ (q.p ^ q.exponent) ^ 4 :=
        Nat.pow_le_pow_right hq1 (by omega)
      have h1 : (p : ℤ) ∣ (((q.p ^ q.exponent) ^ 4 - (q.p ^ q.exponent) ^ 2 + 1 : ℕ) : ℤ) := by
        rw [Nat.cast_add, Nat.cast_sub h24]
        push_cast
        simpa only [exhaustionPhi, eval_add, eval_sub, eval_pow, eval_X, eval_one,
          Nat.cast_pow] using hd
      exact rankLE2_of_pRank_le_one hp
        (CFSG.RankThree.PartOne.K128.pRank_le_one_D4_twelve q.prime_p q.exponent_pos K hK σ hσ
          hp hp5 (Int.natCast_dvd_natCast.1 h1))
    · have hm' : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6 := by omega
      exact rankLE2_of_sylowShape hp
        (CFSG.RankThree.PartOne.K128.sylowShape_D4 q.exponent_pos K hK σ hσ hm' hp hp5
          (CFSG.RankThree.PartOne.K128.dvd_phiNat_of_dvd_cycloVal hq1 hm' hd))
  · exact rankLE2_of_not_dvd hp hdvd

theorem crossCharFamAt_trialityD4_inner : CrossCharFamAt .trialityD4 regimeTrialityD4Inner := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, hp5, hf⟩
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  obtain ⟨K, _, _, σ, hK, -, ⟨Θ, hker⟩, ⟨e⟩⟩ := exists_catEquiv_trialityD4 q hv
  have hK3 : Nat.card K = q.p ^ (q.exponent * 3) := by rw [hK, ← pow_mul]
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      q.prime_p (by have := q.exponent_pos; omega) hK3
  have hcop : Nat.Coprime p (Nat.card (K ≃+* K)) := by
    rw [hcard]
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hp).2 hf)
      ((Nat.coprime_primes hp Nat.prime_three).2 (by omega))
  exact isLocallyBalancedAbs_of_rankLE2 e Θ hp hcop (fun x hx _ => hker ▸ hx)
    (conj_injective_cat_trialityD4 q hv) (rankLE2_cat_trialityD4 q hv hp hp5 hpq)

theorem crossCharFamAt_trialityD4_vac : CrossCharFamAt .trialityD4 regimeTrialityD4Vac :=
  crossCharFamAt_trialityD4.or crossCharFamAt_trialityD4_inner

end Model

end CFSG.HardMathSupport.Timmesfeld.CrossChar
