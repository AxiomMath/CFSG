module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.KappaFixedPrimeCentralizerSylowUnique
import CFSG.FeitThompson.Local.SignalizerProductComponents
import CFSG.FeitThompson.Local.KappaPrimeLineFixedEquivalence
import CFSG.FeitThompson.Local.NonuniqueScnAuxiliaryPrime
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.PowerCentralizerTiCriterion
import CFSG.FeitThompson.Local.CanonicalSignalizerConjugation
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.SigmaCoreConjugation

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise
open _root_.CFSG.FeitThompson
  _root_.CFSG.FeitThompson.Prep09

variable {G : Type*} [Group G]

theorem centralizer_singleton_le_centralizer_zpowers (x : G) :
    centralizer ({x} : Set G) ≤ centralizer ((zpowers x : Subgroup G) : Set G) := by
  intro h hh
  rw [mem_centralizer_iff] at hh ⊢
  intro g hg
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg
  exact ((Commute.symm (mem_centralizer_singleton_iff.1 hh)).zpow_left n)

variable [Finite G]

theorem exists_prime_dvd_orderOf_mem_of_isPiElement {π : Set ℕ} {y : G} (hy : IsPiElement π y)
    (hy1 : y ≠ 1) : ∃ q : ℕ, q.Prime ∧ q ∣ orderOf y ∧ q ∈ π := by
  obtain ⟨q, hq, hqd⟩ :=
    Nat.exists_prime_and_dvd (n := orderOf y) (by simpa [orderOf_eq_one_iff] using hy1)
  exact ⟨q, hq, hqd,
    isPiElement_iff.1 hy q (Nat.mem_primeFactors.2 ⟨hq, hqd, (orderOf_pos y).ne'⟩)⟩

theorem exists_prime_order_subgroup_le_of_mem {A : Subgroup G} {x : G} (hxA : x ∈ A)
    (hx1 : x ≠ 1) :
    ∃ (q : ℕ) (X : Subgroup G), q.Prime ∧ X ≤ A ∧ Nat.card ↥X = q ∧
      centralizer ({x} : Set G) ≤ centralizer (X : Set G) := by
  obtain ⟨q, hq, hqd⟩ :=
    Nat.exists_prime_and_dvd (n := orderOf x) (by simpa [orderOf_eq_one_iff] using hx1)
  have hqcard : q ∣ Nat.card ↥(zpowers x) := by rw [Nat.card_zpowers]; exact hqd
  obtain ⟨w, hw, hwo⟩ := exists_mem_orderOf_eq_of_dvd hq hqcard
  refine ⟨q, zpowers w, hq, (zpowers_le.2 hw).trans (zpowers_le.2 hxA),
    by rw [Nat.card_zpowers, hwo], ?_⟩
  exact (centralizer_singleton_le_centralizer_zpowers x).trans
    (centralizer_le (SetLike.coe_subset_coe.2 (zpowers_le.2 hw)))

theorem conj_image_smul_coe_sigmaSignalizer (x g : G) :
    (fun a => g⁻¹ * a * g) '' (x • (sigmaSignalizer x : Set G))
      = (g⁻¹ * x * g) • (sigmaSignalizer (g⁻¹ * x * g) : Set G) :=
  conj_image_smul_coe_canonicalSignalizer_sigmaCore x g

theorem sigR_eq_sigmaSignalizer (x : G) : Prep03.sigR x = sigmaSignalizer x := (rfl)

theorem exists_eq_mul_of_mem_sigmaDelta {T : Subgroup G} (hT : IsCoatom T) {z : G}
    (hz : z ∈ Prep03.sigmaDelta T) :
    ∃ a ∈ sigmaSupport G, ∃ r ∈ sigmaSignalizer a, z = a * r := by
  rw [Prep03.sigmaDelta] at hz
  obtain ⟨a, ha, hz⟩ := Set.mem_iUnion₂.1 hz
  obtain ⟨g, hg⟩ := Set.mem_iUnion.1 hz
  have hsm : ({a} : Set G) * (Prep03.sigR a : Set G) = a • (sigmaSignalizer a : Set G) := by
    rw [sigR_eq_sigmaSignalizer, Set.singleton_mul]; rfl
  rw [hsm, Prep03.conjSet, conj_image_smul_coe_sigmaSignalizer] at hg
  obtain ⟨r, hr, hrz⟩ := Set.mem_smul_set.1 hg
  refine ⟨g⁻¹ * a * g, ?_, r, hr, by rw [← hrz]; rfl⟩
  refine mem_sigmaSupport.2 ⟨T.map (MulAut.conj g⁻¹ : G →* G), isCoatom_map_conj hT g⁻¹, ?_, ?_⟩
  · rw [mem_sigmaCore_map_conj_iff, show (g⁻¹)⁻¹ * (g⁻¹ * a * g) * g⁻¹ = a from by group]
    exact ha.1
  · intro h
    exact ha.2 (by simpa [mul_eq_one_iff_eq_inv] using congrArg (fun z => g * z * g⁻¹) h)

theorem tauTwoPrimes_conjSub (g : G) (M : Subgroup G) :
    tauTwoPrimes (conjSub g M) = tauTwoPrimes M := by
  have hc : conjSub g M = MulAut.conj g⁻¹ • M := (conj_smul_eq_map_conj g⁻¹ M).symm
  ext p
  simp only [mem_tauTwoPrimes_iff, sigmaPrimes_conjSub]
  refine and_congr_right fun hp => and_congr_right fun _ => ?_
  rw [hc, elementaryAbelianPRank_conj_smul hp.one_lt]

theorem notMem_tauTwoPrimes_of_mem_kappaPrimes {p : ℕ} {M : Subgroup G}
    (hp : p ∈ kappaPrimes M) : p ∉ tauTwoPrimes M := by
  intro h
  obtain ⟨hpp, hpd, -, S, hcyc, -⟩ := mem_kappaPrimes_iff.1 hp
  have hr : elementaryAbelianPRank p ↥M = 1 :=
    elementaryAbelianPRank_eq_one_of_isCyclic_sylow hpp hpd ⟨S, hcyc⟩
  rw [elementaryAbelianPRank_eq_two_of_mem_tauTwoPrimes h] at hr
  exact absurd hr (by decide)

theorem mem_sigmaConstituents_mul_of_inter_eq_empty {M : Subgroup G} (hM : IsCoatom M)
    {π : Set ℕ} {x y : G} (hx : x ∈ sigmaCore M) (hx1 : x ≠ 1) (hy : IsPiElement π y)
    (hdisj : sigmaPrimes M ∩ π = ∅) (hcomm : Commute x y) :
    x ∈ sigmaConstituents (x * y) := by
  have hx0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have hy0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
  have hxpi : IsPiElement (sigmaPrimes M) x :=
    isPiElement_of_mem_of_isPiSubgroup (isPiSubgroup_sigmaCore M) hx
  have hcop : (orderOf x).Coprime (orderOf y) := hxpi.coprime_orderOf hx0 hy0 hy hdisj
  refine mem_sigmaConstituents.2 ⟨sigmaPrimes M, mem_sigmaPrimeSets_sigmaPrimes hM hx hx1, ?_, hx1⟩
  rw [piConstituent_mul_of_commute_of_coprime hcomm hx0 hy0 hcop,
    hxpi.piConstituent_eq_self hx0, piConstituent_eq_one_of_inter_eq_empty hy0 hy hdisj, mul_one]

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup Pointwise CFSG.FeitThompson
  CFSG.FeitThompson
  CFSG.FeitThompson.Prep09

universe u

theorem FNI_kappa_mixed_elements_avoid_packets
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₃ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₄ : Statements.FTS_sigma_prime_separation.{u})
    (h₅ : Statements.FTS_signalizer_unique_supporting_maximum.{u})
    (h₆ : Statements.FTS_tau_one_fixed_line_centralizer_unique.{u}) :
    Statements.FNI_kappa_mixed_elements_avoid_packets.{u} := by
  intro G _ _ hamb M K hM hκ hKH x hxA hx1 y hyK hy1 T hT hmem
  have hmin : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hamb.odd_natCard, hamb.isSimpleGroup, hamb.not_isMulCommutative, hamb.forall_isSolvable⟩
  have hft : IsFTAmbient G :=
    ⟨hamb.isSimpleGroup, hamb.not_isMulCommutative, hamb.odd_natCard, hamb.forall_isSolvable⟩
  have hxS : x ∈ sigmaCore M := hxA.1
  have hcomm : Commute x y := ((mem_centralizer_iff.1 hxA.2) y hyK).symm
  have hyκ : IsPiElement (kappaPrimes M) y :=
    isPiElement_of_mem_of_isPiSubgroup (isPiSubgroup_iff.2 fun r hr => hKH.2.1 r hr) hyK
  have hdisj : sigmaPrimes M ∩ kappaPrimes M = ∅ :=
    Set.disjoint_iff_inter_eq_empty.1 (disjoint_kappaPrimes_sigmaPrimes M).symm
  have hxΔ : x ∈ sigmaConstituents (x * y) :=
    mem_sigmaConstituents_mul_of_inter_eq_empty hM hxS hx1 hyκ hdisj hcomm
  have hxU : x ∈ sigmaSupport G := mem_sigmaSupport.2 ⟨M, hM, hxS, hx1⟩
  have hsetup : Prep03.IsKappaSetup G M K (Prep03.cent (sigmaCore M) (K : Set G))
      (K ⊔ Prep03.cent (sigmaCore M) (K : Set G)) := ⟨hamb, hM, hκ, hKH, rfl, rfl⟩
  have hfix := FNI_kappa_fixed_prime_centralizer_and_sylow_uniqueness h₁ h₂ h₆ G M K _ _ hsetup
  obtain ⟨q₀, X, hq₀, hXA, hXcard, hXle⟩ := exists_prime_order_subgroup_le_of_mem hxA hx1
  have hCxM : centralizer ({x} : Set G) ≤ M := hXle.trans (hfix.2.1 q₀ X hq₀ hXA hXcard).1
  obtain ⟨a, haU, r, hr, hzar⟩ := exists_eq_mul_of_mem_sigmaDelta hT hmem
  have hpc := FTS_signalizer_product_components h₃ h₄ G hmin a haU
  rcases eq_or_ne r 1 with hr1 | hr1
  ·
    have h1 := (hpc.1 r hr).1 hr1
    rw [hzar, h1] at hxΔ
    have hxa : x = a := hxΔ
    rw [hxa, hr1, mul_one] at hzar
    exact hy1 (by simpa [hxa] using hzar.symm)
  · obtain ⟨hset, hrU, hane⟩ := (hpc.1 r hr).2 hr1
    rw [hzar, hset] at hxΔ
    have harcomm : Commute a r :=
      (mem_centralizer_singleton_iff.1 (sigmaSignalizer_le_centralizer a hr)).symm
    rcases hxΔ with hxa | hxr
    ·
      have hRne : sigmaSignalizer x ≠ ⊥ := by
        intro h
        rw [hxa] at h
        rw [h] at hr
        exact hr1 (by simpa using hr)
      have hcard := (h₃ G hft x hxU).2.2.1
      have hk : 1 < sigmaMultiplicity x := by
        have h1 : Nat.card ↥(sigmaSignalizer x) ≠ 1 := fun hh => hRne (Subgroup.card_eq_one.1 hh)
        have h2 : 0 < Nat.card ↥(sigmaSignalizer x) := Nat.card_pos
        omega
      obtain ⟨-, hall⟩ := h₅ G hmin x hxU hk
      obtain ⟨-, -, hτ, -⟩ := hall M hM hCxM
      obtain ⟨q, hq, hqd, hqσ⟩ := exists_prime_dvd_orderOf_mem_of_isPiElement
        (isPiElement_of_mem_of_isPiSubgroup (isPiSubgroup_sigmaCore M) hxS) hx1
      exact notMem_sigmaPrimes_of_mem_tauTwoPrimes (hτ q hq hqd) hqσ
    ·
      have hya : y = a := by
        have : x * y = x * a := by rw [hzar, hxr, harcomm.eq]
        exact mul_left_cancel this
      have hyU : y ∈ sigmaSupport G := by rw [hya]; exact haU
      have hxRy : x ∈ sigmaSignalizer y := by rw [hya, hxr]; exact hr
      have hRne : sigmaSignalizer y ≠ ⊥ := fun h => hx1 (by simpa [h] using hxRy)
      have hcard := (h₃ G hft y hyU).2.2.1
      have hk : 1 < sigmaMultiplicity y := by
        have h1 : Nat.card ↥(sigmaSignalizer y) ≠ 1 := fun hh => hRne (Subgroup.card_eq_one.1 hh)
        have h2 : 0 < Nat.card ↥(sigmaSignalizer y) := Nat.card_pos
        omega
      obtain ⟨⟨T₀, ⟨hT₀, hCyT₀⟩, -⟩, hall⟩ := h₅ G hmin y hyU hk
      obtain ⟨hReq, -, hτ, -⟩ := hall T₀ hT₀ hCyT₀
      have hxT₀ : x ∈ sigmaCore T₀ := by rw [hReq] at hxRy; exact hxRy.1
      obtain ⟨q, hq, hqd, hqσM⟩ := exists_prime_dvd_orderOf_mem_of_isPiElement
        (isPiElement_of_mem_of_isPiSubgroup (isPiSubgroup_sigmaCore M) hxS) hx1
      have hqσT : q ∈ sigmaPrimes T₀ :=
        isPiElement_iff.1 (isPiElement_of_mem_of_isPiSubgroup (isPiSubgroup_sigmaCore T₀) hxT₀) q
          (Nat.mem_primeFactors.2 ⟨hq, hqd, (orderOf_pos x).ne'⟩)
      have hconj : ∃ g : G, T₀ = conjSub g M := by
        by_contra hc
        have hsep := h₄ G hmin M T₀ hM hT₀ (by simpa using hc)
        rw [Set.eq_empty_iff_forall_notMem] at hsep
        exact hsep q ⟨hqσM, hqσT⟩
      obtain ⟨g, rfl⟩ := hconj
      obtain ⟨q', hq', hq'd, hq'κ⟩ := exists_prime_dvd_orderOf_mem_of_isPiElement hyκ hy1
      exact notMem_tauTwoPrimes_of_mem_kappaPrimes hq'κ
        (by rw [← tauTwoPrimes_conjSub g M]; exact hτ q' hq' hq'd)

end

end CFSG.FeitThompson.Proofs
