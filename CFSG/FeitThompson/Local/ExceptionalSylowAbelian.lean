module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.ExceptionalInvariantSylowSeparation
import CFSG.FeitThompson.Local.GlobalMaximalPlaneGeometry
import CFSG.FeitThompson.Local.SigmaCoreNontrivial
import CFSG.FeitThompson.Local.ExceptionalPlaneMaximalElementaryAbelian
import CFSG.FeitThompson.Local.OvergroupJoinsInvariantPrimeSubgroups
import CFSG.FeitThompson.Local.QuotientFittingInvariantComplement
import CFSG.FeitThompson.Local.CoprimePlaneGeneratesSolvableGroup
import CFSG.FeitThompson.Local.OutsideSigmaSylowCentralPrimeElement
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.PrimeCentralizerAbelianCommutatorConjugates
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
import CFSG.FeitThompson.OddOrder.SigmaHallSubgroupNormalizer
import CFSG.FeitThompson.Representations.ZeroFixedSpacePrimeComplementCentralizes
import CFSG.FeitThompson.Representations.CoprimePrimeAutFixedConjugacyClasses
import CFSG.FeitThompson.Foundations.SolvableHallExistence

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G]

theorem smul_subgroup_eq_bot_iff (φ : MulAut G) (X : Subgroup G) : φ • X = ⊥ ↔ X = ⊥ := by
  refine ⟨fun h => ?_, fun h => by rw [h]; simp⟩
  have h2 := congrArg (fun Y : Subgroup G => φ⁻¹ • Y) h
  simpa using h2

theorem smul_eq_self_of_coe_eq_setOf (φ : MulAut G) (n : ℕ) {W Z : Subgroup G}
    (hW : φ • W = W) (hZ : (Z : Set G) = {z | z ∈ W ∧ z ^ n = 1}) : φ • Z = Z := by
  have hmemZ : ∀ y : G, y ∈ Z ↔ (y ∈ W ∧ y ^ n = 1) := fun y => by
    rw [← SetLike.mem_coe, hZ]; exact Iff.rfl
  have hmemW : ∀ y : G, (φ⁻¹ • y) ∈ W ↔ y ∈ W := fun y => by
    rw [← Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hW]
  have hpow : ∀ y : G, (φ⁻¹ • y) ^ n = 1 ↔ y ^ n = 1 := fun y => by
    rw [MulAut.smul_def, ← map_pow]
    refine ⟨fun h => ?_, fun h => by rw [h, map_one]⟩
    simpa using (φ⁻¹ : MulAut G).injective (h.trans (map_one (φ⁻¹ : MulAut G)).symm)
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hmemZ, hmemZ, hmemW, hpow]

theorem exists_line_inf_centralizer_ne_bot [Finite G] {p q : ℕ}
    {A Q : Subgroup G} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    (hAcard : Nat.card ↥A = p ^ 2) (hAexp : ∀ x ∈ A, x ^ p = 1)
    (hQ : IsPGroup q ↥Q) (hQbot : Q ≠ ⊥) (hAQ : A ≤ normalizer (Q : Set G)) :
    ∃ X : Subgroup G, X ≤ A ∧ Nat.card ↥X = p ∧ Q ⊓ centralizer (X : Set G) ≠ ⊥ := by
  have hfp := Fact.mk hp
  have hfq := Fact.mk hq
  have hQnil : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have hQsolv : Group.IsSolvable ↥Q := IsNilpotent.to_isSolvable
  have hpQ : ¬ p ∣ Nat.card ↥Q := by
    obtain ⟨k, hk⟩ := hQ.exists_card_eq
    rw [hk]
    intro hdvd
    exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hdvd)).symm
  have hexp : ∀ a : ↥A, a ^ p = 1 := fun a => Subtype.ext (by simpa using hAexp (a : G) a.2)
  have htop := iSup_autFixedSubgroup_eq_top hp hAcard hexp (conjAction hAQ) hpQ
  obtain ⟨a, ha1, hafix⟩ : ∃ a : ↥A, a ≠ 1 ∧ autFixedSubgroup (conjAction hAQ a) ≠ ⊥ := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    rw [show (⨆ (a : ↥A) (_ : a ≠ 1), autFixedSubgroup (conjAction hAQ a)) = ⊥ from by
      simp only [iSup_eq_bot]
      exact fun a ha => hcon a ha] at htop
    have hnt : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hQbot
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥Q)
    exact hx (Subgroup.mem_bot.1 (htop ▸ Subgroup.mem_top x))
  have hnt : Nontrivial ↥(autFixedSubgroup (conjAction hAQ a)) :=
    (Subgroup.nontrivial_iff_ne_bot _).2 hafix
  obtain ⟨y, hy⟩ := exists_ne (1 : ↥(autFixedSubgroup (conjAction hAQ a)))
  have hcomm : Commute ((a : G)) (((y : ↥Q) : G)) := by
    have h2 : ((conjAction hAQ a (y : ↥Q) : ↥Q) : G) = (((y : ↥Q)) : G) := by
      rw [mem_autFixedSubgroup.1 y.2]
    rw [coe_conjAction_apply] at h2
    change (a : G) * ((y : ↥Q) : G) = ((y : ↥Q) : G) * (a : G)
    calc (a : G) * ((y : ↥Q) : G) = ((a : G) * ((y : ↥Q) : G) * (a : G)⁻¹) * (a : G) := by group
      _ = ((y : ↥Q) : G) * (a : G) := by rw [h2]
  have haG1 : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have haGp : (a : G) ^ p = 1 := hAexp (a : G) a.2
  refine ⟨zpowers (a : G), (zpowers_le).2 a.2, ?_, ?_⟩
  · rw [Nat.card_zpowers, orderOf_eq_prime haGp haG1]
  · intro hbot
    have hyC : ((y : ↥Q) : G) ∈ centralizer ((zpowers (a : G) : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      intro z hz
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
      exact Commute.zpow_left hcomm k
    have hone : ((y : ↥Q) : G) = 1 :=
      Subgroup.mem_bot.1 (hbot ▸ Subgroup.mem_inf.2 ⟨(y : ↥Q).2, hyC⟩)
    exact hy (Subtype.ext (Subtype.ext hone))

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open CFSG.FeitThompson CFSG.FeitThompson
open Subgroup Pointwise

universe u

theorem FTS_exceptional_sylow_abelian
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FPL_low_rank_sylow_central_product.{u})
    (h₃ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_exceptional_sylow_abelian.{u} := by
  intro G _ _ hG p M A₀ A P hc
  have := hG.isSimpleGroup
  have : Fintype G := Fintype.ofFinite G
  have hp : p.Prime := hc.prime
  have hfp := Fact.mk hp
  have hM : IsCoatom M := hc.isCoatom
  have hMin : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hMin6 : Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hAea : IsElementaryAbelian p A :=
    isElementaryAbelian_of_nonempty_mulEquiv_pi hc.isElementaryAbelianPlane
  have hAcard : Nat.card ↥A = p ^ 2 := hc.isElementaryAbelianPlane.natCard hp.ne_zero
  have hAM : A ≤ M := hc.le_of_A.trans hc.le_of_P
  have hPM : P ≤ M := hc.le_of_P
  have hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p := hc.isSylowSubgroupOf.2
  obtain ⟨hrank, hNP, hCAM, hAmax⟩ := exceptional_maximal_plane hG.not_isMulCommutative
    hG.odd_natCard hG.isSolvable hM hp hc.notMem_sigmaPrimes hc.natCard_A₀ hc.le_of_A₀
    hc.le_of_A hc.le_of_P hPcard hAea hAcard hc.normalizer_le
  have hpdvd : p ∣ Nat.card G := by
    have h1 : Nat.card ↥A₀ ∣ Nat.card G := Subgroup.card_subgroup_dvd_card A₀
    rwa [hc.natCard_A₀] at h1
  have hpodd : Odd p := Odd.of_dvd_nat hG.odd_natCard hpdvd
  obtain ⟨-, hSne⟩ := FBG_sigma_core_nontrivial h₁ G hMin M hM
  obtain ⟨q, hqmem⟩ : (Nat.card ↥(sigmaCore M)).primeFactors.Nonempty := by
    rw [Nat.nonempty_primeFactors]
    have h1 : Nat.card ↥(sigmaCore M) ≠ 1 := fun h => hSne (Subgroup.card_eq_one.1 h)
    have h2 : 0 < Nat.card ↥(sigmaCore M) := Nat.card_pos
    omega
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hqmem
  have hqσ : q ∈ sigmaPrimes M := isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) q hqmem
  have hqp : q ≠ p := fun h => hc.notMem_sigmaPrimes (h ▸ hqσ)
  obtain ⟨g, hgN, hgM⟩ := SetLike.not_le_iff_exists.1 hNP
  have hgPeq : MulAut.conj g⁻¹ • P = P := mem_normalizer_iff_conj_smul_eq.1 (inv_mem hgN)
  have hAMg : A ≤ conjBy M g := fun a ha =>
    mem_conjBy.2 (hPM ((mem_normalizer_iff.1 hgN a).1 (hc.le_of_A ha)))
  have hpS : ¬ p ∣ Nat.card ↥(sigmaCore M) := fun hdvd =>
    hc.notMem_sigmaPrimes (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) p
      (Nat.mem_primeFactors.2 ⟨hp, hdvd, Nat.card_pos.ne'⟩))
  have hcop : (Nat.card ↥(sigmaCore M)).Coprime (Nat.card ↥P) := by
    rw [hPcard]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpS).symm
  have hsolvSP : Group.IsSolvable ↥(sigmaCore M ⊔ P) :=
    hG.isSolvable _ fun htop => hM.1 (top_le_iff.1 (htop ▸ sup_le (sigmaCore_le M) hPM))
  have hPnormS : P ≤ normalizer ((sigmaCore M : Subgroup G) : Set G) :=
    hPM.trans (le_normalizer_sigmaCore M)
  have hbotnorm : P ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    intro x _
    rw [mem_normalizer_iff]
    intro y
    simp [Subgroup.mem_bot]
  obtain ⟨Q₁, hQ₁S, hQ₁Hall, -, hPQ₁⟩ :=
    exists_isHallSubgroup_subgroupOf_ge_le_normalizer_of_le_normalizer hsolvSP hPnormS hcop
      ({q} : Set ℕ) bot_le (by rw [Subgroup.card_bot]; exact isPiNumber_one) hbotnorm
  have hQ₁card : Nat.card ↥Q₁ = q ^ (Nat.card ↥(sigmaCore M)).factorization q :=
    natCard_eq_pow_factorization_of_isHallSubgroup_singleton hq hQ₁S hQ₁Hall
  have hfacpos : 0 < (Nat.card ↥(sigmaCore M)).factorization q :=
    hq.factorization_pos_of_dvd Nat.card_pos.ne' (Nat.dvd_of_mem_primeFactors hqmem)
  have hQ₁sylow : IsSylowSubgroupOf q Q₁ (sigmaCore M) := ⟨hQ₁S, hQ₁card⟩
  have hQ₁pg : IsPGroup q ↥Q₁ := IsPGroup.of_card hQ₁card
  have hQ₁bot : Q₁ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hQ₁card
    exact (Nat.one_lt_pow (by omega) hq.one_lt).ne hQ₁card
  set Q₂ : Subgroup G := conjBy Q₁ g with hQ₂def
  have hQ₂eq : Q₂ = MulAut.conj g⁻¹ • Q₁ := rfl
  have hQ₂sylow : IsSylowSubgroupOf q Q₂ (conjBy (sigmaCore M) g) := by
    refine ⟨conjBy_le_conjBy_iff.2 hQ₁S, ?_⟩
    rw [hQ₂def, natCard_conjBy, hQ₁card, natCard_conjBy]
  have hQ₂pg : IsPGroup q ↥Q₂ := IsPGroup.of_card (by rw [hQ₂def, natCard_conjBy, hQ₁card])
  have hQ₂bot : Q₂ ≠ ⊥ := by
    rw [hQ₂eq]
    exact fun h => hQ₁bot ((smul_subgroup_eq_bot_iff _ _).1 h)
  have hAQ₁ : A ≤ normalizer (Q₁ : Set G) := hc.le_of_A.trans hPQ₁
  have hPQ₂ : P ≤ normalizer (Q₂ : Set G) := by
    rw [hQ₂eq]
    exact le_normalizer_conj_pointwise_smul (inv_mem hgN) hPQ₁
  have hAQ₂ : A ≤ normalizer (Q₂ : Set G) := hc.le_of_A.trans hPQ₂
  obtain ⟨-, hdich⟩ := FTS_exceptional_invariant_sylow_separation h₁ h₃ G hG p M A₀ A P hc
    q hqσ g hgM hAMg Q₁ Q₂ hQ₁sylow hQ₂sylow hAQ₁ hAQ₂
  have hAexp : ∀ x ∈ A, x ^ p = 1 := (isElementaryAbelian_iff.1 hAea).2
  obtain ⟨X₁, hX₁A, hX₁card, hX₁ne⟩ :=
    exists_line_inf_centralizer_ne_bot hp hq hqp hAcard hAexp hQ₁pg hQ₁bot hAQ₁
  obtain ⟨X₂, hX₂A, hX₂card, hX₂ne⟩ :=
    exists_line_inf_centralizer_ne_bot hp hq hqp hAcard hAexp hQ₂pg hQ₂bot hAQ₂
  have hX₂Q₁ : Q₁ ⊓ centralizer (X₂ : Set G) = ⊥ :=
    (hdich X₂ hX₂A hX₂card).resolve_right hX₂ne
  have hPab : IsMulCommutative ↥P := by
    by_contra hPnc
    obtain ⟨Z₀, hZ₀set, hZ₀A, hZ₀card, -, htrans⟩ :=
      FPL_global_maximal_plane_geometry h₂ G hMin6 p hp hpodd A P
        hc.isElementaryAbelianPlane
        (fun A' hlt d he => hAmax A' (isElementaryAbelian_of_nonempty_mulEquiv_pi he) hlt)
        ⟨_, hPcard⟩ hc.le_of_A hPnc
        {z : G | z ∈ P ⊓ centralizer (P : Set G) ∧ z ^ p = 1} rfl
    have hWg : MulAut.conj g⁻¹ • (P ⊓ centralizer (P : Set G)) = P ⊓ centralizer (P : Set G) := by
      rw [Subgroup.smul_inf, smul_centralizer_coe, hgPeq]
    have hZ₀g : MulAut.conj g⁻¹ • Z₀ = Z₀ := smul_eq_self_of_coe_eq_setOf _ p hWg hZ₀set
    have hZ₀Q₂ : Q₂ ⊓ centralizer (Z₀ : Set G)
        = MulAut.conj g⁻¹ • (Q₁ ⊓ centralizer (Z₀ : Set G)) := by
      rw [Subgroup.smul_inf, smul_centralizer_coe, hZ₀g, hQ₂eq]
    have hZ₀Q₁bot : Q₁ ⊓ centralizer (Z₀ : Set G) = ⊥ := by
      rcases hdich Z₀ hZ₀A hZ₀card with h | h
      · exact h
      · rw [hZ₀Q₂] at h
        exact (smul_subgroup_eq_bot_iff _ _).1 h
    have hZ₀Q₂bot : Q₂ ⊓ centralizer (Z₀ : Set G) = ⊥ := by
      rw [hZ₀Q₂, hZ₀Q₁bot]; simp
    have hX₁Z : X₁ ≠ Z₀ := fun h => hX₁ne (h ▸ hZ₀Q₁bot)
    have hX₂Z : X₂ ≠ Z₀ := fun h => hX₂ne (h ▸ hZ₀Q₂bot)
    obtain ⟨c, hcmem, hceq⟩ := htrans X₁ X₂ hX₁A hX₂A hX₁card hX₂card hX₁Z hX₂Z
    have hcP : c ∈ P := (Subgroup.mem_inf.1 hcmem).1
    have hQ₁c : MulAut.conj c⁻¹ • Q₁ = Q₁ :=
      mem_normalizer_iff_conj_smul_eq.1 (inv_mem (hPQ₁ hcP))
    have hX₂c : MulAut.conj c⁻¹ • X₁ = X₂ := by rw [conj_smul_eq_map_conj]; exact hceq
    have hkey : Q₁ ⊓ centralizer (X₂ : Set G)
        = MulAut.conj c⁻¹ • (Q₁ ⊓ centralizer (X₁ : Set G)) := by
      rw [Subgroup.smul_inf, smul_centralizer_coe, hX₂c, hQ₁c]
    rw [hkey] at hX₂Q₁
    exact hX₁ne ((smul_subgroup_eq_bot_iff _ _).1 hX₂Q₁)
  refine ⟨hPab, fun Q hQ => ?_⟩
  obtain ⟨m, -, hmeq⟩ := exists_mem_map_conj_eq_of_le hPM hQ.1 hPcard hQ.2
  have e : ↥P ≃* ↥Q := hmeq ▸ P.equivMapOfInjective ((MulAut.conj m : G ≃* G) : G →* G)
    (MulAut.conj m).injective
  exact isMulCommutative_of_mulEquiv e.symm

end

end CFSG.FeitThompson.Proofs
