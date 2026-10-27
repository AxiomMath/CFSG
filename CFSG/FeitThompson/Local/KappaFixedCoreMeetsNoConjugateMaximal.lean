module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.KappaFixedPrimeCentralizerSylowUnique
import CFSG.FeitThompson.Local.KappaResidualComplementNormalizerEscape
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity
import CFSG.FeitThompson.OddOrder.MaximalSubgroupsSelfNormalizing
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep03

universe u

theorem FTS_kappa_fixed_core_outside_conjugate_disjoint
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₃ : Statements.FTS_tau_one_fixed_line_centralizer_unique.{u}) :
    Statements.FTS_kappa_fixed_core_outside_conjugate_disjoint.{u} := by
  intro G _ _ hG M hM hκ K hK g hg
  have hsimple := hG.isSimpleGroup
  have : Fintype G := Fintype.ofFinite G
  have hMco : IsCoatom M := hM
  have hfix := FNI_kappa_fixed_prime_centralizer_and_sylow_uniqueness h₁ h₂ h₃
  have hsetup : IsKappaSetup G M K (sigmaCore M ⊓ centralizer (K : Set G))
      (K ⊔ (sigmaCore M ⊓ centralizer (K : Set G))) :=
    { ambient := ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
      isCoatom := hMco
      kappa_nonempty := hκ
      isHall_K := isHallPiOf_of_isHallPiSubgroupOf hK
      A_eq := rfl
      Z_eq := rfl }
  have hcent := (hfix G M K _ _ hsetup).2.1
  by_contra hne
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd
    (n := Nat.card ↥((sigmaCore M ⊓ centralizer (K : Set G)) ⊓ conjBy M g))
    (fun h => hne (Subgroup.card_eq_one.1 h))
  obtain ⟨x, hx, hxo⟩ := exists_mem_orderOf_eq_of_dvd hq hqdvd
  have hPcard : Nat.card ↥(zpowers x) = q := by rw [Nat.card_zpowers, hxo]
  have hPle : zpowers x ≤ (sigmaCore M ⊓ centralizer (K : Set G)) ⊓ conjBy M g := zpowers_le.2 hx
  have hPA : zpowers x ≤ sigmaCore M ⊓ centralizer (K : Set G) := hPle.trans inf_le_left
  have hPg : zpowers x ≤ conjBy M g := hPle.trans inf_le_right
  have hPS : zpowers x ≤ sigmaCore M := hPA.trans inf_le_left
  have hPM : zpowers x ≤ M := hPS.trans (sigmaCore_le M)
  have hqσ : q ∈ sigmaPrimes M :=
    isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) q (Nat.mem_primeFactors.2
      ⟨hq, hPcard ▸ Subgroup.card_dvd_of_le hPS, Nat.card_pos.ne'⟩)
  have hPp : IsPGroup q ↥(zpowers x) := IsPGroup.of_card (n := 1) (by simpa using hPcard)
  obtain ⟨c, hcP, hcconj⟩ := exists_mem_centralizer_conj_smul_of_mem_sigmaPrimes
    hG.not_isMulCommutative hG.odd_natCard hG.isSolvable hMco hqσ hPp
    (a := 1) (b := g⁻¹) (by simpa using hPM) hPg
  have hcM : c ∈ M := (hcent q (zpowers x) hq hPA hPcard).1 hcP
  have hconj : MulAut.conj g⁻¹ • M = M := by
    rw [← hcconj, map_one, one_smul, Subgroup.conj_smul_eq_self_of_mem hcM]
  exact hg (normalizer_coe_eq_of_isCoatom hG.not_isMulCommutative hMco ▸
    mem_normalizer_iff_conj_inv_smul_eq.2 hconj)

end

end CFSG.FeitThompson.Proofs
