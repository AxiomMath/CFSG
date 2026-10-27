module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Local.GlobalMaximalPlaneGeometry
import CFSG.FeitThompson.Foundations.SolvableHallExistence
import CFSG.FeitThompson.Local.MaximalIntersectionSylowNormalizerControl
public import Mathlib.Topology.Sheaves.Presheaf

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G] {p : ℕ}

theorem not_dvd_natCard_sigmaCore_of_notMem_sigmaPrimes [Finite G] {M : Subgroup G} (hp : p.Prime)
    (hpM : p ∉ sigmaPrimes M) : ¬ p ∣ Nat.card (sigmaCore M) := fun hdvd =>
  hpM (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) p
    (Nat.mem_primeFactors.2 ⟨hp, hdvd, Nat.card_pos.ne'⟩))

theorem le_centralizer_of_isMulCommutative_of_le {P A : Subgroup G} (hP : IsMulCommutative ↥P)
    (hAP : A ≤ P) : P ≤ centralizer (A : Set G) := by
  intro x hx
  refine mem_centralizer_iff.2 fun a ha => ?_
  have := hP.is_comm.comm (⟨a, hAP ha⟩ : ↥P) ⟨x, hx⟩
  simpa using congrArg Subtype.val this

theorem forall_not_nonempty_mulEquiv_of_maximal {A : Subgroup G}
    (hA : Maximal (IsElementaryAbelianSubgroup p) A) :
    ∀ A' : Subgroup G, A < A' → ∀ d : ℕ,
      ¬ Nonempty (↥A' ≃* (Fin d → Multiplicative (ZMod p))) := by
  intro A' hlt d ⟨f⟩
  exact absurd (hA.2 (isElementaryAbelianSubgroup_of_mulEquiv f).1 hlt.le) hlt.not_ge

theorem odd_of_prime_of_dvd_odd {n : ℕ} (hp : p.Prime) (hodd : Odd n) (hdvd : p ∣ n) : Odd p := by
  rcases hp.eq_two_or_odd' with h2 | h
  · exact absurd (h2 ▸ hdvd) (by simpa [Nat.two_dvd_ne_zero, Nat.odd_iff] using hodd)
  · exact h

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson

universe u

theorem FNI_nonabelian_ambient_plane_centralizer
    (h₁ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FPL_low_rank_sylow_central_product.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_ambient_plane_centralizer.{u} := by
  intro G _ _ hG p M A E P R hsetup hnonab hP hAP hR hPR
  have hp : p.Prime := hsetup.prime
  have hfp := Fact.mk hp
  have hG4 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
  have hG6 : _root_.CFSG.FeitThompson.Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
  have hsemi : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E :=
    ⟨hsetup.decomp.2.2.2.1, hsetup.decomp.2.2.1, disjoint_iff.2 hsetup.decomp.2.2.2.2⟩
  have hOSP : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane p M A :=
    ⟨hsetup.isCoatom, hp, hsetup.notMem_sigma, hsetup.le_M_A, hsetup.isPlane⟩
  have hSC : _root_.CFSG.FeitThompson.IsSigmaComplement M E := ⟨hsetup.isCoatom, hsemi⟩
  have hAE : A ≤ E := hsetup.le_E_A
  have h0 : (Nat.card ↥(sigmaCore M)).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd
      (not_dvd_natCard_sigmaCore_of_notMem_sigmaPrimes hp hsetup.notMem_sigma)
  have hfact : (Nat.card ↥M).factorization p = (Nat.card ↥E).factorization p := by
    rw [hsemi.natCard_eq_mul, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
      Finsupp.add_apply, h0, zero_add]
  have hPM : P ≤ M := hP.1.trans hSC.le
  have hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p := by rw [hfact]; exact hP.2
  have hPsyl : _root_.CFSG.FeitThompson.IsSylowIn p M P :=
    (_root_.CFSG.FeitThompson.isSylowIn_iff_natCard hp hPM).2 hPcard
  obtain ⟨-, hAmax, hsylP, -⟩ := h₂ G hG4 p M A hOSP
  have hPcomm : IsMulCommutative ↥P := (hsylP P hPsyl).1
  obtain ⟨Q, hQ, hQnc⟩ := hnonab
  have hRnc : ¬ IsMulCommutative ↥R := by
    intro hc
    obtain ⟨g, hg⟩ := exists_conj_smul_eq (P := Q) (Q := R) hQ hR
    exact hQnc (isMulCommutative_of_mulEquiv
      ((Subgroup.equivSMul (MulAut.conj g) Q).trans (MulEquiv.subgroupCongr hg)))
  have hPltR : P < R := lt_of_le_of_ne hPR fun h => hRnc (h ▸ hPcomm)
  have hRp : IsPGroup p ↥R := IsPGroup.of_card hR
  have hRM : R ⊓ M = P := by
    refine (Subgroup.eq_of_le_of_card_ge (le_inf hPR hPM) ?_).symm
    rw [hPcard]
    exact natCard_le_pow_factorization_of_isPGroup hp inf_le_right (hRp.to_le inf_le_left)
  have hCA : centralizer (A : Set G) ≤ E := (h₁ G hG4 p M A E hOSP hSC hAE).2.2.1
  have hCRA : R ⊓ centralizer (A : Set G) = P := by
    refine le_antisymm ?_ (le_inf hPR (le_centralizer_of_isMulCommutative_of_le hPcomm hAP))
    rw [← hRM]
    exact inf_le_inf_left R (hCA.trans hSC.le)
  refine ⟨hPcomm, hRnc, hPltR, hRM, hCRA, ?_⟩
  have hAcard : Nat.card ↥A = p ^ 2 := hOSP.isElementaryAbelianPlane.natCard'
  have hpodd : Odd p :=
    odd_of_prime_of_dvd_odd hp hG.odd_natCard
      (dvd_trans (hAcard ▸ dvd_pow_self p two_ne_zero) (Subgroup.card_subgroup_dvd_card A))
  intro Z₀ hZ₀
  obtain ⟨Z, hZset, hZA, hZcard, -, htrans⟩ :=
    FPL_global_maximal_plane_geometry h₃ G hG6 p hp hpodd A R hsetup.isPlane
      (forall_not_nonempty_mulEquiv_of_maximal hAmax) ⟨_, hR⟩ (hAP.trans hPR) hRnc
      {z | z ∈ R ⊓ centralizer (R : Set G) ∧ z ^ p = 1} rfl
  have hZeq : Z₀ = Z := SetLike.coe_injective (by rw [hZ₀, hZset]; rfl)
  subst hZeq
  refine ⟨hZA, hZcard, ?_⟩
  intro B₁ B₂ hB₁ hB₂ hc₁ hc₂ hn₁ hn₂
  obtain ⟨g, hg, hgeq⟩ := htrans B₁ B₂ hB₁ hB₂ hc₁ hc₂ hn₁ hn₂
  exact ⟨g, by rwa [inf_comm], hgeq⟩

end

end CFSG.FeitThompson.Proofs
