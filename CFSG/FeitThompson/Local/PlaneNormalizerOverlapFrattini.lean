module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
import CFSG.FeitThompson.Local.SigmaComplementPlaneActionSupport
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.SigmaComplementThreeHallFactors
import CFSG.FeitThompson.Local.SylowInterNormalSylowOrder
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise CFSG.FeitThompson CFSG.FeitThompson
  Subgroup

universe u

variable {G : Type u} [Group G]

theorem normalizer_le_normalizer_of_le_of_isCyclic {D Q₀ : Subgroup G} [Finite D] [IsCyclic D]
    (hQ : Q₀ ≤ D) : normalizer (D : Set G) ≤ normalizer (Q₀ : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  refine eq_of_le_of_natCard_eq_of_isCyclic (A := D) ?_ hQ ?_
  · rw [← hg]; exact Subgroup.map_mono hQ
  · exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem FNI_plane_normalizer_overlap_frattini
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_hall_abelian.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_plane_normalizer_overlap_frattini.{u} := by
  intro G _ _ hG p M A E T hosp hsc hAE _hT _hNT q hq hqidx _hqcard Q₀ Q hQ₀ _hQ₀card hQsyl hQ₀Q
  have hG' : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hqf := Fact.mk hq
  obtain ⟨hEA, -, hCE, -, -⟩ := h₃ G hG p M A E hosp hsc hAE
  set C : Subgroup G := centralizer (A : Set G)
  set N : Subgroup G := normalizer (A : Set G)
  have hCD : C = E ⊓ C := (inf_eq_right.2 hCE).symm
  have hNC : N ≤ normalizer (C : Set G) := normalizer_le_normalizer_centralizer A
  have hEN : E ≤ normalizer (C : Set G) := hEA.trans hNC
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  obtain ⟨E₁, E₂, E₃, hsplit, -⟩ := FNI_sigma_complement_three_factors h₁ G hG M E hsc
  have hsupport := sigma_complement_plane_action_support h₂ h₃ h₄ hG' hosp.isCoatom
    hosp.prime hosp.notMem_sigmaPrimes hosp.le hosp.isElementaryAbelianPlane
    hsc.isInternalSemidirectProduct hAE
    ⟨hsplit.le_E₁, hsplit.isHall_E₁⟩ ⟨hsplit.le_E₂, hsplit.isHall_E₂⟩
    ⟨hsplit.le_E₃, hsplit.isHall_E₃⟩ hsplit.outer hsplit.inner
  have hidxne : (E ⊓ C).relIndex E ≠ 0 := by
    rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite
  have hτ₁ : q ∈ tau1Primes M :=
    hsupport.2.2 q (Nat.mem_primeFactors.2 ⟨hq, hqidx, hidxne⟩)
  obtain ⟨S, hS⟩ := hQsyl
  obtain ⟨-, -, -, -, -, hπ₁, -, -⟩ := FNI_sigma_complement_prime_data h₁ G hG M E hsc
  have hQcyc : IsCyclic Q := by
    rw [← hS]
    exact isCyclic_map_subtype ((hπ₁ ▸ hτ₁ : q ∈ _root_.CFSG.FeitThompson.piOnePrimes' ↥E).2.1 S)
  have hCnormalE : ((C.subgroupOf E)).Normal := normal_subgroupOf_of_le_normalizer hEN
  have hScard := natCard_inf_sylow (p := q) (C.subgroupOf E) S
  have hmapinf : Subgroup.map E.subtype ((C.subgroupOf E) ⊓ (S : Subgroup ↥E)) = C ⊓ Q := by
    rw [Subgroup.map_inf _ _ _ E.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hCE, hS]
  have hQCcard : Nat.card ↥(Q ⊓ C) = q ^ (Nat.card ↥C).factorization q := by
    rw [inf_comm, ← hmapinf, Subgroup.card_map_of_injective E.subtype_injective, hScard,
      natCard_subgroupOf hCE]
  have hSylC : _root_.CFSG.FeitThompson.IsSylowIn q C (Q ⊓ C) :=
    (_root_.CFSG.FeitThompson.isSylowIn_iff_natCard hq (inf_le_right : Q ⊓ C ≤ C)).2 hQCcard
  have hQ₀QC : Q₀ ≤ Q ⊓ C := le_inf hQ₀Q (hQ₀.trans inf_le_right)
  have hQCcyc : IsCyclic ↥(Q ⊓ C) := by
    have := hQcyc
    exact Subgroup.isCyclic_of_le (inf_le_left : Q ⊓ C ≤ Q)
  have hQCN : Q ⊓ C ≤ N := (inf_le_right : Q ⊓ C ≤ C).trans hCN
  have hCnormalN : ((C.subgroupOf N)).Normal := normal_subgroupOf_of_le_normalizer hNC
  have hPle : (Q ⊓ C).subgroupOf N ≤ C.subgroupOf N := Subgroup.comap_mono inf_le_right
  have hPcard : Nat.card ((Q ⊓ C).subgroupOf N)
      = q ^ (Nat.card (C.subgroupOf N)).factorization q := by
    rw [natCard_subgroupOf hQCN, natCard_subgroupOf hCN, hQCcard]
  have hfrat :
      (N : Set G) = (C : Set G) * ((N ⊓ normalizer (Q₀ : Set G) : Subgroup G) : Set G) := by
    refine Set.eq_of_subset_of_subset (fun x hx => ?_) ?_
    · obtain ⟨r, hr, n, hn, hx'⟩ :=
        exists_mem_mul_mem_normalizer (p := q) hPle hPcard (⟨x, hx⟩ : ↥N)
      have hnG : (n : G) ∈ normalizer ((Q ⊓ C : Subgroup G) : Set G) := by
        have := mem_normalizer_map_subtype (L := N) hn
        rwa [Subgroup.map_subgroupOf_eq_of_le hQCN] at this
      exact Set.mem_mul.2 ⟨(r : G), hr, (n : G),
        ⟨n.2, normalizer_le_normalizer_of_le_of_isCyclic hQ₀QC hnG⟩,
        (congrArg Subtype.val hx').symm⟩
    · rintro x ⟨a, ha, b, hb, rfl⟩
      exact mul_mem (hCN ha) hb.1
  exact ⟨hτ₁, hQcyc, hCD, hEN, hNC, hSylC, hfrat⟩

end

end CFSG.FeitThompson.Proofs
