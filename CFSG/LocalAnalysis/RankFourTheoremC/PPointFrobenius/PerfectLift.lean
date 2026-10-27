module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.MCompInst
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Dichotomy

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding
open CFSG.LocalAnalysis.RankThreeTheoremC (exists_perfect_le_map_eq
  nonempty_mulEquiv_map_mk_of_inf_eq_bot perfectCore perfectCore_le le_perfectCore
  commutator_perfectCore conj_mem_perfectCore mul_mem_of_pow_eq_one_of_coprime)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem fr_exists_perfect_lift [Fact p.Prime] (hK : FrobKFacts) (hG : FrobGlobal G)
    (hl : FrobLocal p P M x)
    (hne : CFSG.layer (M ⧸ primeComplementCore (G := M) p) ≠ ⊥) :
    ∃ J : Subgroup G, ⁅J, J⁆ = J ∧
      J ≤ centralizer ((frU P x : Subgroup G) : Set G) ∧ x ∈ J ∧
      (∀ d ∈ centralizer ((frU P x : Subgroup G) : Set G), ∀ j ∈ J, d * j * d⁻¹ ∈ J) ∧
      ∀ Q : Subgroup G, Q ≤ J → IsPGroup p Q → IsCyclic Q := by
  have hp : p.Prime := Fact.out
  set U := frU P x with hU
  set O := primeComplementCore (G := M) p with hO
  obtain ⟨Kb, hKb⟩ := exists_isComponentOf_of_layer_ne_bot hne
  have hxM : x ∈ M := hl.point.elem.1
  obtain ⟨hKn, -, hxK, hKcyc, hUK, -⟩ := fr_MComp hK hG hl hxM hKb
  have hKperf : ⁅Kb, Kb⁆ = Kb := Subgroup.isPerfect_iff.mp ⟨hKb.2.2.1⟩
  have hUM : U ≤ M := frU_le_M hl
  have hUp : IsPGroup p (U.subgroupOf M) := (P.isPGroup'.to_le inf_le_left).comap_subtype
  have hKC : Kb ≤ (centralizer ((U.subgroupOf M : Subgroup M) : Set M)).map
      (QuotientGroup.mk' O) := by
    have h1 : Kb ≤ centralizer (((U.subgroupOf M).map (QuotientGroup.mk' O) :
        Subgroup (M ⧸ O)) : Set (M ⧸ O)) := le_centralizer_iff.mp hUK
    have h2 := comap_centralizer_map_le_sup hp O (primeComplementCore_coprime p) hUp
    calc Kb ≤ ((centralizer (((U.subgroupOf M).map (QuotientGroup.mk' O) :
          Subgroup (M ⧸ O)) : Set (M ⧸ O))).comap (QuotientGroup.mk' O)).map
            (QuotientGroup.mk' O) := by
          rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O)]
          exact h1
      _ ≤ (O ⊔ centralizer ((U.subgroupOf M : Subgroup M) : Set M)).map
            (QuotientGroup.mk' O) := map_mono h2
      _ = _ := by
          rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' O).ge,
            bot_sup_eq]
  obtain ⟨A, hAC, hAK, hAperf⟩ := exists_perfect_le_map_eq (QuotientGroup.mk' O) hKC hKperf
  set Kt : Subgroup G := (Kb.comap (QuotientGroup.mk' O)).map M.subtype with hKt
  set J := perfectCore (Kt ⊓ centralizer (U : Set G)) with hJ
  have hKtM : Kt ≤ M := map_subtype_le _
  have hconj : ∀ d ∈ centralizer (U : Set G), ∀ k ∈ Kt ⊓ centralizer (U : Set G),
      d * k * d⁻¹ ∈ Kt ⊓ centralizer (U : Set G) := by
    intro d hd k hk
    refine ⟨?_, Subgroup.mul_mem _ (Subgroup.mul_mem _ hd hk.2) (Subgroup.inv_mem _ hd)⟩
    have hdM : d ∈ M := fr_centralizer_U_le hG hl hd
    obtain ⟨k', hk', hkk'⟩ := hk.1
    have hn : (⟨d, hdM⟩ : M) * k' * (⟨d, hdM⟩ : M)⁻¹ ∈ Kb.comap (QuotientGroup.mk' O) :=
      (hKn.comap (QuotientGroup.mk' O)).conj_mem k' hk' _
    exact ⟨_, hn, by rw [← hkk']; rfl⟩
  have hJconj : ∀ d ∈ centralizer (U : Set G), ∀ j ∈ J, d * j * d⁻¹ ∈ J :=
    fun d hd j hj => conj_mem_perfectCore (hconj d hd) hj
  have hJKt : J ≤ Kt := (perfectCore_le _).trans inf_le_left
  have hJU : J ≤ centralizer (U : Set G) := (perfectCore_le _).trans inf_le_right
  have hAJ : A.map M.subtype ≤ J := by
    refine le_perfectCore (le_inf (map_mono (map_le_iff_le_comap.mp hAK.le)) ?_)
      (by rw [← map_commutator, hAperf])
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_iff]
    intro u hu
    exact congrArg Subtype.val
      (mem_centralizer_iff.mp (hAC ha) ⟨u, hUM hu⟩ (mem_subgroupOf.mpr hu))
  refine ⟨J, commutator_perfectCore _, hJU, ?_, hJconj, ?_⟩
  ·
    rw [← hAK] at hxK
    obtain ⟨a, ha, hax⟩ := hxK
    have ho : a⁻¹ * ⟨x, hxM⟩ ∈ O := by
      rw [← QuotientGroup.eq]
      exact hax
    have haJ : (a : G) ∈ J := hAJ ⟨a, ha, rfl⟩
    have hxU : x ∈ centralizer (U : Set G) := mem_centralizer_iff.mpr fun u hu =>
      mem_centralizer_iff.mp (fr_x_mem_Z0 hl).2 u hu.2
    have hoU : (a : G)⁻¹ * x ∈ centralizer (U : Set G) := mul_mem (inv_mem (hJU haJ)) hxU
    have hcop : Nat.Coprime p (orderOf ((a : G)⁻¹ * x)) := by
      have h1 : orderOf (a⁻¹ * ⟨x, hxM⟩ : M) ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O ho
      rw [← Subgroup.orderOf_coe] at h1
      exact Nat.Coprime.coprime_dvd_right h1 (primeComplementCore_coprime p)
    have hxp : ((a : G) * ((a : G)⁻¹ * x)) ^ p = 1 := by
      rw [mul_inv_cancel_left]
      have hxo := hl.point.elem.2.1
      rw [← hxo]
      exact pow_orderOf_eq_one x
    have h := mul_mem_of_pow_eq_one_of_coprime haJ (hJconj _ hoU) hxp hcop
    rwa [mul_inv_cancel_left] at h
  ·
    intro Q hQJ hQ
    have hQM : Q ≤ M := hQJ.trans (hJKt.trans hKtM)
    have hQK : (Q.subgroupOf M).map (QuotientGroup.mk' O) ≤ Kb := by
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨k, hk, hkq⟩ := hJKt (hQJ (mem_subgroupOf.mp hq))
      rw [← Subtype.ext hkq]
      exact hk
    have hQp : IsPGroup p (Q.subgroupOf M) := hQ.comap_subtype
    have hinj : O ⊓ Q.subgroupOf M = ⊥ := by
      refine disjoint_iff.mp (disjoint_of_coprime_natCard ?_)
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQp
      rw [hn]
      exact Nat.Coprime.pow_right n (primeComplementCore_coprime p).symm
    obtain ⟨e⟩ := nonempty_mulEquiv_map_mk_of_inf_eq_bot O hinj
    have hQ' : IsPGroup p (((Q.subgroupOf M).map (QuotientGroup.mk' O)).subgroupOf Kb) :=
      (hQp.map (QuotientGroup.mk' O)).comap_subtype
    obtain ⟨R, hR⟩ := hQ'.exists_le_sylow
    have : IsCyclic (R : Subgroup Kb) := hKcyc R
    have hc : IsCyclic (((Q.subgroupOf M).map (QuotientGroup.mk' O)).subgroupOf Kb) :=
      isCyclic_of_le hR
    exact ((subgroupOfEquivOfLe hQM).symm.trans (e.trans
      (subgroupOfEquivOfLe hQK).symm)).isCyclic.mpr hc

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
