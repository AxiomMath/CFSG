module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
import CFSG.FeitThompson.Local.SimpleGroupNormalizerProper
import CFSG.FeitThompson.Local.SigmaCoreNormalHallDerived

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup _root_.CFSG.FeitThompson

variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem mem_sigmaPrimes_of_dvd_natCard_hallCore [IsSimpleGroup G] (hM : IsCoatom M) {p : ℕ}
    (hp : p.Prime) (hdvd : p ∣ Nat.card (hallCore ↥M)) : p ∈ sigmaPrimes M := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvdM : p ∣ Nat.card ↥M := hdvd.trans (Subgroup.card_subgroup_dvd_card _)
  obtain ⟨P, hPnormal⟩ := exists_normal_sylow_of_dvd_natCard_hallCore hp hdvd
  refine mem_sigmaPrimes_iff.2 ⟨hp, hdvdM, P, ?_⟩
  have hPbot : (P : Subgroup ↥M) ≠ ⊥ := by
    intro h
    have hcard : Nat.card (P : Subgroup ↥M) = p ^ (Nat.card ↥M).factorization p :=
      P.card_eq_multiplicity
    rw [h] at hcard
    simp only [Subgroup.card_bot] at hcard
    exact hp.ne_one (Nat.dvd_one.1 (hcard ▸
      dvd_pow_self p (hp.factorization_pos_of_dvd Nat.card_pos.ne' hdvdM).ne'))
  set Q : Subgroup G := (P : Subgroup ↥M).map M.subtype with hQdef
  have hQM : Q ≤ M := Subgroup.map_subtype_le _
  have hQbot : ⊥ < Q := bot_lt_iff_ne_bot.2 fun h =>
    hPbot ((Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).1 h)
  have hQtop : Q < ⊤ := lt_of_le_of_lt hQM (lt_top_iff_ne_top.2 hM.1)
  have hlt : normalizer (Q : Set G) < ⊤ := normalizer_lt_top_of_isSimpleGroup hQbot hQtop
  have hMle : M ≤ normalizer (Q : Set G) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).1 ?_
    rw [hQdef, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    exact hPnormal
  rcases eq_or_lt_of_le hMle with h | h
  · exact le_of_eq h.symm
  · exact absurd (hM.2 _ h) hlt.ne

omit [Finite G] in
theorem subgroupOf_hallCoreIn_eq (M : Subgroup G) :
    (hallCoreIn M).subgroupOf M = hallCore ↥M :=
  Subgroup.comap_map_eq_self_of_injective M.subtype_injective _

theorem isNilpotent_hallCoreIn (M : Subgroup G) : Group.IsNilpotent ↥(hallCoreIn M) :=
  Group.nilpotent_of_mulEquiv ((hallCore ↥M).equivMapOfInjective _ M.subtype_injective)

theorem hallCoreIn_le_sigmaCore [IsSimpleGroup G] (hM : IsCoatom M) :
    hallCoreIn M ≤ sigmaCore M := by
  refine le_sigmaCore (hallCoreIn_le M) ?_ (isPiSubgroup_iff.2 fun p hp => ?_)
  · rw [subgroupOf_hallCoreIn_eq]; exact hallCore_normal
  · rw [hallCoreIn_eq, Subgroup.card_subtype] at hp
    exact mem_sigmaPrimes_of_dvd_natCard_hallCore hM (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)

theorem sigmaCore_le_hallCoreIn [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    (hM : IsCoatom M) (hnil : Group.IsNilpotent ↥(sigmaCore M)) :
    sigmaCore M ≤ hallCoreIn M := by
  have hnil' : Group.IsNilpotent ↥((sigmaCore M).subgroupOf M) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (sigmaCore_le M)).symm
  have hle := CFSG.FeitThompson.Proofs.isHallSubgroup_subgroupOf_sigmaCore hna hodd hsolv hM
  have h := le_hallCore_of_normal_of_isNilpotent_of_coprime
    (sigmaCore_normal_subgroupOf M) hnil' hle.coprime_natCard_index
  have hmap := Subgroup.map_mono (f := M.subtype) h
  rwa [Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le M)] at hmap

theorem hallCoreIn_eq_sigmaCore_iff_isNilpotent [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    (hM : IsCoatom M) : hallCoreIn M = sigmaCore M ↔ Group.IsNilpotent ↥(sigmaCore M) :=
  ⟨fun h => h ▸ isNilpotent_hallCoreIn M, fun hnil =>
    le_antisymm (hallCoreIn_le_sigmaCore hM) (sigmaCore_le_hallCoreIn hna hodd hsolv hM hnil)⟩

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

theorem FBG_normal_hall_core_sigma_containment :
    Statements.FBG_normal_hall_core_sigma_containment.{u} := by
  intro G _ _ hG M hM
  have := hG.isSimpleGroup
  exact ⟨hallCoreIn_le_sigmaCore hM, hallCoreIn_eq_sigmaCore_iff_isNilpotent
    hG.not_isMulCommutative hG.odd_natCard hG.isSolvable hM⟩

end

end CFSG.FeitThompson.Proofs
