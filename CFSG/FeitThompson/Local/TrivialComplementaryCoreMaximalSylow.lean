module

public import CFSG.FeitThompson.Definitions.PuigSubgroupIteration
public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
import CFSG.FeitThompson.Local.PuigCenterNontrivialCharacteristic
import CFSG.FeitThompson.Local.PuigCenterNormalTrivialPComplCore
import CFSG.FeitThompson.Local.PuigSeriesIsomorphismInvariance
import CFSG.FeitThompson.Local.SimpleGroupNormalizerProper
import CFSG.FeitThompson.Local.CentralSylowFixedFreeCycle
import CFSG.FeitThompson.Local.MaximalIntersectionSylowNormalizerControl
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Solvable

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G] {p : ℕ} {M P : Subgroup G}

theorem map_map_puigCenter_subgroupOf (hPM : P ≤ M) :
    ((puigCenter ↥(P.subgroupOf M)).map (P.subgroupOf M).subtype).map M.subtype
      = (puigCenter ↥P).map P.subtype := by
  rw [Subgroup.map_map]
  have he : M.subtype.comp (P.subgroupOf M).subtype
      = P.subtype.comp (Subgroup.subgroupOfEquivOfLe hPM).toMonoidHom := by
    ext x; rfl
  rw [he, ← Subgroup.map_map, puigCenter_map]

theorem le_normalizer_map_puigCenter [Finite G] [Group.IsSolvable ↥M] (hp : p.Prime) (hpodd : Odd p)
    (hModd : Odd (Nat.card ↥M)) (hp' : pComplCore p ↥M = ⊥) (hPM : P ≤ M)
    (hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p) :
    M ≤ normalizer (((puigCenter ↥P).map P.subtype : Subgroup G) : Set G) := by
  have := Fact.mk hp
  have hcard : Nat.card ↥(P.subgroupOf M) = p ^ (Nat.card ↥M).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv, hPcard]
  have hnorm := normal_map_puigCenter_sylow (G := ↥M) hp hpodd hModd hp'
    (Sylow.ofCard (P.subgroupOf M) hcard)
  rw [Sylow.coe_ofCard] at hnorm
  refine le_normalizer_of_normal_subgroupOf ((Subgroup.map_subtype_le _).trans hPM) ?_
  have hsub : ((puigCenter ↥P).map P.subtype).subgroupOf M
      = (puigCenter ↥(P.subgroupOf M)).map (P.subgroupOf M).subtype := by
    rw [← map_map_puigCenter_subgroupOf hPM]
    exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  rw [hsub]
  exact hnorm

theorem nontrivial_of_natCard_eq_pow_factorization [Finite G] (hp : p.Prime)
    (hdvd : p ∣ Nat.card ↥M) (hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p) :
    Nontrivial ↥P := by
  refine Finite.one_lt_card_iff_nontrivial.1 ?_
  rw [hPcard]
  exact Nat.one_lt_pow (hp.factorization_pos_of_dvd Nat.card_pos.ne' hdvd).ne' hp.one_lt

theorem normalizer_eq_of_trivial_pComplCore [Finite G] [IsSimpleGroup G]
    (hp : p.Prime) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hM : IsCoatom M) (hdvd : p ∣ Nat.card ↥M) (hPM : P ≤ M)
    (hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p)
    (hp' : pComplCore p ↥M = ⊥) :
    normalizer (((puigCenter ↥P).map P.subtype : Subgroup G) : Set G) = M := by
  have := Fact.mk hp
  have := hsolv M hM.1
  have hModd : Odd (Nat.card ↥M) := hodd.of_dvd_nat M.card_subgroup_dvd_card
  have hpodd : Odd p := hModd.of_dvd_nat hdvd
  set K : Subgroup G := (puigCenter ↥P).map P.subtype with hK
  have hPnt : Nontrivial ↥P := nontrivial_of_natCard_eq_pow_factorization hp hdvd hPcard
  have hKbot : ⊥ < K := bot_lt_iff_ne_bot.2 fun h =>
    puigCenter_ne_bot hp (IsPGroup.of_card hPcard)
      ((Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective).1 h)
  have hKM : K ≤ M := (Subgroup.map_subtype_le _).trans hPM
  have hle : M ≤ normalizer (K : Set G) :=
    le_normalizer_map_puigCenter hp hpodd hModd hp' hPM hPcard
  have hlt : normalizer (K : Set G) < ⊤ :=
    normalizer_lt_top_of_isSimpleGroup hKbot (hKM.trans_lt hM.lt_top)
  by_contra hne
  exact hlt.ne (hM.2 _ (hle.lt_of_ne fun h => hne h.symm))

theorem exists_sylow_coe_eq_of_natCard_eq_pow_factorization [Finite G] (hp : p.Prime)
    (hPcard : Nat.card ↥P = p ^ (Nat.card G).factorization p) :
    ∃ T : Sylow p G, (T : Subgroup G) = P := by
  have := Fact.mk hp
  exact ⟨Sylow.ofCard P hPcard, Sylow.coe_ofCard _ _⟩

theorem normalizer_le_and_natCard_eq_of_trivial_pComplCore [Finite G] [IsSimpleGroup G]
    (hp : p.Prime) (_hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hM : IsCoatom M) (hdvd : p ∣ Nat.card ↥M) (hPM : P ≤ M)
    (hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p)
    (hp' : pComplCore p ↥M = ⊥) :
    normalizer (P : Set G) ≤ M ∧ Nat.card ↥P = p ^ (Nat.card G).factorization p := by
  have hNK := normalizer_eq_of_trivial_pComplCore hp hodd hsolv hM hdvd hPM hPcard hp'
  have hNP : normalizer (P : Set G) ≤ M := by
    rw [← hNK]
    exact normalizer_le_normalizer_map_subtype P (puigCenter ↥P)
  exact ⟨hNP, natCard_eq_pow_factorization_of_normalizer_le hp hPcard hNP⟩

theorem normalizer_le_and_exists_sylow_of_trivial_pComplCore [Finite G] [IsSimpleGroup G]
    (hp : p.Prime) (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hM : IsCoatom M) (hdvd : p ∣ Nat.card ↥M) (hPM : P ≤ M)
    (hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p)
    (hp' : pComplCore p ↥M = ⊥) :
    normalizer (P : Set G) ≤ M ∧ ∃ T : Sylow p G, (T : Subgroup G) = P := by
  obtain ⟨hNP, hcard⟩ := normalizer_le_and_natCard_eq_of_trivial_pComplCore hp hna hodd hsolv hM
    hdvd hPM hPcard hp'
  exact ⟨hNP, exists_sylow_coe_eq_of_natCard_eq_pow_factorization hp hcard⟩

theorem sylow_natCard_eq_pow_factorization_of_trivial_pComplCore [Finite G] [IsSimpleGroup G]
    (hp : p.Prime) (_hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hM : IsCoatom M) (hdvd : p ∣ Nat.card ↥M) (hp' : pComplCore p ↥M = ⊥) (S : Sylow p ↥M) :
    normalizer (((S : Subgroup ↥M).map M.subtype : Subgroup G) : Set G) ≤ M ∧
      Nat.card ↥((S : Subgroup ↥M).map M.subtype) = p ^ (Nat.card G).factorization p := by
  have := Fact.mk hp
  have hcard : Nat.card ↥((S : Subgroup ↥M).map M.subtype)
      = p ^ (Nat.card ↥M).factorization p := by
    rw [Subgroup.card_map_of_injective M.subtype_injective, S.card_eq_multiplicity]
  exact normalizer_le_and_natCard_eq_of_trivial_pComplCore hp ‹_› hodd hsolv hM hdvd
    (Subgroup.map_subtype_le _) hcard hp'

end CFSG.FeitThompson

end
