module

public import CFSG.FeitThompson.Definitions.PuigSubgroupIteration
public import CFSG.FeitThompson.Local.CompetingMaximalFittingPrimeSupport
import CFSG.FeitThompson.Local.PComplSubgroupNormalizedBySylow
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
import CFSG.FeitThompson.Local.PrimeFittingNormalSelfCentralizingAbelian
import CFSG.FeitThompson.Local.PComplCoreSupPuigCenterNormal
import CFSG.FeitThompson.Local.PuigCenterNontrivialCharacteristic
import CFSG.FeitThompson.Local.CentralSylowFixedFreeCycle
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle
import CFSG.FeitThompson.Local.TrivialComplementaryCoreMaximalSylow

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

omit [Finite G] in
theorem subgroupOf_le_normalizer_subgroupOf {M P K : Subgroup G}
    (h : P ≤ normalizer (K : Set G)) :
    P.subgroupOf M ≤ normalizer ((K.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro y
  have hxK := mem_normalizer_iff.1 (h (mem_subgroupOf.1 hx))
  simpa [mem_subgroupOf] using hxK (y : G)

omit [Finite G] in
theorem le_normalizer_map_subtype_of_normal {M : Subgroup G} {N : Subgroup ↥M} (hN : N.Normal) :
    M ≤ normalizer ((N.map M.subtype : Subgroup G) : Set G) := by
  refine le_normalizer_of_normal_subgroupOf (Subgroup.map_subtype_le N) ?_
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  exact hN

theorem le_pComplCoreIn_of_control {M P B : Subgroup G} [Group.IsSolvable ↥M] (hp : p.Prime)
    (hPM : P ≤ M) (hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p) (hBP : B ≤ P)
    (hcontrol : ∀ K : Subgroup G, p.Coprime (Nat.card ↥K) →
      B ≤ normalizer (K : Set G) → K ≤ M)
    {K : Subgroup G} (hK : p.Coprime (Nat.card ↥K)) (hPK : P ≤ normalizer (K : Set G)) :
    K ≤ pComplCoreIn p M := by
  have hKM : K ≤ M := hcontrol K hK (hBP.trans hPK)
  have hcardK : Nat.card ↥(K.subgroupOf M) = Nat.card ↥K :=
    Nat.card_congr (subgroupOfEquivOfLe hKM).toEquiv
  have hcardP : Nat.card ↥(P.subgroupOf M) = p ^ (Nat.card ↥M).factorization p := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hPM).toEquiv, hPcard]
  have h1 := le_pComplCore_of_coprime_of_le_normalizer (X := ↥M) hp (by rwa [hcardK])
    hcardP (subgroupOf_le_normalizer_subgroupOf hPK)
  have h2 := Subgroup.map_mono (f := M.subtype) h1
  rwa [subgroupOf_map_subtype, inf_eq_left.2 hKM, ← pComplCoreIn_eq] at h2

theorem normalizer_le_normalizer_pComplCoreIn {M P B : Subgroup G} [Group.IsSolvable ↥M]
    (hp : p.Prime) (hPM : P ≤ M) (hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p)
    (hBP : B ≤ P)
    (hcontrol : ∀ K : Subgroup G, p.Coprime (Nat.card ↥K) →
      B ≤ normalizer (K : Set G) → K ≤ M) :
    normalizer (P : Set G) ≤ normalizer ((pComplCoreIn p M : Subgroup G) : Set G) := by
  set D : Subgroup G := pComplCoreIn p M
  have hcop : p.Coprime (Nat.card ↥D) :=
    hp.coprime_iff_not_dvd.2 (not_dvd_natCard_pComplCoreIn hp M)
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  set f : G ≃* G := MulAut.conj g
  have hPf : P.map (f : G →* G) = P := mem_normalizer_iff_map_conj_eq.1 hg
  have hPD : P ≤ normalizer (D : Set G) := hPM.trans (le_normalizer_pComplCoreIn p M)
  have hnorm : (normalizer (D : Set G)).map (f : G →* G)
      = normalizer ((D.map (f : G →* G) : Subgroup G) : Set G) :=
    Subgroup.map_equiv_normalizer_eq D f
  have hPDf : P ≤ normalizer ((D.map (f : G →* G) : Subgroup G) : Set G) := by
    have h := Subgroup.map_mono (f := (f : G →* G)) hPD
    rwa [hPf, hnorm] at h
  have hcard : Nat.card ↥(D.map (f : G →* G)) = Nat.card ↥D :=
    Subgroup.card_map_of_injective f.injective
  have hle : D.map (f : G →* G) ≤ D :=
    le_pComplCoreIn_of_control hp hPM hPcard hBP hcontrol (by rw [hcard]; exact hcop) hPDf
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])

theorem normalizer_le_of_control_of_coprime [IsSimpleGroup G]
    (_hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    {M P B : Subgroup G} (hM : IsCoatom M) (hp : p.Prime) (hPM : P ≤ M)
    (hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p)
    (hB : ⊥ < B) (hBP : B ≤ P)
    (hcontrol : ∀ K : Subgroup G, p.Coprime (Nat.card ↥K) →
      B ≤ normalizer (K : Set G) → K ≤ M) :
    normalizer (P : Set G) ≤ M := by
  have := Fact.mk hp
  have hMsolv : Group.IsSolvable ↥M := hsolv M hM.1
  have hModd : Odd (Nat.card ↥M) := hodd.of_dvd_nat M.card_subgroup_dvd_card
  by_cases hD : pComplCoreIn p M = ⊥
  ·
    have hPne : P ≠ ⊥ := fun h => hB.ne' (le_bot_iff.1 (hBP.trans h.le))
    have hPnt : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).2 hPne
    have hPp : IsPGroup p ↥P := IsPGroup.of_card hPcard
    set K : Subgroup G := (puigCenter ↥P).map P.subtype with hKdef
    have hKne : K ≠ ⊥ := by
      rw [hKdef, Ne, Subgroup.map_eq_bot_iff, P.ker_subtype, le_bot_iff]
      exact puigCenter_ne_bot hp hPp
    have hKM : K ≤ M := (Subgroup.map_subtype_le _).trans hPM
    have hcardP : Nat.card ↥(P.subgroupOf M) = p ^ (Nat.card ↥M).factorization p := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hPM).toEquiv, hPcard]
    have hnormal := normal_pComplCore_sup_map_puigCenter_sylow hp hModd
      (Sylow.ofCard (P.subgroupOf M) hcardP)
    rw [Sylow.coe_ofCard, (pComplCoreIn_eq_bot_iff p M).1 hD, bot_sup_eq] at hnormal
    have hMK : M ≤ normalizer (K : Set G) := by
      have h := le_normalizer_map_subtype_of_normal hnormal
      rwa [map_map_puigCenter_subgroupOf hPM] at h
    rw [← normalizer_eq_of_isCoatom hM hKne hKM hMK, hKdef]
    exact normalizer_le_normalizer_map_subtype P (puigCenter ↥P)
  ·
    rw [← normalizer_eq_of_isCoatom hM hD (pComplCoreIn_le p M) (le_normalizer_pComplCoreIn p M)]
    exact normalizer_le_normalizer_pComplCoreIn hp hPM hPcard hBP hcontrol

theorem normalizer_le_of_control_of_coprime_sylow [IsSimpleGroup G] [Fact p.Prime]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    {M B : Subgroup G} (hM : IsCoatom M) (S : Sylow p ↥M) (hB : ⊥ < B)
    (hBS : B ≤ (S : Subgroup ↥M).map M.subtype)
    (hcontrol : ∀ K : Subgroup G, p.Coprime (Nat.card ↥K) →
      B ≤ normalizer (K : Set G) → K ≤ M) :
    normalizer (((S : Subgroup ↥M).map M.subtype : Subgroup G) : Set G) ≤ M :=
  normalizer_le_of_control_of_coprime hna hodd hsolv hM Fact.out
    (Subgroup.map_subtype_le _)
    (by rw [Subgroup.card_map_of_injective M.subtype_injective]; exact S.card_eq_multiplicity)
    hB hBS hcontrol

end

end CFSG.FeitThompson
