module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi23Local

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

theorem oddCore_eq_bot_of_quasisimple {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X)
    (hZ : Nat.card (center X) = 2) (heven : Even (Nat.card (X ⧸ center X))) :
    CFSG.oddCore X = ⊥ := by
  refine le_bot_iff.1 (sSup_le fun M hM => ?_)
  obtain ⟨hMn, hModd⟩ := hM
  have hs : IsSimpleGroup (X ⧸ center X) := hq.2.1
  have hMc : M ≤ center X := by
    have hn : (M.map (QuotientGroup.mk' (center X))).Normal :=
      hMn.map _ (QuotientGroup.mk'_surjective _)
    rcases hn.eq_bot_or_eq_top with h | h
    · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
      exact h
    · exfalso
      have hd : Nat.card (M.map (QuotientGroup.mk' (center X))) ∣ Nat.card M :=
        Subgroup.card_map_dvd _ _
      rw [h, Subgroup.card_top] at hd
      exact (Nat.not_even_iff_odd.2 (hModd.of_dvd_nat hd)) heven
  have hdvd : Nat.card M ∣ 2 := hZ ▸ Subgroup.card_dvd_of_le hMc
  have h1 : Nat.card M = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact h
    · rw [h] at hModd
      exact absurd hModd (by decide)
  exact le_of_eq (Subgroup.eq_bot_of_card_eq _ h1)

theorem isQuasisimple_inf_centralizer_of_isConj {H Y : Type} [Group H] [Group Y] {L : Subgroup H}
    (ψ : ↥L ≃* Y) {u : H} (hu : u ∈ L) {d : Y} (hconj : IsConj d (ψ ⟨u, hu⟩))
    (hq : CFSG.IsQuasisimple ↥(centralizer ({d} : Set Y))) :
    CFSG.IsQuasisimple ↥(L ⊓ centralizer ({u} : Set H)) := by
  obtain ⟨e1⟩ := nonempty_inf_centralizer_mulEquiv ψ hu
  obtain ⟨c, hcx⟩ := isConj_iff.1 hconj
  have e2 : ↥(centralizer ({d} : Set Y)) ≃* ↥(centralizer ({ψ ⟨u, hu⟩} : Set Y)) :=
    (CFSG.Fischer.centralizerEquiv (MulAut.conj c) d).trans
      (MulEquiv.subgroupCongr (by rw [MulAut.conj_apply, hcx]))
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (e1.trans e2.symm).symm hq

section Certificates


theorem isQuasisimple_centralizer_d :
    CFSG.IsQuasisimple ↥(centralizer ({CFSG.Sporadic.Fi23.d} : Set CFSG.Sporadic.Fi23.J)) := by
  refine ⟨Group.isPerfect_def.2 CFSG.Sporadic.Fi23.commutator_C,
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi22.isSimpleGroup_J
      CFSG.Sporadic.Fi23.quotCenterEquiv, ?_⟩
  obtain ⟨a, b, hab⟩ := CFSG.Sporadic.FischerOddCore.exists_noncomm_fi22J
  refine ⟨CFSG.Sporadic.Fi23.quotCenterEquiv.symm a, CFSG.Sporadic.Fi23.quotCenterEquiv.symm b,
    fun h => hab ?_⟩
  have := congrArg CFSG.Sporadic.Fi23.quotCenterEquiv h
  simpa using this

theorem exists_fiLoc_pair_of_isSporadic_fi23 {H : Type} [Group H] [Finite H] {K L : Subgroup H}
    (hK : IsSporadic ↥K .Fi23) (hKL : K ≤ L) :
    ∃ (K₀ : Subgroup H) (u₀ : H), u₀ ∈ K ∧ Fi23Transposition K u₀ ∧
      K₀ = K ⊓ centralizer ({u₀} : Set H) ∧ fiLoc (2 * 64561751654400) H L K₀ u₀ := by
  obtain ⟨e⟩ := hK
  let ψ : ↥K ≃* CFSG.Sporadic.Fi23.J := e.trans CFSG.Sporadic.Fi23.fi23EquivJ
  set d := CFSG.Sporadic.Fi23.d with hd
  have hu₀K : ((ψ.symm d : ↥K) : H) ∈ K := (ψ.symm d).2
  set u₀ : H := ((ψ.symm d : ↥K) : H) with hu₀
  have hψ : ψ ⟨u₀, hu₀K⟩ = d := by
    have : (⟨u₀, hu₀K⟩ : ↥K) = ψ.symm d := Subtype.ext rfl
    rw [this, MulEquiv.apply_symm_apply]
  have hu₂ : orderOf u₀ = 2 := by
    have h1 : orderOf (ψ.symm d) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact CFSG.Sporadic.Fi23.orderOf_d
    rw [hu₀, Subgroup.orderOf_coe]
    exact h1
  have hcard : Nat.card ↥(K ⊓ centralizer ({u₀} : Set H)) = 129123503308800 := by
    rw [@fi23_card_inf_centralizer_eq H CFSG.Sporadic.Fi23.J _ (inferInstance) K ψ u₀ hu₀K, hψ]
    exact CFSG.Sporadic.Fi23.card_centralizer_d
  have hZ : Nat.card (center ↥(K ⊓ centralizer ({u₀} : Set H))) = 2 := by
    rw [@card_center_inf_centralizer_of_isConj H CFSG.Sporadic.Fi23.J _ (inferInstance) K ψ u₀
      hu₀K d (by rw [hψ]; exact IsConj.refl d)]
    exact CFSG.Sporadic.Fi23.card_center_C
  have hq : CFSG.IsQuasisimple ↥(K ⊓ centralizer ({u₀} : Set H)) :=
    @isQuasisimple_inf_centralizer_of_isConj H CFSG.Sporadic.Fi23.J _ (inferInstance) K ψ u₀ hu₀K d
      (by rw [hψ]; exact IsConj.refl d) isQuasisimple_centralizer_d
  have hev : Even (Nat.card (↥(K ⊓ centralizer ({u₀} : Set H)) ⧸
      center ↥(K ⊓ centralizer ({u₀} : Set H)))) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (center ↥(K ⊓ centralizer ({u₀} : Set H)))
    rw [hcard, hZ] at h1
    exact ⟨32280875827200, by omega⟩
  have hO := oddCore_eq_bot_of_quasisimple hq hZ hev
  refine ⟨K ⊓ centralizer ({u₀} : Set H), u₀, hu₀K, ⟨hu₀K, hu₂, hcard⟩, rfl, hKL hu₀K, hu₂,
    inf_le_left.trans hKL, fun k hk => mem_centralizer_singleton_iff.1 hk.2, hq, ?_⟩
  rw [hO, Nat.card_congr QuotientGroup.quotientBot.toEquiv, hcard]

end Certificates

end CFSG.EvenSporadicStandard.Induction
