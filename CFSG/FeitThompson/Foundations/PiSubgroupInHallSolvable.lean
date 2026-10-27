module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
import CFSG.FeitThompson.Foundations.SolvableGroupElemAbelianMinNormal
import CFSG.FeitThompson.Foundations.CoprimeAbelianNormalComplements
import CFSG.FeitThompson.Foundations.SolvableHallExistence
import CFSG.FeitThompson.Foundations.LiftHallByNormalComplement
import CFSG.FeitThompson.Foundations.QuotientOrderByNormal
import CFSG.FeitThompson.Foundations.HallLiftThroughNormalPi
import CFSG.FeitThompson.Foundations.CoprimeSubgroupInConjugateComplement

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise

universe u

variable {G G' : Type*} [Group G] [Group G'] {π : Set ℕ}

theorem isPiNumber_pow_iff {p d : ℕ} (hp : p.Prime) (hd : d ≠ 0) :
    IsPiNumber π (p ^ d) ↔ p ∈ π := by
  rw [isPiNumber_iff, Nat.primeFactors_pow p hd, hp.primeFactors]
  simp

theorem exists_normal_isMulCommutative_natCard_eq_pow (G : Type*) [Group G] [Finite G]
    [Nontrivial G] [Group.IsSolvable G] :
    ∃ (N : Subgroup G) (_ : N.Normal) (_ : IsMulCommutative ↥N) (p d : ℕ),
      N ≠ ⊥ ∧ p.Prime ∧ d ≠ 0 ∧ Nat.card ↥N = p ^ d := by
  obtain ⟨N, hN, _, _, _, _, ⟨e⟩⟩ := exists_minimal_normal_ne_bot_nonempty_mulEquiv (G := G)
  obtain ⟨hNn, hNb, -⟩ := minimal_normal_ne_bot_iff.1 hN
  obtain ⟨p, d, hp, hd, hcard⟩ := exists_prime_card_eq_pow_of_minimal_normal_ne_bot hN
  exact ⟨N, hNn, isMulCommutative_of_mulEquiv e, p, d, hNb, hp, by omega, hcard⟩

theorem IsHallSubgroup.map_equiv {H : Subgroup G} (hH : IsHallSubgroup π H) (e : G ≃* G') :
    IsHallSubgroup π (H.map (e : G →* G')) where
  natCard := by
    rw [Nat.card_congr (H.equivMapOfInjective (e : G →* G') e.injective).toEquiv.symm]
    exact hH.natCard
  index := by rw [Subgroup.index_map_equiv H e]; exact hH.index

theorem IsHallSubgroup.conj_smul {H : Subgroup G} (hH : IsHallSubgroup π H) (g : G) :
    IsHallSubgroup π (MulAut.conj g • H) := hH.map_equiv (MulAut.conj g)

private theorem exists_isHallSubgroup_ge_aux (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G] [Group.IsSolvable G], Nat.card G ≤ n →
      ∀ {π : Set ℕ} {U : Subgroup G}, IsPiNumber π (Nat.card U) →
        ∃ H : Subgroup G, IsHallSubgroup π H ∧ U ≤ H := by
  induction n with
  | zero =>
    intro G _ _ _ hG
    have := Nat.card_pos (α := G)
    omega
  | succ n ih =>
    intro G _ _ _ hG π U hU
    rcases subsingleton_or_nontrivial G with hs | hnt
    ·
      refine ⟨⊤, isHallSubgroup_top_iff.2 ?_, le_top⟩
      have h1 : Nat.card G = 1 := Nat.card_eq_one_iff_unique.2 ⟨hs, ⟨1⟩⟩
      rw [h1]; exact isPiNumber_one
    obtain ⟨N, hNn, hNc, p, d, hNb, hp, hd, hcardN⟩ :=
      exists_normal_isMulCommutative_natCard_eq_pow G
    have _i : N.Normal := hNn
    have hquot : Nat.card (G ⧸ N) ≤ n := by
      have := natCard_quotient_lt_natCard_of_bot_lt N (bot_lt_iff_ne_bot.2 hNb)
      omega
    set q := QuotientGroup.mk' N with hq
    have hUq : IsPiNumber π (Nat.card (U.map q)) :=
      hU.of_dvd (Subgroup.card_map_dvd U q) Nat.card_pos.ne'
    obtain ⟨J, hJ, hUJ⟩ := ih (G ⧸ N) hquot hUq
    set L : Subgroup G := J.comap q with hL
    have hNL : N ≤ L := le_comap_mk' J
    have hUL : U ≤ L := (Subgroup.le_comap_map q U).trans (Subgroup.comap_mono hUJ)
    by_cases hpπ : p ∈ π
    ·
      exact ⟨L, hJ.comap_mk' (by rw [hcardN]; exact (isPiNumber_pow_iff hp hd).2 hpπ), hUL⟩
    have hNπ' : IsPiNumber πᶜ (Nat.card N) := by
      rw [hcardN]; exact (isPiNumber_pow_iff hp hd).2 hpπ
    set A : Subgroup ↥L := N.subgroupOf L with hA
    have _iA : A.Normal := hNn.subgroupOf L
    have hAN : Nat.card ↥A = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNL).toEquiv
    have _iAc : IsMulCommutative ↥A :=
      isMulCommutative_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNL)
    have hcardL : Nat.card ↥L = Nat.card ↥N * Nat.card ↥J := by
      rw [hL]
      have := natCard_comap_of_surjective (f := q) (QuotientGroup.mk'_surjective N) J
      rwa [QuotientGroup.ker_mk'] at this
    have hAindex : A.index = Nat.card ↥J := by
      refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥A)) ?_
      rw [Subgroup.card_mul_index A, hAN, hcardL]
    have hcopA : (Nat.card ↥A).Coprime A.index := by
      rw [hAN, hAindex]
      exact (hJ.natCard.coprime_of_compl hNπ' Nat.card_pos.ne' Nat.card_pos.ne').symm
    obtain ⟨H', hcomp⟩ := exists_isComplement'_of_coprime_index hcopA
    set H : Subgroup G := H'.map L.subtype with hH
    have hmapA : A.map L.subtype = N := Subgroup.map_subgroupOf_eq_of_le hNL
    have hsup' : A ⊔ H' = ⊤ := hcomp.sup_eq_top
    have hinf' : A ⊓ H' = ⊥ := disjoint_iff.mp hcomp.disjoint
    have hsup : L = N ⊔ H := by
      rw [hH, ← hmapA, ← Subgroup.map_sup, hsup', ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    have hinf : N ⊓ H = ⊥ := by
      rw [hH, ← hmapA, ← Subgroup.map_inf _ _ _ L.subtype_injective, hinf', Subgroup.map_bot]
    have hHall : IsHallSubgroup π H :=
      isHallSubgroup_of_comap_of_sup_eq hNπ' hJ hL hsup hinf
    set V : Subgroup ↥L := U.subgroupOf L with hV
    have hVU : Nat.card ↥V = Nat.card ↥U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUL).toEquiv
    have hcopVA : (Nat.card ↥V).Coprime (Nat.card ↥A) := by
      rw [hVU, hAN]
      exact hU.coprime_of_compl hNπ' Nat.card_pos.ne' Nat.card_pos.ne'
    obtain ⟨a, -, hconj⟩ := exists_mem_forall_mem_conj_mem hsup' hinf' hcopVA
    refine ⟨MulAut.conj ((a : ↥L) : G) • H, hHall.conj_smul _, fun u hu => ?_⟩
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
    have hmem : (⟨u, hUL hu⟩ : ↥L) ∈ V := by rw [hV, Subgroup.mem_subgroupOf]; exact hu
    exact ⟨_, hconj _ hmem, by simp⟩

theorem exists_isHallSubgroup_ge [Finite G] [Group.IsSolvable G] {U : Subgroup G}
    (hU : IsPiNumber π (Nat.card U)) : ∃ H : Subgroup G, IsHallSubgroup π H ∧ U ≤ H :=
  exists_isHallSubgroup_ge_aux (Nat.card G) G le_rfl hU

theorem exists_isHallSubgroup_ge_of_isPiSubgroup [Finite G] [Group.IsSolvable G] {U : Subgroup G}
    (hU : IsPiSubgroup π U) : ∃ H : Subgroup G, IsHallSubgroup π H ∧ U ≤ H :=
  exists_isHallSubgroup_ge (isPiSubgroup_iff_isPiNumber.1 hU)

end

end CFSG.FeitThompson

