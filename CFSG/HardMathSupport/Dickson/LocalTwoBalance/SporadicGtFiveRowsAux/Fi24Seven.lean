module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicGtFiveRowsAux

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Fi24 (R J JR jR cls)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [local instance] CFSG.Sporadic.Fi24.rAction

section Points


theorem R_isPretransitive : MulAction.IsPretransitive ↥R (Fin 306936) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J x y
  exact ⟨jR g, by rw [CFSG.Sporadic.Fi24.jR_smul]; exact hg⟩

theorem not_forall_fix_of_card_seven_sq {E : Subgroup ↥R} (hE : Nat.card E = 7 ^ 2)
    (k : Fin 306936) : ¬ ∀ q ∈ E, q • k = k := by
  intro h
  haveI := R_isPretransitive
  have hle : E ≤ MulAction.stabilizer ↥R k := fun q hq =>
    MulAction.mem_stabilizer_iff.2 (h q hq)
  have hE49 : Nat.card E = 49 := by rw [hE]; norm_num
  obtain ⟨c, hc⟩ := hE49 ▸ Subgroup.card_dvd_of_le hle
  have hidx : (MulAction.stabilizer ↥R k).index = 306936 := by
    rw [MulAction.index_stabilizer_of_transitive]
    simp
  have hmul := (MulAction.stabilizer ↥R k).card_mul_index
  rw [hidx, hc, CFSG.Sporadic.Fi24.card_R] at hmul
  omega

end Points

section Outer


theorem exists_fixed_point_of_commute {E : Subgroup ↥R} (hE : Nat.card E = 7 ^ 2) {n : ↥R}
    (hn2 : n * n = 1) (hnJ : n ∉ JR) (h : ∀ q ∈ E, q * n = n * q) :
    ∃ k : Fin 306936, ∀ q ∈ E, q • k = k := by
  rcases outer_involution_cases hn2 hnJ with ⟨k, rfl⟩ | ⟨K, hK⟩
  · exact ⟨k, fun q hq => (smul_eq_iff_commute_R q k).2 (h q hq)⟩
  · obtain ⟨k₁, k₂, k₃, hKe⟩ := hK.three
    have hperm : ∀ q ∈ E, ∀ k ∈ K, q • k ∈ K := fun q hq k hk =>
      CFSG.Sporadic.FischerOddCore.fo24_triple_perm hK.fix hK.comm hK.char (h q hq) hk
    have hk₁ : k₁ ∈ K := by rw [hKe]; simp
    have horb : MulAction.orbit E k₁ ⊆ K := by
      rintro _ ⟨⟨q, hq⟩, rfl⟩
      exact hperm q hq k₁ hk₁
    have hfin : K.Finite := by rw [hKe]; exact Set.toFinite _
    have hK3 : K.ncard ≤ 3 := by
      have : K = (({k₁, k₂, k₃} : Finset (Fin 306936)) : Set (Fin 306936)) := by
        rw [hKe]; simp
      rw [this, Set.ncard_coe_finset]
      exact Finset.card_le_three
    have hdvd : (MulAction.stabilizer E k₁).index ∣ 7 ^ 2 := hE ▸ Subgroup.index_dvd_card _
    have hle : (MulAction.stabilizer E k₁).index ≤ 3 := by
      rw [MulAction.index_stabilizer]
      exact (Set.ncard_le_ncard horb hfin).trans hK3
    have hpos : 0 < (MulAction.stabilizer E k₁).index :=
      Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
    have h1 : (MulAction.stabilizer E k₁).index = 1 := by
      generalize (MulAction.stabilizer E k₁).index = o at hdvd hle hpos
      interval_cases o
      · rfl
      · exact absurd hdvd (by norm_num)
      · exact absurd hdvd (by norm_num)
    have htop := Subgroup.index_eq_one.1 h1
    refine ⟨k₁, fun q hq => ?_⟩
    have : (⟨q, hq⟩ : E) ∈ MulAction.stabilizer E k₁ := by rw [htop]; trivial
    exact this

theorem exists_noncomm_of_card_seven_sq {E : Subgroup ↥R} (hE : Nat.card E = 7 ^ 2) {n : ↥R}
    (hn2 : n * n = 1) (hnJ : n ∉ JR) : ∃ q ∈ E, q * n ≠ n * q := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := exists_fixed_point_of_commute hE hn2 hnJ hcon
  exact not_forall_fix_of_card_seven_sq hE k hk

theorem gLAPPrimeCoreOf_R_eq_bot_of_plane {d : ↥R}
    (hJ : GLAPPrimeCoreOf 7 (Subgroup.centralizer ({d} : Set ↥R) ⊓ JR) = ⊥)
    {E : Subgroup ↥R} (hE : Nat.card E = 7 ^ 2) (hEd : ∀ q ∈ E, q * d = d * q) :
    GLAPPrimeCoreOf 7 (Subgroup.centralizer ({d} : Set ↥R)) = ⊥ := by
  set C : Subgroup ↥R := Subgroup.centralizer ({d} : Set ↥R)
  set N : Subgroup ↥R := GLAPPrimeCoreOf 7 C
  have hNJ : N ⊓ JR = ⊥ :=
    le_bot_iff.1 ((gLAPPrimeCoreOf_inf_le Nat.prime_seven C JR).trans hJ.le)
  haveI hJn : (JR : Subgroup ↥R).Normal := CFSG.Sporadic.Fi24.normal_JR
  have hidx : (JR : Subgroup ↥R).index = 2 := CFSG.Sporadic.Fi24.index_JR
  by_contra hne
  obtain ⟨n, hnN, hn1⟩ : ∃ n ∈ N, n ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hne ((Subgroup.eq_bot_iff_forall N).2 hcon)
  have hnJ : n ∉ JR := fun hJmem => hn1 (by
    have : n ∈ N ⊓ JR := ⟨hnN, hJmem⟩
    rw [hNJ] at this
    exact this)
  have hn2 : n * n = 1 := by
    have h1 : n ^ 2 ∈ JR := by
      have := Subgroup.pow_index_mem JR n
      rwa [hidx] at this
    have h2 : n ^ 2 ∈ N ⊓ JR := ⟨N.pow_mem hnN 2, h1⟩
    rw [hNJ] at h2
    rw [← pow_two]
    exact h2
  have hcomm : ∀ x ∈ C, x * n = n * x := by
    intro x hx
    have hm : x * n * x⁻¹ ∈ N := GLAPPrimeCoreOf_conj_mem x hx n hnN
    have hmJ : x * n * x⁻¹ ∉ JR := by
      intro hmem
      apply hnJ
      have h' := hJn.conj_mem _ hmem x⁻¹
      have e : x⁻¹ * (x * n * x⁻¹) * x⁻¹⁻¹ = n := by group
      rwa [e] at h'
    have hprod : n⁻¹ * (x * n * x⁻¹) ∈ JR := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      exact iff_of_false (fun hinv => hnJ (by simpa using JR.inv_mem hinv)) hmJ
    have hprodN : n⁻¹ * (x * n * x⁻¹) ∈ N := N.mul_mem (N.inv_mem hnN) hm
    have h1 : n⁻¹ * (x * n * x⁻¹) = 1 := by
      have : n⁻¹ * (x * n * x⁻¹) ∈ N ⊓ JR := ⟨hprodN, hprod⟩
      rw [hNJ] at this
      exact this
    have h2 : x * n * x⁻¹ = n := (inv_mul_eq_one.1 h1).symm
    calc x * n = x * n * x⁻¹ * x := by group
      _ = n * x := by rw [h2]
  obtain ⟨q, hqE, hq⟩ := exists_noncomm_of_card_seven_sq hE hn2 hnJ
  exact hq (hcomm q (Subgroup.mem_centralizer_singleton_iff.2 (hEd q hqE)))

end Outer

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicGtFiveRowsAux
