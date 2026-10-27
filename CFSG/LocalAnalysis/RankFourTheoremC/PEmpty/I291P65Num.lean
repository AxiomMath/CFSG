module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xDefs
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (smallRankIsQ8D8)

theorem q8d8_facts {H : Type} [Group H] [Finite H] {R : Subgroup H} (h : smallRankIsQ8D8 R) :
    Nat.card R = 32 ∧ ∃ r ∈ R, r ^ 2 ≠ 1 := by
  obtain ⟨A, B, ⟨eA⟩, ⟨eB⟩, hcomm, hAB, hint⟩ := h
  have hA : Nat.card A = 8 := by
    rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hB : Nat.card B = 8 := by
    rw [Nat.card_congr eB.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hcomm).1
  rw [hAB, hint, hA, hB] at hprod
  refine ⟨by omega, ⟨((eA.symm (QuaternionGroup.a 1) : ↥A) : H), ?_, ?_⟩⟩
  · rw [← hAB]
    exact mem_sup_left (eA.symm _).2
  · intro h1
    have h2 : (eA.symm (QuaternionGroup.a 1)) ^ 2 = 1 := Subtype.ext h1
    have h3 : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 = 1 := by
      apply eA.symm.injective
      rw [map_pow, h2, map_one]
    revert h3
    decide

theorem card_map_le_sixteen {H : Type} [Group H] [Finite H] {E : Type} [Group E]
    (hE : ∀ e : E, e ^ 2 = 1) {Q R : Subgroup H} (hR32 : Nat.card R ≤ 32)
    (hsq : ∃ r ∈ R, r ^ 2 ≠ 1) (φ : ↥Q →* E) :
    Nat.card (((R ⊓ Q).subgroupOf Q).map φ) ≤ 16 := by
  set S₀ : Subgroup ↥Q := (R ⊓ Q).subgroupOf Q with hS₀
  have hcardS : Nat.card S₀ = Nat.card ↥(R ⊓ Q) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : R ⊓ Q ≤ Q)).toEquiv
  by_cases hRQ : R ≤ Q
  ·
    obtain ⟨r, hrR, hr⟩ := hsq
    have hrS : (⟨r, hRQ hrR⟩ : ↥Q) ∈ S₀ := ⟨hrR, hRQ hrR⟩
    set ψ : ↥S₀ →* E := φ.comp S₀.subtype with hψ
    have hker : (⟨⟨r, hRQ hrR⟩, hrS⟩ : ↥S₀) ^ 2 ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hE _
    have hker1 : ψ.ker ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.mem_bot] at hker
      apply hr
      have := congrArg (fun s : ↥S₀ => ((s : ↥Q) : H)) hker
      simpa using this
    have h2 : 2 ≤ Nat.card ψ.ker :=
      Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot _).mpr hker1)
    have h3 : Nat.card ψ.ker * Nat.card ψ.range = Nat.card ↥S₀ := by
      rw [← Subgroup.index_ker, Subgroup.card_mul_index]
    have h4 : Nat.card ↥(R ⊓ Q) = Nat.card R := by
      rw [inf_eq_left.mpr hRQ]
    have h5 : ψ.range = S₀.map φ := by
      ext e
      constructor
      · rintro ⟨s, rfl⟩
        exact ⟨(s : ↥Q), s.2, rfl⟩
      · rintro ⟨c, hc, rfl⟩
        exact ⟨⟨c, hc⟩, rfl⟩
    rw [← h5]
    have h6 : Nat.card ψ.ker * Nat.card ψ.range ≤ 32 := by
      rw [h3, hcardS, h4]
      exact hR32
    nlinarith
  ·
    have hlt : R ⊓ Q < R := lt_of_le_of_ne inf_le_left fun h => hRQ (h ▸ inf_le_right)
    have h1 : Nat.card ↥(R ⊓ Q) < Nat.card R := Subgroup.card_lt_of_lt hlt
    have h2 : Nat.card ↥(R ⊓ Q) ∣ Nat.card R := Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, hk⟩ := h2
    have hk2 : 2 ≤ k := by
      rcases k with _ | _ | k
      · omega
      · omega
      · omega
    have h3 : Nat.card ↥(R ⊓ Q) ≤ 16 := by nlinarith
    have h4 : Nat.card (S₀.map φ) ≤ Nat.card ↥S₀ := by
      refine Nat.card_le_card_of_surjective
        (fun s : ↥S₀ => (⟨φ (s : ↥Q), Subgroup.mem_map_of_mem φ s.2⟩ : ↥(S₀.map φ))) ?_
      rintro ⟨_, s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, rfl⟩
    omega

theorem finrank_finset_sup_le {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (U : ι → Submodule K V) (s : Finset ι) :
    Module.finrank K ↥(s.sup U) ≤ ∑ i ∈ s, Module.finrank K ↥(U i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sup_insert, Finset.sum_insert ha]
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (by omega)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65
