module

public import CFSG.LocalAnalysis.GL83PartI.I_27_9.GenAlt

public section

namespace GL83.PiGen

open Equiv Equiv.Perm MulAction
open GL83 GL83.CompFam

section Double

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem alternatingGroup_le_closure_Y2_of_ne_zero {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {R : Subgroup (Perm Ω)} (hR : IsPGroup p R) (h5 : 5 ≤ Fintype.card Ω)
    (hn : Fintype.card Ω % p ≠ 0) (horb : ∀ ω : Ω, Nat.card (orbit R ω) ≤ p) :
    alternatingGroup Ω ≤ Subgroup.closure (Y2 p R) := by
  classical
  have hp := (Fact.out : p.Prime)
  have hmod : ∀ E : Subgroup (Perm Ω), E ≤ R →
      Fintype.card Ω ≡ Nat.card (fixSet E) [MOD p] := by
    intro E hE
    have := card_fixSet_modEq (p := p) (hR.to_le hE)
    rwa [Nat.card_eq_fintype_card] at this
  have hFR : 1 ≤ Nat.card (fixSet R) := by
    have h := hmod R le_rfl
    by_contra hlt
    have h0 : Nat.card (fixSet R) = 0 := by omega
    have h2 : Fintype.card Ω % p = Nat.card (fixSet R) % p := h
    rw [h0, Nat.zero_mod] at h2
    exact hn h2
  let P : Subgroup (Perm Ω) → Prop := fun E =>
    E ≤ R ∧ Nat.card R ≤ p * Nat.card E ∧ 5 ≤ Nat.card (fixSet E)
  have hgood : ∀ ω : Ω, ω ∉ fixSet R → P (stabIn R ω) ∧ ω ∈ fixSet (stabIn R ω) := by
    intro ω hω
    refine ⟨⟨stabIn_le R ω, ?_, ?_⟩, mem_fixSet_stabIn R ω⟩
    · rw [card_mul_card_stabIn R ω]
      exact Nat.mul_le_mul_right _ (horb ω)
    · have hsub : fixSet R ⊆ fixSet (stabIn R ω) := fixSet_anti (stabIn_le R ω)
      have hss : fixSet R ⊂ fixSet (stabIn R ω) :=
        ⟨hsub, fun h => hω (h (mem_fixSet_stabIn R ω))⟩
      have hlt : Nat.card (fixSet R) < Nat.card (fixSet (stabIn R ω)) := by
        rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
        exact Set.ncard_lt_ncard hss
      have h1 := hmod R le_rfl
      have h2 := hmod (stabIn R ω) (stabIn_le R ω)
      have h3 : Nat.card (fixSet R) ≡ Nat.card (fixSet (stabIn R ω)) [MOD p] := h1.symm.trans h2
      have h4 := (Nat.modEq_iff_dvd' hlt.le).1 h3
      have h5' : p ≤ Nat.card (fixSet (stabIn R ω)) - Nat.card (fixSet R) :=
        Nat.le_of_dvd (by omega) h4
      omega
  have hcover : ∀ ω : Ω, ∃ E, P E ∧ ω ∈ fixSet E := by
    intro ω
    by_cases hnt : ∃ ω', ω' ∉ fixSet R
    · by_cases hω : ω ∈ fixSet R
      · obtain ⟨ω', hω'⟩ := hnt
        exact ⟨stabIn R ω', (hgood ω' hω').1, fixSet_anti (stabIn_le R ω') hω⟩
      · exact ⟨stabIn R ω, (hgood ω hω).1, (hgood ω hω).2⟩
    · have hall : ∀ ω', ω' ∈ fixSet R := fun ω' => by
        by_contra h
        exact hnt ⟨ω', h⟩
      have hfix : fixSet R = Set.univ := Set.eq_univ_of_forall hall
      refine ⟨R, ⟨le_rfl, ?_, ?_⟩, hall ω⟩
      · have : 1 ≤ p := hp.one_lt.le
        nlinarith [Nat.card_pos (α := R)]
      · rw [hfix, Nat.card_univ, Nat.card_eq_fintype_card]
        exact h5
  have hω₀ : ∃ ω₀, ω₀ ∈ fixSet R := by
    by_contra h
    have h' : ∀ ω, ω ∉ fixSet R := fun ω hω => h ⟨ω, hω⟩
    have : fixSet R = ∅ := Set.eq_empty_of_forall_notMem h'
    rw [this] at hFR
    simp at hFR
  obtain ⟨ω₀, hω₀R⟩ := hω₀
  exact alternatingGroup_le_closure_Y2_of_family {E | P E} (fun E hE => hE) hcover ω₀
    (fun E hE => fixSet_anti hE.1 hω₀R)

end Double

section Cover

variable {X : Type*} [Group X] {K A : Subgroup X}

theorem le_centGenI_of_orbits_of_ne_zero {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    [Group.IsPerfect K] (hA : A ≤ Subgroup.normalizer (K : Set X)) (hApg : IsPGroup p A)
    (hodd : Odd (Nat.card (Subgroup.center K))) {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) (hnp : n % p ≠ 0)
    (horb : ∀ ω : Fin n, Nat.card (MulAction.orbit (permHom hA hn hn6 e).range ω) ≤ p) :
    K ≤ centGenI p A K := by
  refine le_centGenI_of_perm hA hodd hn hn6 e ?_
  have hR : IsPGroup p (permHom hA hn hn6 e).range :=
    hApg.of_surjective (permHom hA hn hn6 e).rangeRestrict
      (permHom hA hn hn6 e).rangeRestrict_surjective
  exact alternatingGroup_le_closure_Y2_of_ne_zero hp5 hR (by simpa using hn) (by simpa using hnp)
    horb

end Cover

end GL83.PiGen
