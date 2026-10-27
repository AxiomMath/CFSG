module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LieType.BorelTits

section Tits

variable {G : Type} [Group G] [Finite G] (r : ℕ) [Fact r.Prime]

@[expose] def titsStep (V : Subgroup G) : Subgroup G :=
  pCoreOf r (Subgroup.normalizer (V : Set G))

theorem le_titsStep {V : Subgroup G} (hV : IsPGroup r V) : V ≤ titsStep r V :=
  le_pCoreOf_normalizer r V hV

theorem titsStep_isPGroup (V : Subgroup G) : IsPGroup r (titsStep r V) :=
  pCoreOf_isPGroup r _

theorem map_titsStep (φ : MulAut G) (V : Subgroup G) :
    (titsStep r V).map φ.toMonoidHom = titsStep r (V.map φ.toMonoidHom) := by
  unfold titsStep
  rw [← pCoreOf_map_mulEquiv r φ, Subgroup.map_equiv_normalizer_eq]

@[expose] def titsIter (A : Subgroup G) (i : ℕ) : Subgroup G := (titsStep r)^[i] A

theorem titsIter_succ (A : Subgroup G) (i : ℕ) :
    titsIter r A (i + 1) = titsStep r (titsIter r A i) := by
  unfold titsIter
  rw [Function.iterate_succ_apply']

theorem titsIter_isPGroup {A : Subgroup G} (hA : IsPGroup r A) (i : ℕ) :
    IsPGroup r (titsIter r A i) := by
  cases i with
  | zero => exact hA
  | succ i => rw [titsIter_succ]; exact titsStep_isPGroup r _

theorem titsIter_mono {A : Subgroup G} (hA : IsPGroup r A) : Monotone (titsIter r A) := by
  refine monotone_nat_of_le_succ fun i => ?_
  rw [titsIter_succ]
  exact le_titsStep r (titsIter_isPGroup r hA i)

theorem map_titsIter {A : Subgroup G} (φ : MulAut G) (hφ : A.map φ.toMonoidHom = A) (i : ℕ) :
    (titsIter r A i).map φ.toMonoidHom = titsIter r A i := by
  induction i with
  | zero => exact hφ
  | succ i ih =>
    rw [titsIter_succ, map_titsStep, ih]

theorem exists_titsLimit {A : Subgroup G} (hA : IsPGroup r A) :
    ∃ V : Subgroup G, A ≤ V ∧ IsPGroup r V ∧ pCoreOf r (Subgroup.normalizer (V : Set G)) = V ∧
      ∀ φ : MulAut G, A.map φ.toMonoidHom = A → V.map φ.toMonoidHom = V := by
  haveI : Finite (Subgroup G) := inferInstance
  obtain ⟨m, hm⟩ := (wellFoundedGT_iff_monotone_chain_condition).1
    (inferInstance : WellFoundedGT (Subgroup G)) ⟨titsIter r A, titsIter_mono r hA⟩
  have h1 : titsIter r A m = titsIter r A (m + 1) := hm (m + 1) (Nat.le_succ m)
  refine ⟨titsIter r A m, ?_, titsIter_isPGroup r hA m, ?_, fun φ hφ => map_titsIter r φ hφ m⟩
  · exact titsIter_mono r hA (Nat.zero_le m)
  · have := titsIter_succ r A m
    rw [← h1] at this
    exact this.symm

end Tits

section Canonical

variable {G : Type} [Group G] [Finite G] (r : ℕ) [Fact r.Prime]

theorem exists_canonical_parabolic (hBT : Holds G r) {A : Subgroup G} (hA1 : A ≠ ⊥)
    (hA : IsPGroup r A) :
    ∃ V : Subgroup G, A ≤ V ∧ V ≠ ⊥ ∧ IsPGroup r V ∧
      (∀ φ : MulAut G, A.map φ.toMonoidHom = A → V.map φ.toMonoidHom = V) ∧
      Subgroup.normalizer (V : Set G) ≠ ⊤ ∧
      pCoreOf r (Subgroup.normalizer (V : Set G)) = V ∧
      ∃ S : Sylow r G, Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
        Subgroup.normalizer (V : Set G) := by
  obtain ⟨V, hAV, hVp, hVc, hVφ⟩ := exists_titsLimit r hA
  have hV1 : V ≠ ⊥ := fun h => hA1 (eq_bot_iff.2 (h ▸ hAV))
  obtain ⟨S, P, hP, hN, -, hVP, hS⟩ := hBT V hV1 hVp
  set Q : Subgroup G := pCoreOf r P with hQ
  have hQp : IsPGroup r Q := pCoreOf_isPGroup r P
  have hX : Q ⊓ Subgroup.normalizer (V : Set G) ≤ V := by
    have hX' : Q ⊓ Subgroup.normalizer (V : Set G) ≤
        pCoreOf r (Subgroup.normalizer (V : Set G)) := by
      refine le_pCoreOf_of_le_normalizer r inf_le_right ?_ (hQp.to_le inf_le_left)
      intro n hn
      have hnP : n ∈ P := hN hn
      have hnQ : n ∈ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf r P hnP
      have hnV : n ∈ Subgroup.normalizer ((Subgroup.normalizer (V : Set G) : Subgroup G) : Set G) :=
        Subgroup.le_normalizer hn
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hnQ, hnV⟩
    rwa [hVc] at hX'
  have hVQ : V = Q := by
    by_contra hne
    have hlt : V < Q := lt_of_le_of_ne hVP hne
    haveI : Group.IsNilpotent ↥Q := hQp.isNilpotent
    set H : Subgroup ↥Q := V.subgroupOf Q with hH
    have hHtop : H < ⊤ := by
      refine lt_of_le_of_ne le_top fun h => ?_
      rw [hH, Subgroup.subgroupOf_eq_top] at h
      exact absurd (le_antisymm hVP h) hne
    have hgrow := (Group.normalizerCondition_of_isNilpotent (G := ↥Q)) H hHtop
    obtain ⟨x, hxN, hxH⟩ := SetLike.exists_of_lt hgrow
    have hxN' : (x : G) ∈ Subgroup.normalizer (V : Set G) := by
      have := Subgroup.subgroupOf_normalizer_eq hVP
      rw [← hH] at this
      have hx : x ∈ Subgroup.normalizer (H : Set ↥Q) := hxN
      rw [← this] at hx
      exact hx
    have hxV : (x : G) ∈ V := hX ⟨x.2, hxN'⟩
    exact hxH (by rw [hH, Subgroup.mem_subgroupOf]; exact hxV)
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := by
    rw [hVQ]; exact le_normalizer_pCoreOf r P
  have hPeq : Subgroup.normalizer (V : Set G) = P := le_antisymm hN hPV
  refine ⟨V, hAV, hV1, hVp, hVφ, ?_, hVc, S, ?_⟩
  · rw [hPeq]; exact hP
  · rw [hPeq]; exact hS

end Canonical

end CFSG.LocalAnalysis.GLTheoremA
