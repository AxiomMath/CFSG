module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.IsElemAbelianOfBinaryRankCounterexample

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

variable {G : Type} [Group G] [Finite G]

open Classical in
theorem isInternal_hyperplane_fixedSubmodule_of_binary_rank_counterexample {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    DirectSum.IsInternal
      (fun D : ↥(Delta p P ρ) => fixedSubmodule ρ (D : Subgroup G)) := by
  have hS : Setting G p P T B := hc.oddPrimeClassTwoAction.setting
  have hpr : p.Prime := hS.prime
  haveI : Fact p.Prime := ⟨hpr⟩
  have hp2 : p ≠ 2 := by
    intro h
    have hodd := hS.odd
    rw [h] at hodd
    exact absurd hodd (by decide)
  have hel : CFSG.Open.IsElemAbelian p P := isElemAbelian_of_binary_rank_counterexample hc
  have hnorm : P.Normal := hc.faithfulBinaryIrreducibleAction.normal
  have hcomm : BinaryRepresentations.commSpace ρ P = ⊤ := by
    let S : Subrepresentation ρ :=
      { toSubmodule := BinaryRepresentations.commSpace ρ P
        apply_mem_toSubmodule := by
          intro g v hv
          induction hv using Submodule.span_induction with
          | mem w hw =>
            obtain ⟨x, hx, u, rfl⟩ := hw
            have h1 : ρ (g * x * g⁻¹) (ρ g u) = ρ g (ρ x u) := by
              rw [← BinaryRepresentations.rho_mul_apply, ← BinaryRepresentations.rho_mul_apply]
              congr 1
              group
            rw [map_sub, ← h1]
            apply Submodule.subset_span
            exact ⟨g * x * g⁻¹, hnorm.conj_mem x hx g, ρ g u, rfl⟩
          | zero => simp
          | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
          | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha }
    rcases hc.faithfulBinaryIrreducibleAction.irreducible.eq_bot_or_eq_top S with h | h
    · exfalso
      have hbot : BinaryRepresentations.commSpace ρ P = ⊥ := congrArg Subrepresentation.toSubmodule h
      have hact : ∀ x ∈ P, ρ x = 1 := by
        intro x hx
        ext v
        have hv : ρ x v - v ∈ BinaryRepresentations.commSpace ρ P :=
          Submodule.subset_span ⟨x, hx, v, rfl⟩
        rw [hbot, Submodule.mem_bot, sub_eq_zero] at hv
        simpa using hv
      have hPbot : P = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        apply Subgroup.mem_bot.2
        apply hc.faithfulBinaryIrreducibleAction.faithful
        rw [map_one]
        exact hact x hx
      have hr := hc.faithfulBinaryIrreducibleAction.rank_gt
      rw [hPbot] at hr
      have hle : CFSG.Open.pRank p (⊥ : Subgroup G) ≤ 0 := by
        apply csSup_le'
        rintro k ⟨E, hE, _, hcard⟩
        have hEb : E = ⊥ := eq_bot_iff.2 hE
        subst hEb
        rw [Subgroup.card_bot] at hcard
        have h1 : p ^ k = p ^ 0 := by rw [← hcard]; simp
        exact le_of_eq (Nat.pow_right_injective hpr.two_le h1)
      omega
    · exact congrArg Subrepresentation.toSubmodule h
  have hfix : ∀ D : Subgroup G, fixedSubmodule ρ D = BinaryRepresentations.fixedSpace ρ D := fun D => rfl
  have hDin : ∀ D : Subgroup G, D ≤ P → D.relIndex P = p → fixedSubmodule ρ D ≠ ⊥ →
      D ∈ Delta p P ρ := fun D h1 h2 h3 => (mem_Delta_iff p P ρ D).2 ⟨h1, h2, h3⟩
  have hDout : ∀ D : Subgroup G, D ∈ Delta p P ρ →
      D ≤ P ∧ D.relIndex P = p ∧ fixedSubmodule ρ D ≠ ⊥ := fun D h =>
    (mem_Delta_iff p P ρ D).1 h
  have hdec := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).1
    (BinaryRepresentations.coprime_hyperplane_decomposition hp2 ρ P hel hcomm)
  obtain ⟨hind, hsup⟩ := hdec
  simp only [hfix]
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · have hmem : ∀ D : ↥(Delta p P ρ), (D : Subgroup G) ∈ BinaryRepresentations.hyperplanes p P := fun D => by
      obtain ⟨h1, h2, _⟩ := hDout _ D.2
      exact ⟨h1, h2⟩
    exact hind.comp (f := fun D : ↥(Delta p P ρ) => (⟨(D : Subgroup G), hmem D⟩ :
      ↥(BinaryRepresentations.hyperplanes p P))) (fun D₁ D₂ h => Subtype.ext (by simpa using congrArg Subtype.val h))
  · rw [eq_top_iff, ← hsup]
    refine iSup_le fun D => ?_
    obtain ⟨h1, h2⟩ := D.2
    by_cases h : BinaryRepresentations.fixedSpace ρ D.1 = ⊥
    · rw [h]; exact bot_le
    · have hD : (D.1 : Subgroup G) ∈ Delta p P ρ := hDin _ h1 h2 h
      exact le_iSup_of_le (⟨D.1, hD⟩ : ↥(Delta p P ρ)) le_rfl

end Section5
end CFSG.LocalAnalysis.RankThreeUC
