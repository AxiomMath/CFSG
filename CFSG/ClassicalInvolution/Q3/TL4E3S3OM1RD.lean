module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1RA

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.Blueprint

namespace E3S3O

@[expose] def ClassicalTag3 (t : Assembly.LowTwoRank.StatedLieTag) : Prop :=
  t = .PSL ∨ t = .PSp ∨ t = .PSU ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus

@[expose] def CentTag3 (t : Assembly.LowTwoRank.StatedLieTag) (n : ℕ) : Prop :=
  (t = .PSp ∧ n = 2) ∨ (t = .PSL ∧ n = 4) ∨ (t = .PSU ∧ n = 4) ∨
    (t = .POmegaOdd ∧ 3 ≤ n) ∨ (t = .POmegaPlus ∧ 4 ≤ n) ∨
    (t = .POmegaMinus ∧ 4 ≤ n)

theorem CentTag3.classical {t : Assembly.LowTwoRank.StatedLieTag} {n : ℕ}
    (h : CentTag3 t n) : ClassicalTag3 t := by
  rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
  all_goals simp [ClassicalTag3]

theorem centOmega3_tag_exact {Y : Type} [Group Y] (h : CentOmega3 Y) :
    ∃ t n, CentTag3 t n ∧ LieModel (Y ⧸ Subgroup.center Y) t n 3 1 := by
  rcases h with h | h | h | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩
  · exact ⟨.PSp, 2, Or.inl ⟨rfl, rfl⟩, h⟩
  · exact ⟨.PSL, 4, Or.inr (Or.inl ⟨rfl, rfl⟩), h⟩
  · exact ⟨.PSU, 4, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), h⟩
  · exact ⟨.POmegaOdd, n, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hn⟩))), h⟩
  · exact ⟨.POmegaPlus, n, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hn⟩)))), h⟩
  · exact ⟨.POmegaMinus, n, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hn⟩)))), h⟩

theorem simple_oddFree_of_lieModel {S : Type} [Group S] [Finite S]
    {t : Assembly.LowTwoRank.StatedLieTag} {n : ℕ} (ht : ClassicalTag3 t)
    (hS : LieModel S t n 3 1) :
    IsSimpleGroup S ∧
      ∀ s : S, orderOf s = 2 → Balance.oddCoreIn (Subgroup.centralizer ({s} : Set S)) = ⊥ := by
  have hcl : t ∈ classicalTags := by
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hFT : IsFundTag t := by
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> exact trivial
  have hne : ¬ ExceptionalFundTag3 t := by
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ExceptionalFundTag3]
  have hmod := Upgrade.statedClassicalModel_of_lieModel hcl hS
  have hsimp : IsSimpleGroup S :=
    (LieType.Simplicity.fam_classical_converse S ⟨t, n, 3, 1, hmod⟩).2.2
  refine ⟨hsimp, fun s hs => ?_⟩
  obtain ⟨ψ, hψ, hker⟩ := Upgrade.lieModelCentralCover t n 3 1 Nat.prime_three (by norm_num) hFT
    hmod.1 S hS
  exact oddCentralizerFreeTag_of_classical hFT hne n Nat.prime_three hFT hmod.1 S ψ hψ hker s hs

variable {W : Type} [Group W] [Finite W] {Φ : Set (Subgroup W)} {K K' : Subgroup W} {k k' : W}

theorem quotCenter_reduction (h : TwinBase3 Φ K K' k k') (N : Subgroup W) [N.Normal]
    (hN : N = Subgroup.zpowers (k * k')) {t : Assembly.LowTwoRank.StatedLieTag} {n : ℕ}
    (ht : ClassicalTag3 t) (hS : LieModel ((W ⧸ N) ⧸ Subgroup.center (W ⧸ N)) t n 3 1) :
    Function.Surjective ((QuotientGroup.mk' (Subgroup.center (W ⧸ N))).comp
        (QuotientGroup.mk' N)) ∧
      IsPGroup 2 ↥((QuotientGroup.mk' (Subgroup.center (W ⧸ N))).comp (QuotientGroup.mk' N)).ker ∧
      IsSimpleGroup ((W ⧸ N) ⧸ Subgroup.center (W ⧸ N)) ∧
      Balance.oddCoreIn (Subgroup.centralizer
        ({(QuotientGroup.mk' (Subgroup.center (W ⧸ N))).comp (QuotientGroup.mk' N) k} :
          Set ((W ⧸ N) ⧸ Subgroup.center (W ⧸ N)))) = ⊥ := by
  set f := (QuotientGroup.mk' (Subgroup.center (W ⧸ N))).comp (QuotientGroup.mk' N) with hfdef
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective N)
  have : Finite ((W ⧸ N) ⧸ Subgroup.center (W ⧸ N)) := Finite.of_surjective f hf
  have hf2 := isPGroup_ker_quotCenter h N hN
  obtain ⟨hs, hO⟩ := simple_oddFree_of_lieModel ht hS
  refine ⟨hf, hf2, hs, hO _ ?_⟩
  have hk1 : f k ≠ 1 := fun h1 => not_mem_ker h f hf2 1 (by simpa using h1)
  exact orderOf_eq_prime (by rw [sq, ← map_mul, h.invK.sq, map_one]) hk1

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
