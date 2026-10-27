module

public import CFSG.ClassicalInvolution.Q3.Q3NMInner
public import CFSG.ClassicalInvolution.Q3.Q3MFOSAut
public import CFSG.ClassicalInvolution.Q3.Q3PPFundAbs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance

@[expose] def OuterFixedOddFree (t : StatedLieTag) (n : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → LieModel S t n 3 1 →
    ∀ σ : MulAut S, σ * σ = 1 → σ ∉ Q3NM.innSubgroup S → oddCoreIn (Q3NM.fixedSubgroup σ) = ⊥

theorem center_eq_bot_of_isQuasisimple {S : Type} [Group S] [IsSimpleGroup S]
    (hq : CFSG.Open.IsQuasisimple S) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    have := hq.2
    obtain ⟨a, b, hab⟩ := exists_pair_ne (S ⧸ Subgroup.center S)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (QuotientGroup.eq.2 (by rw [h]; exact Subgroup.mem_top _))

section Certified


theorem oddAut_inner_of_cover {t : StatedLieTag} {n : ℕ} (hD4 : ¬ (t = .POmegaPlus ∧ n = 4))
    (hT : t ≠ .trialityD4) (hFT : IsFundTag t) (hadm : StatedLieAdmissible t n 3 1)
    {S : Type} [Group S] [Finite S] (ψ : (modelUniv t n 3 1 Nat.prime_three).K →* S)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center _)
    (hZ : Subgroup.center S = ⊥) :
    ∀ α : MulAut S, Odd (orderOf α) → α ∈ Q3NM.innSubgroup S := by
  have h := Q3NM.oddAut_inner_centralQuotient hD4 hT Nat.prime_three hFT hadm S ψ hψ hker
  let e : S ⧸ Subgroup.center S ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  intro α hα
  have hα' : Odd (orderOf (MulAut.congr e.symm α)) := by
    rwa [MulEquiv.orderOf_eq]
  obtain ⟨y, hy⟩ := h _ hα'
  refine ⟨e y, ?_⟩
  ext x
  have h1 := congrArg (fun φ : MulAut (S ⧸ Subgroup.center S) => e (φ (e.symm x))) hy
  simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.apply_symm_apply, map_mul,
    map_inv, MulEquiv.symm_symm] at h1
  rw [MulAut.conj_apply]
  exact h1

theorem autOddFree_of_outer {t : StatedLieTag} {n : ℕ} (hD4 : ¬ (t = .POmegaPlus ∧ n = 4))
    (hT : t ≠ .trialityD4) (hFT : IsFundTag t) (hcl : t ∈ classicalTags)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hS : LieModel S t n 3 1)
    (hout : ∀ σ : MulAut S, σ * σ = 1 → σ ∉ Q3NM.innSubgroup S →
      oddCoreIn (Q3NM.fixedSubgroup σ) = ⊥) : Q3NM.AutOddFree S := by
  have hadm : StatedLieAdmissible t n 3 1 :=
    (Upgrade.statedClassicalModel_of_lieModel hcl hS).1
  obtain ⟨ψ, hψ, hker⟩ :=
    Upgrade.lieModelCentralCover t n 3 1 Nat.prime_three (by norm_num) hFT hadm S hS
  obtain ⟨hSq, -, -, -, -⟩ := Q3NM.centralQuotientData Nat.prime_three hFT hadm S ψ hψ hker
  have hZ := center_eq_bot_of_isQuasisimple hSq
  have hperf : Group.IsPerfect S := ⟨hSq.1⟩
  refine Q3NM.autOddFree_of_fixedOddFree hZ (oddAut_inner_of_cover hD4 hT hFT hadm ψ hψ hker hZ) ?_
  intro σ hσ
  by_cases hin : σ ∈ Q3NM.innSubgroup S
  · obtain ⟨s, rfl⟩ := hin
    have hss : s * s = 1 := by
      apply Q3NM.conj_injective_of_center_eq_bot hZ
      rw [map_mul, hσ, map_one]
    by_cases hs1 : s = 1
    · subst hs1
      rw [map_one, Q3PP.fixedSubgroup_one_eq_top]
      exact Q3MFO.oddCoreIn_top_eq_bot_of_perfect_simple hperf
    · rw [Q3NM.fixedSubgroup_conj]
      exact modelOddCentralizerFree3_proved t n Nat.prime_three hFT hadm S ψ hψ hker s
        (orderOf_eq_prime (by rw [sq]; exact hss) hs1)
  · exact hout σ hσ hin

end Certified

end CFSG.ClassicalInvolution.Q3.TL4
