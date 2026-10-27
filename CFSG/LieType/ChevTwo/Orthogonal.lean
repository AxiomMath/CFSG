module

public import CFSG.LieType.ChevTwo.Defs
public import CFSG.LieType.ChevTwo.OrthogonalBasic
public import CFSG.LieType.ChevTwo.OrthogonalAutLarge
public import CFSG.LieType.ChevTwo.OrthogonalAutSmall
public import CFSG.LieType.ChevTwo.OrthogonalAutEight
public import CFSG.LieType.ChevTwo.OrthogonalOddCent
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOCoords
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightSwap
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOKlein
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOPlusLevi
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem omegaTwoAutInduced :
    (∀ n : ℕ, 1 ≤ n → OmegaTwoAutInduced (StatedQuadMinus (n + 1) (ZMod 2) 1 1)) ∧
      (∀ n : ℕ, 2 ≤ n → n ≠ 3 → OmegaTwoAutInduced (StatedQuadPlus (n + 1) (ZMod 2))) := by
  refine ⟨fun n hn => ?_, fun n hn hn3 => ?_⟩
  · rcases (by omega : n = 1 ∨ n = 2 ∨ 3 ≤ n) with rfl | rfl | h
    · exact omegaTwoAutInduced_minus_one
    · exact omegaTwoAutInduced_minus_two
    · exact omegaTwoAutInduced_minus_of_three_le h
  · rcases (by omega : n = 2 ∨ 4 ≤ n) with rfl | h
    · exact omegaTwoAutInduced_plus_two
    · exact omegaTwoAutInduced_plus_of_four_le h

theorem isPGroup_two_zpowers_of_sq_eq_one {G : Type*} [Group G] {a : G} (h : a ^ 2 = 1) :
    IsPGroup 2 (Subgroup.zpowers a) := by
  have hd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one h
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h2
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1]; rfl)
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h2]; rfl)

theorem omegaPlusEightInvolutions : OmegaPlusEightInvolutions := by
  intro α hα
  obtain ⟨τ, hτ⟩ := fix_plusEight (Subgroup.zpowers α) (isPGroup_two_zpowers_of_sq_eq_one hα)
  exact ⟨τ, hτ α (Subgroup.mem_zpowers α)⟩

section L1

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem card_le_two_of_fix {Q : (ι → ZMod 2) → ZMod 2} (hQ : GoodQ Q)
    (hfix : ∀ T : Subgroup (MulAut ↥(StatedOmega Q)), IsPGroup 2 T →
      ∃ τ : MulAut ↥(StatedOmega Q), ∀ t ∈ T, InducedByIso Q (τ * t * τ⁻¹))
    {K : Type} [Group K] (e : K ≃* ↥(StatedOmega Q)) (T : Subgroup (MulAut K))
    (hT : IsPGroup 2 T) (hTi : T ⊓ inner K = ⊥) : Nat.card T ≤ 2 := by
  set φ : MulAut K →* MulAut ↥(StatedOmega Q) := (MulAut.congr e).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.congr e).injective
  set T' : Subgroup (MulAut ↥(StatedOmega Q)) := T.map φ with hT'
  have hT'2 : IsPGroup 2 T' := hT.map φ
  have hT'i : T' ⊓ inner ↥(StatedOmega Q) = ⊥ := by
    have hm : (inner K).map φ = inner ↥(StatedOmega Q) :=
      CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e
    rw [← hm, hT', ← Subgroup.map_inf _ _ φ hφinj, hTi, Subgroup.map_bot]
  obtain ⟨τ, hτ⟩ := hfix T' hT'2
  set ψ : MulAut ↥(StatedOmega Q) →* MulAut ↥(StatedOmega Q) := (MulAut.conj τ).toMonoidHom
  have hψinj : Function.Injective ψ := (MulAut.conj τ).injective
  set T'' := T'.map ψ with hT''
  have hle : T'' ≤ (kappa Q).range := by
    rintro _ ⟨t, ht, rfl⟩
    exact (inducedByIso_iff_mem_range Q _).1 (hτ t ht)
  have hT''i : T'' ⊓ inner ↥(StatedOmega Q) = ⊥ := by
    have hnorm : (inner ↥(StatedOmega Q)).map ψ = inner ↥(StatedOmega Q) := by
      ext a
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact (CFSG.ComponentClassification.OuterAutomorphisms.inner_normal ↥(StatedOmega Q)).conj_mem b hb τ
      · intro ha
        refine ⟨τ⁻¹ * a * τ, (CFSG.ComponentClassification.OuterAutomorphisms.inner_normal ↥(StatedOmega Q)).conj_mem a ha τ⁻¹, ?_⟩
        simp only [ψ, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
        group
    rw [← hnorm, hT'', ← Subgroup.map_inf _ _ ψ hψinj, hT'i, Subgroup.map_bot]
  have hcard := hQ.card_le_two_of_le_range hle hT''i
  calc Nat.card T = Nat.card T' := (Subgroup.card_map_of_injective hφinj).symm
    _ = Nat.card T'' := (Subgroup.card_map_of_injective hψinj).symm
    _ ≤ 2 := hcard

end L1

theorem omegaTwoAutTwoPart : OmegaTwoAutTwoPart := by
  intro ε n hn K _ _ hsimple hK T hT hTi
  have hind := omegaTwoAutInduced
  have hfix_of_induced : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {Q : (ι → ZMod 2) → ZMod 2},
      OmegaTwoAutInduced Q → ∀ T : Subgroup (MulAut ↥(StatedOmega Q)), IsPGroup 2 T →
        ∃ τ : MulAut ↥(StatedOmega Q), ∀ t ∈ T, InducedByIso Q (τ * t * τ⁻¹) :=
    fun {ι} _ _ {Q} h T _ => ⟨1, fun t _ => by simpa using h t⟩
  cases ε
  ·
    obtain ⟨e⟩ := hK
    exact card_le_two_of_fix (goodQ_minus hn) (hfix_of_induced (hind.1 n hn)) e T hT hTi
  ·
    obtain ⟨e⟩ := hK
    rcases (by omega : n = 1 ∨ n = 3 ∨ (2 ≤ n ∧ n ≠ 3)) with rfl | rfl | ⟨h2, h3⟩
    · exact absurd (e.symm.isSimpleGroup) not_isSimpleGroup_statedOmega_plus_two
    · exact card_le_two_of_fix (goodQ_plus (n := 3) (by norm_num))
        (fun T hT => fix_plusEight T hT) e T hT hTi
    · exact card_le_two_of_fix (goodQ_plus h2)
        (hfix_of_induced (hind.2 n h2 h3)) e T hT hTi

theorem orthOddCentCore : ∀ n : ℕ, 1 ≤ n →
    OrthOddCentCore (StatedQuadPlus (n + 1) (ZMod 2)) true n ∧
      OrthOddCentCore (StatedQuadMinus (n + 1) (ZMod 2) 1 1) false n := fun n hn =>
  ⟨orthOddCentCore_of_strong (orthOddCentCoreStrong n hn).1,
    orthOddCentCore_of_strong (orthOddCentCoreStrong n hn).2⟩

end CFSG.LieType.ChevTwo
