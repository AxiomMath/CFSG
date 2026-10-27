module

public import CFSG.CGT.T75G.Sec68Root
public import CFSG.Timmesfeld.CorollaryBOutcome

public section

namespace CFSG.CGT.T75G

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld CFSG.Timmesfeld.ARS CFSG.Blueprint
open scoped commutatorElement

section CaseL

variable {G : Type} [Group G] {R : Set (Subgroup G)}

theorem caseL_psl3 (h : ARS.Hyp G R) (hno : CorB.NoOppCentral R) {A : Subgroup G} (hA : A ∈ R)
    (hmax : ¬ IsCoatom (Subgroup.normalizer (A : Set G))) :
    ∃ f : ℕ, 1 ≤ f ∧ Nat.card A = 2 ^ f ∧ LieModel G .PSL 3 2 f := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hnd := h.nondeg
  have hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A :=
    fun _ hA _ hB e => eq_of_omegaSet_eq h hA hB e
  obtain ⟨Δ, hΔ, hAΔ⟩ := (exists_isTI_iff h hA).1 hmax
  obtain ⟨m, hm⟩ := Sec5.exists_card_gen_eq_pow hR hiso hnd hΩ hΔ.isWeakTI hAΔ
  obtain ⟨hm2, X, hX⟩ := Linear.exists_isRootFrame hR hiso hnd hΩ hΔ hAΔ hm
  have hm3 : m = 2 := by
    by_contra hm3
    have i0 : (⟨0, by omega⟩ : Fin (m + 1)) ≠ ⟨3, by omega⟩ := by simp [Fin.ext_iff]
    have i1 : (⟨1, by omega⟩ : Fin (m + 1)) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
    have i2 : (⟨0, by omega⟩ : Fin (m + 1)) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
    have i3 : (⟨1, by omega⟩ : Fin (m + 1)) ≠ ⟨3, by omega⟩ := by simp [Fin.ext_iff]
    have i4 : (⟨0, by omega⟩ : Fin (m + 1)) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    have i5 : (⟨2, by omega⟩ : Fin (m + 1)) ≠ ⟨3, by omega⟩ := by simp [Fin.ext_iff]
    exact hno _ (hX.mem _ _ i0) _ ⟨hX.mem _ _ i1, hX.commuting _ _ _ _ i0 i1 i2 i3⟩ _
      ⟨hX.mem _ _ i1.symm, hX.commuting _ _ _ _ i0 i1.symm i4 i5⟩ (hX.opposite _ _ i1)
  subst hm3
  obtain ⟨f, hf, hcard, hL⟩ := hX.lieModel hR hiso h.center hm2
  exact ⟨f, hf, hcard A hA, hL⟩

end CaseL

variable {G : Type} [Group G] {T T₁ : Subgroup G} {m : ℕ}

namespace Cfg68

variable (c : Cfg68 T T₁ m)
include c

theorem hyp {d : G} (hd : d ∈ normIn T T₁) (hd1 : d ≠ 1) : CFSG.Timmesfeld.Hyp G (CorB.cls d) := by
  have := c.hy.finite
  have : IsSimpleGroup G := c.hy.simple
  have hs := c.setup hd hd1
  have hnonab := c.hy.nonab
  have hNtop : Subgroup.normalClosure ({d} : Set G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure ({d} : Set G))
      with h | h
    · exfalso
      apply hd1
      have : d ∈ Subgroup.normalClosure ({d} : Set G) := Subgroup.subset_normalClosure rfl
      rw [h] at this
      exact Subgroup.mem_bot.1 this
    · exact h
  refine ⟨c.hy.finite, ⟨d, rfl⟩, hs.isRootInvolutionSet, ?_, ?_, ?_, ?_⟩
  · rw [← CorB.normalClosure_eq]
    exact hNtop
  · intro N hN hodd
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      rw [h, Subgroup.card_top] at hodd
      have heven : 2 ∣ Nat.card G := hs.orderOf_eq ▸ orderOf_dvd_natCard d
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 heven)
  · intro N hN h2
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      have hG2 : IsPGroup 2 G := fun g => by
        obtain ⟨k, hk⟩ := h2 ⟨g, h ▸ Subgroup.mem_top g⟩
        exact ⟨k, congrArg Subtype.val hk⟩
      have hcen := center_eq_bot_of_simple_nonabelian G hnonab
      have : Nontrivial (Subgroup.center G) := hG2.center_nontrivial
      rw [hcen] at this
      exact absurd this (not_nontrivial (⊥ : Subgroup G))
  · exact c.exists_orderOf_eq_four hd hd1

end Cfg68

section Final

theorem Cfg68.lieModel_psl3 (c : Cfg68 T T₁ m) : ∃ f : ℕ, 1 ≤ f ∧ LieModel G .PSL 3 2 f := by
  have := c.hy.finite
  obtain ⟨⟨d, hd⟩, hd1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 c.hy.pair.nontriv
  have hd1 : d ≠ 1 := fun h => hd1' (Subtype.ext h)
  have hH := c.hyp hd hd1
  have hs := c.setup hd hd1
  have hNO := CorB.noOppCentral_rootClass hs.isRootInvolutionSet hs.noOddCent
  obtain ⟨hc, hsc, hm', -⟩ := CorB.largeFacts hH (c.exists_rootSet_ne hd hd1)
  have hARS := arsHyp_rootClass hH hc hsc hm'
  have hA : normIn T T₁ ∈ rootClass (CorB.cls d) :=
    ⟨d, CorB.mem_cls_self d, (c.rootGroup_eq hd hd1).symm⟩
  obtain ⟨f, hf, -, hLM⟩ := caseL_psl3 hARS hNO hA c.not_isCoatom
  exact ⟨f, hf, hLM⟩

end Final

end CFSG.CGT.T75G
