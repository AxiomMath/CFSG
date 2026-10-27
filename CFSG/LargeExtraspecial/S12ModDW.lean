module

public import CFSG.LargeExtraspecial.S12ModDWDefs
public import CFSG.LargeExtraspecial.DW2AEleven
public import CFSG.LargeExtraspecial.DW2AOut

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.RankThree.OrthogonalInvolutions CFSG.ComponentClassification.OuterAutomorphisms

theorem outcome_casesN
    (hF : DW2FieldInput)
    (hO : ∀ (X : Type) [Group X] [Finite X], NativeSporadic.IsSporadic X .J2 →
      IsPGroup 2 (Outer X))
    {X : Type} [Group X] [Finite X] (hX : CFSG.Timmesfeld.Outcome X) {D : Set X}
    (hD : IsTransClass34 D) :
    IsPGroup 2 (Outer X) ∨ LieModel X .POmegaPlus 4 2 1 ∨ LieModel X .trialityD4 0 2 1 ∨
      LieModel X .twistedE6 0 2 1 := by
  have hF' : ∀ (t : StatedLieTag) (n f : ℕ), 2 ≤ f →
      ((t = .PSL ∧ 3 ≤ n) ∨ (t = .PSp ∧ 3 ≤ n) ∨ ((t = .POmegaPlus ∨ t = .POmegaMinus) ∧ 4 ≤ n) ∨
        (n = 0 ∧ t ∈ ({.G2, .trialityD4, .F4, .E6, .twistedE6, .E7, .E8} :
          Finset StatedLieTag))) → ¬ LieModel X t n 2 f :=
    fun t n f hf ht h => hF X t n f hf ht h D hD
  rcases hX with ⟨n, f, hn, hf, h⟩ | ⟨n, f, hn, hf, h⟩ | ⟨n, f, hn, hf, h | h⟩ | ⟨f, hf, h⟩ |
    ⟨f, hf, t, ht, h⟩ | h | he | h
  · rcases Nat.lt_or_ge f 2 with hf2 | hf2
    · obtain rfl : f = 1 := by omega
      exact Or.inl (isPGroup_outer_psl hn h)
    · exact absurd h (hF' _ _ _ hf2 (Or.inl ⟨rfl, hn⟩))
  · rcases Nat.lt_or_ge f 2 with hf2 | hf2
    · obtain rfl : f = 1 := by omega
      exact Or.inl (isPGroup_outer_psp hn h)
    · exact absurd h (hF' _ _ _ hf2 (Or.inr (Or.inl ⟨rfl, hn⟩)))
  · rcases Nat.lt_or_ge f 2 with hf2 | hf2
    · obtain rfl : f = 1 := by omega
      rcases Nat.lt_or_ge n 5 with hn5 | hn5
      · obtain rfl : n = 4 := by omega
        exact Or.inr (Or.inl h)
      · exact Or.inl (isPGroup_outer_POmegaPlus hn5 h)
    · exact absurd h (hF' _ _ _ hf2 (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, hn⟩))))
  · rcases Nat.lt_or_ge f 2 with hf2 | hf2
    · obtain rfl : f = 1 := by omega
      exact Or.inl (isPGroup_outer_POmegaMinus h)
    · exact absurd h (hF' _ _ _ hf2 (Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, hn⟩))))
  · exact absurd h (hF' _ _ _ hf (Or.inr (Or.inr (Or.inr ⟨rfl, by decide⟩))))
  · rcases Nat.lt_or_ge f 2 with hf2 | hf2
    · obtain rfl : f = 1 := by omega
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inl (isPGroup_outer_F4 h)
      · exact Or.inl (isPGroup_outer_E6 h)
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inl (isPGroup_outer_E78 (Or.inl rfl) h)
      · exact Or.inl (isPGroup_outer_E78 (Or.inr rfl) h)
    · exact absurd h (hF' _ _ _ hf2 (Or.inr (Or.inr (Or.inr ⟨rfl, by revert ht; cases t <;>
        decide⟩))))
  · exact Or.inl (isPGroup_outer_psu h)
  · obtain ⟨e⟩ := he
    exact Or.inl (isPGroup_outer_alt6 e)
  · exact Or.inl (hO X h)

namespace Alpha

variable {G : Type} [Group G] [Finite G] {S : Setting G} {W : Submodule (ZMod 2) S.Qt}

theorem a2Action_Xbar :
    A2Mod.A2Action {x : Xbar S W | (x : S.O) ∈ Tset S W} S.q
      (S.O.subtype.comp (Xbar S W).subtype) :=
  ⟨S.q_nondegenerate, S.O.subtype_injective.comp (Xbar S W).subtype_injective,
    fun x v => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (x : S.O).2 v,
    fun _ hd => hd.2⟩

theorem rootClass_Xbar (hA : Hyp S W) [IsSimpleGroup G] (hn : 2 ≤ S.width) {h₀ : G}
    (hx₀ : IsDx S W h₀) {t₀ : S.O} (ht₀ : t₀ ∈ Abar S (S.clPre W) h₀) (ht₀1 : t₀ ≠ 1) :
    A2Mod.RootClass (Xbar S W) {x : Xbar S W | (x : S.O) ∈ Tset S W} := by
  refine ⟨isTransClass34 hA hn hx₀ ht₀ ht₀1, ?_,
    s12_center_eq_bot fun y hy hc => eq_one_of_mem_center hA (by omega) hy hc,
    s12_normal_pGroup_eq_bot (noNormalTwo_Xbar hA)⟩
  obtain ⟨d, hd, e, he, h4⟩ := exists_orderOf_eq_four hA hn hx₀
  exact ⟨⟨d, hd.1⟩, hd, ⟨e, he.1⟩, he, by rw [s12_orderOf_mul_coe]; exact h4⟩

theorem outTwoN
    [IsSimpleGroup G] (hARS : CFSG.Timmesfeld.ARSInput)
    (hInsp : DW2OutInspectionInputN) (hA : Hyp S W) (hn : 2 ≤ S.width) {h₀ : G}
    (hx₀ : IsDx S W h₀) : OutTwo S W := by
  have : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  have : Finite (S.Qt ≃ₗ[ZMod 2] S.Qt) := finite_linearEquiv
  obtain ⟨t₀, ht₀, -, -, ht₀1, -, -⟩ := exists_two_mem_Abar hA (by omega) hx₀
  obtain ⟨hT₀, -⟩ := Abar_isTypeA hA hx₀ ht₀ ht₀1
  rcases outcome_casesN hInsp.field hInsp.outerJ2 (outcome_Xbar hA hn hx₀ ht₀ ht₀1 hARS)
      (isTransClass34 hA hn hx₀ ht₀ ht₀1) with hO | hP | hM | hM
  · exact outTwo_of_outer hA hO
  ·
    have hD := isA2Class hA hn hx₀ ht₀ ht₀1
    exact hInsp.2.2.1 S.Qt S.q S.q_nondegenerate (XbarL S W) (Ybar S)
      (fun y hy v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (Ybar_le_O hy) v)
      XbarL_le_Ybar (Ybar_le_normalizer_XbarL hA)
      (lieModel_POmegaPlus_of_mulEquiv
        ((Xbar S W).equivMapOfInjective S.O.subtype S.O.subtype_injective) hP)
      (TsetL S W) hD.1 hD.2.1 (by rintro _ ⟨τ, hτ, rfl⟩; exact hτ.2)
  ·
    exfalso
    have h3 := hInsp.moduleD4 (Xbar S W) hM S.Qt (S.O.subtype.comp (Xbar S W).subtype)
      (S.O.subtype_injective.comp (Xbar S W).subtype_injective) ⟨t₀, Abar_le_Xbar hx₀ ht₀⟩
      (fun h => ht₀1 (congrArg Subtype.val h))
      (Subtype.ext (Tset_mul_self (mem_Tset_of_mem_Abar hA hx₀ ht₀ ht₀1)))
    have h2 : finrank (ZMod 2) (commSpace ((S.O.subtype.comp (Xbar S W).subtype)
        ⟨t₀, Abar_le_Xbar hx₀ ht₀⟩)) = 2 := hT₀.2.2.2.1
    omega
  ·
    exact (hInsp.moduleExc (Xbar S W) .twistedE6 (by decide) hM _
      (rootClass_Xbar hA hn hx₀ ht₀ ht₀1) S.Qt S.q _ a2Action_Xbar).elim

theorem false_of_hypN_of_nondeg
    [IsSimpleGroup G] (hARS : CFSG.Timmesfeld.ARSInput)
    (hInsp : DW2OutInspectionInputN) (hA : Hyp S W) (hn : 2 ≤ S.width)
    (hP : NondegWeaklyClosed S) {h₀ : G}
    (hx₀ : IsDx S W h₀) : False :=
  false_of_alpha_of_nondeg hA hn hP hx₀ (outTwoN hARS hInsp hA hn hx₀)

end Alpha

end CFSG.LargeExtraspecial.DW
