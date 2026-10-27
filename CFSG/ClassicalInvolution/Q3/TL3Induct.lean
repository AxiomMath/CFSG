module

public import CFSG.ClassicalInvolution.Q3.TL3LeafEdge

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

@[expose] def TightSelfGen {Y : Type} [Group Y] (R : Subgroup Y) : Prop :=
  (⨆ g : Y, conjSub g (tightCore R)) = ⊤

@[expose] def TightOddFree (Y : Type) [Group Y] : Prop :=
  classicalInvolutionOddCore Y = ⊥

@[expose] def TightCls (Y : Type) [Group Y] (R : Subgroup Y) (S : Sylow 2 R) (_t : Y) : Prop :=
  Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2) ∧ TightSelfGen R ∧ TightOddFree Y

@[expose] def TightInO2 {Y : Type} [Group Y] (t : Y) : Prop :=
  ∃ P : Subgroup Y, P.Normal ∧ IsPGroup 2 P ∧ t ∈ P

@[expose] def TightEdgeless {Y : Type} [Group Y] (R : Subgroup Y) : Prop :=
  Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore R))

@[expose] def TightActs3 {Y : Type} [Group Y] (R : Subgroup Y) (t : Y) : Prop :=
  ∃ (x : Y) (k : ℕ), x ∈ Subgroup.centralizer ({t} : Set Y) ∧ x ^ 3 ^ k = 1 ∧
    ∃ r ∈ R, ⁅x, r⁆ ∉ oddCoreImg R

@[expose] def TightE4 (Y : Type) [Group Y] : Prop :=
  ∃ (Q : Type) (_ : Group Q) (f : Y →* Q), Function.Surjective f ∧ IsPGroup 2 ↥f.ker ∧
    f.ker ≠ ⊥ ∧
      (CFSG.Blueprint.LieModel Q .PSp 3 2 1 ∨ CFSG.Blueprint.LieModel Q .POmegaPlus 4 2 1)

theorem TightE4.of_surjective {Y Y' : Type} [Group Y] [Group Y'] (g : Y →* Y')
    (hg : Function.Surjective g) (hk : IsPGroup 2 ↥g.ker) (h : TightE4 Y') : TightE4 Y := by
  obtain ⟨Q, _, f, hfs, hf2, hf1, hQ⟩ := h
  refine ⟨Q, inferInstance, f.comp g, hfs.comp hg, ?_, fun hbot => hf1 ?_, hQ⟩
  · rw [← MonoidHom.comap_ker]
    exact hf2.comap_of_ker_isPGroup g hk
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := hg x
    have hy : y ∈ (f.comp g).ker := by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
      exact hx
    rw [hbot, Subgroup.mem_bot] at hy
    rw [hy, map_one]
    exact Subgroup.one_mem _

@[expose] def TightEx (Y : Type) [Group Y] (R : Subgroup Y) (_S : Sylow 2 R) (t : Y) : Prop :=
  TightInO2 t ∨ (TightEdgeless R ∧ ¬ TightActs3 R t) ∨
    (TightEdgeless R ∧ ∃ f : Y →* CFSG.Blueprint.NativeSporadic.Carrier .M12,
      Function.Surjective f ∧ IsPGroup 2 ↥f.ker) ∨ TightE4 Y

theorem tightHasLift_of_good {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R}
    {t : Y} (hd : TightDatum R S t) (h : GoodThreeElement R t) : TightHasLift R t := by
  obtain ⟨x, k, hxC, hx3, hxR, hxD⟩ := h
  have hCR : Subgroup.centralizer ({t} : Set Y) ≤ Subgroup.normalizer (R : Set Y) :=
    hd.le_normalizer
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e1⟩ := QuaternionStructure.nonempty_mulEquiv_sylow_of_isPGroup_oddCore_quotient
    hd.twoGroup S
  have hS8 := tl3_nonempty_mulEquiv_q8 S hd.quat hd.twoGroup hCR hxC hx3 hxR
  obtain ⟨e2⟩ := id hS8
  have hsub := isSubnormal_threeElement_join hd.cent hCR (e1.trans e2) hxC hx3 hxR hxD
  exact ⟨_, (tightCore_le R).trans (le_sup_left.trans le_sup_left),
    isClassicalMember3_of_subnormal S hS8 hd.mem hd.order hd.cent hd.normal hd.twoGroup hxC hx3
      hxR hsub⟩

@[expose] def TightBelow (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n → ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightDatum R S t → TightCls Y R S t → TightEx Y R S t ∨ GoodThreeElement R t

@[expose] def TightFStarQuasisimple (Y : Type) [Group Y] : Prop :=
  CFSG.Open.IsQuasisimple ↥(genFittingFStar Y)

@[expose] def TightTwisted (Y : Type) [Group Y] (t : Y) : Prop :=
  ∃ L : Subgroup Y, CFSG.IsComponent L ∧ L.Normal ∧ layer Y = L ∧ t ∈ L ∧
    (∃ x ∈ L, x * t ≠ t * x) ∧ genFittingFitting Y ≤ Subgroup.center Y ∧
    ¬ genFittingFitting Y ≤ L

@[expose] def TightDichotomy (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t →
      TightInO2 t ∨ TightFStarQuasisimple Y ∨ TightTwisted Y t

section Cit3


@[expose] def TightInductive (N : ℕ) : Prop :=
  CIT3Below N → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < N →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t →
      TightEx Y R S t ∨ GoodThreeElement R t

@[expose] def TightStep (n : ℕ) : Prop :=
  CIT3Below n → TightBelow n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t →
      TightEx Y R S t ∨ GoodThreeElement R t

theorem tightInductive_of_step (h : ∀ n, TightStep n) (N : ℕ) : TightInductive N := by
  intro hA
  have key : ∀ n, n ≤ N → TightBelow n := by
    intro n
    induction n with
    | zero =>
      intro _ Y _ _ hlt
      exact absurd hlt (Nat.not_lt_zero _)
    | succ k ih =>
      intro hk Y _ _ hlt R S t hd hc
      by_cases hY : Nat.card Y < k
      · exact ih (by omega) Y hY R S t hd hc
      · exact h k (CIT3Below.mono (by omega) hA) (ih (by omega)) Y (by omega) R S t hd hc
  intro Y _ _ hlt R S t hd hc
  exact key N le_rfl Y hlt R S t hd hc

@[expose] def TightTwistStep (n : ℕ) : Prop :=
  CIT3Below n → TightBelow n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t →
      ¬ TightInO2 t → TightTwisted Y t → TightEx Y R S t ∨ GoodThreeElement R t

@[expose] def TightSmallBase : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CIT3Below (Nat.card Y) →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t →
      ¬ TightInO2 t → TightFStarQuasisimple Y →
        TwoSubgroupsFourGenerated (genFittingFStar Y) → TightEx Y R S t ∨ GoodThreeElement R t

@[expose] def TightLargeEdge (n : ℕ) : Prop :=
  CIT3Below n → TightBelow n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t →
      ¬ TightInO2 t → TightFStarQuasisimple Y →
        ¬ TwoSubgroupsFourGenerated (genFittingFStar Y) → ¬ TightEdgeless R

@[expose] def TightLargeLift (n : ℕ) : Prop :=
  CIT3Below n → TightBelow n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t →
      ¬ TightInO2 t → TightFStarQuasisimple Y →
        ¬ TwoSubgroupsFourGenerated (genFittingFStar Y) → ¬ TightEdgeless R →
          GoodThreeElement R t

theorem tightStep_of_parts (h0 : ∀ n, TightDichotomy n) (htw : ∀ n, TightTwistStep n)
    (h1 : TightSmallBase) (h2 : ∀ n, TightLargeEdge n) (h3 : ∀ n, TightLargeLift n) :
    ∀ n, TightStep n := by
  intro n hA hb Y _ _ hn R S t hd hc
  by_cases hE2 : TightInO2 t
  · exact Or.inl (Or.inl hE2)
  rcases (h0 n Y hn R S t hd hc).resolve_left hE2 with hQ | htw'
  swap
  · exact htw n hA hb Y hn R S t hd hc hE2 htw'
  by_cases hsmall : TwoSubgroupsFourGenerated (genFittingFStar Y)
  · exact h1 Y (by rw [hn]; exact hA) R S t hd hc hE2 hQ hsmall
  · exact Or.inr (h3 n hA hb Y hn R S t hd hc hE2 hQ hsmall
      (h2 n hA hb Y hn R S t hd hc hE2 hQ hsmall))

@[expose] def TightR4 : Prop :=
  ∀ n : ℕ, CIT3Below n → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
    Nat.card G < n → (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ¬ TwoSubgroupsFourGenerated (genFittingFStar G) →
    ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G), TightDatum R S t →
      Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2)

end Cit3

end CFSG.ClassicalInvolution.Q3
