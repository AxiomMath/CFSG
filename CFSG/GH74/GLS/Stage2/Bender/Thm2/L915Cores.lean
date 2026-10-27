module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Lem912
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Main

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

@[expose] def Prop9_5Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx9 G z k S M p →
    ∀ N A B : Subgroup G, L915.Hyp95 z M p N A B → Op 2 N = ⊥ → Fs N ≠ Op p N →
      ¬ A ≤ centralizer (Em N : Set G) → False

@[expose] def Prop9_11Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx9 G z k S M p →
    ∀ X V N : Subgroup G, X ≤ Op p M → X ≠ ⊥ → z ∈ normalizer (X : Set G) → ⁅X, zpowers z⁆ = X →
      IsCoatom N → normalizer (X : Set G) ≤ N → V ≤ Op p M ⊓ N ⊓ Cen z → IsElementaryAbelian p ↥V →
      Nat.card ↥V = p ^ 2 → (∀ v ∈ V, v ≠ 1 → NN z p (Op p M) (zpowers v)) →
      Fm N = Op p N → Em N ≠ ⊥ → False

namespace L915

theorem prop9_5_of_core (h512 : IG_5_12) (h19 : B_signalizer_19_9) (h118 : IG_11_8)
    (hcore : Prop9_5Core) : Prop9_5 := by
  intro G _ _ z k S M p hC N A B hN hAP hBP hA0 hB0 hAz hBz hAc hAN hBN hAN'
  have h : Hyp95 z M p N A B :=
    ⟨hN, hAP, hBP, hA0, hB0, hAz, hBz, hAc, hAN, hBN, hAN'⟩
  by_contra hnot
  exact hcore G z k S M p hC N A B h (lemma9_6a h118 hC h) hnot
    (lemma9_6c h512 h19 h118 hC h hnot)

theorem prop9_11_of_core (h512 : IG_5_12) (h19 : B_signalizer_19_9) (h118 : IG_11_8)
    (h1123 : IG_11_23) (hcore : Prop9_11Core) : Prop9_11 := by
  intro G _ _ z k S M p hC X V N hXP hX0 hzX hXc hN hXN hV hVe hV2 hv
  by_contra hnot
  obtain ⟨hFm, hEm⟩ := lemma9_12 h512 h19 h118 h1123 hC hXP hzX hXc hN hXN hV hVe hV2 hv hnot
  exact hcore G z k S M p hC X V N hXP hX0 hzX hXc hN hXN hV hVe hV2 hv hFm hEm

end L915

theorem lemma9_15_of_cores (h95 : Prop9_5Core) (h911 : Prop9_11Core) : Lemma9_15 :=
  lemma9_15_of
    (L915.lemma9_16_of ig_5_12_thm
      (L915.prop9_5_of_core ig_5_12_thm CFSG.GH74.GLS.Stage2.Signalizer.L199.ig_19_9 ig_11_8_thm h95))
    (L915.prop9_11_of_core ig_5_12_thm CFSG.GH74.GLS.Stage2.Signalizer.L199.ig_19_9 ig_11_8_thm
      ig_11_23_thm h911)

end CFSG.GH74.GLS.Stage2.Bender.Thm2
