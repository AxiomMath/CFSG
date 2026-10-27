module

public import CFSG.GH74.GLS.Stage4.RestDodecA
public import CFSG.GH74.GLS.Stage4.RestDodecB
public import CFSG.CharacterTheory.PSL2Table.Classes
public import CFSG.CharacterTheory.PSL2Table.Halves
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public import CFSG.GH74.Bender
public import CFSG.GH74.GLS.Stage4.LocalAssembly
public import CFSG.GH74.Statements
public import CFSG.LieType.Steinberg.G2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate43

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] {D : Ch6Notation G}

theorem Ch6Core.toCor97 (h : Ch6Core D) (hL : D.L92) :
    Cor97 D.p D.H D.w₁ D.r₂ D.P D.root where
  prime := h.prime
  p_ne_two := h.p_ne_two
  comm_H := h.H_comm
  conj_H₁ := h.toCh6Basics.conj_H₁
  conj_H₂ := h.toCh6Basics.conj_H₂
  sq₁ := h.toCh6Basics.sq₁
  sq₂ := h.toCh6Basics.sq₂
  pow := h.toCh6Basics.pow
  H_pPrime := h.H_pPrime
  U_pGroup := h.P_pGroup
  U_gen := h.U_gen
  ne_bot := h.toCh6Basics.root_ne_bot
  root_comm := h.toCh6Basics.root_comm
  root_exp := h.toCh6Basics.root_exp
  invariant := h.toCh6Basics.invariant
  act₁ := h.toCh6Basics.act₁
  act₂ := h.toCh6Basics.act₂
  opp := h.opp'
  L92 := hL
  sl2₁ := h.toCh6Basics.sl2₁
  sl2₆ := h.toCh6Basics.sl2₆

theorem Ch6Post.out (h : Ch6Post D) : Ch6Out G := by
  have hc := h.core
  have hC := hc.toCor97 h.L92
  have hG := hc.gen97 h.zclass
  refine ⟨D.p, D.H, D.w₁, D.r₂, D.P, D.root, D.z, D.S, D.K₁, D.K₂, D.F, D.P₀, D.q₂, hC, hG,
    hc.q₂_odd, ?_⟩
  rcases hc.q_rel with hq | hq
  · exact Or.inl ⟨hq ▸ hc.q₁_ge, hc.toCh6Basics.rootOrdersG2 hq⟩
  · exact Or.inr ⟨hc.q₂_ge, hc.toCh6Basics.rootOrdersD4 hq⟩

@[expose] def Ch6OutPlus (G : Type) [Group G] : Prop :=
  ∃ (p : ℕ) (H : Subgroup G) (r₁ r₂ : G) (U : Subgroup G) (root : ℤ → Subgroup G) (z : G)
    (S K₁ K₂ F P₀ : Subgroup G) (q : ℕ),
    Cor97 p H r₁ r₂ U root ∧ Gen97 p H r₁ r₂ U root z S K₁ K₂ F P₀ ∧ Odd q ∧
      ((5 ≤ q ∧ RootOrdersG2 root q) ∨
        (3 ≤ q ∧ ∀ i : ℤ, 1 ≤ i → i ≤ 6 → Nat.card ↥(root i) = if i % 2 = 1 then q ^ 3 else q)) ∧
      ((∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) ∧ z ∈ K₁ ∧ z ∈ K₂) ∧
      (∀ i j : ℤ, 1 ≤ i → i ≤ 6 → 1 ≤ j → j ≤ 6 → i ≠ j → ¬ HEquiv H (root i) (root j)) ∧
      ((∀ x ∈ root 2, ∀ y ∈ root 4, x * y = y * x) ∧ (∀ x ∈ root 4, ∀ y ∈ root 6, x * y = y * x) ∧
        (∀ x ∈ root 2, ∀ y ∈ root 6, ⁅x, y⁆ ∈ root 4))

theorem Ch6OutPlus.toOut (h : Ch6OutPlus G) : Ch6Out G := by
  obtain ⟨p, H, r₁, r₂, U, root, z, S, K₁, K₂, F, P₀, q, hC, hG, hq, hc, -, -, -⟩ := h
  refine ⟨p, H, r₁, r₂, U, root, z, S, K₁, K₂, F, P₀, q, hC, hG, hq, ?_⟩
  rcases hc with hc | ⟨h3, hc⟩
  · exact Or.inl hc
  · exact Or.inr ⟨h3, Or.inl hc⟩

theorem Ch6Basics.rootOrdersD4a (h : Ch6Basics D) (hq : D.q₁ = D.q₂ ^ 3) :
    ∀ i : ℤ, 1 ≤ i → i ≤ 6 → Nat.card ↥(D.root i) = if i % 2 = 1 then D.q₂ ^ 3 else D.q₂ := by
  intro i h1 h6
  interval_cases i
  · rw [root_p1, h.card_X₁, hq]
    simp
  · rw [root_p2, DodecA.card_conjBy, h.card_X₂']
    simp
  · rw [root_p3, DodecA.card_conjBy, h.card_X₁', hq]
    simp
  · rw [root_p4, h.card_X₂]
    simp
  · rw [root_p5, DodecA.card_conjBy, h.card_X₁, hq]
    simp
  · rw [root_p6, DodecA.card_conjBy, h.card_X₂']
    simp

theorem Ch6Post.outPlus (h : Ch6Post D) : Ch6OutPlus G := by
  have hc := h.core
  have hC := hc.toCor97 h.L92
  have hG := hc.gen97 h.zclass
  refine ⟨D.p, D.H, D.w₁, D.r₂, D.P, D.root, D.z, D.S, D.K₁, D.K₂, D.F, D.P₀, D.q₂, hC, hG,
    hc.q₂_odd, ?_, ⟨hc.K_comm, hc.z_mem_K₁, hc.z_mem_K₂⟩, hc.inequiv, hc.long_A2⟩
  rcases hc.q_rel with hq | hq
  · exact Or.inl ⟨hq ▸ hc.q₁_ge, hc.toCh6Basics.rootOrdersG2 hq⟩
  · exact Or.inr ⟨hc.q₂_ge, hc.toCh6Basics.rootOrdersD4a hq⟩

@[expose] def Ch6CaseRestPlus : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q₁ q₂ : ℕ), IsTwoCentralG2TypeG2At G Gs q₁ q₂ →
      ¬ (q₁ = 9 ∧ q₂ = 9) → (¬ ∃ n : ℕ, 3 ≤ n ∧ q₁ = 3 ^ n ∧ q₂ = 3 ^ n) → Ch6OutPlus G

@[expose] def Ch6RestMain : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q₁ q₂ : ℕ), IsTwoCentralG2TypeG2At G Gs q₁ q₂ →
      ¬ (q₁ = 9 ∧ q₂ = 9) → (¬ ∃ n : ℕ, 3 ≤ n ∧ q₁ = 3 ^ n ∧ q₂ = 3 ^ n) →
        ∃ D : Ch6Notation G, Ch6Core D

@[expose] def Ch6RestL92 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q₁ q₂ : ℕ), IsTwoCentralG2TypeG2At G Gs q₁ q₂ →
      ∀ D : Ch6Notation G, Ch6Core D → D.L92

@[expose] def Ch6RestZClass : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q₁ q₂ : ℕ), IsTwoCentralG2TypeG2At G Gs q₁ q₂ →
      ∀ D : Ch6Notation G, Ch6Core D → D.ZClass

theorem ch6CaseRestPlus_of_leaves (hMain : Ch6RestMain) (hL : Ch6RestL92) (hZ : Ch6RestZClass) :
    Ch6CaseRestPlus := by
  intro G _ _ hStd hr Gs _ q₁ q₂ hAt h99 hn
  obtain ⟨D, hD⟩ := hMain G hStd hr Gs q₁ q₂ hAt h99 hn
  exact (Ch6Post.mk hD (hL G hStd hr Gs q₁ q₂ hAt D hD) (hZ G hStd hr Gs q₁ q₂ hAt D hD)).outPlus

theorem ch6CaseRest_of_leaves (hMain : Ch6RestMain) (hL : Ch6RestL92) (hZ : Ch6RestZClass) :
    Ch6CaseRest := by
  intro G _ _ hStd hr Gs _ q₁ q₂ hAt h99 hn
  exact (ch6CaseRestPlus_of_leaves hMain hL hZ G hStd hr Gs q₁ q₂ hAt h99 hn).toOut

end CFSG.GH74.GLS.Stage4.Rest
