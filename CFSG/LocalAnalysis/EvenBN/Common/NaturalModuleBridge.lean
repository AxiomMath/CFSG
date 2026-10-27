module

public import CFSG.LocalAnalysis.EvenBN.Common.FongSeitzFourB
public import CFSG.LocalAnalysis.EvenBN.Common.NaturalModule
public import CFSG.LocalAnalysis.EvenBN.U4.Prelim.SL2Modules

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Subgroup
open CFSG.LocalAnalysis.ComponentInitial.EvenLinearTwoModule (actionFixed mem_actionFixed)
open scoped MatrixGroups

variable {G : Type*} [Group G] {k : Type*} [Field k] [Finite k] [CharP k 2]

theorem inf_centralizer_eq_bot_of_not_le [Finite G] {n : ℕ} (hk : Nat.card k = 2 ^ n)
    (hn : 2 ≤ n) {X A : Subgroup G} (ψ : X ≃* SL(2, k)) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hXA : X ≤ normalizer (A : Set G)) (hcard : Nat.card A = (2 ^ n) ^ 2)
    (hnc : ¬ X ≤ centralizer (A : Set G)) : A ⊓ centralizer (X : Set G) = ⊥ := by
  have hXD : X ≤ normalizer ((A ⊓ centralizer (X : Set G) : Subgroup G) : Set G) :=
    (le_centralizer_iff.1 inf_le_right).trans (centralizer_le_normalizer _)
  rcases sl2_eq_bot_or_eq_of_card_le ψ hk hn hcomm (a := 2 * n)
      (by rw [hcard, ← pow_mul, mul_comm]) le_rfl hXA hXD inf_le_left hnc with h | h
  · exact h
  · exact absurd (le_centralizer_iff.1 (inf_eq_left.1 h)) hnc

theorem card_inf_centralizer_le_of_inf_centralizer_eq_bot [Finite G] {n : ℕ}
    (hk : Nat.card k = 2 ^ n) {X A P : Subgroup G} (ψ : X ≃* SL(2, k))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hXA : X ≤ normalizer (A : Set G))
    (hcard : Nat.card A = (2 ^ n) ^ 2) (hfix : A ⊓ centralizer (X : Set G) = ⊥) (hPX : P ≤ X)
    (hP : Nat.card P = Nat.card k) :
    Nat.card (A ⊓ centralizer (P : Set G) : Subgroup G) ≤ 2 ^ n := by
  set P' : Subgroup X := P.subgroupOf X with hP'
  have hP'card : Nat.card (P'.map ψ.toMonoidHom) = Nat.card k := by
    rw [card_map_of_injective ψ.injective, hP', Nat.card_congr (subgroupOfEquivOfLe hPX).toEquiv,
      hP]
  obtain ⟨g, hg⟩ := exists_conj_eq_upperUnipotent hk hP'card
  set ψ' : X ≃* SL(2, k) := ψ.trans (MulAut.conj g) with hψ'
  have hψ'P : ∀ x : X, ψ' x ∈ CFSG.Timmesfeld.upperUnipotent k ↔ (x : G) ∈ P := by
    intro x
    rw [← hg, Subgroup.map_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := ψ'.injective hyx
      rw [← this]
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  let : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  let ρ : SL(2, k) →* MulAut A :=
    (A.normalizerMonoidHom).comp ((Subgroup.inclusion hXA).comp ψ'.symm.toMonoidHom)
  have hρ' : ∀ (x : X) (a : A), ((ρ (ψ' x) a : A) : G) = (x : G) * a * (x : G)⁻¹ := by
    intro x a
    change ((ψ'.symm (ψ' x) : X) : G) * a * ((ψ'.symm (ψ' x) : X) : G)⁻¹ = _
    rw [MulEquiv.symm_apply_apply]
  have hD : actionFixed ρ ⊤ = ⊥ := by
    refine eq_bot_iff.2 fun a ha => ?_
    have haC : (a : G) ∈ A ⊓ centralizer (X : Set G) := by
      refine mem_inf.2 ⟨a.2, mem_centralizer_iff.2 fun x hx => ?_⟩
      have e := congrArg Subtype.val (ha (ψ' ⟨x, hx⟩) (mem_top _))
      rw [hρ'] at e
      calc x * (a : G) = (x * a * x⁻¹) * x := by group
        _ = (a : G) * x := by rw [e]
    rw [hfix, mem_bot] at haC
    exact Subtype.ext haC
  have hfixmem : ∀ a : A, a ∈ actionFixed ρ (CFSG.Timmesfeld.upperUnipotent k) ↔
      (a : G) ∈ centralizer (P : Set G) := by
    intro a
    rw [mem_actionFixed, mem_centralizer_iff]
    constructor
    · intro ha x hx
      have e := congrArg Subtype.val (ha (ψ' ⟨x, hPX hx⟩) ((hψ'P _).2 hx))
      rw [hρ'] at e
      calc x * (a : G) = (x * a * x⁻¹) * x := by group
        _ = (a : G) * x := by rw [e]
    · intro ha s hs
      obtain ⟨x, rfl⟩ := ψ'.surjective s
      apply Subtype.ext
      rw [hρ']
      have hc := ha x ((hψ'P x).1 hs)
      rw [hc, mul_inv_cancel_right]
  have e : (actionFixed ρ (CFSG.Timmesfeld.upperUnipotent k)).map A.subtype =
      A ⊓ centralizer (P : Set G) := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact mem_inf.2 ⟨a.2, (hfixmem a).1 ha⟩
    · intro hy
      exact ⟨⟨y, (mem_inf.1 hy).1⟩, (hfixmem ⟨y, (mem_inf.1 hy).1⟩).2 (mem_inf.1 hy).2, rfl⟩
  rw [← e, card_map_of_injective A.subtype_injective]
  exact U4.card_actionFixed_upperUnipotent_le hcard ρ hD

theorem natural_module_of_card_le [Finite G] {n : ℕ} (hk : Nat.card k = 2 ^ n) (hn : 2 ≤ n)
    {X A P : Subgroup G} (ψ : X ≃* SL(2, k)) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hXA : X ≤ normalizer (A : Set G)) (hcard : Nat.card A = (2 ^ n) ^ 2)
    (hnc : ¬ X ≤ centralizer (A : Set G)) (hPX : P ≤ X) (hP : Nat.card P = Nat.card k)
    (hfixP : 2 ^ n ≤ Nat.card (A ⊓ centralizer (P : Set G) : Subgroup G)) :
    A ⊓ centralizer (X : Set G) = ⊥ ∧
      Nat.card (A ⊓ centralizer (P : Set G) : Subgroup G) = 2 ^ n ∧
      (∀ a ∈ A, ∀ b ∈ A, a ≠ 1 → b ≠ 1 → ∃ x ∈ X, x * a * x⁻¹ = b) ∧
      (∀ a ∈ A ⊓ centralizer (P : Set G), a ≠ 1 → X ⊓ centralizer ({a} : Set G) = P) ∧
      X ⊓ centralizer (A : Set G) = ⊥ := by
  have hfix := inf_centralizer_eq_bot_of_not_le hk hn ψ hcomm hXA hcard hnc
  have hfixS := le_antisymm
    (card_inf_centralizer_le_of_inf_centralizer_eq_bot hk ψ hcomm hXA hcard hfix hPX hP) hfixP
  exact ⟨hfix, hfixS, natural_module_of_card hk ψ hcomm hXA hcard hfix hPX hP hfixS⟩

end CFSG.LocalAnalysis.EvenBN.Common
