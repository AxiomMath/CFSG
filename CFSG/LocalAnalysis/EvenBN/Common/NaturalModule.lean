module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBJEvenLinearTwoModule
public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusThree

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Subgroup
open CFSG.LocalAnalysis.ComponentInitial.EvenLinearTwoModule (actionFixed mem_actionFixed
  even_linear_two_half_fixed_module_transitivity)
open scoped MatrixGroups

variable {G : Type*} [Group G] {k : Type*} [Field k] [Finite k] [CharP k 2]

theorem exists_conj_eq_upperUnipotent {n : ℕ} (hk : Nat.card k = 2 ^ n)
    {H : Subgroup SL(2, k)} (hH : Nat.card H = Nat.card k) :
    ∃ g : SL(2, k), H.map (MulAut.conj g).toMonoidHom = CFSG.Timmesfeld.upperUnipotent k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH2 : IsPGroup 2 H := IsPGroup.of_card (by rw [hH, hk])
  have hU2 : IsPGroup 2 (CFSG.Timmesfeld.upperUnipotent k) :=
    IsPGroup.of_card (by rw [CFSG.Timmesfeld.RankOne.card_upperUnipotent k, hk])
  obtain ⟨P₁, hP₁⟩ := hH2.exists_le_sylow
  obtain ⟨P₂, hP₂⟩ := hU2.exists_le_sylow
  have hc₁ := card_sylow_two_eq (MulEquiv.refl SL(2, k)) P₁
  have hc₂ := card_sylow_two_eq (MulEquiv.refl SL(2, k)) P₂
  have e₁ : H = P₁ := Subgroup.eq_of_le_of_card_ge hP₁ (by rw [hc₁, hH])
  have e₂ : CFSG.Timmesfeld.upperUnipotent k = P₂ :=
    Subgroup.eq_of_le_of_card_ge hP₂ (by rw [hc₂, CFSG.Timmesfeld.RankOne.card_upperUnipotent k])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, k) P₁ P₂
  refine ⟨g, ?_⟩
  rw [e₁, e₂, ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  rfl

theorem natural_module_of_card {n : ℕ} (hk : Nat.card k = 2 ^ n) {X A S : Subgroup G}
    (ψ : X ≃* SL(2, k)) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hXA : X ≤ normalizer (A : Set G)) (hcard : Nat.card A = (2 ^ n) ^ 2)
    (hfix : A ⊓ centralizer (X : Set G) = ⊥) (hSX : S ≤ X) (hS : Nat.card S = Nat.card k)
    (hfixS : Nat.card (A ⊓ centralizer (S : Set G) : Subgroup G) = 2 ^ n) :
    (∀ a ∈ A, ∀ b ∈ A, a ≠ 1 → b ≠ 1 → ∃ x ∈ X, x * a * x⁻¹ = b) ∧
      (∀ a ∈ A ⊓ centralizer (S : Set G), a ≠ 1 → X ⊓ centralizer ({a} : Set G) = S) ∧
      X ⊓ centralizer (A : Set G) = ⊥ := by
  set S' : Subgroup X := S.subgroupOf X with hS'
  have hS'card : Nat.card (S'.map ψ.toMonoidHom) = Nat.card k := by
    rw [card_map_of_injective ψ.injective, hS', Nat.card_congr (subgroupOfEquivOfLe hSX).toEquiv,
      hS]
  obtain ⟨g, hg⟩ := exists_conj_eq_upperUnipotent hk hS'card
  set ψ' : X ≃* SL(2, k) := ψ.trans (MulAut.conj g) with hψ'
  have hψ'S : ∀ x : X, ψ' x ∈ CFSG.Timmesfeld.upperUnipotent k ↔ (x : G) ∈ S := by
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
  have hρ : ∀ (s : SL(2, k)) (a : A), ((ρ s a : A) : G) =
      ((ψ'.symm s : X) : G) * a * ((ψ'.symm s : X) : G)⁻¹ := fun s a => rfl
  have hρ' : ∀ (x : X) (a : A), ((ρ (ψ' x) a : A) : G) = (x : G) * a * (x : G)⁻¹ := by
    intro x a
    rw [hρ, MulEquiv.symm_apply_apply]
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
      (a : G) ∈ centralizer (S : Set G) := by
    intro a
    rw [mem_actionFixed, mem_centralizer_iff]
    constructor
    · intro ha x hx
      have e := congrArg Subtype.val (ha (ψ' ⟨x, hSX hx⟩) ((hψ'S _).2 hx))
      rw [hρ'] at e
      calc x * (a : G) = (x * a * x⁻¹) * x := by group
        _ = (a : G) * x := by rw [e]
    · intro ha s hs
      obtain ⟨x, rfl⟩ := ψ'.surjective s
      apply Subtype.ext
      rw [hρ']
      have hc := ha x ((hψ'S x).1 hs)
      rw [hc, mul_inv_cancel_right]
  have hB : Nat.card (actionFixed ρ (CFSG.Timmesfeld.upperUnipotent k)) = 2 ^ n := by
    rw [← hfixS]
    have e : (actionFixed ρ (CFSG.Timmesfeld.upperUnipotent k)).map A.subtype =
        A ⊓ centralizer (S : Set G) := by
      ext y
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact mem_inf.2 ⟨a.2, (hfixmem a).1 ha⟩
      · intro hy
        exact ⟨⟨y, (mem_inf.1 hy).1⟩, (hfixmem ⟨y, (mem_inf.1 hy).1⟩).2 (mem_inf.1 hy).2, rfl⟩
    rw [← e, card_map_of_injective A.subtype_injective]
  obtain ⟨hinj, -, -, -, htrans, hstab, -⟩ :=
    even_linear_two_half_fixed_module_transitivity hk hcard ρ hD hB
  refine ⟨fun a ha b hb ha1 hb1 => ?_, fun a ha ha1 => ?_, ?_⟩
  · obtain ⟨d, hd⟩ := htrans ⟨a, ha⟩ ⟨b, hb⟩ (fun e => ha1 (congrArg Subtype.val e))
      (fun e => hb1 (congrArg Subtype.val e))
    refine ⟨(ψ'.symm d : X), (ψ'.symm d).2, ?_⟩
    have e := congrArg Subtype.val hd
    rw [hρ] at e
    exact e
  · obtain ⟨haA, haS⟩ := mem_inf.1 ha
    have hafix : (⟨a, haA⟩ : A) ∈ actionFixed ρ (CFSG.Timmesfeld.upperUnipotent k) :=
      (hfixmem ⟨a, haA⟩).2 haS
    have key := hstab ⟨a, haA⟩ hafix (fun e => ha1 (congrArg Subtype.val e))
    ext x
    constructor
    · intro hx
      obtain ⟨hxX, hxC⟩ := mem_inf.1 hx
      have hxa : x * a = a * x := mem_centralizer_singleton_iff.1 hxC
      have : ρ (ψ' ⟨x, hxX⟩) ⟨a, haA⟩ = ⟨a, haA⟩ := by
        apply Subtype.ext
        rw [hρ']
        rw [hxa, mul_inv_cancel_right]
      exact (hψ'S ⟨x, hxX⟩).1 ((key _).1 this)
    · intro hx
      refine mem_inf.2 ⟨hSX hx, mem_centralizer_singleton_iff.2 ?_⟩
      have h1 : ψ' ⟨x, hSX hx⟩ ∈ CFSG.Timmesfeld.upperUnipotent k := (hψ'S _).2 hx
      have e := congrArg Subtype.val ((key _).2 h1)
      rw [hρ'] at e
      calc x * a = (x * a * x⁻¹) * x := by group
        _ = a * x := by rw [e]
  · refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxX, hxC⟩ := mem_inf.1 hx
    have h1 : ρ (ψ' ⟨x, hxX⟩) = 1 := by
      ext a
      rw [hρ']
      have hc := mem_centralizer_iff.1 hxC a a.2
      rw [← hc, mul_inv_cancel_right]
      rfl
    have h2 : ψ' ⟨x, hxX⟩ = 1 := hinj (by rw [h1, map_one])
    have h3 : (⟨x, hxX⟩ : X) = 1 := by
      rw [← map_one ψ'] at h2
      exact ψ'.injective h2
    rw [mem_bot]
    exact congrArg Subtype.val h3

end CFSG.LocalAnalysis.EvenBN.Common
