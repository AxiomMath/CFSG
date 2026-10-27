module

public import CFSG.LargeExtraspecial.AS35KFisB
public import CFSG.LargeExtraspecial.S12InspFamESpOut
public import CFSG.RankThree.SubgroupLists.SymplecticFischerSp
public import CFSG.RankThree.SubgroupLists.SymplecticFischerRefl

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Matrix CFSG.Open CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

namespace AS35K

theorem forall_inner_of_card_outer_eq_one {X : Type*} [Group X] (h : Nat.card (Outer X) = 1) :
    ∀ α : MulAut X, ∃ g : X, α = MulAut.conj g := by
  intro α
  have htop : inner X = ⊤ := Subgroup.index_eq_one.mp h
  obtain ⟨g, hg⟩ := (htop ▸ mem_top α : α ∈ inner X)
  exact ⟨g, hg.symm⟩

theorem isPerfect_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    (hna : ∃ a b : X, a * b ≠ b * a) : Group.IsPerfect X :=
  ⟨commutator_eq_top_of_simple hna⟩

end AS35K

namespace Setting

variable {H : Type} [Group H] [Finite H] (T : Setting H)

omit [Finite H] in
theorem false_of_case2_zGen (hs : IsSimpleGroup T.zGen) (hC : centralizer (T.zGen : Set H) = ⊥)
    {m : ℕ} (hm : 2 ≤ m) {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (h : fischerLinearModel {g : T.zGen | IsConj T.zL g}
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) : False := by
  obtain ⟨φ, hφ⟩ := h
  have hna := T.exists_mul_ne_mul_zGen hC
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  · obtain rfl : m = 2 := by omega
    have : Group.IsPerfect T.zGen := AS35K.isPerfect_of_simple hna
    exact CFSG.RankThree.SubgroupLists.SpFischer.not_isPerfect_sp4 halt hnd
      (Group.IsPerfect.ofSurjective (f := φ.toMonoidHom) φ.surjective)
  · have hout : Nat.card (Outer T.zGen) = 1 := by
      rw [Nat.card_congr (equivalence φ).toEquiv]
      exact S12InspSp.card_outer_SpG hm3 halt hnd
    have htop := T.zGen_eq_top_of_forall_inner hC (AS35K.forall_inner_of_card_outer_eq_one hout)
    set eH : H ≃* T.zGen := ((MulEquiv.subgroupCongr htop).trans topEquiv).symm with heH
    have hcoe : ∀ g : H, ((eH g : T.zGen) : H) = g := fun g => rfl
    refine T.false_of_case2 halt hnd ⟨eH.trans φ, fun g => ?_⟩
    rw [MulEquiv.trans_apply, ← hφ]
    constructor
    · intro hg
      obtain ⟨c, rfl⟩ := isConj_iff.mp hg
      refine isConj_iff.mpr ⟨eH c, Subtype.ext ?_⟩
      rw [coe_mul, coe_mul, coe_inv, hcoe, hcoe, coe_zL]
    · intro hg
      obtain ⟨c, hc⟩ := isConj_iff.mp hg
      refine isConj_iff.mpr ⟨c, ?_⟩
      have h1 := congrArg Subtype.val hc
      rwa [coe_mul, coe_mul, coe_inv, coe_zL, hcoe] at h1

omit [Finite H] in
theorem unitaryModel_of_case5_five (hs : IsSimpleGroup T.zGen)
    (hC : centralizer (T.zGen : Set H) = ⊥) {f : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)}
    (hsymm : ∀ x y, f x y = f y x) (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    (hmodel : fischerCentralQuotientModel {g : T.zGen | IsConj T.zL g}
      (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
      (fischerTransvections (fun x y => f x y) fun v => f v v = 1)) :
    ∃ ψ : T.zGen ≃* PG 4, ∀ l : T.zGen, IsConj T.zL l ↔ ψ l ∈ DG 4 := by
  have hf : IsF3Form f := ⟨hsymm, hnd⟩
  obtain ⟨ψ, hψ⟩ := (fischerCentralQuotientModel_iff _).1 hmodel
  have hna := T.exists_mul_ne_mul_zGen hC
  have : Group.IsPerfect T.zGen := AS35K.isPerfect_of_simple hna
  have hperf : Group.IsPerfect (R3 f) :=
    Group.IsPerfect.ofSurjective (f := ψ.toMonoidHom) ψ.surjective
  have h45 : 45 ≤ Nat.card (D3 f) :=
    CFSG.RankThree.SubgroupLists.fischerReflectionCard 5 le_rfl f hsymm hnd hperf
  rcases R3_five_cases hf with ⟨-, χ, hχ⟩ | ⟨h36, -⟩
  · obtain ⟨Ξ, -, hΞ⟩ := CFSG.Fischer.Classification.LocalU4.exists_mulEquiv_PG_four_R3_I5
    refine ⟨(ψ.trans χ).trans Ξ.symm, fun l => (hψ l).trans ?_⟩
    constructor
    · intro hl
      have h1 : χ (ψ l) ∈ D3 I5Form := hχ ▸ ⟨ψ l, hl, rfl⟩
      rw [← hΞ] at h1
      obtain ⟨d, hd, hdx⟩ := h1
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, ← hdx, MulEquiv.symm_apply_apply]
      exact hd
    · intro hl
      have h1 : Ξ (((ψ.trans χ).trans Ξ.symm) l) ∈ D3 I5Form := hΞ ▸ ⟨_, hl, rfl⟩
      rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulEquiv.trans_apply, ← hχ] at h1
      obtain ⟨x, hx, hxe⟩ := h1
      rwa [← χ.injective hxe]
  · rw [Nat.card_coe_set_eq, h36] at h45
    omega

end Setting

namespace S14

@[expose] def AschTwoReflSixStmt : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (T : Setting H), 2 ≤ T.width → IsSimpleGroup T.zGen →
    centralizer (T.zGen : Set H) = ⊥ →
    (∀ l₁ ∈ T.zGen, ∀ l₂ ∈ T.zGen,
      orderOf (l₁ * T.z * l₁⁻¹ * (l₂ * T.z * l₂⁻¹)) ∈ ({1, 2, 3} : Set ℕ)) →
    ∀ m : ℕ, 6 ≤ m → ∀ f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3),
      (∀ x y, f x y = f y x) → (∀ x, (∀ y, f x y = 0) → x = 0) →
      fischerCentralQuotientModel {g : T.zGen | IsConj T.zL g}
        (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
        (fischerTransvections (fun x y => f x y) fun v => f v v = 1) → False

theorem aschTwoSpReflStmt_of_reflSix (h : AschTwoReflSixStmt) : AschTwoSpReflStmt := by
  intro H _ _ T hw hs hC h3 hcase
  rcases hcase with ⟨m, hm, b, halt, hnd, hmodel⟩ | ⟨m, hm, f, hsymm, hnd, hmodel⟩
  · exact (T.false_of_case2_zGen hs hC hm halt hnd hmodel).elim
  · rcases Nat.lt_or_ge m 6 with hm6 | hm6
    · obtain rfl : m = 5 := by omega
      obtain ⟨ψ, hψ⟩ := T.unitaryModel_of_case5_five hs hC hsymm hnd hmodel
      exact ⟨4, le_rfl, ψ, hψ⟩
    · exact (h H T hw hs hC h3 m hm6 f hsymm hnd hmodel).elim

end S14

end CFSG.LargeExtraspecial
