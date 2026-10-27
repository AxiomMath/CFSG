module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.S6Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9.RB

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem finrank_map_mkQ_add {V U : Submodule (ZMod 2) S.Qt} (hVU : V ≤ U) :
    finrank (ZMod 2) ↥(U.map V.mkQ) + finrank (ZMod 2) V = finrank (ZMod 2) U := by
  have h := LinearMap.finrank_range_add_finrank_ker (V.mkQ.domRestrict U)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ,
    (Submodule.comapSubtypeEquivOfLe hVU).finrank_eq] at h
  exact h

theorem index_le_of_gen {X : Subgroup S.O} {V U : Submodule (ZMod 2) S.Qt} (hVU : V ≤ U)
    (hXV : ∀ x ∈ X, ∀ v ∈ V, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ V)
    (hXU : ∀ x ∈ X, ∀ v ∈ U, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ U) {u u' : S.Qt}
    (hu : u ∈ U) (hu' : u' ∈ U)
    (hgen : ∀ k ∈ X, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ V →
      (k : S.Qt ≃ₗ[ZMod 2] S.Qt) u' - u' ∈ V →
        ∀ v ∈ U, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ V)
    {K : Subgroup X} (hK : ∀ k : X, k ∈ K ↔ ∀ v ∈ U, ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ V) :
    K.index ≤ (2 ^ (finrank (ZMod 2) U - finrank (ZMod 2) V)) ^ 2 := by
  classical
  have hd := finrank_map_mkQ_add hVU
  set Z := U.map V.mkQ with hZ
  have hZfin : Finite Z := Module.finite_of_finite (ZMod 2)
  have hmem : ∀ (r : X) {v : S.Qt}, v ∈ U → V.mkQ (((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) ∈ Z :=
    fun r v hv => Submodule.mem_map_of_mem (hXU r r.2 v hv)
  let Ψ : X → Z × Z := fun r => (⟨_, hmem r hu⟩, ⟨_, hmem r hu'⟩)
  have hab : ∀ (a b : X) (v : S.Qt), (((a⁻¹ * b : X) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v =
      (((a : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (((b : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - ((a : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
    intro a b v
    rw [map_sub, inv_apply_apply_O]
    rfl
  have key : ∀ a b : X, Ψ a = Ψ b ↔ a⁻¹ * b ∈ K := by
    intro a b
    simp only [Ψ, Prod.mk.injEq, Subtype.mk.injEq, Submodule.mkQ_apply, Submodule.Quotient.eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine (hK _).mpr (hgen _ (a⁻¹ * b).2 ?_ ?_)
      · rw [hab]
        have := hXV _ (inv_mem a.2) _ (neg_mem h1)
        rwa [neg_sub] at this
      · rw [hab]
        have := hXV _ (inv_mem a.2) _ (neg_mem h2)
        rwa [neg_sub] at this
    · intro h
      have h' := (hK _).mp h
      have e : ∀ v, ((a : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - ((b : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
          -(((a : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
            ((((a⁻¹ * b : X) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v)) := by
        intro v
        rw [hab, apply_inv_apply_O, neg_sub]
      refine ⟨?_, ?_⟩
      · rw [e]; exact neg_mem (hXV _ a.2 _ (h' u hu))
      · rw [e]; exact neg_mem (hXV _ a.2 _ (h' u' hu'))
  have hle : K.index ≤ Nat.card (Z × Z) := by
    rw [Subgroup.index]
    refine Nat.card_le_card_of_injective (fun q => Quotient.liftOn' q Ψ
      fun a b h => (key a b).mpr (QuotientGroup.leftRel_apply.mp h)) ?_
    intro q₁ q₂ h
    induction q₁ using QuotientGroup.induction_on with | H a => ?_
    induction q₂ using QuotientGroup.induction_on with | H b => ?_
    exact QuotientGroup.eq.mpr ((key a b).mp h)
  have hcard : Nat.card Z = 2 ^ (finrank (ZMod 2) U - finrank (ZMod 2) V) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    congr 1
    omega
  rw [Nat.card_prod, hcard, ← pow_two] at hle
  exact hle

theorem apply_sub_mem_of_transfer {V W : Submodule (ZMod 2) S.Qt} {x y k : S.O}
    (hkW : ∀ w ∈ W, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W)
    (hxe : ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
      (k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w) ∈ V)
    (hye : ∀ w ∈ W, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
      (k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w) ∈ V)
    (hinf : V ⊓ commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥)
    (hfix : ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w → (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w)
    {w : S.Qt} (hw : w ∈ W)
    (h : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) -
      ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) ∈ V) :
    (k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) -
      ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) ∈ V := by
  have hkw : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ W := sub_mem (hkW w hw) hw
  have e1 : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) -
      ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) =
      ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
        (k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) +
      ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) -
        ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w)) := by
    rw [map_sub, map_sub]; abel
  have h1 : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) -
      ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) ∈ V ⊓ commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    ⟨by rw [e1]; exact add_mem (hxe w hw) h, sub_mem_commSpace _ _⟩
  rw [hinf, Submodule.mem_bot, sub_eq_zero] at h1
  have h2 := hfix _ hkw h1
  have e2 : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) -
      ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) =
      ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) -
        ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w)) -
      ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
        (k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) := by
    rw [map_sub, map_sub]; abel
  rw [e2, h2, sub_self, zero_sub]
  exact neg_mem (hye w hw)

end CFSG.LargeExtraspecial.S9.RB
