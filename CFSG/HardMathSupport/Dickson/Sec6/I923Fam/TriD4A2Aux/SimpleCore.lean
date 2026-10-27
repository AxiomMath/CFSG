module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4A2Aux.Final

public section

open scoped commutatorElement

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Dickson.Sec6.I923

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2

@[expose] def SimpleCore (G : Type*) [Group G] (x C : ℕ) : Prop :=
  ∃ S : Subgroup G, ∃ _ : S.Normal, Group.IsSolvable (G ⧸ S) ∧ IsSimpleGroup ↥S ∧
    (∃ a b : ↥S, a * b ≠ b * a) ∧ x ∣ Nat.card ↥S ∧ Nat.card ↥S ≤ x * C

theorem SimpleCore.of_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') {x C : ℕ}
    (h : SimpleCore G x C) : SimpleCore G' x C := by
  obtain ⟨S, hSn, hsol, hs, ⟨a, b, hab⟩, hx, hC⟩ := h
  have hmap : S.map e.toMonoidHom = S.map e.toMonoidHom := rfl
  haveI : (S.map e.toMonoidHom).Normal := hSn.map e.toMonoidHom e.surjective
  let q : G ⧸ S ≃* G' ⧸ S.map e.toMonoidHom := QuotientGroup.congr S (S.map e.toMonoidHom) e rfl
  let eS : ↥S ≃* ↥(S.map e.toMonoidHom) := Subgroup.equivMapOfInjective S e.toMonoidHom e.injective
  refine ⟨S.map e.toMonoidHom, inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · haveI := hsol
    exact Group.isSolvable_of_surjective (f := q.toMonoidHom) q.surjective
  · haveI := hs
    exact eS.symm.isSimpleGroup
  · refine ⟨eS a, eS b, fun h' => hab (eS.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h'
  · rw [← Nat.card_congr eS.toEquiv]
    exact hx
  · rw [← Nat.card_congr eS.toEquiv]
    exact hC

theorem noL2Layer_of_simpleCore {P : Type} [Group P] [Finite P] (ψ : MulAut P) {G : Type}
    [Group G] (e : ↥(fixSubgroup ψ) ≃* G) {x C : ℕ} (h : SimpleCore G x C)
    (hx : x = 1 ∨ IsPrimePow x) (hkey : 2 * C < (x - 1) * (x - 2)) : NoL2Layer ψ := by
  obtain ⟨S, hSn, hsol, hs, hnab, hxS, hSC⟩ := h
  exact noL2Layer_of_simple_normal ψ e S hsol hs hnab hx hxS hSC hkey

theorem exists_noncomm_of_perfect_sub {G : Type*} [Group G] (S : Subgroup G) (hS : S ≠ ⊥)
    (hperf : ⁅S, S⁆ = S) : ∃ a b : ↥S, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  apply hS
  rw [← hperf, eq_bot_iff]
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  have := hcon ⟨a, ha⟩ ⟨b, hb⟩
  have h1 : a * b = b * a := congrArg Subtype.val this
  rw [Subgroup.mem_bot]
  exact commutatorElement_eq_one_iff_mul_comm.2 h1

end CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2
