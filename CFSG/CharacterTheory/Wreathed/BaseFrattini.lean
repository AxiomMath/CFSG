module

public import CFSG.CharacterTheory.Wreathed.CentricVCopies
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.HomocyclicFrattini
public import CFSG.LocalAnalysis.LargeEvenClassification.FrattiniKernel

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

@[expose] def baseFunctionEquiv (m : ℕ) :
    baseSubgroup m ≃* (Multiplicative (ZMod 2) → Multiplicative (ZMod m)) where
  toFun g := g.val.left
  invFun f := ⟨⟨f, 1⟩, rfl⟩
  left_inv g := by
    apply Subtype.ext
    apply RegularWreathProduct.ext
    · rfl
    · exact g.property.symm
  right_inv f := rfl
  map_mul' g h := by
    funext q
    change g.val.left q * h.val.left (g.val.right⁻¹ * q) =
      g.val.left q * h.val.left q
    have hg : g.val.right = 1 := g.property
    have hq : g.val.right⁻¹ * q = q := by
      rw [hg]
      exact one_mul q
    rw [hq]

@[expose] def baseHomocyclicEquiv (m : ℕ) :
    baseSubgroup m ≃* CFSG.StandardHomocyclicCover (Multiplicative (ZMod 2)) m :=
  (baseFunctionEquiv m).trans
    (MulEquiv.funMultiplicative (Multiplicative (ZMod 2)) (ZMod m)).symm

theorem frattini_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (frattini A).map e.toMonoidHom = frattini B := by
  apply le_antisymm
  · exact (Subgroup.map_le_iff_le_comap).mpr
      (frattini_le_comap_frattini_of_surjective e.surjective)
  · intro b hb
    refine Subgroup.mem_map.mpr ⟨e.symm b, ?_, e.apply_symm_apply b⟩
    exact frattini_le_comap_frattini_of_surjective
      (φ := e.symm.toMonoidHom) e.symm.surjective hb

@[expose] def baseFrattiniQuotientEquiv (n : ℕ) (hn : 1 ≤ n) :
    baseSubgroup (2 ^ n) ⧸ frattini (baseSubgroup (2 ^ n)) ≃*
      CFSG.StandardHomocyclicCover (Multiplicative (ZMod 2)) 2 :=
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  (QuotientGroup.congr _ _ (baseHomocyclicEquiv (2 ^ n))
    (frattini_map_mulEquiv (baseHomocyclicEquiv (2 ^ n)))).trans
      (CFSG.standardHomocyclicCoverFrattiniQuotientEquiv
        (Multiplicative (ZMod 2)) 2 n hn)

theorem base_frattini_quotient_card (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (baseSubgroup (2 ^ n) ⧸ frattini (baseSubgroup (2 ^ n))) = 4 := by
  rw [Nat.card_congr (baseFrattiniQuotientEquiv n hn).toEquiv]
  change Nat.card (Multiplicative (Multiplicative (ZMod 2) → ZMod 2)) = 4
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun]
  simp

theorem base_frattini_automorphism_kernel_isPGroup (n : ℕ) :
    IsPGroup 2
      (CFSG.LargeEvenClassification.Helpers.frattiniAutAction
        (baseSubgroup (2 ^ n))).ker := by
  exact CFSG.LargeEvenClassification.Helpers.frattiniAutAction_isPGroup_ker _
    Nat.prime_two ((wreath_isPGroup n).to_subgroup (baseSubgroup (2 ^ n)))

end CFSG.Wreathed
