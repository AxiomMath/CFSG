module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.K54Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.TwoFi22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t z : G}

section Certified


theorem Level55.commutator_centPair (d : Level55 G t z) :
    ⁅centPair z t, centPair z t⁆ = centPair z t := by
  refine d.eq_K_of_not_le_O2K (Subgroup.commutator_le_self _) ?_ ?_
  · intro k hk n hn
    have hnK : n ∈ centPair z t := Subgroup.commutator_le_self _ hn
    have h1 : ⁅k, n⁆ ∈ ⁅centPair z t, centPair z t⁆ := Subgroup.commutator_mem_commutator hk hnK
    have h2 : k * n * k⁻¹ = ⁅k, n⁆ * n := by
      simp only [commutatorElement_def]
      group
    rw [h2]
    exact mul_mem h1 hn
  · intro hle
    obtain ⟨e⟩ := d.quot
    have hSs : IsSimpleGroup (↥(centPair z t) ⧸ CFSG.pCore 2 ↥(centPair z t)) :=
      @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Co2.isSimpleGroup_Co2 e
    have hcomm : ∀ a b : ↥(centPair z t) ⧸ CFSG.pCore 2 ↥(centPair z t), a * b = b * a := by
      intro a b
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      rw [mem_pCore_iff_mem_O2In]
      have h1 := hle (Subgroup.commutator_mem_commutator (inv_mem y.2) (inv_mem x.2))
      convert h1 using 1
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    let _ : CommGroup (↥(centPair z t) ⧸ CFSG.pCore 2 ↥(centPair z t)) :=
      { (inferInstance : Group (↥(centPair z t) ⧸ CFSG.pCore 2 ↥(centPair z t))) with
        mul_comm := hcomm }
    have hprime := IsSimpleGroup.prime_card
      (α := ↥(centPair z t) ⧸ CFSG.pCore 2 ↥(centPair z t))
    have hco : Nat.card (Carrier .Co2) = 42305421312000 := CFSG.Sporadic.Co2.card_Co2
    rw [Nat.card_congr e.toEquiv, hco] at hprime
    norm_num at hprime

end Certified

end CFSG.EvenSporadicStandard.TwoB
