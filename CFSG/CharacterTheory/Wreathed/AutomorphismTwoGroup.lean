module

public import CFSG.CharacterTheory.Wreathed.AutomorphismCoordinates
public import CFSG.Open.Catalog

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

theorem card_center_automorphisms (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (MulAut (Subgroup.center (Wreath (2 ^ n)))) = 2 ^ (n - 1) := by
  have hm : 1 < 2 ^ n := by
    have h := Nat.pow_le_pow_right (n := 2) (by decide) hn
    norm_num at h
    omega
  let : IsCyclic (Subgroup.center (Wreath (2 ^ n))) := center_isCyclic _ hm
  rw [IsCyclic.card_mulAut, card_center _ hm,
    Nat.totient_prime_pow Nat.prime_two (by omega)]
  simp

theorem card_derived_automorphisms (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (MulAut (commutator (Wreath (2 ^ n)))) = 2 ^ (n - 1) := by
  let : IsCyclic (commutator (Wreath (2 ^ n))) := derived_isCyclic _
  rw [IsCyclic.card_mulAut, card_derived,
    Nat.totient_prime_pow Nat.prime_two (by omega)]
  simp

theorem centerDerivedAction_target_isPGroup (n : ℕ) (hn : 1 ≤ n) :
    IsPGroup 2 (MulAut (Subgroup.center (Wreath (2 ^ n))) ×
      MulAut (commutator (Wreath (2 ^ n)))) := by
  apply IsPGroup.of_card (n := (n - 1) + (n - 1))
  rw [Nat.card_prod, card_center_automorphisms n hn, card_derived_automorphisms n hn,
    pow_add]

theorem centerDerivedAction_kernel_isPGroup (n : ℕ) (hn : 2 ≤ n) :
    IsPGroup 2 (centerDerivedAction (2 ^ n)).ker := by
  have hm : 2 < 2 ^ n := by
    have h := Nat.pow_le_pow_right (n := 2) (by decide) hn
    norm_num at h
    omega
  have hp : IsPGroup 2
      (Subgroup.center (Wreath (2 ^ n)) × commutator (Wreath (2 ^ n))) := by
    apply IsPGroup.of_card (n := n + n)
    rw [Nat.card_prod, card_center _ (by omega), card_derived, pow_add]
  exact hp.of_injective (centerDerivedKernelDisplacement (2 ^ n) hm)
    (centerDerivedKernelDisplacement_injective (2 ^ n) hm)

theorem wreath_automorphism_isPGroup (n : ℕ) (hn : 2 ≤ n) :
    IsPGroup 2 (MulAut (Wreath (2 ^ n))) := by
  have htarget := centerDerivedAction_target_isPGroup n (by omega)
  have htop : IsPGroup 2 (⊤ : Subgroup
      (MulAut (Subgroup.center (Wreath (2 ^ n))) ×
        MulAut (commutator (Wreath (2 ^ n))))) :=
    htarget.of_injective (⊤ : Subgroup _).subtype Subtype.val_injective
  have h := htop.comap_of_ker_isPGroup (centerDerivedAction (2 ^ n))
    (centerDerivedAction_kernel_isPGroup n hn)
  rw [Subgroup.comap_top] at h
  exact h.of_equiv Subgroup.topEquiv

theorem wreathedTwoGroup_automorphism_isPGroup (n : ℕ) (hn : 2 ≤ n) :
    IsPGroup 2 (MulAut (CFSG.Open.WreathedTwoGroup n)) :=
  wreath_automorphism_isPGroup n hn

end CFSG.Wreathed
