module

public import CFSG.Fischer.Classification.PartIII.Symp.Sym

public section

namespace CFSG.Fischer.Classification.LocalSymp

open CFSG.Blueprint.Fischer CFSG.Fischer

variable {n : ℕ}

theorem ncard_isSwap : {σ : Equiv.Perm (Fin n) | σ.IsSwap}.ncard = n.choose 2 := by
  refine le_antisymm ncard_isSwap_le ?_
  have hsub : ((Finset.univ.powersetCard 2 : Finset (Finset (Fin n))) : Set (Finset (Fin n))) ⊆
      (fun σ => σ.support) '' {σ : Equiv.Perm (Fin n) | σ.IsSwap} := by
    intro A hA
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hA
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hA.2
    exact ⟨Equiv.swap a b, ⟨a, b, hab, rfl⟩, Equiv.Perm.support_swap hab⟩
  calc n.choose 2 = ((Finset.univ.powersetCard 2 : Finset (Finset (Fin n))) :
        Set (Finset (Fin n))).ncard := by
        rw [Set.ncard_coe_finset, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    _ ≤ _ := Set.ncard_le_ncard hsub
    _ ≤ _ := Set.ncard_image_le

theorem swap_mul_swap_ne_of_ne {a b d : Fin n} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Equiv.swap a b * Equiv.swap a d ≠ Equiv.swap a d * Equiv.swap a b := by
  intro h
  have := congrArg (fun σ : Equiv.Perm (Fin n) => σ a) h
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at this
  rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hbd),
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hab) hbd] at this
  exact hbd this.symm

theorem ne_of_commute_swap {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (hne : Equiv.swap c d ≠ Equiv.swap a b)
    (hcomm : Equiv.swap c d * Equiv.swap a b = Equiv.swap a b * Equiv.swap c d) :
    c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b := by
  have key : ∀ x y z : Fin n, x ≠ y → x ≠ z →
      Equiv.swap x y * Equiv.swap x z = Equiv.swap x z * Equiv.swap x y → y = z := by
    intro x y z hxy hxz h
    by_contra hyz
    exact swap_mul_swap_ne_of_ne hxz hxy (Ne.symm hyz) h.symm
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> subst h
  · exact hne (by rw [key c d b hcd hab hcomm])
  · rw [Equiv.swap_comm a c] at hne hcomm
    exact hne (by rw [key c d a hcd (Ne.symm hab) hcomm])
  · rw [Equiv.swap_comm c d] at hne hcomm
    exact hne (by rw [key d c b (Ne.symm hcd) hab hcomm])
  · rw [Equiv.swap_comm c d, Equiv.swap_comm a d] at hne hcomm
    exact hne (by rw [key d c a (Ne.symm hcd) (Ne.symm hab) hcomm])

theorem ncard_localClass_isSwap {a b : Fin n} (hab : a ≠ b) :
    (LocalClass {σ : Equiv.Perm (Fin n) | σ.IsSwap} (Equiv.swap a b)).ncard =
      (n - 2).choose 2 := by
  have himg : (fun σ => σ.support) ''
      LocalClass {σ : Equiv.Perm (Fin n) | σ.IsSwap} (Equiv.swap a b) =
      (((Finset.univ \ {a, b}).powersetCard 2 : Finset (Finset (Fin n))) :
        Set (Finset (Fin n))) := by
    ext A
    simp only [Set.mem_image, Finset.mem_coe, Finset.mem_powersetCard]
    constructor
    · rintro ⟨σ, ⟨⟨c, d, hcd, rfl⟩, hne, hcomm⟩, rfl⟩
      obtain ⟨hca, hcb, hda, hdb⟩ := ne_of_commute_swap hab hcd hne hcomm
      rw [Equiv.Perm.support_swap hcd]
      refine ⟨fun x hx => ?_, Finset.card_pair hcd⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
        true_and]
      rcases hx with rfl | rfl <;> tauto
    · rintro ⟨hA, hA2⟩
      obtain ⟨c, d, hcd, rfl⟩ := Finset.card_eq_two.1 hA2
      have hc := (Finset.mem_sdiff.1 (hA (Finset.mem_insert_self c {d}))).2
      have hd := (Finset.mem_sdiff.1 (hA (show d ∈ ({c, d} : Finset (Fin n)) by simp))).2
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc hd
      exact ⟨Equiv.swap c d, ⟨⟨c, d, hcd, rfl⟩, swap_ne_swap hcd hc.1 hc.2,
        swap_mul_swap_comm hc.1 hc.2 hd.1 hd.2⟩, Equiv.Perm.support_swap hcd⟩
  have hinj : Set.InjOn (fun σ : Equiv.Perm (Fin n) => σ.support)
      (LocalClass {σ : Equiv.Perm (Fin n) | σ.IsSwap} (Equiv.swap a b)) :=
    fun σ hσ τ hτ h => eq_of_isSwap_of_support_eq hσ.1 hτ.1 h
  rw [← hinj.ncard_image, himg, Set.ncard_coe_finset, Finset.card_powersetCard,
    Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
    Finset.card_pair hab]

end CFSG.Fischer.Classification.LocalSymp
