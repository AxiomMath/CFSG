module

public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses

public section

namespace CFSG.Certificates.Kernel.M23Three

open CFSG.Sporadic.Schreier

variable {n : ℕ}

@[expose] def setStab (G : Subgroup (Equiv.Perm (Fin n))) (F : Finset (Fin n)) :
    Subgroup (Equiv.Perm (Fin n)) where
  carrier := {g | g ∈ G ∧ ∀ x, g x ∈ F ↔ x ∈ F}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨G.mul_mem ha hb, fun x => by rw [Equiv.Perm.mul_apply, ha', hb']⟩
  one_mem' := ⟨G.one_mem, fun _ => Iff.rfl⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨G.inv_mem ha, fun x => ?_⟩
    simpa using (ha' (a⁻¹ x)).symm

@[expose] def restr (G : Subgroup (Equiv.Perm (Fin n))) (F : Finset (Fin n)) :
    setStab G F →* Equiv.Perm {x // x ∈ F} where
  toFun g := (g : Equiv.Perm (Fin n)).subtypePerm fun x => g.2.2 x
  map_one' := by
    ext x
    rfl
  map_mul' g h := by
    ext x
    rfl

theorem card_setStab_le (G : Subgroup (Equiv.Perm (Fin n))) (F : Finset (Fin n)) :
    Nat.card (setStab G F) ≤
      F.card.factorial * Nat.card ↥(G ⊓ fixingSubgroup (Equiv.Perm (Fin n)) (F : Set (Fin n))) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (restr G F).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (restr G F)).toEquiv] at h1
  rw [h1]
  apply Nat.mul_le_mul
  · calc Nat.card (restr G F).range ≤ Nat.card (Equiv.Perm {x // x ∈ F}) :=
          Subgroup.card_le_card_group _
      _ = F.card.factorial := by
          rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_coe]
  · refine Nat.card_le_card_of_injective
      (fun k => ⟨k.1.1, Subgroup.mem_inf.2 ⟨k.1.2.1, ?_⟩⟩)
      (fun a b h => Subtype.ext (Subtype.ext (congrArg Subtype.val h :)))
    · rw [mem_fixingSubgroup_iff]
      intro y hy
      have hk : restr G F k.1 = 1 := k.2
      have := congrArg (fun σ : Equiv.Perm {x // x ∈ F} => (σ ⟨y, hy⟩ : Fin n)) hk
      exact this

theorem two_mul_card_centralizerIn_le (G : Subgroup (Equiv.Perm (Fin n))) (F : Finset (Fin n))
    (z w : Equiv.Perm (Fin n)) (hwG : w ∈ G) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hw : w * z * w⁻¹ = z * z) (hF : ∀ x, z x = x ↔ x ∈ F) :
    2 * Nat.card (centralizerIn G z) ≤
      F.card.factorial * Nat.card ↥(G ⊓ fixingSubgroup (Equiv.Perm (Fin n)) (F : Set (Fin n))) := by
  have hz3' : ∀ x, z (z (z x)) = x := fun x => by
    have := congrArg (fun σ : Equiv.Perm (Fin n) => σ x) hz3
    simpa [pow_succ, Equiv.Perm.mul_apply] using this
  have hfix2 : ∀ x, z (z x) = x ↔ z x = x := fun x =>
    ⟨fun h => by
      have h' := congrArg z h
      rw [hz3'] at h'
      exact h'.symm, fun h => by rw [h, h]⟩
  have hCN : centralizerIn G z ≤ setStab G F := by
    intro g hg
    rw [mem_centralizerIn] at hg
    refine ⟨hg.1, fun x => ?_⟩
    rw [← hF, ← hF]
    have hc : z (g x) = g (z x) := by
      have := congrArg (fun σ : Equiv.Perm (Fin n) => σ x) hg.2
      simpa [Equiv.Perm.mul_apply] using this.symm
    rw [hc]
    exact g.injective.eq_iff
  have hwN : w ∈ setStab G F := by
    refine ⟨hwG, fun x => ?_⟩
    rw [← hF, ← hF, ← hfix2]
    have h1 : z (z (w x)) = w (z x) := by
      have := congrArg (fun σ : Equiv.Perm (Fin n) => σ (w x)) hw
      simpa [Equiv.Perm.mul_apply] using this.symm
    rw [h1]
    exact w.injective.eq_iff
  have hwC : w ∉ centralizerIn G z := by
    rw [mem_centralizerIn]
    rintro ⟨-, h⟩
    apply hz1
    have : z = z * z := by rw [← hw, h, mul_inv_cancel_right]
    simpa using this
  set C := (centralizerIn G z).subgroupOf (setStab G F)
  have hC : Nat.card C = Nat.card (centralizerIn G z) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv
  have hidx := C.card_mul_index
  have hne : C ≠ ⊤ := fun h => hwC (by
    have : (⟨w, hwN⟩ : setStab G F) ∈ C := h ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this)
  have h2 : 2 ≤ C.index := by
    have h0 : C.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : C.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.1 h)
    omega
  have key : 2 * Nat.card (centralizerIn G z) ≤ Nat.card (setStab G F) := by
    rw [← hidx, ← hC, mul_comm]
    exact Nat.mul_le_mul_left _ h2
  exact key.trans (card_setStab_le G F)

end CFSG.Certificates.Kernel.M23Three
