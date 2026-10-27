module

public import CFSG.CGT.PushingUp.Defs

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.CGT.PushingUp

variable {m : ℕ}

theorem mem_altStabilizer_iff {F : Finset (Fin m)} {σ : alternatingGroup (Fin m)} :
    σ ∈ altStabilizer m F ↔ ∀ i ∈ F, (σ : Equiv.Perm (Fin m)) i = i := by
  simp only [altStabilizer, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]
  rfl

section Equiv

variable (F : Finset (Fin m))

theorem card_notMem_finset : Fintype.card {i : Fin m // i ∉ F} = m - F.card := by
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]

@[expose] noncomputable def complEquiv : Fin (m - F.card) ≃ {i : Fin m // i ∉ F} :=
  (Fintype.equivFinOfCardEq (card_notMem_finset F)).symm

@[expose] noncomputable def altStabIncl :
    alternatingGroup (Fin (m - F.card)) →* alternatingGroup (Fin m) :=
  ((Equiv.Perm.ofSubtype (p := fun i : Fin m => i ∉ F)).comp
      ((Equiv.permCongrHom (complEquiv F)).toMonoidHom.comp
        (alternatingGroup (Fin (m - F.card))).subtype)).codRestrict (alternatingGroup (Fin m))
    (fun τ => by
      rw [Equiv.Perm.mem_alternatingGroup]
      show Equiv.Perm.sign (Equiv.Perm.ofSubtype ((complEquiv F).permCongr (τ : Equiv.Perm _))) = 1
      rw [Equiv.Perm.sign_ofSubtype, Equiv.Perm.sign_permCongr]
      exact Equiv.Perm.mem_alternatingGroup.mp τ.2)

theorem altStabIncl_apply (τ : alternatingGroup (Fin (m - F.card))) :
    ((altStabIncl F τ : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) =
      Equiv.Perm.ofSubtype ((complEquiv F).permCongr (τ : Equiv.Perm (Fin (m - F.card)))) := rfl

theorem altStabIncl_injective : Function.Injective (altStabIncl F) := by
  intro a b h
  have h1 : Equiv.Perm.ofSubtype ((complEquiv F).permCongr (a : Equiv.Perm (Fin (m - F.card)))) =
      Equiv.Perm.ofSubtype ((complEquiv F).permCongr (b : Equiv.Perm (Fin (m - F.card)))) := by
    rw [← altStabIncl_apply, ← altStabIncl_apply, h]
  have h2 := Equiv.Perm.ofSubtype_injective h1
  have h3 : (a : Equiv.Perm (Fin (m - F.card))) = b :=
    (Equiv.permCongr (complEquiv F)).injective h2
  exact Subtype.ext h3

theorem altStabIncl_range : (altStabIncl F).range = altStabilizer m F := by
  ext σ
  rw [MonoidHom.mem_range, mem_altStabilizer_iff]
  constructor
  · rintro ⟨τ, rfl⟩ i hi
    rw [altStabIncl_apply]
    exact Equiv.Perm.ofSubtype_apply_of_not_mem _ (not_not.mpr hi)
  · intro hσ
    obtain ⟨τ', hτ'⟩ := (Equiv.Perm.subtypeEquivSubtypePerm (fun i : Fin m => i ∉ F)).surjective
      ⟨(σ : Equiv.Perm (Fin m)), fun a ha => hσ a (not_not.mp ha)⟩
    have hτ'σ : Equiv.Perm.ofSubtype τ' = (σ : Equiv.Perm (Fin m)) := congrArg Subtype.val hτ'
    refine ⟨⟨(complEquiv F).symm.permCongr τ', ?_⟩, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_permCongr]
      have h1 : Equiv.Perm.sign (Equiv.Perm.ofSubtype τ') = 1 := by
        rw [hτ'σ]
        exact Equiv.Perm.mem_alternatingGroup.mp σ.2
      rwa [Equiv.Perm.sign_ofSubtype] at h1
    · apply Subtype.ext
      rw [altStabIncl_apply]
      simp only
      rw [← hτ'σ]
      congr 1
      ext x
      simp [Equiv.permCongr_apply]

@[expose] noncomputable def altStabilizerEquiv :
    altStabilizer m F ≃* alternatingGroup (Fin (m - F.card)) :=
  (MulEquiv.subgroupCongr (altStabIncl_range F).symm).trans
    (MonoidHom.ofInjective (altStabIncl_injective F)).symm

theorem card_altStabilizer (hF : F.card + 2 ≤ m) :
    Nat.card (altStabilizer m F) = (m - F.card).factorial / 2 := by
  have : Nontrivial (Fin (m - F.card)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [Nat.card_congr (altStabilizerEquiv F).toEquiv, nat_card_alternatingGroup,
    Nat.card_eq_fintype_card, Fintype.card_fin]

end Equiv

section ThreeCycle

theorem altStabilizer_eq_zpowers_of_isThreeCycle {π : alternatingGroup (Fin m)}
    (h : (π : Equiv.Perm (Fin m)).IsThreeCycle) :
    altStabilizer m (Finset.univ \ (π : Equiv.Perm (Fin m)).support) = Subgroup.zpowers π := by
  have hsupp : (π : Equiv.Perm (Fin m)).support.card = 3 := h.card_support
  have hcard : (Finset.univ \ (π : Equiv.Perm (Fin m)).support).card = m - 3 := by
    rw [Finset.card_univ_sdiff, Fintype.card_fin, hsupp]
  have hm : 3 ≤ m := by
    have := Finset.card_le_univ (π : Equiv.Perm (Fin m)).support
    rw [hsupp, Fintype.card_fin] at this
    exact this
  symm
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [Subgroup.zpowers_le]
    rw [mem_altStabilizer_iff]
    intro i hi
    rw [Finset.mem_sdiff] at hi
    exact Equiv.Perm.notMem_support.mp hi.2
  · rw [card_altStabilizer _ (by omega), hcard, Nat.card_zpowers]
    have h3 : orderOf π = 3 := by
      have := h.orderOf
      rwa [Subgroup.orderOf_coe] at this
    rw [h3]
    have : m - (m - 3) = 3 := by omega
    rw [this]
    decide

end ThreeCycle

end CFSG.CGT.PushingUpLit.CGT6
