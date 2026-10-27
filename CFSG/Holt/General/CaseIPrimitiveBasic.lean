module

public import CFSG.Holt.General.Defs

public section

namespace CFSG.Holt.General

open MulAction Equiv Equiv.Perm

section Alternating

variable (n : ℕ) [NeZero n]

private theorem ofSubtype_mem_alternatingGroup (a : alternatingGroup {x : Fin n // x ≠ 0}) :
    ofSubtype (a : Perm {x : Fin n // x ≠ 0}) ∈ alternatingGroup (Fin n) := by
  rw [mem_alternatingGroup, sign_ofSubtype]
  exact mem_alternatingGroup.mp a.2

private noncomputable def toAlternatingZero :
    alternatingGroup {x : Fin n // x ≠ 0} →* alternatingGroup (Fin n) :=
  (ofSubtype.comp (alternatingGroup {x : Fin n // x ≠ 0}).subtype).codRestrict
    (alternatingGroup (Fin n)) (ofSubtype_mem_alternatingGroup n)

private theorem toAlternatingZero_mem_stabilizer (a : alternatingGroup {x : Fin n // x ≠ 0}) :
    toAlternatingZero n a ∈ stabilizer (alternatingGroup (Fin n)) (0 : Fin n) := by
  rw [mem_stabilizer_iff]
  exact ofSubtype_apply_of_not_mem _ (by simp)

private noncomputable def toStabilizerZero :
    alternatingGroup {x : Fin n // x ≠ 0} →* stabilizer (alternatingGroup (Fin n)) (0 : Fin n) :=
  (toAlternatingZero n).codRestrict _ (toAlternatingZero_mem_stabilizer n)

private theorem toStabilizerZero_injective : Function.Injective (toStabilizerZero n) := by
  intro a b hab
  have h := congrArg
    (fun g : stabilizer (alternatingGroup (Fin n)) (0 : Fin n) =>
      ((g : alternatingGroup (Fin n)) : Perm (Fin n))) hab
  exact Subtype.ext (ofSubtype_injective h)

private theorem toStabilizerZero_surjective : Function.Surjective (toStabilizerZero n) := by
  rintro ⟨⟨τ, hτ⟩, hτ0⟩
  have h0 : τ 0 = 0 := hτ0
  have h₁ : ∀ x, τ x ≠ 0 ↔ x ≠ 0 := fun x =>
    not_congr ⟨fun h => τ.injective (h.trans h0.symm), fun h => h ▸ h0⟩
  have hsub : ofSubtype (τ.subtypePerm (p := fun y => y ≠ 0) h₁) = τ :=
    ofSubtype_subtypePerm (p := fun y => y ≠ 0) h₁ fun x hx h => hx (h.symm ▸ h0)
  refine ⟨⟨τ.subtypePerm (p := fun y => y ≠ 0) h₁, ?_⟩, ?_⟩
  · rw [mem_alternatingGroup, ← sign_ofSubtype, hsub]
    exact mem_alternatingGroup.mp hτ
  · exact Subtype.ext (Subtype.ext hsub)

noncomputable def alternatingStabilizerZeroEquiv :
    alternatingGroup {x : Fin n // x ≠ 0} ≃* stabilizer (alternatingGroup (Fin n)) (0 : Fin n) :=
  MulEquiv.ofBijective (toStabilizerZero n)
    ⟨toStabilizerZero_injective n, toStabilizerZero_surjective n⟩

end Alternating

section Imprimitive

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] {z : G} {α : Ω}

theorem exists_stabilizer_lt_of_not_isPreprimitive [IsPretransitive G Ω] [Nontrivial Ω]
    (h : ¬ IsPreprimitive G Ω) (α : Ω) : ∃ K : Subgroup G, stabilizer G α < K ∧ K ≠ ⊤ := by
  rw [← isCoatom_stabilizer_iff_preprimitive G α] at h
  have hne : stabilizer G α ≠ ⊤ := by
    intro htop
    obtain ⟨ω, hω⟩ := exists_ne α
    obtain ⟨g, rfl⟩ := exists_smul_eq G α ω
    exact hω (htop ▸ Subgroup.mem_top g : g ∈ stabilizer G α)
  by_contra hK
  refine h ⟨hne, fun K hlt => ?_⟩
  by_contra hKtop
  exact hK ⟨K, hlt, hKtop⟩

end Imprimitive

end CFSG.Holt.General
