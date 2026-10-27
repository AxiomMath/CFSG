module

public import Mathlib
public import CFSG.Open.StatedDefs

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc

@[expose] def LuGroup (L : Type) [Group L] : Prop :=
  (∃ φ : Matrix.SpecialLinearGroup (Fin 4) (GaloisField 3 1) →* L,
      Function.Surjective φ ∧ φ.ker ≤ Subgroup.center _) ∨
  (∃ φ : ↥(CFSG.Open.StatedSp 2 (GaloisField 3 1)) →* L,
      Function.Surjective φ ∧ φ.ker ≤ Subgroup.center _)

@[expose] def LuOutFact : Prop :=
  ∀ (L : Type) [Group L] [Finite L], LuGroup L →
    ∀ Q : Subgroup (MulAut L), Group.IsPerfect ↥Q → Q ≤ (MulAut.conj : L →* MulAut L).range

@[expose] def LuResFact : Prop :=
  ∀ (L : Type) [Group L] [Finite L], LuGroup L →
    ∀ y : L, y * y = 1 → y ∉ Subgroup.center L →
      ∃ A : Subgroup L, (∀ x ∈ A, x * y = y * x) ∧
        (A = ⊥ ∨ Nonempty (↥A ≃* alternatingGroup (Fin 6))) ∧
        ∀ Q : Subgroup L, (∀ x ∈ Q, x * y = y * x) → Group.IsPerfect ↥Q → Q ≤ A

@[expose] def A6AutFact : Prop :=
  ∀ (B : Type) [Group B] [Finite B], Nonempty (B ≃* alternatingGroup (Fin 6)) →
    ∀ f α : MulAut B, f * f = 1 → f ≠ 1 → α * α * α = 1 → α * f = f * α →
      (∀ x, f x = x → α x = x) → α = 1

theorem exists_A_of_fact (hRes : LuResFact) {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : LuGroup ↥L) {y : G} (hyL : y ∈ L) (hy2 : y * y = 1) (hyc : ¬ ∀ l ∈ L, y * l = l * y) :
    ∃ A : Subgroup G, A ≤ L ∧ (∀ x ∈ A, x * y = y * x) ∧
      (A = ⊥ ∨ Nonempty (↥A ≃* alternatingGroup (Fin 6))) ∧
      ∀ Q : Subgroup G, Q ≤ L → (∀ x ∈ Q, x * y = y * x) → Group.IsPerfect ↥Q → Q ≤ A := by
  have hy2' : (⟨y, hyL⟩ : ↥L) * ⟨y, hyL⟩ = 1 := Subtype.ext hy2
  have hyc' : (⟨y, hyL⟩ : ↥L) ∉ Subgroup.center ↥L := by
    intro h
    apply hyc
    intro l hl
    have := Subgroup.mem_center_iff.mp h ⟨l, hl⟩
    exact congrArg Subtype.val this.symm
  obtain ⟨A₀, hA₀y, hA₀type, hA₀max⟩ := hRes ↥L hL ⟨y, hyL⟩ hy2' hyc'
  refine ⟨A₀.map L.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact congrArg Subtype.val (hA₀y a ha)
  · rcases hA₀type with h | ⟨⟨e⟩⟩
    · left
      rw [h, Subgroup.map_bot]
    · right
      exact ⟨(Subgroup.equivMapOfInjective A₀ L.subtype L.subtype_injective).symm.trans e⟩
  · intro Q hQL hQy hQperf
    have hQ0y : ∀ x ∈ Q.subgroupOf L, x * ⟨y, hyL⟩ = ⟨y, hyL⟩ * x := by
      intro x hx
      exact Subtype.ext (hQy x hx)
    have hperf0 : Group.IsPerfect ↥(Q.subgroupOf L) := by
      have e : ↥Q ≃* ↥(Q.subgroupOf L) := (Subgroup.subgroupOfEquivOfLe hQL).symm
      exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    have h1 := hA₀max _ hQ0y hperf0
    intro x hx
    exact ⟨⟨x, hQL hx⟩, h1 hx, rfl⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc
