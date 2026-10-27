module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup CFSG.Open

@[expose] def HasS6Quotient {M : Type*} [Group M] (N K : Subgroup M) : Prop :=
  ∃ φ : ↥N →* Equiv.Perm (Fin 6), Function.Surjective φ ∧ φ.ker = K.subgroupOf N

@[expose] def IsSpecialElem {M : Type*} [Group M] (z : M) (E : Subgroup M) : Prop :=
  z ∈ E ∧ IsElemAbelian 2 E ∧ Nat.card E = 16 ∧ HasS6Quotient (normalizer (E : Set M)) E ∧
    ∀ e ∈ E, e ≠ 1 → ∃ a ∈ normalizer (E : Set M), a * z * a⁻¹ = e

@[expose] def IsSpecialIn {G : Type*} [Group G] (L : Subgroup G) (z : G) (E : Subgroup G) : Prop :=
  E ≤ L ∧ z ∈ E ∧ IsElemAbelian 2 E ∧ Nat.card E = 16 ∧
    HasS6Quotient (normalizer (E : Set G) ⊓ L) E ∧
    ∀ e ∈ E, e ≠ 1 → ∃ a ∈ normalizer (E : Set G) ⊓ L, a * z * a⁻¹ = e

section Aux

variable {M M' : Type*} [Group M] [Group M']

private theorem isElemAbelian_iff {p : ℕ} {E : Subgroup M} :
    IsElemAbelian p E ↔ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ ∀ x ∈ E, x ^ p = 1 := by
  unfold IsElemAbelian
  rw [isMulCommutative_iff_of_setLike]

private theorem HasS6Quotient.of_mulEquiv {N K : Subgroup M} {N' K' : Subgroup M'}
    (e : ↥N ≃* ↥N') (he : ∀ x : ↥N, (x : M) ∈ K ↔ ((e x : ↥N') : M') ∈ K')
    (h : HasS6Quotient N K) : HasS6Quotient N' K' := by
  obtain ⟨φ, hφ, hker⟩ := h
  refine ⟨φ.comp e.symm.toMonoidHom, hφ.comp e.symm.surjective, ?_⟩
  ext x'
  have h1 : (φ.comp e.symm.toMonoidHom) x' = 1 ↔ φ (e.symm x') = 1 := Iff.rfl
  rw [MonoidHom.mem_ker, h1, ← MonoidHom.mem_ker, hker, mem_subgroupOf, he, MulEquiv.apply_symm_apply,
    mem_subgroupOf]

private theorem hasS6Quotient_iff_of_mulEquiv {N K : Subgroup M} {N' K' : Subgroup M'}
    (e : ↥N ≃* ↥N') (he : ∀ x : ↥N, (x : M) ∈ K ↔ ((e x : ↥N') : M') ∈ K') :
    HasS6Quotient N K ↔ HasS6Quotient N' K' := by
  refine ⟨HasS6Quotient.of_mulEquiv e he, HasS6Quotient.of_mulEquiv e.symm ?_⟩
  intro y
  have := he (e.symm y)
  simpa using this.symm

private theorem mem_map_mulEquiv (f : M ≃* M') (E : Subgroup M) (a : M) :
    f a ∈ E.map f.toMonoidHom ↔ a ∈ E :=
  Subgroup.mem_map_iff_mem (f := f.toMonoidHom) f.injective

private theorem mem_normalizer_map_iff (f : M ≃* M') (E : Subgroup M) (x : M) :
    f x ∈ normalizer ((E.map f.toMonoidHom : Subgroup M') : Set M') ↔
      x ∈ normalizer (E : Set M) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h h0
    have := h (f h0)
    rwa [← map_inv, ← map_mul, ← map_mul, mem_map_mulEquiv, mem_map_mulEquiv] at this
  · intro h h'
    obtain ⟨h0, rfl⟩ := f.surjective h'
    have := h h0
    rw [mem_map_mulEquiv, ← map_inv, ← map_mul, ← map_mul, mem_map_mulEquiv]
    exact this

end Aux

theorem IsSpecialElem.map {M M' : Type*} [Group M] [Group M'] (f : M ≃* M') {z : M} {E : Subgroup M}
    (h : IsSpecialElem z E) : IsSpecialElem (f z) (E.map f.toMonoidHom) := by
  obtain ⟨hz, hab, hcard, hS6, htrans⟩ := h
  refine ⟨Subgroup.mem_map_of_mem _ hz, ?_, ?_, ?_, ?_⟩
  · rw [isElemAbelian_iff] at hab ⊢
    obtain ⟨hc, hp⟩ := hab
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hc a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, ← map_pow, hp a ha, map_one]
  · rw [← hcard]
    exact Subgroup.card_map_of_injective f.injective
  · let e : ↥(normalizer (E : Set M)) ≃* ↥(normalizer ((E.map f.toMonoidHom : Subgroup M') : Set M')) :=
      { toFun := fun x => ⟨f x, (mem_normalizer_map_iff f E x).2 x.2⟩
        invFun := fun y => ⟨f.symm y, by
          have := (mem_normalizer_map_iff f E (f.symm y)).1
          rw [f.apply_symm_apply] at this
          exact this y.2⟩
        left_inv := fun x => by ext; simp
        right_inv := fun y => by ext; simp
        map_mul' := fun x y => Subtype.ext (map_mul f (x : M) (y : M)) }
    refine (hasS6Quotient_iff_of_mulEquiv e ?_).1 hS6
    intro x
    change (x : M) ∈ E ↔ f x ∈ E.map f.toMonoidHom
    exact (mem_map_mulEquiv f E x).symm
  · intro e' he' hne
    obtain ⟨e0, he0, rfl⟩ := he'
    obtain ⟨a, ha, hae⟩ := htrans e0 he0 (by rintro rfl; exact hne (map_one _))
    refine ⟨f a, (mem_normalizer_map_iff f E a).2 ha, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_inv, ← map_mul, ← map_mul, hae]

section Internal

variable {G : Type*} [Group G]

private theorem mem_normalizer_subgroupOf_iff {L E : Subgroup G} (hE : E ≤ L) (x : ↥L) :
    x ∈ normalizer ((E.subgroupOf L : Subgroup ↥L) : Set ↥L) ↔
      (x : G) ∈ normalizer (E : Set G) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h g
    by_cases hg : g ∈ L
    · have := h ⟨g, hg⟩
      simpa [mem_subgroupOf] using this
    · have h1 : g ∉ E := fun hgE => hg (hE hgE)
      have h2 : (x : G) * g * (x : G)⁻¹ ∉ E := by
        intro hmem
        apply hg
        have hmL := hE hmem
        have : g = (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * (x : G) := by group
        rw [this]
        exact L.mul_mem (L.mul_mem (L.inv_mem x.2) hmL) x.2
      exact ⟨fun hh => absurd hh h1, fun hh => absurd hh h2⟩
  · intro h g
    have := h (g : G)
    simpa [mem_subgroupOf] using this

theorem isSpecialIn_iff {G : Type*} [Group G] {L : Subgroup G} {z : G} (hz : z ∈ L)
    {E : Subgroup G} (hE : E ≤ L) :
    IsSpecialIn L z E ↔ IsSpecialElem (⟨z, hz⟩ : ↥L) (E.subgroupOf L) := by
  have hab : IsElemAbelian 2 E ↔ IsElemAbelian 2 (E.subgroupOf L) := by
    rw [isElemAbelian_iff, isElemAbelian_iff]
    constructor
    · rintro ⟨hc, hp⟩
      refine ⟨fun a ha b hb => ?_, fun x hx => ?_⟩
      · exact Subtype.ext (hc a ha b hb)
      · exact Subtype.ext (hp x hx)
    · rintro ⟨hc, hp⟩
      refine ⟨fun a ha b hb => ?_, fun x hx => ?_⟩
      · have := hc ⟨a, hE ha⟩ ha ⟨b, hE hb⟩ hb
        exact congrArg Subtype.val this
      · have := hp ⟨x, hE hx⟩ hx
        exact congrArg Subtype.val this
  have hcard : Nat.card E = Nat.card (E.subgroupOf L) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv.symm
  let e : ↥(normalizer (E : Set G) ⊓ L) ≃*
      ↥(normalizer ((E.subgroupOf L : Subgroup ↥L) : Set ↥L)) :=
    { toFun := fun x => ⟨⟨x, x.2.2⟩, (mem_normalizer_subgroupOf_iff hE ⟨x, x.2.2⟩).2 x.2.1⟩
      invFun := fun y => ⟨y.1, (mem_normalizer_subgroupOf_iff hE y.1).1 y.2, y.1.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun y => by ext; rfl
      map_mul' := fun x y => by ext; rfl }
  have hS6 : HasS6Quotient (normalizer (E : Set G) ⊓ L) E ↔
      HasS6Quotient (normalizer ((E.subgroupOf L : Subgroup ↥L) : Set ↥L)) (E.subgroupOf L) := by
    refine hasS6Quotient_iff_of_mulEquiv e ?_
    intro x
    change (x : G) ∈ E ↔ (⟨x, x.2.2⟩ : ↥L) ∈ E.subgroupOf L
    rw [mem_subgroupOf]
  have htrans : (∀ e ∈ E, e ≠ 1 → ∃ a ∈ normalizer (E : Set G) ⊓ L, a * z * a⁻¹ = e) ↔
      ∀ e ∈ E.subgroupOf L, e ≠ 1 →
        ∃ a ∈ normalizer ((E.subgroupOf L : Subgroup ↥L) : Set ↥L),
          a * (⟨z, hz⟩ : ↥L) * a⁻¹ = e := by
    constructor
    · intro h e' he' hne
      have hne' : (e' : G) ≠ 1 := fun h1 => hne (Subtype.ext h1)
      obtain ⟨a, ha, hae⟩ := h (e' : G) he' hne'
      refine ⟨⟨a, ha.2⟩, (mem_normalizer_subgroupOf_iff hE ⟨a, ha.2⟩).2 ha.1, ?_⟩
      exact Subtype.ext hae
    · intro h e' he' hne
      obtain ⟨a, ha, hae⟩ := h ⟨e', hE he'⟩ he' (fun h1 => hne (congrArg Subtype.val h1))
      exact ⟨a, ⟨(mem_normalizer_subgroupOf_iff hE a).1 ha, a.2⟩, congrArg Subtype.val hae⟩
  unfold IsSpecialIn IsSpecialElem
  rw [hab, hcard, hS6, htrans]
  simp only [mem_subgroupOf, hE, true_and]

theorem IsSpecialElem.isSpecialIn {G : Type*} [Group G] {L : Subgroup G} {z : ↥L} {E : Subgroup ↥L}
    (h : IsSpecialElem z E) : IsSpecialIn L (z : G) (E.map L.subtype) := by
  have hle : E.map L.subtype ≤ L := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  rw [isSpecialIn_iff z.2 hle]
  have heq : (E.map L.subtype).subgroupOf L = E :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective E
  rw [heq]
  exact h

end Internal

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
