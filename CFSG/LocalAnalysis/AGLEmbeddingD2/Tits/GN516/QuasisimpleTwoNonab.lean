module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open scoped commutatorElement

@[expose] def IsQuasisimpleTwoNonab (B : Type*) [Group B] : Prop :=
  commutator B = ⊤ ∧ IsSimpleGroup (B ⧸ Subgroup.center B) ∧
    120 < Nat.card (B ⧸ Subgroup.center B) ∧ (∀ z ∈ Subgroup.center B, Odd (orderOf z)) ∧
    ∃ Q : Subgroup B, IsPGroup 2 Q ∧ ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a

theorem IsQuasisimpleTwoNonab.of_mulEquiv {B B' : Type*} [Group B] [Group B'] (e : B ≃* B')
    (h : IsQuasisimpleTwoNonab B) : IsQuasisimpleTwoNonab B' := by
  obtain ⟨hc, hs, hn, ho, Q, hQ, a, ha, b, hb, hab⟩ := h
  have hcen : (Subgroup.center B).map e.toMonoidHom = Subgroup.center B' := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      replace hx : x ∈ Subgroup.center B := hx
      rw [Subgroup.mem_center_iff] at hx
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := e.surjective g
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hx g']
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      show e.symm y ∈ Subgroup.center B
      rw [Subgroup.mem_center_iff] at hy
      rw [Subgroup.mem_center_iff]
      intro g
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hy (e g)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := Subgroup.map_commutator (f := e.toMonoidHom) (⊤ : Subgroup B) ⊤
    rw [Subgroup.map_top_of_surjective _ e.surjective] at this
    rw [commutator_def, ← this, ← commutator_def, hc, Subgroup.map_top_of_surjective _ e.surjective]
  · have eq : B ⧸ Subgroup.center B ≃* B' ⧸ Subgroup.center B' :=
      QuotientGroup.congr (Subgroup.center B) (Subgroup.center B') e hcen
    exact MulEquiv.isSimpleGroup eq.symm
  · have eq : B ⧸ Subgroup.center B ≃* B' ⧸ Subgroup.center B' :=
      QuotientGroup.congr (Subgroup.center B) (Subgroup.center B') e hcen
    rw [← Nat.card_congr eq.toEquiv]; exact hn
  · intro z hz
    have hz' : e.symm z ∈ Subgroup.center B := by
      rw [← hcen] at hz
      obtain ⟨x, hx, hxz⟩ := hz
      have : e.symm z = x := by rw [← hxz]; simp
      rw [this]; exact hx
    have := ho _ hz'
    rwa [MulEquiv.orderOf_eq] at this
  · exact ⟨Q.map e.toMonoidHom, hQ.map _, e a, ⟨a, ha, rfl⟩, e b, ⟨b, hb, rfl⟩,
      fun h => hab (e.injective (by simpa using h))⟩

theorem isQuasisimpleTwoNonab_of_simple {G : Type*} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hcard : 120 < Nat.card G)
    (hQ : ∃ Q : Subgroup G, IsPGroup 2 Q ∧ ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a) :
    IsQuasisimpleTwoNonab G := by
  haveI := hs
  obtain ⟨Q, hQ2, a, ha, b, hb, hab⟩ := hQ
  have hnc : ∃ x y : G, x * y ≠ y * x := ⟨a, b, hab⟩
  have hZ : Subgroup.center G = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      have : y ∈ Subgroup.center G := by rw [h]; trivial
      exact hxy (Subgroup.mem_center_iff.1 this x)
  have e : G ⧸ Subgroup.center G ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨?_, e.isSimpleGroup, ?_, ?_, Q, hQ2, a, ha, b, hb, hab⟩
  · rcases hs.eq_bot_or_eq_top_of_normal (commutator G) with h | h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      apply hxy
      have : ⁅x, y⁆ ∈ commutator G := Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    · exact h
  · rwa [Nat.card_congr e.toEquiv]
  · intro z hz
    rw [hZ, Subgroup.mem_bot] at hz
    rw [hz, orderOf_one]
    exact odd_one

end CFSG.AGLEmbeddingD2.Tits.GN516
