module

public import CFSG.GH74.Generic.Front.DataLin
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.TwinFr

open CFSG CFSG.ClassicalInvolution
open scoped MatrixGroups

@[expose] noncomputable def sl2RingEquiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) :
    SL(2, R) ≃* SL(2, S) :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map e.toRingHom)
    (Matrix.SpecialLinearGroup.map e.symm.toRingHom)
    (by ext x i j; simp) (by ext x i j; simp)

theorem sl2_zmod_three_fact : ∃ x₃ : SL(2, ZMod 3), x₃ ^ 3 = 1 ∧ ∀ b : SL(2, ZMod 3),
    b ^ 4 = 1 → b ^ 2 ≠ 1 → x₃ * b ≠ b * x₃ ∧ x₃ * b * x₃⁻¹ * b ≠ b * (x₃ * b * x₃⁻¹) := by
  decide

variable {Y : Type} [Group Y] {F' : Type} [Field F']

theorem exists_three_of_equiv_sl2 [Finite F'] (h3 : Nat.card F' = 3) {J : Subgroup Y}
    (e : J ≃* SL(2, F')) : ∃ x₃ ∈ J, x₃ ^ 3 = 1 ∧ ∀ b ∈ J, b ^ 4 = 1 → b ^ 2 ≠ 1 →
      x₃ * b ≠ b * x₃ ∧ x₃ * b * x₃⁻¹ * b ≠ b * (x₃ * b * x₃⁻¹) := by
  have : Fintype F' := Fintype.ofFinite F'
  have hc : Fintype.card F' = 3 := by rw [← Nat.card_eq_fintype_card, h3]
  let f : SL(2, ZMod 3) ≃* J := (sl2RingEquiv (ZMod.ringEquivOfPrime F' Nat.prime_three hc)).trans
    e.symm
  obtain ⟨x, hx3, hx⟩ := sl2_zmod_three_fact
  refine ⟨f x, (f x).2, by rw [← Subgroup.coe_pow, ← map_pow, hx3, map_one]; rfl, ?_⟩
  intro b hb hb4 hb2
  obtain ⟨b', hb'⟩ := f.surjective ⟨b, hb⟩
  have hb4' : b' ^ 4 = 1 := f.injective (by
    rw [map_pow, hb', map_one]; exact Subtype.ext (by simpa using hb4))
  have hb2' : b' ^ 2 ≠ 1 := fun h => hb2 (by
    have := congrArg (fun z => ((f z : J) : Y)) h
    simpa [hb'] using this)
  obtain ⟨h1, h2⟩ := hx b' hb4' hb2'
  have hbb : ((f b' : J) : Y) = b := by rw [hb']
  refine ⟨fun h => h1 (f.injective (Subtype.ext ?_)), fun h => h2 (f.injective (Subtype.ext ?_))⟩
  · simpa [hbb] using h
  · simpa [hbb, mul_assoc] using h

set_option synthInstance.maxSize 2048 in
theorem sl2_zmod_three_gen : ∀ β β' γ : SL(2, ZMod 3), β ^ 4 = 1 → β ^ 2 ≠ 1 → β' ^ 4 = 1 →
    β' ^ 2 ≠ 1 → β * β' ≠ β' * β → γ ^ 4 = 1 → γ ^ 2 ≠ 1 →
    γ = β ∨ γ = β⁻¹ ∨ γ = β' ∨ γ = β'⁻¹ ∨ γ = β * β' ∨ γ = (β * β')⁻¹ := by
  decide

theorem comm_of_comm_pair [Finite F'] (h3 : Nat.card F' = 3) {J : Subgroup Y}
    (e : J ≃* SL(2, F')) {β β' γ g : Y} (hβ : β ∈ J) (hβ' : β' ∈ J) (hγ : γ ∈ J)
    (hβ4 : β ^ 4 = 1) (hβ2 : β ^ 2 ≠ 1) (hβ'4 : β' ^ 4 = 1) (hβ'2 : β' ^ 2 ≠ 1)
    (hne : β * β' ≠ β' * β) (hγ4 : γ ^ 4 = 1) (hγ2 : γ ^ 2 ≠ 1) (hgβ : Commute g β)
    (hgβ' : Commute g β') : Commute g γ := by
  have : Fintype F' := Fintype.ofFinite F'
  have hc : Fintype.card F' = 3 := by rw [← Nat.card_eq_fintype_card, h3]
  let f : SL(2, ZMod 3) ≃* J := (sl2RingEquiv (ZMod.ringEquivOfPrime F' Nat.prime_three hc)).trans
    e.symm
  obtain ⟨β₀, hβ₀⟩ := f.surjective ⟨β, hβ⟩
  obtain ⟨β₀', hβ₀'⟩ := f.surjective ⟨β', hβ'⟩
  obtain ⟨γ₀, hγ₀⟩ := f.surjective ⟨γ, hγ⟩
  have key : ∀ (z₀ : SL(2, ZMod 3)) (z : Y) (hz : z ∈ J), f z₀ = ⟨z, hz⟩ → ∀ k : ℕ,
      (z₀ ^ k = 1 ↔ z ^ k = 1) := fun z₀ z hz h k => by
    rw [← f.injective.eq_iff, map_pow, map_one, h, Subtype.ext_iff]
    simp
  have hmul : ∀ (z₀ w₀ : SL(2, ZMod 3)), ((f (z₀ * w₀) : J) : Y) = (f z₀ : Y) * (f w₀ : Y) :=
    fun z₀ w₀ => by rw [map_mul]; rfl
  have hne₀ : β₀ * β₀' ≠ β₀' * β₀ := fun h => hne (by
    have := congrArg (fun z => ((f z : J) : Y)) h
    simpa [hmul, hβ₀, hβ₀'] using this)
  have hgβ₀ : ∀ z₀ : SL(2, ZMod 3), Commute g (f z₀ : Y) → Commute g (f z₀⁻¹ : Y) := fun z₀ h => by
    rw [map_inv]
    exact h.inv_right
  rcases sl2_zmod_three_gen β₀ β₀' γ₀ ((key _ _ hβ hβ₀ 4).mpr hβ4)
      (fun h => hβ2 ((key _ _ hβ hβ₀ 2).mp h)) ((key _ _ hβ' hβ₀' 4).mpr hβ'4)
      (fun h => hβ'2 ((key _ _ hβ' hβ₀' 2).mp h)) hne₀ ((key _ _ hγ hγ₀ 4).mpr hγ4)
      (fun h => hγ2 ((key _ _ hγ hγ₀ 2).mp h)) with h | h | h | h | h | h <;>
    rw [show γ = ((f γ₀ : J) : Y) by rw [hγ₀], h]
  · rw [hβ₀]; exact hgβ
  · exact hgβ₀ β₀ (by rw [hβ₀]; exact hgβ)
  · rw [hβ₀']; exact hgβ'
  · exact hgβ₀ β₀' (by rw [hβ₀']; exact hgβ')
  · rw [hmul, hβ₀, hβ₀']; exact hgβ.mul_right hgβ'
  · exact hgβ₀ _ (by rw [hmul, hβ₀, hβ₀']; exact hgβ.mul_right hgβ')

theorem oddGenerated_of_equiv_sl2 [Finite F'] (hodd : Odd (Nat.card F')) {J : Subgroup Y}
    (e : J ≃* SL(2, F')) : GH74.Generic.OddGenerated J := by
  set S : Set Y := {g | g ∈ J ∧ Odd (orderOf g)} with hS
  apply le_antisymm
  · exact (Subgroup.closure_le _).2 fun g hg => hg.1
  · intro g hg
    let κ : SL(2, F') →* Y := J.subtype.comp e.symm.toMonoidHom
    have hκ : κ (e ⟨g, hg⟩) = g := by simp [κ]
    rw [← hκ]
    refine GH74.Generic.map_mem_closure_of_elementary κ S (fun x hx => ⟨?_, ?_⟩) _
    · exact (e.symm x).2
    · exact GH74.Generic.odd_orderOf_map_elementary hodd κ hx

end CFSG.ClassicalInvolution.Q3.TA3.TwinFr
