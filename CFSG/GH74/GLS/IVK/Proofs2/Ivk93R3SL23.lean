module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage2.Local.Lemma23eRes

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

theorem sl23_q8_mul : ∀ a b : SL23, a ^ 4 = 1 → b ^ 4 = 1 → (a * b) ^ 4 = 1 := by
  decide +kernel

theorem sl23_q8_comm : ∀ x : SL23, x ^ 4 = 1 → ∃ g h : SL23, x = ⁅g, h⁆ := by
  decide +kernel

theorem sl23_q8_quat : ∀ w : SL23, w * w = 1 → w ≠ 1 → (∀ g : SL23, g * w = w * g) →
    w ^ 4 = 1 ∧ ∃ a b : SL23, a ^ 4 = 1 ∧ b ^ 4 = 1 ∧ a * a = w ∧ b * b = w ∧ a * b ≠ b * a := by
  decide +kernel

theorem sl23_q8_card : Fintype.card {x : SL23 // x ^ 4 = 1} = 8 := by
  decide +kernel

@[expose] def sl23Q8 : Subgroup SL23 where
  carrier := {x | x ^ 4 = 1}
  mul_mem' := fun {a b} ha hb => sl23_q8_mul a b ha hb
  one_mem' := one_pow 4
  inv_mem' := fun {a} ha => by
    have : a⁻¹ ^ 4 = (a ^ 4)⁻¹ := (inv_pow a 4)
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [this, ha, inv_one]

theorem sl23_q8_facts {Y : Type} [Group Y] {L : Subgroup Y}
    (h : HasSL2Model ↥L (fun r => r = 3)) {w : Y} (hwL : w ∈ L) (hw2 : w * w = 1) (hw1 : w ≠ 1)
    (hwc : ∀ g ∈ L, g * w = w * g) :
    ∃ Q : Subgroup Y, Q ≤ L ∧ Q ≤ ⁅L, L⁆ ∧ Nat.card ↥Q = 8 ∧ IsPGroup 2 ↥Q ∧ w ∈ Q ∧
      ∃ a ∈ Q, ∃ b ∈ Q, a * a = w ∧ b * b = w ∧ a * b ≠ b * a := by
  obtain ⟨F, hF, hFin, hq, ⟨e⟩⟩ := h
  have hq' : Nat.card F = 3 := hq
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, hq', ZMod.card]
  let φ : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hcard
  let Φ : ↥L ≃* SL23 :=
    (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm).trans (slMapEquiv φ)
  let Q : Subgroup Y := (sl23Q8.map Φ.symm.toMonoidHom).map L.subtype
  have hmemQ : ∀ x : SL23, x ^ 4 = 1 → ((Φ.symm x : ↥L) : Y) ∈ Q := fun x hx =>
    ⟨Φ.symm x, ⟨x, hx, rfl⟩, rfl⟩
  have hQmem : ∀ y ∈ Q, ∃ x : SL23, x ^ 4 = 1 ∧ y = ((Φ.symm x : ↥L) : Y) := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  have hw' : (Φ ⟨w, hwL⟩) * Φ ⟨w, hwL⟩ = 1 := by
    rw [← map_mul]
    have : (⟨w, hwL⟩ : ↥L) * ⟨w, hwL⟩ = 1 := Subtype.ext hw2
    rw [this, map_one]
  have hw1' : Φ ⟨w, hwL⟩ ≠ 1 := by
    intro h1
    apply hw1
    have : (⟨w, hwL⟩ : ↥L) = 1 := Φ.injective (by rw [h1, map_one])
    exact congrArg Subtype.val this
  have hwc' : ∀ g : SL23, g * Φ ⟨w, hwL⟩ = Φ ⟨w, hwL⟩ * g := by
    intro g
    obtain ⟨g', rfl⟩ := Φ.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hwc g' g'.2)
  obtain ⟨hw4, a, b, ha4, hb4, haa, hbb, hab⟩ := sl23_q8_quat _ hw' hw1' hwc'
  have hwΦ : w = ((Φ.symm (Φ ⟨w, hwL⟩) : ↥L) : Y) := by rw [MulEquiv.symm_apply_apply]
  refine ⟨Q, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hQmem y hy
    obtain ⟨g, k, hgk⟩ := sl23_q8_comm x hx
    have hgk' : (Φ.symm x : ↥L) = ⁅Φ.symm g, Φ.symm k⁆ := by
      rw [hgk, map_commutatorElement]
    rw [hgk']
    have : (((⁅Φ.symm g, Φ.symm k⁆ : ↥L)) : Y) = ⁅((Φ.symm g : ↥L) : Y), ((Φ.symm k : ↥L) : Y)⁆ := by
      simp [commutatorElement_def]
    rw [this]
    exact Subgroup.commutator_mem_commutator (Φ.symm g).2 (Φ.symm k).2
  · show Nat.card ↥((sl23Q8.map Φ.symm.toMonoidHom).map L.subtype) = 8
    rw [Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective Φ.symm.injective]
    have : Nat.card ↥sl23Q8 = Nat.card {x : SL23 // x ^ 4 = 1} := rfl
    rw [this, Nat.card_eq_fintype_card, sl23_q8_card]
  · intro g
    obtain ⟨x, hx, hy⟩ := hQmem (g : Y) g.2
    refine ⟨2, ?_⟩
    apply Subtype.ext
    show (g : Y) ^ (2 ^ 2) = 1
    rw [hy]
    have : ((Φ.symm x : ↥L) : Y) ^ (2 ^ 2) = ((Φ.symm (x ^ 4) : ↥L) : Y) := by
      rw [map_pow]
      rfl
    rw [this, hx, map_one]
    rfl
  · rw [hwΦ]
    exact hmemQ _ hw4
  · refine ⟨((Φ.symm a : ↥L) : Y), hmemQ a ha4, ((Φ.symm b : ↥L) : Y), hmemQ b hb4, ?_, ?_, ?_⟩
    · rw [← Subgroup.coe_mul, ← map_mul, haa]
      exact hwΦ.symm
    · rw [← Subgroup.coe_mul, ← map_mul, hbb]
      exact hwΦ.symm
    · intro hc
      apply hab
      have h1 : (Φ.symm a : ↥L) * Φ.symm b = Φ.symm b * Φ.symm a := Subtype.ext hc
      have h2 := congrArg Φ h1
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h2

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
