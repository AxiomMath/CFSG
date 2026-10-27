module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceTraceZeroIrreducible
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceFixedCodimensions

public section

namespace CFSG.OddStandard.Harada75

open Subgroup CFSG.ProperTwoGeneratedCore.BinaryThreeSpace
open scoped commutatorElement Pointwise

theorem card_GL3F2 : Nat.card (GL (Fin 3) (ZMod 2)) = 168 :=
  CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.FixedCodim.card_GL3

theorem card_le_eight_of_isPGroup {H : Subgroup (GL (Fin 3) (ZMod 2))} (hH : IsPGroup 2 H) :
    Nat.card H ≤ 8 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hH
  have hdvd : 2 ^ k ∣ 168 := by
    rw [← hk, ← card_GL3F2]
    exact H.card_subgroup_dvd_card
  rcases le_or_gt k 3 with hk3 | hk4
  · calc Nat.card H = 2 ^ k := hk
      _ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
  · exfalso
    have h16 : 2 ^ 4 ∣ 168 := (pow_dvd_pow 2 hk4).trans hdvd
    norm_num at h16

theorem unitriGL_mul_ne :
    unitriGL 1 0 0 * unitriGL 0 0 1 ≠ unitriGL 0 0 1 * unitriGL 1 0 0 := by
  intro h
  have h' := congrArg (fun g : GL (Fin 3) (ZMod 2) => (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) h
  revert h'
  decide

theorem exists_not_commute_of_card_eq_eight {H : Subgroup (GL (Fin 3) (ZMod 2))}
    (hHp : IsPGroup 2 H) (h8 : Nat.card H = 8) : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hHidx : H.index = 21 := by
    have h := H.card_mul_index
    rw [h8, card_GL3F2] at h
    omega
  have hTidx : sylowT.index = 21 := by
    have h := sylowT.card_mul_index
    rw [card_sylowT, card_GL3F2] at h
    omega
  have hTp : IsPGroup 2 sylowT := IsPGroup.of_card card_sylowT
  let PH : Sylow 2 (GL (Fin 3) (ZMod 2)) := hHp.toSylow (by rw [hHidx]; decide)
  let PT : Sylow 2 (GL (Fin 3) (ZMod 2)) := hTp.toSylow (by rw [hTidx]; decide)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL (Fin 3) (ZMod 2)) PT PH
  have hmem : ∀ t ∈ sylowT, g * t * g⁻¹ ∈ H := by
    intro t ht
    have h1 : MulAut.conj g t ∈ MulAut.conj g • (PT : Subgroup (GL (Fin 3) (ZMod 2))) :=
      Subgroup.smul_mem_pointwise_smul t (MulAut.conj g) _ ht
    rw [← Sylow.coe_subgroup_smul, hg] at h1
    exact h1
  have ha : unitriGL 1 0 0 ∈ sylowT := ⟨1, 0, 0, rfl⟩
  have hb : unitriGL 0 0 1 ∈ sylowT := ⟨0, 0, 1, rfl⟩
  have hab := hcon _ (hmem _ ha) _ (hmem _ hb)
  apply unitriGL_mul_ne
  have h3 : g * (unitriGL 1 0 0 * unitriGL 0 0 1) * g⁻¹ =
      g * (unitriGL 0 0 1 * unitriGL 1 0 0) * g⁻¹ :=
    calc g * (unitriGL 1 0 0 * unitriGL 0 0 1) * g⁻¹
        = g * unitriGL 1 0 0 * g⁻¹ * (g * unitriGL 0 0 1 * g⁻¹) := by group
      _ = g * unitriGL 0 0 1 * g⁻¹ * (g * unitriGL 1 0 0 * g⁻¹) := hab
      _ = g * (unitriGL 0 0 1 * unitriGL 1 0 0) * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h3)

theorem card_le_eight_mul_card_ker {X : Type*} [Group X] [Finite X] (hX : IsPGroup 2 X)
    (ψ : X →* GL (Fin 3) (ZMod 2)) : Nat.card X ≤ 8 * Nat.card ψ.ker := by
  have hrange : IsPGroup 2 ψ.range := hX.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  calc Nat.card X = Nat.card ψ.ker * Nat.card ψ.range := (Subgroup.card_ker_mul_card_range ψ).symm
    _ ≤ Nat.card ψ.ker * 8 := Nat.mul_le_mul_left _ (card_le_eight_of_isPGroup hrange)
    _ = 8 * Nat.card ψ.ker := mul_comm _ _

theorem exists_not_commute_of_card_eq {X : Type*} [Group X] [Finite X] (hX : IsPGroup 2 X)
    (ψ : X →* GL (Fin 3) (ZMod 2)) (h8 : Nat.card X = 8 * Nat.card ψ.ker) :
    ∃ x y : X, ψ x * ψ y ≠ ψ y * ψ x := by
  have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
  have hrange : Nat.card ψ.range = 8 := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [Subgroup.card_ker_mul_card_range, h8, mul_comm]
  obtain ⟨a, ⟨x, rfl⟩, b, ⟨y, rfl⟩, hab⟩ := exists_not_commute_of_card_eq_eight
    (hX.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective) hrange
  exact ⟨x, y, hab⟩

section Main

variable {S : Type} [Group S]

theorem le_normalizer_of_mul_mul_inv_mem {A X : Subgroup S}
    (hXA : ∀ x ∈ X, ∀ a ∈ A, x * a * x⁻¹ ∈ A) : X ≤ normalizer (A : Set S) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro h
  refine ⟨hXA x hx h, fun hh => ?_⟩
  have h' := hXA x⁻¹ (X.inv_mem hx) _ hh
  simpa [mul_assoc] using h'

theorem card_ker_eq_card_inf {A X : Subgroup S} (ψ : X →* GL (Fin 3) (ZMod 2))
    (hψ : ∀ x : X, ψ x = 1 ↔ (x : S) ∈ centralizer (A : Set S)) :
    Nat.card ψ.ker = Nat.card ↥(X ⊓ centralizer (A : Set S)) :=
  Nat.card_congr
    { toFun := fun x => ⟨(x.1 : S), x.1.2, (hψ x.1).1 x.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, (hψ ⟨y.1, y.2.1⟩).2 y.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

variable [Finite S]

theorem exists_hom_GL3F2 {A X : Subgroup S}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hA8 : Nat.card A = 8) (hXA : ∀ x ∈ X, ∀ a ∈ A, x * a * x⁻¹ ∈ A) :
    ∃ ψ : X →* GL (Fin 3) (ZMod 2), ∀ x : X, ψ x = 1 ↔ (x : S) ∈ centralizer (A : Set S) := by
  have hcomm : ∀ a b : A, a * b = b * a := fun a b => Subtype.ext (hAc a a.2 b b.2)
  have hpow : ∀ a : A, a ^ 2 = 1 := fun a => Subtype.ext (by simpa using hA2 a a.2)
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm hpow
    (n := 3) (by rw [hA8]; norm_num)
  have hXN := le_normalizer_of_mul_mul_inv_mem hXA
  let ρ : X →* MulAut A := A.normalizerMonoidHom.comp (Subgroup.inclusion hXN)
  let Φ : MulAut A ≃* GL (Fin 3) (ZMod 2) := CFSG.SectionRank.Ccomm.elemAutEquivGL e
  refine ⟨(Φ : MulAut A →* GL (Fin 3) (ZMod 2)).comp ρ, fun x => ?_⟩
  change Φ (ρ x) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, ← MonoidHom.comap_ker, Subgroup.mem_comap,
    normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
  rfl

theorem card_le_eight_mul_card_inf_centralizer {A X : Subgroup S}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hA8 : Nat.card A = 8) (hX : IsPGroup 2 X) (hXA : ∀ x ∈ X, ∀ a ∈ A, x * a * x⁻¹ ∈ A) :
    Nat.card X ≤ 8 * Nat.card ↥(X ⊓ Subgroup.centralizer (A : Set S)) := by
  obtain ⟨ψ, hψ⟩ := exists_hom_GL3F2 hAc hA2 hA8 hXA
  rw [← card_ker_eq_card_inf ψ hψ]
  exact card_le_eight_mul_card_ker hX ψ

theorem exists_commutator_not_mem_centralizer {A X : Subgroup S}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hA8 : Nat.card A = 8) (hX : IsPGroup 2 X) (hXA : ∀ x ∈ X, ∀ a ∈ A, x * a * x⁻¹ ∈ A)
    (h8 : Nat.card X = 8 * Nat.card ↥(X ⊓ Subgroup.centralizer (A : Set S))) :
    ∃ x ∈ X, ∃ y ∈ X, ⁅x, y⁆ ∉ Subgroup.centralizer (A : Set S) := by
  obtain ⟨ψ, hψ⟩ := exists_hom_GL3F2 hAc hA2 hA8 hXA
  rw [← card_ker_eq_card_inf ψ hψ] at h8
  obtain ⟨x, y, hxy⟩ := exists_not_commute_of_card_eq hX ψ h8
  refine ⟨x, x.2, y, y.2, fun hc => hxy ?_⟩
  have h1 : ψ ⁅x, y⁆ = 1 := (hψ ⁅x, y⁆).2 hc
  rw [map_commutatorElement] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

end Main

end CFSG.OddStandard.Harada75
