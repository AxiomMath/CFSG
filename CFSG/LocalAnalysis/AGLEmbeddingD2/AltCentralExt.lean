module

import CFSG.LocalAnalysis.AGLEmbeddingD2.AltThreeRank
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open
open scoped commutatorElement

namespace AltCentralExt

theorem commutatorElement_mul_of_mem_center {J : Type*} [Group J] {x y z : J}
    (hz : z ∈ Subgroup.center J) : ⁅x * z, y⁆ = ⁅x, y⁆ := by
  have hc : z * y * z⁻¹ = y := by
    rw [← Subgroup.mem_center_iff.1 hz y, mul_inv_cancel_right]
  calc ⁅x * z, y⁆ = x * (z * y * z⁻¹) * x⁻¹ * y⁻¹ := by simp [commutatorElement_def, mul_assoc]
    _ = ⁅x, y⁆ := by rw [hc]; rfl

theorem commutatorElement_eq_of_map_eq {J A : Type*} [Group J] [Group A] (ψ : J →* A)
    (hker : ψ.ker ≤ Subgroup.center J) {x x' y y' : J} (hx : ψ x = ψ x') (hy : ψ y = ψ y') :
    ⁅x, y⁆ = ⁅x', y'⁆ := by
  obtain ⟨z₁, hz₁, rfl⟩ : ∃ z ∈ Subgroup.center J, x' = x * z :=
    ⟨x⁻¹ * x', hker (by simp [MonoidHom.mem_ker, hx]), by simp⟩
  obtain ⟨z₂, hz₂, rfl⟩ : ∃ z ∈ Subgroup.center J, y' = y * z :=
    ⟨y⁻¹ * y', hker (by simp [MonoidHom.mem_ker, hy]), by simp⟩
  have h2 : ⁅x, y * z₂⁆ = ⁅x, y⁆ := by
    rw [← commutatorElement_inv, commutatorElement_mul_of_mem_center hz₂,
      commutatorElement_inv]
  rw [commutatorElement_mul_of_mem_center hz₁, h2]

theorem commute_of_inverted {J A : Type*} [Group J] [Group A] (ψ : J →* A)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center J) (h3 : IsPGroup 3 ψ.ker)
    {u v : J} {g : A} (hu : g * ψ u * g⁻¹ = ψ u) (hv : g * ψ v * g⁻¹ = (ψ v)⁻¹)
    (huv : ψ u * ψ v = ψ v * ψ u) : u * v = v * u := by
  obtain ⟨w, rfl⟩ := hψ g
  have hcker : ⁅u, v⁆ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 huv
  have hcc : ⁅u, v⁆ ∈ Subgroup.center J := hker hcker
  have h1 : ⁅w * u * w⁻¹, w * v * w⁻¹⁆ = ⁅u, v⁆ := by
    rw [← conjugate_commutatorElement, Subgroup.mem_center_iff.1 hcc w, mul_inv_cancel_right]
  have h2 : ⁅w * u * w⁻¹, w * v * w⁻¹⁆ = ⁅u, v⁻¹⁆ :=
    commutatorElement_eq_of_map_eq ψ hker (by rw [map_mul, map_mul, map_inv]; exact hu)
      (by rw [map_mul, map_mul, map_inv, hv, map_inv])
  have h3' : ⁅u, v⁻¹⁆ = ⁅u, v⁆⁻¹ := by
    rw [commutatorElement_inv_right, ← commutatorElement_inv,
      Subgroup.mem_center_iff.1 (inv_mem hcc) v⁻¹, inv_mul_cancel_right]
  have hsq : ⁅u, v⁆ ^ 2 = 1 := by
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.2 (h1.symm.trans (h2.trans h3'))
  obtain ⟨k, hk⟩ := h3 ⟨_, hcker⟩
  have hpow : ⁅u, v⁆ ^ 3 ^ k = 1 := congrArg Subtype.val hk
  have hone : ⁅u, v⁆ = 1 :=
    (pow_eq_one_iff_of_coprime (Nat.Coprime.pow_right k (by norm_num))).1 ⟨hsq, hpow⟩
  exact commutatorElement_eq_one_iff_mul_comm.1 hone

theorem le_pRank_of_cube_ker {J A : Type*} [Group J] [Finite J] [Group A] {p : ℕ} [Fact p.Prime]
    (ψ : J →* A) (C : Subgroup J) [IsMulCommutative C] (hC : ∀ c ∈ C, ψ c ^ p = 1) {k : ℕ}
    (hcard : p ^ k ≤ Nat.card (ψ.comp C.subtype).range) : k ≤ pRank p (⊤ : Subgroup J) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  let φ : C →* C :=
    { toFun := fun x => x ^ p
      map_one' := one_pow p
      map_mul' := fun x y => Commute.mul_pow (mul_comm' x y) p }
  let ψC : C →* A := ψ.comp C.subtype
  have hrange : φ.range ≤ ψC.ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker]
    simpa [φ, ψC] using hC x x.2
  have h1 := Subgroup.card_ker_mul_card_range φ
  have h2 := Subgroup.card_ker_mul_card_range ψC
  have h3 : Nat.card φ.range ≤ Nat.card ψC.ker := Subgroup.card_le_of_le hrange
  have h4 : Nat.card ψC.range ≤ Nat.card φ.ker := by
    refine Nat.le_of_mul_le_mul_left (c := Nat.card ψC.ker) ?_ (Nat.card_pos (α := ψC.ker))
    calc Nat.card ψC.ker * Nat.card ψC.range = Nat.card C := h2
      _ = Nat.card φ.ker * Nat.card φ.range := h1.symm
      _ ≤ Nat.card φ.ker * Nat.card ψC.ker := Nat.mul_le_mul_left _ h3
      _ = Nat.card ψC.ker * Nat.card φ.ker := Nat.mul_comm _ _
  have hpow : ∀ x : φ.ker, x ^ p = 1 := fun x => Subtype.ext (MonoidHom.mem_ker.1 x.2)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 (fun x : φ.ker => ⟨1, by simpa using hpow x⟩ :
    IsPGroup p φ.ker)
  refine ((Nat.pow_le_pow_iff_right hp1).1 (hm ▸ hcard.trans h4)).trans ?_
  exact SectionRank.le_pRank_of_injective hp1 (fun a b => Subtype.ext (mul_comm' a.1 b.1)) hpow hm
    (C.subtype.comp φ.ker.subtype) (Subtype.val_injective.comp Subtype.val_injective) le_top

theorem exists_injective_alt_eight {n : ℕ} (hn : 8 ≤ n) :
    ∃ f : alternatingGroup (Fin 8) →* alternatingGroup (Fin n), Function.Injective f := by
  let ι : Fin 8 ↪ Fin n := Fin.castLEEmb hn
  let φ : alternatingGroup (Fin 8) →* Equiv.Perm (Fin n) :=
    (Equiv.Perm.viaEmbeddingHom ι).comp (alternatingGroup (Fin 8)).subtype
  have hφ : Function.Injective φ :=
    (Equiv.Perm.viaEmbeddingHom_injective ι).comp Subtype.val_injective
  refine ⟨φ.codRestrict (alternatingGroup (Fin n)) fun x => ?_,
    fun x y h => hφ (congrArg Subtype.val h)⟩
  change Equiv.Perm.sign (Equiv.Perm.viaEmbeddingHom ι x.1) = 1
  rw [AltThreeRank.sign_viaEmbeddingHom, Equiv.Perm.mem_alternatingGroup.1 x.2]

end AltCentralExt

end CFSG.AGLEmbeddingD2
