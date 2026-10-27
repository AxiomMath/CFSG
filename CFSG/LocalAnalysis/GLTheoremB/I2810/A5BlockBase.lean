module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
import CFSG.LocalAnalysis.GLTheoremB.I2810.BlocksChief
import CFSG.LocalAnalysis.GLTheoremB.I2810.A5BlockInd

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.A5Base

section Alt

theorem commutator_alt5 : commutator ↥(alternatingGroup (Fin 5)) = ⊤ :=
  commutator_alternatingGroup_eq_top (α := Fin 5) (by simp)

end Alt

section Pure

theorem commutatorElement_mul_central' {Y : Type*} [Group Y] {a b z w : Y}
    (hz : z ∈ Subgroup.center Y) (hw : w ∈ Subgroup.center Y) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz' : ∀ x : Y, z * x * z⁻¹ = x := fun x => by
    rw [← Subgroup.mem_center_iff.1 hz x, mul_inv_cancel_right]
  have hw' : ∀ x : Y, w * x * w⁻¹ = x := fun x => by
    rw [← Subgroup.mem_center_iff.1 hw x, mul_inv_cancel_right]
  calc ⁅a * z, b * w⁆ = a * (z * (b * w) * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by rw [hz']; group
    _ = ⁅a, b⁆ := by rw [hw', commutatorElement_def]

theorem eq_top_of_sup_center {G : Type*} [Group G] (hG : commutator G = ⊤) (H : Subgroup G)
    (h : ∀ g : G, ∃ a ∈ H, ∃ z ∈ Subgroup.center G, g = a * z) : H = ⊤ := by
  rw [eq_top_iff, ← hG, _root_.commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  obtain ⟨a₁, ha₁, z₁, hz₁, rfl⟩ := h g₁
  obtain ⟨a₂, ha₂, z₂, hz₂, rfl⟩ := h g₂
  rw [commutatorElement_mul_central' hz₁ hz₂]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha₁ ha₂) (H.inv_mem ha₁)) (H.inv_mem ha₂)

end Pure

section Bar

variable {X : Type} [Group X] {W K : Subgroup X} [W.Normal] {n : ℕ}

@[expose] noncomputable def piBar
    (e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin n))) :
    ↥(bar W K) →* ↥(alternatingGroup (Fin n)) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥(bar W K)))

theorem toBar_pow_two_pow {z : ↥K} {m : ℕ} (hz : (z : X) ^ (2 ^ m) = 1) :
    toBar W K z ^ (2 ^ m) = 1 := by
  have h1 : z ^ (2 ^ m) = 1 := Subtype.ext (by simpa using hz)
  rw [← map_pow, h1, map_one]

theorem pow_two_pow_add {G : Type*} [Group G] {a : G} {m : ℕ} (h : a ^ (2 ^ m) = 1) (n : ℕ) :
    a ^ (2 ^ (m + n)) = 1 := by
  rw [pow_add, pow_mul, h, one_pow]

theorem piOf_apply
    (e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin n))) (k : ↥K) :
    piOf e k = piBar e (toBar W K k) := rfl

theorem piBar_surjective
    (e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin n))) :
    Function.Surjective (piBar e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem piBar_eq_one_iff
    (e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin n)))
    (a : ↥(bar W K)) : piBar e a = 1 ↔ a ∈ Subgroup.center ↥(bar W K) := by
  simp only [piBar, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

end Bar

section Setting

variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal] {n : ℕ}

theorem piOf_eq_one_iff
    (e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin n))) (k : ↥K) :
    piOf e k = 1 ↔ (k : X) ∈ zPre W K :=
  (BlocksChief.piOf_props_aux e).2 k

theorem piOf_eq_one_of_mem {e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin n))}
    {k : ↥K} (hk : (k : X) ∈ W) : piOf e k = 1 := by
  rw [piOf_apply, (BlocksChief.toBar_eq_one_iff k).2 hk, map_one]

theorem perfect_bar (h : Setup28 W K S) : commutator ↥(bar W K) = ⊤ := by
  have hK : (⁅(⊤ : Subgroup ↥K), ⊤⁆ : Subgroup ↥K) = ⊤ := by
    rw [← commutator_def]; exact A5Ind.commutator_K h
  have h1 := Subgroup.map_commutator (⊤ : Subgroup ↥K) ⊤ (toBar W K)
  rw [hK, Subgroup.map_top_of_surjective _ (BlocksChief.toBar_surjective W K)] at h1
  rw [commutator_def]
  exact h1.symm

theorem central_odd (h : Setup28 W K S) {z : ↥(bar W K)} (hz : z ∈ Subgroup.center ↥(bar W K)) :
    Odd (orderOf z) := by
  have h1 := BlocksChief.centre_odd_aux h
  have h2 : orderOf (⟨z, hz⟩ : ↥(Subgroup.center ↥(bar W K))) ∣
      Nat.card ↥(Subgroup.center ↥(bar W K)) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h2
  exact Odd.of_dvd_nat h1 h2

theorem central_eq_one_of_two_pow (h : Setup28 W K S) {z : ↥(bar W K)}
    (hz : z ∈ Subgroup.center ↥(bar W K)) {m : ℕ} (hzm : z ^ (2 ^ m) = 1) : z = 1 := by
  have h1 : orderOf z ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hzm
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have hodd := central_odd h hz
  rw [hi] at hodd
  have hi0 : i = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (dvd_pow_self 2 hne))
  have h3 : orderOf z = 1 := by rw [hi, hi0, pow_zero]
  exact orderOf_eq_one_iff.1 h3

theorem inf_le_zPre : K ⊓ W ≤ zPre W K := fun w hw =>
  ⟨hw.1, fun k _ => by
    have h1 : ⁅w, k⁆ = w * (k * w⁻¹ * k⁻¹) := by simp only [commutatorElement_def]; group
    rw [h1]
    exact W.mul_mem hw.2 (Subgroup.Normal.conj_mem inferInstance _ (W.inv_mem hw.2) k)⟩

theorem exists_two_pow_of_mem (h : Setup28 W K S) {s : X} (hs : s ∈ S) : ∃ m : ℕ, s ^ (2 ^ m) = 1 := by
  obtain ⟨m, hm⟩ := h.hS ⟨s, hs⟩
  exact ⟨m, by simpa using congrArg Subtype.val hm⟩

end Setting

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.A5Base
