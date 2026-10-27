module

public import CFSG.ClassicalInvolution.QuaternionStructure.Lifting
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition
public import CFSG.GH74.GLS.Bg.TwoGroups.Models
public import CFSG.GH74.GLS.IVK.Lifted.Alt51Idx

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk5An

namespace SL23

open Equiv Equiv.Perm CFSG CFSG.ClassicalInvolution.QuaternionStructure
  CFSG.DisconnectedInvolutionGraph CFSG.DisconnectedInvolutionGraph.Helpers
open scoped MatrixGroups

theorem a4_pow_four : ∀ a : alternatingGroup (Fin 4), a ^ 4 = 1 → a ^ 2 = 1 := by
  decide +kernel

theorem a4_center :
    ∀ a : alternatingGroup (Fin 4), (∀ b : alternatingGroup (Fin 4), b * a = a * b) → a = 1 := by
  decide +kernel

theorem a4_comm_two : ∀ a : alternatingGroup (Fin 4), a ≠ 1 →
    ∃ g : alternatingGroup (Fin 4), g * a * g⁻¹ * a⁻¹ ≠ 1 ∧ (g * a * g⁻¹ * a⁻¹) ^ 2 = 1 := by
  decide +kernel

theorem a4_card : Nat.card (alternatingGroup (Fin 4)) = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

structure Data {S : Type} [Group S] (z : S) (φ : S →* alternatingGroup (Fin 4)) : Prop where
  surj : Function.Surjective φ
  ne_one : z ≠ 1
  sq : z * z = 1
  central : ∀ g : S, g * z = z * g
  φ_z : φ z = 1
  ker : ∀ x : S, φ x = 1 → x = 1 ∨ x = z
  inv : ∀ x : S, x * x = 1 → x = 1 ∨ x = z

namespace Data

variable {S : Type} [Group S] {z : S} {φ : S →* alternatingGroup (Fin 4)} (h : Data z φ)

include h

theorem orderOf_z : orderOf z = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact h.sq) h.ne_one

theorem ker_eq : φ.ker = Subgroup.zpowers z := by
  ext x
  rw [MonoidHom.mem_ker, mem_zpowers_iff_of_orderOf_eq_two h.orderOf_z]
  exact ⟨h.ker x, by rintro (rfl | rfl); exacts [map_one φ, h.φ_z]⟩

theorem natCard : Nat.card S = 24 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ h.surj).toEquiv, a4_card,
    h.ker_eq, Nat.card_zpowers, h.orderOf_z] at h1
  omega

theorem eq_of_orderOf_eq_two {t : S} (ht : orderOf t = 2) : t = z := by
  have : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht, pow_two] at this
  rcases h.inv t this with h1 | h1
  · rw [h1, orderOf_one] at ht
    omega
  · exact h1

theorem center_eq : Subgroup.center S = Subgroup.zpowers z := by
  ext x
  rw [mem_zpowers_iff_of_orderOf_eq_two h.orderOf_z, Subgroup.mem_center_iff]
  constructor
  · intro hx
    have : φ x = 1 := a4_center _ (fun b => by
      obtain ⟨g, rfl⟩ := h.surj b
      rw [← map_mul, ← map_mul, hx g])
    exact h.ker x this
  · rintro (rfl | rfl)
    · intro g
      simp
    · exact h.central

theorem oddCore_eq_bot : CFSG.oddCore S = ⊥ := by
  rw [CFSG.oddCore, sSup_eq_bot]
  rintro M ⟨hM, hodd⟩
  have hord : ∀ x ∈ M, Odd (orderOf x) := fun x hx =>
    hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard M hx)
  have hzM : z ∉ M := fun hz => by
    have h1 := hord z hz
    rw [h.orderOf_z] at h1
    exact absurd h1 (by decide)
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hφx : φ x ≠ 1 := by
    intro h0
    rcases h.ker x h0 with h1 | h1
    · exact hx1 h1
    · exact hzM (h1 ▸ hx)
  obtain ⟨g', hg'1, hg'2⟩ := a4_comm_two (φ x) hφx
  obtain ⟨g, rfl⟩ := h.surj g'
  have hcM : g * x * g⁻¹ * x⁻¹ ∈ M := M.mul_mem (hM.conj_mem x hx g) (M.inv_mem hx)
  have hφc : φ (g * x * g⁻¹ * x⁻¹) = φ g * φ x * (φ g)⁻¹ * (φ x)⁻¹ := by simp
  have hc1 : g * x * g⁻¹ * x⁻¹ ≠ 1 := fun h0 => hg'1 (by rw [← hφc, h0, map_one])
  have hc2 : (g * x * g⁻¹ * x⁻¹) ^ 2 = 1 := by
    have h1 : φ ((g * x * g⁻¹ * x⁻¹) ^ 2) = 1 := by rw [map_pow, hφc]; exact hg'2
    rcases h.ker _ h1 with h2 | h2
    · exact h2
    · exact absurd (h2 ▸ M.pow_mem hcM 2) hzM
  have hc3 : orderOf (g * x * g⁻¹ * x⁻¹) = 2 := orderOf_eq_prime hc2 hc1
  have := hord _ hcM
  rw [hc3] at this
  exact absurd this (by decide)

variable [Finite S]

theorem sylow_equiv (P : Sylow 2 S) :
    Nonempty (↥(P : Subgroup S) ≃* QuaternionGroup (2 ^ (3 - 2))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (P : Subgroup S) = 8 := by
    rw [Sylow.card_eq_multiplicity, h.natCard]
    have : (24 : ℕ).factorization 2 = 3 := by
      rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
        Nat.Prime.factorization_pow Nat.prime_two]
      simp [Nat.factorization_eq_zero_of_not_dvd]
    rw [this]
    norm_num
  have hrank : NoCommutingDistinctInvolutions ↥(P : Subgroup S) := by
    intro u v _
    apply Subtype.ext
    apply Subtype.ext
    have hu : orderOf ((u.1 : ↥(P : Subgroup S)) : S) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact u.2
    have hv : orderOf ((v.1 : ↥(P : Subgroup S)) : S) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact v.2
    rw [h.eq_of_orderOf_eq_two hu, h.eq_of_orderOf_eq_two hv]
  rcases rank_one_two_cyclic_or_quaternion P.isPGroup' hrank with hc | ⟨e, he1, ⟨ε⟩⟩
  · exfalso
    obtain ⟨g, hg⟩ := hc.exists_ofOrder_eq_natCard
    rw [hcard] at hg
    have hg' : orderOf (g : S) = 8 := by rw [Subgroup.orderOf_coe]; exact hg
    have h4 : orderOf ((g : S) ^ 4) = 2 := by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [hg']; norm_num), hg']
    have h4z : (g : S) ^ 4 = z := h.eq_of_orderOf_eq_two h4
    have h1 : φ (g : S) ^ 2 = 1 := by
      apply a4_pow_four
      rw [← map_pow, h4z, h.φ_z]
    have h2 : φ ((g : S) ^ 2) = 1 := by rw [map_pow]; exact h1
    have h5 : (g : S) ^ 4 = 1 := by
      rcases h.ker _ h2 with h3 | h3
      · rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, h3, one_pow]
      · rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, h3, pow_two]
        exact h.sq
    have h6 := orderOf_dvd_of_pow_eq_one h5
    rw [hg'] at h6
    omega
  · have h8 : 4 * 2 ^ e = 8 := by
      have := Nat.card_congr ε.toEquiv
      rw [hcard, Nat.card_eq_fintype_card, QuaternionGroup.card] at this
      omega
    have he : e = 1 := by
      have : 2 ^ e = 2 ^ 1 := by omega
      exact Nat.pow_right_injective (le_refl 2) this
    subst he
    exact ⟨ε.symm⟩

theorem quaternionSetting : QuaternionSetting S z 3 where
  three_le := le_refl _
  orderOf_eq_two := h.orderOf_z
  mem_center := by rw [h.center_eq]; exact Subgroup.mem_zpowers z
  eq_of_orderOf_eq_two := fun _ ht => h.eq_of_orderOf_eq_two ht
  sylow_equiv := h.sylow_equiv
  oddCore_eq_bot := h.oddCore_eq_bot

theorem nonempty_equiv_sl23 : Nonempty (S ≃* SL(2, ZMod 3)) := by
  have hF : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ := h.quaternionSetting
  have : (Subgroup.zpowers z).Normal := hQ.normal_zpowers
  let e1 : (S ⧸ Subgroup.zpowers z) ≃* alternatingGroup (Fin 4) :=
    (QuotientGroup.quotientMulEquivOfEq h.ker_eq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ h.surj)
  let eN : ↥(⊤ : Subgroup (S ⧸ Subgroup.zpowers z)) ≃* CFSG.GorensteinWalter.PSL2 (ZMod 3) :=
    Subgroup.topEquiv.trans (e1.trans CFSG.GorensteinWalter.psl2_three_equiv_alternatingGroup.symm)
  have hchar : ringChar (ZMod 3) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    norm_num
  obtain ⟨eSL⟩ := hQ.exists_mulEquiv_specialLinearGroup hchar ⊤ eN
  exact ⟨(Subgroup.topEquiv.symm.trans
    (MulEquiv.subgroupCongr (Subgroup.comap_top _).symm)).trans eSL⟩

end Data

end SL23

open Equiv Equiv.Perm CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK.Lifted CFSG.Assembly.LowTwoRank

end CFSG.GH74.GLS.IVK.Proofs2.Ivk5An
