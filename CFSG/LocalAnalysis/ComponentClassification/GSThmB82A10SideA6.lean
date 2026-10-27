module

public import CFSG.LocalAnalysis.AGLEmbedding.AltSix
public import Certificates.Certificate23340
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.ComponentClassification.GSThmB.A10Side

open Equiv Equiv.Perm Subgroup

@[expose] def IsSymSixType {Q : Type*} [Group Q] (e : Q ≃* alternatingGroup (Fin 6))
    (φ : MulAut Q) : Prop :=
  ∃ σ : Perm (Fin 6), MulAut.congr e φ = MulAut.conjNormal σ

theorem pow_45_eq_one_of_odd {v : Perm (Fin 6)} (hv : Odd (orderOf v)) : v ^ 45 = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one]
  have h720 : orderOf v ∣ 45 * 2 ^ 4 := by
    have h := orderOf_dvd_card (x := v)
    rw [Fintype.card_perm, Fintype.card_fin] at h
    exact h
  have hcop : Nat.Coprime (orderOf v) (2 ^ 4) :=
    (Nat.Coprime.pow_left 4 (Nat.coprime_two_left.mpr hv)).symm
  exact hcop.dvd_of_dvd_mul_right h720

theorem conj_injective_six :
    Function.Injective (MulAut.conj : alternatingGroup (Fin 6) →*
      MulAut (alternatingGroup (Fin 6))) := by
  intro u v h
  apply Subtype.ext
  apply CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by norm_num)
  rw [MulAut.conjNormal_val, MulAut.conjNormal_val, h]

theorem eq_bot_of_commute_conjNormal {σ : Perm (Fin 6)}
    (hσ : σ * σ = 1) (R : Subgroup (MulAut (alternatingGroup (Fin 6))))
    (hodd : ∀ ψ ∈ R, Odd (orderOf ψ))
    (hcomm : ∀ ψ ∈ R, ψ * MulAut.conjNormal σ = MulAut.conjNormal σ * ψ)
    (hnorm : ∀ c : alternatingGroup (Fin 6), (c : Perm (Fin 6)) * σ = σ * c →
      ∀ ψ ∈ R, MulAut.conj c * ψ * (MulAut.conj c)⁻¹ ∈ R) : R = ⊥ := by
  rw [eq_bot_iff]
  intro ψ hψ
  rw [mem_bot]
  by_contra hne
  obtain ⟨u, rfl⟩ := CFSG.AGLEmbedding.mem_range_conj_of_odd_orderOf ψ (hodd ψ hψ)
  have hu1 : (u : Perm (Fin 6)) ≠ 1 := by
    intro h
    apply hne
    rw [show u = 1 from Subtype.ext h, map_one]
  have huσ : (u : Perm (Fin 6)) * σ = σ * u := by
    apply CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by norm_num)
    rw [map_mul, map_mul, MulAut.conjNormal_val]
    exact hcomm _ hψ
  have huodd : Odd (orderOf (u : Perm (Fin 6))) := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective _ conj_injective_six u]
    exact hodd _ hψ
  obtain ⟨c, hc, hcσ, hne45⟩ := Certificates.certificate23340 σ u hσ
    (mem_alternatingGroup.mp u.2) hu1 huσ (pow_45_eq_one_of_odd huodd)
  set c' : alternatingGroup (Fin 6) := ⟨c, mem_alternatingGroup.mpr hc⟩ with hc'
  have hmem : (MulAut.conj u)⁻¹ * (MulAut.conj c' * MulAut.conj u * (MulAut.conj c')⁻¹) ∈ R :=
    R.mul_mem (R.inv_mem hψ) (hnorm c' hcσ _ hψ)
  have heq : (MulAut.conj u)⁻¹ * (MulAut.conj c' * MulAut.conj u * (MulAut.conj c')⁻¹) =
      MulAut.conj (u⁻¹ * c' * u * c'⁻¹) := by
    simp only [map_mul, map_inv, mul_assoc]
  rw [heq] at hmem
  have hodd' := hodd _ hmem
  rw [orderOf_injective _ conj_injective_six, ← Subgroup.orderOf_coe] at hodd'
  apply hne45
  have h45 := pow_45_eq_one_of_odd hodd'
  simpa [hc'] using h45

end CFSG.ComponentClassification.GSThmB.A10Side
