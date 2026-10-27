module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDH8

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.SD

open CFSG Subgroup Equiv
open CFSG.ComponentClassification.HSFLit

theorem mem_R8_or_mul_k8_mem_R8 {σ : Perm (ZMod 8)} (hσ : σ ∈ H8) (h : σ * k8 = k8 * σ) :
    σ ∈ R8 ∨ σ * k8 ∈ R8 := by
  obtain ⟨u, b, rfl⟩ := hσ
  revert u b
  decide

theorem mem_S16_or_mul_k8_mem_S16 {σ : Perm (ZMod 8)} (hσ : σ ∈ H8) :
    σ ∈ S16 ∨ σ * k8 ∈ S16 := by
  obtain ⟨u, b, rfl⟩ := hσ
  revert u b
  decide

theorem eq_H8_of_S16_le_of_k8_mem {K : Subgroup (Perm (ZMod 8))} (hK : K ≤ H8) (hS : S16 ≤ K)
    (hk : k8 ∈ K) : K = H8 := by
  refine le_antisymm hK fun σ hσ => ?_
  rcases mem_S16_or_mul_k8_mem_S16 hσ with h | h
  · exact hS h
  · have h1 : σ * k8 * k8 ∈ K := K.mul_mem (hS h) hk
    have h2 : k8 * k8 = 1 := by rw [← pow_two]; exact k8_sq
    rwa [mul_assoc, h2, mul_one] at h1

theorem commute_z8_mul_k8_iff {σ : Perm (ZMod 8)} (hσ : σ ∈ H8) :
    σ * (z8 * k8) = (z8 * k8) * σ ↔ σ * k8 = k8 * σ := by
  obtain ⟨u, b, rfl⟩ := hσ
  have h := z8_comm_aff8' u b
  rw [← mul_assoc, h, mul_assoc, mul_assoc, mul_right_inj]

theorem card_H8_inf_centralizer_k8 :
    Nat.card ↥(H8 ⊓ centralizer ({k8} : Set (Perm (ZMod 8)))) = 16 := by
  have hbij : Function.Bijective
      (fun q : {p : (ZMod 8)ˣ × ZMod 8 // aff8 p.1 p.2 * k8 = k8 * aff8 p.1 p.2} =>
        (⟨aff8 q.1.1 q.1.2, aff8_mem_H8 _ _, mem_centralizer_singleton_iff.mpr q.2⟩ :
          ↥(H8 ⊓ centralizer ({k8} : Set (Perm (ZMod 8)))))) := by
    refine ⟨fun q q' h => ?_, fun ⟨g, hg, hgc⟩ => ?_⟩
    · have h' := aff8_injective (congrArg Subtype.val h)
      exact Subtype.ext (Prod.ext h'.1 h'.2)
    · obtain ⟨u, b, rfl⟩ := hg
      exact ⟨⟨(u, b), mem_centralizer_singleton_iff.mp hgc⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card]
  decide

theorem aff8_u5_one_pow_six : aff8 u5 1 ^ 6 = x8 := by decide

end CFSG.OddStandard.SmallF3.L33.KD.SD
