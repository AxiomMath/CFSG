module

public import CFSG.ClassicalInvolution.Q3.E29Ker.Model

public section

namespace CFSG.ClassicalInvolution.Q3.E29Ker

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.E29Data

private theorem mc_mem_aeSubOver {v : Fin 8 → ZMod 2} {σ : Equiv.Perm (Fin 8)}
    (hv : v ∈ evenFin0 ()) (hσ : σ ∈ aglFin ()) : (⟨v, σ⟩ : Wr 8) ∈ aeSubOver agl32 := by
  simp only [evenFin0, aglFin, Finset.mem_filter, Finset.mem_univ, true_and] at hv hσ
  have hσA : σ ∈ agl32 := hσ.1
  exact Subgroup.mem_inf.2 ⟨mem_aeSub.2 ⟨hv.1, hσ.2⟩, Subgroup.mem_comap.2 hσA⟩

private theorem mc_mem {v : Fin 8 → ZMod 2} {σ : Equiv.Perm (Fin 8)}
    (hv : v ∈ evenFin0 ()) (hσ : σ ∈ aglFin ()) : mkQ 8 (⟨v, σ⟩ : Wr 8) ∈ e29Sub :=
  Subgroup.mem_map_of_mem (mkQ 8) (mc_mem_aeSubOver hv hσ)

private theorem mc_vec_zero {v w : Fin 8 → ZMod 2} {σ τ : Equiv.Perm (Fin 8)}
    (h : (⟨v, σ⟩ : Wr 8)⁻¹ * ⟨w, τ⟩ = Wr.allOnes 8) : v 0 + w 0 = 1 := by
  have hx : ((⟨v, σ⟩ : Wr 8)⁻¹ * ⟨w, τ⟩).vec (σ.symm 0) = (Wr.allOnes 8).vec (σ.symm 0) := by
    rw [h]
  simpa [Wr.mul_vec, Wr.inv_vec, Wr.inv_perm, Wr.allOnes, Equiv.Perm.inv_def] using hx

private theorem mc_inj :
    Function.Injective (fun p : ↥(evenFin0 ()) × ↥(aglFin ()) =>
      (⟨mkQ 8 (⟨p.1.1, p.2.1⟩ : Wr 8), mc_mem p.1.2 p.2.2⟩ : ↥e29Sub)) := by
  rintro ⟨⟨v, hv⟩, ⟨σ, hσ⟩⟩ ⟨⟨w, hw⟩, ⟨τ, hτ⟩⟩ h
  have h' : mkQ 8 (⟨v, σ⟩ : Wr 8) = mkQ 8 (⟨w, τ⟩ : Wr 8) := congrArg Subtype.val h
  rcases mkQ_eq_iff.mp h' with h1 | h1
  · have e : (⟨v, σ⟩ : Wr 8) = ⟨w, τ⟩ := inv_mul_eq_one.mp h1
    have hvw : v = w := congrArg Wr.vec e
    have hστ : σ = τ := congrArg Wr.perm e
    subst hvw hστ
    rfl
  · exfalso
    have h0 := mc_vec_zero h1
    simp only [evenFin0, Finset.mem_filter, Finset.mem_univ, true_and] at hv hw
    rw [hv.2, hw.2] at h0
    exact absurd h0 (by decide)

theorem le_card_e29Sub : 86016 ≤ Nat.card e29Sub := by
  obtain ⟨-, -, -, -, -, -, h1344, h64⟩ := model_check
  have hcard : 86016 ≤ Nat.card (↥(evenFin0 ()) × ↥(aglFin ())) := by
    rw [Nat.card_prod, Nat.card_eq_finsetCard, Nat.card_eq_finsetCard, h64]
    omega
  exact hcard.trans (Nat.card_le_card_of_injective _ mc_inj)

end CFSG.ClassicalInvolution.Q3.E29Ker
