module

public import CFSG.ClassicalInvolution.Q3.E64Ker.Model

public section

namespace CFSG.ClassicalInvolution.Q3.E64Ker

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.E64Data

private theorem mc_mem_aeSub {v : Fin 7 → ZMod 2} {σ : Equiv.Perm (Fin 7)}
    (hv : v ∈ evenFin ()) (hσ : σ ∈ l32Fin ()) : (⟨v, σ⟩ : Wr 7) ∈ aeSub 7 := by
  simp only [evenFin, l32Fin, Finset.mem_filter, Finset.mem_univ, true_and] at hv hσ
  exact mem_aeSub.2 ⟨hv, hσ.2⟩

private theorem mc_mem_aeSubOver {v : Fin 7 → ZMod 2} {σ : Equiv.Perm (Fin 7)}
    (hv : v ∈ evenFin ()) (hσ : σ ∈ l32Fin ()) : (⟨v, σ⟩ : Wr 7) ∈ aeSubOver l32 := by
  have hσL : σ ∈ l32 := by
    simp only [l32Fin, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    exact hσ.1
  exact Subgroup.mem_inf.2 ⟨mc_mem_aeSub hv hσ, Subgroup.mem_comap.2 hσL⟩

private theorem mc_mem {v : Fin 7 → ZMod 2} {σ : Equiv.Perm (Fin 7)}
    (hv : v ∈ evenFin ()) (hσ : σ ∈ l32Fin ()) : mkQ 7 (⟨v, σ⟩ : Wr 7) ∈ e64Sub :=
  Subgroup.mem_map_of_mem (mkQ 7) (mc_mem_aeSubOver hv hσ)

private theorem mc_inj :
    Function.Injective (fun p : ↥(evenFin ()) × ↥(l32Fin ()) =>
      (⟨mkQ 7 (⟨p.1.1, p.2.1⟩ : Wr 7), mc_mem p.1.2 p.2.2⟩ : ↥e64Sub)) := by
  rintro ⟨⟨v, hv⟩, ⟨σ, hσ⟩⟩ ⟨⟨w, hw⟩, ⟨τ, hτ⟩⟩ h
  have h' : mkQ 7 (⟨v, σ⟩ : Wr 7) = mkQ 7 (⟨w, τ⟩ : Wr 7) := congrArg Subtype.val h
  have e : (⟨v, σ⟩ : Wr 7) = ⟨w, τ⟩ :=
    mkQ7_inj (mc_mem_aeSub hv hσ) (mc_mem_aeSub hw hτ) h'
  have hvw : v = w := congrArg Wr.vec e
  have hστ : σ = τ := congrArg Wr.perm e
  subst hvw hστ
  rfl

theorem le_card_e64Sub : 10752 ≤ Nat.card e64Sub := by
  obtain ⟨-, -, -, -, -, -, h168, h64⟩ := model_check
  have hcard : Nat.card (↥(evenFin ()) × ↥(l32Fin ())) = 10752 := by
    rw [Nat.card_prod, Nat.card_eq_finsetCard, Nat.card_eq_finsetCard, h64, h168]
  exact hcard.symm.le.trans (Nat.card_le_card_of_injective _ mc_inj)

end CFSG.ClassicalInvolution.Q3.E64Ker
