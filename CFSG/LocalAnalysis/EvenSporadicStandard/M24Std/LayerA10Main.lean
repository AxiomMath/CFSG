module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerA10Fix
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerA10Perm

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open Equiv Equiv.Perm

theorem not_isLayerInvolutionAut_alt_ten (f : MulAut (alternatingGroup (Fin 10))) :
    ¬ IsLayerInvolutionAut 20160 f := by
  rintro ⟨hf, h⟩
  obtain ⟨σ, hσ2, hσ⟩ := exists_perm_sq_eq_one_of_mulAut_alternatingGroup (Or.inr (by norm_num))
    f hf
  rw [card_fixed_mulAut_alternatingGroup hσ] at h
  obtain ⟨hmem, hodd⟩ := card_alternatingGroup_inf_centralizer_ten hσ2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases h with h | ⟨h1, h2, h3⟩
  · omega
  · have h40 : Nat.card (alternatingGroup (Fin 10) ⊓ centralizer {σ} :
        Subgroup (Perm (Fin 10))) = 40320 := by omega
    obtain ⟨s, hs⟩ := h3 h40
    have hsign : sign σ = 1 := by
      rw [eq_of_mulAut_alternatingGroup_eq_conj (by norm_num) hσ hs]
      exact s.2
    rw [hodd h40] at hsign
    exact absurd hsign (by decide)

theorem not_nonempty_layer_alt10 {X : Type} [Group X] [Finite X] {z : X} {H : Subgroup X}
    (hz : orderOf z = 2) (hH : Nonempty (H ≃* alternatingGroup (Fin 8)))
    (hC : centralizer ({z} : Set X) = H ⊔ zpowers z) (hz' : z ∈ centralizer (H : Set X)) :
    ¬ Nonempty (egaLayer (X ⧸ fusionOddCore X) ≃* alternatingGroup (Fin 10)) :=
  not_nonempty_layer_of_alt8 hz hH hC hz' not_isLayerInvolutionAut_alt_ten

end CFSG.EvenSporadicStandard.M24Std
