module

public import CFSG.Certificates.Kernel.Misc.PermGH23Sound
public import CFSG.Certificates.Kernel.Misc.PermClosSound
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23Clos
import CFSG.Certificates.Kernel.Misc.PermClosProof

public section

namespace CFSG.KC.Misc.GH23

open Equiv CFSG.KC.Misc.Clos CFSG.OddStandard.SmallF3.HarrisU33.GH23Data
  CFSG.OddStandard.SmallF3.HarrisU33.Outside

theorem gh23_enc : ClosEnc gh23Code mul8 one8 where
  enc_one := by rw [one8_eq, gh23_oneC]
  enc_mul a b := by rw [mul8_eq, gh23_mulC_code]
  inj := gh23_code_injective

noncomputable def dec8 (c : ℕ) : Perm (Fin 8) :=
  if h : ∃ σ : Perm (Fin 8), gh23Code σ = c then h.choose else 1

theorem code_dec8 {c : ℕ} (h : validC c = true) : gh23Code (dec8 c) = c := by
  have h' := gh23_exists_of_validC h
  rw [dec8, dif_pos h']
  exact h'.choose_spec

theorem gh23_clos {nG N : ℕ} {G E PA SG CT : ℕ → ℕ} {cs : List ℕ}
    (hcs : cs = (List.range nG).map G) (hv : cs.all validC = true) (hN : 0 < N)
    (ht : ∀ k < N, treeAt mul8 one8 G nG E PA k = true)
    (hs : ∀ i < N, sortAt N E SG i = true)
    (hc : ∀ k < N, closedAt mul8 G nG N E CT k = true) :
    Nat.card (gh23Sub cs) = N ∧ ExactList gh23Code (gh23Sub cs) N E := by
  subst hcs
  have hvG : ∀ j < nG, validC (G j) = true := fun j hj =>
    List.all_eq_true.mp hv (G j) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  set gens := ((List.range nG).map G).map dec8 with hgens
  have hl : gens.length = nG := by simp [gens]
  have hG : ∀ j < gens.length, G j = gh23Code (gens.getD j 1) := by
    intro j hj
    rw [hl] at hj
    have : gens.getD j 1 = dec8 (G j) := by
      rw [List.getD_eq_getElem?_getD]
      simp [gens, hj]
    rw [this, code_dec8 (hvG j hj)]
  have hcl : Subgroup.closure {g | g ∈ gens} = gh23Sub ((List.range nG).map G) := by
    unfold gh23Sub
    congr 1
    ext g
    simp only [Set.mem_setOf_eq, gens, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨c, ⟨j, hj, rfl⟩, rfl⟩
      exact ⟨j, hj, (code_dec8 (hvG j hj)).symm⟩
    · rintro ⟨j, hj, hgj⟩
      exact ⟨G j, ⟨j, hj, rfl⟩, gh23_code_injective (by rw [code_dec8 (hvG j hj), hgj])⟩
  rw [← hl] at ht hc
  have h := clos_card_proved gh23_enc gens hG hN ht hs
  obtain ⟨hcard, hall⟩ := h.2.2 hc
  rw [hcl] at h hcard hall
  exact ⟨hcard, h.1, hall, sort_distinct_proved hs⟩

end CFSG.KC.Misc.GH23

end
