module

public import Certificates.Data.Kernel.PermCent.ForceCV
public import CFSG.Certificates.Kernel.PermCent.CVSound
public import CFSG.Certificates.Kernel.Census.CatFacts.PkWordSound

public section

namespace CFSG.Certificates.Kernel.PkCV

open CFSG.Certificates.Kernel.PkEnum

variable {n : Nat}

theorem forceC_eq {β : Sort _} (a : CV n) (k : CV n → β) : forceC a k = k a := by
  unfold forceC
  rw [forceD_eq]

theorem forceCL_eq {β : Sort _} : ∀ (l : List (CV n)) (k : List (CV n) → β), forceCL l k = k l
  | [], _ => rfl
  | a :: l, k => by
    rw [forceCL, forceC_eq, forceCL_eq l]

theorem memC_val (a : CV n) (L : List (CV n)) : memC a.1 L = decide (a ∈ L) := by
  rw [Bool.eq_iff_iff, memC, List.any_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨c, hc, h⟩
    rw [Nat.beq_eq] at h
    rwa [Subtype.ext h]
  · exact fun h => ⟨a, h, Nat.beq_refl a.1⟩

variable [Small n]

theorem groupF_eq (L : List (CV n)) : groupF L = (decide L.Nodup &&
    (L.all fun a => L.all fun b => decide (a * b ∈ L)) && L.all fun a => decide (a⁻¹ ∈ L)) := by
  unfold groupF
  rw [forceCL_eq]
  simp only [forceD_eq, memC_val]

theorem groupF_perm (M : List (Equiv.Perm (Fin n))) (h : groupF (M.map cOf) = true) :
    M.Nodup ∧ (M.all fun a => M.all fun b => decide (a * b ∈ M)) = true ∧
      (M.all fun a => decide (a⁻¹ ∈ M)) = true := by
  rw [groupF_eq, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hM : (M.map cOf).map ev = M := by simp [List.map_map, Function.comp_def, ev_cOf]
  rw [← hM]
  refine ⟨(nodup_map_ev _).2 h1, ?_, ?_⟩
  · simpa only [List.all_map, Function.comp_def, ev_mul', decide_mem_map_ev] using h2
  · simpa only [List.all_map, Function.comp_def, ev_inv', decide_mem_map_ev] using h3

end CFSG.Certificates.Kernel.PkCV

end
