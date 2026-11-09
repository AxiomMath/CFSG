module

public import CFSG.Permutation.FinPackSignCount
public import CFSG.Permutation.FinPackDec
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.GorensteinWalter.A7NormK

open Equiv Equiv.Perm Finset CFSG.Permutation.FinPack

@[expose] noncomputable def conj7 (c x : ℕ) : ℕ := mulK 7 (mulK 7 c x) (invCK 7 c)

@[expose] noncomputable def normB (A A2 c : ℕ) : Bool :=
  Nat.beq (conj7 c A) A || Nat.beq (conj7 c A) A2

theorem check_norm456 :
    Nat.beq (cntK 7 (fun c => normB 73740816 88486416 c && evenK 7 c) 7 0 0 0) 72 = true := by
  decide +kernel

theorem card_norm_of (a : alternatingGroup (Fin 7)) (fT : Fintype (alternatingGroup (Fin 7)))
    (dP : DecidablePred fun g : alternatingGroup (Fin 7) => g * a * g⁻¹ = a ∨ g * a * g⁻¹ = a ^ 2)
    {A A2 N : ℕ} (hA : enc (a : Perm (Fin 7)) = A)
    (hA2 : enc ((a ^ 2 : alternatingGroup (Fin 7)) : Perm (Fin 7)) = A2)
    (h : Nat.beq (cntK 7 (fun c => normB A A2 c && evenK 7 c) 7 0 0 0) N = true) :
    (@Finset.filter _ (fun g : alternatingGroup (Fin 7) => g * a * g⁻¹ = a ∨ g * a * g⁻¹ = a ^ 2)
      dP (@Finset.univ _ fT)).card = N := by
  rw [← Nat.eq_of_beq_eq_true h, ← card_sign_filter_eq_cntK (by norm_num)]
  have hP : ∀ g : alternatingGroup (Fin 7),
      (g * a * g⁻¹ = a ∨ g * a * g⁻¹ = a ^ 2) ↔ normB A A2 (enc (g : Perm (Fin 7))) = true := by
    intro g
    have e : conj7 (enc (g : Perm (Fin 7))) A = enc ((g * a * g⁻¹ : alternatingGroup (Fin 7)) :
        Perm (Fin 7)) := by
      rw [conj7, ← hA, invCK_enc (by norm_num), mulK_enc (by norm_num), mulK_enc (by norm_num)]
      rfl
    rw [normB, e, Bool.or_eq_true, ← hA, ← hA2, beq_enc_iff (by norm_num),
      beq_enc_iff (by norm_num), Subtype.ext_iff, Subtype.ext_iff]
  refine Finset.card_bij (fun g _ => (g : Perm (Fin 7))) ?_ ?_ ?_
  · intro g hg
    rw [Finset.mem_filter] at hg ⊢
    exact ⟨Finset.mem_univ _, Perm.mem_alternatingGroup.1 g.2, (hP g).1 hg.2⟩
  · intro x _ y _ hxy
    exact Subtype.ext hxy
  · intro σ hσ
    rw [Finset.mem_filter] at hσ
    exact ⟨⟨σ, Perm.mem_alternatingGroup.2 hσ.2.1⟩,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, (hP _).2 hσ.2.2⟩, rfl⟩

end CFSG.GorensteinWalter.A7NormK
