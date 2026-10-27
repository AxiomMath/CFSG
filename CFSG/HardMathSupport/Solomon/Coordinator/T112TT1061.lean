module

public import CFSG.HardMathSupport.Solomon.Coordinator.T112TRank
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTables
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.SectionRank.OddCover Matrix

variable {F : Type} [Field F]

theorem three_ne_zero_of_card [Finite F] (h : ¬ 3 ∣ Nat.card F) : (3 : F) ≠ 0 := by
  intro h3
  have := Fintype.ofFinite F
  have hc : ringChar F ∣ 3 := (CharP.cast_eq_zero_iff F (ringChar F) 3).1 (by exact_mod_cast h3)
  have hp : (ringChar F).Prime := by
    have := CharP.char_is_prime_or_zero F (ringChar F)
    rcases this with h | h
    · exact h
    · rw [h] at hc; omega
  have h3' : ringChar F = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hc
  obtain ⟨n, -, hn⟩ := FiniteField.card F (ringChar F)
  apply h
  rw [Nat.card_eq_fintype_card, hn, h3']
  exact dvd_pow_self 3 (PNat.ne_zero n)

theorem det_eq_one_of_mem_statedSU {q : ℕ} {x : GL (Fin 3) F} (hx : x ∈ StatedSU 3 q F) :
    (x : Matrix (Fin 3) (Fin 3) F).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSU hx

theorem pRank_le_two_of_sub {K : Type} [Group K] [Finite K] [Finite F] (h3 : (3 : F) ≠ 0)
    (S : Subgroup (GL (Fin 3) F)) (hS : ∀ g ∈ S, (g : Matrix (Fin 3) (Fin 3) F).det = 1)
    (e : K ≃* ↥S) : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 2 := by
  refine CFSG.SectionRank.pRank_le (by norm_num) ?_
  intro E _ hE
  let f : K →* GL (Fin 3) F := S.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hA := CFSG.SectionRank.isElemAbelian_map hE f
  have hcard : Nat.card (E.map f) = Nat.card E := Subgroup.card_map_of_injective hf
  have := card_le_nine h3 (A := E.map f) ?_ ?_ hA.2
  · rw [hcard] at this; simpa using this
  · rintro _ ⟨y, -, rfl⟩
    exact hS _ (e y).2
  · intro x hx y hy
    exact congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem tables112Types_T10_6_1_holds : ∀ (K : Type) [Group K] [Finite K],
    CFSG.Open.IsQuasisimple K → CFSG.Open.IsKGroup K → IsThreeNine K →
      CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 2 := by
  intro K _ _ _ _ h
  rcases h with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨F, _, _, q, hq, hF, ⟨e⟩⟩
  · refine pRank_le_two_of_sub (three_ne_zero_of_card (by omega)) _
      (fun g hg => det_of_mem_statedSL hg) e
  · refine pRank_le_two_of_sub (three_ne_zero_of_card ?_) _
      (fun g hg => det_eq_one_of_mem_statedSU hg) e
    rw [hq]
    intro hd
    have h3q : 3 ∣ q := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    omega

end CFSG.HardMathSupport.Solomon.Coordinator
