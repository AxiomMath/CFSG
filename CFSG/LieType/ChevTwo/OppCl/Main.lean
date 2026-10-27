module

import CFSG.LieType.ChevTwo.OppCl.Toolkit
import CFSG.LieType.ChevTwo.OppCl.SL
import CFSG.LieType.ChevTwo.OppCl.FormsEA
import CFSG.LieType.ChevTwo.OppCl.AutLifts
public import CFSG.LieType.ChevTwo.OppCl.Bridge
public import CFSG.LieType.ChevTwo.OppCl.Small
public import CFSG.LieType.ChevTwo.OppCl.D4
public import CFSG.LieType.ChevTwo.OppCl.G2

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

section FamilyPSL

variable (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]

theorem oppositeFixed_PSL (hn : 2 ≤ n) (hF : 4 ≤ Nat.card F ∨ 3 ≤ n) :
    OppositeFixed (StatedProj (StatedSL n F)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (StatedSL n F) := inferInstance
  refine oppFixed_of_raise (H := StatedSL n F)
    ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F)) (statedProj_kernel_central _)
    (statedProj_kernel_coprime 2 _) (P := fun _ => True) (natRep (StatedSL n F))
    (natRep_injective _) (fun Q => fixFlag (natRep (StatedSL n F)) Q)
    (fun Q _ => normalizer_le_flagStab_fixFlag _ Q) (fun Q _ => le_flagKernel_fixFlag _ Q) ?_
    (fun p hp hp2 => by haveI : Fact p.Prime := ⟨hp⟩; exact raise_SL n F p hp2)
  intro p hp hp2 R hR
  haveI : Fact p.Prime := ⟨hp⟩
  refine autLift_of_induced (fun _ => True) trivial (fun _ _ _ _ => trivial) (fun _ _ => trivial)
    p R hR ?_
  rcases le_or_gt 3 n with h3 | h3
  · exact induced_PSL n F h3 p hp2 R hR
  · obtain rfl : n = 2 := by omega
    exact induced_PSL_two F p hp2 (hF.resolve_right (by omega)) R hR

end FamilyPSL

section FamilyTheorems

variable (F : Type) [Field F] [Finite F] [CharP F 2]

theorem oppositeFixed_PSp (r : ℕ) (hr : 2 ≤ r) (hF : 4 ≤ Nat.card F ∨ 3 ≤ r) :
    OppositeFixed (StatedProj (StatedSp r F)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine oppFixed_of_raise (H := StatedSp r F)
    ((StatedScalars (Fin r ⊕ Fin r) F).subgroupOf (StatedSp r F)) (statedProj_kernel_central _)
    (statedProj_kernel_coprime 2 _) (P := SemiIso (spForm r F)) (natRep (StatedSp r F))
    (natRep_injective _) (fun Q => isoFlag (spForm r F) (natRep (StatedSp r F)) Q)
    (fun Q _ => normalizer_le_flagStab_isoFlag _ _ (isIsometric_natRep_statedSp r F) Q)
    (fun Q hQ => le_flagKernel_isoFlag _ _ 2 (isIsometric_natRep_statedSp r F) Q hQ) ?_
    (fun p hp hp2 => by haveI : Fact p.Prime := ⟨hp⟩; exact raise_Sp F p hp2 r)
  intro p hp hp2 R hR
  haveI : Fact p.Prime := ⟨hp⟩
  refine autLift_of_induced _ (semiIso_one _) (fun _ _ => semiIso_mul _)
    (fun _ => semiIso_inv _) p R hR ?_
  rcases le_or_gt 3 r with h3 | h3
  · exact induced_PSp F p hp2 r h3 R hR
  · obtain rfl : r = 2 := by omega
    exact induced_PSp_two F p hp2 (hF.resolve_right (by omega)) R hR

end FamilyTheorems

section FamilyTheorems2

variable (F : Type) [Field F] [Finite F] [CharP F 2]

theorem oppositeFixed_PSU (f : ℕ) (hK : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (hn : 3 ≤ n)
    (hq : 2 < 2 ^ f ∨ 4 ≤ n) : OppositeFixed (StatedProj (StatedSU n (2 ^ f) F)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine oppFixed_of_raise (H := StatedSU n (2 ^ f) F)
    ((StatedScalars (Fin n) F).subgroupOf (StatedSU n (2 ^ f) F)) (statedProj_kernel_central _)
    (statedProj_kernel_coprime 2 _) (P := SemiIso (unitaryForm 2 f hK n))
    (natRep (StatedSU n (2 ^ f) F)) (natRep_injective _)
    (fun Q => isoFlag (unitaryForm 2 f hK n) (natRep (StatedSU n (2 ^ f) F)) Q)
    (fun Q _ => normalizer_le_flagStab_isoFlag _ _ (isIsometric_natRep_statedSU hK n) Q)
    (fun Q hQ => le_flagKernel_isoFlag _ _ 2 (isIsometric_natRep_statedSU hK n) Q hQ) ?_
    (fun p hp hp2 => by haveI : Fact p.Prime := ⟨hp⟩; exact raise_SU F p hp2 f hK n)
  intro p hp hp2 R hR
  haveI : Fact p.Prime := ⟨hp⟩
  exact autLift_of_induced _ (semiIso_one _) (fun _ _ => semiIso_mul _) (fun _ => semiIso_inv _)
    p R hR (induced_PSU F p hp2 f hK n hn hq R hR)

theorem oppositeFixed_POmegaPlus (n : ℕ) (hn : 5 ≤ n) :
    OppositeFixed (StatedProj (StatedOmega (StatedQuadPlus n F))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : ∀ (h : StatedOmega (StatedQuadPlus n F)) (v : Fin n ⊕ Fin n → F),
      (quadPlusForm n F).Q (natRep (StatedOmega (StatedQuadPlus n F)) h v) =
        (quadPlusForm n F).Q v := fun h v => by
    rw [natRep_apply]
    exact orthGroup_preserves (quadPlusForm n F).Q (statedOmega_le_orthGroup _ h.2) v
  have hstar : NoQuotientReflection (quadPlusForm n F)
      (natRep (StatedOmega (StatedQuadPlus n F))) := fun h Z hZ a ha hQa => by
    simp only [natRep_apply]
    exact not_reflection_on_quotient_of_mem_statedOmega (quadPlusForm n F) h.2 hZ ha hQa
  refine oppFixed_of_raise (H := StatedOmega (StatedQuadPlus n F))
    ((StatedScalars (Fin n ⊕ Fin n) F).subgroupOf (StatedOmega (StatedQuadPlus n F)))
    (statedProj_kernel_central _) (statedProj_kernel_coprime 2 _)
    (P := SemiIsoQ (quadPlusForm n F)) (natRep (StatedOmega (StatedQuadPlus n F)))
    (natRep_injective _)
    (fun Q => singFlag (quadPlusForm n F) (natRep (StatedOmega (StatedQuadPlus n F))) Q)
    (fun Q _ => normalizer_le_flagStab_singFlag hQ Q)
    (fun Q hQ2 => le_flagKernel_singFlag 2 hQ hstar Q hQ2) ?_
    (fun p hp hp2 => by
      haveI : Fact p.Prime := ⟨hp⟩; exact raise_OmegaPlus F p hp2 n (by omega))
  intro p hp hp2 R hR
  haveI : Fact p.Prime := ⟨hp⟩
  exact autLift_of_induced _ (semiIsoQ_one _) (fun _ _ => semiIsoQ_mul _) (fun _ => semiIsoQ_inv _)
    p R hR (induced_POmegaPlus F p hp2 n hn R hR)

theorem oppositeFixed_POmegaMinus (n : ℕ) (hn : 4 ≤ n) (b c : F)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    OppositeFixed (StatedProj (StatedOmega (StatedQuadMinus n F b c))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : ∀ (h : StatedOmega (StatedQuadMinus n F b c))
      (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F),
      (quadMinusForm n F b c hirr).Q (natRep (StatedOmega (StatedQuadMinus n F b c)) h v) =
        (quadMinusForm n F b c hirr).Q v := fun h v => by
    rw [natRep_apply]
    exact orthGroup_preserves (quadMinusForm n F b c hirr).Q (statedOmega_le_orthGroup _ h.2) v
  have hstar : NoQuotientReflection (quadMinusForm n F b c hirr)
      (natRep (StatedOmega (StatedQuadMinus n F b c))) := fun h Z hZ a ha hQa => by
    simp only [natRep_apply]
    exact not_reflection_on_quotient_of_mem_statedOmega (quadMinusForm n F b c hirr) h.2 hZ ha hQa
  refine oppFixed_of_raise (H := StatedOmega (StatedQuadMinus n F b c))
    ((StatedScalars (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F).subgroupOf
      (StatedOmega (StatedQuadMinus n F b c)))
    (statedProj_kernel_central _) (statedProj_kernel_coprime 2 _)
    (P := SemiIsoQ (quadMinusForm n F b c hirr)) (natRep (StatedOmega (StatedQuadMinus n F b c)))
    (natRep_injective _)
    (fun Q => singFlag (quadMinusForm n F b c hirr)
      (natRep (StatedOmega (StatedQuadMinus n F b c))) Q)
    (fun Q _ => normalizer_le_flagStab_singFlag hQ Q)
    (fun Q hQ2 => le_flagKernel_singFlag 2 hQ hstar Q hQ2) ?_
    (fun p hp hp2 => by
      haveI : Fact p.Prime := ⟨hp⟩; exact raise_OmegaMinus F p hp2 n (by omega) b c hirr)
  intro p hp hp2 R hR
  haveI : Fact p.Prime := ⟨hp⟩
  exact autLift_of_induced _ (semiIsoQ_one _) (fun _ _ => semiIsoQ_mul _) (fun _ => semiIsoQ_inv _)
    p R hR (induced_POmegaMinus F p hp2 n hn b c hirr R hR)

end FamilyTheorems2

section Top

open CFSG.Blueprint

theorem four_le_two_pow {f : ℕ} (hf : 1 ≤ f) (h : 2 ^ f ≠ 2) : 4 ≤ 2 ^ f := by
  rcases Nat.lt_or_ge f 2 with h2 | h2
  · obtain rfl : f = 1 := by omega
    exact absurd (by norm_num) h
  · calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h2

theorem four_le_of_three_le_two_pow {f : ℕ} (h : 3 ≤ 2 ^ f) : 4 ≤ 2 ^ f := by
  rcases Nat.lt_or_ge f 2 with h2 | h2
  · interval_cases f <;> simp at h
  · calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h2

theorem oppositeFixed_top {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (h : CFSG.AGLEmbedding.IsClassicalTwoOrG2 S) :
    OppositeFixed S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases isClassicalTwoOrG2_cases hs hna h with ⟨t, n, f, ht, hmodel⟩ | ⟨f, hG2⟩ | ⟨⟨e⟩⟩ | hU
  · rcases ht with rfl | rfl | rfl | rfl | rfl
    ·
      obtain ⟨⟨hp, hf, hn2, h22, h23⟩, K, _, _, hK, ⟨e⟩⟩ := hmodel
      haveI : CharP K 2 := charP_of_natCard_eq hK
      refine oppositeFixed_of_mulEquiv e.symm (oppositeFixed_PSL n K hn2 ?_)
      by_cases h3 : 3 ≤ n
      · exact Or.inr h3
      · obtain rfl : n = 2 := by omega
        left
        rw [hK]
        exact four_le_two_pow hf fun h' => h22 (by simp [h'])
    ·
      obtain ⟨⟨hp, hf, hn3, h32⟩, K, _, _, hK, ⟨e⟩⟩ := hmodel
      haveI : CharP K 2 := charP_of_natCard_eq (f := f * 2) (by rw [hK, pow_mul])
      refine oppositeFixed_of_mulEquiv e.symm (oppositeFixed_PSU K f hK n hn3 ?_)
      by_cases h4 : 4 ≤ n
      · exact Or.inr h4
      · obtain rfl : n = 3 := by omega
        left
        have h2f : 2 ^ f ≠ 2 := fun h' => h32 (by simp [h'])
        have := four_le_two_pow hf h2f
        omega
    ·
      obtain ⟨⟨hp, hf, hn2, h22⟩, K, _, _, hK, ⟨e⟩⟩ := hmodel
      haveI : CharP K 2 := charP_of_natCard_eq hK
      refine oppositeFixed_of_mulEquiv e.symm (oppositeFixed_PSp K n hn2 ?_)
      by_cases h3 : 3 ≤ n
      · exact Or.inr h3
      · obtain rfl : n = 2 := by omega
        left
        rw [hK]
        exact four_le_two_pow hf fun h' => h22 (by simp [h'])
    ·
      obtain ⟨⟨hp, hf, hn4⟩, K, _, _, hK, ⟨e⟩⟩ := hmodel
      haveI : CharP K 2 := charP_of_natCard_eq hK
      by_cases h5 : 5 ≤ n
      · exact oppositeFixed_of_mulEquiv e.symm (oppositeFixed_POmegaPlus K n h5)
      · obtain rfl : n = 4 := by omega
        exact oppositeFixed_of_mulEquiv e.symm (oppositeFixed_POmegaPlus_four K)
    ·
      obtain ⟨⟨hp, hf, hn4⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hmodel
      haveI : CharP K 2 := charP_of_natCard_eq hK
      exact oppositeFixed_of_mulEquiv e.symm (oppositeFixed_POmegaMinus K n hn4 b c hirr)
  ·
    obtain ⟨⟨hp, hf, hn0, h3⟩, K, _, _, hK, ⟨e⟩⟩ := hG2
    haveI : CharP K 2 := charP_of_natCard_eq hK
    exact oppositeFixed_of_mulEquiv e.symm
      (oppositeFixed_G2 (by rw [hK]; exact four_le_of_three_le_two_pow h3))
  · exact oppositeFixed_of_mulEquiv e.symm oppositeFixed_alternating_six
  · obtain ⟨_, K, _, _, hK, ⟨e⟩⟩ := hU
    exact oppositeFixed_of_mulEquiv e.symm (oppositeFixed_PSU_three_three hK)

end Top

end CFSG.LieType.ChevTwo.OppCl
