module

public import CFSG.GH74.GLS.IVK.Lifted.SL2Aut
public import CFSG.GH74.GLS.IVK.Lifted.TwoA7

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank
open CFSG.GH74.GLS.Stage1.Thm2.Recip (II4_44 II4_Aut IsSL2Or2A7 innOf)

section Dict

open CFSG.GH74.GLS.Stage1.Thm2.Recip (II4_44 II4_Aut IsSL2Or2A7 innOf)

structure HatOK (Q : Type) [Group Q] : Prop where
  quasi : IsQuasisimple Q
  kgrp : IsKGroupNative Q
  rank : pRank 2 Q = 1
  sl2 : IsSL2Or2A7 Q

theorem sl_or_a7 {Q : Type} [Group Q] (hQ : IsSL2Or2A7 Q) :
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧ 3 < Nat.card F ∧
      Nonempty (Q ≃* SpecialLinearGroup (Fin 2) F)) ∨ IsDoubleCoverOfAlt Q 7 := by
  rcases hQ.1 with ⟨F, hF, hFin, hP, ⟨e⟩⟩ | h7
  · left
    obtain ⟨hodd, h5⟩ := hP
    exact ⟨F, hF, hFin, hodd, by omega, ⟨e.trans (specialLinearGroupEquivStatedSL 2 F).symm⟩⟩
  · right
    exact h7

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem conj_eq_one_of_mem_center {c : Q} (hc : c ∈ Subgroup.center Q) : MulAut.conj c = 1 := by
  ext x
  rw [MulAut.conj_apply, MulAut.one_apply]
  have := Subgroup.mem_center_iff.1 hc x
  calc c * x * c⁻¹ = x * c * c⁻¹ := by rw [← this]
    _ = x := mul_inv_cancel_right x c

theorem dict_inner (h2A7 : II4_2A7) (hQ : IsSL2Or2A7 Q) (c : Q)
    (hc : IsFAutomorphism Q (MulAut.conj c)) : c ∈ Subgroup.center Q := by
  by_contra hcz
  rcases sl_or_a7 hQ with ⟨F, _, _, hodd, h3, ⟨e⟩⟩ | h7
  · exact not_fixedCond_conj e c hcz hc.2.2.2.2
  · exact (h2A7 Q h7).1 c hcz hc

theorem dict_sq (h2A7 : II4_2A7) (hQ : IsSL2Or2A7 Q) (φ : MulAut Q) (hφ : IsFAutomorphism Q φ)
    (hin : φ * φ ∈ innOf Q) : φ * φ = 1 := by
  rcases sl_or_a7 hQ with ⟨F, _, _, hodd, h3, ⟨e⟩⟩ | h7
  · obtain ⟨c, hc⟩ := hin
    exact sq_eq_one_of_fixedCond_inner e φ hφ.2.2.2.2 c hc.symm
  · exact (h2A7 Q h7).2.1 φ hφ

theorem dict_coset (h2A7 : II4_2A7) (hO : HatOK Q) (φ ψ : MulAut Q) (hφ : IsFAutomorphism Q φ)
    (hφ1 : φ ≠ 1) (hφ2 : φ * φ = 1) (hψ2 : ψ * ψ = 1) (hin : ψ * φ⁻¹ ∈ innOf Q) :
    IsFAutomorphism Q ψ := by
  rcases sl_or_a7 hO.sl2 with ⟨F, _, _, hodd, h3, ⟨e⟩⟩ | h7
  · exact ⟨hφ.1, hφ.2.1, hφ.2.2.1, exists_pow_two_orderOf hψ2,
      fixedCond_of_coset hodd h3 e φ ψ hφ2 hψ2 hφ1 hφ.2.2.2.2 hin⟩
  · have hφn : φ ∉ innOf Q := by
      rintro ⟨c, hc⟩
      have hcz := dict_inner h2A7 hO.sl2 c (hc ▸ hφ)
      exact hφ1 (hc ▸ conj_eq_one_of_mem_center hcz)
    have hψn : ψ ∉ innOf Q := by
      intro hψ
      apply hφn
      have : φ = (ψ * φ⁻¹)⁻¹ * ψ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hin) hψ
    exact (h2A7 Q h7).2.2.1 ψ hψ2 hψn hO.kgrp

theorem dict_involution (h2A7 : II4_2A7) (hO : HatOK Q) (φ : MulAut Q) (hφ2 : φ * φ = 1)
    (W : Subgroup Q) (hW2 : IsPGroup 2 ↥W) (hWnc : ¬ ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hWφ : ∀ w ∈ W, φ w = w) : φ = 1 ∨ IsFAutomorphism Q φ := by
  by_cases hφ1 : φ = 1
  · exact Or.inl hφ1
  right
  rcases sl_or_a7 hO.sl2 with ⟨F, _, _, hodd, h3, ⟨e⟩⟩ | h7
  · refine ⟨hO.quasi, hO.kgrp, hO.rank, exists_pow_two_orderOf hφ2,
      fixedCond_of_noncomm hodd h3 e φ hφ2 hφ1 ?_⟩
    intro hcomm
    apply hWnc
    intro a ha b hb
    exact hcomm a (hWφ a ha) b (hWφ b hb)
  · by_cases hin : φ ∈ innOf Q
    · exfalso
      obtain ⟨c, hc⟩ := hin
      have hcz : c ∉ Subgroup.center Q := fun hcz => hφ1 (hc ▸ conj_eq_one_of_mem_center hcz)
      have hc2 : c * c ∈ Subgroup.center Q := by
        rw [Subgroup.mem_center_iff]
        intro x
        have h1 : (MulAut.conj (c * c)) x = x := by
          rw [map_mul, hc]
          show φ (φ x) = x
          have := congrArg (fun ρ : MulAut Q => ρ x) hφ2
          simpa using this
        rw [MulAut.conj_apply] at h1
        calc x * (c * c) = (c * c * x * (c * c)⁻¹) * (c * c) := by rw [h1]
          _ = c * c * x := by group
      have hcomm : ∀ w ∈ W, c * w = w * c := by
        intro w hw
        have h1 : (MulAut.conj c) w = w := by rw [hc]; exact hWφ w hw
        rw [MulAut.conj_apply] at h1
        calc c * w = (c * w * c⁻¹) * c := by group
          _ = w * c := by rw [h1]
      have hcyc := (h2A7 Q h7).2.2.2.2.2.1 c hcz hc2 W hW2 hcomm
      apply hWnc
      intro a ha b hb
      let := IsCyclic.commGroup (α := ↥W)
      have := mul_comm (⟨a, ha⟩ : ↥W) ⟨b, hb⟩
      simpa using congrArg Subtype.val this
    · exact (h2A7 Q h7).2.2.1 φ hφ2 hin hO.kgrp

theorem dict_diag (h2A7 : II4_2A7) (hO : HatOK Q) (φ ψ : MulAut Q) (hφ2 : φ * φ = 1)
    (hψ2 : ψ * ψ = 1) (hφ : φ ∉ innOf Q) (hψ : ψ ∉ innOf Q) (hφf : ¬ IsFAutomorphism Q φ)
    (hψf : ¬ IsFAutomorphism Q ψ) : φ * ψ⁻¹ ∈ innOf Q := by
  rcases sl_or_a7 hO.sl2 with ⟨F, _, _, hodd, h3, ⟨e⟩⟩ | h7
  · apply sl_diag hodd h3 e φ ψ hφ2 hψ2 hφ hψ
    · intro hf
      exact hφf ⟨hO.quasi, hO.kgrp, hO.rank, exists_pow_two_orderOf hφ2, hf⟩
    · intro hf
      exact hψf ⟨hO.quasi, hO.kgrp, hO.rank, exists_pow_two_orderOf hψ2, hf⟩
  · exact absurd ((h2A7 Q h7).2.2.1 φ hφ2 hφ hO.kgrp) hφf

theorem dict_pow (h2A7 : II4_2A7) (hO : HatOK Q) (φ : MulAut Q) (hφ : IsFAutomorphism Q φ)
    (hφ1 : φ ≠ 1) :
    ∃ m : ℕ, φ ^ m ≠ 1 ∧ φ ^ m * φ ^ m = 1 ∧ IsFAutomorphism Q (φ ^ m) := by
  rcases sl_or_a7 hO.sl2 with ⟨F, _, _, hodd, h3, ⟨e⟩⟩ | h7
  · obtain ⟨k, hk⟩ := hφ.2.2.2.1
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hφ1
      rw [pow_zero] at hk
      exact orderOf_eq_one_iff.1 hk
    have hne : φ ^ (2 ^ (k - 1)) ≠ 1 := by
      intro h1
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hk] at h2
      have h3 := Nat.le_of_dvd (by positivity) h2
      have h4 : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have hsq : φ ^ (2 ^ (k - 1)) * φ ^ (2 ^ (k - 1)) = 1 := by
      rw [← pow_add]
      have : 2 ^ (k - 1) + 2 ^ (k - 1) = 2 ^ k := by
        rw [← two_mul, ← pow_succ']
        congr 1
        omega
      rw [this, ← hk]
      exact pow_orderOf_eq_one φ
    have hsub : ∀ m : ℕ, fixedSubgroup Q φ ≤ fixedSubgroup Q (φ ^ m) := by
      intro m
      induction m with
      | zero =>
        intro a _
        show (φ ^ 0) a = a
        rw [pow_zero]
        rfl
      | succ m ih =>
        intro a ha
        have h1 : (φ ^ m) a = a := ih ha
        have h2 : φ a = a := ha
        show (φ ^ (m + 1)) a = a
        rw [pow_succ', MulAut.mul_apply, h1, h2]
    refine ⟨2 ^ (k - 1), hne, hsq, hφ.1, hφ.2.1, hφ.2.2.1, exists_pow_two_orderOf hsq, ?_⟩
    refine fixedCond_of_noncomm hodd h3 e _ hsq hne ?_
    intro hcomm
    exact not_fixedCond_of_comm φ (fun a ha b hb => hcomm a (hsub _ ha) b (hsub _ hb)) hφ.2.2.2.2
  · refine ⟨1, by simpa using hφ1, ?_, by simpa using hφ⟩
    rw [pow_one]
    exact (h2A7 Q h7).2.1 φ hφ

end Dict

end CFSG.GH74.GLS.IVK.Lifted
