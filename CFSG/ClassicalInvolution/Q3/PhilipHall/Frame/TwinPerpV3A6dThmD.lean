module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6dAbs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6d

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section ThmD

variable {Y : Type} [Group Y] [Finite Y] {Ω P : Set (Subgroup Y)}

theorem aeIdent8_of_thmD (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    (h8 : ∀ J ∈ Ω, Nat.card J = 8) (hA : ∀ J ∈ Ω, AEmpty Ω J) (hPΩ : P ⊆ Ω)
    (htrans : ∀ L ∈ P, ∀ L' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L')
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (hodd : classicalInvolutionOddCore ↥(pSpan P) = ⊥)
    (he2 : ∀ L ∈ P, ∀ u : Y, IsUniqueInvolution L u → ∃ Q : Subgroup Y, Q ≤ pSpan P ∧
      (∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧ IsPGroup 2 Q ∧ u ∈ Q)
    (hD : ThmDAbsAt 3 ↥(pSpan P)) {z : Y} {A₁ A₂ A₃ A₄ : Subgroup Y}
    (F : FourTwins P z A₁ A₂ A₃ A₄)
    (hthin : ∀ L ∈ P, ∀ u : Y, IsUniqueInvolution L u → ∀ Q : Subgroup Y, Q ≤ pSpan P →
      (∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) → IsPGroup 2 Q → ∀ x ∈ L, x ∈ Q → x = 1 ∨ x = u)
    (hfive : ∃ y : ↥(pSpan P), orderOf y = 5)
    (h64 : NoOrderFive e64Sub) (h29 : NoOrderFive e29Sub) : Nonempty (AEIdent P 8) := by
  have hcard : ∀ J ∈ Ω, Nat.card J = 2 ^ 3 := fun J hJ => (h8 J hJ).trans (by norm_num)
  have hPne : P.Nonempty := ⟨A₁, F.m₁⟩
  obtain ⟨y, hy⟩ := hfive
  rcases thmDGen_at hΩ h2 hcard hA hPΩ hD htrans hinv hodd he2 with
    hsing | ⟨W, hW⟩ | ⟨E, hE⟩ | hI64 | ⟨m, hm5, hIm⟩ | hI29
  · exact absurd (hsing A₁ F.m₁ A₂ F.m₂) F.ne₁₂
  · exact (false_of_WIn_eq hΩ h2 h8 hPΩ hPne hinv hthin hW).elim
  ·
    have hS : SecHyp 3 Ω P := ⟨hΩ, h2, hcard, hA, hPΩ, hinv, htrans, hodd, he2⟩
    have hΦ := hS.thmDHyp
    have hE' := hE.toTop
    have hmem : ∀ {A : Subgroup Y}, A ∈ P → A.subgroupOf (pSpan P) ∈ restrictFamily P (pSpan P) :=
      fun hA => ⟨_, hA, le_pSpan hA, rfl⟩
    have heq := eq_of_inv_e8 hΦ hE' (hmem F.m₁) (hmem F.m₂)
      (isUniqueInvolution_subgroupOf F.z₁ (le_pSpan F.m₁))
      (isUniqueInvolution_subgroupOf F.z₂ (le_pSpan F.m₂))
    have h12 := Subgroup.subgroupOf_inj.mp heq
    rw [inf_eq_left.mpr (le_pSpan F.m₁), inf_eq_left.mpr (le_pSpan F.m₂)] at h12
    exact absurd h12 F.ne₁₂
  · obtain ⟨I⟩ := hI64
    exact (false_of_order_five I.φ (I.toLabel.isPGroup_ker hodd) I.range_eq h64 y hy).elim
  · obtain ⟨I⟩ := hIm
    by_cases hm8 : m = 8
    · subst hm8
      exact ⟨I⟩
    · exact (false_of_four_twins hm5 hm8 hΩ h2 h8 hPΩ I (I.isPGroup_ker hodd) F).elim
  · obtain ⟨I⟩ := hI29
    exact (false_of_order_five I.φ (I.toLabel.isPGroup_ker hodd) I.range_eq h29 y hy).elim

end ThmD

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6d
