module

public import CFSG.ClassicalInvolution.Q3.Q3TSetup
public import CFSG.ClassicalInvolution.Uniform.UThmStmtA

public section

namespace CFSG.ClassicalInvolution.Q3.Disc3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement

section Alpha

variable {G : Type} [Group G]

theorem alphaOf_eq_bot_of_oddCentralizers {A : Subgroup G} (hA : ∃ a ∈ A, a ≠ 1)
    (h : ∀ a ∈ A, a ≠ 1 → oddCoreOf (Subgroup.centralizer ({a} : Set G)) = ⊥) :
    alphaOf A = ⊥ := by
  unfold alphaOf
  have h1 : (⨆ a ∈ A, ⨆ (_ : a ≠ 1), ⁅oddCoreOf (Subgroup.centralizer ({a} : Set G)), A⁆) =
      ⊥ := by
    refine le_bot_iff.mp (iSup₂_le fun a ha => iSup_le fun hne => ?_)
    exact (by rw [h a ha hne, Subgroup.commutator_bot_left] :
      ⁅oddCoreOf (Subgroup.centralizer ({a} : Set G)), A⁆ = ⊥).le
  have h2 : (⨅ a ∈ A, ⨅ (_ : a ≠ 1), oddCoreOf (Subgroup.centralizer ({a} : Set G))) = ⊥ := by
    obtain ⟨a, ha, hne⟩ := hA
    exact le_bot_iff.mp ((iInf₂_le a ha).trans ((iInf_le _ hne).trans (h a ha hne).le))
  rw [h1, h2, sup_bot_eq]

end Alpha

section Generated

variable {G : Type} [Group G] [Finite G]

theorem thm5Gen_three {n : ℕ} (hn : CITBelowT (.sl2 3 1) n) (hlt : Nat.card G < n)
    {Ω : Set (Subgroup G)} (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hne : Ω.Nonempty)
    (hgen : (⨆ J ∈ Ω, J) = ⊤) (hO : classicalInvolutionOddCore G = ⊥) {A : Subgroup G}
    (hA : IsElemAbelian2 A 2) : alphaOf A = ⊥ := by
  have hcls : InClassU (.sl2 3 1) Ω := ⟨hne, hΩ.conjInvariant, hgen, hΩ.classical⟩
  have hLie : LieSystemMod3 Ω :=
    (lieSystemModU_sl2_of_eq_three (p := 3) (f := 1) (by norm_num)).mp (hn G hlt Ω hcls)
  refine alphaOf_eq_bot_of_oddCentralizers ?_ fun a ha hne1 => ?_
  · by_contra hcon
    push Not at hcon
    have hbot : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr hcon
    have h4 := hA.1
    rw [hbot, Subgroup.card_bot] at h4
    omega
  · have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact hA.2 a ha) hne1
    have h := lieSystemOddCentralizer3_proved G Ω hLie a ha2
    rw [hO] at h
    exact le_bot_iff.mp h

end Generated

section NonGenerated

@[expose] def Thm5NonGenBelowU (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ Ω : Set (Subgroup G),
    HypOmegaModU (.sl2 3 1) Ω → (⨆ J ∈ Ω, J) ≠ ⊤ → classicalInvolutionOddCore G = ⊥ →
      ∀ K ∈ Ω, ∀ J ∈ omegaNbr Ω K, ∀ z : G, IsUniqueInvolution K z →
        ∀ A : Subgroup G, IsElemAbelian2 A 2 → A ≤ K ⊔ J → z ∈ A → alphaOf A = ⊥

theorem thm5BelowU_three_of_nonGen {n : ℕ} (h : Thm5NonGenBelowU n)
    (hn : CITBelowT (.sl2 3 1) n) : Thm5BelowU 3 1 n := by
  intro _ _ G _ _ hlt Ω hΩ hO K hK J hJ z hz A hA hAKJ hzA
  by_cases hgen : (⨆ J ∈ Ω, J) = ⊤
  · exact thm5Gen_three hn hlt hΩ ⟨K, hK⟩ hgen hO hA
  · exact h G hlt Ω hΩ hgen hO K hK J hJ z hz A hA hAKJ hzA

end NonGenerated

end CFSG.ClassicalInvolution.Q3.Disc3
