module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapRes
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapRB
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapRC
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapRD
import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapBI

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

namespace SwapP2

@[expose] def PumpSideHeldEleven : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n))
    (M : Subgroup X), Setting t J n e E D M → n = 11 →
    ∀ (e₀ : X) (F : Subgroup X) (DF : Finset (Fin n)) (r : X), Data t J n e E D M e₀ F DF r →
    centralizer ({e₀} : Set X) ≤ Hn E →
    ∀ N₁ : Subgroup X, PumpData M e₀ r N₁ → conjBy N₁ e₀ = N₁ →
    Nonempty (↥N₁ ⧸ Open.fusionZStar ↥N₁ ≃* Blueprint.NativeSporadic.He) →
    ∀ f ∈ F, ∃ a ∈ fixA M e₀ r, f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel N₁ ∧
      f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel M

@[expose] def PumpDiagZEleven : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n))
    (M : Subgroup X), Setting t J n e E D M → n = 11 →
    ∀ (e₀ : X) (F : Subgroup X) (DF : Finset (Fin n)) (r : X), Data t J n e E D M e₀ F DF r →
    (∀ f ∈ F, f ≠ 1 → centralizer ({f} : Set X) ≤ Hn E) →
    centralizer ({e₀} : Set X) ≤ Hn E →
    core (centralizer ({r} : Set X)) ≤ Hn E →
    ∀ N₁ : Subgroup X, PumpData M e₀ r N₁ → conjBy N₁ e₀ ≠ N₁ →
    Nonempty (↥N₁ ⧸ Open.fusionZStar ↥N₁ ≃* alternatingGroup (Fin (n - 4))) → False

theorem swapMemberResidueEleven_of_steps
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    (hSH : PumpSideHeldEleven) (hDZ : PumpDiagZEleven) : SwapMemberResidueEleven := by
  intro X _ _ _ t J n e E D S hn hCH M hMH hMpc hne hJM hMalt hsmall hnarrow
  subst hn
  have hs : Setting t J 11 e E D M := ⟨S, hCH, hMH, hMpc, hne, hJM, hMalt, hsmall, hnarrow⟩
  obtain ⟨e₀, -, -, he₀E, -, -, he₀1, -, -, -, -, -⟩ := exists_three_of_klein S.klein
  obtain ⟨F, DF, r, hd⟩ := dataExist_holds X t J 11 e E D M hs e₀ he₀E he₀1
  have hA := claimAEleven_of_inputs h33 h35 hPump hN1
  have hFH := hA X t J 11 e E D M hs rfl F hd.FJ hd.Fk DF hd.DFc hd.Fs
  have he₀H := hA X t J 11 e E D M hs rfl E S.le S.klein D S.card S.supp e₀ he₀E he₀1
  have hOr := oddCoreR_holds X t J 11 e E D M hs e₀ F DF r hd hFH
  obtain ⟨⟨χr⟩, ⟨hArle, hArpc⟩, N₁, hP⟩ := pump_holds X t J 11 e E D M hs e₀ F DF r hd he₀H
  rcases pumpData_type_eleven hPump hN1 hs hd χr hArle hArpc hP with
    ⟨hfix, hpc, m, hmo, hm7, hm11, ⟨θ₁⟩⟩ | ⟨hfix, ⟨ψ⟩⟩ | ⟨hdiag, ⟨ψ⟩⟩
  ·
    have hside := pumpSide_of_type hs (by norm_num) hd he₀H χr hArle hArpc hP.le hP.pc hP.cover
      θ₁ (by omega) hm11 (Or.inr ⟨hfix, hpc⟩)
    have hside' : ∀ f ∈ F, ∃ a ∈ fixA M e₀ r, f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel N₁ ∧
        f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel M := by
      intro f hf
      obtain ⟨a, ha, h1, h2⟩ := hside f hf
      refine ⟨a, ha, ?_, h2⟩
      rwa [hfix, sup_idem] at h1
    exact isSolomonMember_of_pump hs hd he₀H hP hfix
      (le_of_exact hs (by norm_num) hd hOr hFH hP hfix hside' hmo (by omega) θ₁)
  ·
    have hside := hSH X t J 11 e E D M hs rfl e₀ F DF r hd he₀H N₁ hP hfix ⟨ψ⟩
    exact isSolomonMember_of_pump hs hd he₀H hP hfix
      (le_of_held hs hd hFH he₀H hOr hP hfix ψ hside)
  ·
    exact (hDZ X t J 11 e E D M hs rfl e₀ F DF r hd hFH he₀H hOr N₁ hP hdiag ⟨ψ⟩).elim

theorem pumpSideHeldEleven_holds :
    PumpSideHeldEleven := by
  intro X _ _ _ t J n e E D M hs hn e₀ F DF r hd he₀H N₁ hP hfix hψ
  subst hn
  obtain ⟨ψ⟩ := hψ
  obtain ⟨⟨χr⟩, ⟨hArle, -⟩, -⟩ := pump_holds X t J 11 e E D M hs e₀ F DF r hd he₀H
  have S := hs.sig
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ hd.e₀E
  have he₀o : orderOf e₀ = 2 := orderOf_eq_prime (by rw [sq]; exact he₀2) hd.e₀1
  have he₀r : e₀ ∈ centralizer ({r} : Set X) := mem_centralizer_singleton_iff.mpr hd.re₀.symm
  have hArN : fixA M e₀ r ≤ N₁ := by
    have h1 := hP.cover
    rwa [hfix, sup_idem] at h1
  have hlayer : IsPComponent 2 ((fixA M e₀ r).subgroupOf (N₁ ⊓ centralizer ({e₀} : Set X))) := by
    have h1 := hP.layer
    rwa [hfix, sup_idem] at h1
  have hK : ∀ B : Subgroup X, B ≤ centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X) →
      IsPComponent 2 (B.subgroupOf (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))) →
      (∀ x ∈ B, ∀ z ∈ fixA M e₀ r,
        x * z * x⁻¹ * z⁻¹ ∈ (pPrimeCore 2 ↥(fixA M e₀ r)).map (fixA M e₀ r).subtype) →
      B ≤ UnbalancedLayer.coreActionKernel N₁ ∧
        B ≤ UnbalancedLayer.coreActionKernel (conjBy N₁ e₀) := by
    intro B hBC hBpc hBA
    have h := He9.le_coreActionKernel_of_held he₀r he₀o hP.le hP.pc hfix
      (le_inf hArN (hArle.trans inf_le_right)) hlayer χr hBC hBpc hBA ψ
    refine ⟨h, ?_⟩
    rw [hfix]
    exact h
  intro f hf
  obtain ⟨a, ha, h1, h2⟩ := pumpSide_of_commute hs (by norm_num) hd he₀H hP.le hP.pc hK f hf
  refine ⟨a, ha, ?_, h2⟩
  rwa [hfix, sup_idem] at h1

theorem pumpDiagZEleven_holds : PumpDiagZEleven := by
  intro X _ _ _ t J n e E D M hs hn e₀ F DF r hd hFH he₀H hOr N₁ hP hdiag hψ
  subst hn
  obtain ⟨ψ⟩ := hψ
  obtain ⟨⟨χr⟩, ⟨hArle, hArpc⟩, -⟩ := pump_holds X t J 11 e E D M hs e₀ F DF r hd he₀H
  exact false_of_diagonalZ hs rfl hd he₀H hOr hFH χr hArle hArpc hP.le hP.pc hP.cover hdiag ψ

theorem swapMemberResidueEleven_of_inputs
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion) :
    SwapMemberResidueEleven :=
  swapMemberResidueEleven_of_steps h33 h35 hPump hN1 pumpSideHeldEleven_holds
    pumpDiagZEleven_holds

theorem swapMemberResidue_of_nine
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    (h9 : SwapMemberResidueNine) : SwapMemberResidue :=
  swapMemberResidue_of_eleven_nine (swapMemberResidueEleven_of_inputs h33 h35 hPump hN1) h9

end SwapP2

end CFSG.ComponentClassification.SolMax
