module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23WMu
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23WAbs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23WLab
public import CFSG.ClassicalInvolution.Q3.Q3AMTriB01

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement




namespace W

open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.AE5 CFSG.ClassicalInvolution.Asc77.Thompson

section Fin

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G} {Wg : Subgroup G}

theorem false_of_ae5_mu (hΩ : HypOmegaGen Ω)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hS : Q8Section (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c))
      (TwinDisc.secFam Ω c))
    (I : TC.Thin.AEIdent (TwinDisc.secFam Ω c) 5) (hWg : Wg ∈ WSet Ω)
    (hDc : ∀ R ∈ DSet Ω Wg, R ≤ Subgroup.centralizer ({c} : Set G))
    (e : ↥(muGroup Ω Wg) ≃* Equiv.Perm (Fin 4))
    {J₀ R₀ : Subgroup G} {t : G} (hJ₀ : J₀ ∈ Ω) (hR₀ : IsSylow2In R₀ J₀) (hR₀D : R₀ ∈ DSet Ω Wg)
    (ht : IsUniqueInvolution J₀ t) (htW : t ∈ Wg) : False := by
  classical
  have hgen := hgen_of hS
  have hLc : MGrp Ω Wg ≤ coreLayer Ω c := by
    refine le_trans ?_ (rLayer_le_coreLayer hΩ h2 hc2)
    exact iSup₂_le fun R hR => le_iSup₂_of_le R hR.1
      (le_iSup (fun _ : R ≤ Subgroup.centralizer ({c} : Set G) => R) (hDc R hR))
  set chiM : ↥(MGrp Ω Wg) →* Equiv.Perm (Fin 5) :=
    (chiLayer Ω c hgen I).comp (Subgroup.inclusion hLc) with hchiM
  have hJ₀tq : J₀ ∈ tqMembers3 Ω c :=
    ⟨hJ₀, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₀ ⟨R₀, hR₀, hDc R₀ hR₀D⟩⟩
  obtain ⟨α₀, h₀, b₀, hlab₀⟩ := I.label _ (TwinDisc.secImg_mem_secFam hJ₀tq)
  obtain ⟨p₀, hp₀⟩ := exists_not_mem_finset α₀ h₀
  have hA : ∀ J ∈ tqMembers3 Ω c, IsPGroup 2 ↥(TwinDisc.secImg Ω c J) := fun J hJ =>
    members_twoN (by norm_num) hS I _ (TwinDisc.secImg_mem_secFam hJ)
  have hF3 : ∀ x : ↥(MGrp Ω Wg), PhiM e x = 1 → chiM x p₀ = p₀ := by
    intro x hx
    have hxs : (x : G) ∈ Wg ⊔ OCW Wg := (PhiM_eq_one_iff e x).mp hx
    have hmem : (x : G) ∈ Subgroup.centralizer ({t} : Set G) := by
      refine (sup_le (fun w hw => ?_) (fun o ho => ?_) :
        Wg ⊔ OCW Wg ≤ Subgroup.centralizer ({t} : Set G)) hxs
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Q3CL.Thompson.commutes_of_mem_WSet hΩ hWg t htW w hw).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp (OCW_le_centralizer Wg ho) t htW).symm
    have hxt : (x : G) * t = t * (x : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hmem
    exact chiLayer_fix_of_commutes hΩ hc2 hS I hJ₀tq ht hlab₀ hp₀ (hLc x.2) hxt
  let Nm : Subgroup ↥(MGrp Ω Wg) := (oddCoreOf (coreLayer Ω c)).subgroupOf (MGrp Ω Wg)
  have hNn : Nm.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact Q3AM.conj_mem_oddCoreOf_of_mem_tri (hLc g.2) hn⟩
  have hNodd : Odd (Nat.card Nm) := by
    have hcard : Nat.card Nm = Nat.card ↥(oddCoreOf (coreLayer Ω c) ⊓ MGrp Ω Wg) := by
      show Nat.card ((oddCoreOf (coreLayer Ω c)).subgroupOf (MGrp Ω Wg)) = _
      rw [← Subgroup.inf_subgroupOf_right]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [hcard]
    exact (oddCoreOf_odd_natCard (coreLayer Ω c)).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hχN : ∀ x : ↥(MGrp Ω Wg), chiM x = 1 → ∃ j : ℕ, x ^ 2 ^ j ∈ Nm := by
    intro x hx
    obtain ⟨j, hj⟩ := exists_pow_mem_oddCoreOf_of_chi_eq_one hΩ hc2 hS I (hLc x.2) hx
    refine ⟨j, Subgroup.mem_subgroupOf.mpr ?_⟩
    simpa using hj
  by_cases hall : ∀ R ∈ DSet Ω Wg, ∀ τ ∈ R,
      ∃ hL : τ ∈ coreLayer Ω c, V4m p₀ (chiLayer Ω c hgen I ⟨τ, hL⟩)
  ·
    have hMall : ∀ x ∈ MGrp Ω Wg, ∃ hL : x ∈ coreLayer Ω c,
        V4m p₀ (chiLayer Ω c hgen I ⟨x, hL⟩) := by
      intro x hx
      refine Subgroup.iSup_induction (fun R : Subgroup G => ⨆ (_ : R ∈ DSet Ω Wg), R)
        (C := fun x => ∃ hL : x ∈ coreLayer Ω c, V4m p₀ (chiLayer Ω c hgen I ⟨x, hL⟩)) hx
        ?_ ?_ ?_
      · intro R y hy
        refine Subgroup.iSup_induction (fun _ : R ∈ DSet Ω Wg => R)
          (C := fun x => ∃ hL : x ∈ coreLayer Ω c, V4m p₀ (chiLayer Ω c hgen I ⟨x, hL⟩)) hy
          ?_ ?_ ?_
        · intro hR z hz
          exact hall R hR z hz
        · exact ⟨one_mem _, by
            have : (⟨1, one_mem _⟩ : ↥(coreLayer Ω c)) = 1 := rfl
            rw [this, map_one]
            exact V4m_one p₀⟩
        · rintro a b ⟨hLa, hva⟩ ⟨hLb, hvb⟩
          refine ⟨mul_mem hLa hLb, ?_⟩
          have : (⟨a * b, mul_mem hLa hLb⟩ : ↥(coreLayer Ω c)) = ⟨a, hLa⟩ * ⟨b, hLb⟩ := rfl
          rw [this, map_mul]
          exact V4m_mul p₀ _ _ hva hvb
      · exact ⟨one_mem _, by
          have : (⟨1, one_mem _⟩ : ↥(coreLayer Ω c)) = 1 := rfl
          rw [this, map_one]
          exact V4m_one p₀⟩
      · rintro a b ⟨hLa, hva⟩ ⟨hLb, hvb⟩
        refine ⟨mul_mem hLa hLb, ?_⟩
        have : (⟨a * b, mul_mem hLa hLb⟩ : ↥(coreLayer Ω c)) = ⟨a, hLa⟩ * ⟨b, hLb⟩ := rfl
        rw [this, map_mul]
        exact V4m_mul p₀ _ _ hva hvb
    have hsq : ∀ x : ↥(MGrp Ω Wg), chiM x * chiM x = 1 := by
      intro x
      obtain ⟨hL, hv⟩ := hMall x x.2
      exact V4m_sq p₀ _ hv
    exact no_order_three (PhiM e) (PhiM_surjective e) Nm hNodd chiM hsq hχN
  · push Not at hall
    obtain ⟨R₁, hR₁D, x₁, hx₁R, hx₁⟩ := hall
    obtain ⟨J₁, hJ₁Ω, hRJ₁⟩ := exists_isSylow2In_of_mem_RSet hR₁D.1
    have hJ₁tq : J₁ ∈ tqMembers3 Ω c :=
      ⟨hJ₁Ω, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₁Ω ⟨R₁, hRJ₁, hDc R₁ hR₁D⟩⟩
    obtain ⟨α₁, h₁, b₁, hlab₁⟩ := I.label _ (TwinDisc.secImg_mem_secFam hJ₁tq)
    obtain ⟨p₁, hp₁⟩ := exists_not_mem_finset α₁ h₁
    obtain ⟨hL₁, hv₁⟩ := chiLayer_perm_mem hΩ hc2 hgen I hJ₁tq hRJ₁ (hDc R₁ hR₁D) hlab₁ hp₁ x₁ hx₁R
    have hne : p₀ ≠ p₁ := fun heq => hx₁ hL₁ (heq ▸ hv₁)
    obtain ⟨σ, τ', hσ, hτ', hfree⟩ := V4m_five p₀ p₁ hne
    obtain ⟨x₀, hx₀R, hL₀, hx₀e⟩ := chiLayer_exists_perm hΩ hc2 hgen I hJ₀tq hR₀
      (hDc R₀ hR₀D) (hA J₀ hJ₀tq) hlab₀ hp₀ σ hσ
    obtain ⟨x₁', hx₁'R, hL₁', hx₁'e⟩ := chiLayer_exists_perm hΩ hc2 hgen I hJ₁tq hRJ₁
      (hDc R₁ hR₁D) (hA J₁ hJ₁tq) hlab₁ hp₁ τ' hτ'
    set y : ↥(MGrp Ω Wg) := ⟨x₀, le_MGrp_of_mem_D hR₀D hx₀R⟩ *
      ⟨x₁', le_MGrp_of_mem_D hR₁D hx₁'R⟩ with hy
    have hchiy : chiM y = σ * τ' := by
      rw [hy, map_mul]
      have e0 : chiM ⟨x₀, le_MGrp_of_mem_D hR₀D hx₀R⟩ = σ := hx₀e
      have e1 : chiM ⟨x₁', le_MGrp_of_mem_D hR₁D hx₁'R⟩ = τ' := hx₁'e
      rw [e0, e1]
    exact no_free_power (PhiM e) chiM p₀ hF3 y (by rw [hchiy]; exact hfree)

end Fin

end W

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
