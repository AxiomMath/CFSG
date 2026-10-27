module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NO
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Sub

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


namespace ZNW4

variable (hw : ZNW4 t L S x₁ x₂ lam rho tau)
include hw

private lemma t_cent_V (v : G) (hv : v ∈ fourGrp x₁ x₂) : t * v = v * t := by
  have hmem : t ∈ ctxM t tau x₁ x₂ ⊓
      centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := hw.O_eq_CV ▸ hw.t_mem_O
  exact (Subgroup.mem_centralizer_iff.mp hmem.2 v hv).symm

theorem U_le_O {R A : Subgroup G} (hR : IsPGroup 2 R)
    (hVR : ctxVN t tau x₁ x₂ lam rho ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) :
    A ≤ ctxO t tau x₁ x₂ := by
  intro x hx
  obtain ⟨hVA, hcomm⟩ := hw.U_VA hR hVR hA hAN
  set c := x * t * x⁻¹ * t⁻¹ with hcdef
  have hcV : c ∈ fourGrp x₁ x₂ := hcomm x hx
  have hct : x * t * x⁻¹ = c * t := by rw [hcdef]; group
  have hctc : c * t = t * c := (hw.t_cent_V c hcV).symm
  have hsm : x * t * x⁻¹ ∈ t • (fourGrp x₁ x₂ : Set G) := by
    rw [Set.mem_smul_set]
    refine ⟨c, hcV, ?_⟩
    change t * c = x * t * x⁻¹
    rw [← hctc, ← hct]
  rw [← hw.tQ] at hsm
  obtain ⟨r, hrQ, hr⟩ := hsm
  let s := r⁻¹ * x
  have hs_t : s * t * s⁻¹ = t := by
    have h2 : s * t * s⁻¹ = r⁻¹ * (x * t * x⁻¹) * r := by
      dsimp only [s]; group
    rw [h2, ← hr]; group
  have hst : s * t = t * s := by
    calc s * t = s * t * s⁻¹ * s := by group
      _ = t * s := by rw [hs_t]
  have hscent : s ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hst
  have hSR : S ≤ R := hw.S_le_ctxVN.trans hVR
  have hsR : s ∈ R := by
    have hrR : r ∈ R := hVR (hw.W_le_ctxVN (hw.Q_le_ctxWN hrQ))
    show r⁻¹ * x ∈ R
    exact R.mul_mem (R.inv_mem hrR) (hA.1 hx)
  have hsS : s ∈ S := by
    have heq := S4B.c17_cent_eq hw.toCtx10 hR hSR
    have hmem : s ∈ R ⊓ centralizer ({t} : Set G) := ⟨hsR, hscent⟩
    rwa [heq] at hmem
  have hsV : s ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hrv : r⁻¹ * v = v * r⁻¹ :=
      hw.Q_comm r⁻¹ (Subgroup.inv_mem _ hrQ) v (hw.Y_le_Q (hw.V_le_Y hv))
    have hvx : x * v = v * x := by
      haveI : IsMulCommutative ↥A := hA.2.1.1
      exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥A) (⟨v, hVA hv⟩ : ↥A))
    dsimp only [s]
    calc v * (r⁻¹ * x) = (v * r⁻¹) * x := by group
      _ = (r⁻¹ * v) * x := by rw [hrv]
      _ = r⁻¹ * (v * x) := by group
      _ = r⁻¹ * (x * v) := by rw [← hvx]
      _ = (r⁻¹ * x) * v := by group
  have hsint : s ∈ zpowers t ⊔ closure ({x₁, x₂, tau} : Set G) := by
    have heq := hw.U_CS_V hR hVR hA hAN
    have hmem : s ∈ S ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := ⟨hsS, hsV⟩
    rwa [heq] at hmem
  have hQO : ctxQ t tau x₁ x₂ rho ≤ ctxO t tau x₁ x₂ := by
    rw [hw.O_eq_Q]; exact le_sup_left
  have hsub : zpowers t ⊔ closure ({x₁, x₂, tau} : Set G) ≤ ctxO t tau x₁ x₂ := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact hw.t_mem_O
    · rw [Subgroup.closure_le]
      rintro g (hg : g ∈ ({x₁, x₂, tau} : Set G))
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact hQO (hw.base_le_Q (Subgroup.subset_closure (by simp)))
      · exact hQO (hw.base_le_Q (Subgroup.subset_closure (by simp)))
      · exact hw.tau_mem_O
  have hsO : s ∈ ctxO t tau x₁ x₂ := hsub hsint
  have hxrs : x = r * s := by dsimp only [s]; group
  rw [hxrs]
  exact (ctxO t tau x₁ x₂).mul_mem (hQO hrQ) hsO

theorem U_eq_Y {R A : Subgroup G} (hR : IsPGroup 2 R)
    (hVR : ctxVN t tau x₁ x₂ lam rho ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) :
    A = ctxYq t tau x₁ x₂ rho := by
  have hle : A ≤ ctxYq t tau x₁ x₂ rho := by
    intro x hx
    have hxO : x ∈ ctxO t tau x₁ x₂ := hw.U_le_O hR hVR hA hAN hx
    have hclM : closure ({t, tau} : Set G) ≤ ctxM t tau x₁ x₂ := by
      rw [Subgroup.closure_le]
      rintro g (hg : g ∈ ({t, tau} : Set G))
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact hw.t_mem_M
      · exact hw.tau_mem_M
    have hnorm : ∀ k ∈ closure ({t, tau} : Set G), ∀ h ∈ ctxQ t tau x₁ x₂ rho,
        k * h * k⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
      fun k hk h hh => hw.normal_Q.2 k (hclM hk) h hh
    have hxQ : x ∈ ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G) := by
      rw [← hw.O_eq_Q]; exact hxO
    obtain ⟨q, hq, u, hu, hxqu⟩ :=
      (S4B.mem_sup_iff_of_normalizes (H := ctxQ t tau x₁ x₂ rho)
        (K := closure ({t, tau} : Set G)) hnorm).mp hxQ
    have hu4 := (S4B.mem_closure_pair_of_invol (a := t) (b := tau) (x := u)
      hw.t_mul_self hw.tau_mul_self hw.t_comm_tau).mp hu
    have htM : t ∈ ctxM t tau x₁ x₂ := hw.t_mem_M
    have htauM : tau ∈ ctxM t tau x₁ x₂ := hw.tau_mem_M
    rcases hu4 with h1 | h2 | h3 | h4
    · rw [h1] at hxqu
      rw [hw.mem_Y_iff x]
      refine ⟨?_, hA.2.1.2 x hx⟩
      rw [hxqu]; simpa using hq
    · rw [h2] at hxqu
      exfalso
      have hq' : t⁻¹ * q * t ∈ ctxQ t tau x₁ x₂ rho := by
        simpa using hw.normal_Q.2 t⁻¹ ((ctxM t tau x₁ x₂).inv_mem htM) q hq
      have hxeq : t * (t⁻¹ * q * t) = x := by rw [hxqu]; group
      have hmem : t * (t⁻¹ * q * t) ∈ A := by rw [hxeq]; exact hx
      exact hw.U_tQ hR hVR hA hAN hq' hmem
    · rw [h3] at hxqu
      exfalso
      have hq' : tau⁻¹ * q * tau ∈ ctxQ t tau x₁ x₂ rho := by
        simpa using hw.normal_Q.2 tau⁻¹ ((ctxM t tau x₁ x₂).inv_mem htauM) q hq
      have hxeq : tau * (tau⁻¹ * q * tau) = x := by rw [hxqu]; group
      have hmem : tau * (tau⁻¹ * q * tau) ∈ A := by rw [hxeq]; exact hx
      exact hw.U_tauQ hR hVR hA hAN hq' hmem
    · rw [h4] at hxqu
      exfalso
      have hq' : (t * tau)⁻¹ * q * (t * tau) ∈ ctxQ t tau x₁ x₂ rho := by
        simpa using hw.normal_Q.2 (t * tau)⁻¹
          ((ctxM t tau x₁ x₂).inv_mem ((ctxM t tau x₁ x₂).mul_mem htM htauM)) q hq
      have hxeq : (t * tau) * ((t * tau)⁻¹ * q * (t * tau)) = x := by
        rw [hxqu]; group
      have hmem : (t * tau) * ((t * tau)⁻¹ * q * (t * tau)) ∈ A := by
        rw [hxeq]; exact hx
      exact hw.U_ttauQ hR hVR hA hAN hq' hmem
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hw.card_Y, hA.2.2])

theorem Y_normal_all :
    ∀ R : Subgroup G, IsPGroup 2 R → ctxVN t tau x₁ x₂ lam rho ≤ R →
      NormalIn (ctxYq t tau x₁ x₂ rho) R := by
  exact S4B.normalIn_of_unique_normal_E16 hw.Y_E16 hw.Y_normal_ctxVN
    (fun R hR hVR A hA hAN => hw.U_eq_Y hR hVR hA hAN)

end ZNW4

end CFSG.OddStandard.SmallF3.HarrisU33
