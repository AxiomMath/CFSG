module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbU18b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Sub
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Cm

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private lemma t_cent_V (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ v ∈ fourGrp x₁ x₂, t * v = v * t := by
  intro v hv
  obtain ⟨htO, -, -⟩ := l17_mem_O hc
  have hvCent : v ∈ centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) := by
    have hmem : v ∈ ctxO t tau x₁ x₂ ⊓
        centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) := by
      rw [hc.center_O]; exact hv
    exact hmem.2
  exact Subgroup.mem_centralizer_iff.mp hvCent t htO

theorem l18_U_le_R (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {R A : Subgroup G}
    (hR : IsPGroup 2 R) (h𝒮R : 𝒮 ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) :
    A ≤ ctxR t tau x₁ x₂ := by
  intro x hx
  have hc13 : Ctx13 t L S x₁ x₂ lam rho tau om := hc.toCtx13
  obtain ⟨hVA, hcomm⟩ := l18_U_VA hc hR h𝒮R hA hAN
  set c := x * t * x⁻¹ * t⁻¹ with hcdef
  have hcV : c ∈ fourGrp x₁ x₂ := hcomm x hx
  have hct : x * t * x⁻¹ = c * t := by rw [hcdef]; group
  have hctc : c * t = t * c := ((t_cent_V hc13) c hcV).symm
  have hsm : x * t * x⁻¹ ∈ t • (fourGrp x₁ x₂ : Set G) := by
    rw [Set.mem_smul_set]
    refine ⟨c, hcV, ?_⟩
    change t * c = x * t * x⁻¹
    rw [← hctc, ← hct]
  rw [← hc13.tR] at hsm
  obtain ⟨r, hrR, hr⟩ := hsm
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
  have hSR : S ≤ R := ((l18_le_sylow hc.toCtx18S).2.2.1).trans h𝒮R
  have hsR : s ∈ R := by
    have hrR' : r ∈ R := h𝒮R ((l18_le_sylow hc.toCtx18S).2.2.2 hrR)
    show r⁻¹ * x ∈ R
    exact R.mul_mem (R.inv_mem hrR') (hA.1 hx)
  have hsS : s ∈ S := by
    have heq := c17_cent_eq hc.toCtx13.toCtx11.toCtx10 hR hSR
    have hmem : s ∈ R ⊓ centralizer ({t} : Set G) := ⟨hsR, hscent⟩
    rwa [heq] at hmem
  have hsV : s ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hrO : r ∈ ctxO t tau x₁ x₂ := hc13.R_le_O hrR
    have hvCent : v ∈ centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) := by
      have hmem : v ∈ ctxO t tau x₁ x₂ ⊓
          centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) := by
        rw [hc13.center_O]; exact hv
      exact hmem.2
    have hrv : r⁻¹ * v = v * r⁻¹ :=
      Subgroup.mem_centralizer_iff.mp hvCent r⁻¹ (Subgroup.inv_mem _ hrO)
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
    have heq := l18_U_CS_V hc hR h𝒮R hA hAN
    have hmem : s ∈ S ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := ⟨hsS, hsV⟩
    rwa [heq] at hmem
  have hQleR : ctxQ t tau x₁ x₂ rho ≤ ctxR t tau x₁ x₂ := by
    rw [hc13.R_eq]; exact le_sup_left
  have hsub : zpowers t ⊔ closure ({x₁, x₂, tau} : Set G) ≤ ctxR t tau x₁ x₂ := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact hc13.X_le_R (Subgroup.subset_closure (by simp))
    · rw [Subgroup.closure_le]
      rintro g (hg : g ∈ ({x₁, x₂, tau} : Set G))
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact hQleR (hc13.base_le_Q (Subgroup.subset_closure (by simp)))
      · exact hQleR (hc13.base_le_Q (Subgroup.subset_closure (by simp)))
      · exact hc13.X_le_R (Subgroup.subset_closure (by simp))
  have hsR' : s ∈ ctxR t tau x₁ x₂ := hsub hsint
  have hxrs : x = r * s := by dsimp only [s]; group
  rw [hxrs]
  exact (ctxR t tau x₁ x₂).mul_mem hrR hsR'

theorem l18_U_eq_Y (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {R A : Subgroup G}
    (hR : IsPGroup 2 R) (h𝒮R : 𝒮 ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) :
    A = ctxYq t tau x₁ x₂ rho := by
  have hc13 : Ctx13 t L S x₁ x₂ lam rho tau om := hc.toCtx13
  have hle : A ≤ ctxYq t tau x₁ x₂ rho := by
    intro x hx
    have hxR : x ∈ ctxR t tau x₁ x₂ := l18_U_le_R hc hR h𝒮R hA hAN hx
    have hclR : closure ({t, tau} : Set G) ≤ ctxR t tau x₁ x₂ := by
      rw [Subgroup.closure_le]
      rintro g (hg : g ∈ ({t, tau} : Set G))
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact hc13.X_le_R (Subgroup.subset_closure (by simp))
      · exact hc13.X_le_R (Subgroup.subset_closure (by simp))
    have hnorm : ∀ k ∈ closure ({t, tau} : Set G), ∀ h ∈ ctxQ t tau x₁ x₂ rho,
        k * h * k⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
      fun k hk h hh => l17_R_normalizes_Q hc13 k (hclR hk) h hh
    have hxQ : x ∈ ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G) := by
      rw [← l17_R_eq hc13]; exact hxR
    obtain ⟨q, hq, u, hu, hxqu⟩ :=
      (mem_sup_iff_of_normalizes (H := ctxQ t tau x₁ x₂ rho)
        (K := closure ({t, tau} : Set G)) hnorm).mp hxQ
    obtain ⟨ht2, -, -, htau2, -, httau, -⟩ := ctx13_relations hc13
    have hu4 := (mem_closure_pair_of_invol (by simpa [pow_two] using ht2)
      (by simpa [pow_two] using htau2) httau).mp hu
    have htR : t ∈ ctxR t tau x₁ x₂ :=
      hc13.X_le_R (Subgroup.subset_closure (by simp))
    have htauR : tau ∈ ctxR t tau x₁ x₂ :=
      hc13.X_le_R (Subgroup.subset_closure (by simp))
    rcases hu4 with h1 | h2 | h3 | h4
    · rw [h1] at hxqu
      rw [mem_ctxYq_iff hc13.q_iso]
      refine ⟨?_, hA.2.1.2 x hx⟩
      rw [hxqu]; simpa using hq
    · rw [h2] at hxqu
      exfalso
      have hq' : t⁻¹ * q * t ∈ ctxQ t tau x₁ x₂ rho := by
        simpa using l17_R_normalizes_Q hc13 t⁻¹ ((ctxR t tau x₁ x₂).inv_mem htR) q hq
      have hxeq : t * (t⁻¹ * q * t) = x := by rw [hxqu]; group
      have hmem : t * (t⁻¹ * q * t) ∈ A := by rw [hxeq]; exact hx
      exact (l18_U_tQ hc hR h𝒮R hA hAN hq').1 hmem
    · rw [h3] at hxqu
      exfalso
      have hq' : tau⁻¹ * q * tau ∈ ctxQ t tau x₁ x₂ rho := by
        simpa using l17_R_normalizes_Q hc13 tau⁻¹ ((ctxR t tau x₁ x₂).inv_mem htauR) q hq
      have hxeq : tau * (tau⁻¹ * q * tau) = x := by rw [hxqu]; group
      have hmem : tau * (tau⁻¹ * q * tau) ∈ A := by rw [hxeq]; exact hx
      exact (l18_U_tauQ hc hR h𝒮R hA hAN hq') hmem
    · rw [h4] at hxqu
      exfalso
      have hq' : (t * tau)⁻¹ * q * (t * tau) ∈ ctxQ t tau x₁ x₂ rho := by
        simpa using l17_R_normalizes_Q hc13 (t * tau)⁻¹
          ((ctxR t tau x₁ x₂).inv_mem ((ctxR t tau x₁ x₂).mul_mem htR htauR)) q hq
      have hxeq : (t * tau) * ((t * tau)⁻¹ * q * (t * tau)) = x := by
        rw [hxqu]; group
      have hmem : (t * tau) * ((t * tau)⁻¹ * q * (t * tau)) ∈ A := by
        rw [hxeq]; exact hx
      exact (l18_U_tQ hc hR h𝒮R hA hAN hq').2 hmem
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [l17_card_Y hc13, hA.2.2])

theorem l18_Y_normal_all (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) :
    ∀ R : Subgroup G, IsPGroup 2 R → 𝒮 ≤ R → NormalIn (ctxYq t tau x₁ x₂ rho) R := by
  exact normalIn_of_unique_normal_E16 (l18_Y_E16 hc.toCtx18S) (l18_Y_normal_sylow hc.toCtx18S)
    (fun R hR h𝒮R A hA hAN => l18_U_eq_Y hc hR h𝒮R hA hAN)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
