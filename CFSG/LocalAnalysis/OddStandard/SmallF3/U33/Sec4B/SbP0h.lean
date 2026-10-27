module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARem
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Prod
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Cm
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

section CenterO


theorem p0_center_O (hc : Ctx8e t L S x₁ x₂ lam rho tau) :
    ctxO t tau x₁ x₂ ⊓ centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) =
      fourGrp x₁ x₂ := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx4
  obtain ⟨hXel, -, hXcent, -⟩ := Ctx4.ctxX_facts hc4
  have hXR : ctxX t tau x₁ x₂ ≤ ctxR t tau x₁ x₂ := hc.X_le_R
  have hRO : ctxR t tau x₁ x₂ ≤ ctxO t tau x₁ x₂ := hc.R_le_O
  have hXO : ctxX t tau x₁ x₂ ≤ ctxO t tau x₁ x₂ := hXR.trans hRO
  have hVX : fourGrp x₁ x₂ ≤ ctxX t tau x₁ x₂ := by
    rw [fourGrp, ctxX]
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have hctX : closure {t, tau} ≤ ctxX t tau x₁ x₂ := by
    rw [ctxX]
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  have hVO : fourGrp x₁ x₂ ≤ ctxO t tau x₁ x₂ := by
    rw [hc.O_eq_C, le_inf_iff]
    refine ⟨hc.normal_V.1, ?_⟩
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact hXel.comm (hVX hw) (hVX hv)
  have hRcommV : ∀ k ∈ ctxR t tau x₁ x₂, ∀ v ∈ fourGrp x₁ x₂, k * v = v * k := by
    intro k hk v hv
    have hkM : k ∈ ctxM t tau x₁ x₂ ⊓
        centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
      rw [← hc.O_eq_C]; exact hRO hk
    exact ((Subgroup.mem_centralizer_iff.mp hkM.2) v hv).symm
  have hVcases : ∀ c ∈ closure {t, tau}, c ≠ 1 → c = t ∨ c = tau ∨ c = t * tau := by
    intro c hc_cl hc1
    have ht2 : t * t = 1 := S4A.t_mul_self hc.hyp
    have htau2 : tau * tau = 1 := by simpa [pow_two] using hc.l44.1
    have httau : t * tau = tau * t :=
      (S4A.mem_invCent_iff.mp (hc.le_invCent hc.tau_mem)).symm
    rcases (mem_closure_pair_of_invol ht2 htau2 httau).mp hc_cl with h1 | h1 | h1 | h1
    · exact absurd h1 hc1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  have hclass : ∀ c : G, c = t ∨ c = tau ∨ c = t * tau →
      conjIn (ctxR t tau x₁ x₂) c = c • (fourGrp x₁ x₂ : Set G) := by
    rintro c (rfl | rfl | rfl)
    · exact hc.tR
    · exact hc.tauR
    · exact hc.ttauR
  have hyV : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hy1 : x₁ ^ 2 ≠ 1 := by
    intro h
    have hd : orderOf x₁ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [hc.wreath.ord_x₁] at hd
    omega
  apply le_antisymm
  · intro g hg
    obtain ⟨-, hgC⟩ := hg
    have hgX : g ∈ ctxX t tau x₁ x₂ := by
      rw [← hXcent, Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp hgC) x (hXO hx)
    have hXsplit : ctxX t tau x₁ x₂ = closure {t, tau} ⊔ fourGrp x₁ x₂ := by
      rw [ctxX, fourGrp]
      rw [show ({t, tau, x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G) =
          {t, tau} ∪ {x₁ ^ 2, (x₁ * x₂) ^ 2} by
        ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
        tauto]
      rw [Subgroup.closure_union]
    have hKnorm : ∀ k ∈ fourGrp x₁ x₂, ∀ h ∈ closure {t, tau},
        k * h * k⁻¹ ∈ closure {t, tau} := by
      intro k hk h hh
      have hkh : k * h = h * k := hXel.comm (hVX hk) (hctX hh)
      rw [hkh, mul_assoc, mul_inv_cancel, mul_one]
      exact hh
    obtain ⟨c, hc_cl, v, hv_V, hg_eq⟩ :=
      (mem_sup_iff_of_normalizes hKnorm).mp (by rw [← hXsplit]; exact hgX)
    by_cases hc1 : c = 1
    · rw [hc1, one_mul] at hg_eq
      rw [hg_eq]; exact hv_V
    · exfalso
      have hcases : c = t ∨ c = tau ∨ c = t * tau := hVcases c hc_cl hc1
      have hfix : ∀ k ∈ ctxR t tau x₁ x₂, k * c * k⁻¹ = c := by
        intro k hk
        have hkv : k * v = v * k := hRcommV k hk v hv_V
        have hkg : k * g = g * k :=
          (Subgroup.mem_centralizer_iff.mp hgC) k (hRO hk)
        have hcg : c = g * v⁻¹ := by rw [hg_eq]; group
        calc k * c * k⁻¹ = k * (g * v⁻¹) * k⁻¹ := by rw [hcg]
          _ = (k * g * k⁻¹) * (k * v⁻¹ * k⁻¹) := by group
          _ = g * v⁻¹ := by
              have h1 : k * g * k⁻¹ = g := by rw [hkg]; group
              have h2 : k * v⁻¹ * k⁻¹ = v⁻¹ := by
                have h3 : k * v⁻¹ = v⁻¹ * k := by
                  exact ((show Commute k v from hkv).inv_right).eq
                rw [h3]; group
              rw [h1, h2]
          _ = c := by rw [hcg]
      have hmem : c * x₁ ^ 2 ∈ conjIn (ctxR t tau x₁ x₂) c := by
        rw [hclass c hcases]
        exact Set.smul_mem_smul_set hyV
      obtain ⟨k, hkR, hkc⟩ := hmem
      have hcx : c * x₁ ^ 2 = c := by rw [← hkc, hfix k hkR]
      exact hy1 (mul_left_cancel (a := c) (by simpa using hcx))
  · refine le_inf hVO ?_
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    have ho' : o ∈ ctxM t tau x₁ x₂ ⊓
        centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
      rw [← hc.O_eq_C]; exact ho
    exact ((Subgroup.mem_centralizer_iff.mp ho'.2) v hv).symm

end CenterO

theorem p0_perm_four_cent (σ : Equiv.Perm (Fin 4)) (hσ : orderOf σ = 3) (π : Equiv.Perm (Fin 4))
    (h : π * σ = σ * π) : π ∈ zpowers σ := by
  have key : ∀ σ π : Equiv.Perm (Fin 4), σ ^ 3 = 1 → σ ≠ 1 → π * σ = σ * π →
      π = 1 ∨ π = σ ∨ π = σ ^ 2 := by decide
  have hσ3 : σ ^ 3 = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [hσ] at this
  have hσ1 : σ ≠ 1 := by
    intro h1
    have : orderOf σ = 1 := by rw [h1, orderOf_one]
    rw [hσ] at this
    omega
  rcases key σ π hσ3 hσ1 h with h1 | h1 | h1
  · rw [h1]; exact Subgroup.one_mem _
  · rw [h1]; exact Subgroup.mem_zpowers σ
  · rw [h1]; exact Subgroup.npow_mem_zpowers σ 2

theorem p0_cent_L_tau_rho (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam} ⊓ centralizer ({rho} : Set G) = zpowers rho := by
  obtain ⟨φ⟩ := hc.perm_four
  let F : Subgroup G := L ⊓ centralizer ({tau} : Set G)
  have hF : closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam} = F := hc.cent_L_tau.symm
  have hrhoF : rho ∈ F :=
    ⟨hc.rho_mem, Subgroup.mem_centralizer_singleton_iff.mpr hc.tau_rho.symm⟩
  apply le_antisymm
  · intro g hg
    have hgF : g ∈ F := by rw [← hF]; exact hg.1
    have hgcomm : g * rho = rho * g :=
      Subgroup.mem_centralizer_singleton_iff.mp hg.2
    let r : ↥F := ⟨rho, hrhoF⟩
    let a : ↥F := ⟨g, hgF⟩
    have hrt : a * r = r * a := by
      apply Subtype.ext
      show g * rho = rho * g
      exact hgcomm
    have hcommφ : φ a * φ r = φ r * φ a := by
      rw [← map_mul, ← map_mul, hrt]
    have hord : orderOf (φ r) = 3 := by
      simp [r, hc.ord_rho]
    have hmem : φ a ∈ zpowers (φ r) := p0_perm_four_cent (φ r) hord (φ a) hcommφ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have hkr : r ^ k = a := φ.injective (by rw [map_zpow]; exact hk)
    have hcoe := congrArg (fun x : ↥F => (x : G)) hkr
    simpa [r, a] using hcoe
  · refine le_inf ?_ ?_
    · exact Subgroup.zpowers_le_of_mem (Subgroup.subset_closure (by simp))
    · exact Subgroup.zpowers_le_of_mem
        (Subgroup.mem_centralizer_singleton_iff.mpr rfl)

section CentTrho


theorem p0_cent_trho (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    ctxM t tau x₁ x₂ ⊓ centralizer ((closure {t, tau, rho} : Subgroup G) : Set G) =
      closure {t, tau, rho} := by
  obtain ⟨-, -, -, hcentMt⟩ := Ctx4.ctxX_facts hc
  have hXleM : ctxX t tau x₁ x₂ ≤ ctxM t tau x₁ x₂ := Subgroup.le_normalizer
  have htM : t ∈ ctxM t tau x₁ x₂ := hXleM (Subgroup.subset_closure (by simp))
  have htauM : tau ∈ ctxM t tau x₁ x₂ := hXleM (Subgroup.subset_closure (by simp))
  have hrhoM : rho ∈ ctxM t tau x₁ x₂ := by
    have hmem : rho ∈ invCent t ⊓ ctxM t tau x₁ x₂ := by
      rw [hcentMt]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    exact hmem.2
  obtain ⟨hcent, -, -, -, hcomm_ab⟩ := Ctx4.centralizer_t_tau hc
  have ht_tau : Commute t tau :=
    (S4A.mem_invCent_iff.mp (hc.le_invCent hc.tau_mem)).symm
  have ht_rho : Commute t rho :=
    (S4A.mem_invCent_iff.mp (S4A.L_le_invCent hc.hyp hc.rho_mem)).symm
  have htau_rho : Commute tau rho := hc.tau_rho
  have hpair : ({t, tau, rho} : Set G).Pairwise Commute := by
    intro a ha b hb hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact absurd rfl hab
    · exact ht_tau
    · exact ht_rho
    · exact ht_tau.symm
    · exact absurd rfl hab
    · exact htau_rho
    · exact ht_rho.symm
    · exact htau_rho.symm
    · exact absurd rfl hab
  haveI : IsMulCommutative (closure ({t, tau, rho} : Set G)) :=
    Subgroup.isMulCommutative_closure hpair
  have hleM : closure ({t, tau, rho} : Set G) ≤ ctxM t tau x₁ x₂ := by
    rw [Subgroup.closure_le]
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact htM
    · exact htauM
    · exact hrhoM
  have htt_sub : ({t, tau} : Set G) ⊆ {t, tau, rho} := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    rcases hz with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  apply le_antisymm
  · intro g hg
    obtain ⟨-, hgC⟩ := hg
    have hgC_tt : g ∈ centralizer ((closure {t, tau} : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp hgC) y ((Subgroup.closure_mono htt_sub) hy)
    have hg_sup : g ∈ closure {t, tau} ⊔ closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam} := by
      rw [← hcent]; exact hgC_tt
    have hKnorm : ∀ k ∈ closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam},
        ∀ h ∈ closure {t, tau}, k * h * k⁻¹ ∈ closure {t, tau} := by
      intro k hk h hh
      have hkh : k * h = h * k := (hcomm_ab h hh k hk).symm
      rw [hkh, mul_assoc, mul_inv_cancel, mul_one]
      exact hh
    obtain ⟨c, hc_cl, f, hf_K, hg_eq⟩ := (mem_sup_iff_of_normalizes hKnorm).mp hg_sup
    have hcr : Commute c rho := hcomm_ab c hc_cl rho (Subgroup.subset_closure (by simp))
    have hgr : g * rho = rho * g :=
      ((Subgroup.mem_centralizer_iff.mp hgC) rho
        (Subgroup.subset_closure (by simp))).symm
    have hf_comm : f * rho = rho * f := by
      have hf_eq : f = c⁻¹ * g := by rw [hg_eq]; group
      rw [hf_eq]
      calc c⁻¹ * g * rho = c⁻¹ * (g * rho) := by group
        _ = c⁻¹ * (rho * g) := by rw [hgr]
        _ = (c⁻¹ * rho) * g := by group
        _ = (rho * c⁻¹) * g := by rw [hcr.inv_left.eq]
        _ = rho * (c⁻¹ * g) := by group
    have hf_zp : f ∈ zpowers rho := by
      rw [← p0_cent_L_tau_rho hc]
      exact ⟨hf_K, Subgroup.mem_centralizer_singleton_iff.mpr hf_comm⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hf_zp
    rw [hg_eq, ← hk]
    exact Subgroup.mul_mem _ ((Subgroup.closure_mono htt_sub) hc_cl)
      (Subgroup.zpowers_le_of_mem (Subgroup.subset_closure (by simp))
        (Subgroup.zpow_mem_zpowers rho k))
  · intro x hx
    exact ⟨hleM hx, Subgroup.mem_centralizer_iff.mpr (fun y hy => setLike_mul_comm hy hx)⟩

end CentTrho

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
