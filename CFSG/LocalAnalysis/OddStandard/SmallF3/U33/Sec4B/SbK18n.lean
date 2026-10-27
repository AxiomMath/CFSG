module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP16g
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutAmbient

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private theorem k18n_mem_zpowers_of_sq_eq_one {a : G} (ha : a ^ 2 = 1) {x : G} :
    x ∈ zpowers a ↔ x = 1 ∨ x = a := by
  constructor
  · intro hx
    rw [Subgroup.mem_zpowers_iff] at hx
    obtain ⟨k, rfl⟩ := hx
    have hk : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by
      simpa using Int.emod_two_eq_zero_or_one k
    rcases hk with hk | hk
    · left
      rw [zpow_eq_zpow_emod' (x := a) (n := 2) k ha, hk]
      simp
    · right
      rw [zpow_eq_zpow_emod' (x := a) (n := 2) k ha, hk]
      simp
  · rintro (h1 | h2)
    · rw [h1]
      exact Subgroup.one_mem _
    · rw [h2]
      exact Subgroup.mem_zpowers a

theorem charIn_conj_mem {A B : Subgroup G} (hAB : CharIn A B) {h : G}
    (hh : h ∈ normalizer (B : Set G)) : ∀ a ∈ A, h * a * h⁻¹ ∈ A := by
  obtain ⟨hABle, hABchar⟩ := hAB
  intro a ha
  let φ : MulAut B := Outside.conjAut B h hh
  have hmap : (A.subgroupOf B).map φ.toMonoidHom = A.subgroupOf B :=
    (Subgroup.characteristic_iff_map_eq.mp hABchar) φ
  have hφ : φ ⟨a, hABle ha⟩ ∈ A.subgroupOf B := by
    have h1 : φ ⟨a, hABle ha⟩ ∈ (A.subgroupOf B).map φ.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨⟨a, hABle ha⟩, ha, rfl⟩
    rwa [hmap] at h1
  have hcoe : ((φ ⟨a, hABle ha⟩ : B) : G) = h * a * h⁻¹ :=
    Outside.conjAut_coe B h hh ⟨a, hABle ha⟩
  have := (Subgroup.mem_subgroupOf (H := A) (K := B)).mp hφ
  rwa [hcoe] at this

theorem k18_sylow_normalizes (hc : Ctx18S t L S x₁ x₂ lam rho tau om 𝒮) :
    (∀ k ∈ 𝒮, ∀ v ∈ fourGrp x₁ x₂, k * v * k⁻¹ ∈ fourGrp x₁ x₂) ∧
      ∀ k ∈ 𝒮, ∀ y ∈ ctxYq t tau x₁ x₂ rho, k * y * k⁻¹ ∈ ctxYq t tau x₁ x₂ rho := by
  refine ⟨?_, ?_⟩
  · intro k hk v hv
    exact k18_K_normalizes_V hc.toCtx13 k (hc.sylow.1 hk) v hv
  · intro k hk y hy
    exact l17_K_normalizes_Y hc.toCtx13 k (hc.sylow.1 hk) y hy

theorem k18_cent_V_eq (hc : Ctx18S t L S x₁ x₂ lam rho tau om 𝒮) :
    𝒮 ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) = ctxOK t tau x₁ x₂ rho := by
  have hc13 := hc.toCtx13
  have hlam2 : lam ^ 2 = 1 := (ctx13_lam_facts hc13).1
  have hOKcent : ctxOK t tau x₁ x₂ rho ≤
      centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hfix := k18_OK_cent_V hc13 n hn v hv
    have hnv : n * v = v * n := by
      calc n * v = (n * v * n⁻¹) * n := by group
        _ = v * n := by rw [hfix]
    exact hnv.symm
  refine le_antisymm ?_ (fun n hn => ⟨l18_OK_le_sylow hc hn, hOKcent hn⟩)
  intro x hx
  obtain ⟨hxS, hxC⟩ := Subgroup.mem_inf.mp hx
  have hnorm : ∀ k ∈ zpowers lam, ∀ h ∈ ctxOK t tau x₁ x₂ rho,
      k * h * k⁻¹ ∈ ctxOK t tau x₁ x₂ rho := by
    intro k hk h hh
    have hkK : k ∈ ctxK t tau x₁ x₂ rho :=
      Subgroup.zpowers_le.mpr (l17_mem_K hc13).2.2.2.1 hk
    exact (l18_OK_normal (t := t) (tau := tau) (x₁ := x₁) (x₂ := x₂)
      (rho := rho)).2 k hkK h hh
  have hxS' : x ∈ ctxOK t tau x₁ x₂ rho ⊔ zpowers lam := by
    rw [← k18_sylow_eq hc]
    exact hxS
  obtain ⟨n, hn, k, hk, rfl⟩ := (mem_sup_iff_of_normalizes hnorm).mp hxS'
  have hncent : n ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := hOKcent hn
  rcases (k18n_mem_zpowers_of_sq_eq_one (a := lam) hlam2).mp hk with hk1 | hkl
  · rw [hk1, mul_one]
    exact hn
  · exfalso
    have hkcent : k ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
      have h : n⁻¹ * (n * k) ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hncent) hxC
      simpa [mul_assoc] using h
    have hlamcent : lam ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
      rw [← hkl]
      exact hkcent
    have hyV : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
    have hcomm : x₁ ^ 2 * lam = lam * x₁ ^ 2 :=
      Subgroup.mem_centralizer_iff.mp hlamcent (x₁ ^ 2) hyV
    have hfix : lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 := by
      rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hz1 : (x₁ * x₂) ^ 2 = 1 := by
      have h := l17_lam_y hc13
      rw [hfix] at h
      exact mul_left_cancel (a := x₁ ^ 2) (by simpa using h.symm)
    exact (l17_yz_ne hc13).2.1 hz1

theorem k18_V_conj (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {h : G}
    (hh : ∀ q ∈ ctxQ t tau x₁ x₂ rho, h * q * h⁻¹ ∈ ctxQ t tau x₁ x₂ rho) :
    ∀ v ∈ fourGrp x₁ x₂, h * v * h⁻¹ ∈ fourGrp x₁ x₂ := by
  have hx₁Q : x₁ ∈ ctxQ t tau x₁ x₂ rho :=
    hc.base_le_Q (Subgroup.subset_closure (by simp))
  have hx₁x₂Q : x₁ * x₂ ∈ ctxQ t tau x₁ x₂ rho :=
    hc.base_le_Q (Subgroup.mul_mem _
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
  have hg₁ : h * x₁ ^ 2 * h⁻¹ ∈ fourGrp x₁ x₂ := by
    rw [← conj_pow (a := h) (b := x₁) (i := 2)]
    exact l17_Q_sq_mem hc _ (hh x₁ hx₁Q)
  have hg₂ : h * (x₁ * x₂) ^ 2 * h⁻¹ ∈ fourGrp x₁ x₂ := by
    rw [← conj_pow (a := h) (b := x₁ * x₂) (i := 2)]
    exact l17_Q_sq_mem hc _ (hh (x₁ * x₂) hx₁x₂Q)
  intro v hv
  induction hv using Subgroup.closure_induction with
  | mem g hg =>
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact hg₁
      · exact hg₂
  | one => simp
  | mul a b _ _ iha ihb =>
      rw [show h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) by group]
      exact Subgroup.mul_mem _ iha ihb
  | inv a _ iha =>
      rw [show h * a⁻¹ * h⁻¹ = (h * a * h⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ iha

theorem k18_normalizer_C_Q (hc : Ctx18A t L S x₁ x₂ lam rho tau om 𝒮) :
    ∀ h ∈ normalizer ((ctxCY t tau x₁ x₂ rho : Subgroup G) : Set G),
      ∀ q ∈ ctxQ t tau x₁ x₂ rho, h * q * h⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
  have hQchar : CharIn (ctxQ t tau x₁ x₂ rho)
      (ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G)) :=
    (lemma4_16_proof hc.toCtx13).2.1
  intro h hh q hq
  rw [k18A_C_eq hc] at hh
  exact charIn_conj_mem hQchar hh q hq

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
