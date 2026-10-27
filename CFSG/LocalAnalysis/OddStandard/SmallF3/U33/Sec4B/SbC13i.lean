module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13h
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13V0
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G}

private lemma conj_three_eq_self {g x : G} (hg : g ^ 3 = 1) :
    g * (g * (g * x * g⁻¹) * g⁻¹) * g⁻¹ = x := by
  have h : g * (g * (g * x * g⁻¹) * g⁻¹) * g⁻¹ =
      (g * (g * g)) * x * (g * (g * g))⁻¹ := by group
  rw [h, ← pow_three, hg]
  simp

private lemma conj_two_eq_self {g x : G} (hg : g * g = 1) :
    g * (g * x * g⁻¹) * g⁻¹ = x := by
  have h : g * (g * x * g⁻¹) * g⁻¹ = (g * g) * x * (g * g)⁻¹ := by group
  rw [h, hg]
  simp

private lemma sigma_comm_t (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    (lam * t) * t = t * (lam * t) := by
  have ht2 : t * t = 1 := S4A.t_mul_self hc.hyp
  have hlt : lam * t = t * lam := (c13_lam_data hc.toCtx11).2.2.1
  have e1 : (lam * t) * t = lam := by rw [mul_assoc, ht2, mul_one]
  have e2 : t * (lam * t) = lam := by
    rw [← mul_assoc, hlt.symm, mul_assoc, ht2, mul_one]
  rw [e1, e2]

private lemma cmap_sigma (hc : Ctx13C t L S x₁ x₂ lam rho tau om) (a : G) :
    ((lam * t) * a * (lam * t)⁻¹) *
        (t * ((lam * t) * a * (lam * t)⁻¹) * t⁻¹) =
      (lam * t) * (a * (t * a * t⁻¹)) * (lam * t)⁻¹ := by
  have hσt : (lam * t) * t = t * (lam * t) := sigma_comm_t hc
  have h1 : t * ((lam * t) * a * (lam * t)⁻¹) * t⁻¹ =
      (lam * t) * (t * a * t⁻¹) * (lam * t)⁻¹ := by
    have h : t * ((lam * t) * a * (lam * t)⁻¹) * t⁻¹ =
        (t * (lam * t)) * a * (t * (lam * t))⁻¹ := by group
    rw [h, ← hσt]
    group
  rw [h1]
  group

theorem c13_V'_props (hc : Ctx13C t L S x₁ x₂ lam rho tau om) {v₀ : G}
    (hv₀Y : v₀ ∈ ctxYq t tau x₁ x₂ rho) (hv₀V : v₀ ∉ fourGrp x₁ x₂)
    (hσ : (lam * t) * v₀ * (lam * t)⁻¹ = v₀) :
    orbitGrp rho v₀ ≤ ctxYq t tau x₁ x₂ rho ∧
      CFSG.Open.IsElemAbelian 2 (orbitGrp rho v₀) ∧ Nat.card ↥(orbitGrp rho v₀) = 4 ∧
      rho ∈ normalizer ((orbitGrp rho v₀ : Subgroup G) : Set G) ∧
      lam * t ∈ normalizer ((orbitGrp rho v₀ : Subgroup G) : Set G) ∧
      orbitGrp rho v₀ ⊓ fourGrp x₁ x₂ = ⊥ ∧
      fourGrp x₁ x₂ ⊔ orbitGrp rho v₀ = ctxYq t tau x₁ x₂ rho ∧
      orbitGrp rho v₀ ⊓ centralizer ({lam * t} : Set G) = zpowers v₀ := by
  have hY : CFSG.Open.IsElemAbelian 2 (ctxYq t tau x₁ x₂ rho) := hc.Y_elem
  have hρ3 : rho ^ 3 = 1 := hc.fpf_YV.rho3
  have hρY : ∀ x ∈ ctxYq t tau x₁ x₂ rho, rho * x * rho⁻¹ ∈ ctxYq t tau x₁ x₂ rho :=
    hc.fpf_YV.rhoP
  have hfix : ∀ x ∈ ctxYq t tau x₁ x₂ rho, rho * x * rho⁻¹ = x → x = 1 :=
    hc.fpf_YV.fix
  have hVρ : ∀ x ∈ fourGrp x₁ x₂, rho * x * rho⁻¹ ∈ fourGrp x₁ x₂ := hc.fpf_YV.rhoQ
  have hv₁ : v₀ ≠ 1 := by
    intro h
    exact hv₀V (by rw [h]; exact Subgroup.one_mem _)
  have hσ2 : (lam * t) * (lam * t) = 1 := (c13_sigma_data hc.toCtx11).2.1
  have hσρ : (lam * t) * rho * (lam * t)⁻¹ = rho⁻¹ :=
    (c13_sigma_data hc.toCtx11).2.2.2.1
  obtain ⟨hle, hea, hcard⟩ := orbitGrp_props hY hρ3 hρY hfix hv₀Y hv₁
  obtain ⟨hσstab, hcent⟩ := orbitGrp_sigma hY hρ3 hρY hfix hv₀Y hv₁ hσ hσρ
  have hrhoN : rho ∈ normalizer ((orbitGrp rho v₀ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => orbitGrp_inv hY hρ3 hρY hfix hv₀Y x hx, fun hx => by
      have h1 := orbitGrp_inv hY hρ3 hρY hfix hv₀Y (rho * x * rho⁻¹) hx
      have h2 := orbitGrp_inv hY hρ3 hρY hfix hv₀Y _ h1
      rwa [conj_three_eq_self hρ3] at h2⟩
  have hσN : lam * t ∈ normalizer ((orbitGrp rho v₀ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => hσstab x hx, fun hx => by
      have h1 := hσstab _ hx
      rwa [conj_two_eq_self hσ2] at h1⟩
  have hinf : orbitGrp rho v₀ ⊓ fourGrp x₁ x₂ = ⊥ := by
    rw [inf_comm]
    exact orbitGrp_inf hY hρ3 hρY hfix hv₀Y hVρ hv₀V
  have hsup : fourGrp x₁ x₂ ⊔ orbitGrp rho v₀ = ctxYq t tau x₁ x₂ rho := by
    have hHK : ∀ h ∈ fourGrp x₁ x₂, ∀ k ∈ orbitGrp rho v₀, h * k = k * h :=
      fun h hh k hk =>
        hc.Q_comm h (ctxYq_le_ctxQ (hc.V_le_Y hh)) k (ctxYq_le_ctxQ (hle hk))
    have hVcard : Nat.card (fourGrp x₁ x₂) = 4 := hc.wreath.fourGrp_eq_omega.2.2
    refine Subgroup.eq_of_le_of_card_ge (sup_le hc.V_le_Y hle) ?_
    have h2 : Nat.card ↥(fourGrp x₁ x₂ ⊔ orbitGrp rho v₀) = 16 := by
      have h := card_sup_mul_card_inf (H := fourGrp x₁ x₂) (K := orbitGrp rho v₀) hHK
      have hinf' : Nat.card ↥(fourGrp x₁ x₂ ⊓ orbitGrp rho v₀) = 1 := by
        rw [orbitGrp_inf hY hρ3 hρY hfix hv₀Y hVρ hv₀V, Subgroup.card_bot]
      rw [hinf', mul_one, hVcard, hcard] at h
      norm_num at h
      exact h
    rw [card_ctxYq hc.q_iso, h2]
  exact ⟨hle, hea, hcard, hrhoN, hσN, hinf, hsup, hcent⟩

theorem c13_v0_t (hc : Ctx13C t L S x₁ x₂ lam rho tau om) {v₀ : G}
    (hv₀Y : v₀ ∈ ctxYq t tau x₁ x₂ rho) (hv₀V : v₀ ∉ fourGrp x₁ x₂)
    (hσ : (lam * t) * v₀ * (lam * t)⁻¹ = v₀) :
    t * v₀ * t⁻¹ = v₀ * (x₁ * x₂) ^ 2 := by
  have hv₀sq : v₀ * v₀ = 1 := by
    have h := hc.Y_elem.2 v₀ hv₀Y
    simpa [pow_two] using h
  have hcmem : v₀ * (t * v₀ * t⁻¹) ∈ fourGrp x₁ x₂ := c13_cmap_mem hc v₀ hv₀Y
  have hcfix : (lam * t) * (v₀ * (t * v₀ * t⁻¹)) * (lam * t)⁻¹ =
      v₀ * (t * v₀ * t⁻¹) := by
    have hσt : (lam * t) * t = t * (lam * t) := sigma_comm_t hc
    have h : (lam * t) * (v₀ * (t * v₀ * t⁻¹)) * (lam * t)⁻¹ =
        ((lam * t) * v₀ * (lam * t)⁻¹) *
          (((lam * t) * t) * v₀ * ((lam * t) * t)⁻¹) := by group
    rw [h, hσ, hσt]
    rw [show (t * (lam * t)) * v₀ * (t * (lam * t))⁻¹ =
        t * ((lam * t) * v₀ * (lam * t)⁻¹) * t⁻¹ by group, hσ]
  rcases c13_CV_sigma hc.toCtx11 (v₀ * (t * v₀ * t⁻¹)) hcmem hcfix with h | h
  · exact absurd ((c13_cmap_eq_one hc v₀ hv₀Y).mp h) hv₀V
  · have hmain : t * v₀ * t⁻¹ = v₀⁻¹ * (x₁ * x₂) ^ 2 := by
      rw [← h]
      group
    have hvinv : v₀⁻¹ = v₀ := inv_eq_of_mul_eq_one_right hv₀sq
    rw [hvinv] at hmain
    exact hmain

theorem c13_exists_v2 (hc : Ctx13C t L S x₁ x₂ lam rho tau om) {v₀ : G}
    (hv₀Y : v₀ ∈ ctxYq t tau x₁ x₂ rho) (hv₀V : v₀ ∉ fourGrp x₁ x₂)
    (hσ : (lam * t) * v₀ * (lam * t)⁻¹ = v₀) :
    ∃ v₂ ∈ orbitGrp rho v₀, t * v₂ * t⁻¹ = v₂ * x₁ ^ 2 := by
  obtain ⟨hV'Y, hV'ea, hV'card, -, -, -, hsup, -⟩ := c13_V'_props hc hv₀Y hv₀V hσ
  have hyV : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  obtain ⟨a, haY, hac⟩ := c13_cmap_surj hc (x₁ ^ 2) hyV
  have ha : a ∈ fourGrp x₁ x₂ ⊔ orbitGrp rho v₀ := by rw [hsup]; exact haY
  have hHK : ∀ h ∈ fourGrp x₁ x₂, ∀ k ∈ orbitGrp rho v₀, h * k = k * h :=
    fun h hh k hk =>
      hc.Q_comm h (ctxYq_le_ctxQ (hc.V_le_Y hh)) k (ctxYq_le_ctxQ (hV'Y hk))
  obtain ⟨v, hv, w, hw, haw⟩ := exists_mul_of_sup hHK ha
  have hvY : v ∈ ctxYq t tau x₁ x₂ rho := hc.V_le_Y hv
  have hwY : w ∈ ctxYq t tau x₁ x₂ rho := hV'Y hw
  have hmul := c13_cmap_mul hc v hvY w hwY
  have hcv : v * (t * v * t⁻¹) = 1 := (c13_cmap_eq_one hc v hvY).mpr hv
  have hac' : (v * w) * (t * (v * w) * t⁻¹) = x₁ ^ 2 := by rw [← haw]; exact hac
  have hcw : w * (t * w * t⁻¹) = x₁ ^ 2 := by
    rw [hmul, hcv, one_mul] at hac'
    exact hac'
  refine ⟨w, hw, ?_⟩
  have htw : t * w * t⁻¹ = w⁻¹ * x₁ ^ 2 := by
    rw [← hcw]
    group
  have hw2 : w * w = 1 := by
    have h := hV'ea.2 w hw
    simpa [pow_two] using h
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  rw [htw, hwinv]

theorem c13_sigma_v2 (hc : Ctx13C t L S x₁ x₂ lam rho tau om) {v₀ v₂ : G}
    (hv₀Y : v₀ ∈ ctxYq t tau x₁ x₂ rho) (hv₀V : v₀ ∉ fourGrp x₁ x₂)
    (hσ : (lam * t) * v₀ * (lam * t)⁻¹ = v₀) (hv₂ : v₂ ∈ orbitGrp rho v₀)
    (ht : t * v₂ * t⁻¹ = v₂ * x₁ ^ 2) :
    (lam * t) * v₂ * (lam * t)⁻¹ = v₂ * v₀ := by
  obtain ⟨hV'Y, hV'ea, hV'card, -, hσN, hinf, -, -⟩ := c13_V'_props hc hv₀Y hv₀V hσ
  have hσy : (lam * t) * x₁ ^ 2 * (lam * t)⁻¹ = x₁ ^ 2 * (x₁ * x₂) ^ 2 :=
    (c13_sigma_V hc.toCtx11).1
  have hv₂Y : v₂ ∈ ctxYq t tau x₁ x₂ rho := hV'Y hv₂
  have hv₀sq : v₀ * v₀ = 1 := by
    have h := hc.Y_elem.2 v₀ hv₀Y
    simpa [pow_two] using h
  have hv₂sq : v₂ * v₂ = 1 := by
    have h := hc.Y_elem.2 v₂ hv₂Y
    simpa [pow_two] using h
  have huV' : (lam * t) * v₂ * (lam * t)⁻¹ ∈ orbitGrp rho v₀ :=
    (Subgroup.mem_normalizer_iff.mp hσN v₂).mp hv₂
  have huY : (lam * t) * v₂ * (lam * t)⁻¹ ∈ ctxYq t tau x₁ x₂ rho := hV'Y huV'
  have hu'V' : v₂ * v₀ ∈ orbitGrp rho v₀ :=
    (orbitGrp rho v₀).mul_mem hv₂ (Subgroup.subset_closure (by simp))
  have hu'Y : v₂ * v₀ ∈ ctxYq t tau x₁ x₂ rho := hV'Y hu'V'
  have hcv₀ : v₀ * (t * v₀ * t⁻¹) = (x₁ * x₂) ^ 2 := by
    rw [c13_v0_t hc hv₀Y hv₀V hσ, ← mul_assoc, hv₀sq, one_mul]
  have hcv₂ : v₂ * (t * v₂ * t⁻¹) = x₁ ^ 2 := by
    rw [ht, ← mul_assoc, hv₂sq, one_mul]
  have hcu : ((lam * t) * v₂ * (lam * t)⁻¹) *
      (t * ((lam * t) * v₂ * (lam * t)⁻¹) * t⁻¹) = x₁ ^ 2 * (x₁ * x₂) ^ 2 := by
    rw [cmap_sigma hc v₂, hcv₂, hσy]
  have hcu' : (v₂ * v₀) * (t * (v₂ * v₀) * t⁻¹) = x₁ ^ 2 * (x₁ * x₂) ^ 2 := by
    rw [c13_cmap_mul hc v₂ hv₂Y v₀ hv₀Y, hcv₂, hcv₀]
  have hyz : (x₁ ^ 2 * (x₁ * x₂) ^ 2) * (x₁ ^ 2 * (x₁ * x₂) ^ 2) = 1 := by
    have hmem : x₁ ^ 2 * (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ :=
      Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    have h := hc.Y_elem.2 _ (hc.V_le_Y hmem)
    simpa [pow_two] using h
  have hmemY : ((lam * t) * v₂ * (lam * t)⁻¹) * (v₂ * v₀) ∈ ctxYq t tau x₁ x₂ rho :=
    (ctxYq t tau x₁ x₂ rho).mul_mem huY hu'Y
  have hcprod : ((lam * t) * v₂ * (lam * t)⁻¹) * (v₂ * v₀) *
      (t * (((lam * t) * v₂ * (lam * t)⁻¹) * (v₂ * v₀)) * t⁻¹) = 1 := by
    rw [c13_cmap_mul hc _ huY (v₂ * v₀) hu'Y, hcu, hcu']
    exact hyz
  have hmemV : ((lam * t) * v₂ * (lam * t)⁻¹) * (v₂ * v₀) ∈ fourGrp x₁ x₂ :=
    (c13_cmap_eq_one hc _ hmemY).mp hcprod
  have hmemV' : ((lam * t) * v₂ * (lam * t)⁻¹) * (v₂ * v₀) ∈ orbitGrp rho v₀ :=
    (orbitGrp rho v₀).mul_mem huV' hu'V'
  have hbot : ((lam * t) * v₂ * (lam * t)⁻¹) * (v₂ * v₀) ∈ (⊥ : Subgroup G) := by
    rw [← hinf]
    exact ⟨hmemV', hmemV⟩
  have hone : ((lam * t) * v₂ * (lam * t)⁻¹) * (v₂ * v₀) = 1 := Subgroup.mem_bot.mp hbot
  have heq : (lam * t) * v₂ * (lam * t)⁻¹ = (v₂ * v₀)⁻¹ := eq_inv_of_mul_eq_one_left hone
  have hu'inv : (v₂ * v₀)⁻¹ = v₂ * v₀ := by
    have h2 : (v₂ * v₀) * (v₂ * v₀) = 1 := by
      have h := hV'ea.2 (v₂ * v₀) hu'V'
      simpa [pow_two] using h
    exact inv_eq_of_mul_eq_one_right h2
  rw [heq, hu'inv]

theorem c13_v2_facts (hc : Ctx13C t L S x₁ x₂ lam rho tau om) {v₀ v₂ : G}
    (hv₀Y : v₀ ∈ ctxYq t tau x₁ x₂ rho) (hv₀V : v₀ ∉ fourGrp x₁ x₂)
    (hσ : (lam * t) * v₀ * (lam * t)⁻¹ = v₀) (hv₂ : v₂ ∈ orbitGrp rho v₀)
    (ht : t * v₂ * t⁻¹ = v₂ * x₁ ^ 2) :
    v₂ ∉ zpowers v₀ ∧ orbitGrp rho v₀ = closure ({v₀, v₂} : Set G) := by
  obtain ⟨hV'Y, hV'ea, hV'card, -, -, -, -, -⟩ := c13_V'_props hc hv₀Y hv₀V hσ
  have hv₀sq : v₀ * v₀ = 1 := by
    have h := hc.Y_elem.2 v₀ hv₀Y
    simpa [pow_two] using h
  have hv₂sq : v₂ * v₂ = 1 := by
    have h := hc.Y_elem.2 v₂ (hV'Y hv₂)
    simpa [pow_two] using h
  have hv₁ : v₀ ≠ 1 := by
    intro h
    exact hv₀V (by rw [h]; exact Subgroup.one_mem _)
  have hzp : ∀ x ∈ zpowers v₀, x = 1 ∨ x = v₀ := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h2 : v₀ ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two, hv₀sq]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [← Int.emod_add_mul_ediv k 2, h, zero_add, zpow_mul, h2, one_zpow]
    · right
      rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul, h2, one_zpow, mul_one,
        zpow_one]
  have hnotzp : v₂ ∉ zpowers v₀ := by
    intro hmem
    have hcv₂ : v₂ * (t * v₂ * t⁻¹) = x₁ ^ 2 := by
      rw [ht, ← mul_assoc, hv₂sq, one_mul]
    rcases hzp v₂ hmem with h | h
    · rw [h] at hcv₂
      simp at hcv₂
      exact (c13_V_ne hc.toCtx11).1 hcv₂.symm
    · rw [h] at hcv₂
      rw [c13_v0_t hc hv₀Y hv₀V hσ, ← mul_assoc, hv₀sq, one_mul] at hcv₂
      exact (c13_V_ne hc.toCtx11).2.2 hcv₂.symm
  refine ⟨hnotzp, ?_⟩
  have hcl_le : closure ({v₀, v₂} : Set G) ≤ orbitGrp rho v₀ := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases (by simpa using hx) with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact hv₂
  have hcard2 : Nat.card ↥(zpowers v₀) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by simpa [pow_two] using hv₀sq) hv₁
  have hlt : zpowers v₀ < closure ({v₀, v₂} : Set G) := by
    refine lt_of_le_of_ne ?_ ?_
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    · intro heq
      have hmem : v₂ ∈ closure ({v₀, v₂} : Set G) := Subgroup.subset_closure (by simp)
      rw [← heq] at hmem
      exact hnotzp hmem
  have hcard : Nat.card ↥(orbitGrp rho v₀) ≤ Nat.card ↥(closure ({v₀, v₂} : Set G)) := by
    rw [hV'card]
    have htwo := two_mul_card_le_of_lt hlt
    rw [hcard2] at htwo
    norm_num at htwo
    exact htwo
  exact (Subgroup.eq_of_le_of_card_ge hcl_le hcard).symm

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
