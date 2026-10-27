module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2BigA

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

local notation "β₀" => w ^ (orderOf w / 2) * t ^ i * z ^ j

theorem Setting46e.card_sup_beta_z (hs : Setting46e t L p f S w z V i j) :
    Nat.card ↥(zpowers β₀ ⊔ zpowers z) = 4 := by
  have hβ2 : β₀ * β₀ = 1 := by rw [← sq]; exact hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
  have hz2 : z * z = 1 := by rw [← sq, ← hs.setup.z_order, pow_orderOf_eq_one]
  have hzβ : z ∉ zpowers β₀ := fun h => by
    rcases L415.mem_zpowers_two hβ2 h with h1 | h1
    · exact hs.setup.z_ne_one h1
    · exact hs.setup.beta_ne_z hs.beta h1.symm
  have hβzc : β₀ * z = z * β₀ :=
    (mem_centralizer_singleton_iff.mp (K_le_centralizer_beta i j hs.lemma45.z_mem.2)).symm
  obtain ⟨-, -, h⟩ := L415.elem_sup (L415.elem_zpowers hβ2).1 (L415.elem_zpowers hβ2).2 hz2
    hzβ fun a ha => by
      rcases L415.mem_zpowers_two hβ2 ha with rfl | rfl
      · group
      · exact hβzc
  rw [h, L415.card_zpowers_two hβ2 hs.beta.ne_one]

namespace EndB.L2Ctx

variable {hs : Setting46e t L p f S w z V i j} {W : Subgroup X}

local notation "Q₀" => qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W
local notation "A₀" => (qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ zpowers z : Subgroup X)

theorem exists_normal_z (hKC : AutPSL2CentralizerInput) (hc : L2Ctx hs W) {Y : Subgroup X}
    (hYW : Y ≤ W) (hYn : ∀ g ∈ W, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) (hY2 : ∀ y ∈ Y, y * y = 1)
    (hY8 : 8 ≤ Nat.card Y) :
    ∃ Y₀ : Subgroup X, Y₀ ≤ W ∧ (∀ g ∈ W, ∀ y ∈ Y₀, g * y * g⁻¹ ∈ Y₀) ∧
      (∀ y ∈ Y₀, y * y = 1) ∧ z ∈ Y₀ ∧ 8 ≤ Nat.card Y₀ := by
  by_cases hz : z ∈ Y
  · exact ⟨Y, hYW, hYn, hY2, hz, hY8⟩
  have hz2 : z * z = 1 := by rw [← sq, ← hs.setup.z_order, pow_orderOf_eq_one]
  obtain ⟨-, h2, h3⟩ := L415.elem_sup (fun a ha b hb => EndB.comm_of_sq hY2 ha hb) hY2 hz2 hz
    (fun a ha => hc.z_comm hKC (hYW ha))
  refine ⟨Y ⊔ zpowers z, sup_le hYW (zpowers_le.mpr hc.z_mem_W), ?_, h2,
    mem_sup_right (mem_zpowers z), by rw [h3]; omega⟩
  intro g hg y hy
  have hle : (Y ⊔ zpowers z).map (MulAut.conj g).toMonoidHom ≤ Y ⊔ zpowers z := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨b, hb, rfl⟩
      exact hYn g hg b hb
    · rw [MonoidHom.map_zpowers]
      have : (MulAut.conj g).toMonoidHom z = z := by
        show g * z * g⁻¹ = z
        rw [hc.z_comm hKC hg]
        group
      rw [this]
  exact hle ⟨y, hy, rfl⟩

theorem qTilde_sq_of_normal (hKG : AutPSL2SylowInput) (hKC : AutPSL2CentralizerInput)
    (hFC : AutPSL2FieldCentralizerInput) (hc : L2Ctx hs W)
    (hnc : ¬ IsCyclic ↥(pCore 2 (MBar β₀))) {Y : Subgroup X} (hYW : Y ≤ W)
    (hYn : ∀ g ∈ W, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) (hY2 : ∀ y ∈ Y, y * y = 1)
    (hY8 : 8 ≤ Nat.card Y) : ∀ q ∈ Q₀, q * q = 1 := by
  by_contra hno
  push Not at hno
  obtain ⟨q', hq', hq'2⟩ := hno
  obtain ⟨r, hr, hr4, hr2, hrQ⟩ := hc.exists_r hq' hq'2
  obtain ⟨Y₀, hY₀W, hY₀n, hY₀2, hzY₀, hY₀8⟩ := hc.exists_normal_z hKC hYW hYn hY2 hY8
  have hY₀N := hc.le_N0_of_normal hKG hKC hFC hY₀W hY₀n hY₀2
  have ht2 : t * t = 1 := by rw [← sq, ← hs.standing.config.orderOf_eq, pow_orderOf_eq_one]
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  by_cases hcase : ∃ q ∈ Y₀ ⊓ Q₀, q ∉ zpowers β₀
  · obtain ⟨q, ⟨hqY, hqQ⟩, hqb⟩ := hcase
    have hq2 := hY₀2 q hqY
    have hqi : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq2
    have hq'Y : t * q * t⁻¹ ∈ Y₀ := hY₀n t hc.t_mem_W q hqY
    have hcomm : q * (t * q * t) = (t * q * t) * q := by
      have := EndB.comm_of_sq hY₀2 hqY hq'Y
      rwa [hti] at this
    have hcQ : t * q * t⁻¹ * q⁻¹ ∈ Q₀ := mul_mem (hc.qTilde_normal hc.t_mem_W hqQ) (inv_mem hqQ)
    have hcC : t * q * t⁻¹ * q⁻¹ ∈ centralizer ({t} : Set X) := by
      rw [mem_centralizer_singleton_iff, hti, hqi]
      calc t * q * t * q * t = (t * q * t) * q * t := by group
        _ = q * (t * q * t) * t := by rw [hcomm]
        _ = q * t * q * (t * t) := by group
        _ = (t * t) * (q * t * q) := by rw [ht2, one_mul, mul_one]
        _ = t * (t * q * t * q) := by group
    have htq : t * q * t⁻¹ * q⁻¹ ∈ zpowers β₀ := by
      have : t * q * t⁻¹ * q⁻¹ ∈ Q₀ ⊓ centralizer ({t} : Set X) := ⟨hcQ, hcC⟩
      rwa [hc.qTilde_inf_centralizer] at this
    have hqr : q ∉ zpowers r := fun h => by
      rcases L415.eq_of_mem_zpowers_sq (by norm_num : 1 ≤ 2) (by rw [hr4]; norm_num) h
        (by rw [sq, hq2]) with h1 | h1
      · exact hqb (h1 ▸ one_mem _)
      · apply hqb
        rw [h1, show (2 : ℕ) ^ (2 - 1) = 2 by norm_num, hr2]
        exact mem_zpowers _
    exact hc.false_of_central hr hr4 hr2 hrQ hqQ hqr htq
  push Not at hcase
  have hYA : ¬ Y₀ ≤ A₀ := by
    intro hle
    have hsub : Y₀ ≤ zpowers β₀ ⊔ zpowers z := fun a ha => by
      obtain ⟨q, hq, e | e⟩ := hc.mem_A_cases hKC (hle ha)
      · rw [e] at ha ⊢
        exact mem_sup_left (hcase q ⟨ha, hq⟩)
      · rw [e] at ha ⊢
        have hqY : q ∈ Y₀ := by
          have := mul_mem ha (inv_mem hzY₀)
          rwa [mul_inv_cancel_right] at this
        exact mul_mem (mem_sup_left (hcase q ⟨hqY, hq⟩)) (mem_sup_right (mem_zpowers z))
    have h1 := Subgroup.card_le_of_le hsub
    rw [hs.card_sup_beta_z] at h1
    omega
  obtain ⟨y, hyY, hyA⟩ := Set.not_subset.mp hYA
  obtain ⟨a, haA, rfl⟩ : ∃ a ∈ A₀, y = t * a := by
    rcases hc.mem_A_or_of_mem_N0 hKC (hY₀N hyY) with h | h
    · exact absurd h hyA
    · exact h
  obtain ⟨q₁, hq₁, ha1⟩ := hc.mem_A_cases hKC haA
  have hy' : t * q₁ ∈ Y₀ := by
    rcases ha1 with e | e
    · rw [e] at hyY
      exact hyY
    · rw [e] at hyY
      have := mul_mem hyY (inv_mem hzY₀)
      rwa [show t * (q₁ * z) * z⁻¹ = t * q₁ by group] at this
  have hy'W : t * q₁ ∈ W := mul_mem hc.t_mem_W (hc.qTilde_le hq₁)
  have hP : ∀ q ∈ Q₀, (t * q₁) * q * (t * q₁)⁻¹ * q⁻¹ ∈ zpowers β₀ := by
    intro q hq
    refine hcase _ (Subgroup.mem_inf.mpr ⟨?_, mul_mem (hc.qTilde_normal hy'W hq) (inv_mem hq)⟩)
    have h1 := hY₀n q (hc.qTilde_le hq) _ (inv_mem hy')
    have e : (t * q₁) * q * (t * q₁)⁻¹ * q⁻¹ = (t * q₁) * (q * (t * q₁)⁻¹ * q⁻¹) := by group
    rw [e]
    exact mul_mem hy' h1
  by_cases hq₁r : q₁ ∈ zpowers r
  · have hPq := hc.central_of_mem_zpowers (hc.qTilde_le hr) (hc.central_r hr hr4 hr2 hrQ)
      (inv_mem hq₁r)
    have hPt := hc.central_mul hy'W hP hPq
    rw [show t * q₁ * q₁⁻¹ = t by group] at hPt
    have hnle : ¬ Q₀ ≤ zpowers r := fun hle => by
      have heq : Q₀ = zpowers r := le_antisymm hle (zpowers_le.mpr hr)
      have hcyc : IsCyclic ↥(Q₀) := by rw [heq]; infer_instance
      exact hnc (isCyclic_of_surjective hc.qTildeEquiv.toMonoidHom hc.qTildeEquiv.surjective)
    obtain ⟨q, hq, hqr⟩ := Set.not_subset.mp hnle
    exact hc.false_of_central hr hr4 hr2 hrQ hq hqr (hPt q hq)
  · have h1 := hP q₁ hq₁
    rw [show (t * q₁) * q₁ * (t * q₁)⁻¹ * q₁⁻¹ = t * q₁ * t⁻¹ * q₁⁻¹ by group] at h1
    exact hc.false_of_central hr hr4 hr2 hrQ hq₁ hq₁r h1

end EndB.L2Ctx

end CFSG.ComponentClassification.HarrisLit
