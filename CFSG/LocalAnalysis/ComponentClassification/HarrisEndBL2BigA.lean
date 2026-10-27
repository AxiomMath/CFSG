module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2E4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Q

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

local notation "β₀" => w ^ (orderOf w / 2) * t ^ i * z ^ j

namespace EndB.L2Ctx

variable {hs : Setting46e t L p f S w z V i j} {W : Subgroup X}

local notation "Q₀" => qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W

theorem exists_r (hc : L2Ctx hs W) {q : X} (hq : q ∈ Q₀) (hq2 : q * q ≠ 1) :
    ∃ r ∈ Q₀, orderOf r = 4 ∧ r ^ 2 = β₀ ∧ ∀ x ∈ Q₀, orderOf x = 4 → x ∈ zpowers r :=
  L415.exists_four (hc.sylow.isPGroup.to_le hc.qTilde_le) hc.qTilde_shape hc.beta_mem_qTilde
    hc.beta_sq hs.beta.ne_one (fun _ hx => hc.beta_comm (hc.qTilde_le hx)) hq hq2

theorem not_mem_zpowers_beta (hc : L2Ctx hs W) {r : X} (hr4 : orderOf r = 4) :
    r ∉ zpowers β₀ := fun h => by
  rcases L415.mem_zpowers_two hc.beta_sq h with rfl | rfl
  · rw [orderOf_one] at hr4
    omega
  · have h2 : orderOf β₀ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [sq, hc.beta_sq])
    rw [hr4] at h2
    omega

theorem conj_r (hc : L2Ctx hs W) {r : X} (hr : r ∈ Q₀) (hr4 : orderOf r = 4) (hr2 : r ^ 2 = β₀)
    (hrQ : ∀ x ∈ Q₀, orderOf x = 4 → x ∈ zpowers r) {g : X} (hg : g ∈ W) :
    g * r * g⁻¹ = r ∨ g * r * g⁻¹ = β₀ * r := by
  have hs4 : orderOf (g * r * g⁻¹) = 4 := by
    rw [← hr4]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective r
  have hsr := hrQ _ (hc.qTilde_normal hg hr) hs4
  obtain ⟨a, ha⟩ : ∃ a, a = g * r * g⁻¹ := ⟨_, rfl⟩
  rw [← ha] at hs4 hsr ⊢
  have hsq : a ^ 2 = β₀ := by
    rw [ha, sq, show g * r * g⁻¹ * (g * r * g⁻¹) = g * (r * r) * g⁻¹ by group, ← sq, hr2,
      hc.beta_comm hg]
    group
  have hc' : a * r⁻¹ ∈ zpowers r := mul_mem hsr (inv_mem (mem_zpowers r))
  have hcomm : Commute a r := by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hsr
    rw [← hk]
    exact (Commute.refl r).zpow_left k
  have hcomm' : r⁻¹ * a = a * r⁻¹ := hcomm.inv_right.eq.symm
  have hc2 : (a * r⁻¹) ^ 2 = 1 := by
    calc (a * r⁻¹) ^ 2 = a * (r⁻¹ * a) * r⁻¹ := by rw [sq]; group
      _ = a * (a * r⁻¹) * r⁻¹ := by rw [hcomm']
      _ = a ^ 2 * (r ^ 2)⁻¹ := by rw [sq, sq]; group
      _ = 1 := by rw [hsq, hr2, mul_inv_cancel]
  have e : a = a * r⁻¹ * r := by group
  rcases L415.eq_of_mem_zpowers_sq (by norm_num : 1 ≤ 2) (by rw [hr4]; norm_num) hc' hc2 with
    h | h
  · left
    rw [e, h, one_mul]
  · right
    have h' : a * r⁻¹ = β₀ := by
      rw [h, ← hr2]
      norm_num
    rw [e, h']

theorem t_conj_r (hc : L2Ctx hs W) {r : X} (hr : r ∈ Q₀) (hr4 : orderOf r = 4)
    (hr2 : r ^ 2 = β₀) (hrQ : ∀ x ∈ Q₀, orderOf x = 4 → x ∈ zpowers r) :
    t * r * t⁻¹ = β₀ * r := by
  rcases hc.conj_r hr hr4 hr2 hrQ hc.t_mem_W with h | h
  · exfalso
    have : r ∈ Q₀ ⊓ centralizer ({t} : Set X) := ⟨hr, mem_centralizer_singleton_iff.mpr (by
      calc r * t = t * r * t⁻¹ * t := by rw [h]
        _ = t * r := by group)⟩
    rw [hc.qTilde_inf_centralizer] at this
    exact hc.not_mem_zpowers_beta hr4 this
  · exact h

theorem central_r (hc : L2Ctx hs W) {r : X} (hr : r ∈ Q₀) (hr4 : orderOf r = 4)
    (hr2 : r ^ 2 = β₀) (hrQ : ∀ x ∈ Q₀, orderOf x = 4 → x ∈ zpowers r) :
    ∀ q ∈ Q₀, r * q * r⁻¹ * q⁻¹ ∈ zpowers β₀ := by
  intro q hq
  have e : r * q * r⁻¹ * q⁻¹ = (q * r * q⁻¹ * r⁻¹)⁻¹ := by group
  rw [e]
  rcases hc.conj_r hr hr4 hr2 hrQ (hc.qTilde_le hq) with h | h
  · rw [h, mul_inv_cancel, inv_one]
    exact one_mem _
  · rw [h, mul_inv_cancel_right]
    exact inv_mem (mem_zpowers _)

theorem central_mul (hc : L2Ctx hs W) {g h : X} (hg : g ∈ W)
    (Pg : ∀ q ∈ Q₀, g * q * g⁻¹ * q⁻¹ ∈ zpowers β₀)
    (Ph : ∀ q ∈ Q₀, h * q * h⁻¹ * q⁻¹ ∈ zpowers β₀) :
    ∀ q ∈ Q₀, (g * h) * q * (g * h)⁻¹ * q⁻¹ ∈ zpowers β₀ := by
  intro q hq
  have e : (g * h) * q * (g * h)⁻¹ * q⁻¹ =
      g * (h * q * h⁻¹ * q⁻¹) * g⁻¹ * (g * q * g⁻¹ * q⁻¹) := by group
  rw [e, hc.conj_zpowers_eq hg (Ph q hq)]
  exact mul_mem (Ph q hq) (Pg q hq)

theorem central_inv (hc : L2Ctx hs W) {g : X} (hg : g ∈ W)
    (Pg : ∀ q ∈ Q₀, g * q * g⁻¹ * q⁻¹ ∈ zpowers β₀) :
    ∀ q ∈ Q₀, g⁻¹ * q * g⁻¹⁻¹ * q⁻¹ ∈ zpowers β₀ := by
  intro q hq
  have hq' : g⁻¹ * q * g ∈ Q₀ := by
    have := hc.qTilde_normal (W.inv_mem hg) hq
    rwa [inv_inv] at this
  have e : g⁻¹ * q * g⁻¹⁻¹ * q⁻¹ =
      (g * (g⁻¹ * q * g) * g⁻¹ * (g⁻¹ * q * g)⁻¹)⁻¹ := by group
  rw [e]
  exact inv_mem (Pg _ hq')

theorem central_of_mem_zpowers (hc : L2Ctx hs W) {r x : X} (hrW : r ∈ W)
    (Pr : ∀ q ∈ Q₀, r * q * r⁻¹ * q⁻¹ ∈ zpowers β₀) (hx : x ∈ zpowers r) :
    ∀ q ∈ Q₀, x * q * x⁻¹ * q⁻¹ ∈ zpowers β₀ := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  clear hx
  induction k using Int.induction_on with
  | zero =>
    intro q hq
    rw [zpow_zero, one_mul, inv_one, mul_one, mul_inv_cancel]
    exact one_mem _
  | succ n ih =>
    rw [zpow_add_one]
    exact hc.central_mul (zpow_mem hrW _) ih Pr
  | pred n ih =>
    rw [zpow_sub_one]
    exact hc.central_mul (zpow_mem hrW _) ih (hc.central_inv hrW Pr)

theorem false_of_central (hc : L2Ctx hs W) {r q : X} (hr : r ∈ Q₀) (hr4 : orderOf r = 4)
    (hr2 : r ^ 2 = β₀) (hrQ : ∀ x ∈ Q₀, orderOf x = 4 → x ∈ zpowers r) (hq : q ∈ Q₀)
    (hqr : q ∉ zpowers r) (htq : t * q * t⁻¹ * q⁻¹ ∈ zpowers β₀) : False := by
  have hβr : β₀ ∈ zpowers r := by
    rw [← hr2]
    exact pow_mem (mem_zpowers r) 2
  have e : t * q * t⁻¹ = (t * q * t⁻¹ * q⁻¹) * q := by group
  rcases L415.mem_zpowers_two hc.beta_sq htq with h | h
  · apply hqr
    have h1 : t * q * t⁻¹ = q := by rw [e, h, one_mul]
    have : q ∈ Q₀ ⊓ centralizer ({t} : Set X) := ⟨hq, mem_centralizer_singleton_iff.mpr (by
      calc q * t = t * q * t⁻¹ * t := by rw [h1]
        _ = t * q := by group)⟩
    rw [hc.qTilde_inf_centralizer] at this
    exact (zpowers_le.mpr hβr) this
  · have h1 : t * q * t⁻¹ = β₀ * q := by rw [e, h]
    have h2 := hc.t_conj_r hr hr4 hr2 hrQ
    have hβq := hc.beta_comm (hc.qTilde_le hq)
    have h3 : t * (q * r) * t⁻¹ = q * r := by
      calc t * (q * r) * t⁻¹ = (t * q * t⁻¹) * (t * r * t⁻¹) := by group
        _ = β₀ * q * (β₀ * r) := by rw [h1, h2]
        _ = q * β₀ * (β₀ * r) := by rw [← hβq]
        _ = q * (β₀ * β₀) * r := by simp only [mul_assoc]
        _ = q * r := by rw [hc.beta_sq, mul_one]
    have hqrC : q * r ∈ Q₀ ⊓ centralizer ({t} : Set X) := ⟨mul_mem hq hr,
      mem_centralizer_singleton_iff.mpr (by
        calc q * r * t = t * (q * r) * t⁻¹ * t := by rw [h3]
          _ = t * (q * r) := by group)⟩
    rw [hc.qTilde_inf_centralizer] at hqrC
    apply hqr
    have e2 : q = (q * r) * r⁻¹ := by group
    rw [e2]
    exact mul_mem ((zpowers_le.mpr hβr) hqrC) (inv_mem (mem_zpowers r))

end EndB.L2Ctx

end CFSG.ComponentClassification.HarrisLit
