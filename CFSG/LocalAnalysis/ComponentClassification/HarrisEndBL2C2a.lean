module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2Qc3
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2G5a

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

local notation "β₀" => w ^ (orderOf w / 2) * t ^ i * z ^ j
local notation "T₀" => (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X)
local notation "X₈" => (closure {t, w ^ (orderOf w / 2), z} : Subgroup X)

theorem Setting46e.conj_z_of_normalizer_V (hKC : AutPSL2CentralizerInput)
    (hs : Setting46e t L p f S w z V i j) (hβ : β₀ ∉ V ⊓ centralizer (V : Set X)) {n : X}
    (hn : n ∈ normalizer (V : Set X)) : n * z * n⁻¹ = z := by
  have hzZ := hs.z_mem_center_V
  have hmem : n * z * n⁻¹ ∈ V ⊓ centralizer (V : Set X) := by
    refine Subgroup.mem_inf.mpr ⟨(mem_normalizer_iff.mp hn z).mp hzZ.1,
      mem_centralizer_iff.mpr fun v hv => ?_⟩
    have hv' : n⁻¹ * v * n ∈ V := by
      have := (mem_normalizer_iff.mp (inv_mem hn) v).mp hv
      rwa [inv_inv] at this
    have h1 := (mem_centralizer_iff.mp hzZ.2) _ hv'
    calc v * (n * z * n⁻¹) = n * ((n⁻¹ * v * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * v * n)) * n⁻¹ := by rw [h1]
      _ = n * z * n⁻¹ * v := by group
  have hz2 : z * z = 1 := by rw [← sq, ← hs.setup.z_order, pow_orderOf_eq_one]
  rcases L415.mem_zpowers_two hz2 (hs.center_V_le_of_not_mem hKC hβ hmem) with h | h
  · exfalso
    apply hs.setup.z_ne_one
    have := congrArg (fun y => n⁻¹ * y * n) h
    simpa [mul_assoc] using this
  · exact h

namespace EndB.L2Ctx

variable {hs : Setting46e t L p f S w z V i j} {W : Subgroup X}

theorem qc_beta_not_mem (hKF : AutPSL2FusionInput) (hc : L2Ctx hs W)
    (hSV : S.relIndex V = 2) : β₀ ∉ V ⊓ centralizer (V : Set X) := fun h => by
  obtain ⟨-, hUW, hWS, -⟩ := hc.qc_structure hKF hSV
  have hU : V ⊓ centralizer ({β₀} : Set X) = V := inf_of_le_left fun v hv =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp h.2 v hv)
  have h2 := Subgroup.relIndex_mul_card S V
  rw [inf_of_le_left hs.le_V, hSV] at h2
  have hpos : 0 < Nat.card S := Nat.card_pos
  have : Nat.card V = Nat.card W := by rw [← hUW, hU]
  omega

theorem qc_inf_X (hKG : AutPSL2SylowInput) (hKC : AutPSL2CentralizerInput)
    (hFC : AutPSL2FieldCentralizerInput) (hKF : AutPSL2FusionInput) (hc : L2Ctx hs W)
    (hSV : S.relIndex V = 2) {Y : Subgroup X} (hVY : ∀ v ∈ V, ∀ y ∈ Y, v * y * v⁻¹ ∈ Y)
    (hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (hY2 : ∀ y ∈ Y, y * y = 1)
    (hY8 : Nat.card Y = 8) (hYW : β₀ ∈ Y → Y ≤ W) (hYX : ¬ Y ≤ X₈) :
    t * β₀ ∈ Y ∧ ∀ x ∈ Y, x ∈ X₈ → x = 1 ∨ x = z ∨ x = t * β₀ ∨ x = t * (β₀ * z) := by
  obtain ⟨hQ2', -, -, -⟩ := hc.qc_structure hKF hSV
  obtain ⟨hWV, -⟩ := hc.qc_relIndex hKF hSV
  obtain ⟨v₁, hv₁, hv₁t⟩ := hc.qc_exists_v hKF hSV
  obtain ⟨s, hsS, hsβ⟩ := hc.qc_exists_s hKF hKC hSV
  have hTV : T₀ ≤ V := hs.setup.T_le.trans hs.le_V
  have htV : t ∈ V := hTV (mem_sup_left (mem_sup_left (mem_zpowers t)))
  have ht2 : t * t = 1 := by rw [← sq, ← hs.standing.config.orderOf_eq, pow_orderOf_eq_one]
  have htY : t ∉ Y := fun htY => hYX (hs.setup.le_X_of_elem_centralizer
    (fun y hy => mem_centralizer_singleton_iff.mpr (hYc y hy t htY))
    (fun y hy => by rw [sq]; exact hY2 y hy) (fun g hg y hy => hVY g (hTV hg) y hy))
  have htzY : t * z ∉ Y := fun h => htY (by
    have := hVY v₁⁻¹ (inv_mem hv₁) _ h
    rwa [show v₁⁻¹ * (t * z) * v₁⁻¹⁻¹ = t by rw [← hv₁t]; group] at this)
  have hβY : β₀ ∉ Y := fun h => hYX (by
    have hN := hc.le_N0_of_normal hKG hKC hFC (hYW h) (fun g hg y hy => hVY g (hWV hg) y hy)
      hY2
    exact hN.trans (hc.N0_le_X hQ2'))
  have hβzY : β₀ * z ∉ Y := fun h => hβY (by
    have := hVY s⁻¹ (inv_mem (hs.le_V hsS)) _ h
    rwa [show s⁻¹ * (β₀ * z) * s⁻¹⁻¹ = β₀ by rw [← hsβ]; group] at this)
  have hsq := EndB.card_le_mul_self hYc hY2 ht2 fun a ha => hVY t htV a ha
  rw [hY8] at hsq
  have hCX : Y ⊓ centralizer ({t} : Set X) ≤ X₈ :=
    hs.setup.le_X_of_elem_centralizer inf_le_right (fun x hx => by rw [sq]; exact hY2 x hx.1)
      fun g hg x hx => by
        have hgC : g ∈ centralizer ({t} : Set X) := hs.sylow.le (hs.setup.T_le hg)
        exact Subgroup.mem_inf.mpr ⟨hVY g (hTV hg) x hx.1,
          mul_mem (mul_mem hgC hx.2) (inv_mem hgC)⟩
  have hC4 : 4 ≤ Nat.card ↥(Y ⊓ centralizer ({t} : Set X)) := by
    have hdvd : Nat.card ↥(Y ⊓ centralizer ({t} : Set X)) ∣ 8 := by
      rw [← hY8]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hpos : 0 < Nat.card ↥(Y ⊓ centralizer ({t} : Set X)) := Nat.card_pos
    by_contra hlt
    push Not at hlt
    interval_cases h : Nat.card ↥(Y ⊓ centralizer ({t} : Set X)) <;> omega
  have hF4 : 4 ≤ Nat.card ↥(Y ⊓ X₈) :=
    hC4.trans (Subgroup.card_le_of_le (le_inf inf_le_left hCX))
  obtain ⟨htβ, -⟩ := hs.tbeta_mem inf_le_right hF4 (fun h => htY h.1) (fun h => htzY h.1)
    (fun h => hβY h.1) (fun h => hβzY h.1)
  refine ⟨htβ.1, fun x hx hxX => ?_⟩
  rcases hs.mem_X_cases hxX with h | h | h | h | h | h | h | h <;> rw [h] at hx
  · exact Or.inl h
  · exact absurd hx hβY
  · exact Or.inr (Or.inl h)
  · exact absurd hx hβzY
  · exact absurd hx htY
  · exact Or.inr (Or.inr (Or.inl h))
  · exact absurd hx htzY
  · exact Or.inr (Or.inr (Or.inr h))

end EndB.L2Ctx

end CFSG.ComponentClassification.HarrisLit
