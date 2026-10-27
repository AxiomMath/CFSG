module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.KappaThmC
import CFSG.LocalAnalysis.EvenBN.Tits.S56N2

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.Data

open Matrix Subgroup CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits.N.KappaA
  CFSG.LocalAnalysis.EvenBN.Tits

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem Hyp.kappaForm (h49 : d.Thm49Statement) (hd : d.Hyp)
    {z₀ : G} (hz : d.S56Z0 z₀) :
    ∃ μ : ZMod 2, ∀ x ∈ d.s56V, ∀ q ∈ d.s56J, ∃ u ∈ d.E,
      x * q * x⁻¹ * q⁻¹ = u * z₀ ^ (kk d x q).val ∧
        wcoord d u = betaT (kapTc 0 μ) (eb d x) (fb d q) := by
  have hsq := z0_sq_eq_one h49 hd hz
  have hs0 : zc (z₀ * z₀) = 0 := by rw [hsq]; exact zc_one
  obtain ⟨μ, hμ⟩ := exists_mu h49 hd hz
  rw [hs0] at hμ
  exact ⟨μ, fun x hx q hq => ⟨ep d z₀ x q, ep_mem h49 hd hz hx hq, comm_eq d z₀ x q, hμ x hx q hq⟩⟩

theorem Hyp.kappaLemmaA (h49 : d.Thm49Statement) (hd : d.Hyp)
    {z₀ : G} (hz : d.S56Z0 z₀) {x : G} (hx : x ∈ d.s56V ⊓ d.N) {e₁ e₂ e₃ e₄ d₁ d₂ d₃ : ZMod 2}
    (hε : d.s56Eps x = d.z ^ e₁.val * d.pv 11 ^ e₂.val * d.pv 10 ^ e₃.val * d.pv 9 ^ e₄.val)
    (hδ : x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹ = d.z ^ d₁.val * d.pv 11 ^ d₂.val * d.pv 10 ^ d₃.val) :
    (d₂ = 0 ∧ d₃ = 0) ∨ (d₂ = e₃ + e₄ ∧ d₃ = e₄) := by
  have hxV : x ∈ d.s56V := hx.1
  have hsq := z0_sq_eq_one h49 hd hz
  obtain ⟨μ, hμ⟩ := exists_mu h49 hd hz
  have hs0 : zc (z₀ * z₀) = 0 := by rw [hsq]; exact zc_one
  rw [hs0] at hμ
  have hεc : d.s56Eps x = crdE d ![e₁, e₂, e₃, e₄, 0] := by
    rw [hε]
    unfold crdE
    simp [Data.s56_pv12]
  have hebx : eb d x = ![e₂, e₃, e₄, 0] := by
    unfold eb
    rw [hεc, wcoord_crdE hd]
    funext i
    fin_cases i <;> rfl
  have hδc : x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹ = crdE d ![d₁, d₂, d₃, 0, 0] := by
    rw [hδ]
    unfold crdE
    simp [Data.s56_pv12]
  have hq7 : d.pv 7 ∈ d.s56J := Data.s56_pv_mem_J d (by simp)
  have hB := hμ x hxV (d.pv 7) hq7
  rw [fb_pv7 hd, hebx] at hB
  have hκ : kk d x (d.pv 7) = 0 := by
    unfold kk
    rw [hebx, fb_pv7 hd]
    simp [b0, dotProduct, Fin.sum_univ_four]
  have hep : ep d z₀ x (d.pv 7) = crdE d ![d₁, d₂, d₃, 0, 0] := by
    unfold ep
    rw [hκ]
    simpa using hδc
  have hBv : Bf d z₀ x (d.pv 7) = ![d₂, d₃, 0, 0] := by
    unfold Bf
    rw [hep, wcoord_crdE hd]
    funext i
    fin_cases i <;> rfl
  rw [hBv, kapA_table0 μ ![e₂, e₃, e₄, 0] rfl] at hB
  have h0 := congrFun hB 0
  have h1 := congrFun hB 1
  simp at h0 h1
  rcases zmod2_cases μ with rfl | rfl
  · left
    simp at h0 h1
    exact ⟨h0, h1⟩
  · right
    simp at h0 h1
    exact ⟨h0, h1⟩

end CFSG.LocalAnalysis.EvenBN.Tits.Data
