module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3Gen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy2Cos
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BStrQ
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BStrS
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BStrSP

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x₁ x₂ t a b c : G} {Wp F P M₂ M₃ U : Subgroup G}

private theorem fzc_sy3_F_cov (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) {v : G}
    (hv2F : v ^ 2 ∈ F) (hv2W : v ^ 2 ∉ Wp) :
    ∀ f ∈ F, ∃ k : ℕ, f * (v ^ k)⁻¹ ∈ Wp := by
  intro f hfF
  obtain ⟨w, hw, hf | hf⟩ := (hs.F_mem).1 hfF
  · exact ⟨0, by simpa [hf] using hw⟩
  · obtain ⟨w', hw', hv2 | hv2⟩ := (hs.F_mem).1 hv2F
    · exact absurd (hv2 ▸ hw') hv2W
    · refine ⟨2, ?_⟩
      have h : f * (v ^ 2)⁻¹ = w * w'⁻¹ := by rw [hf, hv2]; group
      rw [h]
      exact Wp.mul_mem hw (Wp.inv_mem hw')

private theorem fzc_sy3_M₃_cov (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) {v : G}
    (hvM₃ : v ∈ M₃) (hvF : v ∉ F) :
    ∀ g ∈ M₃, ∃ k : ℕ, g * (v ^ k)⁻¹ ∈ Wp := by
  have hv2 := hs.M₃_sq v hvM₃ hvF
  obtain ⟨f₀, hf₀F, hv | hv⟩ := (hs.M₃_mem).1 hvM₃
  · exact absurd (hv ▸ hf₀F) hvF
  · intro g hg
    obtain ⟨f, hfF, hgf | hgf⟩ := (hs.M₃_mem).1 hg
    · rw [hgf]
      exact fzc_sy3_F_cov hs hv2.1 hv2.2 f hfF
    · obtain ⟨k, hk⟩ := fzc_sy3_F_cov hs hv2.1 hv2.2 (f * f₀⁻¹)
        (F.mul_mem hfF (F.inv_mem hf₀F))
      refine ⟨k + 1, ?_⟩
      have hg_eq : g = (f * f₀⁻¹) * v := by rw [hgf, hv]; group
      rw [hg_eq]
      have hpow : (f * f₀⁻¹) * v * (v ^ (k + 1))⁻¹ = (f * f₀⁻¹) * (v ^ k)⁻¹ := by
        rw [pow_succ, mul_inv_rev]
        group
      rw [hpow]
      exact hk

theorem fzc_sy3_klein_P (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) {Y : Subgroup G}
    (hY : Y ≤ P) {x y : G} (hx : x ∈ Y) (hy : y ∈ Y) (hxW : x ∉ Wp) (hyW : y ∉ Wp)
    (hxy : x * y⁻¹ ∉ Wp) : ∃ u : G, closure {x, y, u} = Y := by
  have hPU : P ≤ U := hs.chain.2.2.1
  have hx2 : x ^ 2 ∈ Wp := (hs.P_elem).1 x (hY hx)
  have hy2 : y ^ 2 ∈ Wp := (hs.P_elem).1 y (hY hy)
  refine fzc_sy3_klein (N := Wp) (E := baseGrp x₁ x₂) (X := Y)
    hs.E_comm hs.E_exp hs.E_rank hs.E_le_Wp hs.Wp_E hx hy hx2
    (hs.sq_notE x (hPU (hY hx)) hxW hx2) hy2
    (hs.sq_notE y (hPU (hY hy)) hyW hy2) ?_ ?_
  · intro g hg
    exact fzc_sy2_four_cosets (W := Wp) (Q := P)
      (hs.chain.1.trans hs.chain.2.1) (hs.card_P_M₂).1
      (fun q hq w hw => hs.nrm q (hPU hq) w hw) (hs.P_elem).1 (hs.P_elem).2
      (hY hx) hxW (hY hy) hyW (fun hyx => hxy (by simpa using Wp.inv_mem hyx))
      g (hY hg)
  · intro e he
    exact fun heq => hs.SP x (hY hx) y (hY hy) hxW hyW hxy (heq ▸ hs.E_sq e he.2)

theorem fzc_sy3_rank_P (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : S4A.RankLE P 3 := by
  classical
  intro X hXP
  by_cases hXW : X ≤ Wp
  · exact hs.Wp_rank X hXW
  obtain ⟨x, hxX, hxW⟩ := SetLike.not_le_iff_exists.mp hXW
  have hPU : P ≤ U := hs.chain.2.2.1
  have hx2 : x ^ 2 ∈ Wp := (hs.P_elem).1 x (hXP hxX)
  have hx2E : x ^ 2 ∉ baseGrp x₁ x₂ := hs.sq_notE x (hPU (hXP hxX)) hxW hx2
  by_cases hcase : ∃ y ∈ X, y ∉ Wp ∧ x * y⁻¹ ∉ Wp
  · obtain ⟨y, hyX, hyW, hxy⟩ := hcase
    obtain ⟨u, hu⟩ := fzc_sy3_klein_P hs hXP hxX hyX hxW hyW hxy
    refine ⟨{x, y, u}, Finset.card_le_three, ?_⟩
    have hcoe : ((({x, y, u} : Finset G)) : Set G) = {x, y, u} := by simp
    rw [hcoe]
    exact hu
  · obtain ⟨s, hscard, hsc⟩ := fzc_sy3_cyc (N := Wp) (E := baseGrp x₁ x₂) (X := X)
      hs.Wp_comm hs.Wp_exp hs.Wp_rank
      (fun a ha => hs.Z_le_E (hs.Wp_sq a ha)) hxX hx2 hx2E (by
        intro g hg
        by_cases hgW : g ∈ Wp
        · exact ⟨0, by simpa using hgW⟩
        · refine ⟨1, ?_⟩
          have hxg : x * g⁻¹ ∈ Wp := by
            by_contra hxg
            exact hcase ⟨g, hg, hgW, hxg⟩
          have h : g * (x ^ 1)⁻¹ = (x * g⁻¹)⁻¹ := by rw [pow_one, mul_inv_rev, inv_inv]
          rw [h]
          exact Wp.inv_mem hxg)
    exact ⟨s, hscard, hsc⟩

theorem fzc_sy3_rank_M₃ (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    S4A.RankLE M₃ 3 := by
  classical
  intro X hX
  by_cases hXF : X ≤ F
  · exact fzc_sy3_rank_P hs X (hXF.trans hs.chain.2.1)
  obtain ⟨v, hvX, hvF⟩ := SetLike.not_le_iff_exists.mp hXF
  have hFP : F ≤ P := hs.chain.2.1
  have hPU : P ≤ U := hs.chain.2.2.1
  have hvM₃ : v ∈ M₃ := hX hvX
  have hv2 := hs.M₃_sq v hvM₃ hvF
  have hv4W : v ^ 4 ∈ Wp := by
    have h := (hs.P_elem).1 (v ^ 2) (hFP hv2.1)
    have he : v ^ 4 = (v ^ 2) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
    rwa [he]
  have hv4E : v ^ 4 ∉ baseGrp x₁ x₂ := by
    have h := hs.sq_notE (v ^ 2) (hPU (hFP hv2.1)) hv2.2
      ((hs.P_elem).1 (v ^ 2) (hFP hv2.1))
    have he : v ^ 4 = (v ^ 2) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
    rwa [he]
  obtain ⟨s, hscard, hsc⟩ := fzc_sy3_cyc (N := Wp) (E := baseGrp x₁ x₂) (X := X)
    hs.Wp_comm hs.Wp_exp hs.Wp_rank
    (fun a ha => hs.Z_le_E (hs.Wp_sq a ha)) hvX hv4W hv4E
    (fun g hg => fzc_sy3_M₃_cov hs hvM₃ hvF g (hX hg))
  exact ⟨s, hscard, hsc⟩

end CFSG.OddStandard.SmallF3.FritzII
