module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.PZMain
public import CFSG.LocalAnalysis.EvenBN.Tits.N.PZExistsU
public import CFSG.LocalAnalysis.EvenBN.Tits.N.PZY

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.PZ

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits
  CFSG.LocalAnalysis.EvenBN.Tits.Data

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}

structure InvV (d : Data G) (z₀ : G) : Prop where
  sq_z₀ : z₀ * z₀ = 1
  card : Nat.card d.s56V = 2 ^ 10
  abelian : ∀ a ∈ d.s56V, ∀ b ∈ d.s56V, a * b = b * a
  sq_one : ∀ v ∈ d.s56V, v * v = 1

structure StarV (d : Data G) (z₀ : G) : Prop where
  sq_z₀ : z₀ * z₀ = d.z
  card : Nat.card d.s56V = 2 ^ 10
  abelian : ∀ a ∈ d.s56V, ∀ b ∈ d.s56V, a * b = b * a
  exp_four : ∀ v ∈ d.s56V, v ^ 4 = 1
  inv_t : ∀ v ∈ d.s56V, d.t * v * d.t = v⁻¹
  sq_eq_eps : ∀ v ∈ d.s56V, v * v = d.s56Eps v
  sq_eq_one_iff : ∀ v ∈ d.s56V, (v * v = 1 ↔ v ∈ d.E)

@[expose] def ThmA (d : Data G) (z₀ : G) : Prop := InvV d z₀ ∨ StarV d z₀

@[expose] def StepA : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G},
    d.Thm49Statement → d.Hyp → d.S56Z0 z₀ → d.S56Kappa → ThmA d z₀

theorem thmA (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (hκ : d.S56Kappa) :
    ThmA d z₀ := by
  obtain ⟨u, huV, huN, huF, huε⟩ := exists_u h49 hd hz hκ
  have hfix := y_comm_sq h49 hd huF huε
  have hcard := hd.s56_card_V h49 hz
  rcases hd.s56_Z0_sq_cases hz with h1 | h2
  ·
    have tw := twist_one h49 hd hz h1
    have hq : ∀ v ∈ d.s56V, qq (fun _ : G => (1 : G)) v = 1 :=
      tw.qq_eq_one h49 hd hz (by simp [qq, h1])
        ⟨u, huV, huε, qq_u_one hd tw huV hfix (Or.inl rfl)⟩
    have hsq : ∀ v ∈ d.s56V, v * v = 1 := fun v hv => by simpa [qq] using hq v hv
    exact Or.inl ⟨h1, hcard, fun a ha b hb => comm_of_sq_eq_one hsq ha hb, hsq⟩
  ·
    have tw := twist_eps h49 hd hz h2
    have hz₀ : qq d.s56Eps z₀ = 1 := by
      unfold qq
      rw [h2, hz.eps]
      exact hd.s56_z_sq
    have hq : ∀ v ∈ d.s56V, qq d.s56Eps v = 1 :=
      tw.qq_eq_one h49 hd hz hz₀ ⟨u, huV, huε, qq_u_one hd tw huV hfix (Or.inr huε)⟩
    have hε : ∀ v ∈ d.s56V, d.s56Eps v = (v * v)⁻¹ := fun v hv =>
      eq_inv_of_mul_eq_one_right (hq v hv)
    have hinv : ∀ v ∈ d.s56V, d.t * v * d.t = v⁻¹ := by
      intro v hv
      have h3 : d.t * (v * d.t * v⁻¹) = v⁻¹ * v⁻¹ := by
        have h4 : d.s56Eps v = (v * v)⁻¹ := hε v hv
        calc d.t * (v * d.t * v⁻¹) = d.s56Eps v := rfl
          _ = v⁻¹ * v⁻¹ := by rw [h4]; group
      calc d.t * v * d.t = (d.t * (v * d.t * v⁻¹)) * v := by group
        _ = v⁻¹ * v⁻¹ * v := by rw [h3]
        _ = v⁻¹ := by group
    have hsqε : ∀ v ∈ d.s56V, v * v = d.s56Eps v := by
      intro v hv
      have hE := hd.s56_V_eps_mem_E hv
      have h4 : d.s56Eps v * d.s56Eps v = 1 := hd.s56_E_sq hE
      have h5 : (d.s56Eps v)⁻¹ = d.s56Eps v := inv_eq_of_mul_eq_one_right h4
      have h6 : v * v = (d.s56Eps v)⁻¹ := by rw [hε v hv, inv_inv]
      rw [h6, h5]
    refine Or.inr ⟨h2, hcard, fun a ha b hb => ?_, fun v hv => ?_, hinv, hsqε, fun v hv => ?_⟩
    · exact comm_of_inverted hinv hd.t_mul_self ha hb
    · have hE := hd.s56_V_eps_mem_E hv
      have h5 : v ^ 4 = (v * v) * (v * v) := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_two, pow_two]
      rw [h5, hsqε v hv]
      exact hd.s56_E_sq hE
    · rw [hsqε v hv]
      exact hd.s56_V_eps_eq_one_iff h49 hv

theorem stepA_holds : StepA := by
  intro G _ _ d z₀ h49 hd hz hκ
  exact thmA h49 hd hz hκ

end CFSG.LocalAnalysis.EvenBN.Tits.N.PZ
