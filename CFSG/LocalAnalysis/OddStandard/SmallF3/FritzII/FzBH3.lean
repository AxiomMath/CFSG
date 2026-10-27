module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBH1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBH2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBV1

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {c : Bool} {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau : G} {T₂ P : Subgroup G} {q s : G} {β : ℕ → G}

theorem fzb_six_comm (hβ : FzbChart c T₂ P x₁ x₂ t q s lam β) (hF : FzbFactsGen c) :
    ∀ e ∈ fzbSix c, fzbMul c e 832 = fzbMul c 832 e := by
  have htu : Commute (β 128) (β 832) :=
    (fzb_chart_comm (x := 128) (y := 832) hβ hF.mul_lt (by norm_num) (by norm_num)).mp
      hF.comm_t_u
  have hzu : Commute (β 1) (β 832) :=
    (fzb_chart_comm (x := 1) (y := 832) hβ hF.mul_lt (by norm_num) (by norm_num)).mp
      hF.comm_z_u
  intro e he
  simp only [fzbSix, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (fzb_chart_comm (x := 128) (y := 832) hβ hF.mul_lt (by norm_num)
      (by norm_num)).mpr htu
  · have hb2 : fzbMul c 128 1 < 1024 := hF.mul_lt 128 (by norm_num) 1 (by norm_num)
    refine (fzb_chart_comm (x := fzbMul c 128 1) (y := 832) hβ hF.mul_lt hb2
      (by norm_num)).mpr ?_
    rw [hβ.mul 128 (by norm_num) 1 (by norm_num)]
    exact htu.mul_left hzu
  · rfl
  · have hb4 : fzbMul c 832 1 < 1024 := hF.mul_lt 832 (by norm_num) 1 (by norm_num)
    refine (fzb_chart_comm (x := fzbMul c 832 1) (y := 832) hβ hF.mul_lt hb4
      (by norm_num)).mpr ?_
    rw [hβ.mul 832 (by norm_num) 1 (by norm_num)]
    exact (Commute.refl (β 832)).mul_left hzu
  · have hb5 : fzbMul c 128 832 < 1024 := hF.mul_lt 128 (by norm_num) 832 (by norm_num)
    refine (fzb_chart_comm (x := fzbMul c 128 832) (y := 832) hβ hF.mul_lt hb5
      (by norm_num)).mpr ?_
    rw [hβ.mul 128 (by norm_num) 832 (by norm_num)]
    exact htu.mul_left (Commute.refl (β 832))
  · have hb5 : fzbMul c 128 832 < 1024 := hF.mul_lt 128 (by norm_num) 832 (by norm_num)
    have hb6 : fzbMul c (fzbMul c 128 832) 1 < 1024 := hF.mul_lt _ hb5 1 (by norm_num)
    refine (fzb_chart_comm (x := fzbMul c (fzbMul c 128 832) 1) (y := 832) hβ hF.mul_lt hb6
      (by norm_num)).mpr ?_
    rw [hβ.mul (fzbMul c 128 832) hb5 1 (by norm_num),
      hβ.mul 128 (by norm_num) 832 (by norm_num)]
    exact (htu.mul_left (Commute.refl (β 832))).mul_left hzu

theorem fzb_six_conj (hβ : FzbChart c T₂ P x₁ x₂ t q s lam β) (hF : FzbFactsGen c)
    (hu : ∃ g : G, g⁻¹ * t * g = β 832) :
    ∀ e ∈ fzbSix c, e < 1024 ∧ ∃ g : G, g⁻¹ * t * g = β e := by
  have hstep : ∀ {a b : G}, (∃ g : G, g⁻¹ * t * g = b) →
      (∃ g : G, g * b * g⁻¹ = a) → ∃ g : G, g⁻¹ * t * g = a := by
    intro a b hb hc
    obtain ⟨g1, hg1⟩ := hb
    obtain ⟨g0, hg0⟩ := hc
    exact ⟨g1 * g0⁻¹, by rw [← hg0, ← hg1]; group⟩
  intro e he
  simp only [fzbSix, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, ⟨1, by rw [hβ.t_eq]; group⟩⟩
  · obtain ⟨g0, hg0lt, hg0⟩ := hF.conj_tz
    have hb2 : fzbMul c 128 1 < 1024 := hF.mul_lt 128 (by norm_num) 1 (by norm_num)
    refine ⟨hb2, ⟨(β g0)⁻¹, ?_⟩⟩
    rw [inv_inv, ← hβ.t_eq]
    exact (fzb_chart_conj (g := g0) (x := 128) (y := fzbMul c 128 1) hβ hF.mul_lt hg0lt
      (by norm_num) hb2).mp hg0
  · exact ⟨by norm_num, hu⟩
  · obtain ⟨g0, hg0lt, hg0⟩ := hF.conj_uz
    have hb4 : fzbMul c 832 1 < 1024 := hF.mul_lt 832 (by norm_num) 1 (by norm_num)
    exact ⟨hb4, hstep hu ⟨β g0, (fzb_chart_conj (g := g0) (x := 832) (y := fzbMul c 832 1)
      hβ hF.mul_lt hg0lt (by norm_num) hb4).mp hg0⟩⟩
  · obtain ⟨g0, hg0lt, hg0⟩ := hF.conj_tu
    have hb5 : fzbMul c 128 832 < 1024 := hF.mul_lt 128 (by norm_num) 832 (by norm_num)
    exact ⟨hb5, hstep hu ⟨β g0, (fzb_chart_conj (g := g0) (x := 832) (y := fzbMul c 128 832)
      hβ hF.mul_lt hg0lt (by norm_num) hb5).mp hg0⟩⟩
  · obtain ⟨g0, hg0lt, hg0⟩ := hF.conj_tuz
    have hb5 : fzbMul c 128 832 < 1024 := hF.mul_lt 128 (by norm_num) 832 (by norm_num)
    have hb6 : fzbMul c (fzbMul c 128 832) 1 < 1024 := hF.mul_lt _ hb5 1 (by norm_num)
    exact ⟨hb6, hstep hu ⟨β g0, (fzb_chart_conj (g := g0) (x := 832)
      (y := fzbMul c (fzbMul c 128 832) 1) hβ hF.mul_lt hg0lt (by norm_num) hb6).mp hg0⟩⟩

theorem fzb_count_A6 (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 4)
    (hS : FzbStruct t S x₁ x₂ lam rho tau T₂ P q s) (hβ : FzbChart c T₂ P x₁ x₂ t q s lam β)
    (hF : FzbFacts c) (hu : ∃ g : G, g⁻¹ * t * g = q * s * lam) : False := by
  obtain ⟨-, -, ht1, -, h832⟩ := fzb_chart_q hβ hF.toFzbFactsGen
  rw [← h832] at hu
  obtain ⟨g, hgu, hgS⟩ := fzr_transport (fzr_isSylowOf_S h.toCtx0) hS.isPGroup hS.S_le hu
  obtain ⟨ψ, hψ, hψβ⟩ := fzb_emb_of_conj hβ hF.mul_lt hgu (fun x hx => hS.S_le (hgS x hx))
  have hcomm := fzb_six_comm hβ hF.toFzbFactsGen
  have hconj := fzb_six_conj hβ hF.toFzbFactsGen hu
  refine fzb_model_pigeon hF hψ hcomm (fun e he => ?_)
  by_contra hlt
  push_neg at hlt
  obtain ⟨he1024, hge⟩ := hconj e he
  obtain ⟨-, hψe⟩ := hψβ e he1024 (hcomm e he)
  have hz : β (ψ e) ∈ fourGrp x₁ x₂ := (hβ.Z_eq _).mpr ⟨ψ e, hlt, rfl⟩
  obtain ⟨k, hk⟩ := hge
  have hzc : ∃ g' : G, g'⁻¹ * t * g' = β (ψ e) :=
    ⟨k * g, by rw [hψe, ← hk]; group⟩
  by_cases hz1 : β (ψ e) = 1
  · apply ht1
    have h2 : g⁻¹ * β e * g = 1 := by rw [← hψe]; exact hz1
    have h1 : β e = 1 := by
      calc β e = g * (g⁻¹ * β e * g) * g⁻¹ := by group
        _ = 1 := by rw [h2]; group
    calc t = k * (k⁻¹ * t * k) * k⁻¹ := by group
      _ = 1 := by rw [hk, h1]; group
  · exact fzb_Z_not_conj h hK hS hβ hF.toFzbFactsGen hz hz1 hzc

end CFSG.OddStandard.SmallF3.FritzII
