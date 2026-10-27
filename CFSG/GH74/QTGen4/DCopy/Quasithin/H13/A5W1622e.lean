module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622a
public import CFSG.Quasithin.H13.A5W1622b
public import CFSG.Quasithin.H13.A5W1622d

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem false_of_closing_model_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h132two : Stmt13_3_2_two_F4) (h132fsu : Stmt13_3_2_three_fsu_F4)
    (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4) (h1327 : Stmt13_2_7_F4)
    (h39 : Vol2Native.A39ForSQTKCat) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K₀ : Subgroup G} (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hK₀ : K₀ ∈ lFamily S.Tv) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) (hLvK₀ : S.Lv ≤ K₀)
    {A Zc : Subgroup G} (hKA : K₀ ≤ Subgroup.normalizer (A : Set G))
    (hZc : Zc ≤ Subgroup.centralizer (K₀ : Set G)) (hA2 : ∀ x ∈ A, x ^ 2 = 1)
    (hAc : ∀ x ∈ A, ∀ x' ∈ A, x * x' = x' * x)
    (hcommA : ∀ k ∈ K₀, k⁻¹ * S.a * k * S.a⁻¹ ∈ A) (he2A : S.e2 ∈ A)
    (hlA : ∀ y ∈ S.Lv, y * S.e2 * y⁻¹ ∈ A)
    {X N : Type} [Group X] [Finite X] [Group N] [Finite N] (hN2 : ∀ n : N, n ^ 2 = 1)
    (act : X →* MulAut N) {S₀ : Subgroup X} (hS₀ : IsSylowTwoOf S₀ ⊤) (hFix : ModelFix act S₀)
    (α : ↥K₀ →* X) (hα : Function.Surjective α) (β : ↥A →* N) (hβk : β.ker = Zc.subgroupOf A)
    (hβe : ∀ (ℓ : ↥K₀) (u v : ↥A), (v : G) = ℓ * u * ℓ⁻¹ → β v = act (α ℓ) (β u)) : False := by

  obtain ⟨y, hy, hyN, hτ⟩ := S.exists_Lv_line
  obtain ⟨hyp, hyq, -, -⟩ := conj_q_line hyN hτ
  have hyK : y ∈ K₀ := hLvK₀ hy
  have hqA : y * S.e2 * y⁻¹ ∈ A := hlA y hy

  have hpq : y * S.e2 * y⁻¹ * S.e2⁻¹ ∉ Zc := by
    intro h
    have hc := Subgroup.mem_centralizer_iff.mp (hZc h) y hyK
    have hx : y * (y * S.e2 * y⁻¹ * S.e2⁻¹) * y⁻¹ = y * S.e2 * y⁻¹ * S.e2⁻¹ := by
      rw [hc, mul_inv_cancel_right]
    have he2sq : S.e2 * S.e2 = 1 := by
      have := hA2 _ he2A
      rwa [pow_two] at this

    have h1 : y * (y * S.e2 * y⁻¹ * S.e2⁻¹) * y⁻¹ = S.e2 := by
      have e : y * (y * S.e2 * y⁻¹ * S.e2⁻¹) * y⁻¹ =
          (y * (y * S.e2 * y⁻¹) * y⁻¹) * (y * S.e2 * y⁻¹)⁻¹ := by group
      rw [e, hyq]
      group
    rw [hx] at h1

    have hq1 : y * S.e2 * y⁻¹ = 1 := by
      calc y * S.e2 * y⁻¹ = (y * S.e2 * y⁻¹ * S.e2⁻¹) * S.e2 := by group
        _ = S.e2 * S.e2 := by rw [h1]
        _ = 1 := he2sq
    have he1 : S.e2 = 1 := by
      calc S.e2 = y⁻¹ * (y * S.e2 * y⁻¹) * y := by group
        _ = 1 := by rw [hq1]; group
    exact hyp (by rw [hq1, he1])

  have hsylH : IsSylowTwoOf S.Tv (K₀ ⊔ S.Tv) :=
    C1GN.isSylowTwoOf_of_le (S.isSylowTwoOf_Tv_F4 h1222 h517) le_sup_right
      (sup_le hK₀G S.Tv_le_Gv)
  have hSK : IsSylowTwoOf (S.Tv ⊓ K₀) K₀ :=
    A4.isSylowTwoOf_inf_normal hsylH le_sup_left (sup_le Subgroup.le_normalizer hTK₀)
  have hfix := fixed_of_modelFix hZc hN2 act hS₀ hFix α hα β hβk hβe hSK hLvK₀
    (fun t ht => S.Tv_le_normalizer_Lv ht.1) hy he2A hqA hpq
    (fun t ht => S.conj_e2_of_mem_Tv ht.1)
  exact S.false_of_comm_mem_of_fixed_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h39 hF hK₀G hK₀
    hTK₀ hz hA2 hAc hKA hcommA hLvK₀ (fun l hl => S.Lv_comm_a hl) hfix

end Setting

end CFSG.Quasithin.H13.A5
