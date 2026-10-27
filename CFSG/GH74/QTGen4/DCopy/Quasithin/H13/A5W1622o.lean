module

public import CFSG.Quasithin.H13.A5W1622o
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622l
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622n

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem false_of_c134_five_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) {K₀ : Subgroup G}
    (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G))
    (h5 : IsC134Case5 (K₀ ⊔ S.Tv) S.Tv K₀) : False := by
  have hsyl : IsSylowTwoOf S.Tv (K₀ ⊔ S.Tv) :=
    C1GN.isSylowTwoOf_of_le (S.isSylowTwoOf_Tv_F4 h1222 h517) le_sup_right
      (sup_le hK₀G S.Tv_le_Gv)
  have hzZ : S.z ∈ omegaOneCenterOf S.Tv := S.V1_le_omega_Tv (Subgroup.mem_zpowers _)
  have hZ := (h5.2 S.Tv hsyl le_rfl).1 hzZ
  apply hz
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp hZ.2 k ((le_sup_left : K₀ ≤ K₀ ⊔ S.Tv) hk)

theorem false_of_c134_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h132two : Stmt13_3_2_two_F4) (h132fsu : Stmt13_3_2_three_fsu_F4)
    (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4) (h1327 : Stmt13_2_7_F4)
    (h39 : Vol2Native.A39ForSQTKCat) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    (hres : Lem13622Case4Z0_F4) (hH : S.Hyp1367) {K₀ : Subgroup G} (hK : S.ClosingHyp K₀)
    (h16 : ¬ 16 ∣ Nat.card (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)) {i : ℕ}
    (hi : C134CorrLocal.IsC134CaseCorr i (K₀ ⊔ S.Tv) S.Tv K₀) : False := by
  obtain ⟨hK₀G, hK₀, hTK₀, hz, hLvK₀, hchar⟩ := hK
  have hK₀p : ⁅K₀, K₀⁆ = K₀ := perfect_of_mem_cComp hK₀
  obtain ⟨hQO, hQT, hKQ, hUQ⟩ := S.c134Q_facts_F4 h1222 h517 hK₀G hTK₀
  obtain ⟨hcommA, -⟩ := S.comm_mem_blockU_F4 h1222 h517 hK₀G hK₀p hTK₀ hchar
  obtain ⟨y₀, hy₀, hy₀N, hτ₀⟩ := S.exists_Lv_line
  obtain ⟨he2U, -⟩ := S.e2_q_mem_blockU_F4 h1222 h517 hK₀G hK₀p hTK₀ hchar hLvK₀ hy₀ hy₀N hτ₀
  have he2Z := S.e2_mem_center_c134Q_F4 h1222 h517 hK₀G hK₀p hTK₀ hchar hLvK₀
  set Q := c134Q (K₀ ⊔ S.Tv) K₀ with hQdef
  have hQG : Q ≤ Subgroup.centralizer ({S.v12} : Set G) :=
    hQO.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 K₀).trans hK₀G)

  have hvZ : S.v12 ∈ Q → S.v12 ∈ centerOf Q := fun hvQ =>
    ⟨hvQ, Subgroup.mem_centralizer_iff.mpr fun r hr =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hQG hr))⟩
  have hvK : ∀ g ∈ K₀, g * S.v12 * g⁻¹ = S.v12 := fun g hg => by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hK₀G hg), mul_inv_cancel_right]
  have hZK : centerOf Q ≤ K₀ :=
    inf_le_left.trans (hQO.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 K₀))
  have hKZ : K₀ ≤ Subgroup.normalizer ((centerOf Q : Subgroup G) : Set G) :=
    le_normalizer_centerOf hKQ
  have haN : S.a ∈ Subgroup.normalizer (K₀ : Set G) := hTK₀ S.a_mem_Tv
  rcases i with _ | _ | _ | _ | _ | _ | i
  · exact hi
  ·
    exact S.false_of_sl3Block_gen_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h39 hF hK₀G hK₀
      hTK₀ hz hLvK₀ hchar hi.1
  ·
    obtain ⟨⟨n, F, _, _, α, hFn, hα, hM⟩, -⟩ := hi
    exact S.false_of_sumNatural_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h39 hF hK₀G hK₀
      hTK₀ hz hLvK₀ hFn hα hM (fun x hx => hUQ (hcommA x hx)) (hUQ he2U)
  ·
    obtain ⟨⟨n, F, _, _, α, hFn, hα, hM, -⟩, -⟩ := hi
    have hv : S.v12 ∉ Q := fun hvQ =>
      S.v12_ne_one (eq_one_of_fixed_sumNatural hα.1 hM (hvZ hvQ) hvK)
    exact S.false_of_sumNatural_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h39 hF hK₀G hK₀
      hTK₀ hz hLvK₀ hFn hα hM
      (S.comm_a_mem_center_of_not_mem_F4 h1222 h517 hK₀G hK₀p hTK₀ hchar hv) he2Z
  ·
    have h4 := hi
    obtain ⟨⟨n, F, _, _, α, hFn, hα, -, -, -, hM, -, -, -⟩, -⟩ := hi
    have hcZ : ∀ k ∈ K₀, k⁻¹ * S.a * k * S.a⁻¹ ∈ centerOf Q := by
      by_cases hvQ : S.v12 ∈ Q
      ·
        have hF2 := card_eq_two_of_not_dvd hFn hα h16
        have hvCQ : S.v12 ∈ c134CQ (K₀ ⊔ S.Tv) K₀ :=
          ⟨hvQ, Subgroup.mem_centralizer_iff.mpr fun g hg =>
            Subgroup.mem_centralizer_singleton_iff.mp (hK₀G hg)⟩
        have hres' := hres G T L V S hH K₀ hK₀G hK₀ hTK₀ hz hLvK₀
          ⟨F, inferInstance, inferInstance, α, hF2, hα⟩ h4 hvCQ

        set O := pCoreOf 2 K₀ with hOdef
        have hKO : K₀ ≤ Subgroup.normalizer (O : Set G) :=
          CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₀
        have hnorm : (K₀.subgroupOf (K₀ ⊔ S.Tv)).Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
            (sup_le Subgroup.le_normalizer hTK₀)
        have hOG : O ≤ pCoreOf 2 (K₀ ⊔ S.Tv) :=
          CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 K₀
            (K₀ ⊔ S.Tv) le_sup_left hnorm
        have hCO : K₀ ≤ Subgroup.normalizer ((centerOf O : Subgroup G) : Set G) :=
          le_normalizer_centerOf hKO
        have hUZ : ⁅centerOf O, K₀⁆ ≤ centerOf Q := by
          refine le_inf (Subgroup.commutator_mono (inf_le_left.trans hOG) le_rfl) ?_
          rw [Subgroup.commutator_le]
          intro c hc k hk
          have h1 : k * c⁻¹ * k⁻¹ ∈ centerOf O :=
            (Subgroup.mem_normalizer_iff.mp (hCO hk) _).mp ((centerOf O).inv_mem hc)
          have hcc : c * (k * c⁻¹ * k⁻¹) ∈ centerOf O := (centerOf O).mul_mem hc h1
          rw [commutatorElement_def, show c * k * c⁻¹ * k⁻¹ = c * (k * c⁻¹ * k⁻¹) by group]
          exact Subgroup.centralizer_le hQO hcc.2
        intro k hk
        have h1 := S.comm_mem_z0Of_F4 h1222 h517 hK₀G hK₀p hTK₀ hchar k hk
        rw [hres'] at h1
        exact hUZ h1
      · exact S.comm_a_mem_center_of_not_mem_F4 h1222 h517 hK₀G hK₀p hTK₀ hchar hvQ
    have hcU := comm_mem_commutator_of_perfect hZK hKZ hK₀p haN hcZ
    have he2M : S.e2 ∈ ⁅centerOf Q, K₀⁆ := by
      rw [S.e2_eq_comm_mul hy₀N hτ₀, Subgroup.commutator_comm]
      refine Subgroup.mul_mem _ ?_ ?_
      · have := Subgroup.commutator_mem_commutator (hLvK₀ hy₀) he2Z
        rwa [commutatorElement_def] at this
      · have := Subgroup.commutator_mem_commutator (K₀.inv_mem (hLvK₀ hy₀)) he2Z
        rwa [commutatorElement_def, inv_inv] at this
    exact S.false_of_sumNatural_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h39 hF hK₀G hK₀
      hTK₀ hz hLvK₀ hFn hα hM hcU he2M
  ·
    exact S.false_of_c134_five_F4 h1222 h517 hK₀G hz hi
  · exact hi

end Setting

end CFSG.Quasithin.H13.A5
