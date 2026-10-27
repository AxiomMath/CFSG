module

public import CFSG.Quasithin.H13.A5W1622i
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622h

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem false_of_blockModelFin_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h132two : Stmt13_3_2_two_F4) (h132fsu : Stmt13_3_2_three_fsu_F4)
    (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4) (h1327 : Stmt13_2_7_F4)
    (h39 : Vol2Native.A39ForSQTKCat) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K₀ : Subgroup G} (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hK₀ : K₀ ∈ lFamily S.Tv) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) (hLvK₀ : S.Lv ≤ K₀)
    (hchar : CharTwo (K₀ ⊔ S.Tv)) (hshort : IsShort2 K₀) {X : Type} [Group X] [Finite X]
    (α : ↥K₀ →* X) (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K₀)
    {S₀ : Subgroup X} (hS₀ : IsSylowTwoOf S₀ ⊤)
    (hFix : ModelFix (blockLiftAct hshort α hα hker) S₀) : False := by
  obtain ⟨hcommA, he2U, hlA, hU2, hUc⟩ :=
    S.closing_data_blockU_F4 h1222 h517 hK₀G hK₀ hTK₀ hLvK₀ hchar hshort
  have hβe : ∀ (ℓ : ↥K₀) (u v : ↥(blockU K₀)), (v : G) = ℓ * u * ℓ⁻¹ →
      QuotientGroup.mk' ((blockZ K₀).subgroupOf (blockU K₀)) v =
        blockLiftAct hshort α hα hker (α ℓ)
          (QuotientGroup.mk' ((blockZ K₀).subgroupOf (blockU K₀)) u) := by
    intro ℓ u v h
    rw [blockLiftAct_apply]
    exact (blockQuotAct_mk K₀ ℓ u v h).symm
  exact S.false_of_closing_model_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h39 hF hK₀G hK₀
    hTK₀ hz hLvK₀ (C1.le_normalizer_blockU K₀) (Zc := blockZ K₀) inf_le_right hU2 hUc hcommA he2U
    hlA (blockQuot_sq hshort) (blockLiftAct hshort α hα hker) hS₀ hFix α hα
    (QuotientGroup.mk' _) (QuotientGroup.ker_mk' _) hβe

theorem false_of_g2Block_F4
    (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h132two : Stmt13_3_2_two_F4) (h132fsu : Stmt13_3_2_three_fsu_F4)
    (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4) (h1327 : Stmt13_2_7_F4)
    (h39 : Vol2Native.A39ForSQTKCat) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K₀ : Subgroup G} (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hK₀ : K₀ ∈ lFamily S.Tv) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) (hLvK₀ : S.Lv ≤ K₀)
    (hchar : CharTwo (K₀ ⊔ S.Tv)) (hblk : IsG2Block K₀) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hshort, hQ, hidx⟩ := hblk
  have : Finite U33G := (CFSG.Quasithin.u33Pres_finite_card_le).1
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥K₀) := inferInstance
  obtain ⟨ψ, hψs, hψk, -⟩ := ModD.exists_psi hQ P
  have hcard : Nat.card (blockQuot K₀) = 64 := hidx.1
  have hT : IsSylowTwoOf u33Data.T ⊤ := by
    refine ⟨le_top, u33_syl.1, ?_⟩
    rw [show (u33Data.T.subgroupOf ⊤).index = u33Data.T.index from Subgroup.relIndex_top_right _]
    exact u33_syl.2
  refine S.false_of_blockModelFin_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h39 hF hK₀G hK₀ hTK₀
    hz hLvK₀ hchar hshort ψ hψs hψk hT ?_
  intro n p hn hp hnS hpS x hx
  set act := blockLiftAct hshort ψ hψs hψk with hact
  have hfix : ∀ v : blockQuot K₀, (∀ g, act g v = v) → v = 1 := fun v hv =>
    fixed_eq_one_of_short hshort (by rw [hcard]; norm_num) fun ℓ => by
      rw [← blockLiftAct_apply hshort ψ hψs hψk ℓ]
      exact hv _
  have hV2 : ∀ v : blockQuot K₀, v * v = 1 := fun v => by
    rw [← pow_two]
    exact blockQuot_sq hshort v
  have hc := U3.u33_sylow_fixed_card_two hV2 hcard act hfix (u33_syl.1.toSylow u33_syl.2)
  have hnp : n = p :=
    eq_of_card_subtype_two hc (fun s _ => map_one _) hn hp hnS hpS
  rw [← hnp]
  exact hx

end Setting

end CFSG.Quasithin.H13.A5
