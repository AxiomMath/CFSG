module

public import CFSG.Quasithin.H13.A5W1622h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622e

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem closing_data_blockU_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) {K₀ : Subgroup G}
    (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G)) (hK₀ : K₀ ∈ lFamily S.Tv)
    (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G)) (hLvK₀ : S.Lv ≤ K₀)
    (hchar : CharTwo (K₀ ⊔ S.Tv)) (hshort : IsShort2 K₀) :
    (∀ k ∈ K₀, k⁻¹ * S.a * k * S.a⁻¹ ∈ blockU K₀) ∧ S.e2 ∈ blockU K₀ ∧
      (∀ y ∈ S.Lv, y * S.e2 * y⁻¹ ∈ blockU K₀) ∧
      (∀ x ∈ blockU K₀, x ^ 2 = 1) ∧ (∀ x ∈ blockU K₀, ∀ x' ∈ blockU K₀, x * x' = x' * x) := by
  have hK₀p : ⁅K₀, K₀⁆ = K₀ := perfect_of_mem_cComp hK₀
  have hKU : K₀ ≤ Subgroup.normalizer (blockU K₀ : Set G) := C1.le_normalizer_blockU K₀
  obtain ⟨hcommA, -⟩ := S.comm_mem_blockU_F4 h1222 h517 hK₀G hK₀p hTK₀ hchar
  obtain ⟨y₀, hy₀, hy₀N, hτ₀⟩ := S.exists_Lv_line
  obtain ⟨he2U, -⟩ := S.e2_q_mem_blockU_F4 h1222 h517 hK₀G hK₀p hTK₀ hchar hLvK₀ hy₀ hy₀N hτ₀
  refine ⟨hcommA, he2U, fun y hy => (Subgroup.mem_normalizer_iff.mp (hKU (hLvK₀ hy)) _).mp he2U,
    C1.blockU_sq hshort, fun x hx x' hx' => C1.blockU_comm hshort x hx x'
      (C1.blockU_le_blockQ hshort hx')⟩

theorem false_of_blockModelU_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h132two : Stmt13_3_2_two_F4) (h132fsu : Stmt13_3_2_three_fsu_F4)
    (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4) (h1327 : Stmt13_2_7_F4)
    (h39 : Vol2Native.A39ForSQTKCat) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K₀ : Subgroup G} (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hK₀ : K₀ ∈ lFamily S.Tv) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) (hLvK₀ : S.Lv ≤ K₀)
    (hchar : CharTwo (K₀ ⊔ S.Tv)) (hshort : IsShort2 K₀) {X : Type} [Group X] [CFSG.GH74.QTGen4.Finite4 X]
    (α : ↥K₀ →* X) (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K₀)
    {S₀ : Subgroup X} (hS₀ : IsSylowTwoOf S₀ ⊤)
    (hFix : ModelFix (blockLiftConj hshort α hα hker) S₀) : False := by
  obtain ⟨hcommA, he2U, hlA, hU2, hUc⟩ :=
    S.closing_data_blockU_F4 h1222 h517 hK₀G hK₀ hTK₀ hLvK₀ hchar hshort
  have hβe : ∀ (ℓ : ↥K₀) (u v : ↥(blockU K₀)), (v : G) = ℓ * u * ℓ⁻¹ →
      MonoidHom.id ↥(blockU K₀) v =
        blockLiftConj hshort α hα hker (α ℓ) (MonoidHom.id ↥(blockU K₀) u) := by
    intro ℓ u v h
    rw [blockLiftConj_apply]
    exact Subtype.ext h
  have hN2 : ∀ n : ↥(blockU K₀), n ^ 2 = 1 := fun n =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hU2 _ n.2)
  have hβk : (MonoidHom.id ↥(blockU K₀)).ker = (⊥ : Subgroup G).subgroupOf (blockU K₀) := by
    rw [Subgroup.bot_subgroupOf]
    exact MonoidHom.ker_id
  exact S.false_of_closing_model_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h39 hF hK₀G hK₀
    hTK₀ hz hLvK₀ (C1.le_normalizer_blockU K₀) (Zc := ⊥) bot_le hU2 hUc hcommA he2U hlA hN2
    (blockLiftConj hshort α hα hker) hS₀ hFix α hα (MonoidHom.id _) hβk hβe

end Setting

end CFSG.Quasithin.H13.A5
