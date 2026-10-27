module

public import CFSG.Quasithin.H13.A5W1622g
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622e

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.SteinbergBR.SmallAlt (a6P a6P_mul a6P_inv a6P_one a6P_sign a6P_injective)

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem false_of_altBlock6_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h132two : Stmt13_3_2_two_F4) (h132fsu : Stmt13_3_2_three_fsu_F4)
    (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4) (h1327 : Stmt13_2_7_F4)
    (h39 : Vol2Native.A39ForSQTKCat) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K₀ : Subgroup G} (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hK₀ : K₀ ∈ lFamily S.Tv) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) (hLvK₀ : S.Lv ≤ K₀)
    (hchar : CharTwo (K₀ ⊔ S.Tv)) (hblk : IsAltBlockType K₀ 6) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK₀p : ⁅K₀, K₀⁆ = K₀ := perfect_of_mem_cComp hK₀
  obtain ⟨⟨-, -, ⟨hUQ, hU2⟩, -, -⟩, α, hα, -, β, hβ, hβk, hβe⟩ := hblk
  have hQn : K₀ ≤ Subgroup.normalizer (blockQ K₀ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₀
  have hKU : K₀ ≤ Subgroup.normalizer (blockU K₀ : Set G) :=
    le_normalizer_commutator hQn Subgroup.le_normalizer
  have hUc : ∀ x ∈ blockU K₀, ∀ x' ∈ blockU K₀, x * x' = x' * x := fun x hx x' hx' =>
    (Subgroup.mem_centralizer_iff.mp (hUQ hx).2 x' (hUQ hx').1).symm
  obtain ⟨hcommA, -⟩ := S.comm_mem_blockU_F4 h1222 h517 hK₀G hK₀p hTK₀ hchar
  obtain ⟨y₀, hy₀, hy₀N, hτ₀⟩ := S.exists_Lv_line
  obtain ⟨he2U, -⟩ := S.e2_q_mem_blockU_F4 h1222 h517 hK₀G hK₀p hTK₀ hchar hLvK₀ hy₀ hy₀N hτ₀
  have hlA : ∀ y ∈ S.Lv, y * S.e2 * y⁻¹ ∈ blockU K₀ := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hKU (hLvK₀ hy)) _).mp he2U
  have hβe' : ∀ (ℓ : ↥K₀) (u v : ↥(blockU K₀)), (v : G) = ℓ * u * ℓ⁻¹ →
      β v = heartAct6 (α ℓ) (β u) := by
    intro ℓ u v h
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (β u))
    apply Multiplicative.toAdd.injective
    rw [heartAct6_apply, toAdd_ofAdd, ← hx, SBc9.heartAct_mk]
    exact (hβe ℓ u v h x hx).symm
  have hN2 : ∀ n : Multiplicative (AltHeart 6), n ^ 2 = 1 := by
    intro n
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd n)
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, ← hx, ← QuotientAddGroup.mk_nsmul]
    have h2x : 2 • x = 0 := by
      apply Subtype.ext
      funext i
      simp only [AddSubgroup.coe_nsmul, Pi.smul_apply, AddSubgroup.coe_zero, Pi.zero_apply]
      rw [two_nsmul, CharTwo.add_self_eq_zero]
    rw [h2x, QuotientAddGroup.mk_zero]
  exact S.false_of_closing_model_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h39 hF hK₀G hK₀
    hTK₀ hz hLvK₀ hKU (Zc := blockZ K₀) inf_le_right hU2 hUc hcommA he2U hlA hN2 heartAct6
    isSylowTwoOf_a6Syl modelFix_a6 α hα β hβk hβe'

end Setting

end CFSG.Quasithin.H13.A5
