module

public import CFSG.Quasithin.H13.A5W1622b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5X1367d

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

variable {S}

variable (S)

theorem e23_mem_pCoreOf_F4 (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4)
    {H : Subgroup G} (hTH : S.Tv ≤ H) (hHG : H ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hH : CharTwo H) : S.e2 ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : IsSylowTwoOf S.Tv H :=
    C1GN.isSylowTwoOf_of_le (S.isSylowTwoOf_Tv_F4 h1222 h517) hTH hHG
  have hOT : pCoreOf 2 H ≤ S.Tv :=
    le_of_isPGroup_of_le_normalizer hsyl (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
      (hTH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  have he2T : S.e2 ∈ S.Tv := by
    refine ⟨S.V_le_T S.e2_mem_V, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg Subtype.val
      (S.elemAbelian_V.1.is_comm.comm ⟨S.e2, S.e2_mem_V⟩ ⟨S.v12, S.v12_mem_V⟩)
  refine mem_pCoreOf_of_comm_mem hH S.isPGroup_zpowers_v12 (S.zpowers_v12_comm hHG)
    (hTH he2T) fun r hr => ?_
  have h1 : r * S.e2 * r⁻¹ = S.e2 := S.conj_e2_of_mem_Tv (hOT hr)
  have hc : S.e2 * r = r * S.e2 := by
    calc S.e2 * r = (r * S.e2 * r⁻¹) * r := by rw [h1]
      _ = r * S.e2 := by group
  have e : S.e2 * r * S.e2⁻¹ * r⁻¹ = 1 := by rw [hc]; group
  rw [e]
  exact Subgroup.one_mem _

theorem e2_q_mem_blockU_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) {K₀ : Subgroup G} (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hK₀p : ⁅K₀, K₀⁆ = K₀) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hchar : CharTwo (K₀ ⊔ S.Tv)) (hLvK₀ : S.Lv ≤ K₀) {y : G} (hy : y ∈ S.Lv)
    (hyN : y ∈ Subgroup.normalizer (V : Set G))
    (hτ : S.frame.ρ ⟨y, hyN⟩ = c234 ∨ S.frame.ρ ⟨y, hyN⟩ = c234⁻¹) :
    S.e2 ∈ blockU K₀ ∧ y * S.e2 * y⁻¹ ∈ blockU K₀ := by
  have hHG : K₀ ⊔ S.Tv ≤ Subgroup.centralizer ({S.v12} : Set G) := sup_le hK₀G S.Tv_le_Gv
  have he2O := S.e23_mem_pCoreOf_F4 h1222 h517 le_sup_right hHG hchar
  have he2N : S.e2 ∈ Subgroup.normalizer (K₀ : Set G) := by
    have he2T : S.e2 ∈ S.Tv := by
      refine ⟨S.V_le_T S.e2_mem_V, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      exact congrArg Subtype.val
        (S.elemAbelian_V.1.is_comm.comm ⟨S.e2, S.e2_mem_V⟩ ⟨S.v12, S.v12_mem_V⟩)
    exact hTK₀ he2T
  have hc := comm_mem_blockU_of_mem_pCoreOf le_sup_left hK₀p he2O he2N
  have hyK₀ : y ∈ K₀ := hLvK₀ hy

  have h1 : y * S.e2 * y⁻¹ * S.e2⁻¹ ∈ blockU K₀ := by
    have := hc y⁻¹ (K₀.inv_mem hyK₀)
    simpa using this
  have h2 : y⁻¹ * S.e2 * y * S.e2⁻¹ ∈ blockU K₀ := hc y hyK₀

  have hτ' : S.frame.ρ ⟨y, hyN⟩ ∈ ({c234, c234⁻¹} : Finset (Equiv.Perm (Fin 5))) := by
    rcases hτ with h | h <;> simp [h]
  have hprod := e23_eq_prod _ hτ'
  have hqV : y * S.e2 * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hyN _).mp S.e2_mem_V
  have hyN' : y⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ hyN
  have hq'V : y⁻¹ * S.e2 * y ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp hyN' _).mp S.e2_mem_V
    simpa using this
  have he2eq : S.e2 = (y * S.e2 * y⁻¹ * S.e2⁻¹) * (y⁻¹ * S.e2 * y * S.e2⁻¹) := by
    have hm1 : y * S.e2 * y⁻¹ * S.e2⁻¹ ∈ V := V.mul_mem hqV (V.inv_mem S.e2_mem_V)
    have hm2 : y⁻¹ * S.e2 * y * S.e2⁻¹ ∈ V := V.mul_mem hq'V (V.inv_mem S.e2_mem_V)
    have hψ1 : S.frame.ψ ⟨y * S.e2 * y⁻¹ * S.e2⁻¹, hm1⟩ =
        pact (S.frame.ρ ⟨y, hyN⟩) e23 * e23⁻¹ := by
      have e : (⟨y * S.e2 * y⁻¹ * S.e2⁻¹, hm1⟩ : ↥V) = ⟨_, hqV⟩ * (⟨S.e2, S.e2_mem_V⟩)⁻¹ := rfl
      rw [e, map_mul, map_inv, S.psi_conj ⟨y, hyN⟩ ⟨S.e2, S.e2_mem_V⟩, S.psi_e2]
    have hρinv : S.frame.ρ ⟨y⁻¹, hyN'⟩ = (S.frame.ρ ⟨y, hyN⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    have hψ2 : S.frame.ψ ⟨y⁻¹ * S.e2 * y * S.e2⁻¹, hm2⟩ =
        pact (S.frame.ρ ⟨y, hyN⟩)⁻¹ e23 * e23⁻¹ := by
      have hq'V' : y⁻¹ * S.e2 * y⁻¹⁻¹ ∈ V := by simpa using hq'V
      have e : (⟨y⁻¹ * S.e2 * y * S.e2⁻¹, hm2⟩ : ↥V) =
          ⟨y⁻¹ * S.e2 * y⁻¹⁻¹, hq'V'⟩ * (⟨S.e2, S.e2_mem_V⟩)⁻¹ := Subtype.ext (by simp)
      rw [e, map_mul, map_inv, S.psi_conj ⟨y⁻¹, hyN'⟩ ⟨S.e2, S.e2_mem_V⟩, S.psi_e2, hρinv]
    have hm12 : (y * S.e2 * y⁻¹ * S.e2⁻¹) * (y⁻¹ * S.e2 * y * S.e2⁻¹) ∈ V := V.mul_mem hm1 hm2
    have h3 : S.frame.ψ ⟨S.e2, S.e2_mem_V⟩ = S.frame.ψ ⟨_, hm12⟩ := by
      have e : (⟨_, hm12⟩ : ↥V) = ⟨_, hm1⟩ * ⟨_, hm2⟩ := rfl
      rw [e, map_mul, hψ1, hψ2, S.psi_e2]
      exact hprod
    exact congrArg Subtype.val (S.frame.ψ.injective h3)
  have he2U : S.e2 ∈ blockU K₀ := by
    rw [he2eq]
    exact (blockU K₀).mul_mem h1 h2
  refine ⟨he2U, ?_⟩
  have e : y * S.e2 * y⁻¹ = (y * S.e2 * y⁻¹ * S.e2⁻¹) * S.e2 := by group
  rw [e]
  exact (blockU K₀).mul_mem h1 he2U

end Setting

end CFSG.Quasithin.H13.A5
