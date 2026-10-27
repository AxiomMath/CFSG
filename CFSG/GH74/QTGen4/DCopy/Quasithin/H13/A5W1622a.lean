module

public import CFSG.Quasithin.H13.A5W1622a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1617c

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem a_mem_pCoreOf_F4 (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4)
    {H : Subgroup G} (hTH : S.Tv ≤ H) (hHG : H ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hH : CharTwo H) : S.a ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : IsSylowTwoOf S.Tv H :=
    C1GN.isSylowTwoOf_of_le (S.isSylowTwoOf_Tv_F4 h1222 h517) hTH hHG
  have hOT : pCoreOf 2 H ≤ S.Tv :=
    le_of_isPGroup_of_le_normalizer hsyl (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
      (hTH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  exact mem_pCoreOf_of_comm_mem hH S.isPGroup_zpowers_v12 (S.zpowers_v12_comm hHG)
    (hTH S.a_mem_Tv) fun r hr => S.comm_a_Tv (hOT hr)

theorem z_mem_pCoreOf_F4 (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4)
    {H : Subgroup G} (hTH : S.Tv ≤ H) (hHG : H ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hH : CharTwo H) : S.z ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : IsSylowTwoOf S.Tv H :=
    C1GN.isSylowTwoOf_of_le (S.isSylowTwoOf_Tv_F4 h1222 h517) hTH hHG
  have hOT : pCoreOf 2 H ≤ S.Tv :=
    le_of_isPGroup_of_le_normalizer hsyl (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
      (hTH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  refine mem_pCoreOf_of_comm_mem hH S.isPGroup_zpowers_v12 (S.zpowers_v12_comm hHG)
    (hTH S.z_mem_Tv) fun r hr => ?_
  have hr' : r ∈ T := (Subgroup.mem_inf.mp (hOT hr)).1
  have h1 : r * S.z * r⁻¹ = S.z := S.conj_z_of_mem_T hr'
  have hc : S.z * r = r * S.z := by
    calc S.z * r = (r * S.z * r⁻¹) * r := by rw [h1]
      _ = r * S.z := by group
  have e : S.z * r * S.z⁻¹ * r⁻¹ = 1 := by rw [hc]; group
  rw [e]
  exact Subgroup.one_mem _

theorem comm_mem_blockU_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) {K₀ : Subgroup G} (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hK₀p : ⁅K₀, K₀⁆ = K₀) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hchar : CharTwo (K₀ ⊔ S.Tv)) :
    (∀ k ∈ K₀, k⁻¹ * S.a * k * S.a⁻¹ ∈ blockU K₀) ∧
      ∀ k ∈ K₀, k⁻¹ * S.z * k * S.z⁻¹ ∈ blockU K₀ := by
  have hHG : K₀ ⊔ S.Tv ≤ Subgroup.centralizer ({S.v12} : Set G) := sup_le hK₀G S.Tv_le_Gv
  exact ⟨comm_mem_blockU_of_mem_pCoreOf le_sup_left hK₀p
      (S.a_mem_pCoreOf_F4 h1222 h517 le_sup_right hHG hchar) (hTK₀ S.a_mem_Tv),
    comm_mem_blockU_of_mem_pCoreOf le_sup_left hK₀p
      (S.z_mem_pCoreOf_F4 h1222 h517 le_sup_right hHG hchar) (hTK₀ S.z_mem_Tv)⟩

theorem false_of_comm_mem_of_fixed_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h132two : Stmt13_3_2_two_F4) (h132fsu : Stmt13_3_2_three_fsu_F4)
    (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4) (h1327 : Stmt13_2_7_F4)
    (h39 : Vol2Native.A39ForSQTKCat) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K₀ : Subgroup G} (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hK₀ : K₀ ∈ lFamily S.Tv) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) {A : Subgroup G}
    (hA2 : ∀ x ∈ A, x ^ 2 = 1) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hK₀A : K₀ ≤ Subgroup.normalizer (A : Set G))
    (hcomm : ∀ k ∈ K₀, k⁻¹ * S.a * k * S.a⁻¹ ∈ A) {Y : Subgroup G} (hYK : Y ≤ K₀)
    (hYa : ∀ y ∈ Y, y * S.a * y⁻¹ = S.a)
    (hfix : ∀ m ∈ A, (∀ y ∈ Y, y * m * y⁻¹ = m) → ∀ k ∈ K₀, k * m * k⁻¹ = m) : False := by
  classical
  have hK₀p : ⁅K₀, K₀⁆ = K₀ := perfect_of_mem_cComp hK₀

  have hsylH : IsSylowTwoOf S.Tv (K₀ ⊔ S.Tv) :=
    C1GN.isSylowTwoOf_of_le (S.isSylowTwoOf_Tv_F4 h1222 h517) le_sup_right
      (sup_le hK₀G S.Tv_le_Gv)
  have hS₀ : IsSylowTwoOf (S.Tv ⊓ K₀) K₀ :=
    A4.isSylowTwoOf_inf_normal hsylH le_sup_left (sup_le Subgroup.le_normalizer hTK₀)

  let ρ : ↥K₀ →* MulAut ↥A := (conjAct A).comp (Subgroup.inclusion hK₀A)
  have hρ : ∀ (g : ↥K₀) (u : ↥A), ((ρ g u : ↥A) : G) = g * u * (g : G)⁻¹ := fun g u =>
    InternalSec.coe_conjAct_apply _ u
  let δ : ↥K₀ → ↥A := fun k => ⟨(k : G)⁻¹ * S.a * k * S.a⁻¹, hcomm k k.2⟩
  have hδ : ∀ g h, δ (g * h) = ρ h⁻¹ (δ g) * δ h := by
    intro g h
    apply Subtype.ext
    rw [Subgroup.coe_mul, hρ]
    simp only [δ, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hA2' : ∀ u : ↥A, u ^ 2 = 1 := fun u =>
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hA2 u u.2)
  have : IsMulCommutative ↥A := ⟨⟨fun u w => Subtype.ext (hAc u u.2 w w.2)⟩⟩
  set Z₀ : Subgroup ↥A := (Subgroup.zpowers S.v12).subgroupOf A with hZ₀def
  have hZ₀ : ∀ g, ∀ z ∈ Z₀, ρ g z = z := by
    intro g z hz
    apply Subtype.ext
    rw [hρ]
    have hzv : (z : G) ∈ Subgroup.zpowers S.v12 := hz
    rw [← S.zpowers_v12_comm hK₀G _ hzv _ g.2, mul_inv_cancel_right]
  set D : Subgroup ↥K₀ := (S.Tv ⊓ K₀).subgroupOf K₀ with hDdef
  have hD : ∀ d ∈ D, δ d ∈ Z₀ := by
    intro d hd
    have hdT : (d : G) ∈ S.Tv := (Subgroup.mem_subgroupOf.mp hd).1
    show (d : G)⁻¹ * S.a * d * S.a⁻¹ ∈ Subgroup.zpowers S.v12
    have h1 := S.comm_a_Tv (S.Tv.inv_mem hdT)
    have e : (d : G)⁻¹ * S.a * d * S.a⁻¹ = (S.a * (d : G)⁻¹ * S.a⁻¹ * (d : G)⁻¹⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ h1
  have hodd : ¬ 2 ∣ D.index := hS₀.2.2
  have hperf : commutator ↥K₀ = ⊤ := Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hK₀p)
  obtain ⟨m, hm⟩ := exists_coboundary_of_odd_index hA2' ρ δ hδ Z₀ hZ₀ D hD hodd hperf
  have hmk : ∀ k : ↥K₀, (k : G)⁻¹ * S.a * k * S.a⁻¹ = (k : G)⁻¹ * m * k * (m : G)⁻¹ := by
    intro k
    have h1 := congrArg Subtype.val (hm k)
    rw [Subgroup.coe_mul, hρ, Subgroup.coe_inv] at h1
    simp only [δ, Subgroup.coe_inv, inv_inv] at h1
    rw [h1]

  have hmY : ∀ y ∈ Y, y * (m : G) * y⁻¹ = m := by
    intro y hy
    have h1 := hmk ⟨y, hYK hy⟩
    have h2 : y⁻¹ * S.a * y * S.a⁻¹ = 1 := by
      have h3 : S.a * y = y * S.a := by
        calc S.a * y = (y * S.a * y⁻¹) * y := by rw [hYa y hy]
          _ = y * S.a := by group
      calc y⁻¹ * S.a * y * S.a⁻¹ = y⁻¹ * (S.a * y) * S.a⁻¹ := by group
        _ = 1 := by rw [h3]; group
    have h4 : y⁻¹ * (m : G) * y * (m : G)⁻¹ = 1 := by rw [← h2]; exact h1.symm
    calc y * (m : G) * y⁻¹ = y * (y⁻¹ * (m : G) * y * (m : G)⁻¹)⁻¹ * y⁻¹ * m := by group
      _ = m := by rw [h4]; group
  have hmK := hfix m m.2 hmY

  have hK₀a : K₀ ≤ Subgroup.centralizer ({S.a} : Set G) := by
    intro k hk
    have h1 := hmk ⟨k, hk⟩
    have h3 : k⁻¹ * (m : G) * k * (m : G)⁻¹ = 1 := by
      have h5 : (m : G) * k = k * m := by
        calc (m : G) * k = (k * m * k⁻¹) * k := by rw [hmK k hk]
          _ = k * m := by group
      calc k⁻¹ * (m : G) * k * (m : G)⁻¹ = k⁻¹ * ((m : G) * k) * (m : G)⁻¹ := by group
        _ = 1 := by rw [h5]; group
    have h4 : k⁻¹ * S.a * k * S.a⁻¹ = 1 := h1.trans h3
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h5 : S.a * k = k * S.a := by
      calc S.a * k = k * (k⁻¹ * S.a * k * S.a⁻¹) * S.a := by group
        _ = k * S.a := by rw [h4]; group
    exact h5.symm
  obtain ⟨g, -, hga⟩ := S.exists_conj_a
  refine S.not_le_centralizer_conj_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h39 hF hK₀G hK₀
    hTK₀ hz g (fun t ht => by rw [hga]; exact S.comm_a_Tv ht) ?_
  rw [hga]
  exact hK₀a

end Setting

end CFSG.Quasithin.H13.A5
