module

public import CFSG.Quasithin.H13.A5W1622n
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622m

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped Matrix

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem comm_mem_z0Of_F4 (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4)
    {K₀ : Subgroup G} (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hK₀p : ⁅K₀, K₀⁆ = K₀) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hchar : CharTwo (K₀ ⊔ S.Tv)) :
    ∀ k ∈ K₀, k⁻¹ * S.a * k * S.a⁻¹ ∈ ⁅z0Of S.v12 K₀, K₀⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcommA, -⟩ := S.comm_mem_blockU_F4 h1222 h517 hK₀G hK₀p hTK₀ hchar
  obtain ⟨hQO, -, -, hUQ⟩ := S.c134Q_facts_F4 h1222 h517 hK₀G hTK₀
  set O := pCoreOf 2 K₀ with hOdef
  have hOK : O ≤ K₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 K₀
  have hKO : K₀ ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₀

  have hsyl : IsSylowTwoOf S.Tv (K₀ ⊔ S.Tv) :=
    C1GN.isSylowTwoOf_of_le (S.isSylowTwoOf_Tv_F4 h1222 h517) le_sup_right (sup_le hK₀G S.Tv_le_Gv)
  have hnorm : (K₀.subgroupOf (K₀ ⊔ S.Tv)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer hTK₀)
  have hOT : O ≤ S.Tv :=
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 K₀ (K₀ ⊔ S.Tv)
      le_sup_left hnorm).trans (pCoreOf_le_of_isSylowTwoOf hsyl)

  have hUO : blockU K₀ ≤ O := by
    rw [blockU, Subgroup.commutator_le]
    intro r hr k hk
    have h1 : k * r⁻¹ * k⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (hKO hk) _).mp (O.inv_mem hr)
    rw [commutatorElement_def]
    have e : r * k * r⁻¹ * k⁻¹ = r * (k * r⁻¹ * k⁻¹) := by group
    rw [e]
    exact O.mul_mem hr h1

  set s : Set G := {x | x ∈ O ∧ ∀ r ∈ O, x * r * x⁻¹ * r⁻¹ ∈ Subgroup.zpowers S.v12} with hs
  have hZ0K : z0Of S.v12 K₀ ≤ K₀ := (Subgroup.closure_le _).mpr fun x hx => hOK hx.1
  have hKZ0 : K₀ ≤ Subgroup.normalizer ((z0Of S.v12 K₀ : Subgroup G) : Set G) := by
    refine le_normalizer_closure fun g hg x hx => ⟨?_, fun r hr => ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hKO hg) x).mp hx.1
    · have hr' : g⁻¹ * r * g ∈ O := by
        have := (Subgroup.mem_normalizer_iff.mp (hKO (K₀.inv_mem hg)) r).mp hr
        simpa using this
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hx.2 _ hr')
      have hgv : g * S.v12 ^ m = S.v12 ^ m * g :=
        (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hK₀G hg)) m).eq
      have e : g * x * g⁻¹ * r * (g * x * g⁻¹)⁻¹ * r⁻¹ =
          g * (x * (g⁻¹ * r * g) * x⁻¹ * (g⁻¹ * r * g)⁻¹) * g⁻¹ := by group
      rw [e, ← hm, hgv, mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers _ _
  have haN : S.a ∈ Subgroup.normalizer (K₀ : Set G) := hTK₀ S.a_mem_Tv
  refine comm_mem_commutator_of_perfect hZ0K hKZ0 hK₀p haN fun k hk => ?_
  refine Subgroup.subset_closure ⟨hUO (hcommA k hk), fun r hr => ?_⟩
  have hkr : k * r * k⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hKO hk) r).mp hr
  exact S.comm_conj_a_mem_zpowers (hK₀G hk) (hOT hr) (hOT hkr)

theorem e2_mem_center_c134Q_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) {K₀ : Subgroup G} (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hK₀p : ⁅K₀, K₀⁆ = K₀) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hchar : CharTwo (K₀ ⊔ S.Tv)) (hLvK₀ : S.Lv ≤ K₀) :
    S.e2 ∈ centerOf (c134Q (K₀ ⊔ S.Tv) K₀) := by
  obtain ⟨-, hQT, -, hUQ⟩ := S.c134Q_facts_F4 h1222 h517 hK₀G hTK₀
  obtain ⟨y₀, hy₀, hy₀N, hτ₀⟩ := S.exists_Lv_line
  obtain ⟨he2U, -⟩ := S.e2_q_mem_blockU_F4 h1222 h517 hK₀G hK₀p hTK₀ hchar hLvK₀ hy₀ hy₀N hτ₀
  refine ⟨hUQ he2U, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
  have h := S.conj_e2_of_mem_Tv (hQT hr)
  calc r * S.e2 = (r * S.e2 * r⁻¹) * r := by group
    _ = S.e2 * r := by rw [h]

end Setting

end CFSG.Quasithin.H13.A5
