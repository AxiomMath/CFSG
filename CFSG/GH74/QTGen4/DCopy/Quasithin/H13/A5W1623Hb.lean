module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1623b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Y1367c
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.H13.A5W1623End
public import CFSG.Quasithin.H13.A5W1623Tw

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Quasithin
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.BinaryParabolic
open scoped IsMulCommutative

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem map_Lv_eq_middle_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) {K : Subgroup G} (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    (hLvK : S.Lv ≤ K) {α : ↥K →* SpecialLinearGroup (Fin 4) (ZMod 2)}
    (hαC : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ Subgroup.centralizer (S.WK K : Set G))
    (hmapU : ((S.Tv ⊓ K).subgroupOf K).map α = unitriangular 4 (ZMod 2))
    (hgr : ∃ t ∈ S.Tv, ∃ u ∈ unitriangular 4 (ZMod 2), ∀ (l : ↥K) (h : t * l * t⁻¹ ∈ K),
      α ⟨t * l * t⁻¹, h⟩ = graphAut 4 (u * α l * u⁻¹)) :
    ((S.Lv ⊔ (S.Tv ⊓ K)).subgroupOf K).map α =
      flagStabilizer 4 (ZMod 2) (Set.Icc 1 (4 - 1) \ {2}) := by
  obtain ⟨j, hj, hjm, hP⟩ := S.eq_parabolic_of_sl_F4 h1222 h517 hLvK (m := 4) (by norm_num) hαC hmapU
  obtain ⟨t, ht, u, hu, htw⟩ := hgr
  have hTK : t ∈ Subgroup.normalizer ((S.Tv ⊓ K : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hT ht⟩
  have htX : t ∈ Subgroup.normalizer ((S.Lv ⊔ (S.Tv ⊓ K) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (S.Tv_le_normalizer_Lv ht),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hTK]
  set ψ : MulAut (SpecialLinearGroup (Fin 4) (ZMod 2)) := (MulAut.conj u).trans (graphAut 4)
    with hψdef
  have hψ : ∀ g, ψ g = graphAut 4 (u * g * u⁻¹) := fun g => rfl
  have hM : ∀ g ∈ flagStabilizer 4 (ZMod 2) (Set.Icc 1 (4 - 1) \ {j}),
      ψ g ∈ flagStabilizer 4 (ZMod 2) (Set.Icc 1 (4 - 1) \ {j}) := by
    intro g hg
    rw [← hP] at hg ⊢
    obtain ⟨l, hl, rfl⟩ := hg
    have hl' : (l : G) ∈ S.Lv ⊔ (S.Tv ⊓ K) := Subgroup.mem_subgroupOf.mp hl
    have htl : t * l * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hT ht) l).mp l.2
    rw [hψ, ← htw l htl]
    exact ⟨_, Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp htX l).mp hl'), rfl⟩
  have hmj := Ln2P.eq_of_graph_of_map_le hj hjm hu hψ hM
  obtain rfl : j = 2 := by omega
  exact hP

theorem reflection_two_not_mem_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) {K : Subgroup G} (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    (hLvK : S.Lv ≤ K) {α : ↥K →* SpecialLinearGroup (Fin 4) (ZMod 2)}
    (hαC : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ Subgroup.centralizer (S.WK K : Set G))
    (hmapU : ((S.Tv ⊓ K).subgroupOf K).map α = unitriangular 4 (ZMod 2))
    (hgr : ∃ t ∈ S.Tv, ∃ u ∈ unitriangular 4 (ZMod 2), ∀ (l : ↥K) (h : t * l * t⁻¹ ∈ K),
      α ⟨t * l * t⁻¹, h⟩ = graphAut 4 (u * α l * u⁻¹)) :
    reflection 4 (ZMod 2) 2 (by norm_num) (by norm_num) ∉
      ((K ⊓ Subgroup.centralizer ({S.z} : Set G)).subgroupOf K).map α := by
  intro hr
  set Hz := ((K ⊓ Subgroup.centralizer ({S.z} : Set G)).subgroupOf K).map α with hHz
  have hUH := S.unitriangular_le_map_centralizer_z hmapU
  have hM : flagStabilizer 4 (ZMod 2) (Set.Icc 1 (4 - 1) \ {2}) ≤ Hz := by
    rw [parabolic_eq_closure (n := 4) (j := 2) (by norm_num) (by norm_num), Subgroup.closure_le]
    rintro x (hx | hx)
    · exact hUH hx
    · rw [Set.mem_singleton_iff.mp hx]
      exact hr
  have hzW : S.z ∈ S.WK K := le_conjClosure _ _ (Subgroup.mem_zpowers _)
  apply S.not_Lv_le_centralizer_z
  intro l hl
  have hlK := hLvK hl
  have h1 : α ⟨l, hlK⟩ ∈ Hz := by
    apply hM
    rw [← S.map_Lv_eq_middle_F4 h1222 h517 hT hLvK hαC hmapU hgr]
    exact ⟨⟨l, hlK⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hl), rfl⟩
  obtain ⟨c, hc, hce⟩ := h1
  have hcz : (c : G) ∈ Subgroup.centralizer ({S.z} : Set G) := (Subgroup.mem_subgroupOf.mp hc).2
  have hW : ((c⁻¹ * ⟨l, hlK⟩ : ↥K) : G) ∈ Subgroup.centralizer (S.WK K : Set G) :=
    (hαC _).mp (by rw [map_mul, map_inv, hce, inv_mul_cancel])
  have h2 : S.z * ((c : G)⁻¹ * l) = ((c : G)⁻¹ * l) * S.z :=
    Subgroup.mem_centralizer_iff.mp hW S.z hzW
  rw [Subgroup.mem_centralizer_singleton_iff] at hcz ⊢
  calc l * S.z = (c : G) * (((c : G)⁻¹ * l) * S.z) := by group
    _ = (c : G) * (S.z * ((c : G)⁻¹ * l)) := by rw [h2]
    _ = ((c : G) * S.z) * ((c : G)⁻¹ * l) := by group
    _ = (S.z * c) * ((c : G)⁻¹ * l) := by rw [hcz]
    _ = S.z * l := by group

theorem b51Hyp_plus_F4 (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4)
    (hH : S.Hyp1367) {K : Subgroup G} (hYz : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) (hLvK : S.Lv ≤ K)
    (hker : IsPGroup 2 ↥(K ⊓ Subgroup.centralizer (S.WK K : Set G)))
    [IsMulCommutative ↥(S.WK K)] :
    B51Hyp (jStar (S.HK K) S.Tv (S.WK K)) (S.plus K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := hH.hF
  have hKG := hYz.1
  have hR := S.isTwoReducedIn_WK_F4 h1222 h517 hF hKG hT
  have hKH : K ≤ S.HK K := le_sup_left.trans le_sup_left
  have hKW : K ≤ Subgroup.normalizer (S.WK K : Set G) := hKH.trans hR.2.1
  have hWT := (S.WK_le_Tv_F4 h1222 h517 hF hKG hT).1
  set J := jStar (S.HK K) S.Tv (S.WK K) with hJ
  have hNJ : S.plus K ≤ J := S.plus_le_jStar_F4 h1222 h517 hF hYz hT
  have hJn : ∀ x ∈ J, ∀ n ∈ S.plus K, x * n * x⁻¹ ∈ S.plus K := fun x hx n hn =>
    (Subgroup.mem_normalizer_iff.mp (S.HK_le_normalizer_plus_F4 h1222 h517 hF hYz hT
      (jStar_le (S.Tv_le_HK K) hx)) n).mp hn
  have hq := S.isQuasisimple_plus_F4 h1222 h517 hF hYz hT
  have hO2 : pCoreOf 2 J = ⊥ := pCoreOf_jStar (S.Tv_le_HK K) hR
  have hJJ : J = ffJ J := jStar_eq_ffJ hR.2.2.1 hWT (S.Tv_le_HK K) hR.2.1

  have hT2 : IsPGroup 2 ↥S.Tv := (S.isSylowTwoOf_Tv_F4 h1222 h517).2.1
  obtain ⟨e, he⟩ := (IsPGroup.iff_card).mp hT2
  have h2' : ∀ y ∈ S.HK K, ∃ m : ℕ,
      y ^ 2 ^ m ∈ K ⊔ Subgroup.centralizer (S.WK K : Set G) := by
    intro y hy
    rw [S.HK_eq_sup hLvK] at hy
    obtain ⟨k₀, hk₀, s, hs, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hT).mp hy
    obtain ⟨k', hk', hpow⟩ :=
      CFSG.LieType.Chevalley.exists_mul_pow_eq_mul_pow hk₀ (hT hs) (2 ^ e)
    have hs1 : s ^ 2 ^ e = 1 := by
      have h1 := orderOf_dvd_natCard (⟨s, hs⟩ : ↥S.Tv)
      rw [he, Subgroup.orderOf_mk] at h1
      exact orderOf_dvd_iff_pow_eq_one.mp h1
    rw [hs1, mul_one] at hpow
    exact ⟨e, hpow ▸ Subgroup.mem_sup_left hk'⟩
  have h2 : ∀ y ∈ J, ∃ m : ℕ, y ^ 2 ^ m ∈ S.plus K := fun y hy =>
    InternalSec.autOn_two_of hKW h2' y (jStar_le (S.Tv_le_HK K) hy)
  have hFJ : quasithinGenFitting J = S.plus K :=
    InternalSec.quasithinGenFitting_eq_of_two_pow hNJ hJn (B1Red.isQuasisimple_to_open hq) h2 hO2
  have hZ : centerOf J ≤ S.plus K := hFJ ▸ InternalSec.centerOf_le_quasithinGenFitting J
  have hS : SQTKGroup ↥(S.plus K) := InternalSec.sqtkGroup_autOn hKW
    (InternalSec.sqtkGroup_mono (S.sqtkGroup_HK_F4 h1222 h517 hF hKG hT) hKH) hker
  exact ⟨by rw [hFJ, sup_eq_left.2 hZ], hq, hS, hNJ, hO2, hJJ⟩

end Setting

end CFSG.Quasithin.H13.A5
