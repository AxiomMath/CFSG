module

public import CFSG.Quasithin.H13.A5S136o
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136m

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Quasithin
open CFSG.Quasithin.A5Model
open scoped commutatorElement

@[expose] def FactConfSpor_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (K X Q : Subgroup G) (a z l : G)
    (s : TauCeti.SporadicName), CFSG.IsQuasisimple ↥K → IsLemma115SporadicName s →
    Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* NativeSporadic.Carrier s) → ¬ Conf1366 K X Q a z l

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem isSylowTwoOf_Tv_inf_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    {K : Subgroup G} (hK : IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G))) :
    IsSylowTwoOf (S.Tv ⊓ (Subgroup.centralizer ({S.v12} : Set G) ⊓
      Subgroup.normalizer (K : Set G)))
      (Subgroup.centralizer ({S.v12} : Set G) ⊓ Subgroup.normalizer (K : Set G)) := by
  have : IsSimpleGroup G := S.h13.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  have hsyl : IsSylowTwoOf S.Tv Gv :=
    S.isSylowTwoOf_centralizer_F4 h1222 h517 S.v12_mem_V2 S.v12_not_mem_V1
  have hO2 := (S.lemma115Hyp_Gv_F4 h1222 h517).pCore_ne_bot
  have hKG : K ≤ Gv := hK.1
  have hKc : K ∈ cComp Gv := by
    have h2 := map_subtype_mem_cComp (mem_cComp_top_of_isComponent hK.2)
    rwa [Subgroup.map_subgroupOf_eq_of_le hKG] at h2
  refine A4.isSylowTwoOf_inf_normal hsyl inf_le_left ?_
  rcases Vol2Native.lemma_1_2_1_three hloc h37 h38 hO2 hKc with hn | ⟨h2, -⟩
  · have hGN : Gv ≤ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKG).mp hn
    rw [inf_eq_left.mpr hGN]
    exact Subgroup.le_normalizer
  · rw [ncard_conjSubgroupsBy_eq_index] at h2
    have hn : ((Subgroup.normalizer (K : Set G)).subgroupOf Gv).Normal :=
      Subgroup.normal_of_index_eq_two h2
    have he : (Gv ⊓ Subgroup.normalizer (K : Set G)).subgroupOf Gv =
        (Subgroup.normalizer (K : Set G)).subgroupOf Gv := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [← he] at hn
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mp hn

theorem exists_conf1366_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    {K : Subgroup G} (hK : IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G)))
    (hinner : InducesInner S.z K) :
    ∃ (X Q : Subgroup G) (y : G), Conf1366 K X Q S.a S.z y := by
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  have hHyp := S.lemma115Hyp_Gv_F4 h1222 h517
  obtain ⟨hzN, -, hzM, -⟩ := hHyp.component_action hK
  have hzK : ¬ K ≤ Subgroup.centralizer ({S.z} : Set G) := hzM
  have hKG : K ≤ Gv := hK.1
  have hKc : K ∈ cComp Gv := by
    have h2 := map_subtype_mem_cComp (mem_cComp_top_of_isComponent hK.2)
    rwa [Subgroup.map_subgroupOf_eq_of_le hKG] at h2
  have hLvN := S.Lv_le_normalizer_of_mem_cComp_F4 h1222 h517 h37 h38 hKc
  have hsyl : IsSylowTwoOf S.Tv Gv :=
    S.isSylowTwoOf_centralizer_F4 h1222 h517 S.v12_mem_V2 S.v12_not_mem_V1
  obtain ⟨l, hlK, hl⟩ := hinner
  have hlZ := not_mem_centralizer_of_inner hl hzK
  have hl2 := sq_mem_centralizer_of_inner S.z_sq hl hlK
  have haN := S.a_mem_normalizer hK hsyl hlK hl2 hlZ
  obtain ⟨y, hyLv, hyodd, hyz⟩ := S.exists_Lv_odd hKG hLvN hzK
  have hzTv : S.z ∈ S.Tv := (S.lemma115Hyp_Gv_F4 h1222 h517).z_mem
  have hzGv : S.z ∈ Gv := hsyl.1 hzTv
  have hTvT : S.Tv ≤ T := inf_le_left
  have hvC : ∀ k : ℤ, S.v12 ^ k ∈ Subgroup.centralizer (K : Set G) := by
    intro k
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hKG hx)) k).eq
  refine ⟨Gv ⊓ Subgroup.normalizer (K : Set G), S.Tv ⊓ (Gv ⊓ Subgroup.normalizer (K : Set G)), y,
    le_inf hKG Subgroup.le_normalizer, inf_le_right,
    S.isSylowTwoOf_Tv_inf_F4 h1222 h517 h37 h38 hK, ⟨S.a_mem_Tv, S.a_mem_Gv, haN⟩,
    ⟨hzTv, hzGv, hzN⟩, S.a_sq, S.z_sq, fun t ht => ?_, fun t ht => ?_, fun haC => ?_,
    fun hzC => hzK (le_centralizer_of_mem hzC), S.mul_inv_not_mem_centralizer hKG hLvN hzK,
    ⟨l, hlK, hl⟩, hLvN hyLv, hyodd, ?_, hyz⟩
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (S.comm_a_Tv (Subgroup.mem_inf.mp ht).1)
    rw [← hk]
    exact hvC k
  · have := S.conj_z_of_mem_T (hTvT (Subgroup.mem_inf.mp ht).1)
    have e : S.z * t * S.z⁻¹ * t⁻¹ = 1 := by
      calc S.z * t * S.z⁻¹ * t⁻¹ = S.z * (t * S.z * t⁻¹)⁻¹ := by group
        _ = 1 := by rw [this]; group
    rw [e]
    exact Subgroup.one_mem _
  · exact S.not_le_centralizer_a hK (le_centralizer_of_mem haC)
  · rw [S.Lv_comm_a hyLv, mul_inv_cancel]
    exact Subgroup.one_mem _

end Setting

theorem elim1366EF_of_F4 (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hL33 : FactConfL33)
    (hL2 : FactConfL2) (hSp : FactConfSpor_F4) : Elim1366EF_F4 := by
  intro G _ _ T L V S hab K hK hcase
  have hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G) := hK.1
  have hqs : CFSG.IsQuasisimple ↥K :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hKG)).1 hK.2.1
  have hinner : InducesInner S.z K := by
    rcases hcase with ⟨-, h⟩ | ⟨-, ⟨l, hl, hlx, -⟩⟩
    · exact h
    · exact ⟨l, hl, hlx⟩
  obtain ⟨X, Q, y, hconf⟩ := S.exists_conf1366_F4 h1222 h517 h37 h38 hK hinner
  rcases hcase with ⟨h33 | ⟨p, hp, hp2⟩, -⟩ | ⟨⟨s, hs, he⟩, -⟩
  · exact hL33 G K X Q S.a S.z y hqs h33 hconf
  · exact hL2 G K X Q S.a S.z y p hqs hp hp2 hconf
  · exact hSp G K X Q S.a S.z y s hqs hs he hconf

end CFSG.Quasithin.H13.A5
