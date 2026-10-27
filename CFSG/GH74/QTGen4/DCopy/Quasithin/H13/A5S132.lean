module

public import CFSG.Quasithin.H13.A5S132
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5F91
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem conjugate_eq_or_inf_eq_bot_F4 (h1222 : Stmt12_2_2_F4) {m : G}
    (hm : m ∈ Subgroup.normalizer (L : Set G)) :
    CFSG.conjugate V m = V ∨ V ⊓ CFSG.conjugate V m = ⊥ := by
  rcases h1222 G T S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow with h | h
  · exact absurd h S.not_alt12_2_2
  · exact ((h L S.maximal S.h13.faithful S.fsu.quasisimple).2.2 V S.irr).2.1 m hm

theorem mem_normalizer_V_of_F4 (h1222 : Stmt12_2_2_F4) {m : G}
    (hm : m ∈ Subgroup.normalizer (L : Set G)) {U : Subgroup G} (hU : U ≠ ⊥) (hUV : U ≤ V)
    (hmU : m ∈ Subgroup.normalizer (U : Set G)) : m ∈ Subgroup.normalizer (V : Set G) := by
  rcases S.conjugate_eq_or_inf_eq_bot_F4 h1222 hm with h | h
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [← mem_conjugate_iff', h]
  · exfalso
    apply hU
    rw [eq_bot_iff, ← h]
    intro u hu
    exact ⟨hUV hu, mem_conjugate_iff'.mpr (hUV ((Subgroup.mem_normalizer_iff.mp hmU u).mp hu))⟩

theorem M_inf_centralizer_V3_le_F4 (h1222 : Stmt12_2_2_F4) :
    Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (S.V3 : Set G) ≤
      Subgroup.centralizer (V : Set G) := by
  rintro m ⟨hm, hmC⟩
  have hmN := S.mem_normalizer_V_of_F4 h1222 hm S.V3_ne_bot S.V3_le_V
    (Subgroup.centralizer_le_normalizer _ hmC)
  exact S.mem_centralizer_V_of_V3 hmN hmC

theorem R_sylow_CV3_F4 (h1222 : Stmt12_2_2_F4) :
    IsSylowTwoOf (pCoreOf 2 (L ⊔ T)) (Subgroup.centralizer (S.V3 : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [A4.isSylowTwoOf_iff_maximal]
  refine ⟨S.R_le_CV3, pCoreOf_isPGroup 2 _, fun P hPC hP hRP => ?_⟩
  by_contra hPR
  obtain ⟨x, hxP, hxR, hxN⟩ := exists_mem_normalizer_not_mem hP
    (lt_of_le_of_ne hRP fun h => hPR h.ge)
  have hxCV : x ∈ Subgroup.centralizer (V : Set G) :=
    S.M_inf_centralizer_V3_le_F4 h1222 ⟨S.normalizer_R_le hxN, hPC hxP⟩
  have hmax := (A4.isSylowTwoOf_iff_maximal.mp S.R_sylow_CV).2.2
  have hle : pCoreOf 2 (L ⊔ T) ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer (V : Set G) :=
    sup_le S.R_sylow_CV.1 (Subgroup.zpowers_le.mpr hxCV)
  have h2 : IsPGroup 2 ↥(pCoreOf 2 (L ⊔ T) ⊔ Subgroup.zpowers x) :=
    hP.to_le (sup_le hRP (Subgroup.zpowers_le.mpr hxP))
  exact hxR (hmax _ hle h2 le_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))

theorem centralizer_V3_le_F4 (h311 : Theorem311Stmt) (h1222 : Stmt12_2_2_F4) :
    Subgroup.centralizer (S.V3 : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hCM
  have hTC : T ≤ Subgroup.normalizer (Subgroup.centralizer (S.V3 : Set G) : Set G) :=
    S.T_le_NV3.trans (normalizer_le_normalizer_centralizer' _)

  have hV3X : S.V3 ≤ pCoreOf 2 (Subgroup.centralizer (S.V3 : Set G) ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((S.V3_le_V.trans S.V_le_T).trans le_sup_right)
      (sup_le (Subgroup.centralizer_le_normalizer _) S.T_le_NV3) (S.isPGroup_V.to_le S.V3_le_V)
  have hX : InH T (Subgroup.centralizer (S.V3 : Set G) ⊔ T) :=
    ⟨le_sup_right, fun h => S.V3_ne_bot (le_bot_iff.mp (h ▸ hV3X))⟩
  obtain ⟨H, hH, hHX⟩ := exists_isHStar_le' (M := Subgroup.normalizer (L : Set G)) hX
    fun h => hCM (le_sup_left.trans h)

  have hO2H : oTwoUpper H ≤ Subgroup.centralizer (S.V3 : Set G) := by
    refine oTwoUpper_le_of_pow_mem fun x hx => ?_
    have hx' : x ∈ ((Subgroup.centralizer (S.V3 : Set G) : Set G) * (T : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ T hTC]
      exact hHX hx
    obtain ⟨c, hc, t, ht, rfl⟩ := hx'
    obtain ⟨a, ha⟩ := S.isPGroup_T ⟨t, ht⟩
    have hta : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    obtain ⟨c', hc', he⟩ := pow_mem_mul_of_normalizes hc (hTC ht) (2 ^ a)
    rw [hta, mul_one] at he
    exact ⟨a, he ▸ hc'⟩

  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo S.h13.sylow
  have hU : IsUniqueMaxOver H T (H ⊓ Subgroup.normalizer (L : Set G)) := by
    have := IsHStar.isUniqueMaxOver P (hP ▸ hH) (hP ▸ S.T_le_NL)
    rwa [hP] at this

  obtain ⟨R0, hR0, hR0R, hN⟩ := h311 G T S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow
    (L ⊔ T) H (pCoreOf 2 (L ⊔ T)) ⟨le_sup_right, S.R_ne_bot⟩ hH.1 ⟨_, hU⟩ S.R_ne_bot
    S.pCoreOf_LT_le_T
    (A4.isSylowTwoOf_mono (S.R_sylow_CV3_F4 h1222) le_sup_right (sup_le hO2H S.R_le_CV3))
    (le_normalizer_pCoreOf 2 _)

  have hR02 : IsPGroup 2 R0 := (pCoreOf_isPGroup 2 _).to_le hR0R
  obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
    (⟨R0, hR0, hR02, rfl⟩ : IsTwoLocal (Subgroup.normalizer (R0 : Set G)))
  have hM'M := S.uniqueM.2 M' ⟨hM', (le_sup_left.trans hN).trans hM'le⟩
  exact hH.2.1 ((le_sup_right.trans hN).trans (hM'M ▸ hM'le))

theorem normalizer_V3_le_F4 (h311 : Theorem311Stmt) (h1222 : Stmt12_2_2_F4) :
    Subgroup.normalizer (S.V3 : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  intro g hg
  obtain ⟨c, hc, hcg⟩ := exists_mem_normalizer_of_isSylowTwoOf (S.R_sylow_CV3_F4 h1222)
    (normalizer_le_normalizer_centralizer' _ hg)
  have hgM : g ∈ Subgroup.normalizer (L : Set G) := by
    have := (Subgroup.normalizer (L : Set G)).mul_mem (S.centralizer_V3_le_F4 h311 h1222 hc)
      (S.normalizer_R_le hcg)
    simpa using this
  exact S.mem_normalizer_V_of_F4 h1222 hgM S.V3_ne_bot S.V3_le_V hg

end Setting

theorem input1323Two_of_F4 (h311 : Theorem311Stmt) (h1222 : Stmt12_2_2_F4) : Input1323Two_F4 :=
  fun _ _ _ _ _ _ S => S.normalizer_V3_le_F4 h311 h1222

end CFSG.Quasithin.H13.A5
