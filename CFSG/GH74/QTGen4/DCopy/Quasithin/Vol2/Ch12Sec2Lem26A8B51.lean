module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem26A8B51
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem26A8Cfg
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem26A8Stmts

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

namespace Lem26A8

namespace Cfg

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {z v g : G}
  (c : Cfg T L V z v g)
include c

theorem inf_centralizer_le_vv_F4
    (h1222 : Stmt12_2_2_F4) (h3228 : Stmt3_2_2_eight) :
    (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤
      Subgroup.centralizer (conjClosure (quasithinOmegaOneCenter
        (T ⊓ Subgroup.centralizer ({v} : Set G))) L : Set G) := by
  obtain ⟨-, hVvC, -, -, -⟩ := c.vv_facts_F4 h1222 h3228
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact (Subgroup.mem_centralizer_iff.mp (hVvC hw) x
    (c.sup_inf_centralizer_le_F4 h1222 h3228 hx)).symm

theorem nonempty_autOn_equiv_F4
    (h1222 : Stmt12_2_2_F4) (h3228 : Stmt3_2_2_eight) :
    Nonempty (↥(autOn L (conjClosure (quasithinOmegaOneCenter
      (T ⊓ Subgroup.centralizer ({v} : Set G))) L)) ≃* ↥(alternatingGroup (Fin 8))) := by
  obtain ⟨-, -, -, hN, hVV⟩ := c.vv_facts_F4 h1222 h3228
  obtain ⟨-, hred, -⟩ := c.facts_F4 h1222
  have : IsSimpleGroup ↥(alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (α := Fin 8)
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  obtain ⟨e⟩ := c.nonempty_quot_equiv_F4 h1222
  refine nonempty_autOn_mulEquiv_of_simple (le_sup_left.trans hN) ?_ ?_ e
  · intro x hx
    refine c.inf_centralizer_le_vv_F4 h1222 h3228 ⟨Subgroup.mem_sup_left
      (CFSG.LieType.BorelTits.pCoreOf_le 2 L hx), ?_⟩
    exact pCoreOf_le_centralizer_of_hyp1223 c.hyp hred hx
  · intro hLC
    exact not_le_centralizer_of_hyp1223 c.hyp (hLC.trans (Subgroup.centralizer_le hVV))

end Cfg

end Lem26A8

open Lem26A8 in

theorem lem12216A8VvComm_of_F4
    (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3)
    (h3228 : Stmt3_2_2_eight) (h51 : AsB51) : Lem12216A8VvComm_F4 := by
  intro G _ _ T L V z v g hH hNE hmod hVL hz1 hNV hvV hvz hgM hgv hsyl hgN
  obtain ⟨hcomm, hreal⟩ := hmod
  have c : Cfg T L V z v g :=
    ⟨hH, hNE, hcomm, hreal, hVL, hz1, hNV, hvV, hvz, hgM, hgv, hsyl, hgN⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hVvQ, -, hVv2, hN, hVV⟩ := c.vv_facts_F4 h1222 h3228
  have hRed := c.isTwoReducedIn_F4 h1222 h3228
  set Vv := conjClosure (quasithinOmegaOneCenter (T ⊓ Subgroup.centralizer ({v} : Set G))) L
    with hVvdef
  obtain ⟨hVT, hred, hV2⟩ := c.facts_F4 h1222
  have hVe : IsElemAbelian 2 Vv := hRed.2.2.1
  have : IsMulCommutative ↥Vv := hVe.1
  have hLVv : L ≤ Subgroup.normalizer (Vv : Set G) := le_sup_left.trans hN
  have hYL : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hH.normalizes
  set K := autOn L Vv with hK
  set X := autOn (L ⊔ T) Vv with hX

  have hJT : ¬ thompsonJ T ≤ Subgroup.centralizer (Vv : Set G) := fun hJ =>
    not_thompsonJ_le_centralizer h323 h3228 hH hNE c.TV hvV c.v1 c.zV hgM hgv
      (hJ.trans (Subgroup.centralizer_le hVV))
  have hJH : ¬ thompsonJ (L ⊔ T) ≤ Subgroup.centralizer (Vv : Set G) := fun hJ =>
    hJT ((thompsonJ_le_thompsonJ_of_isSylowTwoOf
      (isSylowTwoOf_of_quasithinIsSylowTwo hH.sylow le_sup_right)).trans hJ)
  have hFF : IsFFModule X := (B2_7_of_not_le hVe hRed.1 hN hJH).1
  obtain ⟨A, hA⟩ := B6.exists_isFFStarOffender hFF

  have h2 : ∀ y ∈ L ⊔ T, ∃ e : ℕ, y ^ 2 ^ e ∈ L ⊔ Subgroup.centralizer (Vv : Set G) := by
    intro y hy
    obtain ⟨e, he⟩ := exists_two_pow_mem_of_sup c.T2 hH.normalizes y hy
    exact ⟨e, Subgroup.mem_sup_left he⟩
  have hO2 : pCoreOf 2 X = ⊥ := Setup.pCoreOf_autOn_eq_bot hRed
  obtain ⟨eK⟩ := c.nonempty_autOn_equiv_F4 h1222 h3228
  have hs : IsSimpleGroup ↥K := by
    have : IsSimpleGroup ↥(alternatingGroup (Fin 8)) :=
      alternatingGroup.isSimpleGroup (α := Fin 8)
        (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    exact eK.isSimpleGroup
  have hna : ∃ a b : ↥K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := alt_eight_nonabelian
    refine ⟨eK.symm a, eK.symm b, fun h => hab ?_⟩
    have := congrArg eK h
    simpa using this
  have hCL : L ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 L := c.inf_centralizer_le_F4 h1222
  have hnc : ¬ L ≤ Subgroup.centralizer (Vv : Set G) := fun hLC =>
    not_le_centralizer_of_hyp1223 hH (hLC.trans (Subgroup.centralizer_le hVV))
  have hO2L : pCoreOf 2 L ≤ Subgroup.centralizer (Vv : Set G) := fun x hx =>
    c.inf_centralizer_le_vv_F4 h1222 h3228 ⟨Subgroup.mem_sup_left
      (CFSG.LieType.BorelTits.pCoreOf_le 2 L hx), pCoreOf_le_centralizer_of_hyp1223 hH hred hx⟩
  have hq : CFSG.IsQuasisimple ↥K :=
    isQuasisimple_autOn_of_pCoreOf_le hLVv hH.quasisimple hO2L hnc
  have hSL : SQTKGroup ↥L := by
    have hV2g : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using hV2 x x.2)⟩
    have hP : pCoreOf 2 (L ⊔ T) ≠ ⊥ := by
      intro hb
      apply hH.irrPlus.2.1
      rw [eq_bot_iff, ← hb]
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hVT.trans le_sup_right)
        (sup_le c.LV c.TV) hV2g
    exact InternalSec.sqtkGroup_mono (sqtkGroup_of_pCoreOf_ne_bot hH.qtke hH.simple
      hH.nonabelian hP) le_sup_left
  have hS : SQTKGroup ↥K := by
    refine InternalSec.sqtkGroup_autOn hLVv hSL
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le ?_)
    exact fun x hx => hCL ⟨hx.1, Subgroup.centralizer_le hVV hx.2⟩
  have hLA : ⁅K, A⁆ = K :=
    commutator_autOn_eq_of_simple hN le_sup_left hYL h2 hO2 hs hna hA.1 hA.2.1
  obtain ⟨hB51, -⟩ := InternalSec.b51Hyp_ffJ_autOn hN le_sup_left hYL h2 hO2 hq hS hA hLA
  have hV2' : ∀ w : ↥Vv, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hVv2 w w.2)
  have hP2 : B51Part2 K := (h51 ↥Vv hV2' (ffJ X) K hB51).2.1

  have hmap := map_commV_autOn hLVv
  have hV'U : V.subgroupOf Vv ≤ commV K := by
    intro x hx
    have hx' : (x : G) ∈ ⁅V, L⁆ := by
      rw [hH.irrPlus.2.2.2.1]
      exact hx
    have h1 : (x : G) ∈ ⁅Vv, L⁆ := Subgroup.commutator_mono hVV le_rfl hx'
    rw [← hmap] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    rwa [← Subtype.ext hyx]
  have hfixK := fixV_autOn_eq hLVv
  have hne : fixV K ⊓ commV K ≠ ⊥ := by
    intro hbot
    have hz : (⟨z, hVV c.zV⟩ : ↥Vv) ∈ fixV K ⊓ commV K := by
      refine ⟨?_, hV'U c.zV⟩
      rw [hfixK]
      exact c.zVL.2
    rw [hbot, Subgroup.mem_bot] at hz
    exact hz1 (congrArg Subtype.val hz)
  have hirr := (hP2.2 (hP2.1.mpr (Or.inl hne))).1

  have hinv : ∀ k ∈ K, ∀ w ∈ V.subgroupOf Vv, k w ∈ V.subgroupOf Vv :=
    invariant_subgroupOf_of_le_normalizer hLVv c.LV
  have hfix : ¬ V.subgroupOf Vv ≤ fixV K := by
    intro hle
    apply hvz
    have h1 := hle (show (⟨v, hVV hvV⟩ : ↥Vv) ∈ V.subgroupOf Vv from hvV)
    rw [hfixK] at h1
    have h2 : v ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨hvV, h1⟩
    rwa [hVL] at h2
  have hUV := commV_eq_of_irrPlus hirr hV'U hinv hfix
  rw [← hmap, hUV, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVV]

end CFSG.Quasithin.H13
