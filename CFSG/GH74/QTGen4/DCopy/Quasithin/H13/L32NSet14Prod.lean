module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NSet14Gen
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NSet14Idx
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L14Producers
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem6
public import CFSG.Quasithin.H13.L32NSet14Gen

public section

namespace CFSG.Quasithin.H13.L32NSet14

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace Setting_F4
open CFSG.Quasithin.H13.L32NSet14.Setting_F4

variable [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V] (S : Setting_F4 G T L V V₂)
include S

theorem ti_F4 (h323 : Stmt3_2_3) : ∀ U H : Subgroup G, U ≠ ⊥ → U ≤ V →
    H ≤ normalizer (U : Set G) →
      H ⊓ normalizer (L : Set G) = H ⊓ normalizer (V : Set G) :=
  (stmt12_2_6_of_F4 S.h1222 h323 G T L V (hyp1223_F4 S.h1332 S.hH S.hV)).2

theorem cent_le_F4 (h323 : Stmt3_2_3) :
    centralizer (V : Set G) ≤ normalizer (L : Set G) := by
  have hV : V ≠ ⊥ := fun h => by
    have := S.card_V_F4
    rw [h, card_bot] at this
    omega
  have h := S.ti_F4 h323 V (centralizer (V : Set G)) hV le_rfl (centralizer_le_normalizer _)
  intro g hg
  have hg' : g ∈ centralizer (V : Set G) ⊓ normalizer (V : Set G) :=
    ⟨hg, centralizer_le_normalizer _ hg⟩
  rw [← h] at hg'
  exact hg'.2

theorem set14_F4 (h323 : Stmt3_2_3) : U3.Set14 G T L V V₂ V (L₁Of L (fsuV1 T V)) where
  h13 := S.hH
  irr := S.hV
  zv := S.hZV
  v2 := S.hV2
  card1 := S.card_V1_F4
  le23 := S.hV2.2.1
  le3V := le_rfl
  T_V3 := S.TV_F4
  card3 := S.card_V_F4
  Lp_eq := CFSG.Quasithin.H13.L32NSet14.Setting.Lp_eq
  Lp_L := CFSG.Quasithin.H13.L32NSet14.Setting.L1_le.trans inf_le_left
  Lp_V1 := CFSG.Quasithin.H13.L32NSet14.Setting.L1_le.trans inf_le_right
  T_Lp := S.T_Lp_F4
  gen := S.gen_F4
  irred := S.irred_F4
  comm3 := S.comm3_F4
  index2 := S.index2_eq_F4
  cv3 := fun _ hy _ => hy.2
  clv := S.clv_F4
  bcase := Or.inl (S.cent_le_F4 h323)
  genL := S.genL_F4
  fsu := ((S.h1332 G T L S.hH L S.hH.faithful).2.2.1.2 V S.hV).2.2.1
  T_L := S.TL_F4
  V_T := S.VT_F4
  T_V := S.TV_F4
  Mmax := (S.h1332 G T L S.hH L S.hH.faithful).2.1.2.2.1
  uniq := (S.h1332 G T L S.hH L S.hH.faithful).2.1.2.2.2
  ti := S.ti_F4 h323
  Lp_def := ⟨fun h => absurd h S.not_isHatA6_F4, fun _ => rfl⟩
  Lp3 := S.Lp3_F4

end Setting_F4

theorem set14ProducerL32_of_inputs_F4 (h1332 : Stmt13_3_2_F4) (h1222 : Stmt12_2_2_F4)
    (h323 : Stmt3_2_3) (h1334 : A6.Stmt13_3_4_F4) : U3.Set14ProducerL32_F4 := by
  intro G _ _ T L V V₂ _ hH hV hZV hV2 hlin hnat
  exact ⟨V, L₁Of L (fsuV1 T V),
    (Setting_F4.mk h1222 h1332 h1334 hH hV hZV hV2 hlin hnat).set14_F4 h323⟩

end CFSG.Quasithin.H13.L32NSet14
