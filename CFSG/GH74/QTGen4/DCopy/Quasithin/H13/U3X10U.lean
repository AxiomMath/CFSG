module

public import CFSG.Quasithin.H13.U3X10U
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3C137
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3P33

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Quasithin.SteinbergCB
open scoped Pointwise

variable {G : Type} [Group G]

namespace HullSetting_F4
open CFSG.Quasithin.H13.U3.HullSetting_F4
open CFSG.Quasithin.H13.U3.HullSetting

variable [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} [IsElementaryAbelian 2 V] {z : G}

theorem isSylowTwoOf_inf_F4
    (S : HullSetting_F4 G T L V z) : IsSylowTwoOf (T ⊓ L) L := by
  have hloc := S.hH.faithful.1
  have hTsyl : IsSylowTwoOf T (L ⊔ T) := ⟨le_sup_right, hloc.1, hloc.2.2.1⟩
  exact A4.isSylowTwoOf_inf_normal hTsyl le_sup_left (sup_le le_normalizer S.hTL_F4)

theorem inf_normalizer_V₁_le_F4
    (S : HullSetting_F4 G T L V z) : L ⊓ normalizer (S.V₁_F4 : Set G) ≤ L₁Of L S.V₁_F4 ⊔ T := by
  have hTN : T ⊓ L ≤ L ⊓ normalizer (S.V₁_F4 : Set G) := fun t ht => ⟨ht.2, S.T_le_N_V₁_F4 ht.1⟩
  have hsyl : IsSylowTwoOf (T ⊓ L) (L ⊓ normalizer (S.V₁_F4 : Set G)) :=
    C1GN.isSylowTwoOf_of_le S.isSylowTwoOf_inf_F4 hTN inf_le_left
  have h := C1Pack12.oTwoUpper_sup_eq_of_sylow hsyl
  rw [← h, ← oTwoRes_eq_oTwoUpper]
  exact sup_le_sup le_rfl inf_le_left

theorem L₁T_lt_F4
    (S : HullSetting_F4 G T L V z) : L₁Of L S.V₁_F4 ⊔ T < L ⊔ T := by
  refine lt_of_le_of_ne (sup_le_sup ((oTwoRes_le _).trans inf_le_left) le_rfl) fun h => ?_
  have hLH : L ≤ S.H_F4 := (le_sup_left.trans h.symm.le).trans S.L₁T_le_H_F4
  rw [S.H_eq_F4] at hLH
  have hz : z ∈ V ⊓ centralizer (L : Set G) :=
    ⟨S.hzV_F4, mem_centralizer_iff.2 fun l hl => mem_centralizer_singleton_iff.1 (hLH hl)⟩
  rw [inf_centralizer_L_eq_bot S.hF, mem_bot] at hz
  exact S.hz1_F4 hz

theorem L₁T_max_F4
    (S : HullSetting_F4 G T L V z) (H : Subgroup G) (hPH : L₁Of L S.V₁_F4 ⊔ T ≤ H)
    (hHX : H ≤ L ⊔ T) : H = L₁Of L S.V₁_F4 ⊔ T ∨ H = L ⊔ T := by
  set K : Subgroup U33G := (((H ⊓ L).subgroupOf (normalizer (V : Set G))).map S.rho_F4).comap rho6
    with hK
  have hTH : T ≤ H := le_sup_right.trans hPH
  have hmemK : ∀ {h : G} (hhH : h ∈ H) (hhL : h ∈ L) {g : U33G},
      rho6 g = S.rho_F4 ⟨h, S.hLV_F4 hhL⟩ → g ∈ K := fun hhH hhL g hg =>
    mem_comap.2 (hg ▸ mem_map_of_mem _ (mem_subgroupOf.2 ⟨hhH, hhL⟩))
  obtain ⟨ha, hb, hs, hx, -⟩ := rho6_abs

  have hgen : ∀ (i : Fin 5) (g : U33G), i ∈ ([0, 1, 2] : List (Fin 5)) → rho6 g = u6GL i →
      g ∈ K := by
    intro i g hi hg
    obtain ⟨t, htTL, ht, hrho⟩ := S.exists_T_rho_F4 (u6GL_mem_rhoT hi)
    exact hmemK (hTH htTL.1) htTL.2 (by rw [hg, ← hrho])

  have hxK : u33Data.x ∈ K := by
    have hl₁N : S.l₁ ∈ L ⊓ normalizer (S.V₁_F4 : Set G) := by
      rw [S.normalizer_V₁_F4]
      exact ⟨S.l₁_mem_F4, S.l₁_H_F4⟩
    refine hmemK (hPH (S.inf_normalizer_V₁_le_F4 hl₁N)) S.l₁_mem_F4 ?_
    rw [hx, ← xGL_eq_u6GL]
    exact (S.rho_eq_of_spec_F4 S.l₁_N_F4 S.l₁_spec_F4).symm
  have hAK : u33Data.A ≤ K := by
    refine (closure_le _).2 ?_
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact hgen 0 _ (by simp) ha
    · exact hgen 1 _ (by simp) hb
    · exact hgen 2 _ (by simp) hs
    · exact hxK
  rcases u33Data.lattice K (u33Data.T_le_A.trans hAK) with h | h | h | h
  · exact absurd (le_antisymm u33Data.T_le_A (h ▸ hAK)) u33Data.T_ne_A
  ·
    left
    refine le_antisymm (fun g hg => ?_) hPH
    obtain ⟨l, hl, t, ht, rfl⟩ : ∃ l ∈ L, ∃ t ∈ T, g = l * t := by
      have hmul : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * (T : Set G) :=
        coe_mul_of_right_le_normalizer_left L T S.hTL_F4
      have hx' : g ∈ (L : Set G) * (T : Set G) := by
        rw [← hmul]
        exact hHX hg
      obtain ⟨l, hl, t', ht', rfl⟩ := Set.mem_mul.mp hx'
      exact ⟨l, hl, t', ht', rfl⟩
    have hlH : l ∈ H := by
      have := mul_mem hg (inv_mem (hTH ht))
      rwa [mul_inv_cancel_right] at this
    obtain ⟨g', hg'J⟩ : S.rho_F4 ⟨l, S.hLV_F4 hl⟩ ∈ J6 := S.rho_L_mem_F4 hl
    have hg'K : g' ∈ K := hmemK hlH hl hg'J
    rw [h] at hg'K
    have hfix : glLin (S.rho_F4 ⟨l, S.hLV_F4 hl⟩) (vecOf 15) = vecOf 15 := by
      have := u33A_le_fix15 hg'K
      rw [mem_comap, hg'J] at this
      exact this
    have hlN : l ∈ normalizer (S.V₁_F4 : Set G) := by
      rw [S.normalizer_V₁_F4]
      exact (S.mem_H_iff_F4 (S.hLV_F4 hl) (S.rho_spec_F4 ⟨l, S.hLV_F4 hl⟩)).2 hfix
    exact mul_mem (S.inf_normalizer_V₁_le_F4 ⟨hl, hlN⟩) (mem_sup_right ht)
  ·
    exfalso
    have hAB : u33Data.A ≤ u33Data.A ⊓ u33Data.B := le_inf le_rfl (h ▸ hAK)
    rw [u33Data.inf_AB] at hAB
    exact u33Data.T_ne_A (le_antisymm u33Data.T_le_A hAB)
  ·
    right
    refine le_antisymm hHX (sup_le (fun l hl => ?_) hTH)
    obtain ⟨g', hg'J⟩ : S.rho_F4 ⟨l, S.hLV_F4 hl⟩ ∈ J6 := S.rho_L_mem_F4 hl
    have hg'K : g' ∈ K := h ▸ mem_top g'
    obtain ⟨⟨h', hh'N⟩, hh', hh'ρ⟩ := mem_map.1 (mem_comap.1 hg'K)
    have hh'HL : h' ∈ H ⊓ L := mem_subgroupOf.1 hh'
    have h1 : S.rho_F4 ((⟨h', hh'N⟩ : normalizer (V : Set G))⁻¹ * ⟨l, S.hLV_F4 hl⟩) = 1 := by
      rw [map_mul, map_inv, hh'ρ, hg'J, inv_mul_cancel]
    have h2 : (((⟨h', hh'N⟩ : normalizer (V : Set G))⁻¹ * ⟨l, S.hLV_F4 hl⟩ :
        normalizer (V : Set G)) : G) ∈ centralizer (V : Set G) :=
      (mem_centralizer_V_iff _ (S.rho_spec_F4 _)).2 h1
    have h3 : h'⁻¹ * l ∈ L ⊓ centralizer (V : Set G) :=
      mem_inf.2 ⟨mul_mem (inv_mem hh'HL.2) hl, h2⟩
    have h4 : h'⁻¹ * l ∈ H := hTH (S.pCoreOf_L_le_F4 (S.inf_centralizer_le_F4 h3)).1
    have := mul_mem hh'HL.1 h4
    rwa [mul_inv_cancel_left] at this

theorem not_line_F4
    (S : HullSetting_F4 G T L V z) {l : Subgroup G} (hlV : l ≤ V) (hl4 : Nat.card ↥l = 4)
    (hN : L₁Of L S.V₁_F4 ⊔ T ≤ normalizer (l : Set G)) : False := by
  classical
  have hl1 : l ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hl4
    omega
  obtain ⟨w, hwl, hw1, hwT⟩ := exists_ne_one_mem_center_of_normal S.hH.sylow.1
    (hlV.trans S.hVT_F4) hl1 (le_sup_right.trans hN)
  have hwz : w ∈ zpowers z := by
    rw [← S.hVz_F4]
    exact ⟨hlV hwl, hwT⟩
  have hzl : z ∈ l := by
    rw [mem_zpowers_iff_mem_range_orderOf, S.hz2_F4, Finset.mem_image] at hwz
    obtain ⟨k, hk, hkw⟩ := hwz
    rw [Finset.mem_range] at hk
    interval_cases k
    · rw [pow_zero] at hkw
      exact absurd hkw.symm hw1
    · rw [pow_one] at hkw
      exact hkw ▸ hwl
  have hV2 : A6.IsV2 T V l := by
    refine ⟨?_, hlV, le_sup_right.trans hN, hl4⟩
    rw [S.fsuV1_eq_V₁_F4, S.V₁_eq_F4, zpowers_le]
    exact hzl
  have hle : l = S.V₂_F4 := (S.V2_eq_F4 hV2).trans S.V₂_eq_pullSub_F4.symm
  have h3 : conjClosure S.V₂_F4 (L₁Of L S.V₁_F4) ≤ S.V₂_F4 := conjClosure_le fun h hh v hv => by
    rw [← hle] at hv ⊢
    exact (mem_normalizer_iff.1 (hN (mem_sup_left hh)) v).1 hv
  rw [S.gen3_F4] at h3
  have h4 := Subgroup.card_le_of_le h3
  rw [S.card_V₃_F4, S.card_V₂_F4] at h4
  omega

theorem c137_F4
    (S : HullSetting_F4 G T L V z) (hC137 : C137Statement_F4) :
    CharNormal (baum (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T))) (L ⊔ T) ∨ H13.IsG2Block L := by
  have hcharL : CharTwo L := A5.charTwo_of_faithful S.hH.qtke.2.1 S.hH.sylow S.hH.faithful
  have hLT : ∀ x ∈ L ⊔ T, ∃ l ∈ L, ∃ t ∈ T, x = l * t := by
    intro x hx
    have hmul : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * (T : Set G) :=
      coe_mul_of_right_le_normalizer_left L T S.hTL_F4
    have hx' : x ∈ (L : Set G) * (T : Set G) := by
      rw [← hmul]
      exact hx
    obtain ⟨l, hl, t', ht', rfl⟩ := Set.mem_mul.mp hx'
    exact ⟨l, hl, t', ht', rfl⟩
  have hirr := u3_isIrrPlusIn_F4 S.h1332 S.hH S.hU3 S.hF
  have hVL : ⁅V, L⁆ ≠ ⊥ := by
    rw [hirr.2.2.2.1]
    exact hirr.2.1
  have hcU : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 6048 := card_of_lieModel_PSU_three_three S.hU3
  have hL32 : ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 := fun h => by
    obtain ⟨e⟩ := nonempty_equiv_SL32_of_lieModel h
    have := Nat.card_congr e.toEquiv
    rw [hcU, HSType.card_SL_three_two] at this
    omega
  rcases hC137 G (L ⊔ T) T V L (L₁Of L S.V₁_F4 ⊔ T) (L₁Of L S.V₁_F4 ⊔ T)
      (charTwo_sup_of_normalizes S.hH.sylow.1 S.hTL_F4 hcharL)
      (A5.isSylowTwoOf_of_le S.hH.sylow le_sup_right) hLT S.hH.faithful.1.2.1 hcharL
      (Or.inr (Or.inr (Or.inr S.hU3))) (Or.inl S.hU3) le_sup_right le_rfl S.L₁T_lt_F4
      S.L₁T_max_F4 (Or.inl rfl) S.isTwoReducedIn_F4 hVL (fun h => absurd h hL32) with
    h | h | ⟨-, l, -, hlV, hl4, hN⟩ | h
  · exact Or.inl h
  · exact Or.inr (h.2.2.2 S.hU3)
  · rw [inf_centralizer_L_eq_bot S.hF, card_bot, mul_one] at hl4
    exact (S.not_line_F4 hlV hl4 hN).elim
  · exfalso
    rcases h with he | h
    · obtain ⟨e⟩ := he
      have := Nat.card_congr e.toEquiv
      rw [hcU, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at this
      norm_num [Nat.factorial] at this
    · exact not_isHatA6_of_psu S.hU3 h

end HullSetting_F4

theorem stmt13_3_10_U33_F4
    (h1332 : Stmt13_3_2_F4) (hC137 : C137Statement_F4) [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}
    (hH : QTH13 G T L) (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V)
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) :
    CharNormal (baum (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))) (L ⊔ T) ∨ H13.IsG2Block L := by
  obtain ⟨z, hF⟩ := u3_frame_of_irrPlus_F4 h1332 hH hU3 hV
  have : IsElementaryAbelian 2 V := hF.2.2.1
  obtain ⟨Φ, hL, hLs, hN, hT⟩ := u3_six_module_transport_adapted_F4 h1332 hH hU3 hF
  let S : HullSetting_F4 G T L V z := ⟨h1332, hH, hU3, hF, Φ, hL, hLs, hN, hT⟩
  rw [S.fsuV1_eq_V₁_F4]
  exact S.c137_F4 hC137

end CFSG.Quasithin.H13.U3
