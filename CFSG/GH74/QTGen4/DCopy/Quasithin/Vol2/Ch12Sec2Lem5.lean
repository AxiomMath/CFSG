module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem5
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem6

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

open Lem5

theorem stmt12_2_5_of_F4 (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3) : Stmt12_2_5_F4 := by
  intro G _ _ T L V hH v hv hv1
  have h1226 := stmt12_2_6_of_F4 h1222 h323
  obtain ⟨-, -, hall⟩ := ((h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, -, -, -⟩, -, -, -, -⟩ := hall V hH.irrPlus
  obtain ⟨⟨hM2, -⟩, ⟨-, huniq⟩, -⟩ :=
    h323 G T L hH.simple hH.nonabelian hH.qtke hH.sylow hH.maximal hH.faithful hH.quasisimple
  rw [hH.conjClosure_eq] at hM2 huniq
  have hLM : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  have hTM : T ≤ Subgroup.normalizer (L : Set G) := hH.normalizes
  have hvT : v ∈ T := hVT hv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    exact (oTwoUpper_le _).trans (inf_le_inf_right _ hLM)
  ·
    refine le_trans ?_ (normalizer_le_normalizer_oTwoUpper _)
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hx.1, Subgroup.le_normalizer hx.2⟩
  ·
    obtain ⟨S, hS⟩ := CFSG.Quasithin.exists_sylow_of_quasithinIsSylowTwo hH.sylow
    have hM : CharTwo (Subgroup.normalizer (L : Set G)) :=
      hH.qtke.2.1 _ hM2.1 ⟨S, hS ▸ hTM⟩
    have hz2 : IsPGroup 2 ↥(Subgroup.zpowers v) :=
      hH.sylow.1.to_le ((Subgroup.zpowers_le).mpr hvT)
    have h := hM.inf_centralizer ((Subgroup.zpowers_le).mpr (hTM hvT)) hz2
    rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h
  ·
    unfold cgsIn
    refine iSup₂_le fun C hCQ => iSup₂_le fun hC1 hchar => ?_
    have hC2 : IsPGroup 2 ↥C :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)).to_le hCQ
    obtain ⟨M', hM', hCM'⟩ :=
      CFSG.Quasithin.exists_maxTwoLocal_ge (L := Subgroup.normalizer (C : Set G)) ⟨C, hC1, hC2, rfl⟩
    have hLTC : L ⊔ T ≤ Subgroup.normalizer (C : Set G) :=
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)).trans
        (normalizer_le_normalizer_of_characteristic hCQ hchar)
    have hM'eq := huniq M' hM' (hLTC.trans hCM')
    intro x hx
    have hxM : x ∈ Subgroup.normalizer (L : Set G) := by
      rw [← hM'eq]
      exact hCM' hx.2
    exact ⟨hxM, hx.1⟩
  ·
    have hz1 : Subgroup.zpowers v ≠ ⊥ := by
      intro h
      apply hv1
      have : v ∈ Subgroup.zpowers v := Subgroup.mem_zpowers v
      rw [h, Subgroup.mem_bot] at this
      exact this
    have h := (h1226 G T L V hH).2 (Subgroup.zpowers v)
      (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({v} : Set G)) hz1
      ((Subgroup.zpowers_le).mpr hv) (inf_le_right.trans (centralizer_le_normalizer_zpowers v))
    intro x hx
    have hx' : x ∈ (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({v} : Set G)) ⊓
        Subgroup.normalizer (L : Set G) := ⟨hx, hx.1⟩
    rw [h] at hx'
    exact ⟨hx.1, hx'.2⟩

end CFSG.Quasithin.H13
