module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem6
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem stmt12_2_6_of_F4 (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3) : Stmt12_2_6_F4 := by
  intro G _ _ T L V hH
  obtain ⟨-, -, hall⟩ := ((h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, hTV, -, -⟩, hTI, -, -⟩ := hall V hH.irrPlus
  refine ⟨hTI, fun U H hU hUV hHU => le_antisymm ?_ ?_⟩
  · rintro h ⟨hhH, hhM⟩
    refine ⟨hhH, ?_⟩
    rcases hTI h hhM with heq | hinf
    · exact mem_normalizer_of_conjugate_eq heq
    · exact absurd (eq_bot_iff.mpr (hinf ▸ le_inf_conjugate hUV (hHU hhH))) hU
  ·
    have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.irrPlus.2.2.1
    have h2 : IsPGroup 2 ↥V := (CFSG.Quasithin.exists_sylow_of_quasithinIsSylowTwo hH.sylow).elim
      fun S hS => (hS ▸ S.isPGroup').to_le hVT
    obtain ⟨M', hM', hVM'⟩ :=
      CFSG.Quasithin.exists_maxTwoLocal_ge (L := Subgroup.normalizer (V : Set G))
        ⟨V, hH.irrPlus.2.1, h2, rfl⟩
    obtain ⟨-, ⟨-, huniq⟩, -⟩ :=
      h323 G T L hH.simple hH.nonabelian hH.qtke hH.sylow hH.maximal hH.faithful hH.quasisimple
    rw [hH.conjClosure_eq] at huniq
    have hM'eq := huniq M' hM' ((sup_le hLV hTV).trans hVM')
    rintro h ⟨hhH, hhV⟩
    refine ⟨hhH, ?_⟩
    rw [← hM'eq]
    exact hVM' hhV

end CFSG.Quasithin.H13
