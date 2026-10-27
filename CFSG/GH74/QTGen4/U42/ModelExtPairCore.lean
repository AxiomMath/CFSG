module

public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.GH74.QTGen4.U42.ModelP1CharTwo
public import CFSG.GH74.QTGen4.U42.PairExt
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Mod1

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.F431.U42 U42F431
open CFSG.Quasithin.H13.F431.U42Aut


theorem charTwo_P1h : CharTwo P1h := by
  let N : Subgroup Ah := P1.map incl
  have hNle : N ≤ P1h := by
    rintro _ ⟨g, hg, rfl⟩
    change g ∈ P1h.comap incl
    rwa [comap_P1h]
  have hNeq : N = P1h ⊓ Yh := by
    ext g
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨hNle (Subgroup.mem_map_of_mem _ hy), ?_⟩
      exact (mem_Yh_iff_incl _).mpr ⟨y, rfl⟩
    · rintro ⟨hg, hy⟩
      obtain ⟨y, rfl⟩ := (mem_Yh_iff_incl g).mp hy
      refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
      change y ∈ P1h.comap incl at hg
      rw [comap_P1h] at hg
      exact hg
  have hPN : P1h ≤ Subgroup.normalizer (N : Set Ah) := by
    have hsub : N.subgroupOf P1h = Yh.comap P1h.subtype := by
      rw [hNeq]
      ext g
      change ((g : Ah) ∈ P1h ∧ (g : Ah) ∈ Yh) ↔ (g : Ah) ∈ Yh
      exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩
    haveI : Yh.Normal := Yh_normal
    have hn : (N.subgroupOf P1h).Normal := by rw [hsub]; infer_instance
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mp hn
  have hPlain : CharTwo P1 := by
    rintro g ⟨hg, hc⟩
    exact centralizer_pCoreOf_P1_le g hg
      (fun u hu => ((Subgroup.mem_centralizer_iff.mp hc) u hu).symm)
  have hNchar : CharTwo N :=
    F6.charTwo_of_mulEquiv (Subgroup.equivMapOfInjective P1 incl incl_injective) hPlain
  have hThatP : That ≤ P1h := That_le_Bh.trans Bh_le_P1h
  have hjoin : N ⊔ That = P1h := by
    refine le_antisymm (sup_le hNle hThatP) (P1h_le_closure.trans ?_)
    rw [Subgroup.closure_le]
    rintro g (⟨k, rfl⟩ | rfl | rfl | rfl)
    · exact (le_sup_left : N ≤ N ⊔ That) (Subgroup.mem_map_of_mem incl (B0_le_P1 (gTY_mem_B0 k k.2)))
    · exact (le_sup_right : That ≤ N ⊔ That) fhatA_mem_That
    · exact (le_sup_left : N ≤ N ⊔ That) (Subgroup.mem_map_of_mem incl (B0_le_P1 c3_mem_B0))
    · exact (le_sup_left : N ≤ N ⊔ That) (Subgroup.mem_map_of_mem incl D1_mem_P1)
  rw [← hjoin]
  exact A4.charTwo_sup hNchar (hThatP.trans hPN) isSylowTwoOf_That_Bh.2.1

theorem model_pairCore_extension : PairCore P1h Bh That (pCoreOf 2 P1h) := by
  have hThatP : That ≤ P1h := That_le_Bh.trans Bh_le_P1h
  have hSyl : IsSylowTwoOf That P1h := by
    refine ⟨hThatP, isSylowTwoOf_That_Bh.2.1, ?_⟩
    show ¬ 2 ∣ That.relIndex P1h
    have h := Subgroup.relIndex_mul_card (H := That) (K := P1h)
    rw [inf_eq_left.mpr hThatP, card_That, card_P1h] at h
    have hi : That.relIndex P1h = 9 := by omega
    rw [hi]
    norm_num
  refine ⟨F7.isSylowTwoOf_pCoreOf_le hSyl, That_le_Bh, Bh_le_P1h, ?_,
    hSyl.2.1, hSyl.2.2, ?_, ?_⟩
  · intro h hh u hu
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P1h hh) u).mp hu
  · intro h hh hc
    exact charTwo_P1h ⟨hh, Subgroup.mem_centralizer_iff.mpr (fun u hu => (hc u hu).symm)⟩
  · rw [card_P1h, card_That]

end CFSG.GH74.QTGen4.U42
