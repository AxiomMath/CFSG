module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.ExcClubList
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K144

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem pPrimeCore_map_le {p : ℕ} {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    (CFSG.pPrimeCore p A).map (e : A →* B) ≤ CFSG.pPrimeCore p B := by
  rw [Subgroup.map_le_iff_le_comap]
  unfold CFSG.pPrimeCore
  apply sSup_le
  intro N hN
  rw [← Subgroup.map_le_iff_le_comap]
  apply le_sSup
  refine ⟨?_, ?_⟩
  · exact hN.1.map (e : A →* B) e.surjective
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hN.2

theorem pPrimeCore_map_eq {p : ℕ} {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    (CFSG.pPrimeCore p A).map (e : A →* B) = CFSG.pPrimeCore p B := by
  apply le_antisymm (pPrimeCore_map_le e)
  have h2 := pPrimeCore_map_le (p := p) e.symm
  rw [Subgroup.map_le_iff_le_comap] at h2
  intro x hx
  exact Subgroup.mem_map.2 ⟨e.symm x, h2 hx, e.apply_symm_apply x⟩

theorem pQuot_subgroupOf_equiv {G : Type} [Group G] {p : ℕ} {J K : Subgroup G} (hJK : J ≤ K) :
    Nonempty (PQuot p (J.subgroupOf K) ≃* PQuot p J) := by
  let eJ : ↥(J.subgroupOf K) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJK
  have hmap : (GLAPPrimeCore p ↥(J.subgroupOf K)).map (eJ : ↥(J.subgroupOf K) →* ↥J) =
      GLAPPrimeCore p ↥J := pPrimeCore_map_eq (p := p) eJ
  exact ⟨QuotientGroup.congr _ _ eJ hmap⟩

theorem pSimple_subgroupOf_equiv {G : Type} [Group G] {p : ℕ} {J K : Subgroup G} (hJK : J ≤ K) :
    Nonempty (PSimple p (J.subgroupOf K) ≃* PSimple p J) := by
  obtain ⟨e⟩ := pQuot_subgroupOf_equiv (p := p) hJK
  exact ⟨QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)⟩

theorem isChevSimple_two_of_equiv' {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : IsChevSimple 2 B) : IsChevSimple 2 A := by
  unfold IsChevSimple at h ⊢
  rcases h with h | h
  · exact Or.inl ((CFSG.LocalAnalysis.GLTheoremA.catalogIs_congr e).2 h)
  · exact Or.inr ((CFSG.LocalAnalysis.GLTheoremA.catalogIs_congr e).2 h)

end CFSG.LocalAnalysis.GLTheoremA.K144
