module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFCoverSylow

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G H : Type} [Group G] [Group H] {L : Subgroup G}

theorem fg_pull_sylow_E16 {φ : ↥L →* H} (hinj : Function.Injective φ)
    (hsurj : Function.Surjective φ) {P' B' : Subgroup H}
    (hP' : IsSylow2Of P' (⊤ : Subgroup H)) (hB' : IsNormalE16In P' B')
    {B : Subgroup G} (hBL : B ≤ L) (hB : ffImg φ B = B') :
    ∃ P : Subgroup G, IsSylow2Of P L ∧ IsNormalE16In P B := by
  have hker : φ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff φ).mpr hinj
  have hφ : OddCentralCover φ :=
    { surjective := hsurj
      ker_le_center := by rw [hker]; exact bot_le
      odd_card_ker := by rw [hker, Subgroup.card_bot]; exact ⟨0, by norm_num⟩ }
  let P : Subgroup G := (P'.comap φ).map L.subtype
  have hPdef : P = (P'.comap φ).map L.subtype := rfl
  have hPsub : P.subgroupOf L = P'.comap φ := by
    rw [hPdef, ← Subgroup.comap_subtype]
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have hPL : P ≤ L := by
    rw [hPdef]
    exact Subgroup.map_subtype_le _
  have hP2 : IsPGroup 2 P := by
    rw [hPdef]
    exact (hP'.2.1.comap_of_injective φ hinj).map L.subtype
  have hPsyl : IsSylow2Of P L := by
    refine ⟨hPL, hP2, ?_⟩
    have hrel : P.relIndex L = P'.index := by
      show (P.subgroupOf L).index = P'.index
      rw [hPsub, Subgroup.index_comap_of_surjective (H := P') hsurj]
    rw [hrel]
    simpa [Subgroup.relIndex_top_right] using hP'.2.2
  have hffP : ffImg φ P = P' := by
    unfold ffImg
    rw [hPsub, Subgroup.map_comap_eq_self_of_surjective hsurj P']
  have hBP : B ≤ P := by
    intro b hb
    have hbL : b ∈ L := hBL hb
    have hmem : φ ⟨b, hbL⟩ ∈ ffImg φ B := by
      rw [mem_ffImg_iff]
      exact ⟨⟨b, hbL⟩, hb, rfl⟩
    rw [hB] at hmem
    rw [hPdef, Subgroup.mem_map]
    exact ⟨⟨b, hbL⟩, by rw [Subgroup.mem_comap]; exact hB'.1 hmem, rfl⟩
  refine ⟨P, hPsyl, ?_⟩
  exact (ff_cover_normalE16_iff hφ hPL hP2 hBP).mpr (by rw [hffP, hB]; exact hB')

end CFSG.OddStandard.SmallF3.Omega
