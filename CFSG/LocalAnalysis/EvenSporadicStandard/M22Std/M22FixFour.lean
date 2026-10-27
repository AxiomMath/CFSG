module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.FixFourCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.M22FusionData
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.FixFourSylow

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.ABGLocalTools CFSG.EvenSporadicStandard.M22Std.TabCheck
  CFSG.EvenSporadicStandard.M22Std.FusionCheck CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.M23Std (FixFour card_le_four_of_forall_mem)

theorem tab_mem_of_mem_F1 {F1 : Subgroup (Carrier .M22)}
    (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) {x : Carrier .M22} (hx : x ∈ F1) :
    tab x ∈ idTab :: elemTabs 1 := by
  rcases (hmem1 x).1 hx with rfl | hxm
  · rw [tab_one]
    exact List.mem_cons_self
  · refine List.mem_cons_of_mem _ ?_
    rw [← tab_invs16]
    exact List.mem_map_of_mem hxm

theorem mem_F1_of_tab_mem {F1 : Subgroup (Carrier .M22)}
    (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) {x : Carrier .M22}
    (hx : tab x ∈ idTab :: elemTabs 1) : x ∈ F1 := by
  rw [hmem1]
  rcases List.mem_cons.1 hx with h | h
  · exact Or.inl (tab_injective (h.trans tab_one.symm))
  · rw [← tab_invs16] at h
    obtain ⟨y, hy, hyx⟩ := List.mem_map.1 h
    exact Or.inr (tab_injective hyx ▸ hy)

theorem sylowS_le_normalizer {F1 : Subgroup (Carrier .M22)}
    (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    sylowS ≤ normalizer (F1 : Set (Carrier .M22)) := by
  obtain ⟨-, -, hN, -⟩ := fusionCheck_spec
  refine (Subgroup.closure_le _).2 fun g hg => ?_
  have htabgen : tab g ∈ gensTab := by
    rw [← tab_sylowGens]
    exact List.mem_map_of_mem hg
  exact Subgroup.mem_normalizer_iff.2 (normalizes_of_normOK hmem1 ((hN 1).1 _ htabgen))

theorem isSylowOf_sylowS
    {F1 : Subgroup (Carrier .M22)}
    (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    IsSylowOf 2 sylowS (normalizer (F1 : Set (Carrier .M22)) ⊓ ⊤) := by
  have hS := (Certificates.certificate24781).1
  have hle : sylowS ≤ normalizer (F1 : Set (Carrier .M22)) ⊓ ⊤ :=
    le_inf (sylowS_le_normalizer hmem1) le_top
  exact isSylowOf_iff.2 ⟨hle, IsPGroup.of_card (card_sylowS hS), fun hdvd =>
    sylowS_index_odd (hdvd.trans (Subgroup.relIndex_dvd_index_of_le hle))⟩

theorem fixFour_pinned_sylow {F1 : Subgroup (Carrier .M22)}
    (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) {d : Carrier .M22} (hd : d ∈ sylowS)
    (hdF : d ∉ F1) (hd2 : d * d ∈ F1) :
    Nat.card ↥(F1 ⊓ centralizer ({d} : Set (Carrier .M22))) ≤ 4 := by
  have hS := (Certificates.certificate24781).1
  have h1 : tab d ∉ idTab :: elemTabs 1 := fun h => hdF (mem_F1_of_tab_mem hmem1 h)
  have h2 : tmul (tab d) (tab d) ∈ idTab :: elemTabs 1 := by
    rw [← tab_mul]
    exact tab_mem_of_mem_F1 hmem1 hd2
  have hcount := fixFour_table _ (tab_mem_span_of_mem_sylowS hS hd) h1 h2
  refine card_le_four_of_forall_mem ((invs16 1).filter fun f => comm (tab d) (tab f))
    ?_ fun x hx => ?_
  · have hlen : ((invs16 1).filter fun f => comm (tab d) (tab f)).length =
        (((invs16 1).map tab).filter (comm (tab d))).length := by
      rw [List.filter_map, List.length_map]
      rfl
    rw [hlen, tab_invs16]
    exact hcount
  · obtain ⟨hxF, hxC⟩ := Subgroup.mem_inf.1 hx
    rcases (hmem1 x).1 hxF with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_filter.2 ⟨h,
        comm_tab (Subgroup.mem_centralizer_singleton_iff.1 hxC).symm⟩)

theorem fixFour_pinned
    {F1 : Subgroup (Carrier .M22)}
    (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    FixFour (⊤ : Subgroup (Carrier .M22)) F1 := by
  have hsq : ∀ x ∈ F1, x * x = 1 := by
    intro x hx
    rcases (hmem1 x).1 hx with rfl | hxm
    · simp
    · exact ((invs16_spec 1).2.2 x hxm).2
  have hF : IsPGroup 2 F1 := fun x => ⟨1, Subtype.ext (by simpa [pow_two] using hsq x x.2)⟩
  exact CFSG.EvenSporadicStandard.M23Std.FixFour.of_isSylowOf hF (isSylowOf_sylowS hmem1)
    fun d hd hdF hd2 => fixFour_pinned_sylow hmem1 hd hdF hd2

end CFSG.EvenSporadicStandard.M22Std
