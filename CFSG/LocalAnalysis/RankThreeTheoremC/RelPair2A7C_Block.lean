module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Defs
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_BlockPerm
import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7_Lift

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup Equiv
  CFSG.RankThree.PartTwo.KFacts.KP2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem a7b_normalizer_le {C V : Subgroup G} (hCV : C ≤ V)
    (hC : (C.subgroupOf V).Characteristic) :
    normalizer (V : Set G) ≤ normalizer (C : Set G) := by
  have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (C.subgroupOf V)
  rwa [Subgroup.map_subgroupOf_eq_of_le hCV] at h

section Frame

variable {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)}

omit [Finite G] in
theorem a7b_V_le (hF : A7Frame D H V ι) : V ≤ a7I H ι := by
  intro v hv
  have hmem : ι ⟨v, hF.V_le hv⟩ ∈ (V.subgroupOf H).map ι := ⟨⟨v, hF.V_le hv⟩, hv, rfl⟩
  rw [hF.V_img] at hmem
  exact mem_a7I_iff.2 ⟨⟨v, hF.V_le hv⟩, a7Four_le_a7Five (a7b_vOne_le_a7Four hmem), rfl⟩

omit [Finite G] in
theorem a7b_K_le (hF : A7Frame D H V ι) : a7K H ≤ a7I H ι := by
  rintro _ ⟨k, hk, rfl⟩
  have hk' : k ∈ ι.ker := hF.ker_eq ▸ hk
  exact mem_a7I_iff.2 ⟨k, (MonoidHom.mem_ker.1 hk').symm ▸ one_mem _, rfl⟩

omit [Finite G] in
theorem a7b_inf_normalizer_le (hF : A7Frame D H V ι) {C : Subgroup G} (hCV : C ≤ V)
    (hC0 : C ≠ ⊥) (hNC : normalizer (V : Set G) ≤ normalizer (C : Set G)) :
    a7I H ι ⊓ normalizer (C : Set G) ≤ (a7Four.comap ι).map H.subtype := by
  set X := a7I H ι ⊓ normalizer (C : Set G)
  have hXH : X ≤ H := inf_le_left.trans (a7I_le H ι)
  have hX5 : (X.subgroupOf H).map ι ≤ a7Five := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := mem_a7I_iff.1 (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)).1
    rwa [← Subtype.ext hyx]
  have hV : vOne ≤ (X.subgroupOf H).map ι := by
    rw [← hF.V_img]
    refine Subgroup.map_mono fun v hv => ?_
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    exact Subgroup.mem_inf.2 ⟨a7b_V_le hF hv, hNC (Subgroup.le_normalizer hv)⟩
  have hc : cTwo ∈ (X.subgroupOf H).map ι := by
    have hcD : cTwo ∈ (D.subgroupOf H).map ι := hF.D_img ▸ cTwo_mem_eNine
    obtain ⟨d, hd, hdc⟩ := Subgroup.mem_map.1 hcD
    rw [Subgroup.mem_subgroupOf] at hd
    refine ⟨d, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨mem_a7I_iff.2 ⟨d, ?_, rfl⟩,
      hNC (hF.D_norm hd)⟩), hdc⟩
    rw [hdc]
    exact a7Four_le_a7Five a7b_cTwo_mem_a7Four
  have h4 : a7Four ≤ (X.subgroupOf H).map ι :=
    a7b_a7Four_le_sup.trans (sup_le hV (Subgroup.zpowers_le.2 hc))
  rcases a7b_eq_or_eq_of_le h4 hX5 with h | h
  · intro x hx
    refine Subgroup.mem_map.2 ⟨⟨x, hXH hx⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, ← h]
    exact ⟨⟨x, hXH hx⟩, hx, rfl⟩
  · exfalso
    refine hF.noCover C hCV hC0 hNC (a7b_alternatingGroup_le_sup.trans (sup_le ?_ ?_))
    · rw [← h]
      refine Subgroup.map_mono fun x hx => ?_
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact Subgroup.mem_inf.2 ⟨a7I_le H ι (Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩
    · rw [← hF.D_img]
      refine Subgroup.map_mono fun d hd => ?_
      rw [Subgroup.mem_subgroupOf] at hd ⊢
      exact Subgroup.mem_inf.2 ⟨hF.D_le hd, hNC (hF.D_norm hd)⟩

omit [Finite G] in
theorem a7b_card_I (hF : A7Frame D H V ι) : Nat.card (a7I H ι) = 60 * Nat.card (a7K H) := by
  have h1 : Nat.card (a7I H ι) = Nat.card (a7Five.comap ι) :=
    Subgroup.card_map_of_injective H.subtype_injective
  have h2 := card_eq_card_map_mul_card_inf_ker ι (a7Five.comap ι)
  rw [Subgroup.map_comap_eq, inf_eq_right.2 (a7Five_le_alternatingGroup.trans hF.A7_le),
    inf_eq_right.2 (MonoidHom.ker_le_comap ι a7Five), a7b_card_a7Five, hF.ker_eq] at h2
  have h3 : Nat.card (a7K H) = Nat.card (primeComplementCore (G := H) 3) :=
    Subgroup.card_map_of_injective H.subtype_injective
  rw [h1, h2, h3]

theorem a7b_isSylowTwoOf (hF : A7Frame D H V ι) :
    CFSG.QuasithinUnique.IsSylowTwoOf V (a7I H ι) := by
  have hVI := a7b_V_le hF
  refine ⟨hVI, hF.V_two, ?_⟩
  obtain ⟨hSK, -, hodd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hF.sylow
  have hK : (pCoreOf 2 H).relIndex (a7K H) * Nat.card (pCoreOf 2 H) = Nat.card (a7K H) := by
    have := Subgroup.relIndex_mul_card (pCoreOf 2 H) (a7K H)
    rwa [inf_eq_left.2 hSK] at this
  have hidx := Subgroup.card_mul_index (V.subgroupOf (a7I H ι))
  have hVc : Nat.card (V.subgroupOf (a7I H ι)) = Nat.card V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVI).toEquiv
  rw [hVc, hF.card_V, a7b_card_I hF, ← hK] at hidx
  have hs : 0 < Nat.card (pCoreOf 2 H) := Nat.card_pos
  have h15 : (V.subgroupOf (a7I H ι)).index = 15 * (pCoreOf 2 H).relIndex (a7K H) := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 4 * Nat.card (pCoreOf 2 H) by omega)
    rw [hidx]
    ring
  omega

theorem a7b_charTwo (hF : A7Frame D H V ι) : CFSG.QuasithinUnique.CharTwo (a7I H ι) :=
  CFSG.QuasithinUnique.charTwo_of_pCore_centralizer_le (M := H) hF.charTwo (a7I_le H ι)
    (inf_le_left.trans (hF.sylow.le.trans (a7b_K_le hF)))

end Frame

omit [Finite G] in
theorem A7Frame.cgsIn_ne {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)}
    (hF : A7Frame D H V ι) :
    CFSG.Quasithin.cgsIn (a7I H ι) V ≠ a7I H ι := by
  intro heq
  have hle : CFSG.Quasithin.cgsIn (a7I H ι) V ≤ (a7Four.comap ι).map H.subtype :=
    iSup_le fun C => iSup_le fun hCV => iSup_le fun hC0 => iSup_le fun hC =>
      a7b_inf_normalizer_le hF hCV hC0 (a7b_normalizer_le hCV hC)
  obtain ⟨hσ5, hσ4⟩ := a7b_mem_a7Five_not_mem_a7Four
  obtain ⟨h, hh⟩ := MonoidHom.mem_range.1 (hF.A7_le (a7Five_le_alternatingGroup hσ5))
  have hI : (h : G) ∈ a7I H ι := mem_a7I_iff.2 ⟨h, hh ▸ hσ5, rfl⟩
  rw [← heq] at hI
  obtain ⟨h', hh', hh'eq⟩ := hle hI
  obtain rfl : h' = h := Subtype.ext hh'eq
  exact hσ4 (hh ▸ hh')

theorem A7Frame.exists_block {D H V : Subgroup G}
    {ι : ↥H →* Perm (Fin 7)} (hF : A7Frame D H V ι) :
    ∃ Y : Subgroup G, Y ≤ a7I H ι ∧ IsSubnormal Y (a7I H ι) ∧
      CFSG.AGLEmbedding.InClassXBlock Y ∧ ¬ Y ≤ CFSG.Quasithin.cgsIn (a7I H ι) V :=
  aschbacherLocalCGTBlock_proved G (a7I H ι) V (hF.kGroup _ (a7I_le H ι)) (a7b_charTwo hF)
    (a7b_isSylowTwoOf hF) hF.cgsIn_ne

end CFSG.LocalAnalysis.RankThreeTheoremC
