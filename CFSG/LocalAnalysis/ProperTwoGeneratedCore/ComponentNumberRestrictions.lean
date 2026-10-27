module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalSubgroups

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification
open CFSG.TwoRankLowerBound.Helpers

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem commuting_two_subgroups_join_isPGroup (P Q : Subgroup G)
    (hP : IsPGroup 2 P) (hQ : IsPGroup 2 Q) (hcomm : ⁅P, Q⁆ = ⊥) :
    IsPGroup 2 ↥(P ⊔ Q : Subgroup G) :=
  hP.to_sup_of_normal_left' hQ
    ((Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans
      (Subgroup.centralizer_le_normalizer _))

theorem subgroup_le_core_overgroup_of_commutes
    (S : Sylow 2 G) (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H)
    (D Q : Subgroup G) (hQS : Q ≤ (S : Subgroup G))
    (hrank : 2 ≤ pRank 2 Q) (hcomm : ⁅D, Q⁆ = ⊥) : D ≤ H :=
  (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
    (two_generated_core_subgroup_centralizer_le S H hSH hcore Q
      (hQS.trans hSH) hrank)

theorem proper_full_core_high_rank_component_unique
    (S : Sylow 2 G) (H : Subgroup G) (hH : H ≠ ⊤)
    (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H)
    (L M : Subgroup G) (hL : IsComponentOf L ⊤) (hM : IsComponentOf M ⊤)
    (hLrank : 2 ≤ pRank 2 L) (hMrank : 2 ≤ pRank 2 M) : L = M := by
  classical
  by_contra hne
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let TL : Sylow 2 L := Classical.choice inferInstance
  let TM : Sylow 2 M := Classical.choice inferInstance
  let P := (TL : Subgroup L).map L.subtype
  let Q := (TM : Subgroup M).map M.subtype
  have hPL : P ≤ L := Subgroup.map_subtype_le _
  have hQM : Q ≤ M := Subgroup.map_subtype_le _
  have hcomm : ⁅P, Q⁆ = ⊥ := by
    apply le_bot_iff.mp
    calc
      ⁅P, Q⁆ ≤ ⁅L, M⁆ := Subgroup.commutator_mono hPL hQM
      _ = ⊥ := LocalComponents.commute_of_ne L M hL hM hne
  have htwo := commuting_two_subgroups_join_isPGroup P Q
    (TL.isPGroup'.map L.subtype) (TM.isPGroup'.map M.subtype) hcomm
  obtain ⟨a, ha⟩ := pGroup_conjugate_into_sylow_within_overgroup
    2 Nat.prime_two S ⊤ le_top (P ⊔ Q) htwo le_top
  let e : MulAut G := MulAut.conj (a : G)
  let L' := L.map e.toMonoidHom
  let M' := M.map e.toMonoidHom
  let P' := P.map e.toMonoidHom
  let Q' := Q.map e.toMonoidHom
  have hL' : IsComponentOf L' ⊤ := (LocalComponents.equiv_iff e L).mpr hL
  have hM' : IsComponentOf M' ⊤ := (LocalComponents.equiv_iff e M).mpr hM
  have hne' : L' ≠ M' := fun heq =>
    hne (Subgroup.map_injective e.injective heq)
  have hP'S : P' ≤ (S : Subgroup G) := (Subgroup.map_mono le_sup_left).trans ha
  have hQ'S : Q' ≤ (S : Subgroup G) := (Subgroup.map_mono le_sup_right).trans ha
  have hP'L : P' ≤ L' := Subgroup.map_mono hPL
  have hQ'M : Q' ≤ M' := Subgroup.map_mono hQM
  have hP'rank : 2 ≤ pRank 2 P' := by
    change 2 ≤ pRank 2 (P.map e.toMonoidHom)
    rw [pRank_map_automorphism 2 (by decide)]
    change 2 ≤ pRank 2 ((TL : Subgroup L).map L.subtype)
    rwa [sylow_image_two_rank_eq]
  have hQ'rank : 2 ≤ pRank 2 Q' := by
    change 2 ≤ pRank 2 (Q.map e.toMonoidHom)
    rw [pRank_map_automorphism 2 (by decide)]
    change 2 ≤ pRank 2 ((TM : Subgroup M).map M.subtype)
    rwa [sylow_image_two_rank_eq]
  have hcomponents : ∀ D : Subgroup G, IsComponentOf D ⊤ → D ≤ H := by
    intro D hD
    by_cases hDL : D = L'
    · have hDM : D ≠ M' := by simpa only [hDL] using hne'
      apply subgroup_le_core_overgroup_of_commutes S H hSH hcore D Q' hQ'S hQ'rank
      apply le_bot_iff.mp
      calc
        ⁅D, Q'⁆ ≤ ⁅D, M'⁆ := Subgroup.commutator_mono le_rfl hQ'M
        _ = ⊥ := LocalComponents.commute_of_ne D M' hD hM' hDM
    · apply subgroup_le_core_overgroup_of_commutes S H hSH hcore D P' hP'S hP'rank
      apply le_bot_iff.mp
      calc
        ⁅D, P'⁆ ≤ ⁅D, L'⁆ := Subgroup.commutator_mono le_rfl hP'L
        _ = ⊥ := LocalComponents.commute_of_ne D L' hD hL' hDL
  let E := Layer.subgroup G
  let : E.Normal := Layer.normal G
  have hEH : E ≤ H := sSup_le hcomponents
  have hErank : 2 ≤ pRank 2 E := by
    have hL'rank : 2 ≤ pRank 2 L' := by
      change 2 ≤ pRank 2 (L.map e.toMonoidHom)
      rwa [pRank_map_automorphism 2 (by decide)]
    exact hL'rank.trans (pRank_mono 2 (by decide) (Layer.component_le hL'))
  exact normal_rank_two_not_le_overgroup S H hH hSH hcore E hErank hEH

theorem proper_full_core_high_rank_component_characteristic
    (S : Sylow 2 G) (H : Subgroup G) (hH : H ≠ ⊤)
    (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H)
    (L : Subgroup G) (hL : IsComponentOf L ⊤) (hrank : 2 ≤ pRank 2 L) :
    L.Characteristic := by
  apply Subgroup.characteristic_iff_map_eq.mpr
  intro e
  apply (proper_full_core_high_rank_component_unique S H hH hSH hcore L
    (L.map e.toMonoidHom) hL ((LocalComponents.equiv_iff e L).mpr hL) hrank ?_).symm
  rwa [pRank_map_automorphism 2 (by decide)]

theorem proper_full_core_high_rank_component_restrictions
    (S : Sylow 2 G) (H : Subgroup G) (hH : H ≠ ⊤)
    (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H)
    (L : Subgroup G) (hL : IsComponentOf L ⊤) (hrank : 2 ≤ pRank 2 L) :
    ∃ hchar : L.Characteristic,
      letI := hchar
      letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      let T := CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal S L
      (T : Subgroup L).map L.subtype = (S : Subgroup G) ⊓ L ∧
        properTwoGenCoreGamma (T : Subgroup L) 2 ≤ H.subgroupOf L ∧
          H.subgroupOf L < ⊤ ∧ pRank 2 (Subgroup.centralizer (L : Set G)) ≤ 1 := by
  let hchar := proper_full_core_high_rank_component_characteristic S H hH hSH hcore L hL hrank
  let := hchar
  exact ⟨hchar, proper_full_core_normal_subgroup_restrictions S H hH hSH hcore L hrank⟩

end CFSG.ProperTwoGeneratedCore
