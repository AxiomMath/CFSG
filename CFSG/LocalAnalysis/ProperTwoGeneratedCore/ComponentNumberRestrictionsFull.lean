module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ComponentNumberRestrictionsEven
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ComponentNumberRestrictions

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem commutes_with_join_of_commutes (D P Q : Subgroup G)
    (hP : ⁅D, P⁆ = ⊥) (hQ : ⁅D, Q⁆ = ⊥) : ⁅D, P ⊔ Q⁆ = ⊥ := by
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  apply Subgroup.le_centralizer_iff.mpr
  exact sup_le
    (Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hP))
    (Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQ))

theorem proper_full_core_no_three_even_components
    (S : Sylow 2 G) (H : Subgroup G) (hH : H ≠ ⊤)
    (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H)
    (L M N : Subgroup G)
    (hL : IsComponentOf L ⊤) (hM : IsComponentOf M ⊤) (hN : IsComponentOf N ⊤)
    (hLeven : Even (Nat.card L)) (hMeven : Even (Nat.card M)) (hNeven : Even (Nat.card N))
    (hLM : L ≠ M) (hLN : L ≠ N) (hMN : M ≠ N) : False := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let TL : Sylow 2 L := Classical.choice inferInstance
  let TM : Sylow 2 M := Classical.choice inferInstance
  let TN : Sylow 2 N := Classical.choice inferInstance
  let P := (TL : Subgroup L).map L.subtype
  let Q := (TM : Subgroup M).map M.subtype
  let R := (TN : Subgroup N).map N.subtype
  have hPL : P ≤ L := Subgroup.map_subtype_le _
  have hQM : Q ≤ M := Subgroup.map_subtype_le _
  have hRN : R ≤ N := Subgroup.map_subtype_le _
  have hPQ : ⁅P, Q⁆ = ⊥ := by
    apply le_bot_iff.mp
    calc
      ⁅P, Q⁆ ≤ ⁅L, M⁆ := Subgroup.commutator_mono hPL hQM
      _ = ⊥ := LocalComponents.commute_of_ne L M hL hM hLM
  have hPR : ⁅P, R⁆ = ⊥ := by
    apply le_bot_iff.mp
    calc
      ⁅P, R⁆ ≤ ⁅L, N⁆ := Subgroup.commutator_mono hPL hRN
      _ = ⊥ := LocalComponents.commute_of_ne L N hL hN hLN
  have hQR : ⁅Q, R⁆ = ⊥ := by
    apply le_bot_iff.mp
    calc
      ⁅Q, R⁆ ≤ ⁅M, N⁆ := Subgroup.commutator_mono hQM hRN
      _ = ⊥ := LocalComponents.commute_of_ne M N hM hN hMN
  have hPQR : ⁅P ⊔ Q, R⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    apply commutes_with_join_of_commutes R P Q
    · rwa [Subgroup.commutator_comm]
    · rwa [Subgroup.commutator_comm]
  have htwo := commuting_two_subgroups_join_isPGroup (P ⊔ Q) R
    (commuting_two_subgroups_join_isPGroup P Q
      (TL.isPGroup'.map L.subtype) (TM.isPGroup'.map M.subtype) hPQ)
    (TN.isPGroup'.map N.subtype) hPQR
  obtain ⟨a, ha⟩ := pGroup_conjugate_into_sylow_within_overgroup
    2 Nat.prime_two S ⊤ le_top ((P ⊔ Q) ⊔ R) htwo le_top
  let e : MulAut G := MulAut.conj (a : G)
  let L' := L.map e.toMonoidHom
  let M' := M.map e.toMonoidHom
  let N' := N.map e.toMonoidHom
  let P' := P.map e.toMonoidHom
  let Q' := Q.map e.toMonoidHom
  let R' := R.map e.toMonoidHom
  have hL' : IsComponentOf L' ⊤ := (LocalComponents.equiv_iff e L).mpr hL
  have hM' : IsComponentOf M' ⊤ := (LocalComponents.equiv_iff e M).mpr hM
  have hN' : IsComponentOf N' ⊤ := (LocalComponents.equiv_iff e N).mpr hN
  have hLM' : L' ≠ M' := fun heq => hLM (Subgroup.map_injective e.injective heq)
  have hLN' : L' ≠ N' := fun heq => hLN (Subgroup.map_injective e.injective heq)
  have hMN' : M' ≠ N' := fun heq => hMN (Subgroup.map_injective e.injective heq)
  have hP'L : P' ≤ L' := Subgroup.map_mono hPL
  have hQ'M : Q' ≤ M' := Subgroup.map_mono hQM
  have hR'N : R' ≤ N' := Subgroup.map_mono hRN
  have hP'S : P' ≤ (S : Subgroup G) :=
    (Subgroup.map_mono (le_sup_left.trans le_sup_left : P ≤ (P ⊔ Q) ⊔ R)).trans ha
  have hQ'S : Q' ≤ (S : Subgroup G) :=
    (Subgroup.map_mono (le_sup_right.trans le_sup_left : Q ≤ (P ⊔ Q) ⊔ R)).trans ha
  have hR'S : R' ≤ (S : Subgroup G) := (Subgroup.map_mono le_sup_right).trans ha
  have hPQrank : 2 ≤ pRank 2 (P' ⊔ Q') := by
    change 2 ≤ pRank 2 (P.map e.toMonoidHom ⊔ Q.map e.toMonoidHom)
    rw [← Subgroup.map_sup, pRank_map_automorphism 2 (by decide)]
    exact distinct_even_component_sylow_join_rank L M hL hM hLM hLeven hMeven TL TM
  have hPRrank : 2 ≤ pRank 2 (P' ⊔ R') := by
    change 2 ≤ pRank 2 (P.map e.toMonoidHom ⊔ R.map e.toMonoidHom)
    rw [← Subgroup.map_sup, pRank_map_automorphism 2 (by decide)]
    exact distinct_even_component_sylow_join_rank L N hL hN hLN hLeven hNeven TL TN
  have hQRrank : 2 ≤ pRank 2 (Q' ⊔ R') := by
    change 2 ≤ pRank 2 (Q.map e.toMonoidHom ⊔ R.map e.toMonoidHom)
    rw [← Subgroup.map_sup, pRank_map_automorphism 2 (by decide)]
    exact distinct_even_component_sylow_join_rank M N hM hN hMN hMeven hNeven TM TN
  have hcomponents : ∀ D : Subgroup G, IsComponentOf D ⊤ → D ≤ H := by
    intro D hD
    by_cases hDL : D = L'
    · have hDM : D ≠ M' := by simpa only [hDL] using hLM'
      have hDN : D ≠ N' := by simpa only [hDL] using hLN'
      apply subgroup_le_core_overgroup_of_commutes S H hSH hcore D (Q' ⊔ R')
        (sup_le hQ'S hR'S) hQRrank
      apply commutes_with_join_of_commutes
      · apply le_bot_iff.mp
        calc
          ⁅D, Q'⁆ ≤ ⁅D, M'⁆ := Subgroup.commutator_mono le_rfl hQ'M
          _ = ⊥ := LocalComponents.commute_of_ne D M' hD hM' hDM
      · apply le_bot_iff.mp
        calc
          ⁅D, R'⁆ ≤ ⁅D, N'⁆ := Subgroup.commutator_mono le_rfl hR'N
          _ = ⊥ := LocalComponents.commute_of_ne D N' hD hN' hDN
    · by_cases hDM : D = M'
      · have hDN : D ≠ N' := by simpa only [hDM] using hMN'
        apply subgroup_le_core_overgroup_of_commutes S H hSH hcore D (P' ⊔ R')
          (sup_le hP'S hR'S) hPRrank
        apply commutes_with_join_of_commutes
        · apply le_bot_iff.mp
          calc
            ⁅D, P'⁆ ≤ ⁅D, L'⁆ := Subgroup.commutator_mono le_rfl hP'L
            _ = ⊥ := LocalComponents.commute_of_ne D L' hD hL' hDL
        · apply le_bot_iff.mp
          calc
            ⁅D, R'⁆ ≤ ⁅D, N'⁆ := Subgroup.commutator_mono le_rfl hR'N
            _ = ⊥ := LocalComponents.commute_of_ne D N' hD hN' hDN
      · apply subgroup_le_core_overgroup_of_commutes S H hSH hcore D (P' ⊔ Q')
          (sup_le hP'S hQ'S) hPQrank
        apply commutes_with_join_of_commutes
        · apply le_bot_iff.mp
          calc
            ⁅D, P'⁆ ≤ ⁅D, L'⁆ := Subgroup.commutator_mono le_rfl hP'L
            _ = ⊥ := LocalComponents.commute_of_ne D L' hD hL' hDL
        · apply le_bot_iff.mp
          calc
            ⁅D, Q'⁆ ≤ ⁅D, M'⁆ := Subgroup.commutator_mono le_rfl hQ'M
            _ = ⊥ := LocalComponents.commute_of_ne D M' hD hM' hDM
  let E := Layer.subgroup G
  let : E.Normal := Layer.normal G
  have hEH : E ≤ H := sSup_le hcomponents
  have hP'E : P' ≤ E := hP'L.trans (Layer.component_le hL')
  have hQ'E : Q' ≤ E := hQ'M.trans (Layer.component_le hM')
  have hErank : 2 ≤ pRank 2 E :=
    hPQrank.trans (pRank_mono 2 (by decide) (sup_le hP'E hQ'E))
  exact normal_rank_two_not_le_overgroup S H hH hSH hcore E hErank hEH

theorem ncard_le_two_of_no_three {α : Type*} [Finite α] (A : Set α)
    (h : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → b ≠ c → False) :
    A.ncard ≤ 2 := by
  classical
  by_cases hnone : A = ∅
  · simp [hnone]
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr hnone
  by_cases hone : ∀ b ∈ A, b = a
  · have hsubset : A ⊆ {a} := fun b hb => Set.mem_singleton_iff.mpr (hone b hb)
    exact (Set.ncard_le_ncard hsubset).trans (by simp)
  push Not at hone
  obtain ⟨b, hb, hba⟩ := hone
  have hsubset : A ⊆ {a, b} := by
    intro c hc
    by_cases hca : c = a
    · simp [hca]
    by_cases hcb : c = b
    · simp [hcb]
    exact (h a ha b hb c hc hba.symm (Ne.symm hca) (Ne.symm hcb)).elim
  exact (Set.ncard_le_ncard hsubset).trans (le_of_eq (Set.ncard_pair hba.symm))

theorem proper_full_core_even_components_ncard_le_two
    (S : Sylow 2 G) (H : Subgroup G) (hH : H ≠ ⊤)
    (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H) :
    {L : Subgroup G | IsComponentOf L ⊤ ∧ Even (Nat.card L)}.ncard ≤ 2 := by
  apply ncard_le_two_of_no_three
  intro L hL M hM N hN hLM hLN hMN
  exact proper_full_core_no_three_even_components S H hH hSH hcore L M N
    hL.1 hM.1 hN.1 hL.2 hM.2 hN.2 hLM hLN hMN

theorem component_even_of_odd_core_eq_bot
    (hoddcore : componentClassificationOddCore G = ⊥)
    (L : Subgroup G) (hL : IsComponentOf L ⊤) : Even (Nat.card L) := by
  obtain heven | hodd := Nat.even_or_odd (Nat.card L)
  · exact heven
  have hcore : componentClassificationOddCore L = ⊥ :=
    OddCore.subnormal_corefree hoddcore L hL.2.1
  have htop : componentClassificationOddCore L = ⊤ := by
    apply top_unique
    exact OddCore.maximal L ⊤ (by infer_instance) (by simpa using hodd)
  have hbot : (⊤ : Subgroup L) = ⊥ := htop.symm.trans hcore
  let : Nontrivial L := Quasisimple.nontrivial hL.2.2
  exact (top_ne_bot hbot).elim

theorem proper_full_core_component_number_restrictions
    (S : Sylow 2 G) (H : Subgroup G) (hH : H ≠ ⊤)
    (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H) :
    {L : Subgroup G | IsComponentOf L ⊤ ∧ 2 ≤ pRank 2 L}.ncard ≤ 1 ∧
      (∀ L : Subgroup G, IsComponentOf L ⊤ → 2 ≤ pRank 2 L →
        ∃ hchar : L.Characteristic,
          letI := hchar
          letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          let T := CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal S L
          (T : Subgroup L).map L.subtype = (S : Subgroup G) ⊓ L ∧
            properTwoGenCoreGamma (T : Subgroup L) 2 ≤ H.subgroupOf L ∧
              H.subgroupOf L < ⊤ ∧ pRank 2 (Subgroup.centralizer (L : Set G)) ≤ 1) ∧
      {L : Subgroup G | IsComponentOf L ⊤ ∧ Even (Nat.card L)}.ncard ≤ 2 ∧
      (componentClassificationOddCore G = ⊥ →
        (∀ L : Subgroup G, IsComponentOf L ⊤ → Even (Nat.card L)) ∧
          {L : Subgroup G | IsComponentOf L ⊤}.ncard ≤ 2) := by
  refine ⟨?_, ?_, proper_full_core_even_components_ncard_le_two S H hH hSH hcore, ?_⟩
  · apply (Set.ncard_le_one_iff (Set.toFinite _)).mpr
    intro L M hL hM
    exact proper_full_core_high_rank_component_unique S H hH hSH hcore L M
      hL.1 hM.1 hL.2 hM.2
  · intro L hL hrank
    exact proper_full_core_high_rank_component_restrictions S H hH hSH hcore L hL hrank
  · intro hodd
    refine ⟨component_even_of_odd_core_eq_bot hodd, ?_⟩
    have hset : {L : Subgroup G | IsComponentOf L ⊤} =
        {L : Subgroup G | IsComponentOf L ⊤ ∧ Even (Nat.card L)} := by
      ext L
      exact ⟨fun hL => ⟨hL, component_even_of_odd_core_eq_bot hodd L hL⟩, And.left⟩
    rw [hset]
    exact proper_full_core_even_components_ncard_le_two S H hH hSH hcore

end CFSG.ProperTwoGeneratedCore
