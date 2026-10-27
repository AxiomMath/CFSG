module

public import CFSG.HardMathSupport.Solomon.Coordinator.McLTypeFactsOrth
public import CFSG.HardMathSupport.Solomon.Coordinator.McLTypeFactsSL
public import CFSG.HardMathSupport.Solomon.Coordinator.McLTypeFactsSp

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Assembly.LowTwoRank Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

@[expose] def mcl_Good (W : Type) [Group W] : Prop :=
  Group.IsSolvable W → Nat.card W = 6 ∨ Nat.card W = 72

theorem mcl_good_of_mulEquiv {W W' : Type} [Group W] [Group W'] (e : W ≃* W')
    (h : mcl_Good W') : mcl_Good W := fun hs => by
  rw [Nat.card_congr e.toEquiv]
  exact h (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

theorem mcl_good_of_not_solvable {W : Type} [Group W] (h : ¬ Group.IsSolvable W) : mcl_Good W :=
  fun hs => absurd hs h

theorem mcl_not_solvable_of_derived {W : Type} [Group W] (L : Subgroup W) (k : ℕ)
    (hk : derivedSeries W k = L) (hs : IsSimpleGroup L) (hna : ∃ a b : L, a * b ≠ b * a) :
    ¬ Group.IsSolvable W := by
  have hperf := mcltf_commutator_eq_self L hna
  have hD : ∀ j : ℕ, derivedSeries W (k + j) = L := by
    intro j
    induction j with
    | zero => exact hk
    | succ j ih => rw [← add_assoc, derivedSeries_succ, ih, hperf]
  rintro ⟨n, hn⟩
  have hle : L ≤ derivedSeries W n := by
    rcases le_total n k with hnk | hkn
    · exact hk.symm.le.trans (derivedSeries_antitone W hnk)
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkn
      exact (hD j).symm.le
  rw [hn, le_bot_iff] at hle
  obtain ⟨a, b, hab⟩ := hna
  apply hab
  have ha : (a : W) = 1 := Subgroup.mem_bot.mp (hle ▸ a.2)
  have hb : (b : W) = 1 := Subgroup.mem_bot.mp (hle ▸ b.2)
  exact Subtype.ext (by simp [ha, hb])

theorem mcl_not_solvable_of_simple {W : Type} [Group W] [IsSimpleGroup W]
    (hna : ∃ a b : W, a * b ≠ b * a) : ¬ Group.IsSolvable W := by
  refine mcl_not_solvable_of_derived ⊤ 0 (derivedSeries_zero W) (Subgroup.topEquiv.isSimpleGroup) ?_
  obtain ⟨a, b, hab⟩ := hna
  exact ⟨⟨a, Subgroup.mem_top a⟩, ⟨b, Subgroup.mem_top b⟩, fun h => hab (by
    simpa using congrArg Subtype.val h)⟩

theorem mcl_good_perm {n : ℕ} (hn : 5 ≤ n) : mcl_Good (Equiv.Perm (Fin n)) := by
  refine mcl_good_of_not_solvable ?_
  have h5 : 5 ≤ Nat.card (Fin n) := by rwa [Nat.card_eq_fintype_card, Fintype.card_fin]
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hs := alternatingGroup.isSimpleGroup h5
  refine mcl_not_solvable_of_derived (alternatingGroup (Fin n)) 1 ?_ hs ?_
  · rw [derivedSeries_one]
    exact alternatingGroup.commutator_perm_eq h5
  · exact mcltf_exists_ne_of_perfect (commutator_alternatingGroup_eq_top h5)

theorem mcl_good_SL {n : ℕ} (hn : 2 ≤ n) :
    mcl_Good (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  rcases Nat.lt_or_ge n 3 with h | h
  · obtain rfl : n = 2 := by omega
    intro _
    exact Or.inl mcltf_card_SL22
  · have := mcltf_isSimpleGroup_SL h
    exact mcl_good_of_not_solvable (mcl_not_solvable_of_simple (mcltf_exists_ne_of_perfect
      (CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect h).commutator_eq_top))

theorem mcl_good_Sp {n : ℕ} (hn : 2 ≤ n) : mcl_Good ↥(StatedSp n (ZMod 2)) := by
  rcases Nat.lt_or_ge n 3 with h | h
  · obtain rfl : n = 2 := by omega
    exact mcl_good_of_mulEquiv
      (CFSG.QuasithinUnique.Bridge.Alt57Model.spEquivPerm (ZMod 2) (ZMod.card 2))
      (mcl_good_perm (by norm_num))
  · have hK : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
    have hs := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (ZMod 2) n
      (by omega) (Or.inr (Or.inr ⟨hK, h⟩))
    have : IsSimpleGroup ↥(StatedSp n (ZMod 2)) := (mcltf_spProjEquiv n).isSimpleGroup
    exact mcl_good_of_not_solvable (mcl_not_solvable_of_simple (mcltf_exists_ne_of_perfect
      (CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp n (ZMod 2)
        (Or.inr (Or.inr ⟨hK, h⟩))).commutator_eq_top))

section Orth

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem mcl_not_solvable_orth [Finite V] (Q : QuadraticForm (ZMod 2) V)
    (hs : IsSimpleGroup ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hna : ∃ a b : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆, a * b ≠ b * a) :
    ¬ Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
  set O := TauCeti.QuadraticMap.orthogonalGroup Q
  have hle : ⁅O, O⁆ ≤ O := Subgroup.commutator_le_self O
  let e : ↥(⁅O, O⁆.subgroupOf O) ≃* ↥⁅O, O⁆ := Subgroup.subgroupOfEquivOfLe hle
  refine mcl_not_solvable_of_derived (⁅O, O⁆.subgroupOf O) 1 ?_ e.isSimpleGroup ?_
  · rw [derivedSeries_one, mcltf_commutator_subgroupOf_self]
  · obtain ⟨a, b, hab⟩ := hna
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

theorem mcl_not_solvable_orth_of_elementary [FiniteDimensional (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hnt : Nontrivial V)
    (hs : IsSimpleGroup (ProjElementary Q)) (hperf : commutator (elementaryGroup Q) = ⊤) :
    ¬ Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have hsE : IsSimpleGroup ↥(elementaryGroup Q) :=
    ((QuotientGroup.quotientMulEquivOfEq (mcltf_scalars_subgroupOf_eq_bot _)).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  refine mcl_not_solvable_orth Q (by rw [hE]; exact hsE) ?_
  rw [hE]
  exact mcltf_exists_ne_of_perfect hperf

theorem mcl_good_orth_quadPlus {n : ℕ} (hn : 2 ≤ n) :
    mcl_Good ↥(TauCeti.QuadraticMap.orthogonalGroup (quadPlus n (ZMod 2))) := by
  rcases Nat.lt_or_ge n 3 with h | h
  · obtain rfl : n = 2 := by omega
    refine mcl_good_of_mulEquiv
      (TauCeti.QuadraticMap.orthogonalGroupCongr mcltf_plusIsometry) ?_
    refine mcl_good_of_mulEquiv mcltf_OPlus4Equiv.symm ?_
    intro _
    exact Or.inr mcltf_card_OPlus4
  · refine mcl_good_of_not_solvable ?_
    obtain ⟨hQ, T, hT, hTQ⟩ := regular_quadPlus (K := ZMod 2) h
    have : Nontrivial (Fin n ⊕ Fin n → ZMod 2) := by
      have : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, by omega⟩⟩
      infer_instance
    exact mcl_not_solvable_orth_of_elementary _ (commutator_orthogonalGroup_quadPlus h) this
      (isSimpleGroup_projElementary_quadPlus h)
      (commutator_elementaryGroup_eq_top' hQ hT.ge hTQ)

theorem mcl_good_orth_quadMinus {m : ℕ} (hm : 2 ≤ m) :
    mcl_Good ↥(TauCeti.QuadraticMap.orthogonalGroup (quadMinus m (ZMod 2) 1 1)) := by
  refine mcl_good_of_not_solvable ?_
  have hm1 : 1 ≤ m := by omega
  have hdim := mcltf_finrank_quadMinus hm1
  rcases Nat.lt_or_ge m 4 with h | h
  · have hQ := nondegenerate_polarBilin_quadMinus_of_finite m (ZMod 2) mcltf_irr
    have hts : ∀ U : Submodule (ZMod 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2),
        finrank (ZMod 2) U = finrank (ZMod 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2) / 2 →
          ∃ u ∈ U, quadMinus m (ZMod 2) 1 1 u ≠ 0 := by
      intro U hU
      by_contra h
      push Not at h
      exact CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus hm1 mcltf_irr
        ⟨U, by rw [hU, hdim]; omega, h⟩
    obtain ⟨hs, -, hna, -, -⟩ :=
      CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction
        (quadMinus m (ZMod 2) 1 1) hQ (by rw [hdim]; omega) hts
    have : Finite (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2) := inferInstance
    refine mcl_not_solvable_orth _ hs ?_
    push Not at hna
    exact hna
  · obtain ⟨hQ, T, hT, hTQ⟩ := regular_quadMinus (K := ZMod 2) h mcltf_irr
    have : Nontrivial (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2) := by
      have : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
      infer_instance
    exact mcl_not_solvable_orth_of_elementary _ (commutator_orthogonalGroup_quadMinus h mcltf_irr)
      this (isSimpleGroup_projElementary_quadMinus h mcltf_irr)
      (commutator_elementaryGroup_eq_top' hQ hT.ge hTQ)

theorem mcl_good_glaPlus {n : ℕ} (hn : 2 ≤ n) :
    mcl_Good ↥(CFSG.Open.GLAOrthGroup (CFSG.Open.GLAQPlus (ZMod 2) n)) :=
  mcl_good_of_mulEquiv (mcltf_glaOrthEquiv (mcltf_coe_quadPlus n)) (mcl_good_orth_quadPlus hn)

theorem mcl_good_glaMinus {n : ℕ} (hn : 1 ≤ n) :
    mcl_Good ↥(CFSG.Open.GLAOrthGroup (CFSG.Open.GLAQMinus n (1 : ZMod 2) 1)) :=
  mcl_good_of_mulEquiv ((mcltf_glaOrthEquiv (mcltf_coe_quadMinusGLA n 1 1)).trans
    (TauCeti.QuadraticMap.orthogonalGroupCongr (mcltf_minusIsometry n 1 1)))
    (mcl_good_orth_quadMinus (by omega))

end Orth

theorem mcl_solvable_card {W : Type} [Group W] (h : UniquenessMaximal.IsMcLaughlinGroup W)
    (hs : Group.IsSolvable W) : Nat.card W = 6 ∨ Nat.card W = 72 := by
  rcases h with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact mcl_good_of_mulEquiv e
      (mcl_good_of_mulEquiv (mcltf_SLEquiv n).symm (mcl_good_SL hn)) hs
  · exact mcl_good_of_mulEquiv e
      (mcl_good_of_mulEquiv (MulEquiv.subgroupCongr rfl) (mcl_good_Sp hn)) hs
  · exact mcl_good_of_mulEquiv e (mcl_good_glaPlus hn) hs
  · exact mcl_good_of_mulEquiv e (mcl_good_glaMinus hn) hs
  · exact mcl_good_of_mulEquiv e (mcl_good_perm hn) hs

end CFSG.HardMathSupport.Solomon.Coordinator
