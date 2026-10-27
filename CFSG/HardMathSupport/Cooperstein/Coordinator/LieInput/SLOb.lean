module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SLLevi
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SLChev
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.CentralLift
public import CFSG.Quasithin.EmptyFaithful.R3c21A

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear CFSG.LieType.CurtisTits
  CFSG.AGLEmbedding CFSG.AGLEmbedding.LieOut CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.AGLEmbeddingD2.SquareLinear CFSG.Quasithin.SmithC27 CFSG.LieType.Steinberg

section Inj

variable {m : ℕ} {F : Type} [Field F]

theorem range_coordHom_inf_center_eq_bot (S : Finset (Fin (m + 1))) {a : Fin (m + 1)} (ha : a ∉ S) :
    (coordHom (F := F) S).range ⊓ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨A, rfl⟩, hz⟩
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have h1 := coordHom_apply_of_not_mem S A (Or.inl ha : a ∉ S ∨ a ∉ S)
  have h2 := congrFun (congrFun hr a) a
  have hr1 : r = 1 := by
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h2
    rw [h2, h1]
    simp
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hr, hr1]
  simp

theorem exists_mulEquiv_map_range_coordHom {Y : Type} [Group Y]
    (π : SpecialLinearGroup (Fin (m + 1)) F →* Y)
    (hker : π.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    (S : Finset (Fin (m + 1))) {a : Fin (m + 1)} (ha : a ∉ S) :
    Nonempty (↥(((coordHom (F := F) S).range).map π) ≃* SpecialLinearGroup (Fin S.card) F) := by
  classical
  have hinj : Function.Injective (π.comp (coordHom (F := F) S).range.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx1 : π (x : SpecialLinearGroup (Fin (m + 1)) F) = 1 := hx
    have hxz := hker hx1
    have : (x : SpecialLinearGroup (Fin (m + 1)) F) ∈ (⊥ : Subgroup _) := by
      rw [← range_coordHom_inf_center_eq_bot S ha]
      exact ⟨x.2, hxz⟩
    rw [Subgroup.mem_bot] at this ⊢
    exact Subtype.ext this
  have hrange : (π.comp (coordHom (F := F) S).range.subtype).range =
      ((coordHom (F := F) S).range).map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have eA : ↥((coordHom (F := F) S).range) ≃* ↥(((coordHom (F := F) S).range).map π) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have eB : ↥((coordHom (F := F) S).range) ≃* SpecialLinearGroup ↥S F :=
    (MonoidHom.ofInjective (coordHom_injective (F := F) S)).symm
  exact ⟨(eA.symm.trans eB).trans (slReindexEquiv (Finset.equivFin S))⟩

theorem blockChev [Finite F] [CharP F 2] {Y : Type} [Group Y]
    (π : SpecialLinearGroup (Fin (m + 1)) F →* Y)
    (hker : π.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    (S : Finset (Fin (m + 1))) {a : Fin (m + 1)} (ha : a ∉ S)
    (hNS : 3 ≤ S.card ∨ (S.card = 2 ∧ 4 ≤ Nat.card F)) :
    CFSG.IsQuasisimple ↥(((coordHom (F := F) S).range).map π) ∧
      IsClassicalTwoOrG2 (↥(((coordHom (F := F) S).range).map π) ⧸
        Subgroup.center ↥(((coordHom (F := F) S).range).map π)) := by
  obtain ⟨e⟩ := exists_mulEquiv_map_range_coordHom π hker S ha
  obtain ⟨h1, h2⟩ := isChevComponent_sl (F := F) hNS
  exact ⟨isQuasisimple_of_mulEquiv e.symm h1,
    isClassicalTwoOrG2_of_mulEquiv (quotCenterCongr e.symm) h2⟩

theorem range_coordHom_le_centralizer {N : ℕ} {S S' : Finset (Fin N)} (h : Disjoint S S') :
    (coordHom (F := F) S).range ≤
      Subgroup.centralizer ((coordHom (F := F) S').range : Set (SpecialLinearGroup (Fin N) F)) := by
  rintro _ ⟨A, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨A', rfl⟩
  exact (coordHom_commute_of_disjoint h A A').symm

theorem isSolvable_range_coordHom_of_card_two {N : ℕ} [Finite F] (S : Finset (Fin N))
    (hS : S.card = 2) (hF : Nat.card F = 2) :
    Group.IsSolvable ↥((coordHom (F := F) S).range) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hsolv : Group.IsSolvable (SpecialLinearGroup (Fin 2) F) :=
    CFSG.Quasithin.R3c21.S0.isSolvable_sl2_of_card_two hcard
  let e : ↥((coordHom (F := F) S).range) ≃* SpecialLinearGroup (Fin 2) F :=
    ((MonoidHom.ofInjective (coordHom_injective (F := F) S)).symm.trans
      (slReindexEquiv (Finset.equivFin S))).trans (slReindexEquiv (finCongr hS))
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

end Inj

section Blk

open Classical

variable {m : ℕ} {F : Type} [Field F] {I : Set (Fin m)}

theorem rankOne_le_range_blkSet {i : Fin m} (hi : i ∈ I) :
    rankOne (rootDatum m F).rootGroup i ≤ (coordHom (F := F) (blkSet I i.castSucc)).range := by
  have hs : SameBlk I i.castSucc i.succ := by
    intro j hj
    have : j.val ≠ i.val := fun h => hj (Fin.ext h ▸ hi)
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  exact rankOne_le_range_coordHom i (mem_blkSet.mpr (SameBlk.refl I _)) (mem_blkSet.mpr hs)

theorem exists_not_mem_blkSet (hI : I ≠ Set.univ) (p : Fin (m + 1)) : ∃ a, a ∉ blkSet I p := by
  by_contra h
  push Not at h
  have h0 := mem_blkSet.mp (h 0)
  have h1 := mem_blkSet.mp (h (Fin.last m))
  exact not_sameBlk_of_sepBlk (sepBlk_zero_last hI) (h0.symm.trans h1)

theorem two_le_card_blkSet {i : Fin m} (hi : i ∈ I) : 2 ≤ (blkSet I i.castSucc).card := by
  have hs : SameBlk I i.castSucc i.succ := by
    intro j hj
    have : j.val ≠ i.val := fun h => hj (Fin.ext h ▸ hi)
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  exact Finset.one_lt_card.mpr ⟨i.castSucc, mem_blkSet.mpr (SameBlk.refl I _), i.succ,
    mem_blkSet.mpr hs, Fin.castSucc_lt_succ.ne⟩

theorem leviOb_sl [Finite F] [CharP F 2] {Y : Type} [Group Y]
    (π : SpecialLinearGroup (Fin (m + 1)) F →* Y)
    (hker : π.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    (hI : I ≠ Set.univ) : LeviOb (rootDatum m F) (torus m F) π I := by
  obtain ⟨f, hf1, hfcard⟩ := CFSG.AGLEmbedding.ParabHub.exists_card_eq_two_pow F
  have hext := steinbergExtras m F
  let blocks : Finset (Finset (Fin (m + 1))) := Finset.univ.image (blkSet I)
  let NSb : Finset (Fin (m + 1)) → Prop := fun B => 3 ≤ B.card ∨ (B.card = 2 ∧ 4 ≤ Nat.card F)
  let SOb : Finset (Fin (m + 1)) → Prop := fun B => B.card = 2 ∧ Nat.card F = 2
  have hexcl : ∀ B, NSb B → ¬ SOb B := by
    rintro B (h | ⟨h1, h2⟩) ⟨h3, h4⟩
    · omega
    · omega
  have hdich : ∀ B : Finset (Fin (m + 1)), 2 ≤ B.card → NSb B ∨ SOb B := by
    intro B hB
    by_cases h3 : 3 ≤ B.card
    · exact Or.inl (Or.inl h3)
    · have h2 : B.card = 2 := by omega
      by_cases hf : f = 1
      · exact Or.inr ⟨h2, by rw [hfcard, hf]; norm_num⟩
      · refine Or.inl (Or.inr ⟨h2, ?_⟩)
        rw [hfcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  let ι := ↥(blocks.filter NSb)
  let κ := ↥(blocks.filter SOb)
  have hblocks : ∀ B ∈ blocks, ∃ p, B = blkSet I p := by
    intro B hB
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hB
    exact ⟨p, rfl⟩
  let T : Subgroup (SpecialLinearGroup (Fin (m + 1)) F) := ⨆ k, torus m F k
  let Kb : Finset (Fin (m + 1)) → Subgroup (SpecialLinearGroup (Fin (m + 1)) F) :=
    fun B => (coordHom (F := F) B).range
  let E : Subgroup (SpecialLinearGroup (Fin (m + 1)) F) := T ⊔ ⨆ B : κ, Kb B.1
  let Cf : ι → Subgroup (SpecialLinearGroup (Fin (m + 1)) F) := fun B => Kb B.1
  have hdisj : ∀ B ∈ blocks, ∀ B' ∈ blocks, B ≠ B' → Disjoint B B' := by
    intro B hB B' hB' hne
    obtain ⟨p, rfl⟩ := hblocks B hB
    obtain ⟨q, rfl⟩ := hblocks B' hB'
    exact disjoint_blkSet hne
  have hKleviM : ∀ B ∈ blocks, Kb B ≤ leviM (rootDatum m F) I := by
    intro B hB
    obtain ⟨p, rfl⟩ := hblocks B hB
    exact range_coordHom_le_leviM p
  have hTnorm : ∀ B, T ≤ Subgroup.normalizer ((Kb B : Subgroup _) : Set _) := fun B =>
    torus_le_normalizer_range B
  have hmemNS : ∀ B : ι, B.1 ∈ blocks ∧ NSb B.1 := fun B => Finset.mem_filter.mp B.2
  have hmemSO : ∀ B : κ, B.1 ∈ blocks ∧ SOb B.1 := fun B => Finset.mem_filter.mp B.2
  have hne_NS_SO : ∀ (B : ι) (B' : κ), B.1 ≠ B'.1 := fun B B' h =>
    hexcl B.1 (hmemNS B).2 (h ▸ (hmemSO B').2)
  have hKsol : ∀ B : κ, Group.IsSolvable ↥(Kb B.1) := fun B =>
    isSolvable_range_coordHom_of_card_two B.1 (hmemSO B).2.1 (hmemSO B).2.2
  have hR : Group.IsSolvable ↥(⨆ B : κ, Kb B.1) := by
    refine isSolvable_iSup_of_commute _ hKsol fun B B' hne => ?_
    exact range_coordHom_le_centralizer (hdisj B.1 (hmemSO B).1 B'.1 (hmemSO B').1
      (fun h => hne (Subtype.ext h)))
  have hT : Group.IsSolvable ↥T :=
    isSolvable_of_comm (fun a b => (isMulCommutative_torus hext).is_comm.comm a b)
  have hTn : T ≤ Subgroup.normalizer (((⨆ B : κ, Kb B.1 : Subgroup _)) : Set _) :=
    le_normalizer_iSup fun B => hTnorm B.1
  have hEsolv : Group.IsSolvable ↥E := by
    have := isSolvable_sup_of_normalizes' hR hT hTn
    rwa [sup_comm] at this
  refine ⟨Fintype.card ι, fun j => Cf ((Fintype.equivFin ι).symm j), E, le_sup_left, ?_, hEsolv,
    ?_, ?_, ?_⟩
  · refine sup_le le_sup_left (le_sup_right.trans' ?_)
    exact iSup_le fun B => hKleviM B.1 (hmemSO B).1
  · intro j
    set B : ι := (Fintype.equivFin ι).symm j with hB
    obtain ⟨hBb, hNS⟩ := hmemNS B
    refine ⟨hKleviM B.1 hBb, ?_, ?_⟩
    · refine sup_le (hTnorm B.1) (iSup_le fun B' => ?_)
      exact (range_coordHom_le_centralizer (hdisj B'.1 (hmemSO B').1 B.1 hBb
        (fun h => hne_NS_SO B B' h.symm))).trans (Subgroup.centralizer_le_normalizer _)
    · obtain ⟨p, hp⟩ := hblocks B.1 hBb
      obtain ⟨a, ha⟩ := exists_not_mem_blkSet hI p
      have ha' : a ∉ B.1 := by rw [hp]; exact ha
      exact blockChev π hker B.1 ha' hNS
  · intro j j' hjj'
    have hne : (Fintype.equivFin ι).symm j ≠ (Fintype.equivFin ι).symm j' := fun h =>
      hjj' ((Fintype.equivFin ι).symm.injective h)
    exact range_coordHom_le_centralizer (hdisj _ (hmemNS _).1 _ (hmemNS _).1
      (fun h => hne (Subtype.ext h)))
  · have hiS : (⨆ j, Cf ((Fintype.equivFin ι).symm j)) = ⨆ B : ι, Cf B :=
      (Fintype.equivFin ι).symm.iSup_comp (g := Cf)
    rw [hiS]
    refine iSup₂_le fun i hi => ?_
    have hB0 : blkSet I i.castSucc ∈ blocks := Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    rcases hdich _ (two_le_card_blkSet hi) with hNS | hSO
    · exact (rankOne_le_range_blkSet hi).trans (le_sup_of_le_right
        (le_iSup (fun B : ι => Cf B) ⟨blkSet I i.castSucc, Finset.mem_filter.mpr ⟨hB0, hNS⟩⟩))
    · exact (rankOne_le_range_blkSet hi).trans (le_sup_of_le_left (le_sup_of_le_right
        (le_iSup (fun B : κ => Kb B.1) ⟨blkSet I i.castSucc, Finset.mem_filter.mpr ⟨hB0, hSO⟩⟩)))

end Blk

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
