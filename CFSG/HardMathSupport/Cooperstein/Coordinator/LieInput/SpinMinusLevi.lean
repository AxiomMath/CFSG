module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinMinusBlocks
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinMinusModel
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinMinusComm
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.LeviGeneric
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.OrthMinus
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinMinusComb

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

section Fam

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.AGLEmbeddingD2.ParabLevi CFSG.AGLEmbedding
  CFSG.Assembly.LowTwoRank

@[expose] def lastNodes (n a : ℕ) : Set (Fin (n - 1)) := {j | a ≤ j.val}

variable
  {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

@[expose] def LastBlockEquiv (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) : Prop :=
  ∀ a k : ℕ, a + k = n → 3 ≤ k →
    Nonempty (spinGroup (quadMinus k F b c) ≃* ↥(leviM (minusDatum n hirr) (lastNodes n a)))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem block_decomp_minus (hn : 4 ≤ n) (hlast : LastBlockEquiv n hirr) {Y : Type} [Group Y]
    (π : spinGroup (quadMinus n F b c) →* Y)
    (hker : ∀ z ∈ π.ker, z ∈ Subgroup.center (spinGroup (quadMinus n F b c)))
    (A : Subgroup (spinGroup (quadMinus n F b c))) {J : Set (Fin (n - 1))}
    (hA : A ≤ Subgroup.normalizer ((leviM (minusDatum n hirr) J : Subgroup _) : Set _))
    (hJ : (∃ lo hi : ℕ, lo ≤ hi ∧ hi + 2 < n ∧ J = runNodes n lo hi) ∨
      ∃ a : ℕ, a + 2 ≤ n ∧ J = lastNodes n a) :
    ∃ E C : Subgroup (spinGroup (quadMinus n F b c)),
      E ≤ leviM (minusDatum n hirr) J ∧ C ≤ leviM (minusDatum n hirr) J ∧
      leviM (minusDatum n hirr) J ≤ E ⊔ C ∧ Group.IsSolvable ↥E ∧
      E ≤ Subgroup.normalizer (C : Set (spinGroup (quadMinus n F b c))) ∧
      A ≤ Subgroup.normalizer (E : Set (spinGroup (quadMinus n F b c))) ∧
      A ≤ Subgroup.normalizer (C : Set (spinGroup (quadMinus n F b c))) ∧
      (C ≠ ⊥ → CFSG.IsQuasisimple ↥(C.map π) ∧
        IsClassicalTwoOrG2 (↥(C.map π) ⧸ Subgroup.center ↥(C.map π))) := by
  obtain ⟨f, hf1, hfcard⟩ := CFSG.AGLEmbedding.ParabHub.exists_card_eq_two_pow F
  rcases hJ with ⟨lo, hi, hlh, hhi, rfl⟩ | ⟨a, ha, rfl⟩
  · let e1 := chEquivMinus hirr hlh hhi hn
    by_cases h3 : 3 ≤ hi - lo + 2
    · exact decomp_of_chev π hker A _ hA e1 (isChevComponent_sl (Or.inl h3))
    · have h2 : hi - lo + 2 = 2 := by omega
      by_cases hf : f = 1
      · subst hf
        have : Fintype F := Fintype.ofFinite F
        have hF2 : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hfcard]; norm_num
        have hsolv : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin (hi - lo + 2)) F) := by
          rw [h2]; exact CFSG.Quasithin.R3c21.S0.isSolvable_sl2_of_card_two hF2
        haveI := hsolv
        exact decomp_so π A _ hA (Group.isSolvable_of_isSolvable_injective
          (f := e1.symm.toMonoidHom) e1.symm.injective)
      · have h4 : 4 ≤ Nat.card F := by
          rw [hfcard]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact decomp_of_chev π hker A _ hA e1 (isChevComponent_sl (Or.inr ⟨h2, h4⟩))
  · by_cases hk : 3 ≤ n - a
    · obtain ⟨e⟩ := hlast a (n - a) (by omega) hk
      by_cases hk4 : 4 ≤ n - a
      · exact decomp_of_chev π hker A _ hA e (isChevComponent_spinMinus hirr hk4)
      · have h3 : n - a = 3 := by omega
        have key : ∀ k : ℕ, k = 3 → CFSG.IsQuasisimple (spinGroup (quadMinus k F b c)) ∧
            IsClassicalTwoOrG2 (spinGroup (quadMinus k F b c) ⧸
              Subgroup.center (spinGroup (quadMinus k F b c))) := by
          rintro k rfl
          exact chev_spinMinus_three hirr
        exact decomp_of_chev π hker A _ hA e (key _ h3)
    · have h2 : a = n - 2 := by omega
      subst h2
      have hi0 : ¬ (n - 2) + 1 < n - 1 := by omega
      let i0 : Fin (minusDatum n hirr).rank := ⟨n - 2, by change n - 2 < n - 1; omega⟩
      have hset : lastNodes n (n - 2) = {i0} := by
        ext j
        simp only [lastNodes, Set.mem_setOf_eq, Set.mem_singleton_iff]
        have := j.isLt
        constructor
        · intro h; exact Fin.ext (by simp [i0]; omega)
        · intro h; rw [h]
      have heq : leviM (minusDatum n hirr) (lastNodes n (n - 2)) =
          rankOne (minusDatum n hirr).rootGroup i0 := by
        rw [hset]
        refine le_antisymm (iSup₂_le fun i hi => ?_)
          (le_iSup₂_of_le (f := fun i (_ : i ∈ ({i0} : Set (Fin (minusDatum n hirr).rank))) =>
            rankOne (minusDatum n hirr).rootGroup i) i0 (Set.mem_singleton _) le_rfl)
        have hi' : i = i0 := hi
        subst hi'
        exact le_rfl
      haveI := fact_shortField hirr
      haveI := finite_shortField (b := b) (c := c)
      haveI := charP_shortField (b := b) (c := c)
      let e := (shortEquiv n hirr i0 hi0).trans (MulEquiv.subgroupCongr heq.symm)
      exact decomp_of_chev π hker A _ hA e
        (isChevComponent_sl (F := ShortField b c) (k := 2)
          (Or.inr ⟨rfl, four_le_card_shortField⟩))

theorem leviOb_spinMinus (hn : 4 ≤ n) (hlast : LastBlockEquiv n hirr) {Y : Type} [Group Y]
    (π : spinGroup (quadMinus n F b c) →* Y)
    (hker : ∀ z ∈ π.ker, z ∈ Subgroup.center (spinGroup (quadMinus n F b c)))
    (I : Set (Fin (n - 1))) :
    LeviOb (minusDatum n hirr) (minusTorus n hirr) π I := by
  classical
  have hct := minusDatum_isCTGroupDatum n hirr hn
  have hext := minusDatum_steinbergExtras n hirr
  let blocks : Finset (Finset (Fin (n - 1 + 1))) :=
    (Finset.univ.image (blkSet I)).filter fun B => (nodesOf B).Nonempty
  have hblocks : ∀ b : ↥blocks, ∃ p, b.1 = blkSet I p ∧ (nodesOf b.1).Nonempty := by
    intro b
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp b.2
    obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hb1
    exact ⟨p, hp.symm, hb2⟩
  have hTn : ∀ J : Set (Fin (minusDatum n hirr).rank), (⨆ k, minusTorus n hirr k) ≤
      Subgroup.normalizer ((leviM (minusDatum n hirr) J : Subgroup _) : Set _) := fun J =>
    torus_le_normalizer_leviM (D := minusDatum n hirr) (H := minusTorus n hirr)
      (n := minusWeyl n hirr) (I := J) hct
  refine leviOb_of_node_family hct hext π I (fun b : ↥blocks => nodesOf b.1) ?_ ?_ ?_ ?_
  · intro b
    obtain ⟨p, hp, -⟩ := hblocks b
    rw [hp]
    exact nodesOf_subset p
  · intro i hi
    refine ⟨⟨blkSet I i.castSucc, Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
      ⟨_, Finset.mem_univ _, rfl⟩, ⟨i, mem_nodesOf_of_mem hi⟩⟩⟩, mem_nodesOf_of_mem hi⟩
  · intro b b' hbb' i hi j hj
    obtain ⟨p, hp, -⟩ := hblocks b
    obtain ⟨q, hq, -⟩ := hblocks b'
    have hpq : blkSet I p ≠ blkSet I q := fun h => hbb' (Subtype.ext (by rw [hp, hq, h]))
    rw [hp] at hi
    rw [hq] at hj
    obtain ⟨hne, hadj⟩ := nodes_nonadj hpq hi hj
    exact rankOne_commute_B n hirr hne hadj
  · intro b
    obtain ⟨p, hp, hne⟩ := hblocks b
    rw [hp] at hne ⊢
    obtain ⟨lo, hi, hlh, hhm, hnodes, hlast'⟩ := blk_interval hne
    refine block_decomp_minus hirr hn hlast π hker _ (hTn _) ?_
    by_cases hb : hi = n - 1
    · right
      refine ⟨lo, by omega, ?_⟩
      ext j
      refine (hnodes j).trans ?_
      have hj : j.val < n - 1 := j.isLt
      show lo ≤ j.val ∧ j.val < hi ↔ lo ≤ j.val
      omega
    · left
      refine ⟨lo, hi - 1, by omega, by omega, ?_⟩
      ext j
      refine (hnodes j).trans ?_
      have hj : j.val < n - 1 := j.isLt
      show lo ≤ j.val ∧ j.val < hi ↔ lo ≤ j.val ∧ j.val ≤ hi - 1
      omega

theorem orthMinusLeviOb_of_lastBlock
    (hlast : ∀ (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
      (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0), 4 ≤ n → LastBlockEquiv n hirr) :
    OrthMinusLeviOb := by
  intro n f F _ _ _ b c hirr hadm hcard Y _ π hker I hI
  exact leviOb_spinMinus hirr hadm.2.2 (hlast n hirr hadm.2.2) π hker I

end Fam

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
