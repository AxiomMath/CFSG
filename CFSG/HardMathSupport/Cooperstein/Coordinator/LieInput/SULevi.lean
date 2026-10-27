module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SUBlocks
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SUModel

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.AGLEmbeddingD2.ParabLevi CFSG.AGLEmbeddingD2.SquareLinear CFSG.AGLEmbedding.LeviBlock
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.Open CFSG.AGLEmbedding

section Equivs

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ}

@[expose] noncomputable def GAu_equiv (S : Finset (Fin (n / 2))) :
    ↥(GAu hF S) ≃* Matrix.SpecialLinearGroup (Fin S.card) F :=
  ((MonoidHom.ofInjective (levSU_injective (σ := unitaryInvolution F 2 f) (aIdx_injective S)
    (aIdx_disj S) (unitaryInvolution_involutive hF))).symm).trans
    (slReindexEquiv (Finset.equivFin S))

@[expose] noncomputable def GEu_equiv (S : Finset (Fin (n / 2))) :
    ↥(GEu hF S) ≃* SU (unitaryInvolution F 2 f) (ePos S).card :=
  (MonoidHom.ofInjective (suEmbed_injective (unitaryInvolution F 2 f) (eTau_injective S)
    (eTau_rev S))).symm

end Equivs

section Decomp

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ} {I : Set (Fin (n / 2))}

theorem block_decomp_su {Y : Type} [Group Y]
    (π : SU (unitaryInvolution F 2 f) n →* Y)
    (hker : ∀ z ∈ π.ker, z ∈ Subgroup.center (SU (unitaryInvolution F 2 f) n))
    {B : Finset (Fin (n / 2 + 1))} {p : Fin (n / 2 + 1)} (hB : B = blkSet I p)
    (hne : (nodesOf B).Nonempty)
    (hT : (⨆ k, levelTorus (unitaryInvolution F 2 f) k) ≤
      Subgroup.normalizer (GbU hF B : Set (SU (unitaryInvolution F 2 f) n))) :
    ∃ E C : Subgroup (SU (unitaryInvolution F 2 f) n), E ≤ GbU hF B ∧ C ≤ GbU hF B ∧
      GbU hF B ≤ E ⊔ C ∧ Group.IsSolvable ↥E ∧
      E ≤ Subgroup.normalizer (C : Set (SU (unitaryInvolution F 2 f) n)) ∧
      (⨆ k, levelTorus (unitaryInvolution F 2 f) k) ≤
        Subgroup.normalizer (E : Set (SU (unitaryInvolution F 2 f) n)) ∧
      (⨆ k, levelTorus (unitaryInvolution F 2 f) k) ≤
        Subgroup.normalizer (C : Set (SU (unitaryInvolution F 2 f) n)) ∧
      (C ≠ ⊥ → CFSG.IsQuasisimple ↥(C.map π) ∧
        IsClassicalTwoOrG2 (↥(C.map π) ⧸ Subgroup.center ↥(C.map π))) := by
  obtain ⟨i, hi⟩ := hne
  have hf1 : 1 ≤ f := one_le_f hF
  have h4F : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left (by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1) 2
  by_cases hl : Fin.last (n / 2) ∈ B
  · have hGb : GbU hF B = GEu hF (coordsOf B) := by simp [GbU, hl]
    rw [hGb] at hT ⊢
    have hk1 : 1 ≤ (coordsOf B).card := Finset.card_pos.mpr ⟨i, mem_coordsOf.mpr hi.1⟩
    obtain ⟨N, hN, ⟨e⟩⟩ : ∃ N, N = (ePos (coordsOf B)).card ∧
        Nonempty (↥(GEu hF (coordsOf B)) ≃* SU (unitaryInvolution F 2 f) N) :=
      ⟨_, rfl, ⟨GEu_equiv hF _⟩⟩
    have hNc : N = 2 * (coordsOf B).card + (if Even n then 0 else 1) := hN.trans (ePos_card _)
    have hN2 : 2 ≤ N := by split_ifs at hNc <;> omega
    rcases (by omega : N = 2 ∨ N = 3 ∨ 4 ≤ N) with h2 | h3 | h4
    · subst h2
      rcases (by omega : f = 1 ∨ 2 ≤ f) with hf | hf
      · have hs := su_two_solvable hF hf
        exact decomp_so π _ _ hT (@Group.isSolvable_of_isSolvable_injective _ _ _ _
          e.toMonoidHom e.injective hs)
      · exact decomp_ns π _ _ hT (chev_map_of_central_kernel π hker e.symm (su_two_chev hF hf))
    · subst h3
      rcases (by omega : f = 1 ∨ 2 ≤ f) with hf | hf
      · have hs := su_three_solvable hF hf
        exact decomp_so π _ _ hT (@Group.isSolvable_of_isSolvable_injective _ _ _ _
          e.toMonoidHom e.injective hs)
      · refine decomp_ns π _ _ hT (chev_map_of_central_kernel π hker e.symm
          (isChevComponent_su hF le_rfl ?_))
        intro h
        have h2 : 2 ^ f = 2 ^ 1 := by simpa using congrArg Prod.snd h
        have := Nat.pow_right_injective le_rfl h2
        omega
    · refine decomp_ns π _ _ hT (chev_map_of_central_kernel π hker e.symm
        (isChevComponent_su hF (by omega) ?_))
      intro h
      have := congrArg Prod.fst h
      simp only at this
      omega
  · have hGb : GbU hF B = GAu hF (coordsOf B) := by simp [GbU, hl]
    rw [hGb] at hT ⊢
    have hilt : i.val < n / 2 := i.isLt
    have hs : i.val + 1 < n / 2 := by
      by_contra h
      apply hl
      have : i.succ = Fin.last (n / 2) := Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
      rw [← this]
      exact hi.2
    have hsucc : (⟨i.val + 1, hs⟩ : Fin (n / 2)) ∈ coordsOf B := by
      have : (⟨i.val + 1, hs⟩ : Fin (n / 2)).castSucc = i.succ := Fin.ext (by simp)
      rw [mem_coordsOf, this]; exact hi.2
    have hk2 : 2 ≤ (coordsOf B).card := by
      have := Finset.one_lt_card.mpr ⟨i, mem_coordsOf.mpr hi.1, _, hsucc,
        fun h => by have := congrArg Fin.val h; simp at this⟩
      omega
    have hk : 3 ≤ (coordsOf B).card ∨ ((coordsOf B).card = 2 ∧ 4 ≤ Nat.card F) := by
      rcases (by omega : (coordsOf B).card = 2 ∨ 3 ≤ (coordsOf B).card) with h2 | h3
      · exact Or.inr ⟨h2, h4F⟩
      · exact Or.inl h3
    exact decomp_ns π _ _ hT (chev_map_of_central_kernel π hker (GAu_equiv hF _).symm
      (isChevComponent_sl hk))

end Decomp

section Main

open CFSG.LieType.RootSystem

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ}

theorem leviM_mono_of_subset {K : Type} [Group K] {D : UniversalRootDatum K} {J J' : Set (Fin D.rank)}
    (h : J ⊆ J') : leviM D J ≤ leviM D J' :=
  iSup₂_le fun i hi => rankOne_le_leviM (h hi)

theorem leviOb_su {Y : Type} [Group Y]
    (π : SU (unitaryInvolution F 2 f) n →* Y)
    (hker : ∀ z ∈ π.ker, z ∈ Subgroup.center (SU (unitaryInvolution F 2 f) n))
    (I : Set (Fin (rootDatum hF n).rank)) (hI : I ≠ Set.univ) :
    LeviOb (rootDatum hF n) (levelTorus (unitaryInvolution F 2 f)) π I := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ := unitaryInvolution_involutive (K := F) (p := 2) (f := f) hF
  obtain ⟨j0, hj0⟩ : ∃ j : Fin (rootDatum hF n).rank, j ∉ I := by
    by_contra h
    push Not at h
    exact hI (Set.eq_univ_of_forall h)
  have hjlt : j0.val < n / 2 := j0.isLt
  have hn : 2 ≤ n := by omega
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hct := isCTGroupDatum hF n hn ζ hζ
  have hext := steinbergExtras hF n hn ζ hζ
  let I' : Set (Fin (n / 2)) := I
  let blocks : Finset (Finset (Fin (n / 2 + 1))) :=
    (Finset.univ.image (blkSet I')).filter fun B => (nodesOf B).Nonempty
  have hblocks : ∀ b : ↥blocks, ∃ p, b.1 = blkSet I' p ∧ (nodesOf b.1).Nonempty := by
    intro b
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp b.2
    obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hb1
    exact ⟨p, hp.symm, hb2⟩
  have hTn : ∀ b : ↥blocks, (⨆ k, levelTorus (unitaryInvolution F 2 f) k) ≤
      Subgroup.normalizer (GbU hF b.1 : Set (SU (unitaryInvolution F 2 f) n)) := by
    intro b
    obtain ⟨p, hp, hne⟩ := hblocks b
    rw [GbU_eq hF hn hp hne]
    exact torus_le_normalizer_leviM (D := rootDatum hF n)
      (H := levelTorus (unitaryInvolution F 2 f)) (n := levelWeyl hσ ζ) (I := nodesOf b.1) hct
  have hdec : ∀ b : ↥blocks, ∃ E C : Subgroup (SU (unitaryInvolution F 2 f) n),
      E ≤ GbU hF b.1 ∧ C ≤ GbU hF b.1 ∧ GbU hF b.1 ≤ E ⊔ C ∧ Group.IsSolvable ↥E ∧
      E ≤ Subgroup.normalizer (C : Set (SU (unitaryInvolution F 2 f) n)) ∧
      (⨆ k, levelTorus (unitaryInvolution F 2 f) k) ≤
        Subgroup.normalizer (E : Set (SU (unitaryInvolution F 2 f) n)) ∧
      (⨆ k, levelTorus (unitaryInvolution F 2 f) k) ≤
        Subgroup.normalizer (C : Set (SU (unitaryInvolution F 2 f) n)) ∧
      (C ≠ ⊥ → CFSG.IsQuasisimple ↥(C.map π) ∧
        IsClassicalTwoOrG2 (↥(C.map π) ⧸ Subgroup.center ↥(C.map π))) := by
    intro b
    obtain ⟨p, hp, hne⟩ := hblocks b
    exact block_decomp_su hF π hker hp hne (hTn b)
  choose E C hEG hCG hGEC hEs hEC hTE hTC hCq using hdec
  refine leviOb_of_blocks (rootDatum hF n) (levelTorus (unitaryInvolution F 2 f)) π I
    (fun b : ↥blocks => GbU hF b.1) C E
    (Group.isSolvable_of_comm fun a b => (isMulCommutative_torus hext).is_comm.comm a b) ?_ ?_
    hEG hCG hGEC ?_ hEs hEC hTE hTC hCq
  · intro b
    obtain ⟨p, hp, hne⟩ := hblocks b
    rw [GbU_eq hF hn hp hne]
    exact leviM_mono_of_subset (D := rootDatum hF n) (by
      intro k hk
      have := nodesOf_subset (I := I') p
      rw [← hp] at this
      exact this hk)
  · refine iSup₂_le fun (i : Fin (rootDatum hF n).rank) hi => ?_
    let i' : Fin (n / 2) := i
    have hmem : blkSet I' i'.castSucc ∈ blocks :=
      Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩,
        ⟨i', mem_nodesOf_of_mem hi⟩⟩
    have hG := GbU_eq hF hn (B := blkSet I' i'.castSucc) rfl ⟨i', mem_nodesOf_of_mem hi⟩
    calc rankOne (rootDatum hF n).rootGroup i ≤
          leviM (rootDatum hF n) (nodesOf (blkSet I' i'.castSucc)) :=
          rankOne_le_leviM (mem_nodesOf_of_mem hi)
      _ = GbU hF (blkSet I' i'.castSucc) := hG.symm
      _ ≤ _ := le_iSup (fun b : ↥blocks => GbU hF b.1) ⟨_, hmem⟩
  · intro b b' hbb'
    obtain ⟨p, hp, -⟩ := hblocks b
    obtain ⟨q, hq, -⟩ := hblocks b'
    have : blkSet I' p ≠ blkSet I' q := fun h => hbb' (Subtype.ext (by rw [hp, hq, h]))
    rw [hp, hq]
    exact GbU_commute hF this

end Main

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
