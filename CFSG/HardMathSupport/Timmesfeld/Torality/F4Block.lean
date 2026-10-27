module

public import CFSG.HardMathSupport.Timmesfeld.Torality.A2Block
public import CFSG.HardMathSupport.Timmesfeld.Torality.F4A2Table
public import CFSG.RankThree.PartOne.KF4.LongA2Frame
public import CFSG.RankThree.PartOne.KF4.ShortA2Frame
public import CFSG.RankThree.Chevalley.SteinbergCEF4LatticeTools
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralBlocks

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.F4Weyl CFSG.RankThree.E6 CFSG.RankThree.PartOne.KF4
  CFSG.HardMathSupport.Timmesfeld.CrossChar

@[expose] def f4vec (l : List ℤ) : Fin Tag.F4.rank → ℤ := fun i => l.getD i 0

@[expose] def f4rootL (k : ℕ) : List ℤ := Tag.F4.artifactRoots.getD k []

@[expose] def f4entryPair (e : ℕ) : (Fin Tag.F4.rank → ℤ) × (Fin Tag.F4.rank → ℤ) :=
  (f4vec (f4rootL (e % 48)), f4vec (f4rootL (e / 48 % 48)))

@[expose] def f4entryWord (e : ℕ) : List (Fin 4) := decodeF4Word 12 (e / 2304)

theorem f4LongTable_sound : ∀ e ∈ f4LongTable,
    f4WordAct (f4entryWord e) (Pi.single (CFSG.RankThree.PartOne.KF4.f4Index 0) 1) = (f4entryPair e).1 ∧
    f4WordAct (f4entryWord e) (Pi.single (CFSG.RankThree.PartOne.KF4.f4Index 1) 1) = (f4entryPair e).2 := by
  decide +kernel

theorem f4ShortTable_sound : ∀ e ∈ f4ShortTable,
    f4WordAct (f4entryWord e) (-Pi.single (CFSG.RankThree.PartOne.KF4.f4Index 2) 1) = (f4entryPair e).1 ∧
    f4WordAct (f4entryWord e) (-Pi.single (CFSG.RankThree.PartOne.KF4.f4Index 3) 1) = (f4entryPair e).2 := by
  decide +kernel

theorem f4Table_complete : ∀ ia : Fin 48, ∀ ib : Fin 48,
    iform (τ := Tag.F4) (f4vec (f4rootL ib)) (f4vec (f4rootL ib)) =
        iform (τ := Tag.F4) (f4vec (f4rootL ia)) (f4vec (f4rootL ia)) →
      2 * iform (τ := Tag.F4) (f4vec (f4rootL ia)) (f4vec (f4rootL ib)) =
        -iform (τ := Tag.F4) (f4vec (f4rootL ia)) (f4vec (f4rootL ia)) →
      (∃ e ∈ f4LongTable, e % 48 = ia ∧ e / 48 % 48 = ib) ∨
        (∃ e ∈ f4ShortTable, e % 48 = ia ∧ e / 48 % 48 = ib) := by
  decide +kernel

theorem f4vec_ofFn (α : Fin Tag.F4.rank → ℤ) : f4vec (List.ofFn α) = α := by
  funext i
  simp [f4vec]

section


theorem f4_a2Pair_orbit {α β : Fin Tag.F4.rank → ℤ} (h : IsA2Pair α β) :
    ∃ v : WeylGroup Tag.F4,
      (v • Pi.single (CFSG.RankThree.PartOne.KF4.f4Index 0) 1 = α ∧
        v • Pi.single (CFSG.RankThree.PartOne.KF4.f4Index 1) 1 = β) ∨
      (v • (-Pi.single (CFSG.RankThree.PartOne.KF4.f4Index 2) 1) = α ∧
        v • (-Pi.single (CFSG.RankThree.PartOne.KF4.f4Index 3) 1) = β) := by
  have hmem : ∀ γ : Fin Tag.F4.rank → ℤ, IsRoot Tag.F4 γ → ∃ k : Fin 48,
      f4vec (f4rootL k) = γ := by
    intro γ hγ
    have h1 := (isRoot_iff_mem_artifactRoots (τ := Tag.F4)).1 hγ
    obtain ⟨k, hk, hkγ⟩ := List.mem_iff_getElem.1 h1
    have hlen : Tag.F4.artifactRoots.length = 48 := Tag.length_artifactRoots Tag.F4
    refine ⟨⟨k, by omega⟩, ?_⟩
    rw [f4rootL, List.getD_eq_getElem _ _ hk, hkγ, f4vec_ofFn]
  obtain ⟨ia, hia⟩ := hmem α h.isRoot_fst
  obtain ⟨ib, hib⟩ := hmem β h.isRoot_snd
  have hc := f4Table_complete ia ib (by rw [hia, hib]; exact h.iform_snd)
    (by rw [hia, hib]; exact h.two_iform)
  rcases hc with ⟨e, he, h1, h2⟩ | ⟨e, he, h1, h2⟩
  · obtain ⟨s1, s2⟩ := f4LongTable_sound e he
    refine ⟨f4WordProd (f4entryWord e), Or.inl ⟨?_, ?_⟩⟩
    · rw [f4WordProd_smul, s1, f4entryPair, h1, hia]
    · rw [f4WordProd_smul, s2, f4entryPair, h2, hib]
  · obtain ⟨s1, s2⟩ := f4ShortTable_sound e he
    refine ⟨f4WordProd (f4entryWord e), Or.inr ⟨?_, ?_⟩⟩
    · rw [f4WordProd_smul, s1, f4entryPair, h1, hia]
    · rw [f4WordProd_smul, s2, f4entryPair, h2, hib]

theorem a2BlockToral_F4 : A2BlockToral Tag.F4 := by
  intro L _ _ hL α β hpair
  obtain ⟨v, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := f4_a2Pair_orbit hpair
  · have hfr := (f4Long_frame (L := L)).transport v
    have key := a2BlockAt_of_frame hL hfr
    have e1 : v • chainRoot f4chainLong 0 1 = α := by rw [(f4chainLong_values).1]; exact h1
    have e2 : v • chainRoot f4chainLong 1 2 = β := by rw [(f4chainLong_values).2.1]; exact h2
    simp only [e1, e2] at key
    exact key
  · have hfr := (f4Short_frame (L := L)).transport v
    have key := a2BlockAt_of_frame hL hfr
    have e1 : v • f4ShortSigma 0 1 = α := by rw [(f4ShortSigma_values).2.2.1]; exact h1
    have e2 : v • f4ShortSigma 1 2 = β := by rw [(f4ShortSigma_values).2.2.2]; exact h2
    simp only [e1, e2] at key
    exact key

end

end CFSG.HardMathSupport.Timmesfeld.Torality
