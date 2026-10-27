module

public import CFSG.Certificates.Kernel.He7222.ChainPRep
public import CFSG.Certificates.Kernel.OrbRow.CentLGrp

public section

namespace CFSG.KC.HeChain

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.OrbRow CFSG.KS.Raw.Orb CFSG.KS.PF

variable {n w : ℕ}

theorem chain_prep_le (hn0 : 0 < n) (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (L : ℕ)
    (Gs : ℕ → List ℕ) (B : ℕ → ℕ) (R T Ref Nn : ℕ → List ℕ) (hB : ∀ i < L, B i < n)
    (htr : ∀ i < L, treeK n w (mask w) (pidn n w) (Gs i) (B i) (R i) (T i) = true)
    (hsch : ∀ i, i + 1 < L →
      schK n w (mask w) (Gs i) (B i) (R i) (T i) (Ref i) (Nn i) (Gs (i + 1)) = true)
    (P : Subgroup (Equiv.Perm (Fin n))) [Finite P]
    (h0 : ∀ q < (Gs 0).length, ∃ g ∈ P, PRep n w ((Gs 0).getD q 0) g)
    (hle : Nat.card P ≤ ∏ i ∈ Finset.range L, (T i).length) :
    Nat.card P = ∏ i ∈ Finset.range L, (T i).length ∧
    (∀ i < L, ∀ j < (T i).length, recP n w ((T i).getD j 0) ∈ P ∧
      PRep n w ((T i).getD j 0) (recP n w ((T i).getD j 0)) ∧
      ∀ t < i, recP n w ((T i).getD j 0) (baseF hn0 B t) = baseF hn0 B t) ∧
    ∀ g ∈ P, ∃ f : ℕ → ℕ, (∀ i < L, f i < (T i).length) ∧
      g = ((List.range L).map fun i => recP n w ((T i).getD (f i) 0)).prod := by
  have hn32 : n < 2 ^ 32 := by omega
  let b := baseF hn0 B
  have hbv : ∀ i (hi : i < L), b i = ⟨B i, hB i hi⟩ := fun i hi => by
    change baseF hn0 B i = _
    rw [baseF, dif_pos (hB i hi)]
  let gset : ℕ → Set (Equiv.Perm (Fin n)) := fun i =>
    {g | ∃ q < (Gs i).length, PRep n w ((Gs i).getD q 0) g}
  let G : ℕ → Subgroup (Equiv.Perm (Fin n)) := fun i =>
    if i < L then Subgroup.closure (gset i) else ⊥
  have hGc : ∀ i < L, G i = Subgroup.closure (gset i) := fun i hi => if_pos hi
  have hgen : ∀ i < L, ∀ q < (Gs i).length, ∃ g ∈ stabB P b i, PRep n w ((Gs i).getD q 0) g := by
    intro i
    induction i with
    | zero =>
      intro _ q hq
      obtain ⟨g, hg, hr⟩ := h0 q hq
      exact ⟨g, ⟨hg, fun t ht => absurd ht (Nat.not_lt_zero t)⟩, hr⟩
    | succ i ih =>
      intro hi q hq
      have hiL : i < L := by omega
      obtain ⟨hTR, -, -⟩ := treeK_sound (htr i hiL)
      have hT := tree_prep hn hw (htr i hiL) (stabB P b i) (ih hiL)
      obtain ⟨g, hg, hr, hfx⟩ :=
        sch_prep hn32 (hB i hiL) (hsch i hi) hTR (stabB P b i) (ih hiL) hT q hq
      refine ⟨g, ⟨hg.1, fun t ht => ?_⟩, hr⟩
      rcases Nat.lt_or_ge t i with hti | hti
      · exact hg.2 t hti
      · have : t = i := by omega
        subst this
        rw [hbv t hiL]
        exact hfx
  have hmemG : ∀ i < L, ∀ q < (Gs i).length, ∃ g ∈ G i, PRep n w ((Gs i).getD q 0) g := by
    intro i hi q hq
    obtain ⟨g, -, hr⟩ := hgen i hi q hq
    rw [hGc i hi]
    exact ⟨g, Subgroup.subset_closure ⟨q, hq, hr⟩, hr⟩
  have hGS : ∀ i < L, G i ≤ stabB P b i := by
    intro i hi
    rw [hGc i hi, Subgroup.closure_le]
    rintro g ⟨q, hq, hr⟩
    obtain ⟨g', hg', hr'⟩ := hgen i hi q hq
    rw [prep_unique hr hr']
    exact hg'
  have hGP : ∀ i ≤ L, G i ≤ P := by
    intro i hi
    rcases Nat.lt_or_ge i L with hiL | hiL
    · exact fun g hg => ((hGS i hiL) hg).1
    · have : G i = ⊥ := if_neg (by omega)
      rw [this]
      exact bot_le
  have hfix : ∀ i ≤ L, ∀ g ∈ G i, ∀ t < i, g (b t) = b t := by
    intro i hi g hg t ht
    rcases Nat.lt_or_ge i L with hiL | hiL
    · exact ((hGS i hiL) hg).2 t ht
    · have : G i = ⊥ := if_neg (by omega)
      rw [this, Subgroup.mem_bot] at hg
      rw [hg]
      rfl
  have hdec : ∀ i < L, G (i + 1) ≤ G i := by
    intro i hi
    rcases Nat.lt_or_ge (i + 1) L with hi1 | hi1
    · rw [hGc (i + 1) hi1, Subgroup.closure_le]
      rintro g ⟨q, hq, hr⟩
      obtain ⟨hTR, -, -⟩ := treeK_sound (htr i hi)
      have hT := tree_prep hn hw (htr i hi) (G i) (hmemG i hi)
      obtain ⟨g', hg', hr', -⟩ := sch_prep hn32 (hB i hi) (hsch i hi1) hTR (G i) (hmemG i hi) hT q hq
      rw [prep_unique hr hr']
      exact hg'
    · have : G (i + 1) = ⊥ := if_neg (by omega)
      rw [this]
      exact bot_le
  have hTm : ∀ i < L, ∀ j < (T i).length,
      recP n w ((T i).getD j 0) ∈ G i ∧ PRep n w ((T i).getD j 0) (recP n w ((T i).getD j 0)) := by
    intro i hi j hj
    obtain ⟨t, ht, hr⟩ := tree_prep hn hw (htr i hi) (G i) (hmemG i hi) j hj
    rw [recP_eq hr]
    exact ⟨ht, hr⟩
  have hpg : ∀ i < L, ∀ j < (T i).length,
      pg w (mask w) ((T i).getD j 0) (B i) = ptR (mask w) (R i) j := by
    intro i hi j hj
    obtain ⟨-, hat, -⟩ := treeK_sound (htr i hi)
    obtain ⟨h0', h1'⟩ := hat j hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · rw [(h0' rfl).2, (h0' rfl).1]
      exact pg_pidn hn hw (hB i hi)
    · exact (h1' hpos).1
  have hpts : ∀ i < L, ∀ j < (T i).length, ∀ j' < (T i).length,
      recP n w ((T i).getD j 0) (b i) = recP n w ((T i).getD j' 0) (b i) → j = j' := by
    intro i hi j hj j' hj' he
    obtain ⟨-, -, hdis⟩ := treeK_sound (htr i hi)
    have e := congrArg Fin.val he
    rw [← (hTm i hi j hj).2, ← (hTm i hi j' hj').2, hbv i hi] at e
    simp only at e
    rw [hpg i hi j hj, hpg i hi j' hj'] at e
    rcases Nat.lt_trichotomy j j' with hlt | heq | hgt
    · exact absurd e (hdis j' hj' j hlt)
    · exact heq
    · exact absurd e.symm (hdis j hj j' hgt)
  have horb : ∀ i < L, ∃ s : Finset (Fin n), s.card = (T i).length ∧
      ∀ x ∈ s, ∃ g ∈ G i, g (b i) = x := fun i hi =>
    tight_orbit b G (fun i => (T i).length) (fun i j => recP n w ((T i).getD j 0))
      (fun j hj => (hTm i hi j hj).1) (hpts i hi)
  have hlow := CFSG.KC.OrbRow.CentLGrp.prod_le_card_chain b L G (fun i => (T i).length) hfix hdec
    horb 0 (Nat.zero_le _)
  have hG0 : Nat.card (G 0) ≤ Nat.card P := Subgroup.card_le_of_le (hGP 0 (Nat.zero_le _))
  have hcard : Nat.card P = ∏ i ∈ Finset.range L, (T i).length := by
    refine le_antisymm hle ?_
    rw [Finset.range_eq_Ico]
    exact hlow.trans hG0
  have hfac := tight_factor P b L G (fun i => (T i).length) hGP hfix hdec
    (fun i j => recP n w ((T i).getD j 0)) (fun i hi j hj => (hTm i hi j hj).1) hpts hcard
  exact ⟨hcard, fun i hi j hj => ⟨hGP i hi.le (hTm i hi j hj).1, (hTm i hi j hj).2,
    hfix i hi.le _ (hTm i hi j hj).1⟩, hfac⟩

end CFSG.KC.HeChain

end
