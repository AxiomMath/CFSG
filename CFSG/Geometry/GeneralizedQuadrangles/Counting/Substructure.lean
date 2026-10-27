module

public import CFSG.Geometry.GeneralizedQuadrangles.Basic

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u} {Γ : SimpleGraph V}

theorem ncard_points_eq_of_closed [Fintype V] [DecidableRel Γ.Adj]
    (hP : IsGeneralizedPolygon Γ 4) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {F B : Set V} {s' : ℕ}
    (hF : ∀ x ∈ F, c x = 0) (hB : ∀ L ∈ B, c L = 1)
    (hFB : ∀ x ∈ F, ∀ L, Γ.Adj x L → L ∈ B)
    (hBF : ∀ L ∈ B, (Γ.neighborSet L ∩ F).ncard = s' + 1)
    (hBB : ∀ L ∈ B, ∀ M ∈ B, L ≠ M → ∀ x, Γ.Adj L x → Γ.Adj M x → x ∈ F)
    (hne : B.Nonempty) : F.ncard = (s' + 1) * (s' * t + 1) := by
  classical
  obtain ⟨N, hN⟩ := hne
  let Fs : Finset V := F.toFinset
  let Bs : Finset V := B.toFinset
  let BN : Finset V := Γ.neighborFinset N
  let Is : Finset V := Fs ∩ BN
  let Cs : Finset V := Bs.filter fun L => L ≠ N ∧ Γ.dist L N = 2
  let r : V → V → Prop := fun x L => Γ.Adj L x
  have hIs : Is.card = s' + 1 := by
    have hEq : Is = (F ∩ Γ.neighborSet N).toFinset := by
      ext z
      simp [Is, Fs, BN, mem_neighborFinset, Set.mem_toFinset]
    calc
      Is.card = (F ∩ Γ.neighborSet N).ncard := by
        rw [hEq]
        exact (Set.ncard_eq_toFinset_card' _).symm
      _ = (Γ.neighborSet N ∩ F).ncard := by rw [Set.inter_comm]
      _ = s' + 1 := hBF N hN
  have hCs : Cs.card = (s' + 1) * t := by
    have hCz : ∀ z ∈ Is, (Cs.bipartiteAbove r z).card = t := by
      intro z hz
      simp only [Is, Finset.mem_inter] at hz
      have hzF : z ∈ F := by simpa [Fs] using hz.1
      have hzN : Γ.Adj N z := by simpa [BN, mem_neighborFinset] using hz.2
      have hset : Cs.bipartiteAbove r z = (Γ.neighborFinset z).erase N := by
        ext L
        simp only [r, Finset.mem_bipartiteAbove, Finset.mem_erase, mem_neighborFinset]
        constructor
        · rintro ⟨hLCs, hzL⟩
          simp only [Cs, Finset.mem_filter] at hLCs
          exact ⟨hLCs.2.1, hzL.symm⟩
        · rintro ⟨hLne, hzL⟩
          refine ⟨?_, hzL.symm⟩
          simp only [Cs, Finset.mem_filter]
          refine ⟨?_, hLne, ?_⟩
          · simpa [Bs] using hFB z hzF L hzL
          · rw [SimpleGraph.dist_comm]
            exact dist_eq_two_of_adj_of_adj_of_ne hP hzN hzL hLne.symm
      rw [hset, Finset.card_erase_of_mem]
      · rw [card_neighborFinset_eq_degree, hdeg z, if_pos (hF z hzF)]
        omega
      · simpa [mem_neighborFinset] using hzN.symm
    have hCl : ∀ L ∈ Cs, (Is.bipartiteBelow r L).card = 1 := by
      intro L hL
      simp only [Cs, Finset.mem_filter] at hL
      obtain ⟨hLBs, hLne, hLdist⟩ := hL
      have hLB : L ∈ B := by simpa [Bs] using hLBs
      have hNLdist : Γ.dist N L = 2 := by rw [SimpleGraph.dist_comm]; exact hLdist
      let z := commonNeighbor hP hNLdist
      have hzN : Γ.Adj N z := commonNeighbor_adj_left hP hNLdist
      have hzL : Γ.Adj L z := commonNeighbor_adj_right hP hNLdist
      have hzF : z ∈ F := hBB N hN L hLB hLne.symm z hzN hzL
      have hzIs : z ∈ Is := by
        simp only [Is, Finset.mem_inter]
        exact ⟨by simpa [Fs] using hzF, by simpa [BN, mem_neighborFinset] using hzN⟩
      have hset : Is.bipartiteBelow r L = {z} := by
        ext w
        rw [Finset.mem_singleton]
        constructor
        · intro hw
          simp only [r, Finset.mem_bipartiteBelow] at hw
          obtain ⟨hwIs, hwL⟩ := hw
          simp only [Is, Finset.mem_inter] at hwIs
          have hwN : Γ.Adj N w := by simpa [BN, mem_neighborFinset] using hwIs.2
          exact ((existsUnique_commonNeighbor hP hNLdist).unique
            ⟨hzN, hzL⟩ ⟨hwN, hwL⟩).symm
        · intro hw
          rw [hw]
          simp only [Finset.mem_bipartiteBelow]
          exact ⟨hzIs, hzL⟩
      rw [hset, Finset.card_singleton]
    have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (r := r) (s := Is) (t := Cs)
    rw [Finset.sum_congr rfl hCz, Finset.sum_congr rfl hCl] at hdouble
    rw [Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, mul_one] at hdouble
    rw [hIs] at hdouble
    exact hdouble.symm
  have hCx : ∀ x ∈ Fs \ BN, (Cs.bipartiteAbove r x).card = 1 := by
    intro x hx
    obtain ⟨hxFs, hxBN⟩ := Finset.mem_sdiff.mp hx
    have hxF : x ∈ F := by simpa [Fs] using hxFs
    have hnotN : ¬ Γ.Adj N x := by simpa [BN, mem_neighborFinset] using hxBN
    have hnot : ¬ Γ.Adj x N := fun h => hnotN h.symm
    have hc : c x ≠ c N := by
      rw [hF x hxF, hB N hN]
      decide
    have hdist : Γ.dist x N = 3 :=
      dist_eq_three_of_not_adj_of_color_ne hP c hnot hc
    let z := proj hP hdist
    have hzN : Γ.Adj N z := proj_adj hP hdist
    have hxz : Γ.dist x z = 2 := proj_dist hP hdist
    let L := commonNeighbor hP hxz
    have hxL : Γ.Adj x L := commonNeighbor_adj_left hP hxz
    have hzL : Γ.Adj z L := commonNeighbor_adj_right hP hxz
    have hLB : L ∈ B := hFB x hxF L hxL
    have hLne : L ≠ N := by
      intro hLN
      exact hnot (by rwa [hLN] at hxL)
    have hLdist : Γ.dist L N = 2 := by
      rw [SimpleGraph.dist_comm]
      exact dist_eq_two_of_adj_of_adj_of_ne hP hzN hzL hLne.symm
    have hLCs : L ∈ Cs := by
      simp only [Cs, Finset.mem_filter]
      exact ⟨by simpa [Bs] using hLB, hLne, hLdist⟩
    have hset : Cs.bipartiteAbove r x = {L} := by
      ext M
      simp only [r, Finset.mem_bipartiteAbove, Finset.mem_singleton]
      constructor
      · rintro ⟨hMCs, hxM⟩
        simp only [Cs, Finset.mem_filter] at hMCs
        obtain ⟨hMBs, hMne, hMdist⟩ := hMCs
        have hMB : M ∈ B := by simpa [Bs] using hMBs
        have hNMdist : Γ.dist N M = 2 := by rw [SimpleGraph.dist_comm]; exact hMdist
        let zM := commonNeighbor hP hNMdist
        have hzMN : Γ.Adj N zM := commonNeighbor_adj_left hP hNMdist
        have hzMM : Γ.Adj M zM := commonNeighbor_adj_right hP hNMdist
        have hxne : x ≠ zM := by
          intro hxzM
          exact hnotN (hxzM.symm ▸ hzMN)
        have hxzm : Γ.dist x zM = 2 :=
          dist_eq_two_of_adj_of_adj_of_ne hP hxM.symm hzMM hxne
        have hzeq : z = zM :=
          (existsUnique_proj hP hdist).unique ⟨hzN, hxz⟩ ⟨hzMN, hxzm⟩
        have hMz : Γ.Adj M z := by
          rw [← hzeq] at hzMM
          exact hzMM
        exact (existsUnique_commonNeighbor hP hxz).unique
          ⟨hxM.symm, hMz.symm⟩ ⟨hxL, hzL⟩
      · rintro rfl
        exact ⟨hLCs, hxL.symm⟩
    rw [hset, Finset.card_singleton]
  have hFL : ∀ L ∈ Cs, ((Fs \ BN).bipartiteBelow r L).card = s' := by
    intro L hL
    simp only [Cs, Finset.mem_filter] at hL
    obtain ⟨hLBs, hLne, hLdist⟩ := hL
    have hLB : L ∈ B := by simpa [Bs] using hLBs
    have hNLdist : Γ.dist N L = 2 := by rw [SimpleGraph.dist_comm]; exact hLdist
    let z := commonNeighbor hP hNLdist
    have hzN : Γ.Adj N z := commonNeighbor_adj_left hP hNLdist
    have hzL : Γ.Adj L z := commonNeighbor_adj_right hP hNLdist
    have hzF : z ∈ F := hBB N hN L hLB hLne.symm z hzN hzL
    have hzBN : z ∈ BN := by simpa [BN, mem_neighborFinset] using hzN
    let A : Finset V := (Γ.neighborSet L ∩ F).toFinset
    have hzA : z ∈ A := by
      simp only [A, Set.mem_toFinset, Set.mem_inter_iff]
      exact ⟨hzL, hzF⟩
    have hAcard : A.card = s' + 1 := by
      change ((Γ.neighborSet L ∩ F).toFinset).card = s' + 1
      exact (Set.ncard_eq_toFinset_card' _).symm.trans (hBF L hLB)
    have hAuniq : ∀ w, w ∈ A → w ∈ BN → w = z := by
      intro w hwA hwBN
      simp only [A, Set.mem_toFinset, Set.mem_inter_iff] at hwA
      have hwN : Γ.Adj N w := by simpa [BN, mem_neighborFinset] using hwBN
      exact ((existsUnique_commonNeighbor hP hNLdist).unique
        ⟨hzN, hzL⟩ ⟨hwN, hwA.1⟩).symm
    have hAerased : A \ BN = A.erase z := by
      ext w
      simp only [Finset.mem_sdiff, Finset.mem_erase]
      constructor
      · rintro ⟨hwA, hwBN⟩
        exact ⟨fun hwz => hwBN (hwz ▸ hzBN), hwA⟩
      · rintro ⟨hwne, hwA⟩
        exact ⟨hwA, fun hwBN => hwne (hAuniq w hwA hwBN)⟩
    have hXeq : (Fs \ BN).bipartiteBelow r L = A \ BN := by
      ext w
      simp only [r, Finset.mem_bipartiteBelow, Finset.mem_sdiff, A, Set.mem_toFinset,
        Set.mem_inter_iff]
      constructor
      · rintro ⟨⟨hwFs, hwBN⟩, hwL⟩
        exact ⟨⟨hwL, by simpa [Fs] using hwFs⟩, hwBN⟩
      · rintro ⟨⟨hwL, hwF⟩, hwBN⟩
        exact ⟨⟨by simpa [Fs] using hwF, hwBN⟩, hwL⟩
    rw [hXeq, hAerased, Finset.card_erase_of_mem hzA, hAcard]
    omega
  have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := r) (s := Fs \ BN) (t := Cs)
  rw [Finset.sum_congr rfl hCx, Finset.sum_congr rfl hFL] at hdouble
  rw [Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, mul_one] at hdouble
  have hFoff : (Fs \ BN).card = Cs.card * s' := by simpa using hdouble
  have hsplit : Fs.card = Is.card + (Fs \ BN).card := by
    change Fs.card = (Fs ∩ BN).card + (Fs \ BN).card
    rw [add_comm]
    exact (Finset.card_sdiff_add_card_inter Fs BN).symm
  have hFcard : Fs.card = (s' + 1) * (s' * t + 1) := by
    rw [hsplit, hIs, hFoff, hCs]
    ring
  calc
    F.ncard = Fs.card := Set.ncard_eq_toFinset_card' F
    _ = (s' + 1) * (s' * t + 1) := hFcard

theorem ncard_lines_eq_of_closed [Fintype V] [DecidableRel Γ.Adj]
    (hP : IsGeneralizedPolygon Γ 4) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {F B : Set V} {s' : ℕ}
    (hF : ∀ x ∈ F, c x = 0) (hB : ∀ L ∈ B, c L = 1)
    (hFB : ∀ x ∈ F, ∀ L, Γ.Adj x L → L ∈ B)
    (hBF : ∀ L ∈ B, (Γ.neighborSet L ∩ F).ncard = s' + 1)
    (hBB : ∀ L ∈ B, ∀ M ∈ B, L ≠ M → ∀ x, Γ.Adj L x → Γ.Adj M x → x ∈ F)
    (hne : B.Nonempty) : B.ncard = (t + 1) * (s' * t + 1) := by
  classical
  let Fs : Finset V := F.toFinset
  let Bs : Finset V := B.toFinset
  have hFcard : F.ncard = (s' + 1) * (s' * t + 1) :=
    ncard_points_eq_of_closed hP c hdeg hF hB hFB hBF hBB hne
  have hAbove : ∀ x ∈ Fs, (Bs.bipartiteAbove Γ.Adj x).card = t + 1 := by
    intro x hx
    have hxF : x ∈ F := by simpa [Fs] using hx
    have hset : Bs.bipartiteAbove Γ.Adj x = Γ.neighborFinset x := by
      ext L
      simp only [Finset.mem_bipartiteAbove, mem_neighborFinset]
      constructor
      · rintro ⟨-, hxL⟩
        exact hxL
      · intro hxL
        exact ⟨by simpa [Bs] using hFB x hxF L hxL, hxL⟩
    rw [hset, card_neighborFinset_eq_degree, hdeg x, if_pos (hF x hxF)]
  have hBelow : ∀ L ∈ Bs, (Fs.bipartiteBelow Γ.Adj L).card = s' + 1 := by
    intro L hL
    have hLB : L ∈ B := by simpa [Bs] using hL
    have hset : Fs.bipartiteBelow Γ.Adj L = (Γ.neighborSet L ∩ F).toFinset := by
      ext x
      simp only [Finset.mem_bipartiteBelow, mem_neighborFinset, Set.mem_toFinset,
        Set.mem_inter_iff]
      constructor
      · rintro ⟨hxFs, hxL⟩
        exact ⟨hxL.symm, by simpa [Fs] using hxFs⟩
      · rintro ⟨hxL, hxF⟩
        exact ⟨by simpa [Fs] using hxF, hxL.symm⟩
    rw [hset]
    exact (Set.ncard_eq_toFinset_card' _).symm.trans (hBF L hLB)
  have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := Γ.Adj) (s := Fs) (t := Bs)
  rw [Finset.sum_congr rfl hAbove, Finset.sum_congr rfl hBelow] at hdouble
  rw [Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul] at hdouble
  have hFscard : Fs.card = (s' + 1) * (s' * t + 1) := by
    rw [show Fs.card = F.ncard from (Set.ncard_eq_toFinset_card' F).symm]
    exact hFcard
  have hcancel : (s' + 1) * ((t + 1) * (s' * t + 1)) = (s' + 1) * Bs.card := by
    calc
      (s' + 1) * ((t + 1) * (s' * t + 1)) = Fs.card * (t + 1) := by
        rw [hFscard]
        ring
      _ = Bs.card * (s' + 1) := hdouble
      _ = (s' + 1) * Bs.card := by rw [Nat.mul_comm]
  have hBscard : Bs.card = (t + 1) * (s' * t + 1) :=
    (Nat.mul_left_cancel (Nat.succ_pos s') hcancel).symm
  calc
    B.ncard = Bs.card := Set.ncard_eq_toFinset_card' B
    _ = (t + 1) * (s' * t + 1) := hBscard

theorem eq_or_mul_le_of_closed [Fintype V] [DecidableRel Γ.Adj]
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {F B : Set V} {s' : ℕ}
    (hF : ∀ x ∈ F, c x = 0) (hB : ∀ L ∈ B, c L = 1)
    (hFB : ∀ x ∈ F, ∀ L, Γ.Adj x L → L ∈ B)
    (hBF : ∀ L ∈ B, (Γ.neighborSet L ∩ F).ncard = s' + 1)
    (hBB : ∀ L ∈ B, ∀ M ∈ B, L ≠ M → ∀ x, Γ.Adj L x → Γ.Adj M x → x ∈ F)
    (hne : B.Nonempty) : s' = s ∨ s' * t ≤ s := by
  classical
  have hFcard : F.ncard = (s' + 1) * (s' * t + 1) :=
    ncard_points_eq_of_closed hP c hdeg hF hB hFB hBF hBB hne
  have hBcard : B.ncard = (t + 1) * (s' * t + 1) :=
    ncard_lines_eq_of_closed hP c hdeg hF hB hFB hBF hBB hne
  obtain ⟨N, hN⟩ := hne
  have hs'le : s' ≤ s := by
    have hle : s' + 1 ≤ (Γ.neighborSet N).ncard := by
      rw [← hBF N hN]
      exact Set.ncard_le_ncard Set.inter_subset_left
    have hdegN : Γ.degree N = s + 1 := by
      rw [hdeg N, if_neg (by rw [hB N hN]; decide)]
    rw [SimpleGraph.ncard_neighborSet, hdegN] at hle
    omega
  obtain ⟨x, hxNF⟩ : (Γ.neighborSet N ∩ F).Nonempty := by
    have hpos : 0 < (Γ.neighborSet N ∩ F).ncard := by
      rw [hBF N hN]
      omega
    exact (Set.ncard_pos (s := Γ.neighborSet N ∩ F)).mp hpos
  have hxF : x ∈ F := hxNF.2
  have ht2 : 2 ≤ t := by
    have hxdeg : Γ.degree x = t + 1 := by
      rw [hdeg x, if_pos (hF x hxF)]
    have := hT x
    omega
  let Fs : Finset V := F.toFinset
  let Ds : Finset V := B.toFinset.biUnion fun L => Γ.neighborFinset L \ Fs
  have hLcard : ∀ L ∈ B.toFinset, (Γ.neighborFinset L \ Fs).card = s - s' := by
    intro L hL
    have hLB : L ∈ B := by simpa using hL
    have hdegL : Γ.degree L = s + 1 := by
      rw [hdeg L, if_neg (by rw [hB L hLB]; decide)]
    have hinter : (Fs ∩ Γ.neighborFinset L).card = s' + 1 := by
      have hEq : Fs ∩ Γ.neighborFinset L = (F ∩ Γ.neighborSet L).toFinset := by
        ext y
        simp [Fs, mem_neighborFinset, Set.mem_toFinset, and_comm]
      calc
        (Fs ∩ Γ.neighborFinset L).card = (F ∩ Γ.neighborSet L).ncard := by
          rw [hEq]
          exact (Set.ncard_eq_toFinset_card' _).symm
        _ = (Γ.neighborSet L ∩ F).ncard := by rw [Set.inter_comm]
        _ = s' + 1 := hBF L hLB
    rw [Finset.card_sdiff, card_neighborFinset_eq_degree, hdegL, hinter]
    omega
  have hDcard : Ds.card = B.ncard * (s - s') := by
    have hdisj : (B.toFinset : Set V).PairwiseDisjoint
        (fun L => Γ.neighborFinset L \ Fs) := by
      intro L hL M hM hLM
      rw [Function.onFun, Finset.disjoint_left]
      intro y hyL hyM
      obtain ⟨hyL', hyF⟩ := Finset.mem_sdiff.mp hyL
      obtain ⟨hyM', -⟩ := Finset.mem_sdiff.mp hyM
      have hLB : L ∈ B := by simpa using hL
      have hMB : M ∈ B := by simpa using hM
      have hyLadj : Γ.Adj L y := by simpa [mem_neighborFinset] using hyL'
      have hyMadj : Γ.Adj M y := by simpa [mem_neighborFinset] using hyM'
      exact hyF (by simpa [Fs] using hBB L hLB M hMB hLM y hyLadj hyMadj)
    change (B.toFinset.biUnion fun L => Γ.neighborFinset L \ Fs).card =
      B.ncard * (s - s')
    rw [Finset.card_biUnion hdisj]
    rw [Finset.sum_congr rfl hLcard, Finset.sum_const, smul_eq_mul]
    rw [← Set.ncard_eq_toFinset_card']
  have hFsub : Fs ⊆ pointFinset c := by
    intro y hy
    rw [mem_pointFinset]
    exact hF y (by simpa [Fs] using hy)
  have hDsub : Ds ⊆ pointFinset c := by
    intro y hy
    simp only [Ds, Finset.mem_biUnion] at hy
    obtain ⟨L, hL, hyL⟩ := hy
    obtain ⟨hyL', -⟩ := Finset.mem_sdiff.mp hyL
    have hLB : L ∈ B := by simpa using hL
    have hyLadj : Γ.Adj L y := by simpa [mem_neighborFinset] using hyL'
    have hne : c L ≠ c y := c.valid hyLadj
    rw [mem_pointFinset]
    have hcL : c L = 1 := hB L hLB
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c y) with h | h
    · exact h
    · exact absurd (hcL.trans h.symm) hne
  have hdisjFD : Disjoint Fs Ds := by
    rw [Finset.disjoint_left]
    intro y hyF hyD
    simp only [Ds, Finset.mem_biUnion] at hyD
    obtain ⟨L, -, hyL⟩ := hyD
    exact (Finset.mem_sdiff.mp hyL).2 hyF
  have hsubUnion : Fs ∪ Ds ⊆ pointFinset c := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact hFsub hy
    · exact hDsub hy
  have hle : F.ncard + B.ncard * (s - s') ≤ (s + 1) * (s * t + 1) := by
    calc
      F.ncard + B.ncard * (s - s') = Fs.card + Ds.card := by
        rw [hDcard, show Fs.card = F.ncard from (Set.ncard_eq_toFinset_card' F).symm]
      _ = (Fs ∪ Ds).card := (Finset.card_union_of_disjoint hdisjFD).symm
      _ ≤ (pointFinset c).card := Finset.card_le_card hsubUnion
      _ = (s + 1) * (s * t + 1) := card_pointFinset hP hT c hdeg
  have hmainIneq :
      (s' + 1) * (s' * t + 1) + (t + 1) * (s' * t + 1) * (s - s') ≤
        (s + 1) * (s * t + 1) := by
    calc
      (s' + 1) * (s' * t + 1) + (t + 1) * (s' * t + 1) * (s - s')
          = F.ncard + B.ncard * (s - s') := by rw [hFcard, hBcard]
      _ ≤ (s + 1) * (s * t + 1) := hle
  by_cases hse : s' = s
  · exact Or.inl hse
  · right
    have hs'lt : s' < s := lt_of_le_of_ne hs'le hse
    have htpos : 0 < t := by omega
    have hineqZ :
        ((s' + 1) * (s' * t + 1) : ℤ) +
            ((t + 1) * (s' * t + 1) : ℤ) * ((s - s' : ℕ) : ℤ) ≤
          ((s + 1) * (s * t + 1) : ℤ) := by
      exact_mod_cast hmainIneq
    rw [Nat.cast_sub hs'le] at hineqZ
    have hid :
        ((s + 1) * (s * t + 1) : ℤ) -
            (((s' + 1) * (s' * t + 1) : ℤ) +
              ((t + 1) * (s' * t + 1) : ℤ) * ((s : ℤ) - s')) =
          (t : ℤ) * ((s : ℤ) - s') * ((s : ℤ) - s' * t) := by
      ring
    have hnonneg : 0 ≤ (t : ℤ) * ((s : ℤ) - s') * ((s : ℤ) - s' * t) := by
      rw [← hid]
      linarith
    have htZ : (0 : ℤ) < t := by exact_mod_cast htpos
    have hsdiffZ : (0 : ℤ) < (s : ℤ) - s' := by
      have : (s' : ℤ) < s := by exact_mod_cast hs'lt
      linarith
    have hfactor : (0 : ℤ) ≤ (s : ℤ) - s' * t := by
      by_contra hneg
      have hneg' : (s : ℤ) - s' * t < 0 := not_le.mp hneg
      have hprodpos : 0 < (t : ℤ) * ((s : ℤ) - s') := mul_pos htZ hsdiffZ
      have hprodneg :
          (t : ℤ) * ((s : ℤ) - s') * ((s : ℤ) - s' * t) < 0 :=
        mul_neg_of_pos_of_neg hprodpos hneg'
      linarith
    have hs'ts : s' * t ≤ s := by
      have hcast : ((s' * t : ℕ) : ℤ) ≤ (s : ℤ) := by
        push_cast
        linarith
      exact_mod_cast hcast
    exact hs'ts

theorem eq_or_mul_le_of_closed_dual [Fintype V] [DecidableRel Γ.Adj]
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {F B : Set V} {p : ℕ}
    (hF : ∀ x ∈ F, c x = 0) (hB : ∀ L ∈ B, c L = 1)
    (hBF : ∀ L ∈ B, ∀ x, Γ.Adj L x → x ∈ F)
    (hFB : ∀ x ∈ F, (Γ.neighborSet x ∩ B).ncard = p + 1)
    (hFF : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → ∀ L, Γ.Adj x L → Γ.Adj y L → L ∈ B)
    (hne : F.Nonempty) : p = t ∨ p * s ≤ t := by
  classical
  let dc : Γ.Coloring (Fin 2) := Γ.recolorOfEquiv (Equiv.swap (0 : Fin 2) 1) c
  have hdc0 : ∀ v, dc v = 0 ↔ c v = 1 := by
    intro v
    change Equiv.swap (0 : Fin 2) 1 (c v) = 0 ↔ c v = 1
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c v) with h | h <;> rw [h] <;> decide
  have hdc1 : ∀ v, dc v = 1 ↔ c v = 0 := by
    intro v
    change Equiv.swap (0 : Fin 2) 1 (c v) = 1 ↔ c v = 0
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c v) with h | h <;> rw [h] <;> decide
  have hdeg' : ∀ v, Γ.degree v = if dc v = 0 then s + 1 else t + 1 := by
    intro v
    by_cases hc0 : c v = 0
    · have hdc0' : dc v ≠ 0 := fun h => by
        have h1 : c v = 1 := (hdc0 v).mp h
        rw [hc0] at h1
        exact absurd h1 (by decide)
      rw [hdeg v, if_pos hc0, if_neg hdc0']
    · have hc1 : c v = 1 := by
        have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
        rcases hfin (c v) with h | h
        · exact absurd h hc0
        · exact h
      have hdc0' : dc v = 0 := (hdc0 v).mpr hc1
      rw [hdeg v, if_neg hc0, if_pos hdc0']
  exact eq_or_mul_le_of_closed (s := t) (t := s) hP hT dc hdeg'
    (F := B) (B := F) (s' := p)
    (fun L hL => (hdc0 L).mpr (hB L hL))
    (fun x hx => (hdc1 x).mpr (hF x hx))
    (fun L hL x hxL => hBF L hL x hxL)
    (fun x hx => hFB x hx)
    (fun x hx y hy hxy L hxL hyL => hFF x hx y hy hxy L hxL hyL)
    hne

end CFSG.Geometry.GeneralizedQuadrangles
