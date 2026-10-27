module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434O8pE9Check
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Local

public section

namespace CFSG.AGLEmbedding.O8pCent

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.RankThree.PartTwo.Sec4.Item434O8pE9
open CFSG.Assembly (IsElemAbelian)
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 (posWord wordPerm wordPerm_mem rep_posWord
  letters_of_all dPair_facts mapWord_rep)

@[expose] def commCount (n : ℕ) (cD : ArrCert) (g : Array ℕ) : ℕ :=
  ((List.range cD.pts.size).filter fun i =>
    eqA n (compA n g cD.pts[i]!) (compA n cD.pts[i]! g)).length

@[expose] def centCheck' (X : E9Data) (qg : Array (Array ℕ)) (cD : ArrCert) (gW : List ℕ)
    (b : ℕ) : Bool :=
  gW.all (fun l => decide (l < qg.size)) &&
  !(cD.pts.toList.any (eqA X.n (posWord X.n qg gW))) &&
  decide (commCount X.n cD (posWord X.n qg gW) ≤ b)

@[expose] def centCheck (X : E9Data) (gW : List ℕ) (b : ℕ) : Bool :=
  centCheck' X (qGens X) (dCert X) gW b

private theorem isElemAbelian_mono {G : Type*} [Group G] {p : ℕ} {A B : Subgroup G}
    (hA : IsElemAbelian p A) (hBA : B ≤ A) : IsElemAbelian p B :=
  CFSG.Open.IsElemAbelian.mono hA hBA

theorem centCheck_sound (X : E9Data) (h9 : e9Check X = true) (gW : List ℕ) (b : ℕ)
    (h : centCheck X gW b = true) (P : Subgroup (Equiv.Perm (Fin X.n)))
    (hP : ∀ l < X.pg.size, permOfArr X.n X.pg[l]! ∈ P) :
    ∃ (Q D : Subgroup (Equiv.Perm (Fin X.n))) (g : Equiv.Perm (Fin X.n)),
      Q ≤ P ∧ Nat.card Q = X.qOrd ∧ D ≤ Q ∧ IsElemAbelian 3 D ∧ 81 ≤ Nat.card D ∧
      g ∈ Q ∧ g ∉ D ∧ ∀ C : Subgroup (Equiv.Perm (Fin X.n)), C ≤ D → (∀ c ∈ C, g * c = c * g) →
        Nat.card C ≤ b := by
  unfold e9Check e9Check' at h9
  simp only [Bool.and_eq_true, and_assoc, beq_iff_eq, decide_eq_true_eq] at h9
  obtain ⟨hpg, hkeys, hqW, hhW, hdW, hQenum, hQcard, hDenum, hD81, hDab, hhv, hpairs⟩ := h9
  unfold centCheck centCheck' at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hgW, hnot⟩, hcount⟩ := h
  have hpgv : ∀ l < X.pg.size, validA X.n X.pg[l]! = true := fun l hl => allLt_spec hpg hl
  have hk3 : ∀ p ∈ X.qKeys ++ X.dKeys, p < X.n := fun p hp => by
    simpa using List.all_eq_true.1 hkeys p hp
  have hqk : ∀ p ∈ X.qKeys, p < X.n := fun p hp => hk3 p (by simp [hp])
  have hdk : ∀ p ∈ X.dKeys, p < X.n := fun p hp => hk3 p (by simp [hp])
  have hqWl := letters_of_all hqW
  have hdWl := letters_of_all hdW
  set qg := qGens X with hqg
  have hqgv : ∀ l < qg.size, validA X.n qg[l]! = true := fun l hl => enumOK_gens_valid hQenum hl
  have hqsize : qg.size = X.qW.size := by simp [hqg, qGens]
  have hqgP : ∀ k < qg.size, permOfArr X.n qg[k]! ∈ P := by
    intro k hk
    have hk' : k < X.qW.size := hqsize ▸ hk
    show permOfArr X.n (X.qW.map (posWord X.n X.pg))[k]! ∈ P
    rw [permOfArr_eq_of_rep (mapWord_rep hpgv hqWl hk')]
    exact wordPerm_mem hP (hqWl k hk')
  set Q := Subgroup.closure (permsA X.n qg) with hQdef
  have hQgen : ∀ k < qg.size, permOfArr X.n qg[k]! ∈ Q := fun k hk =>
    Subgroup.subset_closure ⟨k, hk, rfl⟩
  have hQP : Q ≤ P := by
    rw [hQdef, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact hqgP k hk
  have hQcard' : Nat.card Q = X.qOrd := (enumOK_spec hqk hQenum).2.1.trans hQcard
  obtain ⟨D', hD'Q, hD'e, -, hD'mem⟩ := dPair_facts hqgv hQgen hdk hdWl hDenum hD81 hDab
  set D := Subgroup.closure (permsA X.n (dGens X)) with hDdef
  have hmem : ∀ i, i < (dCert X).pts.size → (dCert X).pts[i]! ∈ (dCert X).pts.toList := by
    intro i hi
    rw [getElem!_pos (dCert X).pts i hi]
    exact Array.mem_def.1 (Array.getElem_mem hi)
  have hDD' : D ≤ D' := by
    intro x hx
    obtain ⟨i, hi, hrep⟩ := enumOK_exists_rep hdk hDenum hx
    exact hD'mem _ x hrep (hmem i hi)
  have hDe : IsElemAbelian 3 D := isElemAbelian_mono hD'e hDD'
  have hDQ : D ≤ Q := hDD'.trans hD'Q
  have hD81' : 81 ≤ Nat.card D := by
    rw [(enumOK_spec hdk hDenum).2.1]
    exact hD81
  have hgrep : Rep X.n (posWord X.n qg gW) (wordPerm X.n qg gW) := rep_posWord hqgv gW hgW
  have hgQ : wordPerm X.n qg gW ∈ Q := wordPerm_mem hQgen hgW
  have hgD : wordPerm X.n qg gW ∉ D := by
    intro hgD
    obtain ⟨i, hi, hrep⟩ := enumOK_exists_rep hdk hDenum hgD
    have hany : (dCert X).pts.toList.any (eqA X.n (posWord X.n qg gW)) = true := by
      rw [List.any_eq_true]
      exact ⟨(dCert X).pts[i]!, hmem i hi, (eqA_iff hgrep hrep).2 rfl⟩
    rw [hany] at hnot
    exact absurd hnot (by simp)
  refine ⟨Q, D, wordPerm X.n qg gW, hQP, hQcard', hDQ, hDe, hD81', hgQ, hgD, ?_⟩
  intro C hCD hCg
  set S : Finset ℕ := ((List.range (dCert X).pts.size).filter fun i =>
      eqA X.n (compA X.n (posWord X.n qg gW) (dCert X).pts[i]!)
        (compA X.n (dCert X).pts[i]! (posWord X.n qg gW))).toFinset with hS
  have hSc : S.card ≤ b := by
    have h1 : S.card = commCount X.n (dCert X) (posWord X.n qg gW) := by
      rw [hS, commCount]
      exact List.toFinset_card_of_nodup (List.nodup_range.filter _)
    omega
  have hsub : (C : Set (Equiv.Perm (Fin X.n))) ⊆
      (fun i => permOfArr X.n (dCert X).pts[i]!) '' (S : Set ℕ) := by
    intro x hx
    obtain ⟨i, hi, hrep⟩ := enumOK_exists_rep hdk hDenum (hCD hx)
    refine ⟨i, ?_, permOfArr_eq_of_rep hrep⟩
    rw [Finset.mem_coe, hS, List.mem_toFinset, List.mem_filter]
    exact ⟨List.mem_range.2 hi,
      (eqA_iff (rep_compA hgrep hrep) (rep_compA hrep hgrep)).2 (hCg x hx)⟩
  calc Nat.card C = Set.ncard (C : Set (Equiv.Perm (Fin X.n))) := (Nat.card_coe_set_eq _).symm
    _ ≤ Set.ncard ((fun i => permOfArr X.n (dCert X).pts[i]!) '' (S : Set ℕ)) :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ Set.ncard (S : Set ℕ) := Set.ncard_image_le (Set.toFinite _)
    _ = S.card := Set.ncard_coe_finset S
    _ ≤ b := hSc

end CFSG.AGLEmbedding.O8pCent
