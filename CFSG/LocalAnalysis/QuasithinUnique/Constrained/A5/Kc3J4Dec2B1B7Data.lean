module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1B7Lem

public section

namespace CFSG.QuasithinUnique.A5.B7

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
  CFSG.Sporadic.J4.QT2.B7 CFSG.Sporadic.J4.QT2A

theorem closure_words_eq_Eg {ws : List (List ℤ)} (hlen : ws.length = 4) :
    Subgroup.closure {x : J | x ∈ ws.map el5} = Eg (fun j => el5 (ws.getD j [])) 4 := by
  unfold Eg
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, List.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
    exact ⟨j, by omega, by rw [List.getD_eq_getElem _ _ hj]⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨ws.getD j [], by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _,
      rfl⟩

theorem cross_of_chk {A B : Array (Array V2)} (h : chkCross A B = true) :
    ∀ j < 4, ∃ k < 16, eqRows (A[j]?.getD idRows) (etaRows B 4 k) = true := by
  unfold chkCross at h
  simp only [List.all_eq_true, List.any_eq_true, List.mem_range] at h
  intro j hj
  obtain ⟨k, hk, e⟩ := h j hj
  exact ⟨k, hk, e⟩

theorem Eg_eq_of_rows {u g : ℕ → J} {U G : Array (Array V2)}
    (hu : ∀ j < 4, Mx (u j) = rowsMatrix (U[j]?.getD idRows))
    (hg : ∀ j < 4, Mx (g j) = rowsMatrix (G[j]?.getD idRows))
    (h1 : ∀ j < 4, ∃ k < 16, eqRows (U[j]?.getD idRows) (etaRows G 4 k) = true)
    (h2 : ∀ j < 4, ∃ k < 16, eqRows (G[j]?.getD idRows) (etaRows U 4 k) = true) :
    Eg u 4 = Eg g 4 := by
  have key : ∀ {a b : ℕ → J} {A B : Array (Array V2)},
      (∀ j < 4, Mx (a j) = rowsMatrix (A[j]?.getD idRows)) →
      (∀ j < 4, Mx (b j) = rowsMatrix (B[j]?.getD idRows)) →
      (∀ j < 4, ∃ k < 16, eqRows (A[j]?.getD idRows) (etaRows B 4 k) = true) →
      Eg a 4 ≤ Eg b 4 := by
    intro a b A B ha hb h
    unfold Eg
    rw [Subgroup.closure_le]
    rintro x ⟨j, hj, rfl⟩
    obtain ⟨k, -, hk⟩ := h j hj
    have : a j = eta b 4 k := by
      apply Mx_injective
      rw [ha j hj, Mx_eta_of hb 4 le_rfl k, eqRows_iff.1 hk]
    rw [this]
    exact eta_mem_Eg 4 le_rfl k
  exact le_antisymm (key hu hg h1) (key hg hu h2)

theorem Mx_words_rows (hM : MatFacts) {ws : List (List ℤ)} {j : ℕ} (hj : j < ws.length) :
    Mx (el5 (ws.getD j [])) = rowsMatrix (((ws.map wR).toArray)[j]?.getD idRows) := by
  rw [Mx_el5 hM]
  have : ((ws.map wR).toArray)[j]? = some (wR (ws.getD j [])) := by
    simp [hj]
  rw [this]
  rfl

end CFSG.QuasithinUnique.A5.B7
