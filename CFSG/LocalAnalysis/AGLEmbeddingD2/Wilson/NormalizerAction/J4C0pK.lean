module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4Gam
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Gen
public import Certificates.Certificate12608

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2A CFSG.Quasithin.J4M2 CFSG.Quasithin.J4Loc
  CFSG.AGLEmbeddingD2.Wilson.Coordinator

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def c0pLetJ (l : ℕ) : J :=
  match l with
  | 0 => cA
  | 1 => cB
  | 2 => cZ
  | 3 => cA⁻¹
  | 4 => cB⁻¹
  | _ => cZ⁻¹

@[expose] def c0pWordJ (w : List ℕ) : J := w.foldl (fun acc l => acc * c0pLetJ l) 1

theorem c0pLetJ_mem (l : ℕ) : c0pLetJ l ∈ C0p := by
  have hA : cA ∈ C0p := Subgroup.subset_closure (by simp)
  have hB : cB ∈ C0p := Subgroup.subset_closure (by simp)
  have hZ : cZ ∈ C0p := Subgroup.subset_closure (by simp)
  unfold c0pLetJ
  split
  · exact hA
  · exact hB
  · exact hZ
  · exact C0p.inv_mem hA
  · exact C0p.inv_mem hB
  · exact C0p.inv_mem hZ

theorem foldl_mem_subgroup {G : Type*} [Group G] (H : Subgroup G) (f : ℕ → G)
    (hf : ∀ l, f l ∈ H) (w : List ℕ) :
    ∀ g : G, g ∈ H → w.foldl (fun acc l => acc * f l) g ∈ H := by
  induction w with
  | nil => exact fun g hg => hg
  | cons l w ih => exact fun g hg => ih _ (H.mul_mem hg (hf l))

theorem foldl_hom_aux {G M R : Type*} [Group G] [Monoid M] (φ : G →* M) (ρ : R → M)
    (mulR : R → R → R) (hmul : ∀ X Y, ρ (mulR X Y) = ρ X * ρ Y) (f : ℕ → G) (rs : ℕ → R)
    (w : List ℕ) (hw : ∀ l ∈ w, φ (f l) = ρ (rs l)) : ∀ (g : G) (X : R), φ g = ρ X →
      φ (w.foldl (fun acc l => acc * f l) g) = ρ (w.foldl (fun acc l => mulR acc (rs l)) X) := by
  induction w with
  | nil => exact fun g X h => h
  | cons l w ih =>
    intro g X h
    refine ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) _ _ ?_
    rw [map_mul, hmul, h, hw l List.mem_cons_self]

theorem c0pWordJ_mem (w : List ℕ) : c0pWordJ w ∈ C0p :=
  @foldl_mem_subgroup J (Subgroup.toGroup J) C0p c0pLetJ c0pLetJ_mem w 1 C0p.one_mem

section Matrices


theorem Mx_c0pLetJ {l : ℕ} (hl : l < 6) :
    Mx (c0pLetJ l) = rowsMatrix c0pLetRows[l]! := by
  interval_cases l
  · exact Mx_cA
  · exact Mx_cB
  · exact Mx_cZ
  · exact Mx_cAinv
  · exact Mx_cBinv
  · exact Mx_cZinv

theorem Mx_c0pWordJ (w : List ℕ) (hw : ∀ l ∈ w, l < 6) :
    Mx (c0pWordJ w) = rowsMatrix (c0pWordRows w) :=
  @foldl_hom_aux J _ (Array V2) (Subgroup.toGroup J) _ Mx rowsMatrix mulRows
    rowsMatrix_mulRows c0pLetJ (fun l => c0pLetRows[l]!) w
    (fun l hl => Mx_c0pLetJ (hw l hl)) 1 idRows (by rw [map_one, rowsMatrix_idRows])

theorem mem_C0p_of_word {g : J} {X : Array V2} {w : List ℕ} (hw : ∀ l ∈ w, l < 6)
    (hg : Mx g = rowsMatrix X) (h : eqRows (c0pWordRows w) X = true) : g ∈ C0p := by
  have h1 : c0pWordRows w = X := eqRows_iff.1 h
  have : g = c0pWordJ w := by
    apply Mx_injective
    rw [Mx_c0pWordJ w hw, h1, hg]
  rw [this]
  exact c0pWordJ_mem w

end Matrices

@[expose] def etaRowsN (n c : ℕ) : Array V2 :=
  (List.range n).foldl (fun acc j => if c.testBit j then mulRows acc gmats[j]! else acc) idRows

theorem etaRowsN_succ (n c : ℕ) :
    etaRowsN (n + 1) c = if c.testBit n then mulRows (etaRowsN n c) gmats[n]! else etaRowsN n c := by
  unfold etaRowsN
  rw [List.range_succ, List.foldl_append]
  by_cases h : c.testBit n <;> simp [h]

theorem etaRows12_eq (c : ℕ) : etaRows12 c = etaRowsN 12 c := rfl

section Facts


theorem c0pKOK_parts : c0pKWF = true ∧ (k3Words.all fun w => w.all fun l => decide (l < 6)) = true ∧
    (q8Words.all fun w => w.all fun l => decide (l < 6)) = true ∧
    (List.zip k3Words (k3FormsN.map kEltRows)).all
      (fun p => eqRows (c0pWordRows p.1) p.2) = true ∧
    (List.zip q8Words (q8FormsN.map fun f => qNFRows f.1 f.2)).all
      (fun p => eqRows (c0pWordRows p.1) p.2) = true ∧
    allDistinct (k3FormsN.map kEltRows) = true ∧
    allDistinct (q8FormsN.map fun f => qNFRows f.1 f.2) = true := by
  have h : c0pKOK = true := Certificates.certificate12608
  unfold c0pKOK at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, -, -, -, -, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem wfR_gmats {j : ℕ} (hj : j < 12) : wfR gmats[j]! = true := by
  have h := c0pKOK_parts.1
  unfold c0pKWF at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact h.2 j hj

theorem wfR_zM : wfR zM = true := by
  have h := c0pKOK_parts.1
  unfold c0pKWF at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

theorem wfR_cMat : wfR cMat = true := by
  have h := c0pKOK_parts.1
  unfold c0pKWF at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

theorem wfR_etaRowsN {n : ℕ} (hn : n ≤ 12) (c : ℕ) : wfR (etaRowsN n c) = true := by
  induction n with
  | zero => exact wfR_idRows
  | succ n ih =>
    rw [etaRowsN_succ]
    split_ifs
    · exact wfR_mulRows (ih (by omega)) (wfR_gmats (by omega))
    · exact ih (by omega)

theorem wfR_qNFRows (e : Bool) (c : ℕ) : wfR (qNFRows e c) = true := by
  unfold qNFRows
  refine wfR_mulRows ?_ (by rw [etaRows12_eq]; exact wfR_etaRowsN le_rfl c)
  split_ifs
  · exact wfR_zM
  · exact wfR_idRows

theorem wfR_kEltRows (f : Bool × ℕ × ℕ) : wfR (kEltRows f) = true :=
  wfR_mulRows (wfR_qNFRows _ _) (wfR_powRows wfR_cMat _)

end Facts

theorem Mx_eta_gE (n : ℕ) (hn : n ≤ 12) (c : ℕ) :
    Mx (eta gE n c) = rowsMatrix (etaRowsN n c) := by
  induction n with
  | zero => simp [etaRowsN, eta, rowsMatrix_idRows]
  | succ n ih =>
    rw [etaRowsN_succ, eta_succ, map_mul]
    have ih' := ih (by omega)
    split_ifs with h
    · rw [rowsMatrix_mulRows, ih', Mx_gE matFacts (by omega : n < 32)]
    · rw [ih', map_one, mul_one]

theorem Mx_qNF (e : Bool) (c : ℕ) : Mx (qNF e c) = rowsMatrix (qNFRows e c) := by
  unfold qNF qNFRows
  rw [map_mul, rowsMatrix_mulRows, etaRows12_eq, Mx_eta_gE 12 le_rfl c]
  congr 1
  cases e
  · simp [rowsMatrix_idRows]
  · simpa using rowsMatrix_zM matFacts |>.symm

theorem Mx_kElt
    (f : Bool × ℕ × ℕ) : Mx (kElt f) = rowsMatrix (kEltRows f) := by
  unfold kElt kEltRows
  rw [map_mul, rowsMatrix_mulRows, Mx_qNF, map_pow, Mx_cE matFacts, rowsMatrix_powRows]

theorem eta_gE_mem_Qgrp (n : ℕ) (hn : n ≤ 12) (c : ℕ) : eta gE n c ∈ Qgrp := by
  induction n with
  | zero => exact Qgrp.one_mem
  | succ n ih =>
    rw [eta_succ]
    refine Qgrp.mul_mem (ih (by omega)) ?_
    split_ifs
    · exact gE_mem_Qgrp (by omega)
    · exact Qgrp.one_mem

theorem qNF_mem_Qgrp
    (e : Bool) (c : ℕ) : qNF e c ∈ Qgrp := by
  unfold qNF
  refine Qgrp.mul_mem ?_ (eta_gE_mem_Qgrp 12 le_rfl c)
  split_ifs
  · exact z0_mem_Qgrp matFacts
  · exact Qgrp.one_mem

theorem kElt_mem_Kgrp
    (f : Bool × ℕ × ℕ) : kElt f ∈ Kgrp := by
  unfold kElt
  refine Kgrp.mul_mem ((le_sup_left : Qgrp ≤ Kgrp) (qNF_mem_Qgrp _ _)) (Kgrp.pow_mem ?_ _)
  exact (le_sup_right : Subgroup.zpowers cE ≤ Kgrp) (Subgroup.mem_zpowers cE)

theorem ncard_image_of_idx {α β : Type*} (l : List α) (f : α → β)
    (h : ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length), f l[i] = f l[j] → i = j) :
    (f '' {x | x ∈ l}).ncard = l.length := by
  classical
  have hnd : l.Nodup := by
    rw [List.nodup_iff_injective_get]
    intro i j hij
    exact Fin.ext (h i j i.2 j.2 (by simp only [List.get_eq_getElem] at hij; rw [hij]))
  have hinj : Set.InjOn f {x | x ∈ l} := by
    intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
    obtain rfl := h i j hi hj hxy
    rfl
  rw [hinj.ncard_image]
  have : {x | x ∈ l} = ((l.toFinset : Finset α) : Set α) := by ext; simp
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

theorem k3Forms_eq : k3Forms = k3FormsN := rfl

theorem q8Masks_eq : q8Masks = q8MasksN := rfl

theorem mem_q8FormsN {e : Bool} {c : ℕ} : (e, c) ∈ q8FormsN ↔ c ∈ q8Masks := by
  rw [q8Masks_eq]
  cases e <;> simp [q8FormsN]

theorem K3set_eq_image : K3set = kElt '' {f | f ∈ k3FormsN} := by
  ext g
  simp only [K3set, k3Forms_eq, Set.mem_ofPred_eq, Set.mem_image]
  exact ⟨fun ⟨f, hf, h⟩ => ⟨f, hf, h.symm⟩, fun ⟨f, hf, h⟩ => ⟨f, hf, h.symm⟩⟩

theorem Q8set_eq_image : Q8set = (fun f : Bool × ℕ => qNF f.1 f.2) '' {f | f ∈ q8FormsN} := by
  ext g
  simp only [Q8set, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨e, c, hc, h⟩
    exact ⟨(e, c), mem_q8FormsN.2 hc, h.symm⟩
  · rintro ⟨⟨e, c⟩, hf, h⟩
    exact ⟨e, c, mem_q8FormsN.1 hf, h.symm⟩

theorem K3set_subset :
    K3set ⊆ ((C0p ⊓ Kgrp : Subgroup J) : Set J) := by
  obtain ⟨-, hk, -, hw, -, -, -⟩ := c0pKOK_parts
  rintro g ⟨f, hf, rfl⟩
  rw [k3Forms_eq] at hf
  refine ⟨?_, kElt_mem_Kgrp f⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hf
  have hlen : k3FormsN.length = k3Words.length := by decide
  have hi' : i < (List.zip k3Words (k3FormsN.map kEltRows)).length := by
    simp only [List.length_zip, List.length_map]; omega
  have h1 := List.all_eq_true.1 hw _ (List.getElem_mem hi')
  have hl := List.all_eq_true.1 hk k3Words[i] (List.getElem_mem (by omega))
  simp only [List.getElem_zip, List.getElem_map] at h1
  refine mem_C0p_of_word (w := k3Words[i]'(by omega)) ?_ (Mx_kElt _) h1
  intro l hl'
  simpa using List.all_eq_true.1 hl l hl'

theorem Q8set_subset :
    Q8set ⊆ ((C0p ⊓ Qgrp : Subgroup J) : Set J) := by
  obtain ⟨-, -, hk, -, hw, -, -⟩ := c0pKOK_parts
  rw [Q8set_eq_image]
  rintro g ⟨⟨e, c⟩, hf, rfl⟩
  refine ⟨?_, qNF_mem_Qgrp e c⟩
  obtain ⟨i, hi, hfi⟩ := List.mem_iff_getElem.1 hf
  have hlen : q8FormsN.length = q8Words.length := by decide
  have hi' : i < (List.zip q8Words (q8FormsN.map fun f => qNFRows f.1 f.2)).length := by
    simp only [List.length_zip, List.length_map]; omega
  have h1 := List.all_eq_true.1 hw _ (List.getElem_mem hi')
  have hl := List.all_eq_true.1 hk q8Words[i] (List.getElem_mem (by omega))
  simp only [List.getElem_zip, List.getElem_map, hfi] at h1
  refine mem_C0p_of_word (w := q8Words[i]'(by omega)) ?_ (Mx_qNF e c) h1
  intro l hl'
  simpa using List.all_eq_true.1 hl l hl'

theorem ncard_K3set :
    K3set.ncard = 24 := by
  obtain ⟨-, -, -, -, -, hd, -⟩ := c0pKOK_parts
  rw [K3set_eq_image]
  have h := ncard_image_of_idx k3FormsN kElt (by
    intro i j hi hj hij
    by_contra hne
    have h1 := allDistinct_spec hd i j (by simpa using hi) (by simpa using hj) hne
    simp only [List.getElem_map] at h1
    refine ne_of_eqRows_false (wfR_kEltRows _) (wfR_kEltRows _) h1 ?_
    rw [← Mx_kElt, ← Mx_kElt, hij])
  rw [h]
  decide

theorem ncard_Q8set :
    Q8set.ncard = 8 := by
  obtain ⟨-, -, -, -, -, -, hd⟩ := c0pKOK_parts
  rw [Q8set_eq_image]
  have h := ncard_image_of_idx q8FormsN (fun f : Bool × ℕ => qNF f.1 f.2) (by
    intro i j hi hj hij
    by_contra hne
    have h1 := allDistinct_spec hd i j (by simpa using hi) (by simpa using hj) hne
    simp only [List.getElem_map] at h1
    refine ne_of_eqRows_false (wfR_qNFRows _ _) (wfR_qNFRows _ _) h1 ?_
    rw [← Mx_qNF, ← Mx_qNF]
    exact congrArg Mx hij)
  rw [h]
  decide

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
