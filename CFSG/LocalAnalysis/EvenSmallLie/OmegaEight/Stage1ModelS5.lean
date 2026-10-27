module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelElts

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1.Model

open Subgroup Matrix CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
open CFSG.Certificates.Native

variable {ε : Eps}

theorem mem_enumAux (ok : List Bool → Bool) :
    ∀ (d pre : List Bool), (∀ k, 0 < k → k ≤ d.length → ok (pre ++ d.take k) = true) →
      pre ++ d ∈ enumAux ok d.length pre
  | [], pre, _ => by simp [enumAux]
  | b :: d, pre, h => by
    have hb : ok (pre ++ [b]) = true := by simpa using h 1 (by omega) (by simp)
    have ih := mem_enumAux ok d (pre ++ [b]) fun k hk hkd => by
      have := h (k + 1) (by omega) (by simp; omega)
      simpa using this
    rw [List.length_cons, enumAux]
    cases b
    · apply List.mem_append_left
      simp only [hb, ↓reduceIte]
      simpa using ih
    · apply List.mem_append_right
      simp only [hb, ↓reduceIte]
      simpa using ih

theorem getD_ofFn' {α : Type*} {m : ℕ} (f : Fin m → α) (x : α) {i : ℕ} (hi : i < m) :
    (Array.ofFn f).getD i x = f ⟨i, hi⟩ := by
  simp [Array.getD, hi]

theorem toArray_getD (l : List Bool) (c : ℕ) : l.toArray.getD c false = l.getD c false := by
  by_cases h : c < l.length
  · simp [Array.getD, h]
  · simp [Array.getD, h]

@[expose] noncomputable def uAt (ε : Eps) (i : ℕ) : Array ℕ := (uListW ε).getD i #[]

@[expose] noncomputable def SP (ε : Eps) (i : ℕ) : Equiv.Perm (Fin (deg ε)) :=
  permOfArr (deg ε) (uAt ε i)

theorem s5_parts (ε : Eps) :
    (∀ i < 4096, isInvA (deg ε) (uAt ε i) (invCand (deg ε) (uAt ε i)) = true ∧
      (uAt ε i).size = deg ε ∧ memU ε (uAt ε i) = true) ∧
    (∀ i < 4096, ∀ j < i, eqA (deg ε) (uAt ε i) (uAt ε j) = false) ∧
    (∀ i < 4096, ∀ c j, clsOfW (uClsW ε) i = some (c, j) → c < nClsW (uClsW ε) ∧ j < 4096 ∧
      isInvol (deg ε) (uAt ε i) = true ∧
      eqA (deg ε) (uAt ε i) (conjA (deg ε) (uAt ε j) (uAt ε (repOfW (uClsW ε) c))) = true) ∧
    (∀ i < 4096, clsOfW (uClsW ε) i = none → isInvol (deg ε) (uAt ε i) = false) ∧
    (∀ c < nClsW (uClsW ε), repOfW (uClsW ε) c < 4096) ∧
    (∀ d ∈ enumAux (okPreW ε (uListW ε) (uClsW ε)) (nClsW (uClsW ε)) [],
      sumSelW (uClsW ε) d ≠ 63 ∨ ∃ w ∈ cands ε, finalOKW ε (uListW ε) (uClsW ε) w d = true) := by
  have h := (modelChecks ε).2.2.2
  simp only [s5CheckW, Bool.and_eq_true, allLt_iff, beq_iff_eq, List.all_eq_true,
    Bool.or_eq_true, bne_iff_ne, ne_eq, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨_, h1⟩, hd⟩, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun i hi => ?_, fun i hi j hj => ?_, fun i hi c j hc => ?_, fun i hi hc => ?_,
    fun c hc => by simpa using h3 c hc, fun d hd => ?_⟩
  · obtain ⟨⟨a1, a2⟩, a3⟩ := h1 i hi
    exact ⟨a1, a2, a3⟩
  · simpa [uAt] using hd i hi j hj
  · have := h2 i hi
    rw [hc] at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := this
    exact ⟨a1, a2, a3, a4⟩
  · have := h2 i hi
    rw [hc] at this
    simpa [uAt] using this
  · rcases h4 d hd with h | h
    · exact Or.inl h
    · exact Or.inr h


theorem rep_SP {i : ℕ} (hi : i < 4096) : Rep (deg ε) (uAt ε i) (SP ε i) ∧
    Rep (deg ε) (invCand (deg ε) (uAt ε i)) (SP ε i)⁻¹ :=
  rep_permOfArr ((s5_parts ε).1 i hi).1

theorem SP_mem_U {i : ℕ} (hi : i < 4096) : SP ε i ∈ UQm ε :=
  (memU_iff (rep_SP hi).1).1 ((s5_parts ε).1 i hi).2.2

theorem SP_injective {i j : ℕ} (hi : i < 4096) (hj : j < 4096) (e : SP ε i = SP ε j) : i = j := by
  have key : ∀ a b, a < 4096 → b < a → SP ε a ≠ SP ε b := fun a b ha hba he => by
    have h := (s5_parts ε).2.1 a ha b hba
    rw [(eqA_iff (rep_SP ha).1 (rep_SP (by omega : b < 4096)).1).2 he] at h
    exact absurd h (by decide)
  rcases lt_trichotomy i j with h | h | h
  · exact absurd e.symm (key j i hj h)
  · exact h
  · exact absurd e (key i j hi h)

theorem exists_SP {x : Equiv.Perm (Fin (deg ε))} (hx : x ∈ UQm ε) : ∃ i < 4096, SP ε i = x := by
  classical
  set T : Finset (Equiv.Perm (Fin (deg ε))) := (Finset.range 4096).image (SP ε)
  have hT : T.card = 4096 := by
    rw [Finset.card_image_of_injOn (fun i hi j hj e => SP_injective (by simpa using hi)
      (by simpa using hj) e), Finset.card_range]
  have hsub : (T : Set (Equiv.Perm (Fin (deg ε)))) ⊆ (UQm ε : Set (Equiv.Perm (Fin (deg ε)))) := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hy
    exact SP_mem_U (by simpa using hi)
  have heq : (T : Set (Equiv.Perm (Fin (deg ε)))) = (UQm ε : Set (Equiv.Perm (Fin (deg ε)))) := by
    apply Set.eq_of_subset_of_ncard_le hsub
    rw [Set.ncard_coe_finset, hT, ← Nat.card_coe_set_eq]
    exact (card_UQm ε).le
  have : x ∈ (T : Set (Equiv.Perm (Fin (deg ε)))) := heq ▸ hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 this
  exact ⟨i, by simpa using hi, rfl⟩

theorem SP_cls {i c j : ℕ} (hi : i < 4096) (hc : clsOfW (uClsW ε) i = some (c, j)) :
    c < nClsW (uClsW ε) ∧ j < 4096 ∧ repOfW (uClsW ε) c < 4096 ∧ SP ε i ≠ 1 ∧
      SP ε i = SP ε j * SP ε (repOfW (uClsW ε) c) * (SP ε j)⁻¹ := by
  obtain ⟨hc1, hj, hinv, heq⟩ := (s5_parts ε).2.2.1 i hi c j hc
  have hr := (s5_parts ε).2.2.2.2.1 c hc1
  refine ⟨hc1, hj, hr, fun h1 => ?_, ?_⟩
  · simp only [isInvol, Bool.and_eq_true, Bool.not_eq_true'] at hinv
    rw [(eqA_iff (rep_SP hi).1 rep_idA).2 h1] at hinv
    exact absurd hinv.1 (by decide)
  · exact eq_of_eqA (rep_SP hi).1
      (rep_compA (rep_compA (rep_SP hj).1 (rep_SP hr).1) (rep_SP hj).2) heq

theorem SP_none {i : ℕ} (hi : i < 4096) (hc : clsOfW (uClsW ε) i = none) :
    SP ε i = 1 ∨ SP ε i * SP ε i ≠ 1 := by
  have h := (s5_parts ε).2.2.2.1 i hi hc
  simp only [isInvol, Bool.and_eq_false_iff, Bool.not_eq_false'] at h
  rcases h with h | h
  · exact Or.inl ((eqA_iff (rep_SP hi).1 rep_idA).1 h)
  · right
    intro h1
    rw [(eqA_iff (rep_compA (rep_SP hi).1 (rep_SP hi).1) rep_idA).2 h1] at h
    exact absurd h (by decide)


theorem okPre_of_pairs {S : Array (Array ℕ)} {D : UCls} {l : List Bool}
    (h : ∀ c < l.length, ∀ c' < l.length, l.getD c false = true → l.getD c' false = true →
      adjTW ε S D c' c = true) :
    okPreW ε S D l = true := by
  unfold okPreW
  rcases hl : l.getLast? with _ | b
  · rfl
  · cases b
    · rfl
    · have hne : l ≠ [] := by
        rintro rfl
        simp at hl
      have hlen : 0 < l.length := List.length_pos_of_ne_nil hne
      have hlast : l.getD (l.length - 1) false = true := by
        rw [List.getLast?_eq_getElem?] at hl
        simp [List.getD_eq_getElem?_getD, hl]
      simp only [Bool.and_eq_true, allLt_iff, Bool.or_eq_true, Bool.not_eq_true', toArray_getD]
      refine ⟨h _ (by omega) _ (by omega) hlast hlast, fun c' hc' => ?_⟩
      by_cases hc'd : l.getD c' false = true
      · exact Or.inr (h _ (by omega) _ (by omega) hlast hc'd)
      · exact Or.inl (by simpa using hc'd)

theorem getD_take {l : List Bool} {k c : ℕ} (hc : c < k) :
    (l.take k).getD c false = l.getD c false := by
  simp [List.getD_eq_getElem?_getD, hc]

theorem S5_model {A : Subgroup (Equiv.Perm (Fin (deg ε)))} (hAU : A ≤ UQm ε)
    (hAn : ∀ x ∈ UQm ε, ∀ y ∈ A, x * y * x⁻¹ ∈ A) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hA2 : ∀ x ∈ A, x * x = 1) (hA64 : Nat.card A = 64) :
    ∃ l ∈ Lm ε, (∀ x ∈ A, l * x * l⁻¹ ∈ A) ∧
      l * psiM ε (Pi.single 0 1) * l⁻¹ ≠ psiM ε (Pi.single 0 1) := by
  classical
  have hall : ∀ {i c j : ℕ}, i < 4096 → clsOfW (uClsW ε) i = some (c, j) →
      (SP ε i ∈ A ↔ SP ε (repOfW (uClsW ε) c) ∈ A) := by
    intro i c j hi hc
    obtain ⟨-, hj, -, -, he⟩ := SP_cls hi hc
    rw [he]
    constructor
    · intro h
      have := hAn _ (inv_mem (SP_mem_U hj)) _ h
      simpa [mul_assoc] using this
    · exact hAn _ (SP_mem_U hj) _
  set d : List Bool := List.ofFn fun c : Fin (nClsW (uClsW ε)) => decide (SP ε (repOfW (uClsW ε) c) ∈ A) with hd_def
  have hdlen : d.length = nClsW (uClsW ε) := by simp [d]
  have hd : ∀ c, d.getD c false = true ↔ c < nClsW (uClsW ε) ∧ SP ε (repOfW (uClsW ε) c) ∈ A := by
    intro c
    by_cases hc : c < nClsW (uClsW ε)
    · simp [d, hc, List.getD_eq_getElem?_getD]
    · simp [d, hc, List.getD_eq_getElem?_getD]
  have hsel : ∀ {i : ℕ}, i < 4096 →
      (selB d.toArray (clsOfW (uClsW ε) i) = true ↔ (SP ε i ∈ A ∧ SP ε i ≠ 1)) := by
    intro i hi
    rcases hci : clsOfW (uClsW ε) i with _ | ⟨c, j⟩
    · simp only [selB]
      constructor
      · intro h
        exact absurd h (by decide)
      · rintro ⟨hA, hne⟩
        rcases SP_none hi hci with h | h
        · exact absurd h hne
        · exact absurd (hA2 _ hA) h
    · simp only [selB, toArray_getD]
      obtain ⟨hc1, -, -, hne, -⟩ := SP_cls hi hci
      rw [hd c, hall hi hci]
      exact ⟨fun h => ⟨h.2, hne⟩, fun h => ⟨hc1, h.1⟩⟩
  have hsum : sumSelW (uClsW ε) d = 63 := by
    have h1 : sumSelW (uClsW ε) d =
        ((Finset.range 4096).filter fun i => selB d.toArray (clsOfW (uClsW ε) i) = true).card := by
      simp only [sumSelW]
      rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _), List.toFinset_filter,
        List.toFinset_range]
    have h2 : ((Finset.range 4096).filter fun i => selB d.toArray (clsOfW (uClsW ε) i) = true).card =
        ((A : Set (Equiv.Perm (Fin (deg ε)))) \ {1}).ncard := by
      rw [← Set.ncard_coe_finset]
      refine Set.ncard_congr (fun i _ => SP ε i) ?_ ?_ ?_
      · intro i hi
        simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi
        obtain ⟨hA, hne⟩ := (hsel hi.1).1 hi.2
        exact ⟨hA, hne⟩
      · intro i j hi hj e
        simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi hj
        exact SP_injective hi.1 hj.1 e
      · rintro x ⟨hxA, hx1⟩
        obtain ⟨i, hi, rfl⟩ := exists_SP (hAU hxA)
        refine ⟨i, ?_, rfl⟩
        simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
        exact ⟨hi, (hsel hi).2 ⟨hxA, hx1⟩⟩
    have h3 : ((A : Set (Equiv.Perm (Fin (deg ε)))) \ {1}).ncard = 63 := by
      rw [Set.ncard_sdiff_singleton_of_mem (one_mem A), ← Nat.card_coe_set_eq]
      change Nat.card A - 1 = 63
      rw [hA64]
    rw [h1, h2, h3]
  have hadj : ∀ c < nClsW (uClsW ε), ∀ c' < nClsW (uClsW ε), SP ε (repOfW (uClsW ε) c) ∈ A → SP ε (repOfW (uClsW ε) c') ∈ A →
      adjTW ε (uListW ε) (uClsW ε) c' c = true := by
    intro c hc c' hc' hcA hc'A
    have hT : ∀ c'' < nClsW (uClsW ε), (membersTabW (uClsW ε)).getD c'' [] =
        membersOfW (uClsW ε) c'' := fun c'' h => getD_ofFn' _ _ h
    have htab : adjTW ε (uListW ε) (uClsW ε) c' c =
        adjBW ε (uListW ε) (membersTabW (uClsW ε)) c' c := by
      rw [adjTW, adjTabW, getD_ofFn' _ _ hc', getD_ofFn' _ _ hc]
    rw [htab, adjBW, hT c' hc', hT c hc]
    simp only [List.all_eq_true]
    intro i hi i' hi'
    simp only [membersOfW, List.mem_filter, List.mem_range, beq_iff_eq] at hi hi'
    obtain ⟨hi4, hic⟩ := hi
    obtain ⟨hi'4, hi'c⟩ := hi'
    obtain ⟨⟨c1, j1⟩, hcl1, hc1⟩ := Option.map_eq_some_iff.1 hic
    obtain ⟨⟨c2, j2⟩, hcl2, hc2⟩ := Option.map_eq_some_iff.1 hi'c
    simp only at hc1 hc2
    subst hc1 hc2
    have hxA : SP ε i ∈ A := (hall hi4 hcl1).2 hc'A
    have hyA : SP ε i' ∈ A := (hall hi'4 hcl2).2 hcA
    exact (eqA_iff (rep_compA (rep_SP hi4).1 (rep_SP hi'4).1)
      (rep_compA (rep_SP hi'4).1 (rep_SP hi4).1)).2 (hAc _ hxA _ hyA)
  have hok : ∀ k, 0 < k → k ≤ d.length →
      okPreW ε (uListW ε) (uClsW ε) ([] ++ d.take k) = true := by
    intro k hk hkd
    rw [List.nil_append]
    apply okPre_of_pairs
    intro c hc c' hc' h1 h2
    rw [List.length_take] at hc hc'
    rw [getD_take (by omega)] at h1 h2
    obtain ⟨hcn, hcA⟩ := (hd c).1 h1
    obtain ⟨hc'n, hc'A⟩ := (hd c').1 h2
    exact hadj c hcn c' hc'n hcA hc'A
  have hmem : d ∈ enumAux (okPreW ε (uListW ε) (uClsW ε)) (nClsW (uClsW ε)) [] := by
    have := mem_enumAux (okPreW ε (uListW ε) (uClsW ε)) d [] hok
    rw [hdlen] at this
    simpa using this
  obtain ⟨w, -, hfin⟩ := ((s5_parts ε).2.2.2.2.2 d hmem).resolve_left
    (by rw [hsum]; exact fun h => h rfl)
  simp only [finalOKW, Bool.and_eq_true, allLt_iff, Bool.or_eq_true, Bool.not_eq_true',
    List.any_eq_true, List.mem_range] at hfin
  obtain ⟨⟨⟨hlL, hlinv⟩, hla⟩, hlA⟩ := hfin
  have hrep := rep_permOfArr hlinv
  have ha : Rep (deg ε) (psiT ε 1) (psiM ε (Pi.single 0 1)) := by
    rw [psiT_eq ε (by norm_num)]
    have := (rep_psiM (ε := ε) (Pi.single 0 1)).1
    simpa [vecBits_single] using this
  refine ⟨permOfArr (deg ε) (lWord ε w), (memL_iff hrep.1).1 hlL, fun x hx => ?_, fun e => ?_⟩
  · by_cases hx1 : x = 1
    · rw [hx1, mul_one, mul_inv_cancel]
      exact one_mem _
    · obtain ⟨i, hi, rfl⟩ := exists_SP (hAU hx)
      rcases hlA i hi with h | ⟨k, hk, heq, hksel⟩
      · exact absurd ((hsel hi).2 ⟨hx, hx1⟩) (by simpa using h)
      · have e1 := eq_of_eqA (rep_compA (rep_compA hrep.1 (rep_SP hi).1) hrep.2) (rep_SP hk).1 heq
        rw [e1]
        exact ((hsel hk).1 hksel).1
  · have := (eqA_iff (t := conjA (deg ε) (lWord ε w) (psiT ε 1))
      (rep_compA (rep_compA hrep.1 ha) hrep.2) ha).2 e
    rw [this] at hla
    exact absurd hla (by decide)

end CFSG.EvenSmallLie.OmegaEight.Stage1.Model
