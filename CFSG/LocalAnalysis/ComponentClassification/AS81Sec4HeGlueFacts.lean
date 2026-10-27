module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeGlueTests
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeModelsFactsC
import all CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeModels

public section

namespace CFSG.ComponentClassification.AS81.HeTri

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.Monster.B.Fischer CFSG.ComponentClassification.AS81.HeSylow
open CFSG.ComponentClassification.AS81.Hexa CFSG.ComponentClassification.AS81.HePres.Native

section Words

variable {H : Type*} [Group H]

@[expose] def wval (g : ℕ → H) (w : List ℕ) : H :=
  (w.map fun l => if l % 2 = 0 then g (l / 2) else (g (l / 2))⁻¹).prod

theorem wval_nil (g : ℕ → H) : wval g [] = 1 := rfl

theorem wval_cons (g : ℕ → H) (l : ℕ) (w : List ℕ) :
    wval g (l :: w) = (if l % 2 = 0 then g (l / 2) else (g (l / 2))⁻¹) * wval g w := by
  simp only [wval, List.map_cons, List.prod_cons]

theorem map_wval {K : Type*} [Group K] (f : H →* K) (g : ℕ → H) (w : List ℕ) :
    f (wval g w) = wval (fun k => f (g k)) w := by
  induction w with
  | nil => simp [wval]
  | cons l w ih =>
    rw [wval_cons, wval_cons, map_mul, ih]
    split_ifs <;> simp

theorem wval_congr {g g' : ℕ → H} {w : List ℕ} (h : ∀ l ∈ w, g (l / 2) = g' (l / 2)) :
    wval g w = wval g' w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [wval_cons, wval_cons, h l List.mem_cons_self,
      ih fun l' hl' => h l' (List.mem_cons_of_mem l hl')]

theorem wval_mem {S : Subgroup H} {g : ℕ → H} {w : List ℕ} (h : ∀ l ∈ w, g (l / 2) ∈ S) :
    wval g w ∈ S := by
  induction w with
  | nil => exact S.one_mem
  | cons l w ih =>
    rw [wval_cons]
    refine S.mul_mem ?_ (ih fun l' hl' => h l' (List.mem_cons_of_mem l hl'))
    split_ifs
    · exact h l List.mem_cons_self
    · exact S.inv_mem (h l List.mem_cons_self)

theorem wval_conj (c : H) (g : ℕ → H) (w : List ℕ) :
    wval (fun k => c * g k * c⁻¹) w = c * wval g w * c⁻¹ := by
  simpa using (map_wval (MulAut.conj c).toMonoidHom g w).symm

end Words

section Arrays

variable {n : ℕ}

noncomputable abbrev permsL (n : ℕ) (gs : List (Array ℕ)) (k : ℕ) : Equiv.Perm (Fin n) :=
  permOfArr n (gs.getD k #[])

theorem rep_letterA {gs : List (Array ℕ)} (hv : ∀ a ∈ gs, validA n a = true) {l : ℕ}
    (hl : l / 2 < gs.length) :
    Rep n (letterA n gs l)
      (if l % 2 = 0 then permsL n gs (l / 2) else (permsL n gs (l / 2))⁻¹) := by
  have he : gs.getD (l / 2) (idA n) = gs[l / 2] := List.getD_eq_getElem _ _ hl
  have he' : gs.getD (l / 2) #[] = gs[l / 2] := List.getD_eq_getElem _ _ hl
  have hva := hv _ (List.getElem_mem hl)
  unfold letterA permsL
  rw [he, he']
  split_ifs
  · exact rep_of_validA hva
  · exact rep_inv_of_validA hva

theorem rep_evalW {gs : List (Array ℕ)} (hv : ∀ a ∈ gs, validA n a = true) {w : List ℕ}
    (hw : ∀ l ∈ w, l / 2 < gs.length) : Rep n (evalW n gs w) (wval (permsL n gs) w) := by
  have key : ∀ (w : List ℕ), (∀ l ∈ w, l / 2 < gs.length) →
      ∀ (acc : Array ℕ) (A : Equiv.Perm (Fin n)), Rep n acc A →
        Rep n (w.foldl (fun acc l => compA n acc (letterA n gs l)) acc)
          (A * wval (permsL n gs) w) := by
    intro w
    induction w with
    | nil => intro _ acc A hA; simpa [wval] using hA
    | cons l w ih =>
      intro hw acc A hA
      rw [List.foldl_cons, wval_cons, ← mul_assoc]
      exact ih (fun l' hl' => hw l' (List.mem_cons_of_mem l hl')) _ _
        (rep_compA hA (rep_letterA hv (hw l List.mem_cons_self)))
  simpa [evalW] using key w hw (idA n) 1 rep_idA

theorem relsOK_iff {gs : List (Array ℕ)} (hv : ∀ a ∈ gs, validA n a = true)
    {rels : List (List ℕ)} (hr : ∀ r ∈ rels, ∀ l ∈ r, l / 2 < gs.length) :
    relsOK n gs rels = true ↔ ∀ r ∈ rels, wval (permsL n gs) r = 1 := by
  rw [relsOK, List.all_eq_true]
  exact forall₂_congr fun r hr' => eqA_iff (rep_evalW hv (hr r hr')) rep_idA

theorem isOrd12_iff {a : Array ℕ} {A : Equiv.Perm (Fin n)} (ha : Rep n a A) :
    isOrd12 n a = true ↔ A ^ 12 = 1 ∧ A ^ 6 ≠ 1 ∧ A ^ 4 ≠ 1 := by
  have e12 := eqA_iff (rep_powN ha 12) rep_idA
  have e6 := eqA_iff (rep_powN ha 6) rep_idA
  have e4 := eqA_iff (rep_powN ha 4) rep_idA
  rw [isOrd12, Bool.and_eq_true, Bool.and_eq_true, e12, Bool.not_eq_true', Bool.not_eq_true',
    ← Bool.not_eq_true, ← Bool.not_eq_true, e6, e4, and_assoc]

end Arrays

section Count

variable {n : ℕ} {ps : List ℕ} {gs : List (Array ℕ)} {m : ℕ}

theorem length_eltsK (h : enumCheckK n ps gs m = true) : (eltsK n ps gs m).length = m := by
  simp only [enumCheckK, Bool.and_eq_true, beq_iff_eq] at h
  simpa [eltsK] using h.2

theorem length_filter_eq_ncard (hps : ∀ p ∈ ps, p < n) (h : enumCheckK n ps gs m = true)
    {P : Array ℕ → Bool} {S : Set (Equiv.Perm (Fin n))}
    (hPS : ∀ t ∈ eltsK n ps gs m, P t = true ↔ permOfArr n t ∈ S) :
    ((eltsK n ps gs m).filter P).length = ((grpN n gs : Set (Equiv.Perm (Fin n))) ∩ S).ncard := by
  set L := eltsK n ps gs m
  have h1 : ((grpN n gs : Set (Equiv.Perm (Fin n))) ∩ S).ncard ≤ (L.filter P).length := by
    rw [← Nat.card_coe_set_eq]
    refine card_le_length fun x hx => ?_
    obtain ⟨t, ht, hr⟩ := (mem_grpN_iffK hps h).1 hx.1
    refine ⟨t, List.mem_filter.2 ⟨ht, (hPS t ht).2 ?_⟩, hr⟩
    rw [permOfArr_eq_of_rep hr]
    exact hx.2
  have h2 : ((grpN n gs : Set (Equiv.Perm (Fin n))) \ S).ncard ≤
      (L.filter fun t => !P t).length := by
    rw [← Nat.card_coe_set_eq]
    refine card_le_length fun x hx => ?_
    obtain ⟨t, ht, hr⟩ := (mem_grpN_iffK hps h).1 hx.1
    refine ⟨t, List.mem_filter.2 ⟨ht, ?_⟩, hr⟩
    rw [Bool.not_eq_true', ← Bool.not_eq_true, hPS t ht, permOfArr_eq_of_rep hr]
    exact hx.2
  have h3 := Set.ncard_inter_add_ncard_sdiff_eq_ncard (grpN n gs : Set (Equiv.Perm (Fin n))) S
    (Set.toFinite _)
  have h4 : (grpN n gs : Set (Equiv.Perm (Fin n))).ncard = m := by
    rw [← Nat.card_coe_set_eq]
    exact card_grpNK hps h
  have h5 := List.length_eq_length_filter_add (l := L) P
  have h6 : L.length = m := length_eltsK h
  omega

theorem card_inf_centralizer_congr {G K : Type*} [Group G] [Group K] {A : Subgroup G}
    {B : Subgroup K} (e : ↥A ≃* ↥B) (x : ↥A) :
    Nat.card ↥(A ⊓ centralizer {(x : G)}) = Nat.card ↥(B ⊓ centralizer {(e x : K)}) := by
  have hc : ∀ y : ↥A, (y : G) * x = x * y ↔ ((e y : K) * e x = e x * e y) := by
    intro y
    rw [← coe_mul, ← coe_mul, Subtype.coe_inj, ← coe_mul, ← coe_mul, Subtype.coe_inj, ← map_mul,
      ← map_mul, e.injective.eq_iff]
  refine Nat.card_congr
    { toFun := fun y => ⟨e ⟨y, y.2.1⟩, (e ⟨y, y.2.1⟩).2,
        mem_centralizer_singleton_iff.mpr ((hc ⟨y, y.2.1⟩).1
          (mem_centralizer_singleton_iff.mp y.2.2))⟩
      invFun := fun y => ⟨e.symm ⟨y, y.2.1⟩, (e.symm ⟨y, y.2.1⟩).2,
        mem_centralizer_singleton_iff.mpr ((hc (e.symm ⟨y, y.2.1⟩)).2 (by
          rw [MulEquiv.apply_symm_apply]
          exact mem_centralizer_singleton_iff.mp y.2.2))⟩
      left_inv := fun y => by
        apply Subtype.ext
        simp
      right_inv := fun y => by
        apply Subtype.ext
        simp }

end Count

section Lists

theorem getD_mem {α : Type*} {L : List α} {k : ℕ} (hk : k < L.length) (d : α) : L.getD k d ∈ L := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

theorem forall_mem_getD {α : Type*} {L : List (List α)} {P : α → Prop}
    (h : ∀ w ∈ L, ∀ l ∈ w, P l) (k : ℕ) : ∀ l ∈ L.getD k [], P l := by
  intro l hl
  by_cases hk : k < L.length
  · exact h _ (getD_mem hk []) l hl
  · rw [List.getD_eq_default _ _ (not_lt.1 hk)] at hl
    simp at hl

theorem toList_getD {α : Type*} (a : Array α) (k : ℕ) (d : α) : a.toList.getD k d = a.getD k d := by
  simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]

theorem getD_mem_toList {α : Type*} {a : Array α} {k : ℕ} (hk : k < a.size) (d : α) :
    a.getD k d ∈ a.toList := by
  rw [← toList_getD]
  exact getD_mem (by simpa using hk) d

end Lists

theorem heGlueCheck_parts (hg : heGlueCheck = true) :
    heCheckValid = true ∧ heCheckRange = true ∧ heCheckSrc = true ∧ heCheckClassB = true ∧
      heCheckClassC = true ∧ heCheckRepF = true ∧ heCheckNormB = true ∧ heCheckFus = true ∧
      heCheckPi = true ∧ heCheckKer = true ∧ heCheckMem = true ∧ heCheckZ = true ∧
      heCheckGen = true := by
  simp only [heGlueCheck, Bool.and_eq_true, and_assoc] at hg
  exact hg

section Parts

variable (hg : heGlueCheck = true)
include hg

theorem heCheckValid_parts :
    (∀ a ∈ heRepE ++ heRepF ++ heConjF ++ hePiEArrs.toList ++ hePiFArrs.toList,
      validA 64 a = true) ∧
    (∀ a ∈ (hePiCArrs false).toList ++ (hePiCArrs true).toList, validA 32 a = true) ∧
    validA 64 (idA 64) = true ∧ validA 64 hexaT0 = true ∧
    validA 64 (conjA 64 hexaT0 (hePiFArrs.getD 6 #[])) = true ∧
    validA 64 (conjA 64 hexaT0 (hePiFArrs.getD 7 #[])) = true ∧ heRepE.length = 8 ∧
    heRepF.length = 8 ∧ heConjF.length = 4 ∧ hePiEArrs.size = 8 ∧ hePiFArrs.size = 8 ∧
    (hePiCArrs false).size = 8 ∧ (hePiCArrs true).size = 8 := by
  have h := (heGlueCheck_parts hg).1
  simp only [heCheckValid, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, and_assoc] at h
  exact h

theorem heCheckRange_parts :
    (∀ w ∈ heRelsP ++ heWordsE ++ heWordsF ++ heWordsBE ++ heWordsBF ++ heWit, ∀ l ∈ w, l < 4) ∧
    (∀ w ∈ hePiRels23Codes, ∀ l ∈ w, l < 8 ∨ l / 2 = 6 ∨ l / 2 = 7) ∧
    (∀ w ∈ heGenWordsC0 ++ heGenWordsC1, ∀ l ∈ w, l < 12) ∧
    (∀ w ∈ heGenWordsT ++ heGenWordsM ++ heGenWordsR, ∀ l ∈ w, l < 10 ∨ l / 2 = 6 ∨ l / 2 = 7) := by
  have h := (heGlueCheck_parts hg).2.1
  simp only [heCheckRange, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq, or_assoc, and_assoc] at h
  exact h

theorem valid64_of_mem {a : Array ℕ} (ha : a ∈ heRepE ∨ a ∈ heRepF ∨ a ∈ heConjF ∨
    a ∈ hePiEArrs.toList ∨ a ∈ hePiFArrs.toList) : validA 64 a = true :=
  (heCheckValid_parts hg).1 a (by simp only [List.mem_append]; tauto)

theorem valid_repE {i k : ℕ} (hi : i < 4) (hk : k < 2) : validA 64 (repE i k) = true := by
  have hl := (heCheckValid_parts hg).2.2.2.2.2.2.1
  exact valid64_of_mem hg (Or.inl (getD_mem (by omega) _))

theorem valid_repF {i k : ℕ} (hi : i < 4) (hk : k < 2) : validA 64 (repF i k) = true := by
  have hl := (heCheckValid_parts hg).2.2.2.2.2.2.2.1
  exact valid64_of_mem hg (Or.inr (Or.inl (getD_mem (by omega) _)))

theorem valid_conjF {j : ℕ} (hj : j < 4) : validA 64 (heConjF.getD j #[]) = true := by
  have hl := (heCheckValid_parts hg).2.2.2.2.2.2.2.2.1
  exact valid64_of_mem hg (Or.inr (Or.inr (Or.inl (getD_mem (by omega) _))))

theorem valid_piEArr {k : ℕ} (hk : k < 8) : validA 64 (hePiEArrs.getD k #[]) = true := by
  have hl := (heCheckValid_parts hg).2.2.2.2.2.2.2.2.2.1
  exact valid64_of_mem hg (Or.inr (Or.inr (Or.inr (Or.inl (getD_mem_toList (by omega) _)))))

theorem valid_piFArr {k : ℕ} (hk : k < 8) : validA 64 (hePiFArrs.getD k #[]) = true := by
  have hl := (heCheckValid_parts hg).2.2.2.2.2.2.2.2.2.2.1
  exact valid64_of_mem hg (Or.inr (Or.inr (Or.inr (Or.inr (getD_mem_toList (by omega) _)))))

theorem valid_piCArr (s : Bool) {k : ℕ} (hk : k < 8) :
    validA 32 ((hePiCArrs s).getD k #[]) = true := by
  have hl0 := (heCheckValid_parts hg).2.2.2.2.2.2.2.2.2.2.2.1
  have hl1 := (heCheckValid_parts hg).2.2.2.2.2.2.2.2.2.2.2.2
  refine (heCheckValid_parts hg).2.1 _ (List.mem_append.2 ?_)
  cases s
  · exact Or.inl (getD_mem_toList (by omega) _)
  · exact Or.inr (getD_mem_toList (by omega) _)

theorem valid_idA : validA 64 (idA 64) = true := (heCheckValid_parts hg).2.2.1

theorem valid_t0 : validA 64 hexaT0 = true := (heCheckValid_parts hg).2.2.2.1

theorem valid_yF' : validA 64 (conjA 64 hexaT0 (hePiFArrs.getD 7 #[])) = true :=
  (heCheckValid_parts hg).2.2.2.2.2.1

end Parts

theorem map_eq_wval {H K : Type*} [Group H] [Group K] {S : Subgroup H} (f : ↥S →* K)
    {g : ℕ → H} {g' : ℕ → K} {w : List ℕ}
    (hg : ∀ l ∈ w, ∃ h : g (l / 2) ∈ S, f ⟨g (l / 2), h⟩ = g' (l / 2)) {x : ↥S}
    (hx : (x : H) = wval g w) : f x = wval g' w := by
  induction w generalizing x with
  | nil =>
    have : x = 1 := Subtype.ext hx
    rw [this, map_one, wval_nil]
  | cons l w ih =>
    obtain ⟨hl, hfl⟩ := hg l List.mem_cons_self
    have hw : ∀ l' ∈ w, ∃ h : g (l' / 2) ∈ S, f ⟨g (l' / 2), h⟩ = g' (l' / 2) :=
      fun l' hl' => hg l' (List.mem_cons_of_mem l hl')
    have hmem : wval g w ∈ S := wval_mem fun l' hl' => (hw l' hl').1
    have hx' : x = (if l % 2 = 0 then (⟨g (l / 2), hl⟩ : ↥S) else (⟨g (l / 2), hl⟩ : ↥S)⁻¹) *
        ⟨wval g w, hmem⟩ := by
      apply Subtype.ext
      rw [hx, wval_cons, coe_mul]
      split_ifs <;> rfl
    rw [hx', map_mul, ih (x := ⟨wval g w, hmem⟩) hw rfl, wval_cons]
    split_ifs
    · rw [hfl]
    · rw [map_inv, hfl]

theorem wval_eq_one_map {H K : Type*} [Group H] [Group K] {S : Subgroup H} (f : ↥S →* K)
    {g : ℕ → H} {g' : ℕ → K} {w : List ℕ}
    (hg : ∀ l ∈ w, ∃ h : g (l / 2) ∈ S, f ⟨g (l / 2), h⟩ = g' (l / 2)) (h1 : wval g w = 1) :
    wval g' w = 1 := by
  rw [← map_eq_wval f hg (x := 1) (by rw [h1]; rfl), map_one]

section Conj

variable {G : Type*} [Group G] {K : Subgroup G}

theorem isConj_conj_iff {c : G} (hc : c ∈ K) (a b : G) :
    (∃ d ∈ K, d * (c * a * c⁻¹) * d⁻¹ = c * b * c⁻¹) ↔ ∃ d ∈ K, d * a * d⁻¹ = b := by
  constructor
  · rintro ⟨d, hd, he⟩
    refine ⟨c⁻¹ * d * c, K.mul_mem (K.mul_mem (K.inv_mem hc) hd) hc, ?_⟩
    have : c⁻¹ * (d * (c * a * c⁻¹) * d⁻¹) * c = c⁻¹ * (c * b * c⁻¹) * c := by rw [he]
    simpa [mul_assoc] using this
  · rintro ⟨d, hd, rfl⟩
    exact ⟨c * d * c⁻¹, K.mul_mem (K.mul_mem hc hd) (K.inv_mem hc), by group⟩

theorem isConj_map_iff (u : ↥K ≃* ↥K) (a b : ↥K) :
    (∃ d ∈ K, d * (u a : G) * d⁻¹ = u b) ↔ ∃ d ∈ K, d * (a : G) * d⁻¹ = b := by
  have key : ∀ (v : ↥K ≃* ↥K) (a b : ↥K), (∃ d ∈ K, d * (a : G) * d⁻¹ = b) →
      ∃ d ∈ K, d * (v a : G) * d⁻¹ = v b := by
    rintro v a b ⟨d, hd, he⟩
    have he' : (⟨d, hd⟩ : ↥K) * a * (⟨d, hd⟩ : ↥K)⁻¹ = b := Subtype.ext he
    refine ⟨v ⟨d, hd⟩, (v ⟨d, hd⟩).2, ?_⟩
    rw [← he', map_mul, map_mul, map_inv]
    rfl
  refine ⟨fun h => ?_, key u a b⟩
  simpa using key u.symm (u a) (u b) h

end Conj

@[expose] def heGensC (s : Bool) : List (Array ℕ) := if s then heP13CGens else heP12CGens

theorem heP12C_eq (s : Bool) : heP12C s = grpN 32 (heGensC s) := by
  cases s <;> rfl

noncomputable abbrev piC (s : Bool) (k : ℕ) : Equiv.Perm (Fin 32) :=
  permOfArr 32 ((hePiCArrs s).getD k #[])

noncomputable abbrev piE (k : ℕ) : Equiv.Perm (Fin 64) := permOfArr 64 (hePiEArrs.getD k #[])

noncomputable abbrev piF (k : ℕ) : Equiv.Perm (Fin 64) := permOfArr 64 (hePiFArrs.getD k #[])

noncomputable abbrev gC (s : Bool) : ℕ → Equiv.Perm (Fin 32) := permsL 32 (heGensC s)

noncomputable abbrev rE (i : ℕ) : ℕ → Equiv.Perm (Fin 64) := permsL 64 (pairE i)

noncomputable abbrev rF (i : ℕ) : ℕ → Equiv.Perm (Fin 64) := permsL 64 (pairF i)

@[expose] def wordsB (s : Bool) : List (List ℕ) := if s then heWordsBF else heWordsBE

theorem permsL_toList {n : ℕ} (a : Array (Array ℕ)) (k : ℕ) :
    permsL n a.toList k = permOfArr n (a.getD k #[]) := by
  rw [permsL, toList_getD]

theorem length_heGensC (s : Bool) : (heGensC s).length = 2 := by cases s <;> rfl

theorem piIdx_of_lt {c k : ℕ} (hk : k < 4) : piIdx c k = k := by
  simp [piIdx, hk]

theorem exists_witIdx : ∀ i < 4, ∀ j < 4, ¬(i = 0 ∧ j = 0) →
    ∃ k < 15, heWitIdx.getD k (0, 0) = (i, j) := by decide

theorem heSigmaF_getD : ∀ j < 4, heSigmaF.getD j 0 = j := by decide

theorem length_heBCGens : heBCGens.length = 4 := rfl

section Model

variable (hm : heModelCheck = true) (hg : heGlueCheck = true)

include hm in
theorem enum_gensC (s : Bool) : enumCheckK 32 base32 (heGensC s) 3072 = true := by
  cases s
  · exact enum_P0 hm
  · exact enum_P1 hm

include hm in
theorem valid_gensC (s : Bool) : ∀ a ∈ heGensC s, validA 32 a = true :=
  fun _ ha => validA_of_mem_gensK (enum_gensC hm s) ha

theorem gC_mem (s : Bool) {k : ℕ} (hk : k < 2) : gC s k ∈ heP12C s := by
  rw [heP12C_eq]
  exact gen_mem_grpN (getD_mem (by rw [length_heGensC]; exact hk) _)

include hg in
theorem valid_pairE {i : ℕ} (hi : i < 4) : ∀ a ∈ pairE i, validA 64 a = true := by
  intro a ha
  simp only [pairE, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact valid_repE hg (k := 0) hi (by norm_num)
  · exact valid_repE hg (k := 1) hi (by norm_num)

include hg in
theorem valid_pairF {i : ℕ} (hi : i < 4) : ∀ a ∈ pairF i, validA 64 a = true := by
  intro a ha
  simp only [pairF, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact valid_repF hg (k := 0) hi (by norm_num)
  · exact valid_repF hg (k := 1) hi (by norm_num)

theorem heP23L_eq : heP23L = eltsK 64 base64 heP23Gens 9216 := rfl

end Model

section EnumCount

variable {n : ℕ} {ps : List ℕ} {gs : List (Array ℕ)} {m : ℕ}

theorem card_inf_centralizer_eq_length (hps : ∀ p ∈ ps, p < n) (h : enumCheckK n ps gs m = true)
    {a : Array ℕ} (ha : validA n a = true) :
    Nat.card ↥(grpN n gs ⊓ centralizer {permOfArr n a}) =
      ((eltsK n ps gs m).filter (commN n a)).length := by
  have hPS : ∀ t ∈ eltsK n ps gs m, commN n a t = true ↔
      permOfArr n t ∈ (centralizer {permOfArr n a} : Set (Equiv.Perm (Fin n))) := by
    intro t ht
    rw [commN_iff (rep_of_validA ha) (rep_of_validA (validA_of_mem_eltsK hps h ht)),
      SetLike.mem_coe, mem_centralizer_singleton_iff, eq_comm]
  rw [length_filter_eq_ncard hps h hPS, ← coe_inf, ← Nat.card_coe_set_eq]
  rfl

end EnumCount

section Source

variable (hm : heModelCheck = true) (hg : heGlueCheck = true)
include hm hg

omit hm in
theorem heCheckSrc_parts :
    relsOK 32 (heGensC false) heRelsP = true ∧ relsOK 32 (heGensC true) heRelsP = true ∧
      isOrd12 32 ((heGensC false).getD 1 #[]) = true ∧
      isOrd12 32 ((heGensC true).getD 1 #[]) = true ∧
      ((eltsK 32 base32 (heGensC false) 3072).filter
        (commN 32 ((heGensC false).getD 1 #[]))).length = 12 ∧
      ((eltsK 32 base32 (heGensC true) 3072).filter
        (commN 32 ((heGensC true).getD 1 #[]))).length = 12 ∧
      (∀ a ∈ heRepE, inLN 64 (eltsK 64 base64 heP12Gens 3072) a = true) ∧
      (∀ a ∈ heRepF, inLN 64 (eltsK 64 base64 heP12Gens 3072) a = true) := by
  have h := (heGlueCheck_parts hg).2.2.1
  simp only [heCheckSrc, heP0L_eq, heP1L_eq, heP12L_eq, Bool.and_eq_true, List.all_eq_true,
    beq_iff_eq, and_assoc] at h
  exact h

omit hm in
theorem range_rels : ∀ r ∈ heRelsP, ∀ l ∈ r, l / 2 < 2 := fun r hr l hl => by
  have := (heCheckRange_parts hg).1 r (by simp [hr]) l hl
  omega

theorem src_rels (s : Bool) : ∀ r ∈ heRelsP, wval (gC s) r = 1 := by
  have hr : relsOK 32 (heGensC s) heRelsP = true := by
    cases s
    · exact (heCheckSrc_parts hg).1
    · exact (heCheckSrc_parts hg).2.1
  refine (relsOK_iff (valid_gensC hm s) ?_).1 hr
  intro r hr' l hl
  rw [length_heGensC]
  exact range_rels hg r hr' l hl

theorem src_ord (s : Bool) : gC s 1 ^ 12 = 1 ∧ gC s 1 ^ 6 ≠ 1 ∧ gC s 1 ^ 4 ≠ 1 := by
  have hv := valid_gensC hm s _ (getD_mem (k := 1) (by rw [length_heGensC]; norm_num) #[])
  refine (isOrd12_iff (rep_of_validA hv)).1 ?_
  cases s
  · exact (heCheckSrc_parts hg).2.2.1
  · exact (heCheckSrc_parts hg).2.2.2.1

theorem src_cent (s : Bool) : Nat.card ↥(heP12C s ⊓ centralizer {gC s 1}) = 12 := by
  have hv := valid_gensC hm s _ (getD_mem (k := 1) (by rw [length_heGensC]; norm_num) #[])
  rw [heP12C_eq, card_inf_centralizer_eq_length base32_lt (enum_gensC hm s) hv]
  cases s
  · exact (heCheckSrc_parts hg).2.2.2.2.1
  · exact (heCheckSrc_parts hg).2.2.2.2.2.1

end Source

section Classify

noncomputable def imgC {s : Bool} (φ : ↥(heP12C s) →* ↥heP12) (k : ℕ) : Equiv.Perm (Fin 64) :=
  if hk : k < 2 then (φ ⟨gC s k, gC_mem s hk⟩ : Equiv.Perm (Fin 64)) else 1

theorem map_imgC {s : Bool} (φ : ↥(heP12C s) →* ↥heP12) {w : List ℕ} (hw : ∀ l ∈ w, l / 2 < 2)
    {x : ↥(heP12C s)} (hx : (x : Equiv.Perm (Fin 32)) = wval (gC s) w) :
    (φ x : Equiv.Perm (Fin 64)) = wval (imgC φ) w :=
  map_eq_wval (heP12.subtype.comp φ) (fun l hl => ⟨gC_mem s (hw l hl), by
    rw [imgC, dite_eq_left (hw l hl)]
    rfl⟩) hx

theorem permsL_pair {n : ℕ} {b c : Array ℕ} {B C : Equiv.Perm (Fin n)} (hb : Rep n b B)
    (hc : Rep n c C) {G : ℕ → Equiv.Perm (Fin n)} (h0 : G 0 = B) (h1 : G 1 = C) {w : List ℕ}
    (hw : ∀ l ∈ w, l / 2 < 2) : wval (permsL n [b, c]) w = wval G w := by
  refine wval_congr fun l hl => ?_
  have h2 := hw l hl
  rcases (by omega : l / 2 = 0 ∨ l / 2 = 1) with h | h <;> rw [h]
  · rw [h0, permsL, show [b, c].getD 0 #[] = b from rfl, permOfArr_eq_of_rep hb]
  · rw [h1, permsL, show [b, c].getD 1 #[] = c from rfl, permOfArr_eq_of_rep hc]

theorem valid_pair {n : ℕ} {b c : Array ℕ} (hb : validA n b = true) (hc : validA n c = true) :
    ∀ a ∈ [b, c], validA n a = true := by
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact hb
  · exact hc

theorem rE_eq (i k : ℕ) (hk : k < 2) : rE i k = permOfArr 64 (repE i k) := by
  interval_cases k <;> rfl

theorem rF_eq (i k : ℕ) (hk : k < 2) : rF i k = permOfArr 64 (repF i k) := by
  interval_cases k <;> rfl

variable (hm : heModelCheck = true) (hg : heGlueCheck = true) (hF : HexaFacts)
include hm hg hF

theorem exists_conj_pair {s : Bool} (φ : ↥(heP12C s) →* ↥heP12) (hφ : Function.Injective φ) :
    ∃ i < 4, ∃ p ∈ heP12, ∃ p' ∈ heP12, ∀ k < 2,
      imgC φ k = p * rE i k * p⁻¹ ∧ imgC φ k = p' * rF i k * p'⁻¹ := by
  have hP := P12_eq hm hF
  have hE := hP12 hm
  have hEL : heP12L = eltsK 64 base64 heP12Gens 3072 := rfl
  have himg : ∀ k, imgC φ k ∈ grpN 64 heP12Gens := by
    intro k
    unfold imgC
    split_ifs with hk
    · rw [← hP]
      exact (φ _).2
    · exact one_mem _
  obtain ⟨a0, -, hr0, hv0⟩ := exists_rep_of_memK base64_lt hE (himg 0)
  obtain ⟨a1, ha1, hr1, hv1⟩ := exists_rep_of_memK base64_lt hE (himg 1)
  have hrange : ∀ r ∈ heRelsP, ∀ l ∈ r, l / 2 < [a0, a1].length := range_rels hg
  have hrelsImg : ∀ r ∈ heRelsP, wval (imgC φ) r = 1 := by
    intro r hr
    have h1 := map_imgC φ (x := 1) (range_rels hg r hr) (by rw [src_rels hm hg s r hr]; rfl)
    rw [← h1, map_one]
    rfl
  set x1 : ↥(heP12C s) := ⟨gC s 1, gC_mem s (by norm_num)⟩ with hx1
  have himg1 : imgC φ 1 = (φ x1 : Equiv.Perm (Fin 64)) := dite_eq_left (by norm_num)
  have hpow : ∀ k, imgC φ 1 ^ k = 1 ↔ gC s 1 ^ k = 1 := by
    intro k
    rw [himg1, ← SubmonoidClass.coe_pow, ← map_pow, OneMemClass.coe_eq_one, map_eq_one_iff φ hφ,
      ← OneMemClass.coe_eq_one, SubmonoidClass.coe_pow]
  have hord : isOrd12 64 a1 = true := by
    obtain ⟨h12, h6, h4⟩ := src_ord hm hg s
    rw [isOrd12_iff hr1]
    exact ⟨(hpow 12).2 h12, fun h => h6 ((hpow 6).1 h), fun h => h4 ((hpow 4).1 h)⟩
  have hbij : Function.Bijective φ :=
    hφ.bijective_of_nat_card_le (by rw [card_P12_of hm hF, card_P12C_of hm s])
  have hcard := card_inf_centralizer_congr (MulEquiv.ofBijective φ hbij) x1
  have hlen : (heP12L.filter (commN 64 a1)).length = 12 := by
    rw [hEL, ← card_inf_centralizer_eq_length base64_lt hE hv1, permOfArr_eq_of_rep hr1, ← hP,
      himg1]
    rw [← src_cent hm hg s, hcard]
    rfl
  obtain ⟨i, hi, p1, hp1, hep1⟩ : ∃ i < 4, ∃ p1 ∈ heP12L,
      eqA 64 (conjA 64 p1 (repE i 1)) a1 = true := by
    have hB := (heGlueCheck_parts hg).2.2.2.1
    rw [heCheckClassB, List.all_eq_true] at hB
    have hb := hB a1 ha1
    rw [hord, hlen] at hb
    simpa [List.any_eq_true] using hb
  have hvp1 := validA_of_mem_eltsK base64_lt hE (hEL ▸ hp1)
  set P1 := permOfArr 64 p1 with hP1
  have hP1m : P1 ∈ grpN 64 heP12Gens := perm_mem_of_mem_eltsK base64_lt hE (hEL ▸ hp1)
  have heq1 : P1 * rE i 1 * P1⁻¹ = imgC φ 1 := by
    rw [rE_eq i 1 (by norm_num)]
    exact eq_of_eqA (rep_conjA hvp1 (rep_of_validA (valid_repE hg hi (by norm_num)))) hr1 hep1
  have hbm : P1⁻¹ * imgC φ 0 * P1 ∈ grpN 64 heP12Gens :=
    mul_mem (mul_mem (inv_mem hP1m) (himg 0)) hP1m
  obtain ⟨b, hb, hrb, hvb⟩ := exists_rep_of_memK base64_lt hE hbm
  have hrelsB : relsOK 64 [b, repE i 1] heRelsP = true := by
    have hvR := valid_repE hg (k := 1) hi (by norm_num)
    rw [relsOK_iff (valid_pair hvb hvR) (range_rels hg)]
    intro r hr
    rw [permsL_pair hrb (rep_of_validA hvR) (G := fun k => P1⁻¹ * imgC φ k * P1⁻¹⁻¹) (by simp)
      (by rw [← heq1, ← rE_eq i 1 (by norm_num)]; group) (range_rels hg r hr), wval_conj,
      hrelsImg r hr]
    group
  obtain ⟨i', hi', c, hc, hec0, hec1⟩ : ∃ i' < 4, ∃ c ∈ heP12L,
      eqA 64 (conjA 64 c (repE i' 0)) b = true ∧
        eqA 64 (conjA 64 c (repE i' 1)) (repE i 1) = true := by
    have hC := (heGlueCheck_parts hg).2.2.2.2.1
    rw [heCheckClassC, List.all_eq_true] at hC
    have hc := List.all_eq_true.1 (hC i (List.mem_range.2 hi)) b (hEL ▸ hb)
    rw [hrelsB] at hc
    simpa [List.any_eq_true] using hc
  have hvc := validA_of_mem_eltsK base64_lt hE (hEL ▸ hc)
  set C := permOfArr 64 c with hC
  have hCm : C ∈ grpN 64 heP12Gens := perm_mem_of_mem_eltsK base64_lt hE (hEL ▸ hc)
  have hc0 : C * rE i' 0 * C⁻¹ = P1⁻¹ * imgC φ 0 * P1 := by
    rw [rE_eq i' 0 (by norm_num)]
    exact eq_of_eqA (rep_conjA hvc (rep_of_validA (valid_repE hg hi' (by norm_num)))) hrb hec0
  have hc1 : C * rE i' 1 * C⁻¹ = rE i 1 := by
    rw [rE_eq i' 1 (by norm_num), rE_eq i 1 (by norm_num)]
    exact eq_of_eqA (rep_conjA hvc (rep_of_validA (valid_repE hg hi' (by norm_num))))
      (rep_of_validA (valid_repE hg hi (by norm_num))) hec1
  obtain ⟨d, hd, hed0, hed1⟩ : ∃ d ∈ grpN 64 heP12Gens, d * rE i' 0 * d⁻¹ = rF i' 0 ∧
      d * rE i' 1 * d⁻¹ = rF i' 1 := by
    have hR := (heGlueCheck_parts hg).2.2.2.2.2.1
    rw [heCheckRepF, List.all_eq_true] at hR
    have hr := hR i' (List.mem_range.2 hi')
    rw [heSigmaF_getD i' hi'] at hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
    obtain ⟨⟨⟨-, hin⟩, he0⟩, he1⟩ := hr
    have hvd := valid_conjF hg hi'
    refine ⟨permOfArr 64 (heConjF.getD i' #[]), mem_of_inLNK base64_lt hE hin (rep_of_validA hvd),
      ?_, ?_⟩
    · rw [rE_eq i' 0 (by norm_num), rF_eq i' 0 (by norm_num)]
      exact eq_of_eqA (rep_conjA hvd (rep_of_validA (valid_repE hg hi' (by norm_num))))
        (rep_of_validA (valid_repF hg hi' (by norm_num))) he0
    · rw [rE_eq i' 1 (by norm_num), rF_eq i' 1 (by norm_num)]
      exact eq_of_eqA (rep_conjA hvd (rep_of_validA (valid_repE hg hi' (by norm_num))))
        (rep_of_validA (valid_repF hg hi' (by norm_num))) he1
  refine ⟨i', hi', P1 * C, hP ▸ mul_mem hP1m hCm, P1 * C * d⁻¹,
    hP ▸ mul_mem (mul_mem hP1m hCm) (inv_mem hd), fun k hk => ?_⟩
  have hk' : imgC φ k = P1 * C * rE i' k * (P1 * C)⁻¹ := by
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · calc imgC φ 0 = P1 * (P1⁻¹ * imgC φ 0 * P1) * P1⁻¹ := by group
        _ = P1 * (C * rE i' 0 * C⁻¹) * P1⁻¹ := by rw [hc0]
        _ = P1 * C * rE i' 0 * (P1 * C)⁻¹ := by group
    · calc imgC φ 1 = P1 * rE i 1 * P1⁻¹ := heq1.symm
        _ = P1 * (C * rE i' 1 * C⁻¹) * P1⁻¹ := by rw [hc1]
        _ = P1 * C * rE i' 1 * (P1 * C)⁻¹ := by group
  refine ⟨hk', ?_⟩
  have hd' : rE i' k = d⁻¹ * rF i' k * d := by
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · rw [← hed0]
      group
    · rw [← hed1]
      group
  rw [hk', hd']
  group

end Classify

section Fusion

variable (hm : heModelCheck = true) (hg : heGlueCheck = true)

include hg in
theorem range_pairWords {L : List (List ℕ)}
    (hL : ∀ w ∈ L, w ∈ heRelsP ++ heWordsE ++ heWordsF ++ heWordsBE ++ heWordsBF ++ heWit)
    (k : ℕ) : ∀ l ∈ L.getD k [], l / 2 < 2 := by
  refine forall_mem_getD (fun w hw l hl => ?_) k
  have := (heCheckRange_parts hg).1 w (hL w hw) l hl
  omega

theorem wordsB_sub (s : Bool) : ∀ w ∈ wordsB s, w ∈ heWordsBE ++ heWordsBF := by
  intro w hw
  cases s
  · exact List.mem_append_left _ hw
  · exact List.mem_append_right _ hw

include hg in
theorem range_wordsB (s : Bool) (k : ℕ) : ∀ l ∈ (wordsB s).getD k [], l / 2 < 2 :=
  range_pairWords hg (fun w hw => by
    have := wordsB_sub s w hw
    simp only [List.mem_append] at this ⊢
    tauto) k

theorem wordsB_getD_mem (s : Bool) {k : ℕ} (hk : k < 4) :
    (wordsB s).getD k [] ∈ heWordsBE ++ heWordsBF :=
  wordsB_sub s _ (getD_mem (by cases s <;> exact hk) _)

theorem length_pairE (i : ℕ) : (pairE i).length = 2 := rfl

theorem length_pairF (i : ℕ) : (pairF i).length = 2 := rfl

include hm hg in
theorem heBCGens_eq_wval (s : Bool) {k : ℕ} (hk : k < 4) :
    permOfArr 32 (heBCGens.getD k #[]) = wval (gC s) ((wordsB s).getD k []) := by
  have h := List.all_eq_true.1 (Bool.and_eq_true _ _ ▸ (heGlueCheck_parts hg).2.2.2.2.2.2.2.2.1).2
    k (List.mem_range.2 hk)
  rw [Bool.and_eq_true] at h
  have hr : ∀ l ∈ (wordsB s).getD k [], l / 2 < (heGensC s).length := by
    rw [length_heGensC]
    exact range_wordsB hg s k
  have he : eqA 32 (evalW 32 (heGensC s) ((wordsB s).getD k [])) (heBCGens.getD k #[]) = true := by
    cases s
    · exact h.1
    · exact h.2
  exact permOfArr_eq_of_rep (rep_of_eqA (rep_evalW (valid_gensC hm s) hr) he)

include hm hg in
theorem wvalB_mem {i : ℕ} (hi : i < 4) {w : List ℕ} (hw : w ∈ heWordsBE ++ heWordsBF) :
    wval (rE i) w ∈ heB0 ∧ wval (rF i) w ∈ heB0 := by
  have h := List.all_eq_true.1 (List.all_eq_true.1
    (Bool.and_eq_true _ _ ▸ (heGlueCheck_parts hg).2.2.2.2.2.2.1).2 i (List.mem_range.2 hi)) w hw
  rw [Bool.and_eq_true] at h
  have hr : ∀ l ∈ w, l / 2 < 2 := fun l hl => by
    have := (heCheckRange_parts hg).1 w (by simp only [List.mem_append] at hw ⊢; tauto) l hl
    omega
  exact ⟨mem_of_inLNK base64_lt (hB hm) h.1 (rep_evalW (valid_pairE hg hi) hr),
    mem_of_inLNK base64_lt (hB hm) h.2 (rep_evalW (valid_pairF hg hi) hr)⟩

include hm hg in
theorem mem_heB0_of_normalizer (hF : HexaFacts) {p : Equiv.Perm (Fin 64)} (hp : p ∈ heP12)
    (hpn : p ∈ normalizer (heB0 : Set (Equiv.Perm (Fin 64)))) : p ∈ heB0 := by
  have hcount := (Bool.and_eq_true _ _ ▸ (heGlueCheck_parts hg).2.2.2.2.2.2.1).1
  rw [beq_iff_eq] at hcount
  have hPS : ∀ t ∈ eltsK 64 base64 heP12Gens 3072,
      normsN 64 (eltsK 64 base64 heB0Gens 1024) heB0Gens t = true ↔
        permOfArr 64 t ∈ (normalizer (heB0 : Set (Equiv.Perm (Fin 64))) : Set _) := by
    intro t ht
    have hv := validA_of_mem_eltsK base64_lt (hP12 hm) ht
    exact ⟨mem_normalizer_of_normsN base64_lt (hB hm) hv,
      normsN_of_mem_normalizer base64_lt (hB hm) hv (rep_of_validA hv)⟩
  have hn := length_filter_eq_ncard base64_lt (hP12 hm) hPS
  rw [show eltsK 64 base64 heP12Gens 3072 = heP12L from rfl,
    show eltsK 64 base64 heB0Gens 1024 = heBL from rfl, hcount] at hn
  have hsub : (heB0 : Set (Equiv.Perm (Fin 64))) ⊆
      (grpN 64 heP12Gens : Set (Equiv.Perm (Fin 64))) ∩
        ((normalizer (heB0 : Set (Equiv.Perm (Fin 64))) : Subgroup _) :
          Set (Equiv.Perm (Fin 64))) := by
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, ← P12_eq hm hF]
      exact B0_le_of hm hF hx
    · exact le_normalizer hx
  have heq := Set.eq_of_subset_of_ncard_le hsub (by
    rw [← hn, ← Nat.card_coe_set_eq]
    exact (card_grpNK base64_lt (hB hm)).ge)
  have hp' : p ∈ (grpN 64 heP12Gens : Set (Equiv.Perm (Fin 64))) ∩
      ((normalizer (heB0 : Set (Equiv.Perm (Fin 64))) : Subgroup _) :
        Set (Equiv.Perm (Fin 64))) := by
    refine ⟨?_, hpn⟩
    rw [SetLike.mem_coe, ← P12_eq hm hF]
    exact hp
  rw [← heq] at hp'
  exact hp'

include hm hg in
theorem mem_heB0_of_imgC (hF : HexaFacts) {s : Bool} (φ : ↥(heP12C s) →* ↥heP12)
    (hφ : Function.Injective φ)
    (hφB : ∀ x : ↥(heP12C s), (x : Equiv.Perm (Fin 32)) ∈ heBC → (φ x : Equiv.Perm (Fin 64)) ∈ heB0)
    {R : ℕ → Equiv.Perm (Fin 64)} (hRB : ∀ w ∈ heWordsBE ++ heWordsBF, wval R w ∈ heB0)
    {p : Equiv.Perm (Fin 64)} (hp : p ∈ heP12) (hc : ∀ k < 2, imgC φ k = p * R k * p⁻¹) :
    p ∈ heB0 := by
  set ψ : ↥(heP12C s) →* Equiv.Perm (Fin 64) :=
    (MulAut.conj p⁻¹).toMonoidHom.comp (heP12.subtype.comp φ) with hψdef
  have hψ : ∀ x, ψ x = p⁻¹ * (φ x : Equiv.Perm (Fin 64)) * p := fun x => by
    simp [hψdef]
  have hW : heBC ≤ (heB0.comap ψ).map (heP12C s).subtype := by
    refine grpN_le fun a ha => ?_
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
    have hk4 : k < 4 := by rwa [length_heBCGens] at hk
    rw [← List.getD_eq_getElem _ #[] hk]
    have hmemP : permOfArr 32 (heBCGens.getD k #[]) ∈ heP12C s :=
      BC_le_P_of hm s (gen_mem_grpN (getD_mem hk _))
    refine ⟨⟨_, hmemP⟩, ?_, rfl⟩
    have hwr := range_wordsB hg s k
    have hwB := wordsB_getD_mem s hk4
    show ψ ⟨_, hmemP⟩ ∈ heB0
    rw [hψ, map_imgC φ hwr (heBCGens_eq_wval hm hg s hk4),
      wval_congr (g' := fun k => p * R k * p⁻¹) (fun l hl => hc _ (hwr l hl)), wval_conj]
    simpa [mul_assoc] using hRB _ hwB
  have hgen : ∀ x : ↥(heP12C s), (x : Equiv.Perm (Fin 32)) ∈ heBC →
      p⁻¹ * (φ x : Equiv.Perm (Fin 64)) * p ∈ heB0 := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hW hx
    have : y = x := Subtype.ext hyx
    rw [← hψ, ← this]
    exact hy
  set Y := (heBC.subgroupOf (heP12C s)).map (heP12.subtype.comp φ) with hYdef
  have hYB : Y ≤ heB0 := by
    rintro _ ⟨x, hx, rfl⟩
    exact hφB x hx
  have hYc : Nat.card Y = 1024 := by
    rw [hYdef, card_map_of_injective (by
        rw [MonoidHom.coe_comp]
        exact heP12.subtype_injective.comp hφ),
      Nat.card_congr (subgroupOfEquivOfLe (BC_le_P_of hm s)).toEquiv,
      card_grpNK base32_lt (enum_BC hm)]
  have hYeq : Y = heB0 := eq_of_le_of_card_ge hYB (by rw [hYc, card_grpNK base64_lt (hB hm)])
  have hpn : p⁻¹ ∈ normalizer (heB0 : Set (Equiv.Perm (Fin 64))) := by
    refine mem_normalizer_of_map_conj_le' ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [← hYeq] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    simpa [MulAut.conj_apply] using hgen x hx
  exact mem_heB0_of_normalizer hm hg hF hp (by simpa using inv_mem hpn)

include hm in
theorem conjIn23_iff {x y : Array ℕ} {X Y : Equiv.Perm (Fin 64)} (hx : Rep 64 x X)
    (hy : Rep 64 y Y) : conjIn23 x y = true ↔ ∃ q ∈ heP23, q * X * q⁻¹ = Y := by
  rw [conjIn23, heP23L_eq, List.any_eq_true]
  constructor
  · rintro ⟨q, hq, he⟩
    have hv := validA_of_mem_eltsK base64_lt (hP23 hm) hq
    exact ⟨permOfArr 64 q, perm_mem_of_mem_eltsK base64_lt (hP23 hm) hq,
      eq_of_eqA (rep_conjA hv hx) hy he⟩
  · rintro ⟨q, hq, he⟩
    obtain ⟨t, ht, hrt, hvt⟩ := exists_rep_of_memK base64_lt (hP23 hm) hq
    refine ⟨t, ht, ?_⟩
    rw [eqA_iff (rep_conjA hvt hx) hy, permOfArr_eq_of_rep hrt, he]

include hm in
theorem heB0_le_heP23 (hF : HexaFacts) : heB0 ≤ heP23 := by
  rw [P23_eq_of hm hF]
  exact le_inf ((B0_le_of hm hF).trans inf_le_left) (B0_le_normalizer_F0 hm)

include hm hg in
theorem eq_zero_of_fusion (hF : HexaFacts) {s : Bool} (φ : ↥(heP12C s) →* ↥heP12)
    (hφB : ∀ x : ↥(heP12C s), (x : Equiv.Perm (Fin 32)) ∈ heBC → (φ x : Equiv.Perm (Fin 64)) ∈ heB0)
    (φ' : ↥(heP12C (!s)) →* ↥heP12) (u : ↥heP23 ≃* ↥heP23)
    (hu : ∀ (x : ↥(heP12C s)) (x' : ↥(heP12C (!s))) (y : ↥heP23),
      (x : Equiv.Perm (Fin 32)) = x' → (x : Equiv.Perm (Fin 32)) ∈ heBC →
      (y : Equiv.Perm (Fin 64)) = φ x → (u y : Equiv.Perm (Fin 64)) = φ' x')
    {i j : ℕ} (hi : i < 4) (hj : j < 4) {p p' : Equiv.Perm (Fin 64)} (hp : p ∈ heB0)
    (hp' : p' ∈ heB0) (hc : ∀ k < 2, imgC φ k = p * rE i k * p⁻¹)
    (hc' : ∀ k < 2, imgC φ' k = p' * rF j k * p'⁻¹) : i = 0 ∧ j = 0 := by
  by_contra hne
  obtain ⟨k, hk, hkij⟩ := exists_witIdx i hi j hj hne
  have hfus := List.all_eq_true.1 (heGlueCheck_parts hg).2.2.2.2.2.2.2.1 k (List.mem_range.2 hk)
  simp only [heFusOK, hkij, Bool.and_eq_true] at hfus
  obtain ⟨⟨⟨⟨hs1, hs2⟩, hs3⟩, hs4⟩, hside⟩ := hfus
  have hB23 := heB0_le_heP23 hm hF
  have hwr : ∀ m, ∀ l ∈ heWit.getD m [], l / 2 < 2 :=
    range_pairWords hg (fun w hw => by simp [hw])
  have key : ∀ (wE wF : List ℕ), (∀ l ∈ wE, l / 2 < 2) → (∀ l ∈ wF, l / 2 < 2) →
      eqA 32 (evalW 32 heP12CGens wE) (evalW 32 heP13CGens wF) = true →
      eqA 32 (evalW 32 heP13CGens wE) (evalW 32 heP12CGens wF) = true →
      ∃ y : ↥heP23, (y : Equiv.Perm (Fin 64)) = p * wval (rE i) wE * p⁻¹ ∧
        (u y : Equiv.Perm (Fin 64)) = p' * wval (rF j) wF * p'⁻¹ := by
    intro wE wF hE hF' e1 e2
    have rE' := fun t => rep_evalW (valid_gensC hm t) (w := wE) (by rw [length_heGensC]; exact hE)
    have rF' := fun t => rep_evalW (valid_gensC hm t) (w := wF) (by rw [length_heGensC]; exact hF')
    have hb : wval (gC s) wE = wval (gC (!s)) wF := by
      cases s
      · exact eq_of_eqA (rE' false) (rF' true) e1
      · exact eq_of_eqA (rE' true) (rF' false) e2
    have hbs : wval (gC s) wE ∈ heP12C s := wval_mem fun l hl => gC_mem s (hE l hl)
    have hbs' : wval (gC s) wE ∈ heP12C (!s) := hb ▸ wval_mem fun l hl => gC_mem (!s) (hF' l hl)
    have hbBC : wval (gC s) wE ∈ heBC := by
      rw [← P12C_inf_of hm]
      cases s
      · exact ⟨hbs, hbs'⟩
      · exact ⟨hbs', hbs⟩
    have hx : (φ ⟨_, hbs⟩ : Equiv.Perm (Fin 64)) = p * wval (rE i) wE * p⁻¹ := by
      rw [map_imgC φ hE rfl, wval_congr (g' := fun k => p * rE i k * p⁻¹)
        (fun l hl => hc _ (hE l hl)), wval_conj]
    have hx' : (φ' ⟨_, hbs'⟩ : Equiv.Perm (Fin 64)) = p' * wval (rF j) wF * p'⁻¹ := by
      rw [map_imgC φ' hF' hb, wval_congr (g' := fun k => p' * rF j k * p'⁻¹)
        (fun l hl => hc' _ (hF' l hl)), wval_conj]
    refine ⟨⟨_, hB23 (hφB ⟨_, hbs⟩ hbBC)⟩, hx, ?_⟩
    rw [hu ⟨_, hbs⟩ ⟨_, hbs'⟩ _ rfl hbBC rfl, hx']
  obtain ⟨y1, hy1, hu1⟩ := key _ _ (hwr _) (hwr _) hs1 hs3
  obtain ⟨y2, hy2, hu2⟩ := key _ _ (hwr _) (hwr _) hs2 hs4
  have rX : ∀ m, Rep 64 (evalW 64 (pairE i) (heWit.getD m []))
      (wval (rE i) (heWit.getD m [])) := fun m =>
    rep_evalW (valid_pairE hg hi) (by rw [length_pairE]; exact hwr m)
  have rY : ∀ m, Rep 64 (evalW 64 (pairF j) (heWit.getD m []))
      (wval (rF j) (heWit.getD m [])) := fun m =>
    rep_evalW (valid_pairF hg hj) (by rw [length_pairF]; exact hwr m)
  have hiff : conjIn23 (evalW 64 (pairE i) (heWit.getD (4 * k) []))
      (evalW 64 (pairE i) (heWit.getD (4 * k + 2) [])) = true ↔
      conjIn23 (evalW 64 (pairF j) (heWit.getD (4 * k + 1) []))
        (evalW 64 (pairF j) (heWit.getD (4 * k + 3) [])) = true := by
    rw [conjIn23_iff hm (rX _) (rX _), conjIn23_iff hm (rY _) (rY _),
      ← isConj_conj_iff (hB23 hp), ← hy1, ← hy2, ← isConj_map_iff u y1 y2, hu1, hu2,
      isConj_conj_iff (hB23 hp')]
  cases hw : heWitE.getD k true <;> simp only [hw, Bool.and_eq_true, Bool.not_eq_true',
    Bool.false_eq_true, ite_false, ite_true] at hside
  · rw [← hiff, hside.2] at hside
    exact absurd hside.1 (by simp)
  · rw [hiff, hside.2] at hside
    exact absurd hside.1 (by simp)

end Fusion

section Kernel

theorem heT8_getD_lt {hx hy : Array ℕ} (hsz : hePiFArrs.size = 8) {k : ℕ} (hk : k < 4) :
    (heT8 hx hy).getD k #[] = hePiFArrs.getD k #[] := by
  simp [heT8, List.getD_eq_getElem?_getD, hsz, hk, Array.getD_eq_getD_getElem?,
    show k < 8 by omega]

theorem heT8_getD_6 {hx hy : Array ℕ} (hsz : hePiFArrs.size = 8) :
    (heT8 hx hy).getD 6 #[] = hx := by
  simp [heT8, List.getD_eq_getElem?_getD, hsz]

theorem heT8_getD_7 {hx hy : Array ℕ} (hsz : hePiFArrs.size = 8) :
    (heT8 hx hy).getD 7 #[] = hy := by
  simp [heT8, List.getD_eq_getElem?_getD, hsz]

theorem length_heT8 {hx hy : Array ℕ} (hsz : hePiFArrs.size = 8) : (heT8 hx hy).length = 8 := by
  simp [heT8, hsz]

theorem heRels23_sub : ∀ r ∈ heRels23, r ∈ hePiRels23Codes := fun _ hr =>
  List.mem_append_right _ hr

variable (hm : heModelCheck = true) (hg : heGlueCheck = true)

include hg in
theorem valid_heT8 {hx hy : Array ℕ} (hvx : validA 64 hx = true) (hvy : validA 64 hy = true) :
    ∀ a ∈ heT8 hx hy, validA 64 a = true := by
  intro a ha
  simp only [heT8, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with ha | rfl | rfl | rfl | rfl
  · exact valid64_of_mem hg (Or.inr (Or.inr (Or.inr (Or.inr (List.mem_of_mem_take ha)))))
  · exact valid_idA hg
  · exact valid_idA hg
  · exact hvx
  · exact hvy

include hg in
theorem wval_heT8 {hx hy : Array ℕ} {G : ℕ → Equiv.Perm (Fin 64)}
    (h0 : ∀ k < 4, G k = piF k) {r : List ℕ} (hr : ∀ l ∈ r, l / 2 < 4 ∨ l / 2 = 6 ∨ l / 2 = 7)
    (h6 : (∃ l ∈ r, l / 2 = 6) → G 6 = permOfArr 64 hx)
    (h7 : (∃ l ∈ r, l / 2 = 7) → G 7 = permOfArr 64 hy) :
    wval (permsL 64 (heT8 hx hy)) r = wval G r := by
  have hsz := (heCheckValid_parts hg).2.2.2.2.2.2.2.2.2.2.1
  refine wval_congr fun l hl => ?_
  rcases hr l hl with h | h | h
  · rw [permsL, heT8_getD_lt hsz h, h0 _ h]
  · rw [h, permsL, heT8_getD_6 hsz, h6 ⟨l, hl, h⟩]
  · rw [h, permsL, heT8_getD_7 hsz, h7 ⟨l, hl, h⟩]

include hg in
theorem heCheckKer_parts :
    relsOK 64 hePiEArrs.toList hePiRels23Codes = true ∧
    (∀ hy ∈ eltsK 64 base64 heP23Gens 9216, relsOK 64 (heT8 (idA 64) hy) heRelsY = true →
      eqA 64 hy (hePiFArrs.getD 7 #[]) = true ∨
        eqA 64 hy (conjA 64 hexaT0 (hePiFArrs.getD 7 #[])) = true) ∧
    (∀ hx ∈ eltsK 64 base64 heP23Gens 9216, relsOK 64 (heT8 hx (idA 64)) heRelsX = true →
      (relsOK 64 (heT8 hx (hePiFArrs.getD 7 #[])) heRels23 = true →
        eqA 64 hx (hePiFArrs.getD 6 #[]) = true) ∧
      (relsOK 64 (heT8 hx (conjA 64 hexaT0 (hePiFArrs.getD 7 #[]))) heRels23 = true →
        eqA 64 hx (conjA 64 hexaT0 (hePiFArrs.getD 6 #[])) = true)) := by
  have h := (heGlueCheck_parts hg).2.2.2.2.2.2.2.2.2.1
  simp only [heCheckKer, heP23L_eq, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun hy hhy hr => ?_, fun hx hhx hr => ?_⟩
  · rcases h2 hy hhy with (h | h) | h
    · rw [hr] at h
      exact absurd h (by simp)
    · exact Or.inl h
    · exact Or.inr h
  · rcases h3 hx hhx with h | ⟨ha, hb⟩
    · rw [hr] at h
      exact absurd h (by simp)
    · refine ⟨fun hr' => ?_, fun hr' => ?_⟩
      · rcases ha with h | h
        · rw [hr'] at h
          exact absurd h (by simp)
        · exact h
      · rcases hb with h | h
        · rw [hr'] at h
          exact absurd h (by simp)
        · exact h

include hm hg in
theorem piE_mem_heB0 {k : ℕ} (hk : k < 4) : piE k ∈ heB0 := by
  have h := (Bool.and_eq_true _ _ ▸ (heGlueCheck_parts hg).2.2.2.2.2.2.2.2.2.2.1)
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  have hk' := h.1.1.1.1.1.1.1 k (List.mem_range.2 hk)
  exact mem_of_inLNK base64_lt (hB hm) hk'.1.1.1 (rep_of_validA (valid_piEArr hg (by omega)))

end Kernel

section Pi

variable (hm : heModelCheck = true) (hg : heGlueCheck = true)

include hg in
theorem heCheckPi_parts {k : ℕ} (hk : k < 5) :
    eqA 64 (evalW 64 (pairE 0) (heWordsE.getD k [])) (hePiEArrs.getD (piIdx 4 k) #[]) = true ∧
    eqA 64 (evalW 64 (pairF 0) (heWordsF.getD k [])) (hePiFArrs.getD (piIdx 5 k) #[]) = true ∧
    eqA 32 (evalW 32 heP12CGens (heWordsE.getD k []))
      ((hePiCArrs false).getD (piIdx 4 k) #[]) = true ∧
    eqA 32 (evalW 32 heP13CGens (heWordsF.getD k []))
      ((hePiCArrs false).getD (piIdx 5 k) #[]) = true ∧
    eqA 32 (evalW 32 heP13CGens (heWordsE.getD k []))
      ((hePiCArrs true).getD (piIdx 4 k) #[]) = true ∧
    eqA 32 (evalW 32 heP12CGens (heWordsF.getD k []))
      ((hePiCArrs true).getD (piIdx 5 k) #[]) = true := by
  have h := List.all_eq_true.1 (Bool.and_eq_true _ _ ▸ (heGlueCheck_parts hg).2.2.2.2.2.2.2.2.1).1
    k (List.mem_range.2 hk)
  simp only [Bool.and_eq_true, and_assoc] at h
  exact h

include hg in
theorem range_wordsE (k : ℕ) : ∀ l ∈ heWordsE.getD k [], l / 2 < 2 :=
  range_pairWords hg (fun w hw => by simp [hw]) k

include hg in
theorem range_wordsF (k : ℕ) : ∀ l ∈ heWordsF.getD k [], l / 2 < 2 :=
  range_pairWords hg (fun w hw => by simp [hw]) k

include hg in
theorem piE_eq_wval {k : ℕ} (hk : k < 5) :
    piE (piIdx 4 k) = wval (rE 0) (heWordsE.getD k []) :=
  permOfArr_eq_of_rep (rep_of_eqA (rep_evalW (valid_pairE hg (by norm_num))
    (by rw [length_pairE]; exact range_wordsE hg k)) (heCheckPi_parts hg hk).1)

include hg in
theorem piF_eq_wval {k : ℕ} (hk : k < 5) :
    piF (piIdx 5 k) = wval (rF 0) (heWordsF.getD k []) :=
  permOfArr_eq_of_rep (rep_of_eqA (rep_evalW (valid_pairF hg (by norm_num))
    (by rw [length_pairF]; exact range_wordsF hg k)) (heCheckPi_parts hg hk).2.1)

include hm hg in
theorem piC_eq_wvalE (s : Bool) {k : ℕ} (hk : k < 5) :
    piC s (piIdx 4 k) = wval (gC s) (heWordsE.getD k []) := by
  have hr : ∀ l ∈ heWordsE.getD k [], l / 2 < (heGensC s).length := by
    rw [length_heGensC]
    exact range_wordsE hg k
  cases s
  · exact permOfArr_eq_of_rep (rep_of_eqA (rep_evalW (valid_gensC hm false) hr)
      (heCheckPi_parts hg hk).2.2.1)
  · exact permOfArr_eq_of_rep (rep_of_eqA (rep_evalW (valid_gensC hm true) hr)
      (heCheckPi_parts hg hk).2.2.2.2.1)

include hm hg in
theorem piC_eq_wvalF (s : Bool) {k : ℕ} (hk : k < 5) :
    piC s (piIdx 5 k) = wval (gC (!s)) (heWordsF.getD k []) := by
  have hr : ∀ l ∈ heWordsF.getD k [], l / 2 < (heGensC (!s)).length := by
    rw [length_heGensC]
    exact range_wordsF hg k
  cases s
  · exact permOfArr_eq_of_rep (rep_of_eqA (rep_evalW (valid_gensC hm true) hr)
      (heCheckPi_parts hg hk).2.2.2.1)
  · exact permOfArr_eq_of_rep (rep_of_eqA (rep_evalW (valid_gensC hm false) hr)
      (heCheckPi_parts hg hk).2.2.2.2.2)

end Pi

section Mem

variable (hm : heModelCheck = true) (hg : heGlueCheck = true)

include hg in
theorem heCheckMem_parts :
    (∀ k < 4, inLN 64 heBL (hePiEArrs.getD k #[]) = true ∧
      inLN 64 heBL (hePiFArrs.getD k #[]) = true ∧
      inLN 32 heBCL ((hePiCArrs false).getD k #[]) = true ∧
      inLN 32 heBCL ((hePiCArrs true).getD k #[]) = true) ∧
    inLN 64 heP12L (hePiEArrs.getD 4 #[]) = true ∧ inLN 64 heP12L (hePiFArrs.getD 5 #[]) = true ∧
    inLN 32 heP0L ((hePiCArrs false).getD 4 #[]) = true ∧
    inLN 32 heP1L ((hePiCArrs false).getD 5 #[]) = true ∧
    inLN 32 heP1L ((hePiCArrs true).getD 4 #[]) = true ∧
    inLN 32 heP0L ((hePiCArrs true).getD 5 #[]) = true ∧
    (∀ k, k = 6 ∨ k = 7 → inLN 64 heP23L (hePiEArrs.getD k #[]) = true ∧
      inLN 64 heP23L (hePiFArrs.getD k #[]) = true) := by
  have h := (heGlueCheck_parts hg).2.2.2.2.2.2.2.2.2.2.1
  simp only [heCheckMem, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false, and_assoc] at h
  exact h

include hm in
theorem heB0_le_heP12 : heB0 ≤ heP12 :=
  (grpN_le_of_allK base64_lt (hP12 hm) (fun _ ha => validA_of_mem_gensK (hB hm) ha)
    (heCheckB0_parts hm).2.2.2.2.1).trans (P12gens_le hm)

include hm in
theorem heP23_le_heN0 : heP23 ≤ heN0 := (P23_le hm).trans inf_le_left

include hm hg in
theorem piC_mem_heBC (s : Bool) {k : ℕ} (hk : k < 4) : piC s k ∈ heBC := by
  have h := (heCheckMem_parts hg).1 k hk
  have hv := valid_piCArr hg s (k := k) (by omega)
  cases s
  · exact mem_of_inLNK base32_lt (enum_BC hm) h.2.2.1 (rep_of_validA hv)
  · exact mem_of_inLNK base32_lt (enum_BC hm) h.2.2.2 (rep_of_validA hv)

include hm hg in
theorem piC_mem_P (s : Bool) : piC s 4 ∈ heP12C s := by
  have hv := valid_piCArr hg s (k := 4) (by norm_num)
  rw [heP12C_eq]
  cases s
  · exact mem_of_inLNK base32_lt (enum_gensC hm false) (heCheckMem_parts hg).2.2.2.1
      (rep_of_validA hv)
  · exact mem_of_inLNK base32_lt (enum_gensC hm true) (heCheckMem_parts hg).2.2.2.2.2.1
      (rep_of_validA hv)

include hm hg in
theorem piC_mem_P' (s : Bool) : piC s 5 ∈ heP12C (!s) := by
  have hv := valid_piCArr hg s (k := 5) (by norm_num)
  rw [heP12C_eq]
  cases s
  · exact mem_of_inLNK base32_lt (enum_gensC hm true) (heCheckMem_parts hg).2.2.2.2.1
      (rep_of_validA hv)
  · exact mem_of_inLNK base32_lt (enum_gensC hm false) (heCheckMem_parts hg).2.2.2.2.2.2.1
      (rep_of_validA hv)

include hm hg in
theorem piC_mem (s : Bool) {k : ℕ} (hk : k ≤ 5) : piC s k ∈ hePC := by
  rcases (by omega : k < 4 ∨ k = 4 ∨ k = 5) with h | rfl | rfl
  · exact P_le_PC_of hm s (BC_le_P_of hm s (piC_mem_heBC hm hg s h))
  · exact P_le_PC_of hm s (piC_mem_P hm hg s)
  · exact P_le_PC_of hm (!s) (piC_mem_P' hm hg s)

include hm hg in
theorem piF_mem_heB0 {k : ℕ} (hk : k < 4) : piF k ∈ heB0 :=
  mem_of_inLNK base64_lt (hB hm) ((heCheckMem_parts hg).1 k hk).2.1
    (rep_of_validA (valid_piFArr hg (by omega)))

include hm hg in
theorem piE_mem_heP12 {k : ℕ} (hk : k ≤ 4) : piE k ∈ heP12 := by
  rcases (by omega : k < 4 ∨ k = 4) with h | rfl
  · exact heB0_le_heP12 hm (piE_mem_heB0 hm hg h)
  · exact P12gens_le hm (mem_of_inLNK base64_lt (hP12 hm) (heCheckMem_parts hg).2.1
      (rep_of_validA (valid_piEArr hg (by norm_num))))

include hm hg in
theorem piF_mem_heP12 {k : ℕ} (hk : k < 4 ∨ k = 5) : piF k ∈ heP12 := by
  rcases hk with h | rfl
  · exact heB0_le_heP12 hm (piF_mem_heB0 hm hg h)
  · exact P12gens_le hm (mem_of_inLNK base64_lt (hP12 hm) (heCheckMem_parts hg).2.2.1
      (rep_of_validA (valid_piFArr hg (by norm_num))))

include hm hg in
theorem piE_mem_heP23 {k : ℕ} (hk : k = 6 ∨ k = 7) : piE k ∈ heP23 :=
  mem_of_inLNK base64_lt (hP23 hm) ((heCheckMem_parts hg).2.2.2.2.2.2.2 k hk).1
    (rep_of_validA (valid_piEArr hg (by omega)))

include hm hg in
theorem piF_mem_heP23 {k : ℕ} (hk : k = 6 ∨ k = 7) : piF k ∈ heP23 :=
  mem_of_inLNK base64_lt (hP23 hm) ((heCheckMem_parts hg).2.2.2.2.2.2.2 k hk).2
    (rep_of_validA (valid_piFArr hg (by omega)))

include hm hg in
theorem piE_mem {k : ℕ} (hk : k ≤ 4 ∨ k = 6 ∨ k = 7) : piE k ∈ heN0 := by
  rcases hk with h | h
  · exact (piE_mem_heP12 hm hg h).1
  · exact heP23_le_heN0 hm (piE_mem_heP23 hm hg h)

include hm hg in
theorem piF_mem {k : ℕ} (hk : k < 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) : piF k ∈ heN0 := by
  rcases hk with h | h | h
  · exact (piF_mem_heP12 hm hg (Or.inl h)).1
  · exact (piF_mem_heP12 hm hg (Or.inr h)).1
  · exact heP23_le_heN0 hm (piF_mem_heP23 hm hg h)

end Mem

section KernelCases

variable (hm : heModelCheck = true) (hg : heGlueCheck = true)

include hm hg in
theorem kernel_cases {X Y : Equiv.Perm (Fin 64)} (hX : X ∈ heP23) (hY : Y ∈ heP23)
    {G : ℕ → Equiv.Perm (Fin 64)} (h0 : ∀ k < 4, G k = piF k) (h6 : G 6 = X) (h7 : G 7 = Y)
    (hrels : ∀ r ∈ hePiRels23Codes, wval G r = 1) :
    (X = piF 6 ∧ Y = piF 7) ∨
      (X = hexaT0P * piF 6 * hexaT0P⁻¹ ∧ Y = hexaT0P * piF 7 * hexaT0P⁻¹) := by
  obtain ⟨-, hk2, hk3⟩ := heCheckKer_parts hg
  obtain ⟨xa, hxa, hrx, hvx⟩ := exists_rep_of_memK base64_lt (hP23 hm) hX
  obtain ⟨ya, hya, hry, hvy⟩ := exists_rep_of_memK base64_lt (hP23 hm) hY
  have hsz := (heCheckValid_parts hg).2.2.2.2.2.2.2.2.2.2.1
  have hrange23 : ∀ r ∈ hePiRels23Codes, ∀ l ∈ r, l / 2 < 4 ∨ l / 2 = 6 ∨ l / 2 = 7 :=
    fun r hr l hl => by
      rcases (heCheckRange_parts hg).2.1 r hr l hl with h | h | h
      · left; omega
      · right; left; exact h
      · right; right; exact h
  have hok : ∀ {a b : Array ℕ}, validA 64 a = true → validA 64 b = true →
      ∀ {rels : List (List ℕ)}, (∀ r ∈ rels, r ∈ hePiRels23Codes) →
        (∀ r ∈ rels, ((∃ l ∈ r, l / 2 = 6) → permOfArr 64 a = X) ∧
          ((∃ l ∈ r, l / 2 = 7) → permOfArr 64 b = Y)) → relsOK 64 (heT8 a b) rels = true := by
    intro a b ha hb rels hsub h
    refine (relsOK_iff (valid_heT8 hg ha hb) (fun r hr l hl => by
      rw [length_heT8 hsz]
      rcases hrange23 r (hsub r hr) l hl with h | h | h <;> omega)).2 fun r hr => ?_
    rw [wval_heT8 hg (G := G) h0 (hrange23 r (hsub r hr)) (fun h' => h6.trans ((h r hr).1 h').symm)
      (fun h' => h7.trans ((h r hr).2 h').symm)]
    exact hrels r (hsub r hr)
  have hX' := permOfArr_eq_of_rep hrx
  have hY' := permOfArr_eq_of_rep hry
  have hYc := hk2 ya hya (hok (valid_idA hg) hvy (fun r hr => heRels23_sub r
      (List.mem_filter.1 hr).1) fun r hr => ⟨fun ⟨l, hl, h6'⟩ => by
        have := List.all_eq_true.1 (List.mem_filter.1 hr).2 l hl
        simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at this
        omega, fun _ => hY'⟩)
  have hXc := hk3 xa hxa (hok hvx (valid_idA hg) (fun r hr => heRels23_sub r
      (List.mem_filter.1 hr).1) fun r hr => ⟨fun _ => hX', fun ⟨l, hl, h7'⟩ => by
        have := List.all_eq_true.1 (List.mem_filter.1 hr).2 l hl
        simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at this
        omega⟩)
  have hvF6 := valid_piFArr hg (k := 6) (by norm_num)
  have hvF7 := valid_piFArr hg (k := 7) (by norm_num)
  have hrF6' := rep_conjA (valid_t0 hg) (rep_of_validA hvF6)
  have hrF7' := rep_conjA (valid_t0 hg) (rep_of_validA hvF7)
  rcases hYc with h | h
  · have hYe : Y = piF 7 := eq_of_eqA hry (rep_of_validA hvF7) h
    have hx := hXc.1 (hok hvx hvF7 heRels23_sub fun _ _ => ⟨fun _ => hX', fun _ => hYe.symm⟩)
    exact Or.inl ⟨eq_of_eqA hrx (rep_of_validA hvF6) hx, hYe⟩
  · have hYe : Y = hexaT0P * piF 7 * hexaT0P⁻¹ := eq_of_eqA hry hrF7' h
    have hx := hXc.2 (hok hvx (valid_yF' hg) heRels23_sub fun _ _ =>
      ⟨fun _ => hX', fun _ => (permOfArr_eq_of_rep hrF7').trans hYe.symm⟩)
    exact Or.inr ⟨eq_of_eqA hrx hrF6' hx, hYe⟩

end KernelCases

section Rigidity

theorem piIdx4 {k : ℕ} (hk : k ≤ 4) : piIdx 4 k = k := by
  unfold piIdx
  split_ifs <;> omega

variable (hm : heModelCheck = true) (hg : heGlueCheck = true) (hF : HexaFacts)
include hm hg hF

theorem exists_conj_glue (s : Bool)
    (φ : ↥(heP12C s) →* ↥heP12) (hφ : Function.Injective φ)
    (hφB : ∀ x : ↥(heP12C s), (x : Equiv.Perm (Fin 32)) ∈ heBC → (φ x : Equiv.Perm (Fin 64)) ∈ heB0)
    (φ' : ↥(heP12C (!s)) →* ↥heP12) (hφ' : Function.Injective φ')
    (hφ'B : ∀ x : ↥(heP12C (!s)), (x : Equiv.Perm (Fin 32)) ∈ heBC →
      (φ' x : Equiv.Perm (Fin 64)) ∈ heB0)
    (u : ↥heP23 ≃* ↥heP23)
    (hu : ∀ (x : ↥(heP12C s)) (x' : ↥(heP12C (!s))) (y : ↥heP23),
      (x : Equiv.Perm (Fin 32)) = x' → (x : Equiv.Perm (Fin 32)) ∈ heBC →
      (y : Equiv.Perm (Fin 64)) = φ x → (u y : Equiv.Perm (Fin 64)) = φ' x') :
    ∃ p ∈ heB0, ∃ q ∈ heP12 ⊓ heP23,
      (∀ k ≤ 4, ∀ x : ↥(heP12C s), (x : Equiv.Perm (Fin 32)) = piC s k →
        (φ x : Equiv.Perm (Fin 64)) = p * piE k * p⁻¹) ∧
      (∀ k ≤ 5, k ≠ 4 → ∀ x : ↥(heP12C (!s)), (x : Equiv.Perm (Fin 32)) = piC s k →
        (φ' x : Equiv.Perm (Fin 64)) = q * piF k * q⁻¹) ∧
      (∀ k, k = 6 ∨ k = 7 → ∀ y : ↥heP23, (y : Equiv.Perm (Fin 64)) = p * piE k * p⁻¹ →
        (u y : Equiv.Perm (Fin 64)) = q * piF k * q⁻¹) := by
  obtain ⟨i, hi, p0, hp0, p0', hp0', hcE⟩ := exists_conj_pair hm hg hF φ hφ
  obtain ⟨j, hj, p1', hp1', p1, hp1, hcF⟩ := exists_conj_pair hm hg hF φ' hφ'
  have hpE : p0 ∈ heB0 := mem_heB0_of_imgC hm hg hF φ hφ hφB
    (fun w hw => (wvalB_mem hm hg hi hw).1) hp0 fun k hk => (hcE k hk).1
  have hpF : p1 ∈ heB0 := mem_heB0_of_imgC hm hg hF φ' hφ' hφ'B
    (fun w hw => (wvalB_mem hm hg hj hw).2) hp1 fun k hk => (hcF k hk).2
  obtain ⟨rfl, rfl⟩ := eq_zero_of_fusion hm hg hF φ hφB φ' u hu hi hj hpE hpF
    (fun k hk => (hcE k hk).1) fun k hk => (hcF k hk).2
  have hB23 := heB0_le_heP23 hm hF
  have hE : ∀ k ≤ 4, ∀ x : ↥(heP12C s), (x : Equiv.Perm (Fin 32)) = piC s k →
      (φ x : Equiv.Perm (Fin 64)) = p0 * piE k * p0⁻¹ := by
    intro k hk x hx
    have h1 := piC_eq_wvalE hm hg s (k := k) (by omega)
    have h2 := piE_eq_wval hg (k := k) (by omega)
    rw [piIdx4 hk] at h1 h2
    rw [map_imgC φ (range_wordsE hg k) (hx.trans h1),
      wval_congr (g' := fun k => p0 * rE 0 k * p0⁻¹)
        (fun l hl => (hcE _ (range_wordsE hg k l hl)).1), wval_conj, h2]
  have hF' : ∀ k ≤ 5, k ≠ 4 → ∀ x : ↥(heP12C (!s)), (x : Equiv.Perm (Fin 32)) = piC s k →
      (φ' x : Equiv.Perm (Fin 64)) = p1 * piF k * p1⁻¹ := by
    intro k hk hk4 x hx
    obtain ⟨m, hm5, hmk⟩ : ∃ m < 5, piIdx 5 m = k := by
      rcases (by omega : k < 4 ∨ k = 5) with h | rfl
      · exact ⟨k, by omega, piIdx_of_lt h⟩
      · exact ⟨4, by norm_num, rfl⟩
    have h1 := piC_eq_wvalF hm hg s hm5
    have h2 := piF_eq_wval hg hm5
    rw [hmk] at h1 h2
    rw [map_imgC φ' (range_wordsF hg m) (hx.trans h1),
      wval_congr (g' := fun k => p1 * rF 0 k * p1⁻¹)
        (fun l hl => (hcF _ (range_wordsF hg m l hl)).2), wval_conj, h2]
  set P0 : ↥heP23 := ⟨p0, hB23 hpE⟩ with hP0
  set P1 : ↥heP23 := ⟨p1, hB23 hpF⟩ with hP1
  set u' : ↥heP23 →* ↥heP23 := (MulAut.conj P1⁻¹).toMonoidHom.comp
    (u.toMonoidHom.comp (MulAut.conj P0).toMonoidHom) with hu'def
  have hu' : ∀ y : ↥heP23, (u' y : Equiv.Perm (Fin 64)) =
      p1⁻¹ * (u (P0 * y * P0⁻¹) : Equiv.Perm (Fin 64)) * p1 := fun y => by
    simp [hu'def, P1, MulAut.conj_apply]
  have hb : ∀ k (hk : k < 4),
      (u' ⟨piE k, hB23 (piE_mem_heB0 hm hg hk)⟩ : Equiv.Perm (Fin 64)) = piF k := by
    intro k hk
    have hC := piC_mem_heBC hm hg s hk
    rw [hu', hu ⟨piC s k, BC_le_P_of hm s hC⟩ ⟨piC s k, BC_le_P_of hm (!s) hC⟩ _ rfl hC
      (by rw [hE k (by omega) _ rfl]; rfl), hF' k (by omega) (by omega) _ rfl]
    group
  set XE : ↥heP23 := ⟨piE 6, piE_mem_heP23 hm hg (Or.inl rfl)⟩ with hXE
  set YE : ↥heP23 := ⟨piE 7, piE_mem_heP23 hm hg (Or.inr rfl)⟩ with hYE
  set G : ℕ → Equiv.Perm (Fin 64) := fun k =>
    if k < 4 then piF k else if k = 6 then (u' XE : Equiv.Perm (Fin 64))
    else if k = 7 then (u' YE : Equiv.Perm (Fin 64)) else 1 with hG
  have hrange23 : ∀ r ∈ hePiRels23Codes, ∀ l ∈ r, l / 2 < 4 ∨ l / 2 = 6 ∨ l / 2 = 7 :=
    fun r hr l hl => by
      rcases (heCheckRange_parts hg).2.1 r hr l hl with h | h | h
      · left; omega
      · right; left; exact h
      · right; right; exact h
  have hrelsE : ∀ r ∈ hePiRels23Codes, wval piE r = 1 := by
    have hsz := (heCheckValid_parts hg).2.2.2.2.2.2.2.2.2.1
    have h := (relsOK_iff (fun a ha => valid64_of_mem hg (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
      (fun r hr l hl => by
        rw [Array.length_toList, hsz]
        rcases hrange23 r hr l hl with h | h | h <;> omega)).1 (heCheckKer_parts hg).1
    intro r hr
    rw [← h r hr]
    exact wval_congr fun l _ => (permsL_toList _ _).symm
  have hrelsG : ∀ r ∈ hePiRels23Codes, wval G r = 1 := by
    intro r hr
    refine wval_eq_one_map (heP23.subtype.comp u') (g := piE) (fun l hl => ?_) (hrelsE r hr)
    rcases hrange23 r hr l hl with h | h | h
    · refine ⟨hB23 (piE_mem_heB0 hm hg h), ?_⟩
      simp only [MonoidHom.coe_comp, Function.comp_apply, coe_subtype, hG, ite_eq_left h]
      exact hb _ h
    · refine ⟨piE_mem_heP23 hm hg (Or.inl h), ?_⟩
      simp only [MonoidHom.coe_comp, Function.comp_apply, coe_subtype, hG, h]
      simp [hXE]
    · refine ⟨piE_mem_heP23 hm hg (Or.inr h), ?_⟩
      simp only [MonoidHom.coe_comp, Function.comp_apply, coe_subtype, hG, h]
      simp [hYE]
  have hux : ∀ k, k = 6 ∨ k = 7 → ∀ y : ↥heP23, (y : Equiv.Perm (Fin 64)) = p0 * piE k * p0⁻¹ →
      (u y : Equiv.Perm (Fin 64)) = p1 * G k * p1⁻¹ := by
    rintro k hk y hy
    have hyE : P0⁻¹ * y * P0 = if k = 6 then XE else YE := by
      apply Subtype.ext
      rcases hk with rfl | rfl
      · simp [hy, hXE, P0, mul_assoc]
      · simp [hy, hYE, P0, mul_assoc]
    have h1 := hu' (P0⁻¹ * y * P0)
    have h2 : P0 * (P0⁻¹ * y * P0) * P0⁻¹ = y := by group
    rw [h2, hyE] at h1
    have hGk : G k = (u' (if k = 6 then XE else YE) : Equiv.Perm (Fin 64)) := by
      rcases hk with rfl | rfl <;> simp [hG]
    rw [hGk, h1]
    group
  have hT0 : hexaT0P ∈ heB0 := T_le_B0_of hm (t0_mem_T hm)
  rcases kernel_cases hm hg (u' XE).2 (u' YE).2 (G := G) (fun k hk => by simp [hG, hk])
      (by simp [hG]) (by simp [hG]) hrelsG with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · refine ⟨p0, hpE, p1, ⟨heB0_le_heP12 hm hpF, hB23 hpF⟩, hE, hF', fun k hk y hy' => ?_⟩
    rw [hux k hk y hy']
    rcases hk with rfl | rfl
    · rw [show G 6 = (u' XE : Equiv.Perm (Fin 64)) by simp [hG], hx]
    · rw [show G 7 = (u' YE : Equiv.Perm (Fin 64)) by simp [hG], hy]
  · have hq : p1 * hexaT0P ∈ heB0 := mul_mem hpF hT0
    refine ⟨p0, hpE, p1 * hexaT0P, ⟨heB0_le_heP12 hm hq, hB23 hq⟩, hE,
      fun k hk hk4 x hx => ?_, fun k hk y hy' => ?_⟩
    · have hc : piF k * hexaT0P = hexaT0P * piF k :=
        mem_centralizer_singleton_iff.mp (piF_mem_heP12 hm hg (by omega)).2
      rw [hF' k hk hk4 x hx]
      calc p1 * piF k * p1⁻¹ = p1 * (piF k * hexaT0P) * hexaT0P⁻¹ * p1⁻¹ := by group
        _ = p1 * hexaT0P * piF k * (p1 * hexaT0P)⁻¹ := by rw [hc]; group
    · rw [hux k hk y hy']
      rcases hk with rfl | rfl
      · rw [show G 6 = (u' XE : Equiv.Perm (Fin 64)) by simp [hG], hx]
        group
      · rw [show G 7 = (u' YE : Equiv.Perm (Fin 64)) by simp [hG], hy]
        group

end Rigidity

section Gen

theorem lift_mk_ofCodes {G : Type*} [Group G] (g : Fin 8 → G) {w : List ℕ}
    (hw : ∀ l ∈ w, l < 16) :
    FreeGroup.lift g (FreeGroup.mk (ofCodes w)) =
      wval (fun k => if h : k < 8 then g ⟨k, h⟩ else 1) w := by
  rw [FreeGroup.lift_mk, wval, ofCodes, List.map_map]
  congr 1
  refine List.map_congr_left fun l hl => ?_
  have h8 : l / 2 < 8 := by have := hw l hl; omega
  have hmod : l / 2 % 8 = l / 2 := Nat.mod_eq_of_lt h8
  simp only [Function.comp_apply, dite_eq_left h8]
  by_cases h : l % 2 = 0 <;> simp [h, hmod]

theorem length_hexaR0Gens : hexaR0Gens.length = 2 := rfl

variable (hm : heModelCheck = true) (hg : heGlueCheck = true)

include hg in
theorem heCheckGen_parts :
    heGenWordsC0.length = hePCGens.length ∧ heGenWordsC1.length = hePCGens.length ∧
    heGenWordsT.length = hexaTGens.length ∧ heGenWordsM.length = hexaMGens.length ∧
    (∀ k < hePCGens.length,
      eqA 32 (evalW 32 (hePiCArrs false).toList (heGenWordsC0.getD k [])) (hePCGens.getD k #[]) =
        true ∧
      eqA 32 (evalW 32 (hePiCArrs true).toList (heGenWordsC1.getD k [])) (hePCGens.getD k #[]) =
        true) ∧
    (∀ k < hexaTGens.length,
      eqA 64 (evalW 64 hePiEArrs.toList (heGenWordsT.getD k [])) (hexaTGens.getD k #[]) = true) ∧
    (∀ k < hexaMGens.length,
      eqA 64 (evalW 64 hePiEArrs.toList (heGenWordsM.getD k [])) (hexaMGens.getD k #[]) = true) ∧
    heGenWordsR.length = hexaR0Gens.length ∧
    (∀ k < hexaR0Gens.length,
      eqA 64 (evalW 64 hePiEArrs.toList (heGenWordsR.getD k [])) (hexaR0Gens.getD k #[]) =
        true) := by
  have h := (heGlueCheck_parts hg).2.2.2.2.2.2.2.2.2.2.2.2
  simp only [heCheckGen, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    and_assoc] at h
  exact h

include hg in
theorem valid_piCList (s : Bool) : ∀ a ∈ (hePiCArrs s).toList, validA 32 a = true := by
  intro a ha
  refine (heCheckValid_parts hg).2.1 a (List.mem_append.2 ?_)
  cases s
  · exact Or.inl ha
  · exact Or.inr ha

include hg in
theorem valid_piEList : ∀ a ∈ hePiEArrs.toList, validA 64 a = true := fun _ ha =>
  valid64_of_mem hg (Or.inr (Or.inr (Or.inr (Or.inl ha))))

include hg in
theorem length_piCList (s : Bool) : (hePiCArrs s).toList.length = 8 := by
  rw [Array.length_toList]
  cases s
  · exact (heCheckValid_parts hg).2.2.2.2.2.2.2.2.2.2.2.1
  · exact (heCheckValid_parts hg).2.2.2.2.2.2.2.2.2.2.2.2

include hg in
theorem length_piEList : hePiEArrs.toList.length = 8 := by
  rw [Array.length_toList]
  exact (heCheckValid_parts hg).2.2.2.2.2.2.2.2.2.1

include hg in
theorem piC_z (s : Bool) : piC s 1 * piC s 2 * piC s 1 * piC s 2 = heTC := by
  have h := (heGlueCheck_parts hg).2.2.2.2.2.2.2.2.2.2.2.1
  simp only [heCheckZ, Bool.and_eq_true] at h
  have he : eqA 32 (evalW 32 (hePiCArrs s).toList [2, 4, 2, 4]) heTCArr = true := by
    cases s
    · exact h.1
    · exact h.2
  have hr := permOfArr_eq_of_rep (rep_of_eqA (rep_evalW (valid_piCList hg s) (w := [2, 4, 2, 4])
    (fun l hl => by rw [length_piCList hg s]; simp at hl; omega)) he)
  rw [heTC, hr]
  simp only [wval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, permsL_toList,
    show (2 : ℕ) % 2 = 0 from rfl, show (2 : ℕ) / 2 = 1 from rfl,
    show (4 : ℕ) / 2 = 2 from rfl, ite_true, mul_one, mul_assoc]

theorem wval_piC_mem_closure (s : Bool) {w : List ℕ} (hw : ∀ l ∈ w, l < 12) :
    wval (permsL 32 (hePiCArrs s).toList) w ∈ closure {x | ∃ k ≤ 5, piC s k = x} :=
  wval_mem fun l hl => subset_closure ⟨l / 2, by have := hw l hl; omega, by
    rw [permsL_toList]⟩

theorem wval_piE_mem_closure {w : List ℕ} (hw : ∀ l ∈ w, l < 10 ∨ l / 2 = 6 ∨ l / 2 = 7) :
    wval (permsL 64 hePiEArrs.toList) w ∈
      closure {x | ∃ k, (k ≤ 4 ∨ k = 6 ∨ k = 7) ∧ piE k = x} :=
  wval_mem fun l hl => subset_closure ⟨l / 2, by
    rcases hw l hl with h | h | h
    · left; omega
    · right; left; exact h
    · right; right; exact h, by rw [permsL_toList]⟩

include hg in
theorem hePC_le_closure (s : Bool) : hePC ≤ closure {x | ∃ k ≤ 5, piC s k = x} := by
  obtain ⟨h0, h1, -, -, hC, -⟩ := heCheckGen_parts hg
  refine grpN_le fun a ha => ?_
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
  rw [← List.getD_eq_getElem _ #[] hk]
  have hw : ∀ l ∈ (if s then heGenWordsC1 else heGenWordsC0).getD k [], l < 12 := by
    refine forall_mem_getD (fun w hw l hl => (heCheckRange_parts hg).2.2.1 w ?_ l hl) k
    cases s
    · exact List.mem_append_left _ hw
    · exact List.mem_append_right _ hw
  have he : eqA 32 (evalW 32 (hePiCArrs s).toList
      ((if s then heGenWordsC1 else heGenWordsC0).getD k [])) (hePCGens.getD k #[]) = true := by
    cases s
    · exact (hC k hk).1
    · exact (hC k hk).2
  rw [permOfArr_eq_of_rep (rep_of_eqA (rep_evalW (valid_piCList hg s) (fun l hl => by
    rw [length_piCList hg s]; have := hw l hl; omega)) he)]
  exact wval_piC_mem_closure s hw

include hg in
theorem heN0_le_closure : heN0 ≤ closure {x | ∃ k, (k ≤ 4 ∨ k = 6 ∨ k = 7) ∧ piE k = x} := by
  obtain ⟨-, -, -, -, -, hT, hM, -⟩ := heCheckGen_parts hg
  have key : ∀ {L : List (List ℕ)} {gs : List (Array ℕ)},
      (∀ w ∈ L, w ∈ heGenWordsT ++ heGenWordsM ++ heGenWordsR) →
      (∀ k < gs.length, eqA 64 (evalW 64 hePiEArrs.toList (L.getD k [])) (gs.getD k #[]) = true) →
      grpN 64 gs ≤ closure {x | ∃ k, (k ≤ 4 ∨ k = 6 ∨ k = 7) ∧ piE k = x} := by
    intro L gs hL hgs
    refine grpN_le fun a ha => ?_
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
    rw [← List.getD_eq_getElem _ #[] hk]
    have hw : ∀ l ∈ L.getD k [], l < 10 ∨ l / 2 = 6 ∨ l / 2 = 7 :=
      forall_mem_getD (fun w hw l hl => (heCheckRange_parts hg).2.2.2 w (hL w hw) l hl) k
    rw [permOfArr_eq_of_rep (rep_of_eqA (rep_evalW (valid_piEList hg) (fun l hl => by
      rw [length_piEList hg]
      rcases hw l hl with h | h | h <;> omega)) (hgs k hk))]
    exact wval_piE_mem_closure hw
  exact sup_le (key (fun w hw => by simp [hw]) hT) (key (fun w hw => by simp [hw]) hM)

include hg in
theorem hexaR0Gens_eq_wval {k : ℕ} (hk : k < 2) :
    permOfArr 64 (hexaR0Gens.getD k #[]) = wval (fun k => piE k) (heGenWordsR.getD k []) := by
  obtain ⟨-, -, -, -, -, -, -, -, hR⟩ := heCheckGen_parts hg
  have hw : ∀ l ∈ heGenWordsR.getD k [], l < 10 ∨ l / 2 = 6 ∨ l / 2 = 7 :=
    forall_mem_getD (fun w hw l hl => (heCheckRange_parts hg).2.2.2 w (by simp [hw]) l hl) k
  rw [permOfArr_eq_of_rep (rep_of_eqA (rep_evalW (valid_piEList hg) (fun l hl => by
    rw [length_piEList hg]
    rcases hw l hl with h | h | h <;> omega)) (hR k (by rw [length_hexaR0Gens]; exact hk)))]
  exact wval_congr fun l _ => permsL_toList _ _

include hg in
theorem heGenWordsR_eval {k : ℕ} (hk : k < 2) :
    FreeGroup.lift (fun i : Fin 8 => piE i) (FreeGroup.mk (ofCodes (heGenWordsR.getD k []))) =
      permOfArr 64 (hexaR0Gens.getD k #[]) := by
  have hw : ∀ l ∈ heGenWordsR.getD k [], l < 10 ∨ l / 2 = 6 ∨ l / 2 = 7 :=
    forall_mem_getD (fun w hw l hl => (heCheckRange_parts hg).2.2.2 w (by simp [hw]) l hl) k
  have h16 : ∀ l ∈ heGenWordsR.getD k [], l < 16 := fun l hl => by
    rcases hw l hl with h | h | h <;> omega
  rw [lift_mk_ofCodes _ h16, hexaR0Gens_eq_wval hg hk]
  refine wval_congr fun l hl => ?_
  have h8 : l / 2 < 8 := by have := h16 l hl; omega
  rw [dite_eq_left h8]

end Gen

end CFSG.ComponentClassification.AS81.HeTri
