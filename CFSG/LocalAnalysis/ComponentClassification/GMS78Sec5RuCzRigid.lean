module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCzRigidTab
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCzChecks

public section

namespace CFSG.ComponentClassification.GMS78.RuCz

open Subgroup CFSG.CosetTable CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Fischer CFSG.RankThree.Native RigidTab
open CFSG.EvenSporadicStandard.Fin76b
open CFSG.EvenSporadicStandard.Fin76b.AutETable (tab ix tab_getD ix_tab Realizes ev_congr)

section Words

variable {G G' : Type*} [Group G] [Group G']

theorem evalC_map' (φ : G →* G') (g : ℕ → G) (w : List ℕ) :
    φ (Sign.evalC g w) = Sign.evalC (fun j => φ (g j)) w := by
  induction w with
  | nil => rw [Sign.evalC_nil, Sign.evalC_nil, map_one]
  | cons l w ih =>
    rw [Sign.evalC_cons, Sign.evalC_cons, map_mul, ih]
    split <;> simp

theorem wordOfCodes6_single : ∀ c (hc : c < 12),
    wordOfCodes 6 [c] = [(⟨c / 2, by omega⟩, c % 2 == 0)] := by
  decide

theorem lift_mk_wordOfCodes6 (x : Fin 6 → G) {w : List ℕ} (hw : ∀ c ∈ w, c < 12) :
    FreeGroup.lift x (FreeGroup.mk (wordOfCodes 6 w)) =
      Sign.evalC (fun i => if hi : i < 6 then x ⟨i, hi⟩ else 1) w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    have hc : c < 12 := hw c List.mem_cons_self
    have hw' : ∀ c ∈ w, c < 12 := fun c' h => hw c' (List.mem_cons_of_mem _ h)
    have e : wordOfCodes 6 (c :: w) = wordOfCodes 6 [c] ++ wordOfCodes 6 w := by
      simp only [wordOfCodes, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [e, ← FreeGroup.mul_mk, map_mul, ih hw', wordOfCodes6_single c hc, Sign.evalC_cons]
    simp only [show c / 2 < 6 by omega, ↓reduceDIte]
    congr 1
    rcases Nat.mod_two_eq_zero_or_one c with h2 | h2
    · simp only [h2, ↓reduceIte]
      exact FreeGroup.lift_apply_of
    · simp only [h2, one_ne_zero, ↓reduceIte]
      change FreeGroup.lift x (FreeGroup.of _)⁻¹ = _
      rw [map_inv, FreeGroup.lift_apply_of]

theorem czRelsJ_lt : ∀ r ∈ czRelsJ, ∀ c ∈ r, c < 12 := by decide

theorem rels_of (x : Fin 6 → G)
    (h : ∀ w ∈ czRelsJ, Sign.evalC (fun i => if hi : i < 6 then x ⟨i, hi⟩ else 1) w = 1) :
    ∀ r ∈ {r : FreeGroup (Fin 6) | r ∈ czRelsJW.map FreeGroup.mk}, FreeGroup.lift x r = 1 := by
  intro r hr
  simp only [Set.mem_ofPred_eq, czRelsJW, List.map_map, List.mem_map, Function.comp_apply] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  rw [lift_mk_wordOfCodes6 x (czRelsJ_lt w hw), h w hw]

end Words

structure TabFacts : Prop where
  enum : enumOK 128 czT128 czBase128 czJCert = true
  tab : tableOK czN czJCert czJTab czJInv czJGens = true
  rels : relsHold czJTab czJInv czRelsJ czJGens = true

theorem tabFacts_of_rigid (h : czRigidCheck = true) : TabFacts := by
  simp only [czRigidCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩

theorem czT128_size : czT128.size = 6 := by decide

theorem czBase128_lt : ∀ p ∈ czBase128, p < 128 := by decide

namespace TabFacts

variable (F : TabFacts)
include F

theorem size : czJCert.pts.size = czN := by
  have h := F.tab
  simp only [tableOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

theorem treeTab {a : ℕ} (ha0 : 0 < a) (ha : a < czN) :
    AutETable.mt czJTab (czJGens.getD (ix czJCert.lab a) 0) (ix czJCert.par a) = a := by
  have h := F.tab
  simp only [tableOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq] at h
  rcases h.1.2 a ha with h0 | h1
  · omega
  · exact h1

theorem invOK : InvOK czN czJTab czJInv := by
  have h := F.tab
  simp only [tableOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq] at h
  exact fun a ha => h.2 a ha

theorem realizes :
    Realizes (↥(closure (permsA 128 czT128))) czN czJTab (ptElt 128 czT128 czJCert) := by
  have h := realizes_tabOf czBase128_lt F.enum F.size
  rwa [czT128_size] at h

omit F in
theorem gens_getD {j : ℕ} (hj : j < 6) : czJGens.getD j 0 = gIdx czJCert j := by
  simp [czJGens, hj]

theorem gens_getD_lt (j : ℕ) : czJGens.getD j 0 < czN := by
  by_cases hj : j < 6
  · rw [TabFacts.gens_getD hj, ← F.size]
    exact (ptPerm_gIdx F.enum (by rw [czT128_size]; exact hj)).1
  · have : czJGens.getD j 0 = 0 := by simp [czJGens, hj]
    rw [this]
    decide

theorem tree {a : ℕ} (ha0 : 0 < a) (ha : a < czN) :
    ix czJCert.par a < a ∧ ix czJCert.lab a < 6 := by
  obtain ⟨hp, hl, -⟩ := ptPerm_tree F.enum ha0 (F.size ▸ ha)
  rw [czT128_size] at hl
  exact ⟨by rw [ix, ← getElem!_eq_getD]; exact hp, by rw [ix, ← getElem!_eq_getD]; exact hl⟩

theorem homVal_eq {H : Type*} [Group H] {elt : ℕ → H} (R : Realizes H czN czJTab elt)
    (φ : H →* H) {t : List ℕ}
    (ht : ∀ j < 6, t.getD j 0 = idxMap R φ (czJGens.getD j 0)) {a : ℕ} (ha : a < czN) :
    homVal czJTab czJCert t czN a = idxMap R φ a := by
  refine RigidTab.homVal_eq (gi := czJGens) (fun b hb0 hb => ?_)
    (fun a b ha hb => idxMap_mt R φ ha hb)
    (idxMap_zero R φ) czN a ha ha
  obtain ⟨hp, hl⟩ := F.tree hb0 hb
  exact ⟨hp, F.gens_getD_lt _, F.treeTab hb0 hb, ht _ hl⟩

end TabFacts

abbrev FJ : Type := PG 6 czRelsJW

abbrev FJCard : Prop := Finite FJ ∧ Nat.card FJ ≤ 2048

section Present

variable (F : TabFacts)

@[expose] noncomputable def jGen (i : Fin 6) : ↥(closure (permsA 128 czT128)) :=
  ptElt 128 czT128 czJCert (gIdx czJCert i)

include F in
theorem elt_gens (j : ℕ) :
    ptElt 128 czT128 czJCert (czJGens.getD j 0) = if hj : j < 6 then jGen ⟨j, hj⟩ else 1 := by
  by_cases hj : j < 6
  · simp only [hj, ↓reduceDIte]
    rw [TabFacts.gens_getD hj]
    rfl
  · simp only [hj, ↓reduceDIte]
    have : czJGens.getD j 0 = 0 := by simp [czJGens, hj]
    rw [this]
    exact F.realizes.one

include F in
theorem jGen_rels : ∀ w ∈ czRelsJ,
    Sign.evalC (fun i => if hi : i < 6 then jGen ⟨i, hi⟩ else 1) w = 1 := by
  intro w hw
  have h := F.rels
  simp only [relsHold, List.all_eq_true, beq_iff_eq] at h
  have e := elt_evW F.realizes F.invOK F.gens_getD_lt w
  rw [h w hw, F.realizes.one] at e
  have e2 : (fun i => if hi : i < 6 then jGen ⟨i, hi⟩ else 1) =
      fun j => ptElt 128 czT128 czJCert (czJGens.getD j 0) :=
    funext fun j => (elt_gens F j).symm
  rw [e2, ← e]

@[expose] noncomputable def rhoJ : FJ →* ↥(closure (permsA 128 czT128)) :=
  PresentedGroup.toGroup (rels_of jGen (jGen_rels F))

theorem rhoJ_of (i : Fin 6) : rhoJ F (PresentedGroup.of i) = jGen i :=
  PresentedGroup.toGroup.of _

include F in
theorem coe_jGen (i : Fin 6) :
    (jGen i : Equiv.Perm (Fin 128)) = permOfArr 128 czT128[(i : ℕ)]! := by
  have hi : (i : ℕ) < czT128.size := by rw [czT128_size]; exact i.2
  rw [jGen, coe_ptElt czBase128_lt F.enum (ptPerm_gIdx F.enum hi).1, (ptPerm_gIdx F.enum hi).2]

theorem rhoJ_surjective : Function.Surjective (rhoJ F) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff,
    ← closure_closure_coe_preimage (k := permsA 128 czT128), closure_le]
  rintro x ⟨j, hj, hjx⟩
  have hj6 : j < 6 := by rwa [czT128_size] at hj
  refine ⟨PresentedGroup.of ⟨j, hj6⟩, ?_⟩
  rw [rhoJ_of]
  exact Subtype.ext ((coe_jGen F ⟨j, hj6⟩).trans hjx)

theorem card_FJ_le (hb : FJCard) : Finite FJ ∧ Nat.card FJ ≤ 2048 :=
  hb

include F in
theorem card_closure_czT128 : Nat.card (closure (permsA 128 czT128)) = 2048 := by
  rw [card_closure_permsA czBase128_lt F.enum, F.size]

@[expose] noncomputable def rhoEquiv (hb : FJCard) :
    FJ ≃* ↥(closure (permsA 128 czT128)) :=
  have : Finite FJ := (card_FJ_le hb).1
  MulEquiv.ofBijective (rhoJ F) ((rhoJ_surjective F).bijective_of_nat_card_le
    ((card_FJ_le hb).2.trans (card_closure_czT128 F).ge))

theorem rhoEquiv_apply (hb : FJCard) (x : FJ) : rhoEquiv F hb x = rhoJ F x := rfl

end Present

section Realize

variable {K : Type*} [Group K]

abbrev jSub (k : ℕ → K) : Subgroup K := closure (k '' {i | i < 6})

@[expose] def kQ (k : ℕ → K) (i : Fin 6) : ↥(jSub k) := ⟨k i, subset_closure ⟨i, i.2, rfl⟩⟩

theorem evalC_mem (k : ℕ → K) {w : List ℕ} (hw : ∀ c ∈ w, c < 12) :
    Sign.evalC k w ∈ jSub k := by
  induction w with
  | nil => rw [Sign.evalC_nil]; exact one_mem _
  | cons c w ih =>
    have hc : c / 2 < 6 := by have := hw c List.mem_cons_self; omega
    have hk : k (c / 2) ∈ jSub k := subset_closure ⟨c / 2, hc, rfl⟩
    rw [Sign.evalC_cons]
    refine mul_mem ?_ (ih fun c' h => hw c' (List.mem_cons_of_mem _ h))
    split
    · exact hk
    · exact inv_mem hk

theorem coe_evalC_kQ (k : ℕ → K) {w : List ℕ} (hw : ∀ c ∈ w, c < 12) :
    ((Sign.evalC (fun i => if hi : i < 6 then kQ k ⟨i, hi⟩ else 1) w : ↥(jSub k)) : K) =
      Sign.evalC k w := by
  rw [← (jSub k).coe_subtype, evalC_map']
  apply Sign.evalC_congr
  intro c hc
  have h6 : c / 2 < 6 := by have := hw c hc; omega
  simp only [h6, ↓reduceDIte, coe_subtype]
  rfl

theorem kQ_rels (k : ℕ → K) (hrel : ∀ r ∈ czRelsJ, Sign.evalC k r = 1) :
    ∀ w ∈ czRelsJ, Sign.evalC (fun i => if hi : i < 6 then kQ k ⟨i, hi⟩ else 1) w = 1 := by
  intro w hw
  apply Subtype.ext
  rw [coe_evalC_kQ k (czRelsJ_lt w hw), hrel w hw]
  rfl

@[expose] noncomputable def psiJ (k : ℕ → K) (hrel : ∀ r ∈ czRelsJ, Sign.evalC k r = 1) :
    FJ →* ↥(jSub k) :=
  PresentedGroup.toGroup (rels_of (kQ k) (kQ_rels k hrel))

theorem psiJ_of (k : ℕ → K) (hrel : ∀ r ∈ czRelsJ, Sign.evalC k r = 1) (i : Fin 6) :
    psiJ k hrel (PresentedGroup.of i) = kQ k i :=
  PresentedGroup.toGroup.of _

theorem psiJ_surjective (k : ℕ → K) (hrel : ∀ r ∈ czRelsJ, Sign.evalC k r = 1) :
    Function.Surjective (psiJ k hrel) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff,
    ← closure_closure_coe_preimage (k := k '' {i | i < 6}), closure_le]
  rintro x ⟨j, hj, hjx⟩
  refine ⟨PresentedGroup.of ⟨j, hj⟩, ?_⟩
  rw [psiJ_of]
  exact Subtype.ext hjx

@[expose] noncomputable def psiEquiv (hb : FJCard) (k : ℕ → K)
    (hrel : ∀ r ∈ czRelsJ, Sign.evalC k r = 1) (hcard : Nat.card (jSub k) = 2048) :
    FJ ≃* ↥(jSub k) :=
  have : Finite FJ := (card_FJ_le hb).1
  MulEquiv.ofBijective (psiJ k hrel) ((psiJ_surjective k hrel).bijective_of_nat_card_le
    ((card_FJ_le hb).2.trans hcard.ge))

theorem psiEquiv_apply (hb : FJCard) (k : ℕ → K)
    (hrel : ∀ r ∈ czRelsJ, Sign.evalC k r = 1) (hcard : Nat.card (jSub k) = 2048) (x : FJ) :
    psiEquiv hb k hrel hcard x = psiJ k hrel x := rfl

variable (F : TabFacts) (hb : FJCard) (k : ℕ → K)
  (hrel : ∀ r ∈ czRelsJ, Sign.evalC k r = 1) (hcard : Nat.card (jSub k) = 2048)

@[expose] noncomputable def eltQ (a : ℕ) : ↥(jSub k) :=
  ((rhoEquiv F hb).symm.trans (psiEquiv hb k hrel hcard)) (ptElt 128 czT128 czJCert a)

theorem realizes_czJ : Realizes (↥(jSub k)) czN czJTab (eltQ F hb k hrel hcard) :=
  realizes_map F.realizes _

theorem eltQ_gens (j : ℕ) :
    eltQ F hb k hrel hcard (czJGens.getD j 0) = if hj : j < 6 then kQ k ⟨j, hj⟩ else 1 := by
  rw [eltQ, elt_gens F j]
  by_cases hj : j < 6
  · simp only [hj, ↓reduceDIte]
    rw [← rhoJ_of F ⟨j, hj⟩, ← rhoEquiv_apply F hb, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, psiEquiv_apply, psiJ_of]
  · simp only [hj, ↓reduceDIte, map_one]

theorem coe_eltQ_evW {w : List ℕ} (hw : ∀ c ∈ w, c < 12) :
    (eltQ F hb k hrel hcard (evW czJTab czJInv czJGens w) : K) = Sign.evalC k w := by
  rw [elt_evW (realizes_czJ F hb k hrel hcard) F.invOK F.gens_getD_lt w]
  have e : (fun j => eltQ F hb k hrel hcard (czJGens.getD j 0)) =
      fun i => if hi : i < 6 then kQ k ⟨i, hi⟩ else 1 :=
    funext fun j => eltQ_gens F hb k hrel hcard j
  rw [e, coe_evalC_kQ k hw]

theorem idx_evalC {w : List ℕ} (hw : ∀ c ∈ w, c < 12) :
    idx (realizes_czJ F hb k hrel hcard) ⟨Sign.evalC k w, evalC_mem k hw⟩ =
      evW czJTab czJInv czJGens w := by
  rw [idx_eq_iff _ (evW_lt (realizes_czJ F hb k hrel hcard) F.invOK F.gens_getD_lt w)]
  exact Subtype.ext (coe_eltQ_evW F hb k hrel hcard hw).symm

end Realize

section Conj

variable {K : Type*} [Group K]

@[expose] def conjQ (Q : Subgroup K) (y : K) (hy : ∀ u ∈ Q, y⁻¹ * u * y ∈ Q) : ↥Q →* ↥Q where
  toFun u := ⟨y⁻¹ * u * y, hy u u.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext (by simp [mul_assoc])

theorem coe_conjQ (Q : Subgroup K) (y : K) (hy : ∀ u ∈ Q, y⁻¹ * u * y ∈ Q) (u : ↥Q) :
    (conjQ Q y hy u : K) = y⁻¹ * u * y := rfl

theorem conj_mem_jSub {k : ℕ → K} {y : K} (h : ∀ i < 6, y⁻¹ * k i * y ∈ jSub k) :
    ∀ u ∈ jSub k, y⁻¹ * u * y ∈ jSub k := by
  intro u hu
  have hle : jSub k ≤ (jSub k).comap (MulAut.conj y⁻¹).toMonoidHom := by
    rw [jSub, closure_le]
    rintro _ ⟨i, hi, rfl⟩
    simpa [MulAut.conj_apply] using h i hi
  simpa [MulAut.conj_apply] using hle hu

theorem conj_mem_of_words {k : ℕ → K} {y : K} {W : List (List ℕ)}
    (hW : ∀ i < 6, ∀ c ∈ W.getD i [], c < 12)
    (h : ∀ i < 6, y⁻¹ * k i * y = Sign.evalC k (W.getD i [])) :
    ∀ u ∈ jSub k, y⁻¹ * u * y ∈ jSub k :=
  conj_mem_jSub fun i hi => (h i hi) ▸ evalC_mem k (hW i hi)

variable (F : TabFacts) (hb : FJCard) (k : ℕ → K)
  (hrel : ∀ r ∈ czRelsJ, Sign.evalC k r = 1) (hcard : Nat.card (jSub k) = 2048)

theorem idxMap_conjQ_gens {y : K} {W : List (List ℕ)}
    (hW : ∀ i < 6, ∀ c ∈ W.getD i [], c < 12)
    (h : ∀ i < 6, y⁻¹ * k i * y = Sign.evalC k (W.getD i []))
    (hy : ∀ u ∈ jSub k, y⁻¹ * u * y ∈ jSub k) {j : ℕ} (hj : j < 6) :
    idxMap (realizes_czJ F hb k hrel hcard) (conjQ (jSub k) y hy) (czJGens.getD j 0) =
      evW czJTab czJInv czJGens (W.getD j []) := by
  rw [idxMap, eltQ_gens F hb k hrel hcard j, ← idx_evalC F hb k hrel hcard (hW j hj)]
  simp only [hj, ↓reduceDIte]
  congr 1
  exact Subtype.ext (h j hj)

theorem getD_map_evW (W : List (List ℕ)) (j : ℕ) :
    (W.map (evW czJTab czJInv czJGens)).getD j 0 = evW czJTab czJInv czJGens (W.getD j []) := by
  have h0 : evW czJTab czJInv czJGens [] = 0 := rfl
  rw [← h0, List.getD_map]

theorem ix_homTab_conjQ {y : K} {W : List (List ℕ)} (hW : ∀ i < 6, ∀ c ∈ W.getD i [], c < 12)
    (h : ∀ i < 6, y⁻¹ * k i * y = Sign.evalC k (W.getD i []))
    (hy : ∀ u ∈ jSub k, y⁻¹ * u * y ∈ jSub k) {a : ℕ} (ha : a < czN) :
    ix (homTab czN czJTab czJCert (W.map (evW czJTab czJInv czJGens))) a =
      idxMap (realizes_czJ F hb k hrel hcard) (conjQ (jSub k) y hy) a := by
  rw [ix_homTab ha]
  refine F.homVal_eq (realizes_czJ F hb k hrel hcard) _ (fun j hj => ?_) ha
  rw [getD_map_evW, idxMap_conjQ_gens F hb k hrel hcard hW h hy hj]

end Conj

theorem czWq_lt : ∀ i < 6, ∀ c ∈ czWq.getD i [], c < 12 := by decide
theorem czWw_lt : ∀ i < 6, ∀ c ∈ czWw.getD i [], c < 12 := by decide
theorem czWv_lt : ∀ i < 6, ∀ c ∈ czWv.getD i [], c < 12 := by decide

theorem evW_congr {M : Array (Array ℕ)} {inv : Array ℕ} {t t' : List ℕ} {w : List ℕ}
    (h : ∀ c ∈ w, t.getD (c / 2) 0 = t'.getD (c / 2) 0) : evW M inv t w = evW M inv t' w := by
  unfold evW
  apply ev_congr
  intro c hc
  unfold letF
  rw [h c hc]

theorem relsHold_iff {M : Array (Array ℕ)} {inv : Array ℕ} {rs : List (List ℕ)} {t : List ℕ} :
    relsHold M inv rs t = true ↔ ∀ r ∈ rs, evW M inv t r = 0 := by
  simp [relsHold]

theorem czRels1_mem {r : List ℕ} (hr : r ∈ czRels1) : r ∈ czRelsJ ∧ ∀ c ∈ r, c < 4 := by
  simp only [czRels1, List.mem_filter, List.all_eq_true, decide_eq_true_eq] at hr
  exact hr

theorem czRels3_mem {r : List ℕ} (hr : r ∈ czRels3) : r ∈ czRelsJ ∧ ∀ c ∈ r, c < 8 := by
  simp only [czRels3, List.mem_filter, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at hr
  exact ⟨hr.1, hr.2.1⟩

theorem czRels5_mem {r : List ℕ} (hr : r ∈ czRels5) : r ∈ czRelsJ := by
  simp only [czRels5, List.mem_filter] at hr
  exact hr.1

theorem czWq3_letters : ∀ c ∈ czWq.getD 3 [], c / 2 = 2 ∨ c / 2 = 3 := by decide

theorem czWq5_letters : ∀ c ∈ czWq.getD 5 [], c / 2 = 4 ∨ c / 2 = 5 := by decide

theorem czSols_lt : ∀ s < 8, ∀ i < 6, ∀ c ∈ (czSols.getD s []).getD i [], c < 12 := by decide

theorem mt_conj {H : Type*} [Group H] {elt : ℕ → H} (R : Realizes H czN czJTab elt)
    (hinv : InvOK czN czJTab czJInv) {d g : ℕ} (hd : d < czN) (hg : g < czN) :
    AutETable.mt czJTab (AutETable.mt czJTab (ix czJInv d) g) d =
      idx R ((elt d)⁻¹ * elt g * elt d) := by
  have hi := (hinv d hd).1
  rw [eq_comm, idx_eq_iff R (R.lt _ _ (R.lt _ _ hi hg) hd), R.mul _ _ (R.lt _ _ hi hg) hd,
    R.mul _ _ hi hg, elt_inv R hinv hd]

theorem czRigid_of (hb : FJCard) (hc : czRigidCheck = true) {K : Type*} [Group K]
    (k : ℕ → K) (hrel : ∀ r ∈ czRelsJ, Sign.evalC k r = 1)
    (hcard : Nat.card (closure (k '' {i | i < 6})) = 2048) {yq yw h : K}
    (hq : ∀ i < 6, yq⁻¹ * k i * yq = Sign.evalC k (czWq.getD i []))
    (hw : ∀ i < 6, yw⁻¹ * k i * yw = Sign.evalC k (czWw.getD i []))
    (hn : ∀ i < 6, h⁻¹ * k i * h ∈ closure (k '' {i | i < 6}))
    (hhq : h * yq = yq * h) (h3 : (yw * h) ^ 3 ∈ closure (k '' {i | i < 6})) :
    ∃ s < 8, ∀ i < 6, h⁻¹ * k i * h = Sign.evalC k ((czSols.getD s []).getD i []) := by
  have F := tabFacts_of_rigid hc
  have hS : rigidSearch czN czJTab czJInv czJCert czJGens = true := by
    simp only [czRigidCheck, Bool.and_eq_true] at hc
    exact hc.2
  unfold rigidSearch at hS
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.mem_filter, List.mem_range] at hS
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h4⟩, hall⟩ := hS
  set R := realizes_czJ F hb k hrel hcard with hR
  have hqQ := conj_mem_of_words czWq_lt hq
  have hwQ := conj_mem_of_words czWw_lt hw
  have hhQ := conj_mem_jSub hn
  set cq := conjQ (jSub k) yq hqQ with hcq
  set cw := conjQ (jSub k) yw hwQ with hcw
  set ch := conjQ (jSub k) h hhQ with hch
  set kq := homTab czN czJTab czJCert (czWq.map (evW czJTab czJInv czJGens)) with hkq
  set kw := homTab czN czJTab czJCert (czWw.map (evW czJTab czJInv czJGens)) with hkw
  have ekq : ∀ a < czN, ix kq a = idxMap R cq a := fun a ha =>
    ix_homTab_conjQ F hb k hrel hcard czWq_lt hq hqQ ha
  have ekw : ∀ a < czN, ix kw a = idxMap R cw a := fun a ha =>
    ix_homTab_conjQ F hb k hrel hcard czWw_lt hw hwQ ha
  set σ := idxMap R ch with hσ
  have hσlt : ∀ a, σ a < czN := idxMap_lt R ch
  have hgl := F.gens_getD_lt
  have hcomm : ∀ a, idxMap R cq (σ a) = σ (idxMap R cq a) := by
    intro a
    rw [hσ, idxMap_comp, idxMap_comp]
    congr 1
    funext u
    apply Subtype.ext
    simp only [Function.comp_apply, hcq, hch, coe_conjQ]
    calc yq⁻¹ * (h⁻¹ * ↑u * h) * yq = (h * yq)⁻¹ * ↑u * (h * yq) := by group
      _ = (yq * h)⁻¹ * ↑u * (yq * h) := by rw [hhq]
      _ = h⁻¹ * (yq⁻¹ * ↑u * yq) * h := by group
  set a : ℕ → ℕ := fun i => σ (czJGens.getD i 0) with ha
  have hkqa : ∀ i, ix kq (a i) = σ (ix kq (czJGens.getD i 0)) := fun i => by
    rw [ekq _ (hσlt _), hcomm, ← ekq _ (hgl i)]
  have hq3 : ix kq (czJGens.getD 3 0) = evW czJTab czJInv czJGens (czWq.getD 3 []) := by
    rw [ekq _ (hgl 3), idxMap_conjQ_gens F hb k hrel hcard czWq_lt hq hqQ (by norm_num)]
  have hq5 : ix kq (czJGens.getD 5 0) = evW czJTab czJInv czJGens (czWq.getD 5 []) := by
    rw [ekq _ (hgl 5), idxMap_conjQ_gens F hb k hrel hcard czWq_lt hq hqQ (by norm_num)]
  set t : List ℕ := [a 0, a 1, a 2, a 3, a 4, a 5] with htdef
  have htg : ∀ j, t.getD j 0 = σ (czJGens.getD j 0) := by
    intro j
    rcases Nat.lt_or_ge j 6 with hj | hj
    · interval_cases j <;> rfl
    · have e1 : t.getD j 0 = 0 := by
        rw [htdef, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
        rfl
      have e2 : czJGens.getD j 0 = 0 := by simp [czJGens, show ¬ j < 6 by omega]
      rw [e1, e2, hσ, idxMap_zero]
  have htσ : ∀ w, evW czJTab czJInv t w = σ (evW czJTab czJInv czJGens w) := by
    intro w
    rw [hσ, idxMap_evW R F.invOK ch hgl w]
    apply evW_congr
    intro c _
    rw [htg, getD_map_idxMap]
  have hrels : ∀ r ∈ czRelsJ, evW czJTab czJInv t r = 0 := by
    intro r hr
    have h' := F.rels
    rw [relsHold_iff] at h'
    rw [htσ, h' r hr, hσ, idxMap_zero]
  have hfix0 : a 0 < czN ∧ ix kq (a 0) = a 0 := ⟨hσlt _, by rw [hkqa, h0]⟩
  have hfix1 : a 1 < czN ∧ ix kq (a 1) = a 1 := ⟨hσlt _, by rw [hkqa, h1]⟩
  have hk2 : ix kq (a 2) = a 3 := by rw [hkqa, h2]
  have hk4 : ix kq (a 4) = a 5 := by rw [hkqa, h4]
  have hd3 : a 2 < czN ∧ ix kq (ix kq (a 2)) =
      evW czJTab czJInv [0, 0, a 2, ix kq (a 2), 0, 0] (czWq.getD 3 []) := by
    refine ⟨hσlt _, ?_⟩
    rw [hk2, hkqa, hq3, ← htσ]
    apply evW_congr
    intro c hc
    rcases czWq3_letters c hc with e | e <;> rw [e] <;> rfl
  have hd5 : a 4 < czN ∧ ix kq (ix kq (a 4)) =
      evW czJTab czJInv [0, 0, 0, 0, a 4, ix kq (a 4)] (czWq.getD 5 []) := by
    refine ⟨hσlt _, ?_⟩
    rw [hk4, hkqa, hq5, ← htσ]
    apply evW_congr
    intro c hc
    rcases czWq5_letters c hc with e | e <;> rw [e] <;> rfl
  have hr1 : relsHold czJTab czJInv czRels1 [a 0, a 1, 0, 0, 0, 0] = true := by
    rw [relsHold_iff]
    intro r hr
    obtain ⟨hrJ, hr4⟩ := czRels1_mem hr
    have e : evW czJTab czJInv [a 0, a 1, 0, 0, 0, 0] r = evW czJTab czJInv t r := by
      apply evW_congr
      intro c hc
      have : c / 2 = 0 ∨ c / 2 = 1 := by have := hr4 c hc; omega
      rcases this with e | e <;> rw [e] <;> rfl
    rw [e]
    exact hrels r hrJ
  have hr3 : relsHold czJTab czJInv czRels3 [a 0, a 1, a 2, ix kq (a 2), 0, 0] = true := by
    rw [relsHold_iff]
    intro r hr
    obtain ⟨hrJ, hr8⟩ := czRels3_mem hr
    have e : evW czJTab czJInv [a 0, a 1, a 2, ix kq (a 2), 0, 0] r = evW czJTab czJInv t r := by
      rw [hk2]
      apply evW_congr
      intro c hc
      have : c / 2 = 0 ∨ c / 2 = 1 ∨ c / 2 = 2 ∨ c / 2 = 3 := by have := hr8 c hc; omega
      rcases this with e | e | e | e <;> rw [e] <;> rfl
    rw [e]
    exact hrels r hrJ
  have ht' : [a 0, a 1, a 2, ix kq (a 2), a 4, ix kq (a 4)] = t := by rw [hk2, hk4]
  have hr5 : relsHold czJTab czJInv czRels5 [a 0, a 1, a 2, ix kq (a 2), a 4, ix kq (a 4)] =
      true := by
    rw [ht', relsHold_iff]
    exact fun r hr => hrels r (czRels5_mem hr)
  have hphi : ∀ b < czN, homVal czJTab czJCert t czN (ix kw b) = idxMap R (ch ∘ cw) b := by
    intro b hb'
    rw [ekw b hb', F.homVal_eq R ch (fun j _ => htg j) (idxMap_lt R cw b), idxMap_comp]
  have hcube : cubeInner czN czJTab czJCert czJGens (conjTuples czN czJTab czJInv czJGens) kw
      [a 0, a 1, a 2, ix kq (a 2), a 4, ix kq (a 4)] = true := by
    rw [ht']
    unfold cubeInner
    rw [List.contains_iff_mem]
    set D : ↥(jSub k) := ⟨(yw * h) ^ 3, h3⟩ with hD
    refine List.mem_map.mpr ⟨idx R D, List.mem_range.mpr (idx_lt R D), ?_⟩
    apply List.map_congr_left
    intro g hg
    have hg' : g < czN := by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
      have := hgl j
      rwa [TabFacts.gens_getD (List.mem_range.mp hj)] at this
    dsimp only
    rw [hphi g hg', hphi _ (idxMap_lt R _ _), hphi _ (idxMap_lt R _ _), idxMap_comp, idxMap_comp,
      mt_conj R F.invOK (idx_lt R D) hg', idxMap, elt_idx R]
    congr 1
    apply Subtype.ext
    simp only [hD, Function.comp_apply, hch, hcw, coe_conjQ, Subgroup.coe_mul, Subgroup.coe_inv,
      pow_three]
    group
  have hm1 := hall (a 0) hfix0 (a 1) hfix1
  rw [hr1] at hm1
  have hm2 := (hm1.resolve_left (by decide)) (a 2) hd3
  rw [hr3] at hm2
  have hm3 := (hm2.resolve_left (by decide)) (a 4) hd5
  rw [hr5, hcube] at hm3
  have hm4 := hm3.resolve_left (by decide)
  rw [ht', List.contains_iff_mem, List.mem_map] at hm4
  obtain ⟨S, hS, hSt⟩ := hm4
  obtain ⟨s, hs, hsS⟩ := List.getElem_of_mem hS
  have hs8 : s < 8 := by
    have e8 : czSols.length = 8 := rfl
    rwa [e8] at hs
  have eS : czSols.getD s [] = S := by rw [List.getD_eq_getElem _ _ hs, hsS]
  refine ⟨s, hs8, fun i hi => ?_⟩
  have e1 : h⁻¹ * k i * h = (eltQ F hb k hrel hcard (σ (czJGens.getD i 0)) : K) := by
    rw [hσ, elt_idxMap R ch, eltQ_gens F hb k hrel hcard i]
    simp only [hi, ↓reduceDIte]
    rfl
  rw [e1, ← htg i, ← hSt, getD_map_evW, eS.symm,
    coe_eltQ_evW F hb k hrel hcard (czSols_lt s hs8 i hi)]

theorem czNormX_lt : ∀ s < 4, ∀ c ∈ czNormX.getD s [], c < 12 := by decide

theorem czHTarget_lt : ∀ i < 6, ∀ c ∈ czHTarget i, c < 12 := by decide

theorem c2JCodes_lt : ∀ i < 6, ∀ c ∈ c2JCodes.getD i [], c < 12 := by decide

theorem getD_sols (s i : ℕ) :
    ((czSols.map fun S => S.map (evW czJTab czJInv czJGens)).getD s []).getD i 0 =
      evW czJTab czJInv czJGens ((czSols.getD s []).getD i []) := by
  rw [List.getD_eq_getElem?_getD (l := czSols.map fun S => S.map (evW czJTab czJInv czJGens)),
    List.getElem?_map, List.getD_eq_getElem?_getD (l := czSols)]
  cases czSols[s]? with
  | none => rfl
  | some S => exact getD_map_evW S i

theorem getD_range_evW (f : ℕ → List ℕ) {i : ℕ} (hi : i < 6) :
    ((List.range 6).map fun j => evW czJTab czJInv czJGens (f j)).getD i 0 =
      evW czJTab czJInv czJGens (f i) := by
  simp [hi]

theorem czNorm_of (hb : FJCard) (hc : czRigidCheck = true)
    (hd : czJIdentCheck = true) {K : Type*} [Group K] (k : ℕ → K)
    (hrel : ∀ r ∈ czRelsJ, Sign.evalC k r = 1)
    (hcard : Nat.card (closure (k '' {i | i < 6})) = 2048) {h : K} {s : ℕ} (hs : s < 4)
    (hh : ∀ i < 6, h⁻¹ * k i * h = Sign.evalC k ((czSols.getD s []).getD i [])) :
    ∀ i < 6, (h * Sign.evalC k (czNormX.getD s []))⁻¹ * k i *
      (h * Sign.evalC k (czNormX.getD s [])) = Sign.evalC k (czHTarget i) := by
  intro i hi
  have F := tabFacts_of_rigid hc
  set R := realizes_czJ F hb k hrel hcard
  have hI := hd
  simp only [czJIdentCheck, identSearch, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    beq_iff_eq] at hI
  have e := hI.2.1.1.1.1.1 s hs i hi
  rw [getD_sols, getD_range_evW _ hi] at e
  set x := evW czJTab czJInv czJGens (czNormX.getD s [])
  have hx : x < czN := evW_lt R F.invOK F.gens_getD_lt _
  have hsol : evW czJTab czJInv czJGens ((czSols.getD s []).getD i []) < czN :=
    evW_lt R F.invOK F.gens_getD_lt _
  rw [mt_conj R F.invOK hx hsol] at e
  have e2 := congrArg (fun a => (eltQ F hb k hrel hcard a : K)) e
  rw [elt_idx R, coe_eltQ_evW F hb k hrel hcard (czHTarget_lt i hi)] at e2
  rw [← e2, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_eltQ_evW F hb k hrel hcard (czNormX_lt s hs),
    coe_eltQ_evW F hb k hrel hcard (czSols_lt s (by omega) i hi), ← hh i hi]
  group

@[expose] noncomputable def fjOf (i : ℕ) : FJ := if h : i < 6 then PresentedGroup.of ⟨i, h⟩ else 1

theorem rho_evalC_fjOf (F : TabFacts) (hb : FJCard) (w : List ℕ) :
    rhoEquiv F hb (Sign.evalC fjOf w) =
      ptElt 128 czT128 czJCert (evW czJTab czJInv czJGens w) := by
  rw [← MulEquiv.coe_toMonoidHom, evalC_map', elt_evW F.realizes F.invOK F.gens_getD_lt w]
  congr 1
  funext j
  rw [elt_gens F j, MulEquiv.coe_toMonoidHom, rhoEquiv_apply]
  unfold fjOf
  split
  · exact rhoJ_of F _
  · exact map_one _

theorem coe_psi_evalC_fjOf {K : Type*} [Group K] (hb : FJCard) (k : ℕ → K)
    (hrel : ∀ r ∈ czRelsJ, Sign.evalC k r = 1) (hcard : Nat.card (jSub k) = 2048)
    {w : List ℕ} (hw : ∀ c ∈ w, c < 12) :
    (psiEquiv hb k hrel hcard (Sign.evalC fjOf w) : K) = Sign.evalC k w := by
  rw [← MulEquiv.coe_toMonoidHom, evalC_map', ← coe_evalC_kQ k hw]
  congr 2
  funext j
  rw [MulEquiv.coe_toMonoidHom, psiEquiv_apply]
  unfold fjOf
  split
  · exact psiJ_of k hrel _
  · exact map_one _

@[expose] noncomputable def gammaFJ (F : TabFacts) (hb : FJCard)
    (hγ : relsHold czJTab czJInv czRelsJ
      ((List.range 6).map fun i => evW czJTab czJInv czJGens (c2JCodes.getD i [])) = true) :
    FJ →* FJ :=
  PresentedGroup.toGroup (rels_of (fun i : Fin 6 => Sign.evalC fjOf (c2JCodes.getD i [])) (by
    intro w hw
    apply (rhoEquiv F hb).injective
    rw [map_one, ← MulEquiv.coe_toMonoidHom, evalC_map']
    set γg := (List.range 6).map fun i => evW czJTab czJInv czJGens (c2JCodes.getD i [])
    have hγlt : ∀ j, γg.getD j 0 < czN := fun j =>
      getD_map_lt (σ := fun i => evW czJTab czJInv czJGens (c2JCodes.getD i []))
        (fun _ => evW_lt F.realizes F.invOK F.gens_getD_lt _) (by decide) (List.range 6) j
    rw [relsHold_iff] at hγ
    have e := elt_evW F.realizes F.invOK hγlt w
    rw [hγ w hw, F.realizes.one] at e
    rw [e]
    congr 1
    funext j
    rw [MulEquiv.coe_toMonoidHom]
    by_cases hj : j < 6
    · simp only [hj, ↓reduceDIte]
      rw [rho_evalC_fjOf, getD_range_evW _ hj]
    · simp only [hj, ↓reduceDIte, map_one]
      have : γg.getD j 0 = 0 := by simp [γg, hj]
      rw [this, F.realizes.one]))

theorem gammaFJ_of (F : TabFacts) (hb : FJCard) (hγ) (i : Fin 6) :
    gammaFJ F hb hγ (PresentedGroup.of i) = Sign.evalC fjOf (c2JCodes.getD i []) :=
  PresentedGroup.toGroup.of _

theorem psiEquiv_symm_kQ {K : Type*} [Group K] (hb : FJCard) (k : ℕ → K)
    (hrel : ∀ r ∈ czRelsJ, Sign.evalC k r = 1) (hcard : Nat.card (jSub k) = 2048) (i : Fin 6) :
    (psiEquiv hb k hrel hcard).symm (kQ k i) = PresentedGroup.of i := by
  rw [MulEquiv.symm_apply_eq, psiEquiv_apply, psiJ_of]

theorem czClass2_of (hb : FJCard) (hc : czRigidCheck = true)
    (hd : czJIdentCheck = true) {K : Type*} [Group K] (k : ℕ → K)
    (hrel : ∀ r ∈ czRelsJ, Sign.evalC k r = 1)
    (hcard : Nat.card (closure (k '' {i | i < 6})) = 2048) {h : K} {s : ℕ} (hs4 : 4 ≤ s)
    (hs8 : s < 8) (hh : ∀ i < 6, h⁻¹ * k i * h = Sign.evalC k ((czSols.getD s []).getD i [])) :
    czClass2To1.getD (s - 4) 0 < 4 ∧ ∀ i < 6, h⁻¹ * Sign.evalC k (c2JCodes.getD i []) * h =
      Sign.evalC (fun j => Sign.evalC k (c2JCodes.getD j []))
        ((czSols.getD (czClass2To1.getD (s - 4) 0) []).getD i []) := by
  have F := tabFacts_of_rigid hc
  set R := realizes_czJ F hb k hrel hcard
  have hI := hd
  simp only [czJIdentCheck, identSearch, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    beq_iff_eq, decide_eq_true_eq] at hI
  have hγ := hI.2.1.1.1.1.2
  have hII := hI.2.1.1.1.2 (s - 4) (by omega)
  obtain ⟨hs', hII⟩ := hII
  refine ⟨hs', fun i hi => ?_⟩
  have e4 : s - 4 + 4 = s := by omega
  rw [e4] at hII
  set γQ : ↥(jSub k) →* ↥(jSub k) := (psiEquiv hb k hrel hcard).toMonoidHom.comp
    ((gammaFJ F hb hγ).comp (psiEquiv hb k hrel hcard).symm.toMonoidHom) with hγQ
  have hγk : ∀ j (hj : j < 6), (γQ (kQ k ⟨j, hj⟩) : K) = Sign.evalC k (c2JCodes.getD j []) := by
    intro j hj
    rw [hγQ, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.coe_toMonoidHom, psiEquiv_symm_kQ, gammaFJ_of,
      coe_psi_evalC_fjOf hb k hrel hcard (c2JCodes_lt j hj)]
  have hγgen : ∀ j < 6, idxMap R γQ (czJGens.getD j 0) =
      evW czJTab czJInv czJGens (c2JCodes.getD j []) := by
    intro j hj
    rw [idxMap, eltQ_gens F hb k hrel hcard j, ← idx_evalC F hb k hrel hcard (c2JCodes_lt j hj)]
    simp only [hj, ↓reduceDIte]
    congr 1
    exact Subtype.ext (hγk j hj)
  have hch := conj_mem_jSub (fun i hi => (hh i hi) ▸ evalC_mem k (czSols_lt s hs8 i hi))
  set ch := conjQ (jSub k) h hch
  have hchgen : ∀ j < 6, idxMap R ch (czJGens.getD j 0) =
      evW czJTab czJInv czJGens ((czSols.getD s []).getD j []) := fun j hj =>
    idxMap_conjQ_gens F hb k hrel hcard (czSols_lt s hs8) hh hch hj
  have egam : ∀ a < czN, ix (homTab czN czJTab czJCert
      ((List.range 6).map fun i => evW czJTab czJInv czJGens (c2JCodes.getD i []))) a =
      idxMap R γQ a := by
    intro a ha
    rw [ix_homTab ha]
    exact F.homVal_eq R γQ (fun j hj => by rw [getD_range_evW _ hj, hγgen j hj]) ha
  have eal : ∀ a < czN, ix (homTab czN czJTab czJCert
      ((czSols.map fun S => S.map (evW czJTab czJInv czJGens)).getD s [])) a = idxMap R ch a := by
    intro a ha
    rw [ix_homTab ha]
    exact F.homVal_eq R ch (fun j hj => by rw [getD_sols, hchgen j hj]) ha
  have e := hII i hi
  set s' := czClass2To1.getD (s - 4) 0
  rw [getD_sols, egam _ (F.gens_getD_lt i), egam _ (evW_lt R F.invOK F.gens_getD_lt _),
    eal _ (idxMap_lt R _ _)] at e
  have e2 := congrArg (fun a => (eltQ F hb k hrel hcard a : K)) e
  simp only [elt_idxMap R] at e2
  rw [eltQ_gens F hb k hrel hcard i] at e2
  simp only [hi, ↓reduceDIte] at e2
  have e2' : h⁻¹ * (γQ (kQ k ⟨i, hi⟩) : K) * h = (γQ (eltQ F hb k hrel hcard
      (evW czJTab czJInv czJGens ((czSols.getD s' []).getD i []))) : K) := e2
  rw [hγk i hi] at e2'
  rw [e2']
  have hw := czSols_lt s' (by omega) i hi
  have e3 : (⟨Sign.evalC k ((czSols.getD s' []).getD i []), evalC_mem k hw⟩ : ↥(jSub k)) =
      eltQ F hb k hrel hcard (evW czJTab czJInv czJGens ((czSols.getD s' []).getD i [])) :=
    Subtype.ext (coe_eltQ_evW F hb k hrel hcard hw).symm
  rw [← e3]
  have e4 : (⟨Sign.evalC k ((czSols.getD s' []).getD i []), evalC_mem k hw⟩ : ↥(jSub k)) =
      Sign.evalC (fun j => if hj : j < 6 then kQ k ⟨j, hj⟩ else 1)
        ((czSols.getD s' []).getD i []) :=
    Subtype.ext (coe_evalC_kQ k hw).symm
  rw [e4, evalC_map', ← (jSub k).coe_subtype, evalC_map']
  apply Sign.evalC_congr
  intro c hc
  have h6 : c / 2 < 6 := by have := hw c hc; omega
  simp only [h6, ↓reduceDIte, coe_subtype]
  exact hγk _ h6

section Signs

variable {K : Type*} [Group K] (F : TabFacts) (hb : FJCard) (x : ℕ → K)
  (hrel : ∀ r ∈ czRelsJ, Sign.evalC x r = 1) (hcard : Nat.card (jSub x) = 2048)

@[expose] def Represents (T : Array ℕ) (e : K) : Prop :=
  ∀ a < czN, T[a]! < czN ∧
    (eltQ F hb x hrel hcard T[a]! : K) = e⁻¹ * (eltQ F hb x hrel hcard a : K) * e

theorem represents_idA : Represents F hb x hrel hcard (idA czN) 1 := fun a ha => by
  rw [idA_get ha]
  exact ⟨ha, by group⟩

theorem represents_compA {T L : Array ℕ} {e y : K} (hT : Represents F hb x hrel hcard T e)
    (hL : Represents F hb x hrel hcard L y) :
    Represents F hb x hrel hcard (compA czN L T) (e * y) := fun a ha => by
  rw [compA_get ha]
  obtain ⟨h1, h2⟩ := hT a ha
  obtain ⟨h3, h4⟩ := hL _ h1
  refine ⟨h3, ?_⟩
  rw [h4, h2]
  group

@[expose] def lv (l : ℕ) : K := if l % 2 = 0 then x (l / 2) else (x (l / 2))⁻¹

theorem evalC_cons_lv (l : ℕ) (w : List ℕ) :
    Sign.evalC x (l :: w) = lv x l * Sign.evalC x w := by
  rw [Sign.evalC_cons, lv]

theorem represents_foldl (LT : ℕ → Array ℕ) :
    ∀ (w : List ℕ), (∀ l ∈ w, Represents F hb x hrel hcard (LT l) (lv x l)) →
      ∀ (T : Array ℕ) (e : K), Represents F hb x hrel hcard T e →
      Represents F hb x hrel hcard (w.foldl (fun T l => compA czN (LT l) T) T)
        (e * Sign.evalC x w)
  | [], _, T, e, hT => by rw [List.foldl_nil, Sign.evalC_nil, mul_one]; exact hT
  | l :: w, hLT, T, e, hT => by
    rw [List.foldl_cons, evalC_cons_lv, ← mul_assoc]
    exact represents_foldl LT w (fun l' h => hLT l' (List.mem_cons_of_mem _ h)) _ _
      (represents_compA F hb x hrel hcard hT (hLT l List.mem_cons_self))

theorem inv_conj_mem {Q : Subgroup K} [Finite Q] {y : K} (hy : ∀ u ∈ Q, y⁻¹ * u * y ∈ Q) :
    ∀ u ∈ Q, y * u * y⁻¹ ∈ Q := by
  intro u hu
  have hinj : Function.Injective (conjQ Q y hy) := fun a b hab => by
    have := congrArg Subtype.val hab
    simp only [coe_conjQ, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨u, hu⟩
  have e0 : y⁻¹ * (v : K) * y = u := congrArg Subtype.val hv
  have e : (v : K) = y * u * y⁻¹ := by
    rw [← e0]
    group
  rw [← e]
  exact v.2

theorem represents_homTab_conjQ {y : K} {W : List (List ℕ)}
    (hW : ∀ i < 6, ∀ c ∈ W.getD i [], c < 12)
    (hyW : ∀ i < 6, y⁻¹ * x i * y = Sign.evalC x (W.getD i [])) :
    Represents F hb x hrel hcard (homTab czN czJTab czJCert (W.map (evW czJTab czJInv czJGens)))
      y := fun a ha => by
  have hy := conj_mem_of_words hW hyW
  rw [getElem!_eq_getD, ← ix, ix_homTab_conjQ F hb x hrel hcard hW hyW hy ha]
  exact ⟨idxMap_lt _ _ _, by rw [elt_idxMap (realizes_czJ F hb x hrel hcard), coe_conjQ]⟩

theorem represents_invCand {T : Array ℕ} {y : K} (hT : Represents F hb x hrel hcard T y)
    (hinv : isInvA czN T (invCand czN T) = true) :
    Represents F hb x hrel hcard (invCand czN T) y⁻¹ := fun a ha => by
  set R := realizes_czJ F hb x hrel hcard
  have : Finite (jSub x) := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  have hyQ : ∀ u ∈ jSub x, y⁻¹ * u * y ∈ jSub x := by
    intro u hu
    obtain ⟨b, hb', hbu⟩ := R.surj ⟨u, hu⟩
    have := (hT b hb').2
    rw [hbu] at this
    rw [← this]
    exact (eltQ F hb x hrel hcard _).2
  have hm := inv_conj_mem hyQ _ (eltQ F hb x hrel hcard a).2
  set b := idx R ⟨y * eltQ F hb x hrel hcard a * y⁻¹, hm⟩
  have hb' : b < czN := idx_lt R _
  have hbe : (eltQ F hb x hrel hcard b : K) = y * eltQ F hb x hrel hcard a * y⁻¹ := by
    rw [elt_idx R]
  have hTb : T[b]! = a := by
    obtain ⟨h1, h2⟩ := hT b hb'
    apply R.inj _ _ h1 ha
    apply Subtype.ext
    rw [h2, hbe]
    group
  have := (isInvA_spec hinv hb').2
  rw [hTb] at this
  rw [this]
  exact ⟨hb', by rw [hbe]; group⟩

theorem represents_letterTab (Kt : Array (Array ℕ))
    (hK : ∀ j < 4, Represents F hb x hrel hcard (Kt.getD j #[]) (x (j + 6)))
    (hKinv : ∀ j < 4, isInvA czN (Kt.getD j #[]) (invCand czN (Kt.getD j #[])) = true)
    {l : ℕ} (hl : l < 20) :
    Represents F hb x hrel hcard (letterTab czN czJTab czJInv czJGens Kt l) (lv x l) := by
  set R := realizes_czJ F hb x hrel hcard
  unfold letterTab lv
  by_cases h12 : l < 12
  · simp only [h12, ↓reduceIte]
    have hl6 : l / 2 < 6 := by omega
    intro a ha
    by_cases hpar : l % 2 = 0
    · simp only [hpar, ↓reduceIte]
      have hg := F.gens_getD_lt (l / 2)
      rw [getElem!_eq_getD, tab_getD _ ha, mt_conj R F.invOK hg ha]
      refine ⟨idx_lt R _, ?_⟩
      rw [elt_idx R, eltQ_gens F hb x hrel hcard]
      simp only [hl6, ↓reduceDIte, Subgroup.coe_mul, Subgroup.coe_inv]
      rfl
    · simp only [hpar, ↓reduceIte]
      have hg := (F.invOK _ (F.gens_getD_lt (l / 2))).1
      rw [getElem!_eq_getD, tab_getD _ ha, mt_conj R F.invOK hg ha]
      refine ⟨idx_lt R _, ?_⟩
      rw [elt_idx R, elt_inv R F.invOK (F.gens_getD_lt _), eltQ_gens F hb x hrel hcard]
      simp only [hl6, ↓reduceDIte, Subgroup.coe_mul, Subgroup.coe_inv]
      rfl
  · simp only [h12, ↓reduceIte]
    have hj : l / 2 - 6 < 4 := by omega
    have hj6 : l / 2 - 6 + 6 = l / 2 := by omega
    split
    · have := hK _ hj
      rwa [hj6] at this
    · have := represents_invCand F hb x hrel hcard (hK _ hj) (hKinv _ hj)
      rwa [hj6] at this

end Signs

theorem czHCodes_lt : ∀ r ∈ czHCodes, ∀ c ∈ r, c < 20 := by decide

theorem czJGens_mem {g : ℕ} (hg : g ∈ czJGens) : ∃ i < 6, czJGens.getD i 0 = g := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
  have hi6 := List.mem_range.mp hi
  exact ⟨i, hi6, TabFacts.gens_getD hi6⟩

theorem getD_gens_mem {i : ℕ} (hi : i < 6) : czJGens.getD i 0 ∈ czJGens := by
  rw [TabFacts.gens_getD hi]
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

theorem czSignCentral_of (hb : FJCard) (hc : czRigidCheck = true)
    (hd : czJIdentCheck = true) {K : Type*} [Group K] (x : ℕ → K)
    (hrel : ∀ r ∈ czRelsJ, Sign.evalC x r = 1)
    (hcard : Nat.card (closure (x '' {i | i < 6})) = 2048)
    (hq : ∀ i < 6, (x 6)⁻¹ * x i * x 6 = Sign.evalC x (czWq.getD i []))
    (hv : ∀ i < 6, (x 7)⁻¹ * x i * x 7 = Sign.evalC x (czWv.getD i []))
    (hw : ∀ i < 6, (x 8)⁻¹ * x i * x 8 = Sign.evalC x (czWw.getD i []))
    (hh : ∀ i < 6, (x 9)⁻¹ * x i * x 9 = Sign.evalC x (czHTarget i))
    {r : List ℕ} (hr : r ∈ czHCodes.drop 7)
    (he : Sign.evalC x r ∈ closure (x '' {i | i < 6})) :
    Sign.evalC x r = 1 ∨ Sign.evalC x r = x 0 ^ 2 := by
  have F := tabFacts_of_rigid hc
  set R := realizes_czJ F hb x hrel hcard
  have hI := hd
  simp only [czJIdentCheck, identSearch, Bool.and_eq_true] at hI
  have hKinv := hI.2.1.1.2
  have hT := hI.2.1.2
  have hZ := hI.2.2
  rw [List.all_eq_true] at hKinv hT
  rw [beq_iff_eq] at hZ
  have hW9 : ∀ i < 6, ∀ c ∈ ((List.range 6).map czHTarget).getD i [], c < 12 := by
    intro i hi
    simpa [hi] using czHTarget_lt i hi
  have hh' : ∀ i < 6,
      (x 9)⁻¹ * x i * x 9 = Sign.evalC x (((List.range 6).map czHTarget).getD i []) := by
    intro i hi
    simpa [hi] using hh i hi
  have hA : ((List.range 6).map fun i => evW czJTab czJInv czJGens (czHTarget i)) =
      ((List.range 6).map czHTarget).map (evW czJTab czJInv czJGens) := by
    rw [List.map_map]
    rfl
  set Kt : Array (Array ℕ) := #[homTab czN czJTab czJCert (czWq.map (evW czJTab czJInv czJGens)),
    homTab czN czJTab czJCert (czWv.map (evW czJTab czJInv czJGens)),
    homTab czN czJTab czJCert (czWw.map (evW czJTab czJInv czJGens)),
    homTab czN czJTab czJCert ((List.range 6).map fun i =>
      evW czJTab czJInv czJGens (czHTarget i))] with hKt
  have hK : ∀ j < 4, Represents F hb x hrel hcard (Kt.getD j #[]) (x (j + 6)) := by
    intro j hj
    interval_cases j
    · exact represents_homTab_conjQ F hb x hrel hcard czWq_lt hq
    · exact represents_homTab_conjQ F hb x hrel hcard czWv_lt hv
    · exact represents_homTab_conjQ F hb x hrel hcard czWw_lt hw
    · change Represents F hb x hrel hcard (homTab czN czJTab czJCert
        ((List.range 6).map fun i => evW czJTab czJInv czJGens (czHTarget i))) (x 9)
      rw [hA]
      exact represents_homTab_conjQ F hb x hrel hcard hW9 hh'
  have hKinv' : ∀ j < 4, isInvA czN (Kt.getD j #[]) (invCand czN (Kt.getD j #[])) = true :=
    fun j hj => hKinv j (List.mem_range.mpr hj)
  have hrep := represents_foldl F hb x hrel hcard (letterTab czN czJTab czJInv czJGens Kt) r
    (fun l hl => represents_letterTab F hb x hrel hcard Kt hK hKinv'
      (czHCodes_lt r (List.mem_of_mem_drop hr) l hl)) (idA czN) 1
    (represents_idA F hb x hrel hcard)
  rw [one_mul] at hrep
  set e := Sign.evalC x r with hedef
  have hcomm : ∀ i < 6, e * x i = x i * e := by
    intro i hi
    have hg := hT r hr
    rw [List.all_eq_true] at hg
    have hg' := hg _ (getD_gens_mem hi)
    rw [beq_iff_eq] at hg'
    obtain ⟨-, h2⟩ := hrep _ (F.gens_getD_lt i)
    rw [getElem!_eq_getD, ← ix, hg'] at h2
    have hx : (eltQ F hb x hrel hcard (czJGens.getD i 0) : K) = x i := by
      rw [eltQ_gens F hb x hrel hcard]
      simp only [hi, ↓reduceDIte]
      rfl
    rw [hx] at h2
    calc e * x i = e * (e⁻¹ * x i * e) := by rw [← h2]
      _ = x i * e := by group
  set m := idx R ⟨e, he⟩ with hmdef
  have hm : m ∈ (List.range czN).filter (fun a => czJGens.all fun g =>
      AutETable.mt czJTab a g == AutETable.mt czJTab g a) := by
    rw [List.mem_filter]
    refine ⟨List.mem_range.mpr (idx_lt R _), ?_⟩
    rw [List.all_eq_true]
    intro g hg
    rw [beq_iff_eq]
    obtain ⟨i, hi, rfl⟩ := czJGens_mem hg
    have hgl := F.gens_getD_lt i
    apply R.inj _ _ (R.lt _ _ (idx_lt R _) hgl) (R.lt _ _ hgl (idx_lt R _))
    rw [R.mul _ _ (idx_lt R _) hgl, R.mul _ _ hgl (idx_lt R _), elt_idx R,
      eltQ_gens F hb x hrel hcard]
    simp only [hi, ↓reduceDIte]
    exact Subtype.ext (hcomm i hi)
  rw [hZ, List.mem_cons, List.mem_singleton] at hm
  have hme := elt_idx R ⟨e, he⟩
  rcases hm with h0 | hz
  · left
    rw [← hmdef, h0, R.one] at hme
    exact (congrArg Subtype.val hme).symm
  · right
    rw [← hmdef, hz] at hme
    have h2 : Sign.evalC x [0, 0] = e :=
      (coe_eltQ_evW F hb x hrel hcard (by decide)).symm.trans (congrArg Subtype.val hme)
    rw [← h2, Sign.evalC_cons, Sign.evalC_cons, Sign.evalC_nil, pow_two]
    simp

section Cert

variable {K : Type*} [Group K]

theorem czRigid (k : ℕ → K) (hrel : ∀ r ∈ czRelsJ, Sign.evalC k r = 1)
    (hcard : Nat.card (closure (k '' {i | i < 6})) = 2048) {yq yw h : K}
    (hq : ∀ i < 6, yq⁻¹ * k i * yq = Sign.evalC k (czWq.getD i []))
    (hw : ∀ i < 6, yw⁻¹ * k i * yw = Sign.evalC k (czWw.getD i []))
    (hn : ∀ i < 6, h⁻¹ * k i * h ∈ closure (k '' {i | i < 6}))
    (hhq : h * yq = yq * h) (h3 : (yw * h) ^ 3 ∈ closure (k '' {i | i < 6})) :
    ∃ s < 8, ∀ i < 6, h⁻¹ * k i * h = Sign.evalC k ((czSols.getD s []).getD i []) :=
  czRigid_of cz_jcard cz_rigid_check k hrel hcard hq hw hn hhq h3

theorem czNorm (k : ℕ → K) (hrel : ∀ r ∈ czRelsJ, Sign.evalC k r = 1)
    (hcard : Nat.card (closure (k '' {i | i < 6})) = 2048) {h : K} {s : ℕ} (hs : s < 4)
    (hh : ∀ i < 6, h⁻¹ * k i * h = Sign.evalC k ((czSols.getD s []).getD i [])) :
    ∀ i < 6, (h * Sign.evalC k (czNormX.getD s []))⁻¹ * k i *
      (h * Sign.evalC k (czNormX.getD s [])) = Sign.evalC k (czHTarget i) :=
  czNorm_of cz_jcard cz_rigid_check cz_jident_check k hrel hcard hs hh

theorem czClass2 (k : ℕ → K) (hrel : ∀ r ∈ czRelsJ, Sign.evalC k r = 1)
    (hcard : Nat.card (closure (k '' {i | i < 6})) = 2048) {h : K} {s : ℕ} (hs4 : 4 ≤ s)
    (hs8 : s < 8) (hh : ∀ i < 6, h⁻¹ * k i * h = Sign.evalC k ((czSols.getD s []).getD i [])) :
    czClass2To1.getD (s - 4) 0 < 4 ∧ ∀ i < 6, h⁻¹ * Sign.evalC k (c2JCodes.getD i []) * h =
      Sign.evalC (fun j => Sign.evalC k (c2JCodes.getD j []))
        ((czSols.getD (czClass2To1.getD (s - 4) 0) []).getD i []) :=
  czClass2_of cz_jcard cz_rigid_check cz_jident_check k hrel hcard hs4 hs8 hh

theorem czSignCentral (x : ℕ → K) (hrel : ∀ r ∈ czRelsJ, Sign.evalC x r = 1)
    (hcard : Nat.card (closure (x '' {i | i < 6})) = 2048)
    (hq : ∀ i < 6, (x 6)⁻¹ * x i * x 6 = Sign.evalC x (czWq.getD i []))
    (hv : ∀ i < 6, (x 7)⁻¹ * x i * x 7 = Sign.evalC x (czWv.getD i []))
    (hw : ∀ i < 6, (x 8)⁻¹ * x i * x 8 = Sign.evalC x (czWw.getD i []))
    (hh : ∀ i < 6, (x 9)⁻¹ * x i * x 9 = Sign.evalC x (czHTarget i))
    {r : List ℕ} (hr : r ∈ czHCodes.drop 7)
    (he : Sign.evalC x r ∈ closure (x '' {i | i < 6})) :
    Sign.evalC x r = 1 ∨ Sign.evalC x r = x 0 ^ 2 :=
  czSignCentral_of cz_jcard cz_rigid_check cz_jident_check x hrel hcard hq hv hw hh hr he

end Cert

end CFSG.ComponentClassification.GMS78.RuCz
