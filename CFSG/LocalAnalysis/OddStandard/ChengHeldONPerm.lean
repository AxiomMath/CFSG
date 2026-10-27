module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldONPres
public import Certificates.Data.ChengHeldONImages
public import CFSG.Sporadic.Schreier.ONSylowCenter

public section

namespace CFSG.OddStandard.ChengHeld.ONSylow

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.Recognition.PresentedWords
open CFSG.CosetTable

theorem getD_toList (a : Array ℕ) (i : ℕ) : a.toList.getD i 0 = a[i]! := by
  by_cases h : i < a.size
  · rw [getElem!_pos a i h]; simp [List.getD_eq_getElem?_getD, h]
  · rw [getElem!_neg a i h]; simp [List.getD_eq_getElem?_getD, h]

def LRep (n : ℕ) (l : List ℕ) (g : Equiv.Perm (Fin n)) : Prop :=
  l.length = n ∧ ∀ x : Fin n, l.getD x 0 = g x

theorem LRep.unique {n : ℕ} {l : List ℕ} {g h : Equiv.Perm (Fin n)} (hg : LRep n l g)
    (hh : LRep n l h) : g = h :=
  Equiv.ext fun x => Fin.ext ((hg.2 x).symm.trans (hh.2 x))

theorem lrep_one (n : ℕ) : LRep n (List.range n) 1 :=
  ⟨List.length_range, fun x => by simp [List.getD_eq_getElem?_getD]⟩

theorem LRep.comp {n : ℕ} {t u : List ℕ} {g h : Equiv.Perm (Fin n)} (ht : LRep n t g)
    (hu : LRep n u h) : LRep n (compL t u) (g * h) := by
  refine ⟨by simp [compL, hu.1], fun x => ?_⟩
  have hx : (x : ℕ) < u.length := by rw [hu.1]; exact x.2
  have h1 : u[(x : ℕ)] = (h x : ℕ) := by
    have := hu.2 x
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx, Option.getD_some] at this
  have h2 := ht.2 (h x)
  simp only [compL, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hx,
    Option.map_some, Option.getD_some, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  rw [h2]
  rfl

theorem lrep_of_prep {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (hp : PRep n t g)
    (hl : t.toList.length = n) : LRep n t.toList g :=
  ⟨hl, fun x => by rw [getD_toList]; exact hp x⟩

theorem prep_of_lrep {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (hl : LRep n t.toList g) :
    PRep n t g := fun x => by rw [← getD_toList]; exact hl.2 x

theorem permOfArr_eq_of_prep {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (h : PRep n t g) :
    permOfArr n t = g := by
  have hc : (∀ i < n, t[i]! < n) ∧ ∀ i < n, ∀ j < n, t[i]! = t[j]! → i = j := by
    refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_⟩
    · rw [h.apply hi]; exact (g _).2
    · rw [h.apply hi, h.apply hj] at hij
      exact congrArg Fin.val (g.injective (Fin.ext hij))
  have ht : PRep n t (permOfArr n t) := fun x => by
    rw [permOfArr, dite_eq_left hc]
    rfl
  exact ht.unique h

theorem wprod_mem {G : Type*} [Group G] {K : Subgroup G} {x : Fin 8 → G} (hx : ∀ i, x i ∈ K)
    (w : List (Fin 8 × Bool)) : wprod x w ∈ K := by
  induction w with
  | nil => exact K.one_mem
  | cons l w ih =>
    rw [wprod_cons]
    refine K.mul_mem ?_ ih
    split
    · exact hx _
    · exact K.inv_mem (hx _)

theorem pisInv_of_isInvL {t r : Array ℕ} (h : isInvL t.toList r.toList = true) :
    pisInv 32 t r = true := by
  simp only [isInvL, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨-, -⟩, h⟩ := h
  rw [pisInv, allBelowN_iff]
  intro i hi
  have := h i hi
  rw [getD_toList, getD_toList] at this
  simpa [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using this

theorem onImgOK_eq_true : onImgOK = true := by decide +kernel

noncomputable def onPerm (i : Fin 8) : Equiv.Perm (Fin 32) := permOfArr 32 onImgs[i.val]!

structure ImgParts : Prop where
  inv : ∀ i < 8, isInvL onImgs[i]!.toList onInvs[i]!.toList = true
  rels : ∀ w ∈ onRels, wordL w = List.range 32
  gens : ∀ j < 6, wordL onGenWords[j]! = CFSG.ONSchreier.Data.T32Chain.generators[j]!.toList

theorem imgParts (h : onImgOK = true) : ImgParts := by
  simp only [onImgOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, fun w hw => by simpa using h2 w hw, h3⟩

theorem lrep_onPerm (hp : ImgParts) (i : Fin 8) :
    LRep 32 onImgs[i.val]!.toList (onPerm i) ∧ LRep 32 onInvs[i.val]!.toList (onPerm i)⁻¹ := by
  have h := hp.inv i.val i.2
  have hl := h
  simp only [isInvL, Bool.and_eq_true, beq_iff_eq] at hl
  obtain ⟨⟨hl1, hl2⟩, -⟩ := hl
  obtain ⟨p1, p2⟩ := prep_permOfArr (pisInv_of_isInvL h)
  exact ⟨lrep_of_prep p1 hl1, lrep_of_prep p2 hl2⟩

theorem lrep_letL (hp : ImgParts) (l : Fin 8 × Bool) :
    LRep 32 (letL l) (if l.2 then onPerm l.1 else (onPerm l.1)⁻¹) := by
  obtain ⟨h1, h2⟩ := lrep_onPerm hp l.1
  by_cases hb : l.2
  · simpa [letL, hb] using h1
  · simpa [letL, hb] using h2

theorem lrep_foldl (hp : ImgParts) (w : List (Fin 8 × Bool)) :
    ∀ (acc : List ℕ) (g : Equiv.Perm (Fin 32)), LRep 32 acc g →
      LRep 32 (w.foldl (fun acc l => compL acc (letL l)) acc) (g * wprod onPerm w) := by
  induction w with
  | nil => intro acc g hg; simpa using hg
  | cons l w ih =>
    intro acc g hg
    rw [List.foldl_cons, wprod_cons, ← mul_assoc]
    exact ih _ _ (hg.comp (lrep_letL hp l))

theorem lrep_wordL (hp : ImgParts) (w : List (Fin 8 × Bool)) :
    LRep 32 (wordL w) (wprod onPerm w) := by
  have h := lrep_foldl hp w (List.range 32) 1 (lrep_one 32)
  rw [one_mul] at h
  exact h

theorem exists_images :
    ∃ x : Fin 8 → Equiv.Perm (Fin 32), (∀ w ∈ onRels, wprod x w = 1) ∧
      onT32Chain.originalSubgroup ≤ Subgroup.closure (Set.range x) := by
  have hp := imgParts onImgOK_eq_true
  refine ⟨onPerm, fun w hw => ?_, ?_⟩
  · have h1 := lrep_wordL hp w
    rw [hp.rels w hw] at h1
    exact h1.unique (lrep_one 32)
  · rw [onT32_sub, Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    dsimp only
    have h1 := lrep_wordL hp onGenWords[j]!
    rw [hp.gens j hj] at h1
    rw [permOfArr_eq_of_prep (prep_of_lrep h1)]
    exact wprod_mem (K := Subgroup.closure (Set.range onPerm))
      (fun i => Subgroup.subset_closure ⟨i, rfl⟩) _

theorem exists_mulEquiv_t32
    (hpres : Finite ONPres ∧ Nat.card ONPres ≤ 512) :
    Nonempty (ONPres ≃* ↥onT32Chain.originalSubgroup) := by
  obtain ⟨hfin, hP⟩ := hpres
  obtain ⟨x, hx, hle⟩ := exists_images
  have hc : 512 ≤ Nat.card (Subgroup.closure (Set.range x)) := by
    rw [← card_onT32]
    exact Subgroup.card_le_of_le hle
  obtain ⟨e⟩ := exists_mulEquiv_closure hP x hx hc
  have hge : Nat.card (Subgroup.closure (Set.range x)) ≤
      Nat.card onT32Chain.originalSubgroup := by
    rw [card_onT32, Nat.card_congr e.symm.toEquiv]
    exact hP
  exact ⟨e.trans (MulEquiv.subgroupCongr (Subgroup.eq_of_le_of_card_ge hle hge).symm)⟩

end CFSG.OddStandard.ChengHeld.ONSylow
