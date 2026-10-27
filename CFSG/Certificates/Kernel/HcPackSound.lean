module

public import Certificates.Data.Kernel.HcPack
public import Certificates.Data.G23RecogHFactsInputs
import all Certificates.Data.Kernel.HcPack
import all Certificates.Data.G23RecogGlueInputs
import all Certificates.Data.G23RecogHFactsInputs

public section

namespace CFSG.KC.HcPack

open CFSG.GH74.QTGen4.Recog.G23 CFSG.GH74.QTGen4.Recog.G23.HFactsData

theorem pk_cons (a : ℕ) (l : List ℕ) : pk (a :: l) = a + 32 * pk l := rfl

theorem pk_cons_mod {a : ℕ} (ha : a < 32) (l : List ℕ) : pk (a :: l) % 32 = a := by
  rw [pk_cons, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

theorem pk_cons_div {a : ℕ} (ha : a < 32) (l : List ℕ) : pk (a :: l) / 32 = pk l := by
  rw [pk_cons, Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt ha, Nat.zero_add]

theorem lane_pk : ∀ (l : List ℕ), (∀ a ∈ l, a < 32) → ∀ j : ℕ, lane (pk l) j = l.getD j 0
  | [], _, j => by simp [lane, pk]
  | a :: l, h, 0 => by
    simp only [lane, pow_zero, Nat.div_one, List.getD_cons_zero]
    exact pk_cons_mod (h a List.mem_cons_self) l
  | a :: l, h, j + 1 => by
    have ha := h a List.mem_cons_self
    have ih := lane_pk l (fun b hb => h b (List.mem_cons_of_mem _ hb)) j
    simp only [lane, List.getD_cons_succ] at ih ⊢
    rw [pow_succ', ← Nat.div_div_eq_div_mul, pk_cons_div ha]
    exact ih

theorem mulGo_succ (x n g : ℕ) : mulGo x (n + 1) g = lane x (g % 32) + 32 * mulGo x n (g / 32) :=
  rfl

theorem mulGo_pk (x : List ℕ) (hx : ∀ a ∈ x, a < 32) :
    ∀ g : List ℕ, (∀ a ∈ g, a < 32) →
      mulGo (pk x) g.length (pk g) = pk (g.map fun j => x.getD j 0)
  | [], _ => rfl
  | a :: g, h => by
    have ha := h a List.mem_cons_self
    rw [List.length_cons, mulGo_succ, pk_cons_mod ha, pk_cons_div ha, List.map_cons, pk_cons,
      lane_pk x hx, mulGo_pk x hx g (fun b hb => h b (List.mem_cons_of_mem _ hb))]

def VL (l : List ℕ) : Prop := l.length = 32 ∧ ∀ a ∈ l, a < 32

theorem pk_mulL {x g : List ℕ} (hx : VL x) (hg : VL g) : pk (mulL x g) = mulP (pk x) (pk g) := by
  rw [mulP, ← hg.1, mulGo_pk x hx.2 g hg.2]
  rfl

theorem getD_lt : ∀ (x : List ℕ), (∀ a ∈ x, a < 32) → ∀ j, x.getD j 0 < 32
  | [], _, _ => by simp
  | a :: _, h, 0 => by simpa using h a List.mem_cons_self
  | _ :: x, h, j + 1 => by
    rw [List.getD_cons_succ]
    exact getD_lt x (fun b hb => h b (List.mem_cons_of_mem _ hb)) j

theorem VL_mulL {x g : List ℕ} (hx : VL x) (hg : VL g) : VL (mulL x g) := by
  refine ⟨by rw [mulL, List.length_map, hg.1], fun a ha => ?_⟩
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp ha
  exact getD_lt x hx.2 j

theorem pk_inj : ∀ (x y : List ℕ), x.length = y.length → (∀ a ∈ x, a < 32) → (∀ a ∈ y, a < 32) →
    pk x = pk y → x = y
  | [], [], _, _, _, _ => rfl
  | a :: x, b :: y, hl, hx, hy, h => by
    have ha := hx a List.mem_cons_self
    have hb := hy b List.mem_cons_self
    have e1 : a = b := by rw [← pk_cons_mod ha x, ← pk_cons_mod hb y, h]
    have e2 : pk x = pk y := by rw [← pk_cons_div ha x, ← pk_cons_div hb y, h]
    rw [e1, pk_inj x y (by simpa using hl) (fun c hc => hx c (List.mem_cons_of_mem _ hc))
      (fun c hc => hy c (List.mem_cons_of_mem _ hc)) e2]

theorem VL_inj {x y : List ℕ} (hx : VL x) (hy : VL y) (h : pk x = pk y) : x = y :=
  pk_inj x y (by rw [hx.1, hy.1]) hx.2 hy.2 h

theorem VL_Lst (σ : Equiv.Perm (Fin 32)) : VL (Lst σ) := by
  refine ⟨by simp [Lst], fun a ha => ?_⟩
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  exact (σ i).isLt

section Map

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β) (S : α → Prop)
  (mul : α → α → α) (mul' : β → β → β) (cap : ℕ)
  (hS : ∀ x g, S x → S g → S (mul x g))
  (hf : ∀ x g, S x → S g → f (mul x g) = mul' (f x) (f g))
  (hi : ∀ x y, S x → S y → f x = f y → x = y)

def mapSt (p : List α × List α) : List β × List β := (p.1.map f, p.2.map f)

include hi in
theorem contains_map (L : List α) (hL : ∀ y ∈ L, S y) (x : α) (hx : S x) :
    (L.map f).contains (f x) = L.contains x := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨y, hy, hfy⟩
    rwa [← hi y x (hL y hy) hx hfy]
  · exact fun h => ⟨x, h, rfl⟩

include hS hf hi in
theorem addOne_map (x g : α) (hx : S x) (hg : S g) (acc : List α × List α)
    (h1 : ∀ y ∈ acc.1, S y) :
    mapSt f (addOne cap mul x acc g) = addOne cap mul' (f x) (mapSt f acc) (f g) := by
  have hc := contains_map f S hi acc.1 h1 (mul x g) (hS x g hx hg)
  unfold addOne mapSt
  rw [← hf x g hx hg, List.length_map, hc]
  by_cases h : acc.1.length < cap ∧ ¬ acc.1.contains (mul x g) = true
  · rw [if_pos h, if_pos h]
    simp
  · rw [if_neg h, if_neg h]

include hS hf hi in
theorem gensFold_map (x : α) (hx : S x) :
    ∀ gs : List α, (∀ g ∈ gs, S g) → ∀ acc : List α × List α, (∀ y ∈ acc.1, S y) →
      (∀ y ∈ acc.2, S y) →
      mapSt f (gs.foldl (addOne cap mul x) acc) =
        (gs.map f).foldl (addOne cap mul' (f x)) (mapSt f acc)
  | [], _, _, _, _ => rfl
  | g :: gs, hgs, acc, h1, h2 => by
    have hg := hgs g List.mem_cons_self
    obtain ⟨h1', h2'⟩ := addOne_sub S cap mul hS x g acc hx hg h1 h2
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, ← addOne_map f S mul mul' cap hS hf hi x g hx hg acc h1]
    exact gensFold_map x hx gs (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ h1' h2'

include hS hf hi in
theorem frFold_map (gens : List α) (hgs : ∀ g ∈ gens, S g) :
    ∀ fr : List α, (∀ x ∈ fr, S x) → ∀ acc : List α × List α, (∀ y ∈ acc.1, S y) →
      (∀ y ∈ acc.2, S y) →
      mapSt f (fr.foldl (fun acc x => gens.foldl (addOne cap mul x) acc) acc) =
        (fr.map f).foldl (fun acc x => (gens.map f).foldl (addOne cap mul' x) acc) (mapSt f acc)
  | [], _, _, _, _ => rfl
  | x :: fr, hfr, acc, h1, h2 => by
    have hx := hfr x List.mem_cons_self
    obtain ⟨h1', h2'⟩ := gens_fold_sub S cap mul hS x hx gens hgs acc h1 h2
    rw [List.foldl_cons, List.map_cons, List.foldl_cons,
      ← gensFold_map f S mul mul' cap hS hf hi x hx gens hgs acc h1 h2]
    exact frFold_map gens hgs fr (fun y hy => hfr y (List.mem_cons_of_mem _ hy)) _ h1' h2'

include hS hf hi in
theorem bfsStep_map (gens : List α) (hgs : ∀ g ∈ gens, S g) (seen fr : List α)
    (hs : ∀ y ∈ seen, S y) (hfr : ∀ y ∈ fr, S y) :
    mapSt f (bfsStep cap mul gens seen fr) = bfsStep cap mul' (gens.map f) (seen.map f) (fr.map f) := by
  unfold bfsStep
  exact frFold_map f S mul mul' cap hS hf hi gens hgs fr hfr (seen, []) hs (by simp)

include hS hf hi in
theorem bfsAux_map (gens : List α) (hgs : ∀ g ∈ gens, S g) :
    ∀ (n : ℕ) (seen fr : List α), (∀ y ∈ seen, S y) → (∀ y ∈ fr, S y) →
      (bfsAux cap mul gens n seen fr).map f = bfsAux cap mul' (gens.map f) n (seen.map f) (fr.map f)
  | 0, _, _, _, _ => by simp only [bfsAux]
  | n + 1, seen, fr, hs, hfr => by
    have hst := bfsStep_map f S mul mul' cap hS hf hi gens hgs seen fr hs hfr
    obtain ⟨h1, h2⟩ := bfsStep_sub S cap mul hS gens hgs seen fr hs hfr
    simp only [bfsAux, List.isEmpty_map]
    split
    · rfl
    · have e1 : (bfsStep cap mul' (gens.map f) (seen.map f) (fr.map f)).1 =
          (bfsStep cap mul gens seen fr).1.map f := by rw [← hst]; rfl
      have e2 : (bfsStep cap mul' (gens.map f) (seen.map f) (fr.map f)).2 =
          (bfsStep cap mul gens seen fr).2.map f := by rw [← hst]; rfl
      rw [e1, e2]
      exact bfsAux_map gens hgs n _ _ h1 h2

end Map

section Nodup

variable {α : Type*} [DecidableEq α] (mul : α → α → α) (cap : ℕ)

theorem addOne_nodup (x g : α) (acc : List α × List α) (h : acc.1.Nodup) :
    (addOne cap mul x acc g).1.Nodup := by
  unfold addOne
  split_ifs with hc
  · rw [List.nodup_append_comm, List.singleton_append, List.nodup_cons]
    exact ⟨fun hm => hc.2 (List.contains_iff_mem.mpr hm), h⟩
  · exact h

theorem gensFold_nodup (x : α) :
    ∀ (gs : List α) (acc : List α × List α), acc.1.Nodup → (gs.foldl (addOne cap mul x) acc).1.Nodup
  | [], _, h => h
  | g :: gs, acc, h => gensFold_nodup x gs _ (addOne_nodup mul cap x g acc h)

theorem frFold_nodup (gens : List α) :
    ∀ (fr : List α) (acc : List α × List α), acc.1.Nodup →
      (fr.foldl (fun acc x => gens.foldl (addOne cap mul x) acc) acc).1.Nodup
  | [], _, h => h
  | x :: fr, acc, h => frFold_nodup gens fr _ (gensFold_nodup mul cap x gens acc h)

theorem bfsAux_nodup (gens : List α) :
    ∀ (n : ℕ) (seen fr : List α), seen.Nodup → (bfsAux cap mul gens n seen fr).Nodup
  | 0, _, _, h => by simpa only [bfsAux] using h
  | n + 1, seen, fr, h => by
    simp only [bfsAux]
    split
    · exact h
    · exact bfsAux_nodup gens n _ _ (frFold_nodup mul cap gens fr (seen, []) h)

end Nodup

theorem VL_idL : VL idL := VL_Lst 1

theorem pk_idL : pk idL = idP := by decide +kernel

theorem VL_gensOf (ss : List ↥Hc) : ∀ g ∈ gensOf ss, VL g := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨s, -, rfl⟩ := List.mem_map.mp hg
    exact VL_Lst _
  · obtain ⟨s, -, rfl⟩ := List.mem_map.mp hg
    exact VL_Lst _

theorem VL_gensL : ∀ g ∈ gensL, VL g := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    exact VL_Lst _
  · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    exact VL_Lst _

theorem bfs_map_pk (gens : List (List ℕ)) (hg : ∀ g ∈ gens, VL g) :
    (bfsAux 576 mulL gens 600 [idL] [idL]).map pk = bfsP (gens.map pk) := by
  have h := bfsAux_map pk VL mulL mulP 576 (fun _ _ => VL_mulL) (fun _ _ => pk_mulL)
    (fun _ _ => VL_inj) gens hg 600 [idL] [idL] (by simpa using VL_idL) (by simpa using VL_idL)
  rw [h, bfsP]
  simp [pk_idL]

theorem cl_map_pk (ss : List ↥Hc) : (cl ss).map pk = bfsP ((gensOf ss).map pk) :=
  bfs_map_pk _ (VL_gensOf ss)

theorem elts_map_pk : elts.map pk = bfsP (gensL.map pk) := bfs_map_pk _ VL_gensL

theorem VL_bfs (gens : List (List ℕ)) (hg : ∀ g ∈ gens, VL g) :
    ∀ l ∈ bfsAux 576 mulL gens 600 [idL] [idL], VL l :=
  bfsAux_sub VL 576 mulL (fun _ _ => VL_mulL) gens hg 600 [idL] [idL] (by simpa using VL_idL)
    (by simpa using VL_idL)

theorem VL_cl (ss : List ↥Hc) : ∀ l ∈ cl ss, VL l := VL_bfs _ (VL_gensOf ss)

theorem VL_elts : ∀ l ∈ elts, VL l := VL_bfs _ VL_gensL

theorem mem_iff_pk {L : List (List ℕ)} (hL : ∀ y ∈ L, VL y) {l : List ℕ} (hl : VL l) :
    l ∈ L ↔ pk l ∈ L.map pk := by
  refine ⟨fun h => List.mem_map_of_mem h, fun h => ?_⟩
  obtain ⟨y, hy, he⟩ := List.mem_map.mp h
  rwa [← VL_inj (hL y hy) hl he]

end CFSG.KC.HcPack

end
