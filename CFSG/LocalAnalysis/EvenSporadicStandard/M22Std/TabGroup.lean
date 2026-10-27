module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.TabCheck

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Equiv CFSG.Blueprint CFSG.EvenSporadicStandard.M22Std.TabCheck
open CFSG.Blueprint.NativeSporadic (Carrier)

instance : Finite (Carrier .M22) := inferInstanceAs (Finite NativeSporadic.M22)

@[expose] def tabP (σ : Perm (Fin 22)) : Tab := List.ofFn fun i => (σ i).val

theorem length_tabP (σ : Perm (Fin 22)) : (tabP σ).length = 22 := by
  simp only [tabP, List.length_ofFn]

theorem getD_tabP (σ : Perm (Fin 22)) (j : Fin 22) : (tabP σ).getD j.val 0 = (σ j).val := by
  rw [List.getD_eq_getElem _ _ (by rw [length_tabP]; exact j.2)]
  simp only [tabP, List.getElem_ofFn]

theorem tabP_one : tabP 1 = idTab := by
  decide

theorem tabP_mul (σ τ : Perm (Fin 22)) : tabP (σ * τ) = tmul (tabP σ) (tabP τ) := by
  simp only [tmul, tabP, List.map_ofFn]
  congr 1
  funext i
  have := getD_tabP σ (τ i)
  simp only [tabP] at this
  simp only [Function.comp_apply, this, Perm.mul_apply]

theorem tabP_injective : Function.Injective tabP := by
  intro σ τ h
  have := List.ofFn_injective h
  ext i
  exact congrFun this i

@[expose] def toPerm : Carrier .M22 →* Perm (Fin 22) := NativeSporadic.M22.subtype

@[expose] def tab (g : Carrier .M22) : Tab := tabP (toPerm g)

theorem tab_one : tab 1 = idTab := by
  simp only [tab, map_one, tabP_one]

theorem tab_mul (g h : Carrier .M22) : tab (g * h) = tmul (tab g) (tab h) := by
  simp only [tab, map_mul, tabP_mul]

theorem tab_injective : Function.Injective tab := fun _ _ hgh =>
  Subtype.val_injective (tabP_injective hgh)

@[expose] def pinA : Perm (Fin 22) :=
  List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] *
    List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13]

@[expose] def pinB : Perm (Fin 22) :=
  List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] *
    List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18]

theorem pinA_mem : pinA ∈ NativeSporadic.M22 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem pinB_mem : pinB ∈ NativeSporadic.M22 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] def genA : Carrier .M22 := ⟨pinA, pinA_mem⟩

@[expose] def genB : Carrier .M22 := ⟨pinB, pinB_mem⟩

@[expose] def genBi : Carrier .M22 := genB * (genB * genB)

theorem tab_genA : tab genA = tabA := by
  show tabP pinA = tabA
  decide

theorem tab_genB : tab genB = tabB := by
  show tabP pinB = tabB
  decide

theorem tab_genBi : tab genBi = tabBi := by
  simp only [genBi, tab_mul, tab_genB, tabBi]

@[expose] def wordElt {G : Type*} [Monoid G] (ls : List G) : List Nat → G
  | [] => 1
  | i :: w => ls.getD i 1 * wordElt ls w

theorem tab_wordElt (ls : List (Carrier .M22)) (w : List Nat) :
    tab (wordElt ls w) = wordTab (ls.map tab) w := by
  induction w with
  | nil => simp only [wordElt, wordTab, tab_one]
  | cons i w ih =>
    have h : (ls.map tab).getD i idTab = tab (ls.getD i 1) := by
      rw [← tab_one, List.getD_map]
    simp only [wordElt, wordTab, tab_mul, ih, h]

@[expose] def spanE {G : Type*} [Monoid G] : List G → List G
  | [] => [1]
  | g :: gs => spanE gs ++ (spanE gs).map (g * ·)

theorem tab_spanE (gs : List (Carrier .M22)) : (spanE gs).map tab = span (gs.map tab) := by
  induction gs with
  | nil => simp only [spanE, span, List.map_cons, tab_one, List.map]
  | cons g gs ih =>
    simp only [spanE, List.map_cons, span, TabCheck.ext, List.map_append, ← ih]
    congr 1
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun x _ => tab_mul g x

theorem mem_spanE_iff (gs : List (Carrier .M22)) (x : Carrier .M22) :
    tab x ∈ span (gs.map tab) ↔ x ∈ spanE gs := by
  rw [← tab_spanE, List.mem_map]
  exact ⟨fun ⟨y, hy, hyx⟩ => tab_injective hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

theorem one_mem_spanE {G : Type*} [Monoid G] (gs : List G) : (1 : G) ∈ spanE gs := by
  induction gs with
  | nil => simp only [spanE, List.mem_singleton]
  | cons g gs ih => exact List.mem_append_left _ ih

theorem length_spanE {G : Type*} [Monoid G] (gs : List G) :
    (spanE gs).length = 2 ^ gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [spanE, List.length_append, List.length_map, ih, List.length_cons, pow_succ]
    omega

theorem mem_of_mem_spanE {G : Type*} [Group G] (H : Subgroup G) {gs : List G}
    (hgs : ∀ g ∈ gs, g ∈ H) : ∀ y ∈ spanE gs, y ∈ H := by
  induction gs with
  | nil => intro y hy; simp only [spanE, List.mem_singleton] at hy; rw [hy]; exact H.one_mem
  | cons g gs ih =>
    intro y hy
    simp only [spanE, List.mem_append, List.mem_map] at hy
    rcases hy with hy | ⟨z, hz, rfl⟩
    · exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) y hy
    · exact H.mul_mem (hgs g List.mem_cons_self)
        (ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) z hz)

@[expose] def sylowGens : List (Carrier .M22) := sylowWords.map (wordElt [genA, genB, genBi])

theorem tab_sylowGens : sylowGens.map tab = gensTab := by
  have h : [genA, genB, genBi].map tab = letterTabs := by
    simp only [List.map_cons, List.map_nil, tab_genA, tab_genB, tab_genBi, letterTabs]
  simp only [sylowGens, gensTab, List.map_map]
  refine List.map_congr_left fun w _ => ?_
  rw [Function.comp_apply, tab_wordElt, h]

@[expose] def sylowS : Subgroup (Carrier .M22) := Subgroup.closure {g | g ∈ sylowGens}

theorem sylowGens_mem {g : Carrier .M22} (hg : g ∈ sylowGens) : g ∈ sylowS :=
  Subgroup.subset_closure hg

theorem tab_mem_span_of_mem_sylowS (hS : sylowOK gensTab = true) {x : Carrier .M22}
    (hx : x ∈ sylowS) : tab x ∈ span gensTab := by
  obtain ⟨-, -, hcl⟩ := of_decide_eq_true hS
  have hx' : x ∈ Submonoid.closure {g | g ∈ sylowGens} := by
    rw [← Subgroup.closure_toSubmonoid_of_isOfFinOrder (fun x _ => isOfFinOrder_of_finite x)]
    exact hx
  have key : ∀ y ∈ Submonoid.closure {g | g ∈ sylowGens},
      ∀ l : Carrier .M22, tab l ∈ span gensTab → tab (l * y) ∈ span gensTab := by
    intro y hy
    induction hy using Submonoid.closure_induction with
    | mem y hy =>
      intro l hl
      rw [tab_mul]
      refine hcl _ hl _ ?_
      rw [← tab_sylowGens]
      exact List.mem_map_of_mem hy
    | one => intro l hl; rwa [mul_one]
    | mul y z _ _ hy hz => intro l hl; rw [← mul_assoc]; exact hz _ (hy l hl)
  have h1 : tab (1 * x) ∈ span gensTab := key x hx' 1 (by
    rw [tab_one]
    induction gensTab with
    | nil => simp only [span, List.mem_singleton]
    | cons g gs ih => exact List.mem_append_left _ ih)
  rwa [one_mul] at h1

theorem mem_sylowS_iff (hS : sylowOK gensTab = true) (x : Carrier .M22) :
    x ∈ sylowS ↔ x ∈ spanE sylowGens := by
  constructor
  · intro hx
    have := tab_mem_span_of_mem_sylowS hS hx
    rwa [← tab_sylowGens, mem_spanE_iff] at this
  · exact fun hx => mem_of_mem_spanE sylowS (fun g hg => sylowGens_mem hg) x hx

theorem natCard_subtype_mem {α : Type*} (l : List α) (h : l.Nodup) :
    Nat.card {x // x ∈ l} = l.length := by
  classical
  have e : {x // x ∈ l} ≃ {x // x ∈ l.toFinset} := Equiv.subtypeEquivRight (by simp)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup h]

theorem card_sylowS (hS : sylowOK gensTab = true) : Nat.card sylowS = 2 ^ 7 := by
  obtain ⟨hlen, hnd, -⟩ := of_decide_eq_true hS
  have hspan : (spanE sylowGens).map tab = span gensTab := by
    rw [tab_spanE, tab_sylowGens]
  have hnd' : (spanE sylowGens).Nodup := List.Nodup.of_map _ (hspan ▸ hnd)
  have hlen' : (spanE sylowGens).length = 128 := by
    rw [← List.length_map (f := tab), hspan, hlen]
  rw [show Nat.card sylowS = Nat.card {x // x ∈ spanE sylowGens} from
    Nat.card_congr (Equiv.subtypeEquivRight (mem_sylowS_iff hS)), natCard_subtype_mem _ hnd',
    hlen']
  norm_num

end CFSG.EvenSporadicStandard.M22Std
