module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.M23SylowCheck

public section

namespace CFSG.EvenSporadicStandard.Wong77.M23Sylow

open Equiv CFSG.Blueprint
open CFSG.Blueprint.NativeSporadic (Carrier)

@[expose] def tabP (σ : Perm (Fin 23)) : Tab := List.ofFn fun i => (σ i).val

theorem length_tabP (σ : Perm (Fin 23)) : (tabP σ).length = 23 := by
  simp only [tabP, List.length_ofFn]

theorem getD_tabP (σ : Perm (Fin 23)) (j : Fin 23) : (tabP σ).getD j.val 0 = (σ j).val := by
  rw [List.getD_eq_getElem _ _ (by rw [length_tabP]; exact j.2)]
  simp only [tabP, List.getElem_ofFn]

theorem tabP_one : tabP 1 = idTab := by
  decide

theorem tabP_mul (σ τ : Perm (Fin 23)) : tabP (σ * τ) = tmul (tabP σ) (tabP τ) := by
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

@[expose] def toPerm : Carrier .M23 →* Perm (Fin 23) := NativeSporadic.M23.subtype

@[expose] def tab (g : Carrier .M23) : Tab := tabP (toPerm g)

theorem tab_one : tab 1 = idTab := by
  simp only [tab, map_one, tabP_one]

theorem tab_mul (g h : Carrier .M23) : tab (g * h) = tmul (tab g) (tab h) := by
  simp only [tab, map_mul, tabP_mul]

theorem tab_injective : Function.Injective tab := fun _ _ hgh =>
  Subtype.val_injective (tabP_injective hgh)

@[expose] def pinA : Perm (Fin 23) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
    List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
    List.formPerm [20, 21]

@[expose] def pinB : Perm (Fin 23) :=
  List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
    List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]

theorem pinA_mem : pinA ∈ NativeSporadic.M23 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem pinB_mem : pinB ∈ NativeSporadic.M23 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] def genA : Carrier .M23 := ⟨pinA, pinA_mem⟩

@[expose] def genB : Carrier .M23 := ⟨pinB, pinB_mem⟩

@[expose] def genBi : Carrier .M23 := genB * (genB * genB)

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

theorem tab_wordElt (ls : List (Carrier .M23)) (w : List Nat) :
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

theorem tab_spanE (gs : List (Carrier .M23)) : (spanE gs).map tab = span (gs.map tab) := by
  induction gs with
  | nil => simp only [spanE, span, List.map_cons, tab_one, List.map]
  | cons g gs ih =>
    simp only [spanE, List.map_cons, span, ext, List.map_append, ← ih]
    congr 1
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun x _ => tab_mul g x

theorem mem_spanE_iff (gs : List (Carrier .M23)) (x : Carrier .M23) :
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

end CFSG.EvenSporadicStandard.Wong77.M23Sylow
