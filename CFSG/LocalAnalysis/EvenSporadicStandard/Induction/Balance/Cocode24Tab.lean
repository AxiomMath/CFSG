module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.List.GetD

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance.Cocode24

open Equiv

abbrev Tab : Type := List ℕ

@[expose] def idTab : Tab := List.range 24

@[expose] def tmul (s t : Tab) : Tab := t.map fun j => s.getD j 0

@[expose] def tabP (σ : Perm (Fin 24)) : Tab := List.ofFn fun i => (σ i).val

theorem length_tabP (σ : Perm (Fin 24)) : (tabP σ).length = 24 := by
  simp only [tabP, List.length_ofFn]

theorem getD_tabP (σ : Perm (Fin 24)) (j : Fin 24) : (tabP σ).getD j.val 0 = (σ j).val := by
  rw [List.getD_eq_getElem _ _ (by rw [length_tabP]; exact j.2)]
  simp only [tabP, List.getElem_ofFn]

theorem tabP_one : tabP 1 = idTab := by
  decide

theorem tabP_mul (σ τ : Perm (Fin 24)) : tabP (σ * τ) = tmul (tabP σ) (tabP τ) := by
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

@[expose] def extend (sp : List Tab) (g : Tab) : List Tab := sp ++ sp.map (tmul g)

@[expose] def span : List Tab → List Tab
  | [] => [idTab]
  | g :: gs => extend (span gs) g

@[expose] def spanE {G : Type*} [Monoid G] : List G → List G
  | [] => [1]
  | g :: gs => spanE gs ++ (spanE gs).map (g * ·)

theorem tabP_spanE (gs : List (Perm (Fin 24))) : (spanE gs).map tabP = span (gs.map tabP) := by
  induction gs with
  | nil => simp only [spanE, span, List.map_cons, tabP_one, List.map]
  | cons g gs ih =>
    simp only [spanE, List.map_cons, span, extend, List.map_append, ← ih]
    congr 1
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun x _ => tabP_mul g x

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

theorem head_spanE {G : Type*} [Monoid G] (gs : List G) : (spanE gs).head? = some 1 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [spanE]
    rw [List.head?_append, ih]
    rfl

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

@[expose] def spanOK (n : ℕ) (gs : List Tab) : Bool :=
  decide ((span gs).length = n ∧ (span gs).Nodup ∧ ∀ l ∈ span gs, ∀ g ∈ gs, tmul l g ∈ span gs)

theorem tab_mem_span_of_mem_closure {gs : List (Perm (Fin 24))} {n : ℕ}
    (hS : spanOK n (gs.map tabP) = true) {x : Perm (Fin 24)}
    (hx : x ∈ Subgroup.closure {g | g ∈ gs}) : tabP x ∈ span (gs.map tabP) := by
  obtain ⟨-, -, hcl⟩ := of_decide_eq_true hS
  have hx' : x ∈ Submonoid.closure {g | g ∈ gs} := by
    rw [← Subgroup.closure_toSubmonoid_of_isOfFinOrder (fun x _ => isOfFinOrder_of_finite x)]
    exact hx
  have key : ∀ y ∈ Submonoid.closure {g | g ∈ gs},
      ∀ l : Perm (Fin 24), tabP l ∈ span (gs.map tabP) → tabP (l * y) ∈ span (gs.map tabP) := by
    intro y hy
    induction hy using Submonoid.closure_induction with
    | mem y hy =>
      intro l hl
      rw [tabP_mul]
      exact hcl _ hl _ (List.mem_map_of_mem hy)
    | one => intro l hl; rwa [mul_one]
    | mul y z _ _ hy hz => intro l hl; rw [← mul_assoc]; exact hz _ (hy l hl)
  have h1 : tabP (1 * x) ∈ span (gs.map tabP) := key x hx' 1 (by
    rw [tabP_one]
    induction gs.map tabP with
    | nil => simp only [span, List.mem_singleton]
    | cons g gs ih => exact List.mem_append_left _ ih)
  rwa [one_mul] at h1

theorem mem_closure_iff_of_spanOK {gs : List (Perm (Fin 24))} {n : ℕ}
    (hS : spanOK n (gs.map tabP) = true) (x : Perm (Fin 24)) :
    x ∈ Subgroup.closure {g | g ∈ gs} ↔ x ∈ spanE gs := by
  constructor
  · intro hx
    have := tab_mem_span_of_mem_closure hS hx
    rw [← tabP_spanE, List.mem_map] at this
    obtain ⟨y, hy, hyx⟩ := this
    exact tabP_injective hyx ▸ hy
  · exact fun hx => mem_of_mem_spanE _ (fun g hg => Subgroup.subset_closure hg) x hx

theorem natCard_subtype_mem {α : Type*} (l : List α) (h : l.Nodup) :
    Nat.card {x // x ∈ l} = l.length := by
  classical
  have e : {x // x ∈ l} ≃ {x // x ∈ l.toFinset} := Equiv.subtypeEquivRight (by simp)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup h]

theorem nodup_spanE {gs : List (Perm (Fin 24))} {n : ℕ} (hS : spanOK n (gs.map tabP) = true) :
    (spanE gs).Nodup := by
  obtain ⟨-, hnd, -⟩ := of_decide_eq_true hS
  rw [← tabP_spanE] at hnd
  exact List.Nodup.of_map _ hnd

theorem length_spanE_of_spanOK {gs : List (Perm (Fin 24))} {n : ℕ}
    (hS : spanOK n (gs.map tabP) = true) : (spanE gs).length = n := by
  obtain ⟨hlen, -, -⟩ := of_decide_eq_true hS
  rw [← tabP_spanE, List.length_map] at hlen
  exact hlen

theorem card_closure_of_spanOK {gs : List (Perm (Fin 24))} {n : ℕ}
    (hS : spanOK n (gs.map tabP) = true) : Nat.card (Subgroup.closure {g | g ∈ gs}) = n := by
  rw [show Nat.card (Subgroup.closure {g | g ∈ gs}) = Nat.card {x // x ∈ spanE gs} from
    Nat.card_congr (Equiv.subtypeEquivRight (mem_closure_iff_of_spanOK hS)),
    natCard_subtype_mem _ (nodup_spanE hS), length_spanE_of_spanOK hS]

end CFSG.EvenSporadicStandard.Induction.Balance.Cocode24
