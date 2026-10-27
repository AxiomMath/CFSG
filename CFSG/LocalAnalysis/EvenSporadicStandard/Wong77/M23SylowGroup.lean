module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.M23SylowTab

public section

namespace CFSG.EvenSporadicStandard.Wong77.M23Sylow

open CFSG.Blueprint
open CFSG.Blueprint.NativeSporadic (Carrier)

instance : Finite (Carrier .M23) := inferInstanceAs (Finite NativeSporadic.M23)

@[expose] def sylowGens : List (Carrier .M23) := sylowWords.map (wordElt [genA, genB, genBi])

theorem tab_sylowGens : sylowGens.map tab = gensTab := by
  have h : [genA, genB, genBi].map tab = letterTabs := by
    simp only [List.map_cons, List.map_nil, tab_genA, tab_genB, tab_genBi, letterTabs]
  simp only [sylowGens, gensTab, List.map_map]
  refine List.map_congr_left fun w _ => ?_
  rw [Function.comp_apply, tab_wordElt, h]

@[expose] def sylowS : Subgroup (Carrier .M23) := Subgroup.closure {g | g ∈ sylowGens}

theorem sylowGens_mem {g : Carrier .M23} (hg : g ∈ sylowGens) : g ∈ sylowS :=
  Subgroup.subset_closure hg

theorem tab_mem_span_of_mem_sylowS (hS : sylowOK gensTab = true) {x : Carrier .M23}
    (hx : x ∈ sylowS) : tab x ∈ span gensTab := by
  obtain ⟨-, -, hcl⟩ := of_decide_eq_true hS
  have hx' : x ∈ Submonoid.closure {g | g ∈ sylowGens} := by
    rw [← Subgroup.closure_toSubmonoid_of_isOfFinOrder (fun x _ => isOfFinOrder_of_finite x)]
    exact hx
  have key : ∀ y ∈ Submonoid.closure {g | g ∈ sylowGens},
      ∀ l : Carrier .M23, tab l ∈ span gensTab → tab (l * y) ∈ span gensTab := by
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

theorem mem_sylowS_iff (hS : sylowOK gensTab = true) (x : Carrier .M23) :
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

end CFSG.EvenSporadicStandard.Wong77.M23Sylow
