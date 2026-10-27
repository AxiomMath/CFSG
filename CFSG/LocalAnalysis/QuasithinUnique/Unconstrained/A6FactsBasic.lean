module

public import Mathlib.GroupTheory.OrderOfElement
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.QuasithinUnique.A6Facts

open Equiv

abbrev P10 : Type := Equiv.Perm (Fin 10)

@[expose] def code (σ : P10) : List ℕ := List.ofFn fun i => (σ i : ℕ)

theorem code_getElem? (σ : P10) (n : ℕ) :
    (code σ)[n]? = if h : n < 10 then some (σ ⟨n, h⟩ : ℕ) else none := by
  unfold code
  rw [List.getElem?_ofFn]

theorem code_getD (σ : P10) (i : Fin 10) : (code σ).getD i 0 = (σ i : ℕ) := by
  rw [List.getD_eq_getElem?_getD, code_getElem?]
  simp

theorem code_mul (σ τ : P10) : code (σ * τ) = Core.cmul (code σ) (code τ) := by
  apply List.ext_getElem?
  intro n
  rw [code_getElem?, Core.cmul, List.getElem?_map, code_getElem?]
  by_cases hn : n < 10
  · simp only [hn, dite_true, Option.map_some]
    congr 1
    rw [code_getD]
    rfl
  · simp [hn]

theorem code_one : code (1 : P10) = Core.cid := by
  apply List.ext_getElem?
  intro n
  by_cases hn : n < 10
  · rw [code_getElem?, Core.cid, List.getElem?_range hn]
    simp [hn]
  · rw [code_getElem?, Core.cid, List.getElem?_eq_none (by simpa using hn)]
    simp [hn]

theorem code_injective : Function.Injective code := by
  intro σ τ h
  ext i
  have := congrArg (fun l => l.getD i 0) h
  simp only [code_getD] at this
  exact_mod_cast this

theorem code_length (σ : P10) : (code σ).length = 10 := by
  unfold code; exact List.length_ofFn

theorem getD_mem_or_default {α : Type*} (l : List α) (n : ℕ) (d : α) :
    l.getD n d ∈ l ∨ l.getD n d = d := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[n]? with
  | none => right; simp
  | some a => left; simpa using List.mem_of_getElem? h

theorem buildCodes_foldl_spec {gens : List P10} {gc : List (List ℕ)} (hgc : gens.map code = gc) :
    ∀ (t : List (ℕ × ℕ)) (acc : List (List ℕ)),
      (∀ c ∈ acc, ∃ y ∈ Submonoid.closure {g | g ∈ gens}, code y = c) →
      ∀ c ∈ t.foldl
        (fun acc pk => acc ++ [Core.cmul (acc.getD pk.1 Core.cid) (gc.getD pk.2 Core.cid)]) acc,
        ∃ y ∈ Submonoid.closure {g | g ∈ gens}, code y = c := by
  intro t
  induction t with
  | nil => intro acc hacc c hc; exact hacc c hc
  | cons pk t ih =>
    intro acc hacc
    apply ih
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hacc c hc
    · rw [List.mem_singleton] at hc
      rw [hc]
      have h1 : ∃ y ∈ Submonoid.closure {g | g ∈ gens}, code y = acc.getD pk.1 Core.cid := by
        rcases getD_mem_or_default acc pk.1 Core.cid with h | h
        · exact hacc _ h
        · exact ⟨1, Submonoid.one_mem _, by rw [code_one, h]⟩
      have h2 : ∃ y ∈ Submonoid.closure {g | g ∈ gens}, code y = gc.getD pk.2 Core.cid := by
        rcases getD_mem_or_default gc pk.2 Core.cid with h | h
        · have h' : gc.getD pk.2 Core.cid ∈ gens.map code := by rw [hgc]; exact h
          obtain ⟨g, hg, hgc'⟩ := List.mem_map.mp h'
          exact ⟨g, Submonoid.subset_closure hg, hgc'⟩
        · exact ⟨1, Submonoid.one_mem _, by rw [code_one, h]⟩
      obtain ⟨y1, hy1, e1⟩ := h1
      obtain ⟨y2, hy2, e2⟩ := h2
      exact ⟨y1 * y2, Submonoid.mul_mem _ hy1 hy2, by rw [code_mul, e1, e2]⟩

theorem mem_of_tblCheckC {gc E : List (List ℕ)} {T : List (List ℕ)}
    (h : Core.tblCheckC Core.cid gc E T = true) :
    ∀ c ∈ E, ∀ g ∈ gc, Core.cmul c g ∈ E := by
  intro c hc g hg
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  unfold Core.tblCheckC at h
  rw [List.all_eq_true] at h
  have h1 := h i (List.mem_range.mpr hi)
  rw [List.all_eq_true] at h1
  have h2 := h1 k (List.mem_range.mpr hk)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h2
  obtain ⟨hj, hcode⟩ := h2
  have hi' : E.getD i Core.cid = E[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  have hk' : gc.getD k Core.cid = gc[k] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
  rw [hi', hk'] at hcode
  have hj' : E.getD ((T.getD i []).getD k 0) Core.cid = E[(T.getD i []).getD k 0] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
  rw [hj'] at hcode
  rw [hcode]
  exact List.getElem_mem hj

theorem cid_mem_buildCodes (gc : List (List ℕ)) (tree : List (ℕ × ℕ)) :
    Core.cid ∈ Core.buildCodes Core.cid gc tree := by
  unfold Core.buildCodes
  suffices h : ∀ (t : List (ℕ × ℕ)) (acc : List (List ℕ)), Core.cid ∈ acc →
      Core.cid ∈ t.foldl (fun acc pk =>
        acc ++ [Core.cmul (acc.getD pk.1 Core.cid) (gc.getD pk.2 Core.cid)]) acc by
    exact h tree [Core.cid] (by simp)
  intro t
  induction t with
  | nil => intro acc h; exact h
  | cons pk t ih => intro acc h; exact ih _ (List.mem_append_left _ h)

theorem mem_closure_iff_of_tbl {gens : List P10} {gc : List (List ℕ)} (hgc : gens.map code = gc)
    {tree : List (ℕ × ℕ)} {T : List (List ℕ)}
    (h : Core.tblCheckC Core.cid gc (Core.buildCodes Core.cid gc tree) T = true) :
    (∀ x : P10, x ∈ Subgroup.closure {g | g ∈ gens} ↔ code x ∈ Core.buildCodes Core.cid gc tree) ∧
      ∀ c ∈ Core.buildCodes Core.cid gc tree,
        ∃ x ∈ Subgroup.closure {g | g ∈ gens}, code x = c := by
  have hsub : (Subgroup.closure {g | g ∈ gens}).toSubmonoid = Submonoid.closure {g | g ∈ gens} :=
    Subgroup.closure_toSubmonoid_of_finite
  have hspec := buildCodes_foldl_spec hgc tree [Core.cid] (by
    intro c hc
    rw [List.mem_singleton] at hc
    exact ⟨1, Submonoid.one_mem _, by rw [hc, code_one]⟩)
  have hspec' : ∀ c ∈ Core.buildCodes Core.cid gc tree,
      ∃ y ∈ Submonoid.closure {g | g ∈ gens}, code y = c := hspec
  refine ⟨fun x => ⟨fun hx => ?_, fun hx => ?_⟩, fun c hc => ?_⟩
  · have hx' : x ∈ Submonoid.closure {g | g ∈ gens} := by
      rw [← hsub]; exact hx
    refine Submonoid.closure_induction_right
      (motive := fun m _ => code m ∈ Core.buildCodes Core.cid gc tree) ?_ ?_ hx'
    · rw [code_one]; exact cid_mem_buildCodes gc tree
    · intro m _ y hy ih
      rw [code_mul]
      refine mem_of_tblCheckC h _ ih _ ?_
      rw [← hgc]
      exact List.mem_map.mpr ⟨y, hy, rfl⟩
  · obtain ⟨y, hy, hyc⟩ := hspec' _ hx
    have : x = y := code_injective hyc.symm
    rw [this]
    have h3 : y ∈ (Subgroup.closure {g | g ∈ gens}).toSubmonoid := by rw [hsub]; exact hy
    exact h3
  · obtain ⟨y, hy, hyc⟩ := hspec' c hc
    refine ⟨y, ?_, hyc⟩
    have h3 : y ∈ (Subgroup.closure {g | g ∈ gens}).toSubmonoid := by rw [hsub]; exact hy
    exact h3

theorem card_closure_eq_of_tbl {gens : List P10} {gc : List (List ℕ)} (hgc : gens.map code = gc)
    {tree : List (ℕ × ℕ)} {T : List (List ℕ)}
    (h : Core.tblCheckC Core.cid gc (Core.buildCodes Core.cid gc tree) T = true)
    (hnd : (Core.buildCodes Core.cid gc tree).Nodup) :
    Nat.card (Subgroup.closure {g | g ∈ gens}) = (Core.buildCodes Core.cid gc tree).length := by
  obtain ⟨hmem, hsurj⟩ := mem_closure_iff_of_tbl hgc h
  set E := Core.buildCodes Core.cid gc tree
  have h1 : code '' ((Subgroup.closure {g | g ∈ gens} : Subgroup P10) : Set P10) =
      ↑E.toFinset := by
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using (hmem x).mp hx
    · intro hc
      have hc' : c ∈ E := by simpa using hc
      obtain ⟨x, hx, rfl⟩ := hsurj c hc'
      exact ⟨x, hx, rfl⟩
  calc Nat.card (Subgroup.closure {g | g ∈ gens})
      = Nat.card (code '' ((Subgroup.closure {g | g ∈ gens} : Subgroup P10) : Set P10)) :=
        (Nat.card_image_of_injective code_injective _).symm
    _ = Nat.card ↥(↑E.toFinset : Set (List ℕ)) := by rw [h1]
    _ = E.length := by
        rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

theorem card_eq_of_code_mem {X : Subgroup P10} {E : List (List ℕ)} (hnd : E.Nodup)
    (hmem : ∀ x : P10, x ∈ X ↔ code x ∈ E) (hsurj : ∀ c ∈ E, ∃ x ∈ X, code x = c) :
    Nat.card X = E.length := by
  have h1 : code '' (X : Set P10) = ↑E.toFinset := by
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using (hmem x).mp hx
    · intro hc
      have hc' : c ∈ E := by simpa using hc
      obtain ⟨x, hx, rfl⟩ := hsurj c hc'
      exact ⟨x, hx, rfl⟩
  calc Nat.card X = Nat.card (code '' (X : Set P10)) :=
        (Nat.card_image_of_injective code_injective _).symm
    _ = Nat.card ↥(↑E.toFinset : Set (List ℕ)) := by rw [h1]
    _ = E.length := by
        rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

end CFSG.QuasithinUnique.A6Facts
