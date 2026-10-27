module

public import Mathlib.GroupTheory.OrderOfElement
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.QuasithinUnique.A6Facts

open Equiv

@[expose] def codeN (n : ℕ) (σ : Equiv.Perm (Fin n)) : List ℕ := List.ofFn fun i => (σ i : ℕ)

variable {n : ℕ}

theorem codeN_getElem? (σ : Equiv.Perm (Fin n)) (m : ℕ) :
    (codeN n σ)[m]? = if h : m < n then some (σ ⟨m, h⟩ : ℕ) else none := by
  unfold codeN
  rw [List.getElem?_ofFn]

theorem codeN_getD (σ : Equiv.Perm (Fin n)) (i : Fin n) : (codeN n σ).getD i 0 = (σ i : ℕ) := by
  rw [List.getD_eq_getElem?_getD, codeN_getElem?]
  simp

theorem codeN_mul (σ τ : Equiv.Perm (Fin n)) :
    codeN n (σ * τ) = Core.cmul (codeN n σ) (codeN n τ) := by
  apply List.ext_getElem?
  intro m
  rw [codeN_getElem?, Core.cmul, List.getElem?_map, codeN_getElem?]
  by_cases hm : m < n
  · simp only [hm, dite_true, Option.map_some]
    congr 1
    rw [codeN_getD]
    rfl
  · simp [hm]

theorem codeN_one : codeN n (1 : Equiv.Perm (Fin n)) = List.range n := by
  apply List.ext_getElem?
  intro m
  by_cases hm : m < n
  · rw [codeN_getElem?, List.getElem?_range hm]
    simp [hm]
  · rw [codeN_getElem?, List.getElem?_eq_none (by simpa using hm)]
    simp [hm]

theorem codeN_injective : Function.Injective (codeN n) := by
  intro σ τ h
  ext i
  have := congrArg (fun l => l.getD i 0) h
  simp only [codeN_getD] at this
  exact_mod_cast this

theorem codeN_length (σ : Equiv.Perm (Fin n)) : (codeN n σ).length = n := by
  unfold codeN; exact List.length_ofFn

theorem getD_mem_or_default' {α : Type*} (l : List α) (m : ℕ) (d : α) :
    l.getD m d ∈ l ∨ l.getD m d = d := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[m]? with
  | none => right; simp
  | some a => left; simpa using List.mem_of_getElem? h

theorem buildCodes_foldl_specN {gens : List (Equiv.Perm (Fin n))} {gc : List (List ℕ)}
    (hgc : gens.map (codeN n) = gc) :
    ∀ (t : List (ℕ × ℕ)) (acc : List (List ℕ)),
      (∀ c ∈ acc, ∃ y ∈ Submonoid.closure {g | g ∈ gens}, codeN n y = c) →
      ∀ c ∈ t.foldl
        (fun acc pk => acc ++ [Core.cmul (acc.getD pk.1 (List.range n)) (gc.getD pk.2 (List.range n))]) acc,
        ∃ y ∈ Submonoid.closure {g | g ∈ gens}, codeN n y = c := by
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
      have h1 : ∃ y ∈ Submonoid.closure {g | g ∈ gens}, codeN n y = acc.getD pk.1 (List.range n) := by
        rcases getD_mem_or_default' acc pk.1 (List.range n) with h | h
        · exact hacc _ h
        · exact ⟨1, Submonoid.one_mem _, by rw [codeN_one, h]⟩
      have h2 : ∃ y ∈ Submonoid.closure {g | g ∈ gens}, codeN n y = gc.getD pk.2 (List.range n) := by
        rcases getD_mem_or_default' gc pk.2 (List.range n) with h | h
        · have h' : gc.getD pk.2 (List.range n) ∈ gens.map (codeN n) := by rw [hgc]; exact h
          obtain ⟨g, hg, hgc'⟩ := List.mem_map.mp h'
          exact ⟨g, Submonoid.subset_closure hg, hgc'⟩
        · exact ⟨1, Submonoid.one_mem _, by rw [codeN_one, h]⟩
      obtain ⟨y1, hy1, e1⟩ := h1
      obtain ⟨y2, hy2, e2⟩ := h2
      exact ⟨y1 * y2, Submonoid.mul_mem _ hy1 hy2, by rw [codeN_mul, e1, e2]⟩

theorem tbl_spec {gc E : List (List ℕ)} {T : List (List ℕ)} {e : List ℕ}
    (h : Core.tblCheckC e gc E T = true) :
    ∀ i (hi : i < E.length) k (hk : k < gc.length), ∃ hj : (T.getD i []).getD k 0 < E.length,
      E[(T.getD i []).getD k 0] = Core.cmul E[i] gc[k] := by
  intro i hi k hk
  unfold Core.tblCheckC at h
  rw [List.all_eq_true] at h
  have h1 := h i (List.mem_range.mpr hi)
  rw [List.all_eq_true] at h1
  have h2 := h1 k (List.mem_range.mpr hk)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h2
  obtain ⟨hj, hcode⟩ := h2
  refine ⟨hj, ?_⟩
  have hi' : E.getD i e = E[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  have hk' : gc.getD k e = gc[k] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
  have hj' : E.getD ((T.getD i []).getD k 0) e = E[(T.getD i []).getD k 0] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
  rw [hi', hk', hj'] at hcode
  exact hcode.symm

theorem mem_of_tblCheckCN {gc E : List (List ℕ)} {T : List (List ℕ)}
    (h : Core.tblCheckC (List.range n) gc E T = true) :
    ∀ c ∈ E, ∀ g ∈ gc, Core.cmul c g ∈ E := by
  intro c hc g hg
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  obtain ⟨hj, hcode⟩ := tbl_spec h i hi k hk
  rw [← hcode]
  exact List.getElem_mem hj

theorem range_mem_buildCodes (gc : List (List ℕ)) (tree : List (ℕ × ℕ)) :
    List.range n ∈ Core.buildCodes (List.range n) gc tree := by
  unfold Core.buildCodes
  suffices h : ∀ (t : List (ℕ × ℕ)) (acc : List (List ℕ)), List.range n ∈ acc →
      List.range n ∈ t.foldl (fun acc pk =>
        acc ++ [Core.cmul (acc.getD pk.1 (List.range n)) (gc.getD pk.2 (List.range n))]) acc by
    exact h tree [List.range n] (by simp)
  intro t
  induction t with
  | nil => intro acc h; exact h
  | cons pk t ih => intro acc h; exact ih _ (List.mem_append_left _ h)

theorem mem_closure_iff_of_tblN {gens : List (Equiv.Perm (Fin n))} {gc : List (List ℕ)}
    (hgc : gens.map (codeN n) = gc) {tree : List (ℕ × ℕ)} {T : List (List ℕ)}
    (h : Core.tblCheckC (List.range n) gc (Core.buildCodes (List.range n) gc tree) T = true) :
    (∀ x : Equiv.Perm (Fin n), x ∈ Subgroup.closure {g | g ∈ gens} ↔
        codeN n x ∈ Core.buildCodes (List.range n) gc tree) ∧
      ∀ c ∈ Core.buildCodes (List.range n) gc tree,
        ∃ x ∈ Subgroup.closure {g | g ∈ gens}, codeN n x = c := by
  have hsub : (Subgroup.closure {g | g ∈ gens}).toSubmonoid = Submonoid.closure {g | g ∈ gens} :=
    Subgroup.closure_toSubmonoid_of_finite
  have hspec := buildCodes_foldl_specN hgc tree [List.range n] (by
    intro c hc
    rw [List.mem_singleton] at hc
    exact ⟨1, Submonoid.one_mem _, by rw [hc, codeN_one]⟩)
  have hspec' : ∀ c ∈ Core.buildCodes (List.range n) gc tree,
      ∃ y ∈ Submonoid.closure {g | g ∈ gens}, codeN n y = c := hspec
  refine ⟨fun x => ⟨fun hx => ?_, fun hx => ?_⟩, fun c hc => ?_⟩
  · have hx' : x ∈ Submonoid.closure {g | g ∈ gens} := by
      rw [← hsub]; exact hx
    refine Submonoid.closure_induction_right
      (motive := fun m _ => codeN n m ∈ Core.buildCodes (List.range n) gc tree) ?_ ?_ hx'
    · rw [codeN_one]; exact range_mem_buildCodes gc tree
    · intro m _ y hy ih
      rw [codeN_mul]
      refine mem_of_tblCheckCN h _ ih _ ?_
      rw [← hgc]
      exact List.mem_map.mpr ⟨y, hy, rfl⟩
  · obtain ⟨y, hy, hyc⟩ := hspec' _ hx
    have : x = y := codeN_injective hyc.symm
    rw [this]
    have h3 : y ∈ (Subgroup.closure {g | g ∈ gens}).toSubmonoid := by rw [hsub]; exact hy
    exact h3
  · obtain ⟨y, hy, hyc⟩ := hspec' c hc
    refine ⟨y, ?_, hyc⟩
    have h3 : y ∈ (Subgroup.closure {g | g ∈ gens}).toSubmonoid := by rw [hsub]; exact hy
    exact h3

theorem card_closure_eq_of_tblN {gens : List (Equiv.Perm (Fin n))} {gc : List (List ℕ)}
    (hgc : gens.map (codeN n) = gc) {tree : List (ℕ × ℕ)} {T : List (List ℕ)}
    (h : Core.tblCheckC (List.range n) gc (Core.buildCodes (List.range n) gc tree) T = true)
    (hnd : (Core.buildCodes (List.range n) gc tree).Nodup) :
    Nat.card (Subgroup.closure {g | g ∈ gens}) =
      (Core.buildCodes (List.range n) gc tree).length := by
  obtain ⟨hmem, hsurj⟩ := mem_closure_iff_of_tblN hgc h
  set E := Core.buildCodes (List.range n) gc tree
  have h1 : codeN n '' ((Subgroup.closure {g | g ∈ gens} : Subgroup (Equiv.Perm (Fin n))) :
      Set (Equiv.Perm (Fin n))) = ↑E.toFinset := by
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using (hmem x).mp hx
    · intro hc
      have hc' : c ∈ E := by simpa using hc
      obtain ⟨x, hx, rfl⟩ := hsurj c hc'
      exact ⟨x, hx, rfl⟩
  calc Nat.card (Subgroup.closure {g | g ∈ gens})
      = Nat.card (codeN n '' ((Subgroup.closure {g | g ∈ gens} :
          Subgroup (Equiv.Perm (Fin n))) : Set (Equiv.Perm (Fin n)))) :=
        (Nat.card_image_of_injective codeN_injective _).symm
    _ = Nat.card ↥(↑E.toFinset : Set (List ℕ)) := by rw [h1]
    _ = E.length := by
        rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

end CFSG.QuasithinUnique.A6Facts
