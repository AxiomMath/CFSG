module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelBase

public section

namespace CFSG.OddStandard.ChengHeld.Model

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.OddStandard.ChengHeldData

@[expose] def peArr (n : ℕ) (T : Array Tab) : Array Tab := Id.run do
  let mut a : Array Tab := Array.replicate n (idTab n)
  for i in [0:T.size] do
    a := a.set! (T[i]!)[0]! T[i]!
  return a

@[expose] def mkRegGen (n : ℕ) (gens : Array Tab) (E : Enum) : RegModel :=
  let T := E.tabs
  let pe := peArr n T
  let mul : Array ℕ := Array.ofFn (n := n * n) fun k => (pe[k.val / n]!)[k.val % n]!
  let inv : Array ℕ := Array.ofFn (n := n) fun a =>
    ((List.range n).find? fun b => mul[a.val * n + b]! == 0).getD 0
  let gpt : Array ℕ := gens.map fun g => g[0]!
  { N := n, mul := mul, inv := inv, gpt := gpt, order := T.map fun t => t[0]!,
    parent := E.par.map fun p => (T[p]!)[0]!, label := E.lab }

theorem mkReg_eq (α : ℕ) : mkReg α = mkRegGen (regN α) (regGens α) (regEnum α) := by
  unfold mkReg mkRegGen peArr
  rfl

theorem peArr_foldl (n : ℕ) (T : Array Tab) :
    peArr n T = (List.range T.size).foldl (fun a i => a.set! (T[i]!)[0]! T[i]!)
      (Array.replicate n (idTab n)) := by
  unfold peArr
  simp [Id.run, List.range_eq_range']
  rfl

theorem peArr_get {n : ℕ} {T : Array Tab}
    (hd : ∀ i j, i < T.size → j < T.size → (T[i]!)[0]! = (T[j]!)[0]! → i = j)
    (hlt : ∀ i < T.size, (T[i]!)[0]! < n) {i : ℕ} (hi : i < T.size) :
    (peArr n T)[(T[i]!)[0]!]! = T[i]! := by
  rw [peArr_foldl]
  have key : ∀ r, r ≤ T.size → ∀ i, i < r →
      ((List.range r).foldl (fun a i => a.set! (T[i]!)[0]! T[i]!)
        (Array.replicate n (idTab n)))[(T[i]!)[0]!]! = T[i]! := by
    intro r
    induction r with
    | zero => intro _ i hi; omega
    | succ r ih =>
      intro hr i hi
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      by_cases hir : i = r
      · subst hir
        have hsz : ∀ s, s ≤ T.size →
            ((List.range s).foldl (fun a i => a.set! (T[i]!)[0]! T[i]!)
              (Array.replicate n (idTab n))).size = n := by
          intro s _
          induction s with
          | zero => simp
          | succ s ihs =>
            rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
              Array.size_set!, ihs (by omega)]
        rw [Array.getElem!_set!_self _ _ _ (by rw [hsz i (by omega)]; exact hlt i (by omega))]
      · have hne : (T[r]!)[0]! ≠ (T[i]!)[0]! := fun h => hir (hd r i (by omega) (by omega) h).symm
        rw [Array.getElem!_set!_ne _ _ _ _ hne]
        exact ih (by omega) i (by omega)
  exact key T.size le_rfl i hi

structure RegData (n : ℕ) (gens : Array Tab) (E : Enum) (p : ℕ → Equiv.Perm (Fin n)) : Prop where
  pos : 0 < n
  gensRep : ∀ j < gens.size, TabRep gens[j]! (p j)
  enum : enumOK n gens E = true
  size : E.tabs.size = n
  distinct : ∀ i j, i < n → j < n → (E.tabs[i]!)[0]! = (E.tabs[j]!)[0]! → i = j

@[expose] def permGroup (n : ℕ) (p : ℕ → Equiv.Perm (Fin n)) (k : ℕ) :
    Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure {a | ∃ j < k, a = p j}

namespace RegData

variable {n : ℕ} {gens : Array Tab} {E : Enum} {p : ℕ → Equiv.Perm (Fin n)}

theorem enumerates (hd : RegData n gens E p) :
    Enumerates (permGroup n p gens.size) E.tabs.toList :=
  enumerates_closure (A := {a | ∃ j < gens.size, a = p j})
    (fun _ ⟨j, hj, ha⟩ => ⟨j, hj, ha ▸ hd.gensRep j hj⟩)
    (fun j hj => ⟨p j, ⟨j, hj, rfl⟩, hd.gensRep j hj⟩) hd.enum

theorem card_group (hd : RegData n gens E p) : Nat.card (permGroup n p gens.size) = n := by
  rw [hd.enumerates.card]
  simpa using hd.size

theorem exists_idx (hd : RegData n gens E p) {g : Equiv.Perm (Fin n)}
    (hg : g ∈ permGroup n p gens.size) : ∃ i < n, TabRep (E.tabs[i]!) g := by
  obtain ⟨i, hi, h⟩ := hd.enumerates.exists_pos hg
  exact ⟨i, hd.size ▸ hi, h⟩

theorem tab_zero_lt (hd : RegData n gens E p) {i : ℕ} (hi : i < n) : (E.tabs[i]!)[0]! < n := by
  obtain ⟨g, -, hg⟩ := hd.enumerates.exists_elt (k := i) (by rw [hd.size]; exact hi)
  rw [hg.apply ⟨0, hd.pos⟩]
  exact (g _).2

@[expose] def ptOf (hd : RegData n gens E p) (g : ↥(permGroup n p gens.size)) : ℕ :=
  ((g : Equiv.Perm (Fin n)) ⟨0, hd.pos⟩ : ℕ)

theorem ptOf_lt (hd : RegData n gens E p) (g : ↥(permGroup n p gens.size)) : hd.ptOf g < n :=
  (((g : Equiv.Perm (Fin n)) ⟨0, hd.pos⟩).2)

theorem ptOf_eq_tab (hd : RegData n gens E p) {g : ↥(permGroup n p gens.size)} {i : ℕ}
    (h : TabRep (E.tabs[i]!) (g : Equiv.Perm (Fin n))) : hd.ptOf g = (E.tabs[i]!)[0]! :=
  (h.apply ⟨0, hd.pos⟩).symm

theorem ptOf_inj (hd : RegData n gens E p) : Function.Injective hd.ptOf := by
  intro g g' h
  obtain ⟨i, hi, hg⟩ := hd.exists_idx g.2
  obtain ⟨j, hj, hg'⟩ := hd.exists_idx g'.2
  have h1 : (E.tabs[i]!)[0]! = (E.tabs[j]!)[0]! := by
    rw [← hd.ptOf_eq_tab hg, ← hd.ptOf_eq_tab hg']
    exact h
  have := hd.distinct i j hi hj h1
  subst this
  exact Subtype.ext (hg.perm_eq hg')

theorem ptOf_surj (hd : RegData n gens E p) {a : ℕ} (ha : a < n) : ∃ g, hd.ptOf g = a := by
  have hinj : Function.Injective (fun g => (⟨hd.ptOf g, hd.ptOf_lt g⟩ : Fin n)) := fun g g' h =>
    hd.ptOf_inj (by simpa using congrArg Fin.val h)
  have : Finite (permGroup n p gens.size) := by
    have : 0 < Nat.card (permGroup n p gens.size) := by rw [hd.card_group]; exact hd.pos
    exact Nat.finite_of_card_ne_zero this.ne'
  have hb := hinj.bijective_of_nat_card_le (by rw [hd.card_group, Nat.card_fin])
  obtain ⟨g, hg⟩ := hb.2 ⟨a, ha⟩
  exact ⟨g, by simpa using congrArg Fin.val hg⟩

theorem hlt (hd : RegData n gens E p) : ∀ i < E.tabs.size, (E.tabs[i]!)[0]! < n :=
  fun _ hi => hd.tab_zero_lt (hd.size ▸ hi)

theorem hdist (hd : RegData n gens E p) :
    ∀ i j, i < E.tabs.size → j < E.tabs.size → (E.tabs[i]!)[0]! = (E.tabs[j]!)[0]! → i = j :=
  fun _ _ hi hj h => hd.distinct _ _ (hd.size ▸ hi) (hd.size ▸ hj) h

theorem pe_get (hd : RegData n gens E p) {g : ↥(permGroup n p gens.size)} {i : ℕ} (hi : i < n)
    (h : TabRep (E.tabs[i]!) (g : Equiv.Perm (Fin n))) :
    (peArr n E.tabs)[hd.ptOf g]! = E.tabs[i]! := by
  rw [hd.ptOf_eq_tab h]
  exact peArr_get hd.hdist hd.hlt (hd.size ▸ hi)

theorem m_eq_pe (n : ℕ) (gens : Array Tab) (E : Enum) {a b : ℕ} (ha : a < n) (hb : b < n) :
    (mkRegGen n gens E).m a b = ((peArr n E.tabs)[a]!)[b]! := by
  have hab : a * n + b < n * n := by
    calc a * n + b < a * n + n := by omega
      _ = (a + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right n ha
  have hn : 0 < n := by omega
  unfold RegModel.m mkRegGen
  simp only
  rw [getElem!_pos _ _ (by simpa using hab), Array.getElem_ofFn]
  have e1 : (a * n + b) / n = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hb, zero_add]
  have e2 : (a * n + b) % n = b := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  simp only [e1, e2]

theorem m_ptOf (hd : RegData n gens E p) (g g' : ↥(permGroup n p gens.size)) :
    (mkRegGen n gens E).m (hd.ptOf g) (hd.ptOf g') = hd.ptOf (g * g') := by
  obtain ⟨i, hi, hg⟩ := hd.exists_idx g.2
  rw [m_eq_pe n gens E (hd.ptOf_lt g) (hd.ptOf_lt g'), hd.pe_get hi hg]
  rw [hg.apply ⟨hd.ptOf g', hd.ptOf_lt g'⟩]
  show _ = ((g.1 * g'.1) ⟨0, hd.pos⟩ : ℕ)
  rw [Equiv.Perm.mul_apply]
  rfl

theorem ptOf_one (hd : RegData n gens E p) : hd.ptOf 1 = 0 := rfl

theorem find_unique {l : List ℕ} {P : ℕ → Bool} {x : ℕ} (hx : x ∈ l) (hPx : P x = true)
    (hu : ∀ y ∈ l, P y = true → y = x) : l.find? P = some x := by
  have hs : (l.find? P).isSome = true := List.find?_isSome.2 ⟨x, hx, hPx⟩
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hs
  rw [hy]
  exact congrArg some (hu y (List.mem_of_find?_eq_some hy) (List.find?_some hy))

theorem inv_ptOf (hd : RegData n gens E p) (g : ↥(permGroup n p gens.size)) :
    (mkRegGen n gens E).inv[hd.ptOf g]! = hd.ptOf g⁻¹ := by
  have hlt := hd.ptOf_lt g
  have hinv : (mkRegGen n gens E).inv[hd.ptOf g]! =
      ((List.range n).find? fun b => (mkRegGen n gens E).m (hd.ptOf g) b == 0).getD 0 := by
    unfold mkRegGen
    simp only
    rw [getElem!_pos _ _ (by simpa using hlt), Array.getElem_ofFn]
    rfl
  rw [hinv, find_unique (x := hd.ptOf g⁻¹) (List.mem_range.2 (hd.ptOf_lt _))]
  · rfl
  · rw [hd.m_ptOf, mul_inv_cancel]
    simp [hd.ptOf_one]
  · intro y hy hP
    obtain ⟨g', rfl⟩ := hd.ptOf_surj (List.mem_range.1 hy)
    rw [hd.m_ptOf] at hP
    have h1 : hd.ptOf (g * g') = hd.ptOf 1 := by
      rw [hd.ptOf_one]
      simpa using hP
    have := hd.ptOf_inj h1
    rw [eq_inv_of_mul_eq_one_right this]

@[expose] def rep (hd : RegData n gens E p) :
    Rep (mkRegGen n gens E) ↥(permGroup n p gens.size) where
  pt := hd.ptOf
  pt_lt := hd.ptOf_lt
  pt_inj := hd.ptOf_inj
  pt_surj := fun _ ha => hd.ptOf_surj ha
  pt_mul := fun a b => (hd.m_ptOf a b).symm
  pt_one := hd.ptOf_one
  pt_inv := fun a => (hd.inv_ptOf a).symm

end RegData

structure TreeSpec (M : RegModel) : Prop where
  size_order : M.order.size = M.N
  order_zero : M.order[0]! = 0
  order_lt : ∀ i < M.N, M.order[i]! < M.N
  order_inj : ∀ i j, i < M.N → j < M.N → M.order[i]! = M.order[j]! → i = j
  step : ∀ i, 0 < i → i < M.N → ∃ p < i, M.parent[i]! = M.order[p]! ∧ M.label[i]! < 7 ∧
    M.order[i]! = M.m M.gpt[M.label[i]!]! M.order[p]!

namespace RegData

variable {n : ℕ} {gens : Array Tab} {E : Enum} {p : ℕ → Equiv.Perm (Fin n)}

theorem tab_zero_zero (hd : RegData n gens E p) : (E.tabs[0]!)[0]! = 0 := by
  have h0 := (treeOK_spec hd.enum).2.1
  rw [h0]
  have := TabRep.idTab_getElem! (n := n) ⟨0, hd.pos⟩
  simpa using this

theorem order_get (hd : RegData n gens E p) {i : ℕ} (hi : i < n) :
    (E.tabs.map fun t => t[0]!)[i]! = (E.tabs[i]!)[0]! := by
  rw [getElem!_pos _ _ (by simpa [hd.size] using hi), Array.getElem_map,
    getElem!_pos E.tabs i (hd.size ▸ hi)]

theorem parent_get (hd : RegData n gens E p) (i : ℕ) :
    (E.par.map fun q => (E.tabs[q]!)[0]!)[i]! = (E.tabs[E.par[i]!]!)[0]! := by
  by_cases hi : i < E.par.size
  · rw [getElem!_pos _ _ (by simpa using hi), Array.getElem_map, getElem!_pos E.par i hi]
  · rw [getElem!_neg _ _ (by simpa using hi), getElem!_neg E.par i hi]
    exact hd.tab_zero_zero.symm

theorem gen_mem (j k : ℕ) (hj : j < k) : p j ∈ permGroup n p k :=
  Subgroup.subset_closure ⟨j, hj, rfl⟩

theorem tree (hd : RegData n gens E p) (hk : gens.size = 7) : TreeSpec (mkRegGen n gens E) := by
  refine ⟨by simpa [mkRegGen] using hd.size, ?_, fun i hi => ?_, fun i j hi hj h => ?_, ?_⟩
  · show (E.tabs.map fun t => t[0]!)[0]! = 0
    rw [hd.order_get hd.pos]
    exact hd.tab_zero_zero
  · show (E.tabs.map fun t => t[0]!)[i]! < n
    rw [hd.order_get hi]
    exact hd.tab_zero_lt hi
  · exact hd.distinct i j hi hj (by
      simpa [mkRegGen, hd.order_get hi, hd.order_get hj] using h)
  · intro i hi0 hi
    have hin : i < n := hi
    obtain ⟨-, -, -, -, htree⟩ := treeOK_spec hd.enum
    obtain ⟨hpar, hlab, hT⟩ := htree i (by simpa [hd.size] using hin) hi0
    refine ⟨E.par[i]!, hpar, ?_, ?_, ?_⟩
    · show (E.par.map fun q => (E.tabs[q]!)[0]!)[i]! = (E.tabs.map fun t => t[0]!)[E.par[i]!]!
      rw [hd.parent_get, hd.order_get (hpar.trans hin)]
    · show E.lab[i]! < 7
      rw [← hk]
      exact hlab
    · show (E.tabs.map fun t => t[0]!)[i]! = (mkRegGen n gens E).m
        ((gens.map fun g => g[0]!)[E.lab[i]!]!) ((E.tabs.map fun t => t[0]!)[E.par[i]!]!)
      have hl : E.lab[i]! < gens.size := hlab
      have hparn : E.par[i]! < n := hpar.trans hin
      rw [hd.order_get hin, hd.order_get hparn]
      have hg : (gens.map fun g => g[0]!)[E.lab[i]!]! = (gens[E.lab[i]!]!)[0]! := by
        rw [getElem!_pos _ _ (by simpa using hl), Array.getElem_map, getElem!_pos gens _ hl]
      rw [hg]
      obtain ⟨idx, hidx, hgidx⟩ := hd.exists_idx (g := p E.lab[i]!) (gen_mem _ _ hl)
      have hgens : gens[E.lab[i]!]! = E.tabs[idx]! := (hd.gensRep _ hl).tab_eq hgidx
      have hg0 : (gens[E.lab[i]!]!)[0]! < n := by rw [hgens]; exact hd.tab_zero_lt hidx
      rw [m_eq_pe n gens E hg0 (hd.tab_zero_lt hparn), hgens,
        peArr_get hd.hdist hd.hlt (hd.size ▸ hidx), ← hgens]
      rw [hT]
      have := TabRep.comp_getElem! (n := n) gens[E.lab[i]!]! (E.tabs[E.par[i]!]!) ⟨0, hd.pos⟩
      simpa [leftStep] using this

end RegData

end CFSG.OddStandard.ChengHeld.Model
