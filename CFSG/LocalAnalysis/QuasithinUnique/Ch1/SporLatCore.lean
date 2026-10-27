module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatPt
public import Certificates.Data.CFSGNative.SporLat.Spec
public import Std.Data.HashMap
public import Std.Data.HashSet

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat

open CFSG.QuasithinUnique.K1.SporadicPerm

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)] {Lab : Type}

@[expose] def lab (n : ℕ) [MulAction Γ (Fin n)] (A : LabAct Lab) (Δ : Lab) (g : Γ) : Lab :=
  A.act (tab n g).toArray Δ

section Lab

variable {A : LabAct Lab} {valid : Lab → Prop} {Δ : Lab}

theorem lab_mul (hlaw : LabLawful Γ n A valid) (hΔ : valid Δ) (g h : Γ) :
    lab n A Δ (g * h) = A.act (tab n g).toArray (lab n A Δ h) := hlaw.act_mul g h hΔ

theorem lab_one (hlaw : LabLawful Γ n A valid) (hΔ : valid Δ) : lab n A Δ (1 : Γ) = Δ :=
  hlaw.act_one hΔ

theorem valid_lab (hlaw : LabLawful Γ n A valid) (hΔ : valid Δ) (g : Γ) : valid (lab n A Δ g) :=
  hlaw.valid_act g hΔ

@[expose] def stab (hlaw : LabLawful Γ n A valid) (hΔ : valid Δ) : Subgroup Γ where
  carrier := {g | lab n A Δ g = Δ}
  one_mem' := lab_one hlaw hΔ
  mul_mem' {g h} hg hh := by
    show lab n A Δ (g * h) = Δ
    rw [lab_mul hlaw hΔ, show lab n A Δ h = Δ from hh]
    exact hg
  inv_mem' {g} hg := by
    show lab n A Δ g⁻¹ = Δ
    have h1 : lab n A Δ (g⁻¹ * g) = A.act (tab n g⁻¹).toArray (lab n A Δ g) :=
      lab_mul hlaw hΔ _ _
    rw [inv_mul_cancel, lab_one hlaw hΔ, show lab n A Δ g = Δ from hg] at h1
    exact h1.symm

theorem mem_stab (hlaw : LabLawful Γ n A valid) (hΔ : valid Δ) {g : Γ} :
    g ∈ stab hlaw hΔ ↔ lab n A Δ g = Δ := Iff.rfl

theorem lab_eq_iff (hlaw : LabLawful Γ n A valid) (hΔ : valid Δ) (g h : Γ) :
    lab n A Δ g = lab n A Δ h ↔ g⁻¹ * h ∈ stab hlaw hΔ := by
  rw [mem_stab, lab_mul hlaw hΔ]
  constructor
  · intro e
    rw [← e]
    have h1 : lab n A Δ (g⁻¹ * g) = A.act (tab n g⁻¹).toArray (lab n A Δ g) :=
      lab_mul hlaw hΔ _ _
    rw [inv_mul_cancel, lab_one hlaw hΔ] at h1
    exact h1.symm
  · intro e
    have h1 : lab n A Δ (g * (g⁻¹ * h)) = A.act (tab n g).toArray (lab n A Δ (g⁻¹ * h)) :=
      lab_mul hlaw hΔ _ _
    have h2 : lab n A Δ (g⁻¹ * h) = Δ := by rw [lab_mul hlaw hΔ]; exact e
    rw [mul_inv_cancel_left, h2] at h1
    exact h1.symm

end Lab

section Distinct

variable [DecidableEq Lab] [Hashable Lab]

@[expose] def distinctStep (acc : Bool × Std.HashSet Lab) (x : Lab) : Bool × Std.HashSet Lab :=
  if acc.2.contains x then (false, acc.2) else (acc.1, acc.2.insert x)

theorem distinct_foldl_false (l : List Lab) (S : Std.HashSet Lab) :
    (l.foldl distinctStep (false, S)).1 = false := by
  induction l generalizing S with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons, distinctStep]
    split_ifs
    · exact ih S
    · exact ih _

theorem distinct_foldl_true (l : List Lab) (f : Bool) (S : Std.HashSet Lab)
    (h : (l.foldl distinctStep (f, S)).1 = true) :
    f = true ∧ l.Nodup ∧ ∀ x ∈ l, S.contains x = false := by
  induction l generalizing f S with
  | nil => simpa using h
  | cons x l ih =>
    simp only [List.foldl_cons, distinctStep] at h
    by_cases hc : S.contains x = true
    · simp only [hc, ite_true] at h
      rw [distinct_foldl_false] at h
      exact absurd h (by simp)
    · simp only [hc] at h
      obtain ⟨hf, hnd, hnot⟩ := ih f _ h
      refine ⟨hf, ?_, ?_⟩
      · refine List.nodup_cons.mpr ⟨fun hx => ?_, hnd⟩
        have := hnot x hx
        simp at this
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · simpa using hc
        · have := hnot y hy
          rw [Std.HashSet.contains_insert] at this
          simp only [Bool.or_eq_false_iff] at this
          exact this.2

theorem distinctB_spec [Inhabited Lab] {a : Array Lab} (h : distinctB a = true) :
    ∀ i j, i < a.size → j < a.size → a[i]! = a[j]! → i = j := by
  have h' : (a.toList.foldl distinctStep (true, ∅)).1 = true := by
    rw [Array.foldl_toList]; exact h
  obtain ⟨-, hnd, -⟩ := distinct_foldl_true _ _ _ h'
  intro i j hi hj hij
  rw [getElem!_pos a i hi, getElem!_pos a j hj] at hij
  exact (hnd.getElem_inj_iff (hi := by simpa using hi) (hj := by simpa using hj)).mp
    (by simpa using hij)

end Distinct

@[expose] def evalElt (els : Array Γ) (w : List ℕ) : Γ := (w.map fun l => els.getD l 1).prod

theorem evalElt_nil (els : Array Γ) : evalElt els [] = 1 := by simp [evalElt]

theorem evalElt_cons (els : Array Γ) (l : ℕ) (w : List ℕ) :
    evalElt els (l :: w) = els.getD l 1 * evalElt els w := by simp [evalElt]

@[expose] def wordElt (a b : Γ) (w : List ℕ) : Γ := evalElt #[a, b] w

theorem evalElt_mem {H : Subgroup Γ} (els : Array Γ) (hels : ∀ l < els.size, els.getD l 1 ∈ H)
    (w : List ℕ) (hw : ∀ l ∈ w, l < els.size) : evalElt els w ∈ H := by
  induction w with
  | nil => rw [evalElt_nil]; exact H.one_mem
  | cons l w ih =>
    rw [evalElt_cons]
    exact H.mul_mem (hels l (hw l List.mem_cons_self))
      (ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))

theorem evalElt_getD_mem_closure (els : Array Γ) {l : ℕ} (hl : l < els.size) :
    els.getD l 1 ∈ Subgroup.closure {x | x ∈ els.toList} := by
  apply Subgroup.subset_closure
  show els.getD l 1 ∈ els.toList
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hl]
  simp

section Omega

variable [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

variable {A : LabAct Lab} {valid : Lab → Prop} {Δ : Lab} {O : OmegaData Lab}
  {letters : Array (Array ℕ)}

theorem OmegaSpec.pathWord_lt (hO : OmegaSpec A.act letters Δ O) :
    ∀ f i, i < O.lbl.size → ∀ l ∈ O.pathWord f i, l < letters.size := by
  obtain ⟨-, -, -, htree, -⟩ := hO
  intro f
  induction f with
  | zero => intro i _ l hl; simp [OmegaData.pathWord] at hl
  | succ f ih =>
    intro i hi l hl
    by_cases hi0 : i = 0
    · simp [OmegaData.pathWord, hi0] at hl
    · obtain ⟨hlt, hvia, -⟩ := htree i hi (Nat.pos_of_ne_zero hi0)
      simp only [OmegaData.pathWord, hi0, ite_false, List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact hvia
      · exact ih _ (by omega) l hl

theorem OmegaSpec.reach (hlaw : LabLawful Γ n A valid) (hΔ : valid Δ) (els : Array Γ)
    (hel : ∀ l < letters.size, letters[l]! = (tab n (els.getD l 1)).toArray)
    (hO : OmegaSpec A.act letters Δ O) :
    ∀ f i, i ≤ f → i < O.lbl.size →
      lab n A Δ (evalElt els (O.pathWord f i)) = O.lbl[i]! := by
  obtain ⟨h0, hpos, hA, htree, -⟩ := hO
  intro f
  induction f with
  | zero =>
    intro i hi _
    obtain rfl : i = 0 := by omega
    simp only [OmegaData.pathWord, evalElt_nil]
    rw [lab_one hlaw hΔ, h0]
  | succ f ih =>
    intro i hi hiN
    by_cases hi0 : i = 0
    · subst hi0
      simp only [OmegaData.pathWord, ite_true, evalElt_nil]
      rw [lab_one hlaw hΔ, h0]
    · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
      obtain ⟨hlt, hvia, hpn⟩ := htree i hiN hipos
      have hp := ih (O.par[i]!) (by omega) (by omega)
      simp only [OmegaData.pathWord, hi0, ite_false]
      rw [evalElt_cons, lab_mul hlaw hΔ, hp, ← hel _ hvia,
        ← (hA _ hvia (O.par[i]!) (by omega)).2, hpn]

theorem OmegaSpec.cover [Finite Γ] (hlaw : LabLawful Γ n A valid) (hΔ : valid Δ) (els : Array Γ)
    (hsz : els.size = letters.size)
    (hel : ∀ l < letters.size, letters[l]! = (tab n (els.getD l 1)).toArray)
    (hO : OmegaSpec A.act letters Δ O) {H : Subgroup Γ}
    (hH : Subgroup.closure {x | x ∈ els.toList} = H) :
    ∀ g ∈ H, ∃ i < O.lbl.size, lab n A Δ g = O.lbl[i]! := by
  obtain ⟨h0, hpos, hA, htree, hdist⟩ := hO
  intro g hg
  rw [← hH] at hg
  have hg' : g ∈ Submonoid.closure {x | x ∈ els.toList} := by
    have := Subgroup.closure_toSubmonoid_of_finite (s := {x | x ∈ els.toList})
    rw [← this]; exact hg
  clear hg
  induction hg' using Submonoid.closure_induction_left with
  | one => exact ⟨0, hpos, by rw [lab_one hlaw hΔ, h0]⟩
  | mul_left x hx y _ ih =>
    obtain ⟨i, hi, hyi⟩ := ih
    obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hx
    have hl' : l < letters.size := by rw [← hsz]; simpa using hl
    have hxl : els.getD l 1 = els.toList[l] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hl)]
      simp
    refine ⟨(O.pn[l]!)[i]!, (hA l hl' i hi).1, ?_⟩
    rw [lab_mul hlaw hΔ, hyi, ← hxl, ← hel l hl', (hA l hl' i hi).2]

theorem OmegaSpec.card_eq [Finite Γ] (hlaw : LabLawful Γ n A valid) (hΔ : valid Δ) (els : Array Γ)
    (hsz : els.size = letters.size)
    (hel : ∀ l < letters.size, letters[l]! = (tab n (els.getD l 1)).toArray)
    (hO : OmegaSpec A.act letters Δ O) {H : Subgroup Γ}
    (hH : Subgroup.closure {x | x ∈ els.toList} = H) (hS : stab hlaw hΔ ≤ H) :
    Nat.card H = O.lbl.size * Nat.card (stab hlaw hΔ) := by
  classical
  have hcover := hO.cover hlaw hΔ els hsz hel hH
  have hreach := hO.reach hlaw hΔ els hel
  have hwlt := hO.pathWord_lt
  have hdist := distinctB_spec hO.2.2.2.2
  have hels : ∀ l < els.size, els.getD l 1 ∈ H := fun l hl => by
    rw [← hH]; exact evalElt_getD_mem_closure els hl
  have hwH : ∀ i < O.lbl.size, evalElt els (O.pathWord i i) ∈ H := fun i hi =>
    evalElt_mem els hels _ (fun l hl => by rw [hsz]; exact hwlt i i hi l hl)
  have hsub : Nat.card ((stab hlaw hΔ).subgroupOf H) = Nat.card (stab hlaw hΔ) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ((stab hlaw hΔ).subgroupOf H), hsub]
  congr 1
  let e : Fin O.lbl.size → H ⧸ (stab hlaw hΔ).subgroupOf H := fun i =>
    (QuotientGroup.mk ⟨evalElt els (O.pathWord i i), hwH i i.2⟩ : H ⧸ (stab hlaw hΔ).subgroupOf H)
  have hlabe : ∀ i : Fin O.lbl.size,
      lab n A Δ (evalElt els (O.pathWord i i)) = O.lbl[(i : ℕ)]! :=
    fun i => hreach i i le_rfl i.2
  have hbij : Function.Bijective e := by
    constructor
    · intro i j hij
      have h1 := QuotientGroup.eq.mp hij
      have h3 : (evalElt els (O.pathWord i i))⁻¹ * evalElt els (O.pathWord j j) ∈
          stab hlaw hΔ := h1
      have h4 := (lab_eq_iff hlaw hΔ _ _).mpr h3
      rw [hlabe, hlabe] at h4
      exact Fin.ext (hdist i j i.2 j.2 h4)
    · intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨i, hi, hyi⟩ := hcover (y : Γ) y.2
      refine ⟨⟨i, hi⟩, ?_⟩
      apply QuotientGroup.eq.mpr
      show (evalElt els (O.pathWord i i))⁻¹ * (y : Γ) ∈ stab hlaw hΔ
      exact (lab_eq_iff hlaw hΔ _ _).mp (by rw [hlabe ⟨i, hi⟩, hyi])
  have := Nat.card_eq_of_bijective e hbij
  simpa using this.symm

theorem OmegaSpec.mem_iff [Finite Γ] (hlaw : LabLawful Γ n A valid) (hΔ : valid Δ) (els : Array Γ)
    (hsz : els.size = letters.size)
    (hel : ∀ l < letters.size, letters[l]! = (tab n (els.getD l 1)).toArray)
    (hO : OmegaSpec A.act letters Δ O) {H : Subgroup Γ}
    (hH : Subgroup.closure {x | x ∈ els.toList} = H) (hS : stab hlaw hΔ ≤ H) (g : Γ) :
    g ∈ H ↔ ∃ i < O.lbl.size, lab n A Δ g = O.lbl[i]! := by
  have hcover := hO.cover hlaw hΔ els hsz hel hH
  have hreach := hO.reach hlaw hΔ els hel
  have hwlt := hO.pathWord_lt
  have hels : ∀ l < els.size, els.getD l 1 ∈ H := fun l hl => by
    rw [← hH]; exact evalElt_getD_mem_closure els hl
  constructor
  · exact hcover g
  · rintro ⟨i, hi, hgi⟩
    have hwH : evalElt els (O.pathWord i i) ∈ H :=
      evalElt_mem els hels _ (fun l hl => by rw [hsz]; exact hwlt i i hi l hl)
    have h1 : (evalElt els (O.pathWord i i))⁻¹ * g ∈ stab hlaw hΔ :=
      (lab_eq_iff hlaw hΔ _ _).mp (by rw [hreach i i le_rfl hi, hgi])
    have : g = evalElt els (O.pathWord i i) * ((evalElt els (O.pathWord i i))⁻¹ * g) := by group
    rw [this]
    exact H.mul_mem hwH (hS h1)

theorem OmegaSpec.card_top [Finite Γ] (hlaw : LabLawful Γ n A valid) (hΔ : valid Δ)
    (els : Array Γ) (hsz : els.size = letters.size)
    (hel : ∀ l < letters.size, letters[l]! = (tab n (els.getD l 1)).toArray)
    (hO : OmegaSpec A.act letters Δ O)
    (hH : Subgroup.closure {x | x ∈ els.toList} = ⊤) :
    Nat.card Γ = O.lbl.size * Nat.card (stab hlaw hΔ) := by
  have := hO.card_eq hlaw hΔ els hsz hel hH le_top
  rwa [Subgroup.card_top] at this

theorem OmegaSpec.sylow_eq_stab [Finite Γ] (hlaw : LabLawful Γ n A valid) (hΔ : valid Δ)
    (els : Array Γ) (hsz : els.size = letters.size)
    (hel : ∀ l < letters.size, letters[l]! = (tab n (els.getD l 1)).toArray)
    (hO : OmegaSpec A.act letters Δ O)
    (hH : Subgroup.closure {x | x ∈ els.toList} = ⊤) {gens : List Γ}
    (hs : ∀ s ∈ gens, lab n A Δ s = Δ) {k : ℕ}
    (hS : Nat.card (Subgroup.closure {x | x ∈ gens}) = 2 ^ k)
    (hΓ : Nat.card Γ = O.lbl.size * 2 ^ k) :
    Subgroup.closure {x | x ∈ gens} = stab hlaw hΔ := by
  have hle : Subgroup.closure {x | x ∈ gens} ≤ stab hlaw hΔ := by
    rw [Subgroup.closure_le]
    intro x hx
    exact hs x hx
  have h1 := hO.card_top hlaw hΔ els hsz hel hH
  have hpos := hO.2.1
  have h2 : Nat.card (stab hlaw hΔ) = 2 ^ k := by
    rw [hΓ] at h1
    exact (Nat.eq_of_mul_eq_mul_left hpos h1).symm
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hS, h2])

end Omega

section Forest

variable [DecidableEq Lab] [Inhabited Lab]

omit [DecidableEq Lab] in
theorem ForestSpec.reach_root {act : Array ℕ → Lab → Lab} {lbl : Array Lab}
    {letters : Array (Array ℕ)} {F : ForestData} (S : Subgroup Γ)
    (hlet : ∀ l < letters.size, ∃ s ∈ S, letters[l]! = (tab n s).toArray)
    {valid : Lab → Prop} (A : LabAct Lab) (hA : A.act = act)
    (hlaw : LabLawful Γ n A valid) (hvalid : ∀ i < lbl.size, valid lbl[i]!)
    (hF : ForestSpec act lbl letters F) :
    ∀ d i, F.fdep[i]! = d → i < lbl.size →
      ∃ s ∈ S, F.froot[i]! < lbl.size ∧ F.fdep[F.froot[i]!]! = 0 ∧
        lbl[i]! = act (tab n s).toArray lbl[F.froot[i]!]! := by
  intro d
  induction d with
  | zero =>
    intro i hi hiN
    rcases hF i hiN with ⟨-, hr⟩ | ⟨hpl, hdep, -⟩
    · refine ⟨1, S.one_mem, by rw [hr]; exact hiN, by rw [hr]; exact hi, ?_⟩
      rw [hr, ← hA, hlaw.act_one (hvalid i hiN)]
    · omega
  | succ d ih =>
    intro i hi hiN
    rcases hF i hiN with ⟨h0, -⟩ | ⟨hpl, hdep, hfl, heq, hroot⟩
    · rw [h0] at hi; exact absurd hi (by omega)
    · obtain ⟨s, hs, hr, hr0, hrs⟩ := ih (F.fpar[i]!) (by omega) hpl
      obtain ⟨s', hs', hlt⟩ := hlet (F.fl[i]!) hfl
      refine ⟨s' * s, S.mul_mem hs' hs, by rw [hroot]; exact hr, by rw [hroot]; exact hr0, ?_⟩
      rw [hroot, heq, hrs, hlt, ← hA]
      exact (hlaw.act_mul s' s (hvalid _ hr)).symm

end Forest

theorem act_evalElt (els : Array Γ) (tabs : Array (Array ℕ))
    (hel : ∀ l < els.size, tabs.getD l #[] = (tab n (els.getD l 1)).toArray) (w : List ℕ)
    (hw : ∀ l ∈ w, l < els.size) : ∀ p < n, act n (evalElt els w) p = wordImg tabs w p := by
  induction w with
  | nil => intro p hp; simp [evalElt_nil, wordImg, act_one hp]
  | cons l w ih =>
    intro p hp
    have hl : l < els.size := hw l List.mem_cons_self
    have h1 := ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) p hp
    rw [evalElt_cons, act_mul _ _ hp]
    simp only [wordImg, List.foldr_cons]
    have h2 : List.foldr (fun l q => (tabs.getD l #[]).getD q 0) p w = act n (evalElt els w) p :=
      h1.symm
    rw [h2, hel l hl]
    exact (img_tab _ _).symm

theorem wordTabA_eq (els : Array Γ) (tabs : Array (Array ℕ))
    (hel : ∀ l < els.size, tabs.getD l #[] = (tab n (els.getD l 1)).toArray) (w : List ℕ)
    (hw : ∀ l ∈ w, l < els.size) :
    wordTabA tabs n w = (tab n (evalElt els w)).toArray := by
  apply Array.ext
  · simp [wordTabA, tab]
  · intro p h1 h2
    have hp : p < n := by simpa [wordTabA] using h1
    simp only [wordTabA, Array.getElem_map, Array.getElem_range]
    rw [← act_evalElt els tabs hel w hw p hp]
    have hlen : p < (tab n (evalElt els w)).length := by simpa using h2
    simp [act, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]

theorem eq_of_act_eq_base {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) {x y : Γ}
    (h : ∀ b ∈ B, act n x b = act n y b) : x = y := by
  have h1 : x⁻¹ * y = 1 := by
    apply hbase
    intro b hb
    rw [act_mul _ _ (hB b hb), ← h b hb, ← act_mul _ _ (hB b hb), inv_mul_cancel,
      act_one (hB b hb)]
  exact inv_mul_eq_one.mp h1


@[expose] def memberOrTop (J : ℕ) (Y : ℕ → Subgroup Γ) (j : ℕ) : Subgroup Γ :=
  if j < J then Y j else ⊤

theorem family_complete [Finite Γ] {S : Subgroup Γ} (J : ℕ) (Y : ℕ → Subgroup Γ) (R : ℕ)
    (rep : ℕ → Γ) (jc : ℕ → ℕ) (hSY : ∀ j < J, S ≤ Y j) (hY0 : 0 < J ∧ Y 0 = S)
    (hcover : ∀ g : Γ, ∃ c < R, ∃ s ∈ S, ∃ t ∈ S, g = s * rep c * t)
    (hatom : ∀ c < R, jc c ≤ J ∧ rep c ∈ memberOrTop J Y (jc c) ∧
      ∀ Z : Subgroup Γ, S ≤ Z → rep c ∈ Z → memberOrTop J Y (jc c) ≤ Z)
    (hjoin : ∀ j < J, ∀ j' ≤ J, ∃ j'' ≤ J, memberOrTop J Y j ⊔ memberOrTop J Y j' =
      memberOrTop J Y j'') :
    ∀ Z : Subgroup Γ, S ≤ Z → ∃ j ≤ J, Z = memberOrTop J Y j := by
  have hS0 : S = memberOrTop J Y 0 := by
    simp [memberOrTop, hY0.1, hY0.2]
  have adj : ∀ j ≤ J, ∀ g : Γ, ∃ j' ≤ J,
      Subgroup.closure (↑(memberOrTop J Y j) ∪ {g}) = memberOrTop J Y j' := by
    intro j hj g
    by_cases hjJ : j < J
    · obtain ⟨c, hc, s, hs, t, ht, rfl⟩ := hcover g
      obtain ⟨hjcle, hrep, hmin⟩ := hatom c hc
      have hSj : S ≤ Y j := hSY j hjJ
      have hmj : memberOrTop J Y j = Y j := by simp [memberOrTop, hjJ]
      obtain ⟨j', hj', hj'e⟩ := hjoin j hjJ (jc c) hjcle
      refine ⟨j', hj', ?_⟩
      rw [← hj'e, hmj]
      have hMj : Y j ≤ Subgroup.closure (↑(Y j) ∪ {s * rep c * t}) := fun x hx =>
        Subgroup.subset_closure (Or.inl hx)
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro x (hx | hx)
        · exact Subgroup.mem_sup_left hx
        · rw [Set.mem_singleton_iff] at hx
          subst hx
          have h1 : s ∈ Y j ⊔ memberOrTop J Y (jc c) := Subgroup.mem_sup_left (hSj hs)
          have h2 : rep c ∈ Y j ⊔ memberOrTop J Y (jc c) := Subgroup.mem_sup_right hrep
          have h3 : t ∈ Y j ⊔ memberOrTop J Y (jc c) := Subgroup.mem_sup_left (hSj ht)
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h3
      · apply sup_le hMj
        apply hmin _ (le_trans hSj hMj)
        have hg : s * rep c * t ∈ Subgroup.closure (↑(Y j) ∪ {s * rep c * t}) :=
          Subgroup.subset_closure (Or.inr rfl)
        have hs' : s⁻¹ ∈ Subgroup.closure (↑(Y j) ∪ {s * rep c * t}) :=
          Subgroup.inv_mem _ (hMj (hSj hs))
        have ht' : t⁻¹ ∈ Subgroup.closure (↑(Y j) ∪ {s * rep c * t}) :=
          Subgroup.inv_mem _ (hMj (hSj ht))
        have := Subgroup.mul_mem _ (Subgroup.mul_mem _ hs' hg) ht'
        have e : s⁻¹ * (s * rep c * t) * t⁻¹ = rep c := by group
        rw [e] at this
        exact this
    · have hjJ' : j = J := by omega
      refine ⟨J, le_rfl, ?_⟩
      have : memberOrTop J Y J = ⊤ := by simp [memberOrTop]
      rw [hjJ', this]
      exact top_le_iff.mp (fun x _ => Subgroup.subset_closure (Or.inl (Subgroup.mem_top x)))
  intro Z hSZ
  have hfin : (Z : Set Γ).Finite := Set.toFinite _
  obtain ⟨l, hl⟩ : ∃ l : List Γ, ∀ x, x ∈ l ↔ x ∈ Z :=
    ⟨hfin.toFinset.toList, fun x => by simp⟩
  have key : ∀ l' : List Γ, (∀ x ∈ l', x ∈ Z) →
      ∃ j ≤ J, Subgroup.closure ({x | x ∈ S} ∪ {x | x ∈ l'}) = memberOrTop J Y j := by
    intro l'
    induction l' with
    | nil =>
      intro _
      refine ⟨0, Nat.zero_le _, ?_⟩
      rw [← hS0]
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro x (hx | hx)
        · exact hx
        · exact absurd hx (by simp)
      · intro x hx
        exact Subgroup.subset_closure (Or.inl hx)
    | cons g l' ih =>
      intro hZ
      obtain ⟨j, hj, hje⟩ := ih (fun x hx => hZ x (List.mem_cons_of_mem _ hx))
      obtain ⟨j', hj', hj'e⟩ := adj j hj g
      refine ⟨j', hj', ?_⟩
      rw [← hj'e, ← hje]
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro x (hx | hx)
        · exact Subgroup.subset_closure (Or.inl (Subgroup.subset_closure (Or.inl hx)))
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact Subgroup.subset_closure (Or.inr rfl)
          · exact Subgroup.subset_closure (Or.inl (Subgroup.subset_closure (Or.inr hx)))
      · rw [Subgroup.closure_le]
        rintro x (hx | hx)
        · have : x ∈ Subgroup.closure ({x | x ∈ S} ∪ {x | x ∈ g :: l'}) := by
            have : x ∈ Subgroup.closure ({x | x ∈ S} ∪ {x | x ∈ l'}) := hx
            exact Subgroup.closure_mono (Set.union_subset_union_right _
              (fun y hy => List.mem_cons_of_mem _ hy)) this
          exact this
        · rw [Set.mem_singleton_iff] at hx
          subst hx
          exact Subgroup.subset_closure (Or.inr List.mem_cons_self)
  obtain ⟨j, hj, hje⟩ := key l (fun x hx => (hl x).mp hx)
  refine ⟨j, hj, ?_⟩
  rw [← hje]
  apply le_antisymm
  · intro x hx
    exact Subgroup.subset_closure (Or.inr ((hl x).mpr hx))
  · rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · exact hSZ hx
    · exact (hl x).mp hx

end CFSG.QuasithinUnique.Ch1.SporLat
