module

public import CFSG.Sporadic.SmallOddCore.CentSpec
public import Certificates.Data.CFSGNative.PropA.Check

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Equiv Subgroup CFSG.Sporadic CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.M12Std.PropA.Native

variable {n : ℕ}

structure Enum (n : ℕ) (E : List Table) (S : Set (Perm (Fin n))) : Prop where
  forall₂ : ∃ ps : List (Perm (Fin n)),
    List.Forall₂ (Th.Rep n) E ps ∧ ps.Nodup ∧ ∀ g, g ∈ ps ↔ g ∈ S

theorem Enum.card {E : List Table} {S : Set (Perm (Fin n))} (h : Enum n E S) :
    Nat.card S = E.length := by
  obtain ⟨ps, h2, hnd, hmem⟩ := h
  have hS : S = (ps.toFinset : Set (Perm (Fin n))) := by
    ext g
    rw [← hmem g]
    simp [List.mem_toFinset]
  rw [hS, Nat.card_coe_set_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd,
    h2.length_eq]

private theorem forall₂_all_iff {E : List Table} {ps : List (Perm (Fin n))}
    {f : Table → Bool} {P : Perm (Fin n) → Prop}
    (hf : ∀ T g, Th.Rep n T g → (f T = true ↔ P g))
    (h : List.Forall₂ (Th.Rep n) E ps) :
    (∀ T ∈ E, f T = true) ↔ ∀ g ∈ ps, P g := by
  induction h with
  | nil => simp
  | cons hT _ ih =>
    simp only [List.mem_cons, forall_eq_or_imp]
    rw [hf _ _ hT, ih]

private theorem forall₂_any_iff {E : List Table} {ps : List (Perm (Fin n))}
    {f : Table → Bool} {P : Perm (Fin n) → Prop}
    (hf : ∀ T g, Th.Rep n T g → (f T = true ↔ P g))
    (h : List.Forall₂ (Th.Rep n) E ps) :
    (∃ T ∈ E, f T = true) ↔ ∃ g ∈ ps, P g := by
  induction h with
  | nil => simp
  | cons hT _ ih =>
    simp only [List.mem_cons, exists_eq_or_imp]
    rw [hf _ _ hT, ih]

private theorem forall₂_filter {E : List Table} {ps : List (Perm (Fin n))}
    {f : Table → Bool} {P : Perm (Fin n) → Prop} [DecidablePred P]
    (hf : ∀ T g, Th.Rep n T g → (f T = true ↔ P g))
    (h : List.Forall₂ (Th.Rep n) E ps) :
    List.Forall₂ (Th.Rep n) (E.filter f) (ps.filter fun g => decide (P g)) :=
  List.rel_filter (R := Th.Rep n) (p := f) (q := fun g => decide (P g))
    (fun T g hT => (hf T g hT).trans (iff_of_eq (decide_eq_true_eq (p := P g))).symm) h

theorem Enum.all_iff {E : List Table} {S : Set (Perm (Fin n))} (h : Enum n E S)
    {f : Table → Bool} {P : Perm (Fin n) → Prop}
    (hf : ∀ T g, Th.Rep n T g → (f T = true ↔ P g)) :
    E.all f = true ↔ ∀ g ∈ S, P g := by
  obtain ⟨ps, h2, -, hmem⟩ := h
  rw [List.all_eq_true, forall₂_all_iff hf h2]
  constructor
  · intro h g hg; exact h g ((hmem g).2 hg)
  · intro h g hg; exact h g ((hmem g).1 hg)

theorem Enum.any_iff {E : List Table} {S : Set (Perm (Fin n))} (h : Enum n E S)
    {f : Table → Bool} {P : Perm (Fin n) → Prop}
    (hf : ∀ T g, Th.Rep n T g → (f T = true ↔ P g)) :
    E.any f = true ↔ ∃ g ∈ S, P g := by
  obtain ⟨ps, h2, -, hmem⟩ := h
  rw [List.any_eq_true, forall₂_any_iff hf h2]
  constructor
  · rintro ⟨g, hg, hP⟩; exact ⟨g, (hmem g).1 hg, hP⟩
  · rintro ⟨g, hg, hP⟩; exact ⟨g, (hmem g).2 hg, hP⟩

theorem Enum.filter {E : List Table} {S : Set (Perm (Fin n))} (h : Enum n E S)
    {f : Table → Bool} {P : Perm (Fin n) → Prop}
    (hf : ∀ T g, Th.Rep n T g → (f T = true ↔ P g)) :
    Enum n (E.filter f) {g | g ∈ S ∧ P g} := by
  classical
  obtain ⟨ps, h2, hnd, hmem⟩ := h
  refine ⟨ps.filter fun g => decide (P g), forall₂_filter hf h2, hnd.filter _, ?_⟩
  intro g
  rw [List.mem_filter, hmem g, decide_eq_true_eq]
  rfl

theorem Enum.card_array {A : Array Table} {S : Set (Perm (Fin n))} (h : Enum n A.toList S) :
    Nat.card S = A.size := by
  rw [Enum.card h, Array.length_toList]

theorem Enum.all_iff_array {A : Array Table} {S : Set (Perm (Fin n))} (h : Enum n A.toList S)
    {f : Table → Bool} {P : Perm (Fin n) → Prop}
    (hf : ∀ T g, Th.Rep n T g → (f T = true ↔ P g)) :
    A.all f = true ↔ ∀ g ∈ S, P g := by
  rw [← Array.all_toList]
  exact Enum.all_iff h hf

theorem Enum.any_iff_array {A : Array Table} {S : Set (Perm (Fin n))} (h : Enum n A.toList S)
    {f : Table → Bool} {P : Perm (Fin n) → Prop}
    (hf : ∀ T g, Th.Rep n T g → (f T = true ↔ P g)) :
    A.any f = true ↔ ∃ g ∈ S, P g := by
  rw [← Array.any_toList]
  exact Enum.any_iff h hf

theorem Enum.filter_array {A : Array Table} {S : Set (Perm (Fin n))} (h : Enum n A.toList S)
    {f : Table → Bool} {P : Perm (Fin n) → Prop}
    (hf : ∀ T g, Th.Rep n T g → (f T = true ↔ P g)) :
    Enum n (A.filter f).toList {g | g ∈ S ∧ P g} := by
  rw [Array.toList_filter]
  exact Enum.filter h hf

theorem Enum.memT_iff {A : Array Table} {S : Set (Perm (Fin n))} (h : Enum n A.toList S)
    {x : Table} {g : Perm (Fin n)} (hx : Th.Rep n x g) :
    memT n A x = true ↔ g ∈ S := by
  rw [memT]
  have hiff := Enum.any_iff_array h (f := tblEq n x) (P := fun g' => g = g')
    (fun T g' hT => tblEq_iff_eq hx hT)
  rw [hiff]
  constructor
  · rintro ⟨g', hg', rfl⟩; exact hg'
  · intro hg; exact ⟨g, hg, rfl⟩

theorem commP_iff {S T : Table} {g h : Perm (Fin n)} (hS : Th.Rep n S g) (hT : Th.Rep n T h) :
    commP n S T = true ↔ g * h = h * g :=
  commTT_iff hS hT

theorem involP_iff (hn : n < 2 ^ 32) {T : Table} {g : Perm (Fin n)} (hT : Th.Rep n T g) :
    involP n T = true ↔ orderOf g = 2 :=
  ⟨orderOf_eq_two_of_involOK hn hT, involOK_of_orderOf hn hT⟩

theorem rep_commutT {a b : Table} {g h : Perm (Fin n)} (ha : Th.Rep n a g) (hb : Th.Rep n b h)
    (hai : invOK n a (invT n a) = true) (hbi : invOK n b (invT n b) = true) :
    Th.Rep n (commutT n a b) (g * h * g⁻¹ * h⁻¹) := by
  have hcomp := Th.Rep.compT (Th.Rep.compT ha hb)
    (Th.Rep.compT (rep_invT ha hai) (rep_invT hb hbi))
  rwa [show (g * h) * (g⁻¹ * h⁻¹) = g * h * g⁻¹ * h⁻¹ by simp only [mul_assoc]] at hcomp

theorem gensP_spec {gs : Array Table} (h : gensP n gs = true) :
    ∀ x ∈ gs, permOK n x = true ∧ invOK n x (invT n x) = true := by
  rw [gensP, Array.all_eq_true'] at h
  intro x hx
  have hx' := h x hx
  rw [Bool.and_eq_true_iff] at hx'
  exact hx'

theorem closure_tp_eq {gs : Array Table} {gg : ℕ → Perm (Fin n)}
    (hrep : ∀ l < gs.size, Th.Rep n gs[l]! (gg l)) (hp : ∀ x ∈ gs, permOK n x = true) :
    closure (tp n '' {x | x ∈ gs}) = closure (gg '' {l | l < gs.size}) := by
  have key : ∀ l < gs.size, tp n gs[l]! = gg l := fun l hl =>
    rep_unique (rep_tp (hp gs[l]! (getElem!_mem_array hl))) (hrep l hl)
  apply le_antisymm
  · rw [closure_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨l, hl, rfl⟩ := Array.getElem_of_mem hx
    rw [← getElem!_pos gs l hl, key l hl]
    exact subset_closure ⟨l, hl, rfl⟩
  · rw [closure_le]
    rintro _ ⟨l, hl, rfl⟩
    exact subset_closure ⟨gs[l]!, getElem!_mem_array hl, key l hl⟩

theorem closedOK_of_closedHOK {gens L : Array Table} (h : closedHOK n gens L = true) :
    closedOK n gens L = true := by
  rw [closedOK, Array.all_eq_true']
  simp only [closedHOK] at h
  rw [Array.all_eq_true'] at h
  intro x hx
  rw [Array.all_eq_true']
  intro g hg
  have hxg := h x hx
  rw [Array.all_eq_true'] at hxg
  have hxg' := hxg g hg
  rw [memT, Array.any_eq_true']
  split at hxg'
  · rename_i i _
    rw [Bool.and_eq_true_iff, decide_eq_true_eq, tblEq_iff] at hxg'
    exact ⟨L[i]!, getElem!_mem_array hxg'.1, by
      rw [tblEq_iff]
      intro j hj
      exact (hxg'.2 j hj).symm⟩
  · exact Bool.noConfusion hxg'

theorem enumP_spec (hn : n < 2 ^ 32) {cap N : ℕ} {gs : Array Table}
    (h : enumP n cap gs N = true) :
    Enum n (mulClosureH n gs cap).1.toList ↑(closure (tp n '' {x | x ∈ gs})) ∧
      (mulClosureH n gs cap).1.size = N := by
  rw [enumP] at h
  simp only [Bool.and_eq_true, Bool.and_eq_true_iff, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hgens, htree⟩, hclosed⟩, hdist⟩, hsize⟩ := h
  have hgspec := gensP_spec hgens
  have hg : ∀ x ∈ gs, permOK n x = true := fun x hx => (hgspec x hx).1
  have hginv : ∀ x ∈ gs, invOK n x (invT n x) = true := fun x hx => (hgspec x hx).2
  obtain ⟨hErep, hcov, -⟩ :=
    enum_spec hn hg hginv htree (closedOK_of_closedHOK hclosed) hdist
  have hE : ∀ k < (mulClosureH n gs cap).1.size,
      Th.Rep n (mulClosureH n gs cap).1[k]! (tablePerm n (mulClosureH n gs cap).1[k]!) :=
    fun k hk => (hErep k hk).1
  refine ⟨⟨(mulClosureH n gs cap).1.toList.map (tablePerm n), ?_, ?_, ?_⟩, hsize⟩
  · exact forall₂_tablePerm hE
  · exact nodup_of_hkeysDistinct (forall₂_tablePerm hE) hdist
  · intro g
    constructor
    · intro hgm
      obtain ⟨k, hk, hgk⟩ := mem_map_tablePerm hE hgm
      rw [hgk]
      exact (hErep k hk).2
    · intro hg
      obtain ⟨k, hk, hrep⟩ := hcov g hg
      exact List.mem_map.mpr ⟨(mulClosureH n gs cap).1[k]!,
        Array.mem_toList_iff.mpr (getElem!_mem_array hk), tablePerm_eq hrep⟩

private theorem exists_mem_of_forall₂ {E : List Table} {ps : List (Perm (Fin n))}
    (h : List.Forall₂ (Th.Rep n) E ps) {T : Table} (hT : T ∈ E) : ∃ g ∈ ps, Th.Rep n T g := by
  induction h with
  | nil => exact absurd hT (by simp)
  | cons hab _ ih =>
    rcases List.mem_cons.mp hT with rfl | hT
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨g, hg, hrep⟩ := ih hT
      exact ⟨g, List.mem_cons_of_mem _ hg, hrep⟩

private theorem exists_mem_of_forall₂_right {E : List Table} {ps : List (Perm (Fin n))}
    (h : List.Forall₂ (Th.Rep n) E ps) {g : Perm (Fin n)} (hg : g ∈ ps) :
    ∃ T ∈ E, Th.Rep n T g := by
  induction h with
  | nil => exact absurd hg (by simp)
  | cons hab _ ih =>
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨T, hT, hrep⟩ := ih hg
      exact ⟨T, List.mem_cons_of_mem _ hT, hrep⟩

theorem Enum.mem_of_rep {E : List Table} {S : Set (Perm (Fin n))} (h : Enum n E S) {T : Table}
    (hT : T ∈ E) : ∃ g ∈ S, Th.Rep n T g := by
  obtain ⟨ps, h2, -, hmem⟩ := h
  obtain ⟨g, hg, hrep⟩ := exists_mem_of_forall₂ h2 hT
  exact ⟨g, (hmem g).1 hg, hrep⟩

theorem Enum.rep_of_mem {E : List Table} {S : Set (Perm (Fin n))} (h : Enum n E S)
    {g : Perm (Fin n)} (hg : g ∈ S) : ∃ T ∈ E, Th.Rep n T g := by
  obtain ⟨ps, h2, -, hmem⟩ := h
  exact exists_mem_of_forall₂_right h2 ((hmem g).2 hg)

theorem Enum.all_imp_array {A : Array Table} {S : Set (Perm (Fin n))} (h : Enum n A.toList S)
    {f : Table → Bool} {P : Perm (Fin n) → Prop}
    (hf : ∀ T g, Th.Rep n T g → f T = true → P g) (hall : A.all f = true) :
    ∀ g ∈ S, P g := by
  intro g hg
  obtain ⟨T, hT, hrep⟩ := Enum.rep_of_mem h hg
  rw [Array.all_eq_true'] at hall
  exact hf T g hrep (hall T (Array.mem_toList_iff.mp hT))

theorem Enum.any_imp_array {A : Array Table} {S : Set (Perm (Fin n))} (h : Enum n A.toList S)
    {f : Table → Bool} {P : Perm (Fin n) → Prop}
    (hf : ∀ T g, Th.Rep n T g → f T = true → P g) (hany : A.any f = true) :
    ∃ g ∈ S, P g := by
  rw [Array.any_eq_true'] at hany
  obtain ⟨T, hT, hfT⟩ := hany
  obtain ⟨g, hg, hrep⟩ := Enum.mem_of_rep h (Array.mem_toList_iff.mpr hT)
  exact ⟨g, hg, hf T g hrep hfT⟩

end CFSG.EvenSporadicStandard.M12Std.PropA
