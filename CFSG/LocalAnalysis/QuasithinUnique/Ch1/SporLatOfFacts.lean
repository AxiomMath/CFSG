module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatLat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtThreeDLocKer

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat

open CFSG.QuasithinUnique.K1.SporadicPerm

section Enum

variable {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

theorem arr_ofFn_getElem! {α : Type} [Inhabited α] {m : ℕ} (f : Fin m → α) {i : ℕ}
    (hi : i < m) : (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi)]
  simp

@[expose] def EnumInv (act : Array ℕ → Lab → Lab) (letters : Array (Array ℕ)) (Δ : Lab)
    (labs : Set Lab) (m : ℕ) (lb : ℕ → Lab) (par via : ℕ → ℕ) : Prop :=
  0 < m ∧ lb 0 = Δ ∧ (∀ i < m, ∀ j < m, lb i = lb j → i = j) ∧ (∀ i < m, lb i ∈ labs) ∧
  ∀ i < m, 0 < i → par i < i ∧ via i < letters.size ∧ act letters[via i]! (lb (par i)) = lb i

variable {act : Array ℕ → Lab → Lab} {letters : Array (Array ℕ)} {Δ : Lab} {labs : Set Lab}

theorem EnumInv.step {m : ℕ} {lb : ℕ → Lab} {par via : ℕ → ℕ}
    (h : EnumInv act letters Δ labs m lb par via)
    (hcl : ∀ x ∈ labs, ∀ l < letters.size, act letters[l]! x ∈ labs) {l i : ℕ}
    (hl : l < letters.size) (hi : i < m) (hnew : ∀ j < m, lb j ≠ act letters[l]! (lb i)) :
    EnumInv act letters Δ labs (m + 1) (fun j => if j = m then act letters[l]! (lb i) else lb j)
      (fun j => if j = m then i else par j) (fun j => if j = m then l else via j) := by
  obtain ⟨hm, h0, hinj, hlabs, htree⟩ := h
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · simp only
    rw [if_neg (by omega)]
    exact h0
  · intro a ha b hb hab
    simp only at hab
    by_cases ham : a = m <;> by_cases hbm : b = m
    · omega
    · rw [if_pos ham, if_neg hbm] at hab
      exact absurd hab.symm (hnew b (by omega))
    · rw [if_neg ham, if_pos hbm] at hab
      exact absurd hab (hnew a (by omega))
    · rw [if_neg ham, if_neg hbm] at hab
      exact hinj a (by omega) b (by omega) hab
  · intro a ha
    simp only
    by_cases ham : a = m
    · rw [if_pos ham]; exact hcl _ (hlabs i hi) l hl
    · rw [if_neg ham]; exact hlabs a (by omega)
  · intro a ha hpos
    simp only
    by_cases ham : a = m
    · rw [if_pos ham, if_pos ham, if_pos ham, if_neg (by omega)]
      exact ⟨by omega, hl, rfl⟩
    · obtain ⟨h1, h2, h3⟩ := htree a (by omega) hpos
      rw [if_neg ham, if_neg ham, if_neg ham, if_neg (by omega)]
      exact ⟨h1, h2, h3⟩

theorem EnumInv.le_card (hfin : labs.Finite) {m : ℕ} {lb : ℕ → Lab} {par via : ℕ → ℕ}
    (h : EnumInv act letters Δ labs m lb par via) : m ≤ hfin.toFinset.card := by
  obtain ⟨-, -, hinj, hlabs, -⟩ := h
  have hc : ((Finset.range m).image lb).card = m := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    exact hinj a (by simpa using ha) b (by simpa using hb) hab
  rw [← hc]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  simpa using hlabs a (by simpa using ha)

theorem EnumInv.closed (hfin : labs.Finite)
    (hcl : ∀ x ∈ labs, ∀ l < letters.size, act letters[l]! x ∈ labs) :
    ∀ e m lb par via, EnumInv act letters Δ labs m lb par via → hfin.toFinset.card ≤ m + e →
      ∃ m lb par via, EnumInv act letters Δ labs m lb par via ∧
        ∀ l < letters.size, ∀ i < m, ∃ j < m, lb j = act letters[l]! (lb i) := by
  intro e
  induction e with
  | zero =>
    intro m lb par via h hb
    refine ⟨m, lb, par, via, h, ?_⟩
    intro l hl i hi
    by_contra hne
    push Not at hne
    have := (h.step hcl hl hi hne).le_card hfin
    omega
  | succ e ih =>
    intro m lb par via h hb
    by_cases hc : ∀ l < letters.size, ∀ i < m, ∃ j < m, lb j = act letters[l]! (lb i)
    · exact ⟨m, lb, par, via, h, hc⟩
    · push Not at hc
      obtain ⟨l, hl, i, hi, hne⟩ := hc
      exact ih _ _ _ _ (h.step hcl hl hi hne) (by omega)

theorem exists_omegaSpec (hfin : labs.Finite) (hΔ : Δ ∈ labs)
    (hcl : ∀ x ∈ labs, ∀ l < letters.size, act letters[l]! x ∈ labs) :
    ∃ O : OmegaData Lab, OmegaSpec act letters Δ O := by
  have h1 : EnumInv act letters Δ labs 1 (fun _ => Δ) (fun _ => 0) (fun _ => 0) :=
    ⟨by omega, rfl, fun i hi j hj _ => by omega, fun _ _ => hΔ, fun i hi hpos => by omega⟩
  obtain ⟨m, lb, par, via, ⟨hm, h0, hinj, -, htree⟩, hclo⟩ :=
    EnumInv.closed hfin hcl hfin.toFinset.card 1 _ _ _ h1 (by omega)
  choose f hf hfe using hclo
  refine ⟨{ lbl := Array.ofFn (n := m) fun i => lb i,
            pn := Array.ofFn (n := letters.size) fun l =>
              Array.ofFn (n := m) fun i => f l l.2 i i.2,
            par := Array.ofFn (n := m) fun i => par i,
            via := Array.ofFn (n := m) fun i => via i }, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [arr_ofFn_getElem! _ hm]
    exact h0
  · simpa using hm
  · intro l hl i hi
    have hi' : i < m := by simpa using hi
    dsimp only
    rw [arr_ofFn_getElem! _ hl, arr_ofFn_getElem! _ hi']
    refine ⟨by simpa using hf l hl i hi', ?_⟩
    rw [arr_ofFn_getElem! _ (hf l hl i hi'), arr_ofFn_getElem! _ hi']
    exact hfe l hl i hi'
  · intro i hi hpos
    have hi' : i < m := by simpa using hi
    obtain ⟨h1, h2, h3⟩ := htree i hi' hpos
    dsimp only
    rw [arr_ofFn_getElem! _ hi', arr_ofFn_getElem! _ hi']
    refine ⟨h1, h2, ?_⟩
    rw [arr_ofFn_getElem! _ h2, arr_ofFn_getElem! _ (by omega : par i < m)]
    exact hinj _ (hf _ h2 _ (by omega)) i hi' (by rw [hfe, h3])
  · apply CFSG.Quasithin.GoldD3.distinctB_of_nodup
    rw [Array.toList_ofFn, List.nodup_ofFn]
    intro a b hab
    exact Fin.ext (hinj a a.2 b b.2 hab)

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem exists_omegaSpec_lab {A : LabAct Lab} {valid : Lab → Prop}
    (hlaw : LabLawful Γ n A valid) (hΔ : valid Δ) (els : Array Γ)
    (hel : ∀ l < letters.size, letters[l]! = (tab n (els.getD l 1)).toArray) :
    ∃ O : OmegaData Lab, OmegaSpec A.act letters Δ O := by
  apply exists_omegaSpec (Set.finite_range (lab n A Δ)) ⟨1, lab_one hlaw hΔ⟩
  rintro x ⟨g, rfl⟩ l hl
  exact ⟨els.getD l 1 * g, by rw [lab_mul hlaw hΔ, hel l hl]⟩

end Enum

@[expose] def trivForest (m : ℕ) : ForestData where
  fpar := Array.replicate m 0
  fl := Array.replicate m 0
  fdep := Array.replicate m 0
  froot := Array.range m

theorem trivForest_fdep {m i : ℕ} (hi : i < m) : (trivForest m).fdep[i]! = 0 := by
  rw [getElem!_pos _ i (by simpa [trivForest] using hi)]
  simp [trivForest]

theorem trivForest_spec {Lab : Type} [Inhabited Lab] (act : Array ℕ → Lab → Lab)
    (lbl : Array Lab) (letters : Array (Array ℕ)) :
    ForestSpec act lbl letters (trivForest lbl.size) := by
  intro i hi
  left
  refine ⟨trivForest_fdep hi, ?_⟩
  rw [getElem!_pos _ i (by simpa [trivForest] using hi)]
  simp [trivForest]

section Facts

structure LatFacts (Γ : Type) [Group Γ] [Finite Γ] (n : ℕ) [MulAction Γ (Fin n)] (Lab : Type)
    [DecidableEq Lab] [Hashable Lab] [Inhabited Lab] where
  A : LabAct Lab
  valid : Lab → Prop
  hlaw : LabLawful Γ n A valid
  Δ : Lab
  hΔ : valid Δ
  a : Γ
  b : Γ
  ta : Array ℕ
  tb : Array ℕ
  ha : (tab n a).toArray = ta
  hb : (tab n b).toArray = tb
  gen : Subgroup.closure ({a, b} : Set Γ) = ⊤
  D0 : LatData Lab
  sg : List Γ
  k : ℕ
  hsg : genTabs n sg = D0.sTabs
  hSk : Nat.card (Subgroup.closure {x | x ∈ sg}) = 2 ^ k
  N : ℕ
  hΓ : Nat.card Γ = N * 2 ^ k
  hM : MembersOK A.act n ta tb Δ D0
  hstab : ∀ g : Γ, lab n A Δ g = Δ ↔ g ∈ Subgroup.closure {x | x ∈ sg}
  hcomp : ∀ Z : Subgroup Γ, Subgroup.closure {x | x ∈ sg} ≤ Z → ∃ j ≤ D0.mw.size,
    Z = memberOrTop D0.mw.size
      (fun j => Subgroup.closure {x | x ∈ sg ++ (D0.mw[j]!).map (wordElt a b)}) j

namespace LatFacts

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab] (F : LatFacts Γ n Lab)

@[expose] def S : Subgroup Γ := stab F.hlaw F.hΔ

@[expose] def J : ℕ := F.D0.mw.size

@[expose] def gens (j : ℕ) : List Γ := (F.D0.mw[j]!).map (wordElt F.a F.b)

@[expose] def Y (j : ℕ) : Subgroup Γ := Subgroup.closure {x | x ∈ F.sg ++ F.gens j}

theorem hSeq : Subgroup.closure {x | x ∈ F.sg} = F.S :=
  Subgroup.ext fun g => (F.hstab g).symm

theorem S_le (X : List Γ) : F.S ≤ Subgroup.closure {x | x ∈ F.sg ++ X} := by
  rw [← F.hSeq]
  apply Subgroup.closure_mono
  intro x hx
  exact List.mem_append_left _ hx

theorem sg_le (X : List Γ) :
    Subgroup.closure {x | x ∈ F.sg} ≤ Subgroup.closure {x | x ∈ F.sg ++ X} := by
  rw [F.hSeq]; exact F.S_le X

theorem S_card : Nat.card F.S = 2 ^ F.k := by
  rw [← F.hSeq]; exact F.hSk

theorem card_S_pos : 0 < Nat.card F.S := Nat.card_pos

theorem hel0 : ∀ l < (#[F.ta, F.tb] : Array (Array ℕ)).size, (#[F.ta, F.tb] : Array (Array ℕ))[l]! =
    (tab n ((#[F.a, F.b] : Array Γ).getD l 1)).toArray := by
  intro l hl
  have : l < 2 := hl
  interval_cases l
  · simpa using F.ha.symm
  · simpa using F.hb.symm

theorem hel0' : ∀ l < (#[F.a, F.b] : Array Γ).size, (#[F.ta, F.tb] : Array (Array ℕ)).getD l #[] =
    (tab n ((#[F.a, F.b] : Array Γ).getD l 1)).toArray := by
  intro l hl
  have : l < 2 := hl
  interval_cases l
  · simpa using F.ha.symm
  · simpa using F.hb.symm

theorem hgen0 : Subgroup.closure {x | x ∈ (#[F.a, F.b] : Array Γ).toList} = ⊤ := by
  have : {x | x ∈ (#[F.a, F.b] : Array Γ).toList} = ({F.a, F.b} : Set Γ) := by
    ext x; simp
  rw [this]; exact F.gen

theorem exO : ∃ O : OmegaData Lab, OmegaSpec F.A.act #[F.ta, F.tb] F.Δ O :=
  exists_omegaSpec_lab F.hlaw F.hΔ #[F.a, F.b] F.hel0

@[expose] noncomputable def O : OmegaData Lab := Classical.choose F.exO

theorem hO : OmegaSpec F.A.act #[F.ta, F.tb] F.Δ F.O := Classical.choose_spec F.exO

theorem card_top : Nat.card Γ = F.O.lbl.size * Nat.card F.S :=
  F.hO.card_top F.hlaw F.hΔ #[F.a, F.b] rfl F.hel0 F.hgen0

theorem O_size : F.O.lbl.size = F.N := by
  have h := F.card_top
  rw [F.S_card, F.hΓ] at h
  exact (Nat.eq_of_mul_eq_mul_right (by positivity) h).symm

theorem gens_tabs {j : ℕ} (hj : j < F.J) : genTabs n (F.gens j) = F.D0.mt[j]! := by
  obtain ⟨hw, hmt, -⟩ := F.hM.2.2.2.2 j hj
  rw [hmt]
  unfold gens genTabs
  rw [List.map_map]
  apply List.map_congr_left
  intro w hw'
  have := wordTabA_eq #[F.a, F.b] #[F.ta, F.tb] F.hel0' w
    (fun l hl => by simpa using hw w hw' l hl)
  simp only [Function.comp_apply]
  rw [this]
  rfl

theorem hOm {j : ℕ} (hj : j < F.J) :
    OmegaSpec F.A.act (genTabs n (F.sg ++ F.gens j)).toArray F.Δ F.D0.Om[j]! := by
  rw [genTabs_append, F.hsg, F.gens_tabs hj]; exact (F.hM.2.2.2.2 j hj).2.2

theorem Y_card {j : ℕ} (hj : j < F.J) :
    Nat.card (F.Y j) = F.D0.Om[j]!.lbl.size * Nat.card F.S :=
  (F.hOm hj).card_eq F.hlaw F.hΔ (F.sg ++ F.gens j).toArray (genTabs_size _).symm
    (genTabs_hel' _) (H := F.Y j) (by rw [LatCtx.toList_toArray_set]; rfl) (F.S_le _)

theorem Y_mem_iff {j : ℕ} (hj : j < F.J) (g : Γ) :
    g ∈ F.Y j ↔ ∃ x < F.D0.Om[j]!.lbl.size, lab n F.A F.Δ g = F.D0.Om[j]!.lbl[x]! :=
  (F.hOm hj).mem_iff F.hlaw F.hΔ (F.sg ++ F.gens j).toArray (genTabs_size _).symm
    (genTabs_hel' _) (H := F.Y j) (by rw [LatCtx.toList_toArray_set]; rfl) (F.S_le _) g

theorem member_card (j : ℕ) :
    Nat.card (memberOrTop F.J F.Y j) =
      (if j < F.J then F.D0.Om[j]!.lbl.size else F.O.lbl.size) * Nat.card F.S := by
  by_cases h : j < F.J
  · simp only [memberOrTop, h, ite_true]; exact F.Y_card h
  · simp only [memberOrTop, h, ite_false]
    rw [Subgroup.card_top]; exact F.card_top

theorem size_eq (X : List Γ) {O' : OmegaData Lab}
    (hO' : OmegaSpec F.A.act (genTabs n (F.sg ++ X)).toArray F.Δ O') {j : ℕ}
    (hZ : Subgroup.closure {x | x ∈ F.sg ++ X} = memberOrTop F.J F.Y j) :
    O'.lbl.size = if j < F.J then F.D0.Om[j]!.lbl.size else F.O.lbl.size := by
  have h1 := hO'.card_eq F.hlaw F.hΔ (F.sg ++ X).toArray (genTabs_size _).symm (genTabs_hel' _)
    (H := Subgroup.closure {x | x ∈ F.sg ++ X}) (by rw [LatCtx.toList_toArray_set]) (F.S_le X)
  rw [hZ, F.member_card] at h1
  exact (Nat.eq_of_mul_eq_mul_right F.card_S_pos h1).symm

theorem mem_label {X : List Γ} {j : ℕ}
    (hZ : Subgroup.closure {x | x ∈ F.sg ++ X} = memberOrTop F.J F.Y j) {g : Γ}
    (hg : g ∈ F.sg ++ X) (hj : j < F.J) :
    ∃ x < F.D0.Om[j]!.lbl.size, lab n F.A F.Δ g = F.D0.Om[j]!.lbl[x]! := by
  have h := Subgroup.subset_closure (k := {x | x ∈ F.sg ++ X}) hg
  rw [hZ] at h
  have e : memberOrTop F.J F.Y j = F.Y j := if_pos hj
  rw [e] at h
  exact (F.Y_mem_iff hj g).mp h

@[expose] noncomputable def rep (c : ℕ) : Γ := evalElt #[F.a, F.b] (F.O.pathWord c c)

theorem rep_lab {c : ℕ} (hc : c < F.O.lbl.size) : lab n F.A F.Δ (F.rep c) = F.O.lbl[c]! :=
  F.hO.reach F.hlaw F.hΔ #[F.a, F.b] F.hel0 c c le_rfl hc

@[expose] noncomputable def rcL (c : ℕ) : List (Array ℕ) :=
  F.D0.sTabs ++ [wordTabA #[F.ta, F.tb] n (F.O.pathWord c c)]

theorem rcL_eq {c : ℕ} (hc : c < F.O.lbl.size) : F.rcL c = genTabs n (F.sg ++ [F.rep c]) := by
  unfold rcL
  rw [genTabs_append, F.hsg]
  congr 1
  have := wordTabA_eq #[F.a, F.b] #[F.ta, F.tb] F.hel0' (F.O.pathWord c c)
    (fun l hl => by simpa using F.hO.pathWord_lt c c hc l hl)
  simp only [genTabs, List.map_cons, List.map_nil]
  rw [this]
  rfl

theorem exOc (c : Fin F.O.lbl.size) : ∃ O' : OmegaData Lab,
    OmegaSpec F.A.act (F.rcL c).toArray F.Δ O' := by
  rw [F.rcL_eq c.2]
  exact exists_omegaSpec_lab F.hlaw F.hΔ (F.sg ++ [F.rep c]).toArray (genTabs_hel' _)

theorem exCls (c : ℕ) : ∃ j ≤ F.J,
    Subgroup.closure {x | x ∈ F.sg ++ [F.rep c]} = memberOrTop F.J F.Y j :=
  F.hcomp _ (F.sg_le _)

noncomputable def atom (c : Fin F.O.lbl.size) : AtomData Lab where
  root := c
  cls := Classical.choose (F.exCls c)
  mode := 0
  oc := Classical.choose (F.exOc c)
  refPos := 0
  refWord := []
  refIdx := 0

@[expose] def jL (j j' : ℕ) : List (Array ℕ) := F.D0.sTabs ++ F.D0.mt[j]! ++ F.D0.mt[j']!

theorem jL_eq {j j' : ℕ} (hj : j < F.J) (hj' : j' < F.J) :
    F.jL j j' = genTabs n (F.sg ++ (F.gens j ++ F.gens j')) := by
  unfold jL
  rw [genTabs_append, genTabs_append, F.hsg, F.gens_tabs hj, F.gens_tabs hj', List.append_assoc]

theorem exOj (j j' : Fin F.J) : ∃ O' : OmegaData Lab,
    OmegaSpec F.A.act (F.jL j j').toArray F.Δ O' := by
  rw [F.jL_eq j.2 j'.2]
  exact exists_omegaSpec_lab F.hlaw F.hΔ (F.sg ++ (F.gens j ++ F.gens j')).toArray
    (genTabs_hel' _)

theorem exJj (j j' : ℕ) : ∃ jj ≤ F.J,
    Subgroup.closure {x | x ∈ F.sg ++ (F.gens j ++ F.gens j')} = memberOrTop F.J F.Y jj :=
  F.hcomp _ (F.sg_le _)

noncomputable def jn (j j' : Fin F.J) : JoinData Lab where
  j := j
  j' := j'
  jj := Classical.choose (F.exJj j j')
  mode := 0
  oj := Classical.choose (F.exOj j j')
  refPos := 0
  refWord := []
  refIdx := 0

noncomputable def joins : List (JoinData Lab) :=
  (List.finRange F.J).flatMap fun j => (List.finRange F.J).map fun j' => F.jn j j'

@[expose] noncomputable def D : LatData Lab where
  O := F.O
  F := trivForest F.O.lbl.size
  sTabs := F.D0.sTabs
  mw := F.D0.mw
  mt := F.D0.mt
  Om := F.D0.Om
  atoms := Array.ofFn F.atom
  joins := F.joins

theorem sfix : ∀ t ∈ F.D0.sTabs, F.A.act t F.Δ = F.Δ := by
  intro t ht
  rw [← F.hsg] at ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact (F.hstab s).mpr (Subgroup.subset_closure hs)

theorem atom_ok (c : Fin F.O.lbl.size) :
    AtomOK' F.A.act F.Δ F.D c (F.atom c) (rcLetters n F.ta F.tb F.D (F.atom c).root) := by
  have hspec := Classical.choose_spec (F.exCls c)
  have hoc := Classical.choose_spec (F.exOc c)
  refine ⟨c.2, trivForest_fdep c.2, hspec.1, Or.inl ⟨rfl, ?_, hoc, ?_⟩⟩
  · intro hj
    obtain ⟨x, hx, hxe⟩ :=
      F.mem_label hspec.2 (List.mem_append_right _ (List.mem_singleton_self _)) hj
    exact ⟨x, hx, hxe.symm.trans (F.rep_lab c.2)⟩
  · exact F.size_eq [F.rep c] (by rw [← F.rcL_eq c.2]; exact hoc) hspec.2

theorem atoms_ok : AtomsOK F.A.act n F.ta F.tb F.Δ F.D := by
  constructor
  · intro r hr
    have hr' : r < F.O.lbl.size := by
      unfold ForestData.roots at hr
      exact List.mem_range.mp (List.mem_filter.mp hr).1
    refine ⟨r, by simpa [D] using hr', ?_⟩
    change (Array.ofFn F.atom)[r]!.root = r
    rw [arr_ofFn_getElem! _ hr']
    rfl
  · intro i hi
    have hi' : i < F.O.lbl.size := by simpa [D] using hi
    change AtomOK' F.A.act F.Δ F.D i (Array.ofFn F.atom)[i]!
      (rcLetters n F.ta F.tb F.D (Array.ofFn F.atom)[i]!.root)
    rw [arr_ofFn_getElem! _ hi']
    exact F.atom_ok ⟨i, hi'⟩

theorem gensIn {X : List Γ} {j jj : ℕ}
    (hZ : Subgroup.closure {x | x ∈ F.sg ++ X} = memberOrTop F.J F.Y jj)
    (hX : ∀ g ∈ F.gens j, g ∈ F.sg ++ X) (hj : j < F.J) (hjj : jj < F.J) :
    GensIn F.A.act F.Δ F.D j jj := by
  intro t ht
  have ht' : t ∈ genTabs n (F.gens j) := by rw [F.gens_tabs hj]; exact ht
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ht'
  obtain ⟨x, hx, hxe⟩ := F.mem_label hZ (hX g hg) hjj
  exact ⟨x, hx, hxe.symm⟩

theorem jn_ok (j j' : Fin F.J) :
    JoinOK' F.A.act F.Δ F.D (F.jn j j') (joinLetters F.D (F.jn j j')) := by
  have hspec := Classical.choose_spec (F.exJj j j')
  have hoj := Classical.choose_spec (F.exOj j j')
  refine ⟨j.2, j'.2, hspec.1, Or.inl ⟨rfl, fun hjj => ⟨?_, ?_⟩, hoj, ?_⟩⟩
  · exact F.gensIn hspec.2
      (fun g hg => List.mem_append_right _ (List.mem_append_left _ hg)) j.2 hjj
  · exact F.gensIn hspec.2
      (fun g hg => List.mem_append_right _ (List.mem_append_right _ hg)) j'.2 hjj
  · exact F.size_eq _ (by rw [← F.jL_eq j.2 j'.2]; exact hoj) hspec.2

theorem joins_ok : JoinsOK F.A.act F.Δ F.D := by
  intro j hj j' hj' _
  right
  right
  refine ⟨F.jn ⟨j, hj⟩ ⟨j', hj'⟩, ?_, rfl, rfl, F.jn_ok _ _⟩
  change _ ∈ F.joins
  unfold joins
  exact List.mem_flatMap.mpr ⟨⟨j, hj⟩, List.mem_finRange _,
    List.mem_map.mpr ⟨⟨j', hj'⟩, List.mem_finRange _, rfl⟩⟩

theorem latOK : LatOK F.A.act n F.ta F.tb F.Δ F.D :=
  ⟨F.hO, F.sfix, trivForest_spec _ _ _, F.hM, F.atoms_ok, F.joins_ok⟩

@[expose] noncomputable def toCtx : LatCtx Γ n Lab where
  A := F.A
  valid := F.valid
  hlaw := F.hlaw
  Δ := F.Δ
  hΔ := F.hΔ
  a := F.a
  b := F.b
  ta := F.ta
  tb := F.tb
  ha := F.ha
  hb := F.hb
  gen := F.gen
  D := F.D
  sg := F.sg
  k := F.k
  hsg := F.hsg
  hSk := F.hSk
  hΓ := by
    change Nat.card Γ = F.O.lbl.size * 2 ^ F.k
    rw [F.O_size]; exact F.hΓ
  hD := F.latOK

end LatFacts

end Facts

section OfFacts

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

@[expose] noncomputable def LatCtx.ofFacts
    (A : LabAct Lab) (valid : Lab → Prop) (hlaw : LabLawful Γ n A valid) (Δ : Lab)
    (hΔ : valid Δ) (a b : Γ) (ta tb : Array ℕ) (ha : (tab n a).toArray = ta)
    (hb : (tab n b).toArray = tb) (gen : Subgroup.closure ({a, b} : Set Γ) = ⊤)
    (D0 : LatData Lab) (sg : List Γ) (k : ℕ) (hsg : genTabs n sg = D0.sTabs)
    (hSk : Nat.card (Subgroup.closure {x | x ∈ sg}) = 2 ^ k)
    (N : ℕ) (hΓ : Nat.card Γ = N * 2 ^ k)
    (hM : MembersOK A.act n ta tb Δ D0)
    (hstab : ∀ g : Γ, lab n A Δ g = Δ ↔ g ∈ Subgroup.closure {x | x ∈ sg})
    (hcomp : ∀ Z : Subgroup Γ, Subgroup.closure {x | x ∈ sg} ≤ Z → ∃ j ≤ D0.mw.size,
      Z = memberOrTop D0.mw.size
        (fun j => Subgroup.closure {x | x ∈ sg ++ (D0.mw[j]!).map (wordElt a b)}) j) :
    LatCtx Γ n Lab :=
  LatFacts.toCtx
    { A := A, valid := valid, hlaw := hlaw, Δ := Δ, hΔ := hΔ, a := a, b := b, ta := ta, tb := tb,
      ha := ha, hb := hb, gen := gen, D0 := D0, sg := sg, k := k, hsg := hsg, hSk := hSk, N := N,
      hΓ := hΓ, hM := hM, hstab := hstab, hcomp := hcomp }

variable (A : LabAct Lab) (valid : Lab → Prop) (hlaw : LabLawful Γ n A valid) (Δ : Lab)
    (hΔ : valid Δ) (a b : Γ) (ta tb : Array ℕ) (ha : (tab n a).toArray = ta)
    (hb : (tab n b).toArray = tb) (gen : Subgroup.closure ({a, b} : Set Γ) = ⊤)
    (D0 : LatData Lab) (sg : List Γ) (k : ℕ) (hsg : genTabs n sg = D0.sTabs)
    (hSk : Nat.card (Subgroup.closure {x | x ∈ sg}) = 2 ^ k)
    (N : ℕ) (hΓ : Nat.card Γ = N * 2 ^ k)
    (hM : MembersOK A.act n ta tb Δ D0)
    (hstab : ∀ g : Γ, lab n A Δ g = Δ ↔ g ∈ Subgroup.closure {x | x ∈ sg})
    (hcomp : ∀ Z : Subgroup Γ, Subgroup.closure {x | x ∈ sg} ≤ Z → ∃ j ≤ D0.mw.size,
      Z = memberOrTop D0.mw.size
        (fun j => Subgroup.closure {x | x ∈ sg ++ (D0.mw[j]!).map (wordElt a b)}) j)

theorem LatCtx.ofFacts_Om : (LatCtx.ofFacts A valid hlaw Δ hΔ a b ta tb ha hb gen D0 sg k hsg hSk
    N hΓ hM hstab hcomp).D.Om = D0.Om := rfl

theorem LatCtx.ofFacts_mw : (LatCtx.ofFacts A valid hlaw Δ hΔ a b ta tb ha hb gen D0 sg k hsg hSk
    N hΓ hM hstab hcomp).D.mw = D0.mw := rfl

theorem LatCtx.ofFacts_mt : (LatCtx.ofFacts A valid hlaw Δ hΔ a b ta tb ha hb gen D0 sg k hsg hSk
    N hΓ hM hstab hcomp).D.mt = D0.mt := rfl

theorem LatCtx.ofFacts_sTabs : (LatCtx.ofFacts A valid hlaw Δ hΔ a b ta tb ha hb gen D0 sg k hsg
    hSk N hΓ hM hstab hcomp).D.sTabs = D0.sTabs := rfl

theorem LatCtx.ofFacts_O_size : (LatCtx.ofFacts A valid hlaw Δ hΔ a b ta tb ha hb gen D0 sg k hsg
    hSk N hΓ hM hstab hcomp).D.O.lbl.size = N :=
  LatFacts.O_size _

end OfFacts

end CFSG.QuasithinUnique.Ch1.SporLat
