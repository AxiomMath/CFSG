module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCore
public import Certificates.Data.CFSGNative.SporLat.Spec

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat

open CFSG.QuasithinUnique.K1.SporadicPerm

section Words

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)] {Lab : Type}

variable {A : LabAct Lab} {valid : Lab → Prop} {Δ : Lab}

theorem lab_evalElt (hlaw : LabLawful Γ n A valid) (hΔ : valid Δ) (els : Array Γ)
    (letters : Array (Array ℕ))
    (hel : ∀ l < els.size, letters.getD l #[] = (tab n (els.getD l 1)).toArray) (w : List ℕ)
    (hw : ∀ l ∈ w, l < els.size) :
    lab n A Δ (evalElt els w) = labWord A.act letters Δ w := by
  induction w with
  | nil => rw [evalElt_nil, lab_one hlaw hΔ]; rfl
  | cons l w ih =>
    have hl : l < els.size := hw l List.mem_cons_self
    have h1 := ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    rw [evalElt_cons, lab_mul hlaw hΔ, h1]
    simp only [labWord, List.foldr_cons]
    rw [hel l hl]

end Words

section Pairing

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem genTabs_append (E F : List Γ) : genTabs n (E ++ F) = genTabs n E ++ genTabs n F := by
  simp [genTabs]

theorem genTabs_length (E : List Γ) : (genTabs n E).length = E.length := by simp [genTabs]

theorem genTabs_hel (E : List Γ) :
    ∀ l < E.toArray.size, (genTabs n E).toArray.getD l #[] =
      (tab n (E.toArray.getD l 1)).toArray := by
  intro l hl
  have hl' : l < E.length := by simpa using hl
  simp [genTabs, Array.getD_eq_getD_getElem?, List.getElem?_eq_getElem hl']

theorem genTabs_hel' (E : List Γ) :
    ∀ l < (genTabs n E).toArray.size, (genTabs n E).toArray[l]! =
      (tab n (E.toArray.getD l 1)).toArray := by
  intro l hl
  have hl' : l < E.length := by simpa [genTabs] using hl
  rw [getElem!_pos _ l hl]
  simp [genTabs, Array.getD_eq_getD_getElem?, List.getElem?_eq_getElem hl']

theorem genTabs_size (E : List Γ) : (genTabs n E).toArray.size = E.toArray.size := by
  simp [genTabs]

end Pairing

section Sound

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

structure LatCtx (Γ : Type) [Group Γ] [Finite Γ] (n : ℕ) [MulAction Γ (Fin n)] (Lab : Type)
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
  D : LatData Lab
  sg : List Γ
  k : ℕ
  hsg : genTabs n sg = D.sTabs
  hSk : Nat.card (Subgroup.closure {x | x ∈ sg}) = 2 ^ k
  hΓ : Nat.card Γ = D.O.lbl.size * 2 ^ k
  hD : LatOK A.act n ta tb Δ D

namespace LatCtx

variable (C : LatCtx Γ n Lab)

@[expose] def S : Subgroup Γ := stab C.hlaw C.hΔ

@[expose] def J : ℕ := C.D.mw.size

@[expose] def gens (j : ℕ) : List Γ := (C.D.mw[j]!).map (wordElt C.a C.b)

@[expose] def Y (j : ℕ) : Subgroup Γ := Subgroup.closure {x | x ∈ C.sg ++ C.gens j}

@[expose] def rep (c : ℕ) : Γ := evalElt #[C.a, C.b] (C.D.O.pathWord c c)

theorem hsz0 : (#[C.a, C.b] : Array Γ).size = (#[C.ta, C.tb] : Array (Array ℕ)).size := rfl

theorem hel0 : ∀ l < (#[C.ta, C.tb] : Array (Array ℕ)).size, (#[C.ta, C.tb] : Array (Array ℕ))[l]! =
    (tab n ((#[C.a, C.b] : Array Γ).getD l 1)).toArray := by
  intro l hl
  have : l < 2 := hl
  interval_cases l
  · simpa using C.ha.symm
  · simpa using C.hb.symm

theorem hel0' : ∀ l < (#[C.a, C.b] : Array Γ).size, (#[C.ta, C.tb] : Array (Array ℕ)).getD l #[] =
    (tab n ((#[C.a, C.b] : Array Γ).getD l 1)).toArray := by
  intro l hl
  have : l < 2 := hl
  interval_cases l
  · simpa using C.ha.symm
  · simpa using C.hb.symm

theorem hgen0 : Subgroup.closure {x | x ∈ (#[C.a, C.b] : Array Γ).toList} = ⊤ := by
  have : {x | x ∈ (#[C.a, C.b] : Array Γ).toList} = ({C.a, C.b} : Set Γ) := by
    ext x; simp
  rw [this]; exact C.gen

theorem hO : OmegaSpec C.A.act #[C.ta, C.tb] C.Δ C.D.O := C.hD.1

theorem hsfix : ∀ s ∈ C.sg, lab n C.A C.Δ s = C.Δ := by
  intro s hs
  have h1 : (tab n s).toArray ∈ C.D.sTabs := by
    rw [← C.hsg]
    exact List.mem_map.mpr ⟨s, hs, rfl⟩
  exact C.hD.2.1 _ h1

theorem hSeq : Subgroup.closure {x | x ∈ C.sg} = C.S :=
  (C.hO).sylow_eq_stab C.hlaw C.hΔ #[C.a, C.b] C.hsz0 C.hel0 C.hgen0 C.hsfix C.hSk C.hΓ

theorem S_card : Nat.card C.S = 2 ^ C.k := by
  rw [← C.hSeq]; exact C.hSk

theorem membersOK : MembersOK C.A.act n C.ta C.tb C.Δ C.D := C.hD.2.2.2.1

theorem J_pos : 0 < C.J := C.membersOK.1

theorem gens_zero : C.gens 0 = [] := by
  unfold gens
  rw [C.membersOK.2.1]; rfl

theorem gens_tabs {j : ℕ} (hj : j < C.J) : genTabs n (C.gens j) = C.D.mt[j]! := by
  obtain ⟨hw, hmt, -⟩ := C.membersOK.2.2.2.2 j hj
  rw [hmt]
  unfold gens genTabs
  rw [List.map_map]
  apply List.map_congr_left
  intro w hw'
  have := wordTabA_eq #[C.a, C.b] #[C.ta, C.tb] C.hel0' w
    (fun l hl => by simpa using hw w hw' l hl)
  simp only [Function.comp_apply]
  rw [this]
  rfl

theorem Y_letters {j : ℕ} (hj : j < C.J) :
    genTabs n (C.sg ++ C.gens j) = C.D.sTabs ++ C.D.mt[j]! := by
  rw [genTabs_append, C.hsg, C.gens_tabs hj]

theorem hOm {j : ℕ} (hj : j < C.J) :
    OmegaSpec C.A.act (genTabs n (C.sg ++ C.gens j)).toArray C.Δ C.D.Om[j]! := by
  rw [C.Y_letters hj]; exact (C.membersOK.2.2.2.2 j hj).2.2

theorem S_le_Y (j : ℕ) : C.S ≤ C.Y j := by
  rw [← C.hSeq]
  apply Subgroup.closure_mono
  intro x hx
  exact List.mem_append_left _ hx

theorem Y_zero : C.Y 0 = C.S := by
  unfold Y
  rw [C.gens_zero, ← C.hSeq]
  simp

omit [Group Γ] [Finite Γ] in
theorem toList_toArray_set (E : List Γ) : {x | x ∈ E.toArray.toList} = {x | x ∈ E} := by
  simp

theorem Y_card {j : ℕ} (hj : j < C.J) : Nat.card (C.Y j) = C.D.Om[j]!.lbl.size * 2 ^ C.k := by
  have := (C.hOm hj).card_eq C.hlaw C.hΔ (C.sg ++ C.gens j).toArray (genTabs_size _).symm
    (genTabs_hel' _) (H := C.Y j) (by rw [toList_toArray_set]; rfl) (C.S_le_Y j)
  rw [this]
  congr 1
  exact C.S_card

theorem Y_mem_iff {j : ℕ} (hj : j < C.J) (g : Γ) :
    g ∈ C.Y j ↔ ∃ x < C.D.Om[j]!.lbl.size, lab n C.A C.Δ g = C.D.Om[j]!.lbl[x]! :=
  (C.hOm hj).mem_iff C.hlaw C.hΔ (C.sg ++ C.gens j).toArray (genTabs_size _).symm
    (genTabs_hel' _) (H := C.Y j) (by rw [toList_toArray_set]; rfl) (C.S_le_Y j) g

theorem gens_mem_Y {j : ℕ} : ∀ g ∈ C.gens j, g ∈ C.Y j := fun _ hg =>
  Subgroup.subset_closure (List.mem_append_right _ hg)

theorem sg_mem_S : ∀ s ∈ C.sg, s ∈ C.S := fun s hs => by
  rw [← C.hSeq]; exact Subgroup.subset_closure hs

theorem member_card {j : ℕ} :
    Nat.card (memberOrTop C.J C.Y j) =
      (if j < C.J then C.D.Om[j]!.lbl.size else C.D.O.lbl.size) * 2 ^ C.k := by
  by_cases h : j < C.J
  · simp only [memberOrTop, h, ite_true]; exact C.Y_card h
  · simp only [memberOrTop, h, ite_false]
    rw [Subgroup.card_top]; exact C.hΓ

theorem S_le_member {j : ℕ} : C.S ≤ memberOrTop C.J C.Y j := by
  by_cases h : j < C.J
  · simp only [memberOrTop, h, ite_true]; exact C.S_le_Y j
  · simp only [memberOrTop, h, ite_false]; exact le_top

theorem member_mem_of_label {j : ℕ} {g : Γ}
    (hlab : j < C.J → ∃ x < C.D.Om[j]!.lbl.size, lab n C.A C.Δ g = C.D.Om[j]!.lbl[x]!) :
    g ∈ memberOrTop C.J C.Y j := by
  by_cases h : j < C.J
  · simp only [memberOrTop, h, ite_true]; exact (C.Y_mem_iff h g).mpr (hlab h)
  · simp only [memberOrTop, h, ite_false]; exact Subgroup.mem_top g

theorem rep_lab {c : ℕ} (hc : c < C.D.O.lbl.size) :
    lab n C.A C.Δ (C.rep c) = C.D.O.lbl[c]! :=
  (C.hO).reach C.hlaw C.hΔ #[C.a, C.b] C.hel0 c c le_rfl hc

theorem valid_lbl {c : ℕ} (hc : c < C.D.O.lbl.size) : C.valid C.D.O.lbl[c]! := by
  rw [← C.rep_lab hc]; exact valid_lab C.hlaw C.hΔ _

theorem forest_reach {i : ℕ} (hi : i < C.D.O.lbl.size) :
    ∃ s ∈ C.S, C.D.F.froot[i]! < C.D.O.lbl.size ∧ C.D.F.fdep[C.D.F.froot[i]!]! = 0 ∧
      C.D.O.lbl[i]! = C.A.act (tab n s).toArray C.D.O.lbl[C.D.F.froot[i]!]! := by
  have hlet : ∀ l < C.D.sTabs.toArray.size, ∃ s ∈ C.S,
      C.D.sTabs.toArray[l]! = (tab n s).toArray := by
    intro l hl
    have hl2 : l < (genTabs n C.sg).toArray.size := by rw [C.hsg]; exact hl
    have hl3 : l < C.sg.toArray.size := by rw [← genTabs_size (n := n)]; exact hl2
    refine ⟨C.sg.toArray.getD l 1, ?_, ?_⟩
    · apply C.sg_mem_S
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hl3]
      simp
    · rw [← C.hsg]; exact genTabs_hel' C.sg l hl2
  exact ForestSpec.reach_root C.S hlet C.A rfl C.hlaw (fun i hi => C.valid_lbl hi) C.hD.2.2.1
    _ i rfl hi

omit [Group Γ] [Finite Γ] in
theorem getD_mem (E : List Γ) [One Γ] {l : ℕ} (hl : l < E.toArray.size) :
    E.toArray.getD l 1 ∈ E := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hl]
  simp

theorem ref_mem {Z : Subgroup Γ} (hSZ : C.S ≤ Z) (E : List Γ) (hE : ∀ x ∈ E, x ∈ Z)
    (w : List ℕ) (hw : ∀ l ∈ w, l < E.length) {idx : ℕ} (hidx : idx < C.D.O.lbl.size)
    (hlab : C.D.O.lbl[idx]! = labWord C.A.act (genTabs n E).toArray C.Δ w) :
    C.rep C.D.F.froot[idx]! ∈ Z := by
  have hwE : ∀ l ∈ w, l < E.toArray.size := fun l hl => by simpa using hw l hl
  have h1 := lab_evalElt C.hlaw C.hΔ E.toArray (genTabs n E).toArray (genTabs_hel E) w hwE
  have hmem : evalElt E.toArray w ∈ Z :=
    evalElt_mem E.toArray (fun l hl => hE _ (getD_mem E hl)) w hwE
  obtain ⟨s, hs, hr, hr0, hlbl⟩ := C.forest_reach hidx
  have h2 : lab n C.A C.Δ (s * C.rep C.D.F.froot[idx]!) =
      lab n C.A C.Δ (evalElt E.toArray w) := by
    rw [lab_mul C.hlaw C.hΔ, C.rep_lab hr, h1, ← hlab, hlbl]
  have h3 := (lab_eq_iff C.hlaw C.hΔ _ _).mp h2
  have e : C.rep C.D.F.froot[idx]! = s⁻¹ * evalElt E.toArray w *
      ((s * C.rep C.D.F.froot[idx]!)⁻¹ * evalElt E.toArray w)⁻¹ := by group
  rw [e]
  exact Z.mul_mem (Z.mul_mem (Z.inv_mem (hSZ hs)) hmem) (Z.inv_mem (hSZ h3))

@[expose] def AtomClaim (c j : ℕ) : Prop :=
  j ≤ C.J ∧ C.rep c ∈ memberOrTop C.J C.Y j ∧
    ∀ Z : Subgroup Γ, C.S ≤ Z → C.rep c ∈ Z → memberOrTop C.J C.Y j ≤ Z

theorem rcLetters_eq {c : ℕ} (hc : c < C.D.O.lbl.size) :
    rcLetters n C.ta C.tb C.D c = genTabs n (C.sg ++ [C.rep c]) := by
  unfold rcLetters
  rw [genTabs_append, C.hsg]
  congr 1
  have := wordTabA_eq #[C.a, C.b] #[C.ta, C.tb] C.hel0' (C.D.O.pathWord c c)
    (fun l hl => by simpa using (C.hO).pathWord_lt c c hc l hl)
  simp only [genTabs, List.map_cons, List.map_nil]
  rw [this]
  rfl

theorem memberOrTop_top {j : ℕ} (hj : j = C.J) : memberOrTop C.J C.Y j = ⊤ := by
  rw [hj]; simp [memberOrTop]

theorem atom_claim : ∀ i, i < C.D.atoms.size →
    C.AtomClaim C.D.atoms[i]!.root C.D.atoms[i]!.cls := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hok := C.hD.2.2.2.2.1.2 i hi
    obtain ⟨hcN, hdep, hjle, hmode⟩ := hok
    have hLE := C.rcLetters_eq hcN
    rcases hmode with ⟨hm0, hmem, hOc, hsize⟩ |
        ⟨hm1, hcls, hpos, hcls', hidx, hroot, hlab, hwl⟩
    · rw [hLE] at hOc
      have hSH : C.S ≤ Subgroup.closure {x | x ∈ C.sg ++ [C.rep C.D.atoms[i]!.root]} := by
        rw [← C.hSeq]
        apply Subgroup.closure_mono
        intro x hx
        exact List.mem_append_left _ hx
      have hcardH := hOc.card_eq C.hlaw C.hΔ (C.sg ++ [C.rep C.D.atoms[i]!.root]).toArray
        (genTabs_size _).symm (genTabs_hel' _)
        (H := Subgroup.closure {x | x ∈ C.sg ++ [C.rep C.D.atoms[i]!.root]})
        (by rw [toList_toArray_set]) hSH
      have hmemrep : C.rep C.D.atoms[i]!.root ∈ memberOrTop C.J C.Y C.D.atoms[i]!.cls :=
        C.member_mem_of_label (fun hj => by
          obtain ⟨x, hx, hxe⟩ := hmem hj
          exact ⟨x, hx, by rw [C.rep_lab hcN, hxe]⟩)
      have hHle : Subgroup.closure {x | x ∈ C.sg ++ [C.rep C.D.atoms[i]!.root]} ≤
          memberOrTop C.J C.Y C.D.atoms[i]!.cls := by
        rw [Subgroup.closure_le]
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact C.S_le_member (C.sg_mem_S x hx)
        · rw [List.mem_singleton.mp hx]; exact hmemrep
      have hsize' : C.D.atoms[i]!.oc.lbl.size = (if C.D.atoms[i]!.cls < C.J then
          C.D.Om[C.D.atoms[i]!.cls]!.lbl.size else C.D.O.lbl.size) := hsize
      have hS' : Nat.card (stab C.hlaw C.hΔ) = 2 ^ C.k := C.S_card
      have hHeq : Subgroup.closure {x | x ∈ C.sg ++ [C.rep C.D.atoms[i]!.root]} =
          memberOrTop C.J C.Y C.D.atoms[i]!.cls :=
        Subgroup.eq_of_le_of_card_ge hHle (by
          rw [C.member_card, hcardH, hS', hsize'])
      refine ⟨hjle, hmemrep, ?_⟩
      intro Z hSZ hrZ
      rw [← hHeq, Subgroup.closure_le]
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hSZ (C.sg_mem_S x hx)
      · rw [List.mem_singleton.mp hx]; exact hrZ
    · have hMt : memberOrTop C.J C.Y C.D.atoms[i]!.cls = ⊤ := C.memberOrTop_top hcls
      refine ⟨hjle, by rw [hMt]; exact Subgroup.mem_top _, ?_⟩
      intro Z hSZ hrZ
      rw [hMt, top_le_iff]
      have hrefClaim := ih C.D.atoms[i]!.refPos hpos (by omega)
      have hrr : C.rep C.D.atoms[C.D.atoms[i]!.refPos]!.root ∈ Z := by
        have := C.ref_mem hSZ (C.sg ++ [C.rep C.D.atoms[i]!.root]) (fun x hx => by
            rcases List.mem_append.mp hx with hx | hx
            · exact hSZ (C.sg_mem_S x hx)
            · rw [List.mem_singleton.mp hx]; exact hrZ)
          C.D.atoms[i]!.refWord (by
            intro l hl
            have := hwl l hl
            rwa [hLE, genTabs_length] at this)
          hidx (by rw [← hLE]; exact hlab)
        rwa [hroot] at this
      have h4 := hrefClaim.2.2 Z hSZ hrr
      rw [C.memberOrTop_top hcls', top_le_iff] at h4
      exact h4

theorem joinLetters_eq {e : JoinData Lab} (hj : e.j < C.J) (hj' : e.j' < C.J) :
    joinLetters C.D e = genTabs n (C.sg ++ C.gens e.j ++ C.gens e.j') := by
  unfold joinLetters
  rw [genTabs_append, genTabs_append, C.hsg, C.gens_tabs hj, C.gens_tabs hj']

theorem gensIn_le {j jj : ℕ} (hj : j < C.J) (hjj : jj < C.J)
    (h : GensIn C.A.act C.Δ C.D j jj) : C.Y j ≤ C.Y jj := by
  unfold Y
  rw [Subgroup.closure_le]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact C.S_le_Y jj (C.sg_mem_S x hx)
  · have h1 : (tab n x).toArray ∈ C.D.mt[j]! := by
      rw [← C.gens_tabs hj]; exact List.mem_map.mpr ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hye⟩ := h _ h1
    exact (C.Y_mem_iff hjj x).mpr ⟨y, hy, by rw [hye]; rfl⟩

theorem Y_le_member {j jj : ℕ} (hj : j < C.J) (h : jj < C.J → GensIn C.A.act C.Δ C.D j jj) :
    C.Y j ≤ memberOrTop C.J C.Y jj := by
  by_cases hjj : jj < C.J
  · simp only [memberOrTop, hjj, ite_true]; exact C.gensIn_le hj hjj (h hjj)
  · simp only [memberOrTop, hjj, ite_false]; exact le_top

theorem join_entry {e : JoinData Lab}
    (he : JoinOK' C.A.act C.Δ C.D e (joinLetters C.D e)) :
    C.Y e.j ⊔ C.Y e.j' = memberOrTop C.J C.Y e.jj := by
  obtain ⟨hj, hj', hjj, hmode⟩ := he
  have hLE := C.joinLetters_eq hj hj'
  have hSW : C.S ≤ C.Y e.j ⊔ C.Y e.j' := le_trans (C.S_le_Y e.j) le_sup_left
  have hEW : ∀ x ∈ C.sg ++ C.gens e.j ++ C.gens e.j', x ∈ C.Y e.j ⊔ C.Y e.j' := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact hSW (C.sg_mem_S x hx)
      · exact Subgroup.mem_sup_left (C.gens_mem_Y x hx)
    · exact Subgroup.mem_sup_right (C.gens_mem_Y x hx)
  rcases hmode with ⟨hm0, hgi, hOj, hsize⟩ | ⟨hm1, hjjJ, hpos, hcls, hidx, hroot, hlab, hwl⟩
  · rw [hLE] at hOj
    have hSH : C.S ≤ Subgroup.closure {x | x ∈ C.sg ++ C.gens e.j ++ C.gens e.j'} := by
      rw [← C.hSeq]
      apply Subgroup.closure_mono
      intro x hx
      exact List.mem_append_left _ (List.mem_append_left _ hx)
    have hcardH := hOj.card_eq C.hlaw C.hΔ (C.sg ++ C.gens e.j ++ C.gens e.j').toArray
      (genTabs_size _).symm (genTabs_hel' _)
      (H := Subgroup.closure {x | x ∈ C.sg ++ C.gens e.j ++ C.gens e.j'})
      (by rw [toList_toArray_set]) hSH
    have hYj : C.Y e.j ≤ memberOrTop C.J C.Y e.jj :=
      C.Y_le_member hj (fun h => (hgi h).1)
    have hYj' : C.Y e.j' ≤ memberOrTop C.J C.Y e.jj :=
      C.Y_le_member hj' (fun h => (hgi h).2)
    have hHle : Subgroup.closure {x | x ∈ C.sg ++ C.gens e.j ++ C.gens e.j'} ≤
        memberOrTop C.J C.Y e.jj := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · exact C.S_le_member (C.sg_mem_S x hx)
        · exact hYj (C.gens_mem_Y x hx)
      · exact hYj' (C.gens_mem_Y x hx)
    have hsize' : e.oj.lbl.size = (if e.jj < C.J then
        C.D.Om[e.jj]!.lbl.size else C.D.O.lbl.size) := hsize
    have hS' : Nat.card (stab C.hlaw C.hΔ) = 2 ^ C.k := C.S_card
    have hHeq : Subgroup.closure {x | x ∈ C.sg ++ C.gens e.j ++ C.gens e.j'} =
        memberOrTop C.J C.Y e.jj :=
      Subgroup.eq_of_le_of_card_ge hHle (by rw [C.member_card, hcardH, hS', hsize'])
    have hHW : Subgroup.closure {x | x ∈ C.sg ++ C.gens e.j ++ C.gens e.j'} ≤
        C.Y e.j ⊔ C.Y e.j' := by
      rw [Subgroup.closure_le]
      exact hEW
    apply le_antisymm
    · exact sup_le hYj hYj'
    · rw [← hHeq]; exact hHW
  · have hMt : memberOrTop C.J C.Y e.jj = ⊤ := C.memberOrTop_top hjjJ
    rw [hMt, eq_top_iff]
    have hrr : C.rep C.D.atoms[e.refPos]!.root ∈ C.Y e.j ⊔ C.Y e.j' := by
      have := C.ref_mem hSW (C.sg ++ C.gens e.j ++ C.gens e.j') hEW e.refWord (by
          intro l hl
          have := hwl l hl
          rwa [hLE, genTabs_length] at this)
        hidx (by rw [← hLE]; exact hlab)
      rwa [hroot] at this
    have h4 := (C.atom_claim e.refPos hpos).2.2 _ hSW hrr
    rwa [C.memberOrTop_top hcls] at h4

theorem hjoin : ∀ j < C.J, ∀ j' ≤ C.J, ∃ j'' ≤ C.J,
    memberOrTop C.J C.Y j ⊔ memberOrTop C.J C.Y j' = memberOrTop C.J C.Y j'' := by
  intro j hj j' hj'
  by_cases hjj : j' < C.J
  · have hm : ∀ i, i < C.J → memberOrTop C.J C.Y i = C.Y i := fun i hi => by
      simp [memberOrTop, hi]
    rw [hm j hj, hm j' hjj]
    rcases lt_trichotomy j j' with hlt | heq | hgt
    · rcases C.hD.2.2.2.2.2 j hj j' hjj hlt with h1 | h2 | ⟨e, he, rfl, rfl, hok⟩
      · exact ⟨j', hj', by rw [hm j' hjj]; exact sup_eq_right.mpr (C.gensIn_le hj hjj h1)⟩
      · exact ⟨j, by omega, by rw [hm j hj]; exact sup_eq_left.mpr (C.gensIn_le hjj hj h2)⟩
      · exact ⟨e.jj, hok.2.2.1, C.join_entry hok⟩
    · subst heq
      exact ⟨j, by omega, by rw [hm j hj]; exact sup_idem _⟩
    · rcases C.hD.2.2.2.2.2 j' hjj j hj hgt with h1 | h2 | ⟨e, he, rfl, rfl, hok⟩
      · exact ⟨j, by omega, by rw [hm j hj]; exact sup_eq_left.mpr (C.gensIn_le hjj hj h1)⟩
      · exact ⟨j', hj', by rw [hm j' hjj]; exact sup_eq_right.mpr (C.gensIn_le hj hjj h2)⟩
      · exact ⟨e.jj, hok.2.2.1, by rw [sup_comm]; exact C.join_entry hok⟩
  · have : j' = C.J := by omega
    refine ⟨C.J, le_rfl, ?_⟩
    rw [C.memberOrTop_top this, C.memberOrTop_top rfl, sup_top_eq]

theorem hcover : ∀ g : Γ, ∃ c < C.D.atoms.size, ∃ s ∈ C.S, ∃ t ∈ C.S,
    g = s * C.rep C.D.atoms[c]!.root * t := by
  intro g
  obtain ⟨x, hx, hgx⟩ := (C.hO).cover C.hlaw C.hΔ #[C.a, C.b] C.hsz0 C.hel0 C.hgen0 g
    (Subgroup.mem_top g)
  obtain ⟨s, hs, hr, hr0, hlbl⟩ := C.forest_reach hx
  have hrroots : C.D.F.froot[x]! ∈ C.D.F.roots C.D.O.lbl.size := by
    unfold ForestData.roots
    rw [List.mem_filter]
    exact ⟨List.mem_range.mpr hr, by simp [hr0]⟩
  obtain ⟨i, hi, hir⟩ := C.hD.2.2.2.2.1.1 _ hrroots
  refine ⟨i, hi, s, hs, (s * C.rep C.D.F.froot[x]!)⁻¹ * g, ?_, ?_⟩
  · apply (lab_eq_iff C.hlaw C.hΔ _ _).mp
    rw [lab_mul C.hlaw C.hΔ, C.rep_lab hr, hgx, hlbl]
  · rw [hir]; group

theorem complete : ∀ Z : Subgroup Γ, C.S ≤ Z → ∃ j ≤ C.J, Z = memberOrTop C.J C.Y j :=
  family_complete C.J C.Y C.D.atoms.size (fun i => C.rep C.D.atoms[i]!.root)
    (fun i => C.D.atoms[i]!.cls) (fun j _ => C.S_le_Y j) ⟨C.J_pos, C.Y_zero⟩ C.hcover
    (fun c hc => C.atom_claim c hc) C.hjoin

end LatCtx

end Sound

section SGens

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem sGens_of_baseCertS [Finite Γ] (B : List ℕ) (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (a b : Γ) (prog : List (ℕ × ℕ))
    (hv : slpValidAux prog 2 = true) (qp : List (ℕ × ℕ)) (zn gn gin hn hin : ℕ)
    (Ts : Array (List ℕ)) (par cl : Array ℕ) (k : ℕ)
    (hcert : BaseCertS n B (slpTabsA (tab n a).toArray (tab n b).toArray prog) qp zn gn gin hn hin
      Ts par cl k) :
    genTabs n (qp.map fun p => (slpElts a b prog).getD p.1 1) =
      qp.map (fun p => (slpTabsA (tab n a).toArray (tab n b).toArray prog)[p.1]!) ∧
    Nat.card (Subgroup.closure {x | x ∈ qp.map fun p => (slpElts a b prog).getD p.1 1}) =
      2 ^ k := by
  obtain ⟨hqp, hz, hg, hgi, hh, hhi, hc⟩ := hcert
  obtain ⟨hinvq, -, -, hEnum, hsize, -⟩ := hc
  set T := slpTabsA (tab n a).toArray (tab n b).toArray prog with hT
  have hinv := slp_foldl_inv (n := n) prog #[a, b] #[(tab n a).toArray, (tab n b).toArray]
    (by simp) (by
      intro i hi
      have hi' : i < 2 := by simpa using hi
      interval_cases i <;> simp) hv
  have hE : ∀ i < T.size, tab n ((slpElts a b prog).getD i 1) = (T[i]!).toList := hinv.2
  have hE' : ∀ i < T.size, (tab n ((slpElts a b prog).getD i 1)).toArray = T[i]! := by
    intro i hi
    rw [hE i hi, Array.toArray_toList]
  have hsg : genTabs n (qp.map fun p => (slpElts a b prog).getD p.1 1) =
      qp.map (fun p => T[p.1]!) := by
    simp only [genTabs, List.map_map]
    apply List.map_congr_left
    intro p hp
    exact hE' p.1 (hqp p hp).1
  have hinv_of : ∀ x y : Γ,
      (∀ q < n, img (tab n y).toArray (img (tab n x).toArray q) = q) → y = x⁻¹ := by
    intro x y hxy
    apply eq_inv_of_mul_eq_one_left
    apply hbase
    intro b hb
    rw [act_mul _ _ (hB b hb)]
    have := hxy b (hB b hb)
    simpa only [img_tab] using this
  have hsgi : genTabsInv n (qp.map fun p => (slpElts a b prog).getD p.1 1) =
      qp.map (fun p => T[p.2]!) := by
    simp only [genTabsInv, List.map_map]
    apply List.map_congr_left
    intro p hp
    have h1 := hE' p.1 (hqp p hp).1
    have h2 := hE' p.2 (hqp p hp).2
    have h3 : (slpElts a b prog).getD p.2 1 = ((slpElts a b prog).getD p.1 1)⁻¹ := by
      apply hinv_of
      intro q hq
      have := hinvq (T[p.1]!, T[p.2]!) (List.mem_map.mpr ⟨p, hp, rfl⟩) q hq
      simpa only [← h1, ← h2] using this
    simp only [Function.comp_apply]
    rw [← h2, h3]
  refine ⟨hsg, ?_⟩
  have hEnum' : BaseEnumOK n B (genTabs n (qp.map fun p => (slpElts a b prog).getD p.1 1))
      (genTabsInv n (qp.map fun p => (slpElts a b prog).getD p.1 1)) Ts par cl := by
    rw [hsg, hsgi]
    simpa only [List.map_map, Function.comp_def] using hEnum
  rw [benum_card hB hbase _ Ts par cl hEnum', hsize]

end SGens

end CFSG.QuasithinUnique.Ch1.SporLat
