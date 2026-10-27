module

public import CFSG.Certificates.Kernel.E6TT.RowSound
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoTableTBridge

public section

namespace CFSG.KC.E6TT

open CFSG.KC.Enum (strictB)
open Certificates.Data.E6TableT (Vec iform roots reps classes kerRoots act)
open Certificates.Data.E6TableTTwo (cosetW orbitLen inOrbit rankOf)
open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Timmesfeld.LangTorus (twistInner compRank componentOrbitLength)
open CFSG.StandardType.TablePThreeKG (classSet E6Admissible E6KerComponent E6SolvTwo E6RowTwoW
  E6RowTwoT E6CosetW E6TableTTwoAt repZ bList act_bList_ofFn e6Two_classes_facts
  e6KerComponent_iff_classes classSet_ncard classes_lengths classes_compRank_eq_rankOf
  e6CosetW_iff_cosetW isRoot_iff_mem_roots)

theorem bIf_cases {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c <;> simp_all

theorem permK_lt {π : List Nat} {n : Nat} (h : permK π n = true) {i : Nat} (hi : i < π.length) :
    π.getD i 0 < n := by
  have hmem : π.getD i 0 ∈ π := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have h1 : Nat.blt (π.getD i 0) n = true := List.all_eq_true.1 (bAnd_true h).1 _ hmem
  rwa [Nat.blt_eq] at h1

theorem permK_surj {π : List Nat} {n : Nat} (h : permK π n = true) {i : Nat} (hi : i < n) :
    ∃ i' < π.length, π.getD i' 0 = i := by
  have h1 : π.contains i = true := List.all_eq_true.1 (bAnd_true h).2 i (List.mem_range.2 hi)
  obtain ⟨i', hi', he⟩ := List.getElem_of_mem (List.contains_iff_mem.1 h1)
  exact ⟨i', hi', by rw [List.getD_eq_getElem _ _ hi', he]⟩

theorem orbitLen_one {π : List Nat} (hlen : π.length = 1) (h0 : π.getD 0 0 < 1) :
    orbitLen π 0 = 1 := by
  obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hlen
  have ha : a = 0 := by simpa using h0
  subst ha
  rfl

theorem iterate_add_hom (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y) :
    ∀ (n : ℕ) (x y : Fin Tag.E6.rank → ℤ),
      (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[n] (x + y) =
        (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[n] x +
          (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[n] y
  | 0, _, _ => rfl
  | n + 1, x, y => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      hadd, iterate_add_hom ρ hadd n]

theorem f1_ofFn (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)) (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y)
    (γ : Fin Tag.E6.rank → ℤ) :
    f1 (bList fun i => ρ (Pi.single i 1)) (List.ofFn γ) = List.ofFn (ρ γ) :=
  act_bList_ofFn ρ hadd γ

theorem f2_ofFn (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)) (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y)
    (γ : Fin Tag.E6.rank → ℤ) :
    f2 (bList fun i => ρ (Pi.single i 1)) (List.ofFn γ) =
      List.ofFn ((ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[2] γ) := by
  unfold f2
  rw [act_bList_ofFn ρ hadd, act_bList_ofFn ρ hadd]
  rfl

theorem f3_ofFn (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)) (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y)
    (γ : Fin Tag.E6.rank → ℤ) :
    f3 (bList fun i => ρ (Pi.single i 1)) (List.ofFn γ) =
      List.ofFn ((ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[3] γ) := by
  unfold f3
  rw [act_bList_ofFn ρ hadd, act_bList_ofFn ρ hadd, act_bList_ofFn ρ hadd]
  rfl

theorem getD_mem_classes (k : Fin 5) {j : Nat} (hj : j < (classes (reps.getD k [])).length) :
    (classes (reps.getD k [])).getD j [] ∈ classes (reps.getD k []) := by
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

theorem class_roots (k : Fin 5) {l : List Vec} (hl : l ∈ classes (reps.getD k [])) :
    ∀ x ∈ l, x ∈ roots () := by
  intro x hx
  obtain ⟨hxK, hx6⟩ := class_ker k hl hx
  rw [← ofFn_toV hx6] at hxK ⊢
  exact (isRoot_iff_mem_roots _).1 ((ofFn_mem_ker k _).1 hxK).1

theorem getD_range_map {α : Type} (f : Nat → α) (d : α) {k n : Nat} (hk : k < n) :
    ((List.range n).map f).getD k d = f k := by
  have hk' : k < ((List.range n).map f).length := by
    rw [List.length_map, List.length_range]
    exact hk
  rw [List.getD_eq_getElem _ _ hk', List.getElem_map, List.getElem_range]

theorem cls_count (k : Fin 5) : (classes (reps.getD k [])).length =
    (([[6, 6, 6], [20, 2], [24], [30], [40]] : List (List Nat)).getD k []).length := by
  have h : (((List.range 5).map fun k => (classes (reps.getD k [])).map List.length).getD k
      []).length = (([[6, 6, 6], [20, 2], [24], [30], [40]] : List (List Nat)).getD k []).length := by
    rw [classes_lengths]
  rw [← h, getD_range_map _ _ k.isLt, List.length_map]

theorem cls_len (k : Fin 5) {j : Nat} (hj : j < (classes (reps.getD k [])).length) :
    ((classes (reps.getD k [])).getD j []).length =
      (([[6, 6, 6], [20, 2], [24], [30], [40]] : List (List Nat)).getD k []).getD j 0 := by
  have h : (((List.range 5).map fun k => (classes (reps.getD k [])).map List.length).getD k
      []).getD j 0 = (([[6, 6, 6], [20, 2], [24], [30], [40]] : List (List Nat)).getD k []).getD j 0 := by
    rw [classes_lengths]
  rw [← h, getD_range_map _ _ k.isLt]
  have hj' : j < ((classes (reps.getD k [])).map List.length).length := by
    rw [List.length_map]
    exact hj
  rw [List.getD_eq_getElem _ _ hj', List.getElem_map, List.getD_eq_getElem _ _ hj]

theorem hdK_mem (k : Fin 5)
    {l : List Vec} (hl : l ∈ classes (reps.getD k [])) {H : List Nat} {O : List (List Nat)}
    (hc : classK l H O = true) : hdK H ∈ l := by
  obtain ⟨hΔl, -, -, -⟩ := classK_spec hc
  obtain ⟨-, hlen, hne, -, -⟩ := (e6Two_classes_facts k).1 l hl
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil l hne
  have hm := meet_of_mem (class_roots k hl) hc hx (hlen x hx)
  unfold meetK at hm
  obtain ⟨δ, hδ, -⟩ := List.any_eq_true.1 hm
  obtain ⟨a, t, ht⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hδ)
  have key : hdK H ∈ dK H := by
    unfold hdK
    rw [ht, List.getD_cons_zero]
    exact List.mem_cons_self
  exact hΔl _ key

theorem rowK_orbits (k : Fin 5)
    {Hs : List (List Nat)} {Os : List (List (List Nat))}
    (hw : wOKK (classes (reps.getD k [])) Hs Os = true) (hs : hsK Hs = true)
    (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)) (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y)
    (hroot : ∀ γ, IsRoot Tag.E6 γ → IsRoot Tag.E6 (ρ γ))
    (hadm : E6Admissible (fun i => ρ (Pi.single i 1)) (repZ k) 2)
    (hperm : permK (piK Hs (bList fun i => ρ (Pi.single i 1))) Hs.length = true)
    (j : ℕ) (hj : j < (classes (reps.getD k [])).length) :
    componentOrbitLength ρ (classSet ((classes (reps.getD k [])).getD j [])) =
        orbitLen (piK Hs (bList fun i => ρ (Pi.single i 1))) j ∧
      ∀ j' < (classes (reps.getD k [])).length,
        ((∃ m : ℕ, (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[m] ''
            classSet ((classes (reps.getD k [])).getD j []) =
              classSet ((classes (reps.getD k [])).getD j' [])) ↔
          inOrbit (piK Hs (bList fun i => ρ (Pi.single i 1))) j j' = true) := by
  obtain ⟨hHlen, -, hc⟩ := wOKK_spec hw
  obtain ⟨hconnAll, hsep⟩ := bAnd_true hs
  have hconn : ∀ i < (classes (reps.getD k [])).length, connK (Hs.getD i []) = true := by
    intro i hi
    have hi' : i < Hs.length := by omega
    have hmem : Hs.getD i [] ∈ Hs := by
      rw [List.getD_eq_getElem _ _ hi']
      exact List.getElem_mem hi'
    exact List.all_eq_true.1 hconnAll _ hmem
  have hπlen : (piK Hs (bList fun i => ρ (Pi.single i 1))).length =
      (classes (reps.getD k [])).length := by
    rw [piK, List.length_map, hHlen]
  have hπget : ∀ i < (classes (reps.getD k [])).length,
      (piK Hs (bList fun i => ρ (Pi.single i 1))).getD i 0 =
        idxK (act (bList fun i => ρ (Pi.single i 1)) (hdK (Hs.getD i []))) Hs 0 := by
    intro i hi
    have hi' : i < Hs.length := by omega
    rw [List.getD_eq_getElem _ _ (by rw [hπlen]; exact hi), List.getD_eq_getElem _ _ hi']
    simp only [piK, List.getElem_map]
  have hlt : ∀ i < (classes (reps.getD k [])).length,
      (piK Hs (bList fun i => ρ (Pi.single i 1))).getD i 0 < (classes (reps.getD k [])).length := by
    intro i hi
    rw [← hHlen]
    exact permK_lt hperm (by rw [hπlen]; exact hi)
  have hsurj : ∀ i < (classes (reps.getD k [])).length, ∃ i' < (classes (reps.getD k [])).length,
      (piK Hs (bList fun i => ρ (Pi.single i 1))).getD i' 0 = i := by
    intro i hi
    obtain ⟨i', hi', he⟩ := permK_surj hperm (by omega : i < Hs.length)
    exact ⟨i', by rw [← hπlen]; exact hi', he⟩
  have hsub : ∀ i < (classes (reps.getD k [])).length, ∀ x ∈ (classes (reps.getD k [])).getD i [],
      List.ofFn (ρ (toV x)) ∈ (classes (reps.getD k [])).getD
        ((piK Hs (bList fun i => ρ (Pi.single i 1))).getD i 0) [] := by
    intro i hi x hx
    have hpi := hlt i hi
    have hm : meetK (Hs.getD ((piK Hs (bList fun i => ρ (Pi.single i 1))).getD i 0) [])
        (act (bList fun i => ρ (Pi.single i 1)) (hdK (Hs.getD i []))) = true := by
      obtain ⟨-, h2⟩ := idxK_spec (act (bList fun i => ρ (Pi.single i 1)) (hdK (Hs.getD i []))) Hs 0
      have h3 := h2 (by rw [← hπget i hi]; omega)
      rw [Nat.sub_zero, ← hπget i hi] at h3
      exact h3
    have hx6 := (class_ker k (getD_mem_classes k hi) hx).2
    rw [← act_toV ρ hadd hx6]
    exact classSub k ρ hadd hroot hadm (getD_mem_classes k hi) (getD_mem_classes k hpi) (hc i hi)
      (hc _ hpi) (hconn i hi) hm x hx
  have hinj : ∀ i i', i < (classes (reps.getD k [])).length →
      i' < (classes (reps.getD k [])).length →
      classSet ((classes (reps.getD k [])).getD i []) =
        classSet ((classes (reps.getD k [])).getD i' []) → i = i' := by
    intro i i' hi hi' heq
    by_contra hne
    have hx := hdK_mem k (getD_mem_classes k hi) (hc i hi)
    have hx6 := (class_ker k (getD_mem_classes k hi) hx).2
    have h1 : toV (hdK (Hs.getD i [])) ∈ classSet ((classes (reps.getD k [])).getD i []) := by
      change List.ofFn (toV (hdK (Hs.getD i []))) ∈ (classes (reps.getD k [])).getD i []
      rw [ofFn_toV hx6]
      exact hx
    rw [heq] at h1
    have h2 : List.ofFn (toV (hdK (Hs.getD i []))) ∈ (classes (reps.getD k [])).getD i' [] := h1
    rw [ofFn_toV hx6] at h2
    have hm := meet_of_mem (class_roots k (getD_mem_classes k hi')) (hc i' hi') h2 hx6
    unfold sepK at hsep
    have hs1 := List.all_eq_true.1 hsep i (List.mem_range.2 (by omega))
    have hs2 := List.all_eq_true.1 hs1 i' (List.mem_range.2 (by omega))
    have hb : Nat.beq i i' = false := by
      cases h : Nat.beq i i'
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hne
    rw [hb] at hs2
    have hs3 : (!meetK (Hs.getD i' []) (hdK (Hs.getD i []))) = true := hs2
    rw [hm] at hs3
    exact absurd hs3 (by decide)
  exact classPermK k ρ (piK Hs (bList fun i => ρ (Pi.single i 1))) hπlen hlt hsurj hsub hinj j hj

theorem rowK_zero {Hs : List (List Nat)} {Os : List (List (List Nat))} {b : List Vec}
    (h : rowK 0 Hs Os b = true) :
    (List.range Hs.length).all (rowA2 Hs Os b (piK Hs b) (cosetW b)) = true := by
  have h2 := (bAnd_true h).2
  exact h2

theorem rowK_one {Hs : List (List Nat)} {Os : List (List (List Nat))} {b : List Vec}
    (h : rowK 1 Hs Os b = true) :
    (piK Hs b == [0, 1]) = true ∧
      (!cosetW b && outK (Hs.getD 0 []) (Os.getD 0 []) (f1 b)) = true := by
  have h1 := (bAnd_true (bAnd_true h).2).1
  have h2 := (bAnd_true (bAnd_true h).2).2
  exact ⟨h1, h2⟩

theorem rowK_two {Hs : List (List Nat)} {Os : List (List (List Nat))} {b : List Vec}
    (h : rowK 2 Hs Os b = true) : rowD4 (Hs.getD 0 []) (Os.getD 0 []) b (cosetW b) = true := by
  have h2 := (bAnd_true h).2
  exact h2

theorem rowK_three {Hs : List (List Nat)} {Os : List (List (List Nat))} {b : List Vec}
    (h : rowK 3 Hs Os b = true) :
    Bool.rec (motive := fun _ => Bool) (outK (Hs.getD 0 []) (Os.getD 0 []) (f1 b))
      (inK (Hs.getD 0 []) (f1 b)) (cosetW b) = true := by
  have h2 := (bAnd_true h).2
  exact h2

theorem rowK_four {Hs : List (List Nat)} {Os : List (List (List Nat))} {b : List Vec}
    (h : rowK 4 Hs Os b = true) :
    (!cosetW b && outK (Hs.getD 0 []) (Os.getD 0 []) (f1 b)) = true := by
  have h2 := (bAnd_true h).2
  exact h2

theorem rowK_sound (k : Fin 5)
    {Hs : List (List Nat)} {Os : List (List (List Nat))}
    (hw : wOKK (classes (reps.getD k [])) Hs Os = true) (hs : hsK Hs = true)
    (hrow : ∀ ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ), (∀ x y, ρ (x + y) = ρ x + ρ y) →
      (∀ γ, IsRoot Tag.E6 γ → IsRoot Tag.E6 (ρ γ)) →
      E6Admissible (fun i => ρ (Pi.single i 1)) (repZ k) 2 →
      rowK k Hs Os (bList fun i => ρ (Pi.single i 1)) = true) :
    E6TableTTwoAt (repZ k) := by
  intro ρ hadd hroot hadm _ Ψ hΨ hnot hout
  obtain ⟨l, hl, rfl⟩ := (e6KerComponent_iff_classes k Ψ).1 hΨ
  obtain ⟨j, hj, rfl⟩ : ∃ j, j < (classes (reps.getD k [])).length ∧
      (classes (reps.getD k [])).getD j [] = l := by
    obtain ⟨j, hj, he⟩ := List.getElem_of_mem hl
    exact ⟨j, hj, by rw [List.getD_eq_getElem _ _ hj, he]⟩
  have hr := hrow ρ hadd hroot hadm
  have hperm : permK (piK Hs (bList fun i => ρ (Pi.single i 1))) Hs.length = true :=
    (bAnd_true hr).1
  have horb := rowK_orbits k hw hs ρ hadd hroot hadm hperm
  obtain ⟨hHlen, -, hc⟩ := wOKK_spec hw
  have hπlen : (piK Hs (bList fun i => ρ (Pi.single i 1))).length =
      (classes (reps.getD k [])).length := by
    rw [piK, List.length_map, hHlen]
  have hmemj := getD_mem_classes k hj
  have hrank := classes_compRank_eq_rankOf k _ hmemj
  have hncard := classSet_ncard k _ hmemj
  have hR := class_roots k hmemj
  have hcw := e6CosetW_iff_cosetW ρ hadd
  have hk := k.isLt
  rcases (by omega : (k : ℕ) = 0 ∨ (k : ℕ) = 1 ∨ (k : ℕ) = 2 ∨ (k : ℕ) = 3 ∨ (k : ℕ) = 4) with
    h0 | h0 | h0 | h0 | h0 <;> rw [h0] at hr
  ·
    have hcnt3 : (classes (reps.getD k [])).length = 3 := by
      rw [cls_count k, h0]
      rfl
    have h6 : ∀ j' < (classes (reps.getD k [])).length,
        ((classes (reps.getD k [])).getD j' []).length = 6 := by
      intro j' hj'
      rw [cls_len k hj', h0]
      have : j' < 3 := by omega
      interval_cases j' <;> rfl
    have hA : rowA2 Hs Os (bList fun i => ρ (Pi.single i 1))
        (piK Hs (bList fun i => ρ (Pi.single i 1))) (cosetW (bList fun i => ρ (Pi.single i 1)))
        j = true := List.all_eq_true.1 (rowK_zero hr) j (List.mem_range.2 (by omega))
    unfold rowA2 at hA
    simp only [strictB_eqE] at hA
    rcases bIf_cases hA with ⟨hA1, -⟩ | ⟨-, hA⟩
    ·
      obtain ⟨ho, hout1⟩ := bAnd_true hA1
      exfalso
      exact hnot (Or.inr ⟨by rw [hrank, h6 j hj]; rfl, by rw [hncard, h6 j hj],
        by rw [(horb j hj).1]; exact Nat.eq_of_beq_eq_true ho,
        outK_sound hR (hc j hj) hadd (f1_ofFn ρ hadd) hout1⟩)
    rcases bIf_cases hA with ⟨hB, -⟩ | ⟨-, hV⟩
    · rcases bIf_cases hB with ⟨hcwT, hW⟩ | ⟨hcwF, hT⟩
      · obtain ⟨ho, hi2⟩ := bAnd_true hW
        exact ⟨fun _ => Or.inr (Or.inr ⟨by rw [hrank, h6 j hj]; rfl, by rw [hncard, h6 j hj],
          by rw [(horb j hj).1]; exact Nat.eq_of_beq_eq_true ho,
          inK_sound hR (hc j hj) (iterate_add_hom ρ hadd 2) (f2_ofFn ρ hadd) hi2⟩),
          fun hn => absurd (hcw.2 hcwT) hn⟩
      · obtain ⟨ho, ho3⟩ := bAnd_true hT
        refine ⟨fun hc' => absurd (hcw.1 hc') (by rw [hcwF]; decide), fun _ => ?_⟩
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by rw [hrank, h6 j hj]; rfl,
          by rw [hncard, h6 j hj], by rw [(horb j hj).1]; exact Nat.eq_of_beq_eq_true ho,
          outK_sound hR (hc j hj) (iterate_add_hom ρ hadd 3) (f3_ofFn ρ hadd) ho3⟩)))
    ·
      exfalso
      unfold vacA2 at hV
      obtain ⟨j', hj', hV⟩ := List.any_eq_true.1 hV
      rw [List.mem_range] at hj'
      obtain ⟨hno, hV⟩ := bAnd_true hV
      have hj'c : j' < (classes (reps.getD k [])).length := by omega
      have hmem' := getD_mem_classes k hj'c
      have hsol := hout (classSet ((classes (reps.getD k [])).getD j' []))
        ((e6KerComponent_iff_classes k _).2 ⟨_, hmem', rfl⟩) (fun m hm => by
          have hio := ((horb j hj).2 j' hj'c).1 ⟨m, hm⟩
          rw [hio] at hno
          exact absurd hno (by decide))
      rcases hsol with ⟨hr1, -⟩ | ⟨-, -, ho1, hni⟩
      · rw [classes_compRank_eq_rankOf k _ hmem', h6 j' hj'c] at hr1
        exact absurd hr1 (by decide)
      · rw [(horb j' hj'c).1] at ho1
        rcases bIf_cases hV with ⟨hne1, -⟩ | ⟨-, hin⟩
        · rw [ho1] at hne1
          exact absurd hne1 (by decide)
        · exact hni (inK_sound (class_roots k hmem') (hc j' hj'c) hadd (f1_ofFn ρ hadd) hin)
  ·
    obtain ⟨hπ, hrest⟩ := rowK_one hr
    rw [Bool.and_eq_true] at hrest
    obtain ⟨hnc, hout1⟩ := hrest
    have hπ' : piK Hs (bList fun i => ρ (Pi.single i 1)) = [0, 1] := beq_iff_eq.1 hπ
    have hcnt2 : (classes (reps.getD k [])).length = 2 := by
      rw [cls_count k, h0]
      rfl
    have ho1 : componentOrbitLength ρ (classSet ((classes (reps.getD k [])).getD j [])) = 1 := by
      rw [(horb j hj).1, hπ']
      have : j < 2 := by omega
      interval_cases j <;> rfl
    have hj2 : j < 2 := by omega
    interval_cases j
    · have hlenj : ((classes (reps.getD k [])).getD 0 []).length = 20 := by
        rw [cls_len k hj, h0]
        rfl
      refine ⟨fun hc' => absurd (hcw.1 hc') (by simpa using hnc), fun _ => ?_⟩
      exact Or.inr (Or.inl ⟨by rw [hrank, hlenj]; rfl, by rw [hncard, hlenj], ho1,
        outK_sound hR (hc 0 hj) hadd (f1_ofFn ρ hadd) hout1⟩)
    · have hlenj : ((classes (reps.getD k [])).getD 1 []).length = 2 := by
        rw [cls_len k hj, h0]
        rfl
      exfalso
      exact hnot (Or.inl ⟨by rw [hrank, hlenj]; rfl, ho1⟩)
  all_goals
    have hcnt1 : (classes (reps.getD k [])).length = 1 := by
      rw [cls_count k, h0]
      rfl
    obtain rfl : j = 0 := by omega
    have ho1 : componentOrbitLength ρ (classSet ((classes (reps.getD k [])).getD 0 [])) = 1 := by
      rw [(horb 0 hj).1]
      exact orbitLen_one (by rw [hπlen, hcnt1])
        (by have := permK_lt hperm (i := 0) (by rw [hπlen, hcnt1]; omega); omega)
  ·
    have hlenj : ((classes (reps.getD k [])).getD 0 []).length = 24 := by
      rw [cls_len k hj, h0]
      rfl
    have hD := rowK_two hr
    unfold rowD4 at hD
    rcases bIf_cases hD with ⟨hcwT, hW⟩ | ⟨hcwF, hT⟩
    · obtain ⟨ho, hi2⟩ := bAnd_true hW
      refine ⟨fun _ => Or.inr (Or.inl ⟨by rw [hrank, hlenj]; rfl, by rw [hncard, hlenj], ho1,
        outK_sound hR (hc 0 hj) hadd (f1_ofFn ρ hadd) ho,
        inK_sound hR (hc 0 hj) (iterate_add_hom ρ hadd 2) (f2_ofFn ρ hadd) hi2⟩),
        fun hn => absurd (hcw.2 hcwT) hn⟩
    · refine ⟨fun hc' => absurd (hcw.1 hc') (by rw [hcwF]; decide), fun _ => ?_⟩
      rcases bIf_cases hT with ⟨hi1, -⟩ | ⟨-, hoo⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by rw [hrank, hlenj]; rfl,
          by rw [hncard, hlenj], ho1, inK_sound hR (hc 0 hj) hadd (f1_ofFn ρ hadd) hi1⟩))))
      · obtain ⟨ho, ho2⟩ := bAnd_true hoo
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by rw [hrank, hlenj]; rfl,
          by rw [hncard, hlenj], ho1, outK_sound hR (hc 0 hj) hadd (f1_ofFn ρ hadd) ho,
          outK_sound hR (hc 0 hj) (iterate_add_hom ρ hadd 2) (f2_ofFn ρ hadd) ho2⟩))))
  ·
    have hlenj : ((classes (reps.getD k [])).getD 0 []).length = 30 := by
      rw [cls_len k hj, h0]
      rfl
    rcases bIf_cases (rowK_three hr) with ⟨hcwT, hi1⟩ | ⟨hcwF, ho⟩
    · exact ⟨fun _ => Or.inl ⟨by rw [hrank, hlenj]; rfl, by rw [hncard, hlenj], ho1,
        inK_sound hR (hc 0 hj) hadd (f1_ofFn ρ hadd) hi1⟩, fun hn => absurd (hcw.2 hcwT) hn⟩
    · refine ⟨fun hc' => absurd (hcw.1 hc') (by rw [hcwF]; decide), fun _ => ?_⟩
      exact Or.inr (Or.inr (Or.inl ⟨by rw [hrank, hlenj]; rfl, by rw [hncard, hlenj], ho1,
        outK_sound hR (hc 0 hj) hadd (f1_ofFn ρ hadd) ho⟩))
  ·
    have hlenj : ((classes (reps.getD k [])).getD 0 []).length = 40 := by
      rw [cls_len k hj, h0]
      rfl
    have hD := rowK_four hr
    rw [Bool.and_eq_true] at hD
    obtain ⟨hnc, hout1⟩ := hD
    refine ⟨fun hc' => absurd (hcw.1 hc') (by simpa using hnc), fun _ => ?_⟩
    exact Or.inl ⟨by rw [hrank, hlenj]; rfl, by rw [hncard, hlenj], ho1,
      outK_sound hR (hc 0 hj) hadd (f1_ofFn ρ hadd) hout1⟩

end CFSG.KC.E6TT

end
