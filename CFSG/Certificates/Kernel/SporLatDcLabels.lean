module

public import CFSG.Certificates.Kernel.SporLatDcMem

public section

namespace CFSG.KC.SLDc

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F

namespace DcSoundCtx

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]

variable (P : DcSoundCtx Γ n)

private theorem labF_eq_lab_of {x : List ℕ} (hx : ∀ p ∈ x, p < n) {w : List ℕ}
    (hw : ∀ l ∈ w, l < 2 + P.C.ns) :
    labF (wordF P.C.L w) x = lab n ptLab x (evalElt P.els w) := by
  have h1 : lab n ptLab x (evalElt P.els w) =
      sortN (x.map fun p => act n (evalElt P.els w) p) := ptAct_tab _ _
  rw [labF, h1, sortN_eq]
  congr 1
  exact List.map_congr_left fun p hp => (P.act_wordF_eq hw (hx p hp)).symm

theorem wordF_append (w₁ w₂ : List ℕ) (p : ℕ) :
    wordF P.C.L (w₁ ++ w₂) p = wordF P.C.L w₁ (wordF P.C.L w₂ p) := by
  simp [wordF, List.foldr_append]

theorem act_inj {g : Γ} {p q : ℕ} (hp : p < n) (hq : q < n)
    (h : act n g p = act n g q) : p = q := by
  have e1 : (g • (⟨p, hp⟩ : Fin n)) = (g • (⟨q, hq⟩ : Fin n)) := by
    apply Fin.ext
    exact (act_eq g ⟨p, hp⟩).symm.trans (h.trans (act_eq g ⟨q, hq⟩))
  have h2 := MulAction.injective g e1
  simpa using h2

theorem lab_toFinset {x : List ℕ} (g : Γ) :
    (lab n ptLab x g).toFinset = x.toFinset.image (fun p => act n g p) := by
  have h1 : lab n ptLab x g = sortN (x.map fun p => act n g p) := ptAct_tab _ _
  rw [h1, sortN_toFinset]
  ext q
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]

theorem lab_lt {x : List ℕ} (hx : ∀ p ∈ x, p < n) (g : Γ) :
    ∀ p ∈ lab n ptLab x g, p < n := by
  intro p hp
  rw [← List.mem_toFinset, lab_toFinset] at hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  rw [List.mem_toFinset] at hq
  exact act_lt g (hx q hq)

theorem lab_nodup {x : List ℕ} (hx : ∀ p ∈ x, p < n) (hnd : x.Nodup) (g : Γ) :
    (lab n ptLab x g).Nodup := by
  have h1 : lab n ptLab x g = sortN (x.map fun p => act n g p) := ptAct_tab _ _
  rw [h1]
  change ((x.map fun p => act n g p).mergeSort (fun a b => decide (a ≤ b))).Nodup
  rw [List.nodup_mergeSort]
  exact List.Nodup.map_on (fun p hp q hq h => act_inj (Γ := Γ) (g := g) (hx p hp) (hx q hq) h) hnd

theorem lab_valid {x : List ℕ} (hx : ∀ p ∈ x, p < n) (g : Γ) :
    PtValid n (lab n ptLab x g) := by
  refine ⟨sortN_sorted _, ?_⟩
  have h1 : lab n ptLab x g = sortN (x.map fun p => act n g p) := ptAct_tab _ _
  rw [h1]
  intro p hp
  rw [mem_sortN] at hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact act_lt g (hx q hq)

@[expose] noncomputable def Oj (j : ℕ) : Finset ℕ :=
  ((List.range n).filter (fun p => Nat.beq (oid P.D p) j)).toFinset

theorem mem_Oj {j p : ℕ} : p ∈ P.Oj j ↔ p < n ∧ oid P.D p = j := by
  rw [Oj, List.mem_toFinset, List.mem_filter, List.mem_range, Nat.beq_eq]

theorem Oj_card {j : ℕ} (hj : j < P.D.obase.length) : (P.Oj j).card = P.D.osz.getD j 0 := by
  rw [Oj, List.toFinset_card_of_nodup (List.Nodup.filter _ List.nodup_range),
    ← cntB_eq_length_filter, ← osz_eq_cntB P hj]

private theorem Oj_inv {j : ℕ} {s : Γ} (hs : s ∈ P.S) {p : ℕ} (hp : p < n) :
    act n s p ∈ P.Oj j ↔ p ∈ P.Oj j := by
  rw [mem_Oj, mem_Oj, P.oid_inv hs hp]
  exact ⟨fun h => ⟨hp, h.2⟩, fun h => ⟨act_lt s hp, h.2⟩⟩

private theorem Oj_inv_iff {j : ℕ} {s : Γ} (hs : s ∈ P.S) {p : ℕ} (hp : p < n) :
    act n s p ∈ P.Oj j ↔ oid P.D p = j := by
  rw [Oj_inv P hs hp, mem_Oj]
  exact ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩

theorem filter_card_eq_cntO {x : List ℕ} (hnd : x.Nodup) (j : ℕ) :
    (x.toFinset.filter (fun p => oid P.D p = j)).card = cntO P.D x j := by
  rw [cntO, cntB_eq_length_filter]
  rw [← List.toFinset_card_of_nodup (List.Nodup.filter (fun p => Nat.beq (oid P.D p) j) hnd),
    List.toFinset_filter]
  congr 1

theorem card_inter_Oj {x : List ℕ} (hx : ∀ p ∈ x, p < n) (hnd : x.Nodup) {s : Γ}
    (hs : s ∈ P.S) (j : ℕ) :
    ((lab n ptLab x s).toFinset ∩ P.Oj j).card =
      (x.toFinset.filter (fun p => oid P.D p = j)).card := by
  rw [lab_toFinset]
  have himg : (x.toFinset.image (fun p => act n s p)) ∩ P.Oj j =
      (x.toFinset.filter (fun p => act n s p ∈ P.Oj j)).image (fun p => act n s p) := by
    ext M
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hM⟩
      exact ⟨p, ⟨hp, hM⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hpOj⟩, rfl⟩
      exact ⟨⟨p, hp, rfl⟩, hpOj⟩
  rw [himg, Finset.card_image_of_injOn]
  · congr 1
    refine Finset.filter_congr ?_
    intro p hp
    have hp' : p < n := hx p (List.mem_toFinset.mp hp)
    exact Oj_inv_iff P hs hp'
  · rintro p hp q hq h
    have hp' : p < n := by
      have h : p ∈ x.toFinset ∧ act n s p ∈ P.Oj j := by simpa using hp
      exact hx p (List.mem_toFinset.mp h.1)
    have hq' : q < n := by
      have h : q ∈ x.toFinset ∧ act n s q ∈ P.Oj j := by simpa using hq
      exact hx q (List.mem_toFinset.mp h.1)
    exact act_inj hp' hq' h

@[expose] noncomputable def Sx (x : List ℕ) : Finset (List ℕ) := by
  classical
  letI : Fintype ↥P.S := Fintype.ofFinite _
  exact Finset.univ.image (fun s : P.S => lab n ptLab x (s : Γ))

theorem mem_Sx {x : List ℕ} {M : List ℕ} :
    M ∈ P.Sx x ↔ ∃ s ∈ P.S, M = lab n ptLab x s := by
  classical
  letI : Fintype ↥P.S := Fintype.ofFinite _
  rw [Sx, Finset.mem_image]
  constructor
  · rintro ⟨s, -, rfl⟩
    exact ⟨s, s.2, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, Finset.mem_univ _, rfl⟩

theorem Sx_lt {x : List ℕ} (hx : ∀ p ∈ x, p < n) {M : List ℕ} (hM : M ∈ P.Sx x) :
    ∀ p ∈ M, p < n := by
  rw [mem_Sx] at hM
  obtain ⟨s, -, rfl⟩ := hM
  exact lab_lt hx s

private theorem Sx_valid {x : List ℕ} (hx : ∀ p ∈ x, p < n) {M : List ℕ} (hM : M ∈ P.Sx x) :
    PtValid n M := by
  rw [mem_Sx] at hM
  obtain ⟨s, -, rfl⟩ := hM
  exact lab_valid hx s

private theorem Sx_nodup {x : List ℕ} (hx : ∀ p ∈ x, p < n) (hnd : x.Nodup) {M : List ℕ}
    (hM : M ∈ P.Sx x) : M.Nodup := by
  rw [mem_Sx] at hM
  obtain ⟨s, -, rfl⟩ := hM
  exact lab_nodup hx hnd s

theorem card_Sx_inter {x : List ℕ} (hx : ∀ p ∈ x, p < n) (hnd : x.Nodup) {j : ℕ}
    {M : List ℕ} (hM : M ∈ P.Sx x) : (M.toFinset ∩ P.Oj j).card = cntO P.D x j := by
  rw [mem_Sx] at hM
  obtain ⟨s, hs, rfl⟩ := hM
  rw [card_inter_Oj P hx hnd hs, filter_card_eq_cntO P hnd]

end DcSoundCtx

end CFSG.KC.SLDc

end
