module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD48Real
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterElem
public import Certificates.Certificate9641

public section

namespace CFSG.AGLEmbedding.ChevOuterD48

open CFSG.AGLEmbedding.ChevOuter CFSG.Open

namespace Realization

variable {X : Type} [Group X] (R : Realization X)

@[expose] def ea (i : ℕ) : X := R.wordElt (d48E.getD i [])

@[expose] def Egrp : Subgroup X := Subgroup.closure {R.ea 0, R.ea 1, R.ea 2}

@[expose] def hx (h : ℕ) : X :=
  match h with
  | 0 => R.ea 0
  | 1 => R.ea 0
  | 2 => R.ea 1
  | 3 => R.ea 0 * R.ea 1
  | _ => R.ea 0 * R.ea 1 ^ 2

@[expose] def hy (h : ℕ) : X :=
  match h with
  | 0 => R.ea 1
  | _ => R.ea 2

@[expose] def nel (j : ℕ) : X := R.wordElt (nWord j)

@[expose] def ninv (j : ℕ) : X := R.wordElt (invWord (nWord j))

@[expose] def slpEl (i : ℕ) : X :=
  if i < 2 * numN then (if i % 2 = 0 then R.nel (i / 2) else R.ninv (i / 2))
  else R.letter (i - 2 * numN)

theorem rep_ea (i : ℕ) : R.Rep (eP i) (R.ea i) := R.rep_word _

theorem rep_hx (h : ℕ) : R.Rep (hypX h) (R.hx h) := by
  match h with
  | 0 => exact R.rep_ea 0
  | 1 => exact R.rep_ea 0
  | 2 => exact R.rep_ea 1
  | 3 => exact R.rep_mul (R.rep_ea 0) (R.rep_ea 1)
  | h + 4 => exact R.rep_mul (R.rep_ea 0) (R.rep_pow (R.rep_ea 1) 2)

theorem rep_hy (h : ℕ) : R.Rep (hypY h) (R.hy h) := by
  match h with
  | 0 => exact R.rep_ea 1
  | h + 1 => exact R.rep_ea 2

theorem rep_nel (j : ℕ) : R.Rep (nP j) (R.nel j) := R.rep_word _

theorem rep_ninv (j : ℕ) : R.Rep (nInvP j) (R.ninv j) := R.rep_word _

theorem rep_slpEl {i : ℕ} (hi : i < 2 * numN ∨ (2 * numN ≤ i ∧ i - 2 * numN < 24)) :
    R.Rep (slpElt i) (R.slpEl i) := by
  unfold slpElt slpEl
  by_cases h : i < 2 * numN
  · simp only [h, ite_true]
    have hj : i / 2 < numN := by omega
    by_cases hev : i % 2 = 0
    · simp only [hev, ite_true]
      have : nList.getD (i / 2) oneP = nP (i / 2) := by
        simp [nList, List.getD_eq_getElem?_getD, hj]
      rw [this]
      exact R.rep_nel _
    · simp only [hev, ite_false]
      have : nInvList.getD (i / 2) oneP = nInvP (i / 2) := by
        simp [nInvList, List.getD_eq_getElem?_getD, hj]
      rw [this]
      exact R.rep_ninv _
  · simp only [h, ite_false]
    have hk : i - 2 * numN < 24 := (hi.resolve_left h).2
    have := R.rep_letter hk
    simpa [symP, hk] using this

theorem rep_slpP {ids : List ℕ}
    (hids : ∀ i ∈ ids, i < 2 * numN ∨ (2 * numN ≤ i ∧ i - 2 * numN < 24)) {acc : Pr} {α : X}
    (hacc : R.Rep acc α) :
    R.Rep (ids.foldl (fun acc i => mulP acc (slpElt i)) acc) (α * (ids.map R.slpEl).prod) := by
  induction ids generalizing acc α with
  | nil => simpa using hacc
  | cons i ids ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    rw [← mul_assoc]
    exact ih (fun j hj => hids j (List.mem_cons_of_mem i hj))
      (R.rep_mul hacc (R.rep_slpEl (hids i List.mem_cons_self)))

theorem conj_mem_closure_of_rep {pn pn' pg px py : Pr} {n n' g x y : X}
    (hn : R.Rep pn n) (hn' : R.Rep pn' n') (hg : R.Rep pg g) (hx : R.Rep px x) (hy : R.Rep py y)
    (hnn : n * n' = 1) {s t : ℕ}
    (h : mulP (mulP pn pg) pn' = mulP (powP px s) (powP py t)) :
    n * g * n⁻¹ ∈ Subgroup.closure {x, y} := by
  have h1 := R.rep_ext (R.rep_mul (R.rep_mul hn hg) hn')
    (R.rep_mul (R.rep_pow hx s) (R.rep_pow hy t)) h
  rw [eq_inv_of_mul_eq_one_right hnn] at h1
  rw [h1]
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

theorem eq_one_of_pair_eq {p : Pr} {x : X} (hp : R.Rep p x) (h : p = oneP) : x = 1 :=
  R.rep_ext hp R.rep_one h

theorem pair_eq_of_eq_one {p : Pr} {x : X} (hp : R.Rep p x) (h : x = 1) : p = oneP :=
  R.rep_id (h ▸ hp)

theorem ea_cube (hcube : ∀ i ∈ List.range 3, powP (eP i) 3 = oneP) {i : ℕ} (hi : i < 3) :
    R.ea i ^ 3 = 1 :=
  R.eq_one_of_pair_eq (R.rep_pow (R.rep_ea i) 3) (hcube i (List.mem_range.2 hi))

section Main

variable [Finite X]

theorem egrp_facts (hchk : D48Check) :
    IsMulCommutative R.Egrp ∧ (∀ g ∈ R.Egrp, g ^ 3 = 1) ∧ Nat.card R.Egrp = 3 ^ 3 := by
  obtain ⟨⟨hcube, hc01, hc02, hc12, hind⟩, -⟩ := hchk
  have ha3 : ∀ i, i < 3 → R.ea i ^ 3 = 1 := fun i hi => R.ea_cube hcube hi
  have h01 : Commute (R.ea 0) (R.ea 1) :=
    R.rep_ext (R.rep_mul (R.rep_ea 0) (R.rep_ea 1)) (R.rep_mul (R.rep_ea 1) (R.rep_ea 0)) hc01
  have h02 : Commute (R.ea 0) (R.ea 2) :=
    R.rep_ext (R.rep_mul (R.rep_ea 0) (R.rep_ea 2)) (R.rep_mul (R.rep_ea 2) (R.rep_ea 0)) hc02
  have h12 : Commute (R.ea 1) (R.ea 2) :=
    R.rep_ext (R.rep_mul (R.rep_ea 1) (R.rep_ea 2)) (R.rep_mul (R.rep_ea 2) (R.rep_ea 1)) hc12
  have hind3 : ∀ a b c : ℕ, a < 3 → b < 3 → c < 3 →
      R.ea 0 ^ a * R.ea 1 ^ b * R.ea 2 ^ c = 1 → a = 0 ∧ b = 0 ∧ c = 0 := by
    intro a b c ha hb hc h1
    rcases hind a (List.mem_range.2 ha) b (List.mem_range.2 hb) c (List.mem_range.2 hc) with
      h2 | h2
    · exact h2
    · exfalso
      apply h2
      exact R.pair_eq_of_eq_one (R.rep_mul (R.rep_mul (R.rep_pow (R.rep_ea 0) a)
        (R.rep_pow (R.rep_ea 1) b)) (R.rep_pow (R.rep_ea 2) c)) h1
  exact closure_triple (R.ea 0) (R.ea 1) (R.ea 2) (ha3 0 (by norm_num))
    (ha3 1 (by norm_num)) (ha3 2 (by norm_num)) h01 h02 h12 hind3

theorem letter_mem_weakCore (hchk : D48Check) {Q : Subgroup X} (hQ : R.Egrp ≤ Q) :
    ∀ k, k < 24 → R.letter k ∈ GLBWeakCore 3 Q := by
  obtain ⟨hEc, hE3, hEcard⟩ := R.egrp_facts hchk
  obtain ⟨-, hhyp, hn, hs1, hs2, hcov⟩ := hchk
  have e0 : R.ea 0 ∈ R.Egrp := Subgroup.subset_closure (by simp)
  have e1 : R.ea 1 ∈ R.Egrp := Subgroup.subset_closure (by simp)
  have e2 : R.ea 2 ∈ R.Egrp := Subgroup.subset_closure (by simp)
  have hF : ∀ h, h < 5 → R.hx h ∈ R.Egrp ∧ R.hy h ∈ R.Egrp ∧
      Nat.card (Subgroup.closure {R.hx h, R.hy h}) = 3 ^ 2 := by
    intro h hh
    obtain ⟨hx3, hy3, hcm, hindh⟩ := hhyp h (List.mem_range.2 hh)
    have hxE : R.hx h ∈ R.Egrp := by
      match h with
      | 0 => exact e0
      | 1 => exact e0
      | 2 => exact e1
      | 3 => exact Subgroup.mul_mem _ e0 e1
      | h + 4 => exact Subgroup.mul_mem _ e0 (Subgroup.pow_mem _ e1 2)
    have hyE : R.hy h ∈ R.Egrp := by
      match h with
      | 0 => exact e1
      | h + 1 => exact e2
    refine ⟨hxE, hyE, ?_⟩
    have hx3' : R.hx h ^ 3 = 1 :=
      R.eq_one_of_pair_eq (R.rep_pow (R.rep_hx h) 3) hx3
    have hy3' : R.hy h ^ 3 = 1 :=
      R.eq_one_of_pair_eq (R.rep_pow (R.rep_hy h) 3) hy3
    have hcm' : Commute (R.hx h) (R.hy h) :=
      R.rep_ext (R.rep_mul (R.rep_hx h) (R.rep_hy h)) (R.rep_mul (R.rep_hy h) (R.rep_hx h)) hcm
    have hind2 : ∀ a b : ℕ, a < 3 → b < 3 → R.hx h ^ a * R.hy h ^ b = 1 → a = 0 ∧ b = 0 := by
      intro a b ha hb h1
      rcases hindh a (List.mem_range.2 ha) b (List.mem_range.2 hb) with h2 | h2
      · exact h2
      · exfalso
        apply h2
        exact R.pair_eq_of_eq_one (R.rep_mul (R.rep_pow (R.rep_hx h) a)
          (R.rep_pow (R.rep_hy h) b)) h1
    exact (closure_pair (R.hx h) (R.hy h) hx3' hy3' hcm' hind2).2.2
  have hnn : ∀ j, j < numN → R.nel j * R.ninv j = 1 := fun j hj =>
    R.eq_one_of_pair_eq (R.rep_mul (R.rep_nel j) (R.rep_ninv j))
      (hn j (List.mem_range.2 hj)).2.1
  have hΓ : ∀ j, j < numN → R.nel j ∈ GLBWeakCore 3 Q := by
    intro j hj
    obtain ⟨hh, -, hconj⟩ := hn j (List.mem_range.2 hj)
    obtain ⟨hxE, hyE, hFcard⟩ := hF _ hh
    have hm : R.nel j ∈ Subgroup.normalizer
        ((Subgroup.closure {R.hx (nHyp j), R.hy (nHyp j)} : Subgroup X) : Set X) := by
      apply mem_normalizer_of_conj_mem
      apply conj_mem_of_gens (S := {R.hx (nHyp j), R.hy (nHyp j)})
      intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      · obtain ⟨s', -, t', -, hst⟩ := hconj (hypX (nHyp j)) (by simp)
        exact R.conj_mem_closure_of_rep (R.rep_nel j) (R.rep_ninv j) (R.rep_hx _) (R.rep_hx _)
          (R.rep_hy _) (hnn j hj) hst
      · obtain ⟨s', -, t', -, hst⟩ := hconj (hypY (nHyp j)) (by simp)
        exact R.conj_mem_closure_of_rep (R.rep_nel j) (R.rep_ninv j) (R.rep_hy _) (R.rep_hx _)
          (R.rep_hy _) (hnn j hj) hst
    have hFE : Subgroup.closure {R.hx (nHyp j), R.hy (nHyp j)} ≤ R.Egrp := by
      rw [Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact hxE
      · exact hyE
    exact normalizer_le_weakCore_of_E27 hQ hEc hE3 hEcard hFE hFcard hm
  have hΓinv : ∀ j, j < numN → R.ninv j ∈ GLBWeakCore 3 Q := fun j hj => by
    rw [eq_inv_of_mul_eq_one_right (hnn j hj)]
    exact Subgroup.inv_mem _ (hΓ j hj)
  have hlet1 : ∀ x ∈ d48Slp1, R.letter x.1 ∈ GLBWeakCore 3 Q := by
    intro x hx
    obtain ⟨hk, hids, hprod⟩ := hs1 x hx
    have hrep := R.rep_slpP (ids := x.2) (fun i hi => Or.inl (hids i hi)) R.rep_one
    have hsym : symP x.1 = (letterArr x.1, 0) := by simp [symP, hk]
    have heq := R.rep_ext hrep (R.rep_letter hk) (hprod.trans hsym.symm)
    rw [← heq, one_mul]
    refine Subgroup.list_prod_mem _ fun a ha => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
    have hi' := hids i hi
    unfold Realization.slpEl
    simp only [hi', ite_true]
    by_cases hev : i % 2 = 0
    · simp only [hev, ite_true]
      exact hΓ _ (by omega)
    · simp only [hev, ite_false]
      exact hΓinv _ (by omega)
  have hlet2 : ∀ x ∈ d48Slp2, R.letter x.1 ∈ GLBWeakCore 3 Q := by
    intro x hx
    obtain ⟨hk, hids, hprod⟩ := hs2 x hx
    have hvalid : ∀ i ∈ x.2, i < 2 * numN ∨ (2 * numN ≤ i ∧ i - 2 * numN < 24) := by
      intro i hi
      rcases hids i hi with h | ⟨h1, h2⟩
      · exact Or.inl h
      · obtain ⟨y, hy, hyi⟩ := List.mem_map.1 h2
        exact Or.inr ⟨h1, hyi ▸ (hs1 y hy).1⟩
    have hrep := R.rep_slpP (ids := x.2) hvalid R.rep_one
    have hsym : symP x.1 = (letterArr x.1, 0) := by simp [symP, hk]
    have heq := R.rep_ext hrep (R.rep_letter hk) (hprod.trans hsym.symm)
    rw [← heq, one_mul]
    refine Subgroup.list_prod_mem _ fun a ha => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
    unfold Realization.slpEl
    by_cases hlt : i < 2 * numN
    · simp only [hlt, ite_true]
      by_cases hev : i % 2 = 0
      · simp only [hev, ite_true]
        exact hΓ _ (by omega)
      · simp only [hev, ite_false]
        exact hΓinv _ (by omega)
    · simp only [hlt, ite_false]
      obtain ⟨y, hy, hyi⟩ := List.mem_map.1 ((hids i hi).resolve_left hlt).2
      rw [← hyi]
      exact hlet1 y hy
  intro k hk
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (hcov k (List.mem_range.2 hk))
  rcases List.mem_append.1 hx with h1 | h2
  · exact hlet1 x h1
  · exact hlet2 x h2

theorem letter_mem_weakCore_of_cert {Q : Subgroup X}
    (hQ : R.Egrp ≤ Q) : ∀ k, k < 24 → R.letter k ∈ GLBWeakCore 3 Q :=
  R.letter_mem_weakCore Certificates.certificate9641 hQ

end Main

end Realization

end CFSG.AGLEmbedding.ChevOuterD48
