module

public import Certificates.Certificate9587
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterElem

public section

namespace CFSG.AGLEmbedding.ChevOuter

open CFSG.Quasithin CFSG.AGLEmbedding.D4Two CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.Open

instance : Finite (MulAut lineGroup) :=
  Finite.of_injective (fun f : MulAut lineGroup => (f : lineGroup → lineGroup))
    DFunLike.coe_injective

theorem lineGroup_induction {P : lineGroup → Prop} (hl : ∀ k < 18, P (letterX k)) (h1 : P 1)
    (hm : ∀ a b, P a → P b → P (a * b)) (hi : ∀ a, P a → P a⁻¹) : ∀ g, P g := by
  rintro ⟨g, hg⟩
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, hk, rfl⟩ := hy
    have hk' : k < 18 := hk
    have : (⟨letterGL k, Subgroup.subset_closure ⟨k, hk, rfl⟩⟩ : lineGroup) = letterX k := by
      simp [letterX, hk']
    rw [this]
    exact hl k hk'
  | one => exact h1
  | mul y z hy hz ihy ihz => exact hm ⟨y, hy⟩ ⟨z, hz⟩ ihy ihz
  | inv y hy ihy => exact hi ⟨y, hy⟩ ihy

@[expose] noncomputable def d42a (i : ℕ) : MulAut lineGroup := wordAut (d42E.getD i [])

@[expose] noncomputable def d42n (j : ℕ) : MulAut lineGroup := wordAut (d42N.getD j [])

@[expose] noncomputable def d42nInv (j : ℕ) : MulAut lineGroup :=
  wordAut (invWord (d42N.getD j []))

@[expose] noncomputable def d42Group : Subgroup (MulAut lineGroup) :=
  Subgroup.closure {d42a 0, d42a 1, d42a 2}

theorem rep_a (i : ℕ) : Rep (d42eP i) (d42a i) := rep_wordP _

theorem rep_n (j : ℕ) : Rep (d42nP j) (d42n j) := rep_wordP _

theorem rep_nInv (j : ℕ) : Rep (d42nInvP j) (d42nInv j) := rep_wordP _

theorem rep_slpElt {i : ℕ} (hi : i < 2 * (d42N1 + d42N2)) :
    Rep (d42slpElt i) (if i % 2 = 0 then d42n (i / 2) else d42nInv (i / 2)) := by
  have hj : i / 2 < d42N1 + d42N2 := by omega
  by_cases h : i % 2 = 0
  · simp only [d42slpElt, h, ite_true]
    have : d42nList.getD (i / 2) oneP = d42nP (i / 2) := by
      simp [d42nList, List.getD_eq_getElem?_getD, hj]
    rw [this]
    exact rep_n _
  · simp only [d42slpElt, h, ite_false]
    have : d42nInvList.getD (i / 2) oneP = d42nInvP (i / 2) := by
      simp [d42nInvList, List.getD_eq_getElem?_getD, hj]
    rw [this]
    exact rep_nInv _

theorem rep_slpP {ids : List ℕ} (hids : ∀ i ∈ ids, i < 2 * (d42N1 + d42N2)) {acc : Pr}
    {α : MulAut lineGroup} (hacc : Rep acc α) :
    Rep (ids.foldl (fun acc i => mulP acc (d42slpElt i)) acc)
      (α * (ids.map fun i => if i % 2 = 0 then d42n (i / 2) else d42nInv (i / 2)).prod) := by
  induction ids generalizing acc α with
  | nil => simpa using hacc
  | cons i ids ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    rw [← mul_assoc]
    exact ih (fun j hj => hids j (List.mem_cons_of_mem i hj))
      (rep_mul hacc (rep_slpElt (hids i List.mem_cons_self)))

theorem conj_mem_closure_of_rep {pn pn' pg px py : Pr} {n n' g x y : MulAut lineGroup}
    (hn : Rep pn n) (hn' : Rep pn' n') (hg : Rep pg g) (hx : Rep px x) (hy : Rep py y)
    (hnn : n * n' = 1) {s t : ℕ}
    (h : mulP (mulP pn pg) pn' = mulP (powP px s) (powP py t)) :
    n * g * n⁻¹ ∈ Subgroup.closure {x, y} := by
  have h1 := rep_ext (rep_mul (rep_mul hn hg) hn') (rep_mul (rep_powP hx s) (rep_powP hy t)) h
  rw [eq_inv_of_mul_eq_one_right hnn] at h1
  rw [h1]
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

theorem d42_front (hZ : Subgroup.center lineGroup = ⊥) (h : D42Check) :
    (∀ i, i < 3 → d42a i ^ 3 = 1) ∧ Commute (d42a 0) (d42a 1) ∧ Commute (d42a 0) (d42a 2) ∧
      Commute (d42a 1) (d42a 2) ∧ ∀ a b c : ℕ, a < 3 → b < 3 → c < 3 →
        d42a 0 ^ a * d42a 1 ^ b * d42a 2 ^ c = 1 → a = 0 ∧ b = 0 ∧ c = 0 := by
  obtain ⟨hcube, hc01, hc02, hc12, hind, -⟩ := h
  refine ⟨fun i hi => rep_ext (rep_powP (rep_a i) 3) rep_oneP (hcube i (List.mem_range.2 hi)),
    rep_ext (rep_mul (rep_a 0) (rep_a 1)) (rep_mul (rep_a 1) (rep_a 0)) hc01,
    rep_ext (rep_mul (rep_a 0) (rep_a 2)) (rep_mul (rep_a 2) (rep_a 0)) hc02,
    rep_ext (rep_mul (rep_a 1) (rep_a 2)) (rep_mul (rep_a 2) (rep_a 1)) hc12, ?_⟩
  intro a b c ha hb hc h1
  rcases hind a (List.mem_range.2 ha) b (List.mem_range.2 hb) c (List.mem_range.2 hc) with h2 | h2
  · exact h2
  · exfalso
    apply h2
    have hrep := rep_mul (rep_mul (rep_powP (rep_a 0) a) (rep_powP (rep_a 1) b))
      (rep_powP (rep_a 2) c)
    rw [h1] at hrep
    exact rep_one hZ hrep

theorem d42Group_facts (hZ : Subgroup.center lineGroup = ⊥) (h : D42Check) :
    IsMulCommutative d42Group ∧ (∀ g ∈ d42Group, g ^ 3 = 1) ∧ Nat.card d42Group = 3 ^ 3 := by
  obtain ⟨ha3, h01, h02, h12, hind3⟩ := d42_front hZ h
  exact closure_triple (d42a 0) (d42a 1) (d42a 2) (ha3 0 (by norm_num)) (ha3 1 (by norm_num))
    (ha3 2 (by norm_num)) h01 h02 h12 hind3

theorem inn_le_weakCore_of_check (hZ : Subgroup.center lineGroup = ⊥) (h : D42Check)
    {R : Subgroup (MulAut lineGroup)} (hR : d42Group ≤ R) :
    (MulAut.conj : lineGroup →* MulAut lineGroup).range ≤ GLBWeakCore 3 R := by
  obtain ⟨ha3, h01, h02, h12, hind3⟩ := d42_front hZ h
  obtain ⟨hEc, hE3, hEcard⟩ := d42Group_facts hZ h
  obtain ⟨-, hc01, hc02, hc12, hind, hinv, hfam1, hfam2, hslp, hcov⟩ := h
  have hind01 : ∀ a b : ℕ, a < 3 → b < 3 → d42a 0 ^ a * d42a 1 ^ b = 1 → a = 0 ∧ b = 0 := by
    intro a b ha hb h1
    obtain ⟨h2, h3, -⟩ := hind3 a b 0 ha hb (by norm_num) (by simpa using h1)
    exact ⟨h2, h3⟩
  have hind02 : ∀ a b : ℕ, a < 3 → b < 3 → d42a 0 ^ a * d42a 2 ^ b = 1 → a = 0 ∧ b = 0 := by
    intro a b ha hb h1
    obtain ⟨h2, -, h3⟩ := hind3 a 0 b ha (by norm_num) hb (by simpa using h1)
    exact ⟨h2, h3⟩
  obtain ⟨-, -, hF1card⟩ := closure_pair (d42a 0) (d42a 1) (ha3 0 (by norm_num))
    (ha3 1 (by norm_num)) h01 hind01
  obtain ⟨-, -, hF2card⟩ := closure_pair (d42a 0) (d42a 2) (ha3 0 (by norm_num))
    (ha3 2 (by norm_num)) h02 hind02
  have hF1E : Subgroup.closure {d42a 0, d42a 1} ≤ d42Group :=
    Subgroup.closure_mono (Set.insert_subset_iff.2 ⟨Set.mem_insert _ _,
      Set.singleton_subset_iff.2 (Set.mem_insert_of_mem _ (Set.mem_insert _ _))⟩)
  have hF2E : Subgroup.closure {d42a 0, d42a 2} ≤ d42Group :=
    Subgroup.closure_mono (Set.insert_subset_iff.2 ⟨Set.mem_insert _ _,
      Set.singleton_subset_iff.2 (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))⟩)
  have hnn : ∀ j, j < d42N1 + d42N2 → d42n j * d42nInv j = 1 := fun j hj =>
    rep_ext (rep_mul (rep_n j) (rep_nInv j)) rep_oneP (hinv j (List.mem_range.2 hj))
  have hΓ : ∀ j, j < d42N1 + d42N2 → d42n j ∈ GLBWeakCore 3 R := by
    intro j hj
    by_cases hj1 : j < d42N1
    · have hm : d42n j ∈ Subgroup.normalizer
          ((Subgroup.closure {d42a 0, d42a 1} : Subgroup (MulAut lineGroup)) :
            Set (MulAut lineGroup)) := by
        apply mem_normalizer_of_conj_mem
        apply conj_mem_of_gens (S := {d42a 0, d42a 1})
        intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · obtain ⟨s', -, t', -, hst⟩ := hfam1 j (List.mem_range.2 hj1) 0 (by simp)
          exact conj_mem_closure_of_rep (rep_n j) (rep_nInv j) (rep_a 0) (rep_a 0) (rep_a 1)
            (hnn j hj) hst
        · obtain ⟨s', -, t', -, hst⟩ := hfam1 j (List.mem_range.2 hj1) 1 (by simp)
          exact conj_mem_closure_of_rep (rep_n j) (rep_nInv j) (rep_a 1) (rep_a 0) (rep_a 1)
            (hnn j hj) hst
      exact normalizer_le_weakCore_of_E27 hR hEc hE3 hEcard hF1E hF1card hm
    · obtain ⟨j', rfl⟩ : ∃ j', j = d42N1 + j' := ⟨j - d42N1, by omega⟩
      have hj2 : j' < d42N2 := by omega
      have hm : d42n (d42N1 + j') ∈ Subgroup.normalizer
          ((Subgroup.closure {d42a 0, d42a 2} : Subgroup (MulAut lineGroup)) :
            Set (MulAut lineGroup)) := by
        apply mem_normalizer_of_conj_mem
        apply conj_mem_of_gens (S := {d42a 0, d42a 2})
        intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · obtain ⟨s', -, t', -, hst⟩ := hfam2 j' (List.mem_range.2 hj2) 0 (by simp)
          exact conj_mem_closure_of_rep (rep_n (d42N1 + j')) (rep_nInv (d42N1 + j')) (rep_a 0)
            (rep_a 0) (rep_a 2) (hnn _ hj) hst
        · obtain ⟨s', -, t', -, hst⟩ := hfam2 j' (List.mem_range.2 hj2) 2 (by simp)
          exact conj_mem_closure_of_rep (rep_n (d42N1 + j')) (rep_nInv (d42N1 + j')) (rep_a 2)
            (rep_a 0) (rep_a 2) (hnn _ hj) hst
      exact normalizer_le_weakCore_of_E27 hR hEc hE3 hEcard hF2E hF2card hm
  have hΓinv : ∀ j, j < d42N1 + d42N2 → d42nInv j ∈ GLBWeakCore 3 R := fun j hj => by
    rw [eq_inv_of_mul_eq_one_right (hnn j hj)]
    exact Subgroup.inv_mem _ (hΓ j hj)
  have hletter : ∀ k, k < 18 → MulAut.conj (letterX k) ∈ GLBWeakCore 3 R := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := hcov k (List.mem_range.2 hk)
    obtain ⟨hbound, hprod⟩ := hslp x hx
    have hrep := rep_slpP hbound rep_oneP
    have hsym : Rep (letterArr x.1, 0) (MulAut.conj (letterX x.1)) := by
      have := rep_sym x.1
      simpa [symP, hk] using this
    have heq := rep_ext hrep hsym hprod
    rw [← heq, one_mul]
    refine Subgroup.list_prod_mem _ fun a ha => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
    have hi' := hbound i hi
    by_cases hev : i % 2 = 0
    · simp only [hev, ite_true]
      exact hΓ _ (by omega)
    · simp only [hev, ite_false]
      exact hΓinv _ (by omega)
  rintro _ ⟨g, rfl⟩
  exact lineGroup_induction (P := fun g => MulAut.conj g ∈ GLBWeakCore 3 R) hletter
    (by simp) (fun a b ha hb => by rw [map_mul]; exact Subgroup.mul_mem _ ha hb)
    (fun a ha => by rw [map_inv]; exact Subgroup.inv_mem _ ha) g

theorem inn_le_weakCore (hZ : Subgroup.center lineGroup = ⊥)
    {R : Subgroup (MulAut lineGroup)} (hR : d42Group ≤ R) :
    (MulAut.conj : lineGroup →* MulAut lineGroup).range ≤ GLBWeakCore 3 R :=
  inn_le_weakCore_of_check hZ Certificates.certificate9587 hR

end CFSG.AGLEmbedding.ChevOuter
