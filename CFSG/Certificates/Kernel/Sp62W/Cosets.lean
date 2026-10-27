module

public import Certificates.Data.Kernel.Sp62W.Cosets
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalTab
public import CFSG.Quasithin.H13.L32NKGSp6Group

public section

namespace CFSG.KC.Sp62W

open CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.KD.Sp62W CFSG.KGroups.Sp6
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.H13

@[expose] noncomputable def qOf (x : H6) : ℕ := qbits (KGSp6.colsOf (mat6 x))

theorem rep_cols (x : H6) : Rep x (KGSp6.colsOf (mat6 x)) :=
  ⟨KGSp6.validC_colsOf _, (KGSp6.decodeC_colsOf _).symm⟩

theorem qOf_eq {x : H6} {c : List ℕ} (h : Rep x c) : qOf x = qbits c := by
  rw [qOf, ((rep_cols x).eq_iff h).1 rfl]

theorem qbits_map {f : ℕ → ℕ} (hf : ∀ y < 64, qv (f y) = qv y) {c : List ℕ}
    (hc : KGCert.ValidC c) : qbits (c.map f) = qbits c := by
  obtain ⟨hlen, hlt⟩ := hc
  match c, hlen with
  | [a0, a1, a2, a3, a4, a5], _ =>
    have h0 := hf a0 (hlt a0 (by simp))
    have h1 := hf a1 (hlt a1 (by simp))
    have h2 := hf a2 (hlt a2 (by simp))
    have h3 := hf a3 (hlt a3 (by simp))
    have h4 := hf a4 (hlt a4 (by simp))
    have h5 := hf a5 (hlt a5 (by simp))
    simp only [qbits, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
    rw [h0, h1, h2, h3, h4, h5]

theorem qOf_mul_left (hc : dcCosetsCheck = true) {w : H6} (hw : w ∈ Hgen gensWD) (x : H6) :
    qOf (w * x) = qOf x := by
  simp only [dcCosetsCheck, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨hiso, -⟩, hq⟩, -⟩, -⟩ := hc
  induction hw using Subgroup.closure_induction generalizing x with
  | mem g hg =>
    obtain ⟨c, hcg, rfl⟩ := hg
    rw [qOf_eq ((rep_elt (hiso c hcg)).mul (rep_cols x)), qOf]
    refine qbits_map (fun y hy => ?_) (KGSp6.validC_colsOf _)
    have := hq c hcg
    simp only [qPres, List.all_eq_true, List.mem_range, beq_iff_eq] at this
    exact this y hy
  | one => rw [one_mul]
  | mul a b _ _ ha hb => rw [mul_assoc, ha, hb]
  | inv a _ ha => rw [← ha (a⁻¹ * x), mul_inv_cancel_left]

@[expose] noncomputable def wordE (w : List ℕ) : H6 :=
  w.foldr (fun j acc => elt (gensWD.getD j oneC) * acc) 1

theorem getD_mem_gensWD {j : ℕ} (hj : j < 7) : gensWD.getD j oneC ∈ gensWD := by
  rw [List.getD_eq_getElem _ _ (by simpa [gensWD] using hj)]
  exact List.getElem_mem _

theorem rep_wordE (hiso : ∀ c ∈ gensWD, isoB c = true) :
    ∀ w : List ℕ, (∀ j ∈ w, j < 7) → Rep (wordE w) (wordC w) ∧ wordE w ∈ Hgen gensWD
  | [], _ => ⟨Rep.one, one_mem _⟩
  | j :: w, hw => by
    have hj : j < 7 := hw j (by simp)
    obtain ⟨hr, hm⟩ := rep_wordE hiso w (fun i hi => hw i (by simp [hi]))
    exact ⟨(rep_elt (hiso _ (getD_mem_gensWD hj))).mul hr,
      mul_mem (elt_mem_Hgen (getD_mem_gensWD hj)) hm⟩

@[expose] noncomputable def tE (k : ℕ) : H6 :=
  if k = 0 then 1 else elt cG1 * wordE (dcWords.getD (k - 1) [])

theorem rep_tE (hc : dcCosetsCheck = true) {k : ℕ} (hk : k < 28) :
    Rep (tE k) (dcRep k) ∧ (k ≠ 0 → ∃ h ∈ Hgen gensWD, tE k = elt cG1 * h) := by
  simp only [dcCosetsCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hiso, hg1⟩, -⟩, hidx⟩, -⟩ := hc
  by_cases h0 : k = 0
  · subst h0
    exact ⟨by simpa [tE, dcRep] using Rep.one, fun h => absurd rfl h⟩
  · obtain ⟨hr, hm⟩ := rep_wordE hiso (dcWords.getD (k - 1) []) (hidx _ (by omega))
    refine ⟨?_, fun _ => ⟨_, hm, by simp [tE, h0]⟩⟩
    simpa [tE, dcRep, h0] using (rep_elt hg1).mul hr

theorem double_cosets (hW : Nat.card (Hgen gensWD) = 51840) (hc : dcCosetsCheck = true)
    (x : H6) : x ∈ Hgen gensWD ∨
      ∃ w ∈ Hgen gensWD, ∃ w' ∈ Hgen gensWD, x = w * elt cG1 * w' := by
  have hnd : ((List.range 28).map fun k => qbits (dcRep k)).Nodup := by
    simp only [dcCosetsCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.2
  let φ : Hgen gensWD × Fin 28 → H6 := fun p => p.1 * tE p.2
  have hinj : Function.Injective φ := by
    rintro ⟨w, k⟩ ⟨w', j⟩ h
    have hq : qbits (dcRep k) = qbits (dcRep j) := by
      have := congrArg qOf h
      simp only [φ, qOf_mul_left hc w.2, qOf_mul_left hc w'.2] at this
      rwa [qOf_eq (rep_tE hc k.2).1, qOf_eq (rep_tE hc j.2).1] at this
    have hkj : k = j := Fin.ext (List.inj_on_of_nodup_map hnd (List.mem_range.2 k.2)
      (List.mem_range.2 j.2) hq)
    subst hkj
    exact Prod.ext (Subtype.ext (mul_right_cancel h)) rfl
  have hfin : Finite H6 := Nat.finite_of_card_ne_zero (by rw [card_H6]; norm_num)
  have hcard : Nat.card H6 ≤ Nat.card (Hgen gensWD × Fin 28) := by
    rw [Nat.card_prod, hW, card_H6]
    simp
  obtain ⟨⟨w, k⟩, hx⟩ := (hinj.bijective_of_nat_card_le hcard).2 x
  simp only [φ] at hx
  by_cases hk : (k : ℕ) = 0
  · left
    rw [← hx, tE, if_pos hk, mul_one]
    exact w.2
  · right
    obtain ⟨h, hh, he⟩ := (rep_tE hc k.2).2 hk
    exact ⟨w, w.2, h, hh, by rw [← hx, he, mul_assoc]⟩

end CFSG.KC.Sp62W
