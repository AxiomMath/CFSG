module

public import CFSG.Certificates.Kernel.Stroth77.MnsBfs

public section

namespace CFSG.KC.Stroth77MN

open Equiv Equiv.Perm CFSG.CGT.Stroth77
open CFSG.KC.Stroth77SP (vb mulK invK conjK rd l16 l32 mem_l16 zval_add zval_lt fin6_lt)

theorem rels_of (h : relOK = true) :
    StrothRel mnsX1 mnsY1 mnsUV mnsT mnsX mnsY mnsU mnsW ∧
    StrothRhoRel mnsX1 mnsY1 mnsUV mnsT mnsX mnsY mnsW mnsU mnsRho ∧
    Stroth21Rel mnsW mnsX mnsY mnsUV mnsT mnsU mnsRho := by
  simp only [relOK, commK, cjI, Bool.and_eq_true, beq_iff_eq] at h
  repeat obtain ⟨h, _⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  all_goals
    try unfold Commute SemiconjBy
    apply encN_injective
    simp only [encN_mul, encN_inv, encN_one, pow_two, pow_three, encN_mnsX1, encN_mnsY1,
      encN_mnsUV, encN_mnsT, encN_mnsX, encN_mnsY, encN_mnsU, encN_mnsW, encN_mnsRho]
    assumption

variable {D : Tabs}

theorem gensE_mem {g : Mns} (h : g ∈ gensE) : g ∈ Eg := Subgroup.subset_closure h

theorem elS_lt16 {c : ℕ} (hc : c < 16) : elS c = ePhiN c := by
  rw [elS_def, Nat.mod_eq_of_lt hc, Nat.div_eq_of_lt hc, Nat.zero_mod, pPhiN_zero, mul_one]

theorem mem_Eg_iff (ht : tabOK D = true) (hc : clOK D = true) {g : Mns} :
    g ∈ Eg ↔ ∃ c < 16, elS c = g := by
  have hcl : closedB D (fun c => decide (c < 16)) = true := by
    simp only [clOK, Bool.and_eq_true] at hc
    exact hc.1.2
  constructor
  · intro hg
    have hle : Eg ≤ subS D (fun c => decide (c < 16)) ht (closed_facts hcl) := by
      refine (Subgroup.closure_le _).2 fun x hx => ?_
      simp only [Set.mem_setOf_eq, gensE, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨1, by norm_num, by decide, elS_1⟩
      · exact ⟨2, by norm_num, by decide, elS_2⟩
      · exact ⟨4, by norm_num, by decide, elS_4⟩
      · exact ⟨8, by norm_num, by decide, elS_8⟩
    obtain ⟨c, -, hc', h⟩ := hle hg
    exact ⟨c, of_decide_eq_true hc', h⟩
  · rintro ⟨c, hc', rfl⟩
    have hE : ∀ g ∈ gensE, g ∈ Eg := fun g hg => gensE_mem hg
    rw [elS_lt16 hc']
    unfold ePhiN
    exact mul_mem (mul_mem (mul_mem (ite_one_mem _ (hE _ (by simp [gensE])))
      (ite_one_mem _ (hE _ (by simp [gensE])))) (ite_one_mem _ (hE _ (by simp [gensE]))))
      (ite_one_mem _ (hE _ (by simp [gensE])))

theorem card_Eg_of (ht : tabOK D = true) (hc : clOK D = true) : Nat.card Eg = 16 :=
  card_of_param elS (fun _ => mem_Eg_iff ht hc) fun _ hk _ hl h =>
    elS_injective ht (by omega) (by omega) h

theorem Eg_le_Qns_of (ht : tabOK D = true) (hc : clOK D = true) : Eg ≤ Qns := by
  intro g hg
  obtain ⟨c, hc', rfl⟩ := (mem_Eg_iff ht hc).1 hg
  rw [mem_Qns, elS_lt16 hc']
  exact ePhiN_perm ht hc'

theorem Eg_eq_Qns_of (ht : tabOK D = true) (hc : clOK D = true) : Eg = Qns :=
  Subgroup.eq_of_le_of_card_ge (Eg_le_Qns_of ht hc) (by rw [card_Eg_of ht hc, card_Qns])

theorem conj_vec {g a : Mns} (ha : a.perm = 1) : (g * a * g⁻¹).vec = nrm (pact g.perm a.vec) := by
  rw [Mns.vec_mul, Mns.vec_mul, Mns.perm_mul, ha, mul_one, Mns.vec_inv, nrm_add_nrm_left,
    nrm_add_pact_nrm, pact_pact_inv]
  funext i
  simp only [nrm_apply, Pi.add_apply]
  generalize pact g.perm a.vec i = u; generalize pact g.perm a.vec 5 = v
  generalize g.vec i = x; generalize g.vec 5 = y
  revert x y u v; decide

theorem conj_coord {g a : Mns} (ha : a.perm = 1) (i : Fin 6) :
    a.vec i + (g * a * g⁻¹).vec (g.perm i) = a.vec 0 + (g * a * g⁻¹).vec (g.perm 0) := by
  have e : ∀ j, g.perm⁻¹ (g.perm j) = j := fun j => by simp
  rw [conj_vec ha]
  simp only [nrm_apply, pact_apply, e]
  generalize a.vec i = p; generalize a.vec 0 = q; generalize a.vec (g.perm⁻¹ 5) = r
  revert p q r; decide

theorem vec_val_bt (z : Mns) (i : Fin 6) : (z.vec i).val = bt (encN z % 32) i.val := by
  obtain ⟨k, hk⟩ := i
  by_cases h5 : k < 5
  · have hv : (z.vec ⟨k, hk⟩).val = encN z / 2 ^ k % 2 := by
      rw [← vb_encN]
      simp only [vb, Fin.val_mk]
      rw [if_pos h5]
    rw [hv]
    simp only [bt, Fin.val_mk]
    interval_cases k <;> omega
  · obtain rfl : k = 5 := by omega
    have h0 : z.vec ⟨5, hk⟩ = 0 := z.vec_five
    rw [h0, ZMod.val_zero]
    simp only [bt, Fin.val_mk]
    omega

theorem pcB_conj {g a : Mns} (ha : a.perm = 1) (i : Fin 6) :
    pcB (encN a % 32) (encN (g * a * g⁻¹) % 32) (g.perm 0).val i.val (g.perm i).val = true := by
  have h := congrArg ZMod.val (conj_coord (g := g) ha i)
  rw [zval_add, zval_add, vec_val_bt, vec_val_bt, vec_val_bt, vec_val_bt, Fin.val_zero] at h
  rw [pcB, h, beq_self_eq_true]

theorem lt4_of_memA (ha : aOK D = true) {c : ℕ} (hc : c < 16) (hm : memA D c = true) : c < 4 := by
  simp only [aOK, Bool.and_eq_true] at ha
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h5⟩, -⟩, -⟩ := ha
  have := List.all_eq_true.1 h5 c (mem_l16 hc)
  rw [beq_iff_eq, hm] at this
  exact of_decide_eq_true this.symm

theorem code_elS1 : encN (elS 1) % 32 = 20 := by rw [encN_elS']; decide +kernel
theorem code_elS2 : encN (elS 2) % 32 = 23 := by rw [encN_elS']; decide +kernel
theorem code_elS3 : encN (elS 3) % 32 = 3 := by rw [encN_elS']; decide +kernel

theorem code_mem_lQ (ht : tabOK D = true) (hc : clOK D = true) (ha : aOK D = true) {z : Mns}
    (hzA : z ∈ Ag) (hzQ : z ∈ Qns) (hz1 : z ≠ 1) : encN z % 32 ∈ lQ := by
  rw [← Eg_eq_Qns_of ht hc] at hzQ
  obtain ⟨c, hc16, rfl⟩ := (mem_Eg_iff ht hc).1 hzQ
  have h4 := lt4_of_memA ha hc16 ((elS_mem_Ag_iff ht hc ha (by omega)).1 hzA)
  interval_cases c
  · exact absurd elS_zero hz1
  · rw [code_elS1]; simp [lQ]
  · rw [code_elS2]; simp [lQ]
  · rw [code_elS3]; simp [lQ]

theorem mem_l6 {q : ℕ} (h : q < 6) : q ∈ l6 := by
  simp only [l6, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem mem_l24 {k : ℕ} (h : k < 24) : k ∈ l24 := by
  simp only [l24, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem fin6_lt6 (x : Fin 6) : x.val < 6 := x.isLt

theorem inj6_of (σ : Perm (Fin 6)) :
    inj6 (σ 0).val (σ 1).val (σ 2).val (σ 3).val (σ 4).val (σ 5).val = true := by
  have h : ∀ i j : Fin 6, i ≠ j → ((σ i).val == (σ j).val) = false := fun i j hij =>
    beq_eq_false_iff_ne.2 fun h => hij (σ.injective (Fin.ext h))
  simp only [inj6, h 0 1 (by decide), h 0 2 (by decide), h 0 3 (by decide), h 0 4 (by decide),
    h 0 5 (by decide), h 1 2 (by decide), h 1 3 (by decide), h 1 4 (by decide), h 1 5 (by decide),
    h 2 3 (by decide), h 2 4 (by decide), h 2 5 (by decide), h 3 4 (by decide), h 3 5 (by decide),
    h 4 5 (by decide), Bool.not_false, Bool.and_self]

theorem perm_eq_of_imCode {a b : Mns} (h : imCode (encN a) = imCode (encN b)) : a.perm = b.perm := by
  rw [imCode_encN, imCode_encN] at h
  simp only [tc] at h
  have a0 := fin6_lt6 (a.perm 0)
  have a1 := fin6_lt6 (a.perm 1)
  have a2 := fin6_lt6 (a.perm 2)
  have a3 := fin6_lt6 (a.perm 3)
  have a4 := fin6_lt6 (a.perm 4)
  have a5 := fin6_lt6 (a.perm 5)
  have b0 := fin6_lt6 (b.perm 0)
  have b1 := fin6_lt6 (b.perm 1)
  have b2 := fin6_lt6 (b.perm 2)
  have b3 := fin6_lt6 (b.perm 3)
  have b4 := fin6_lt6 (b.perm 4)
  have b5 := fin6_lt6 (b.perm 5)
  refine Equiv.ext fun k => Fin.ext ?_
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk] <;> omega

theorem na_facts (h : naOK D = true) :
    (∀ i ∈ l48, rd 10 D.NW i / 32 < 24 ∧
      imCode (mulK (rd 44 D.AF (rd 10 D.NW i % 32)) (rd 44 D.LF (rd 10 D.NW i / 32))) =
        rd 18 D.NPC i) ∧
    ∀ f1 ∈ lQ, ∀ f2 ∈ lQ, ∀ q ∈ l6, ∀ p1 ∈ l6, pc2 f1 f2 q 1 p1 = true → ∀ p2 ∈ l6,
      pc2 f1 f2 q 2 p2 = true → ∀ p3 ∈ l6, pc2 f1 f2 q 3 p3 = true → ∀ p4 ∈ l6,
      pc2 f1 f2 q 4 p4 = true → ∀ p5 ∈ l6, pc2 f1 f2 q 5 p5 = true →
      inj6 q p1 p2 p3 p4 p5 = true → ∃ i ∈ l48, rd 18 D.NPC i = tc q p1 p2 p3 p4 p5 := by
  simp only [naOK, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.any_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  refine ⟨h.1, fun f1 hf1 f2 hf2 q hq p1 h1 c1 p2 h2 c2 p3 h3 c3 p4 h4 c4 p5 h5 c5 hi => ?_⟩
  have ne : ∀ {b : Bool}, b = true → ¬ b = false := fun hb => by rw [hb]; decide
  have r := (((((h.2 f1 hf1 f2 hf2 q hq p1 h1).resolve_left (ne c1) p2 h2).resolve_left (ne c2)
    p3 h3).resolve_left (ne c3) p4 h4).resolve_left (ne c4) p5 h5)
  rcases r with (r | r) | r
  · exact absurd r (ne c5)
  · exact absurd r (ne hi)
  · exact r

theorem pc2_conj (ht : tabOK D = true) (hc : clOK D = true) (ha : aOK D = true) {g : Mns}
    (hx : mnsX1.perm = 1) (hy : mnsY1.perm = 1) (i : Fin 6) :
    pc2 (encN (g * mnsX1 * g⁻¹) % 32) (encN (g * mnsY1 * g⁻¹) % 32) (g.perm 0).val i.val
      (g.perm i).val = true := by
  have h1 := pcB_conj (g := g) hx i
  have h2 := pcB_conj (g := g) hy i
  rw [encN_mnsX1] at h1
  rw [encN_mnsY1] at h2
  rw [pc2, Bool.and_eq_true]
  exact ⟨h1, h2⟩

theorem Eg_le_sup (hb : bfsOK D = true) : Eg ≤ Ag ⊔ Lg := by
  refine (Subgroup.closure_le _).2 fun x hx => ?_
  simp only [Set.mem_setOf_eq, gensE, List.mem_cons, List.not_mem_nil, or_false] at hx
  have hA : ∀ g ∈ gensA, g ∈ Ag ⊔ Lg := fun g hg => Subgroup.mem_sup_left (gensA_mem hg)
  have hL : ∀ g ∈ gensL, g ∈ Ag ⊔ Lg := fun g hg =>
    Subgroup.mem_sup_right (Subgroup.subset_closure hg)
  rcases hx with rfl | rfl | rfl | rfl
  · exact hA _ (by simp [gensA])
  · exact hA _ (by simp [gensA])
  · exact hL _ (by simp [gensL])
  · exact hL _ (by simp [gensL])

theorem normalizer_le_sup (ht : tabOK D = true) (hc : clOK D = true) (ha : aOK D = true)
    (hn : naOK D = true) (hb : bfsOK D = true) : NAg ≤ Ag ⊔ Lg := by
  intro g hg
  have hQ : ∀ z ∈ Eg, z.perm = 1 := fun z hz => mem_Qns.1 (Eg_le_Qns_of ht hc hz)
  have hx : mnsX1.perm = 1 := hQ _ (gensE_mem (by simp [gensE]))
  have hy : mnsY1.perm = 1 := hQ _ (gensE_mem (by simp [gensE]))
  have hconjQ : ∀ {a : Mns}, a.perm = 1 → g * a * g⁻¹ ∈ Qns := fun {a} h => by
    rw [mem_Qns, Mns.perm_mul, Mns.perm_mul, Mns.perm_inv, h, mul_one, mul_inv_cancel]
  have hconjA : ∀ {a : Mns}, a ∈ Ag → g * a * g⁻¹ ∈ Ag := fun {a} h =>
    (Subgroup.mem_set_normalizer_iff.1 hg a).1 h
  have hne : ∀ {a : Mns}, a ≠ 1 → g * a * g⁻¹ ≠ 1 := fun {a} h e => h (by
    rw [mul_inv_eq_one, mul_eq_left] at e
    exact e)
  have hx1 : mnsX1 ≠ 1 := fun e => by
    have := congrArg encN e
    rw [encN_mnsX1, encN_one] at this
    exact absurd this (by decide)
  have hy1 : mnsY1 ≠ 1 := fun e => by
    have := congrArg encN e
    rw [encN_mnsY1, encN_one] at this
    exact absurd this (by decide)
  have hxA : mnsX1 ∈ Ag := gensA_mem (by simp [gensA])
  have hyA : mnsY1 ∈ Ag := gensA_mem (by simp [gensA])
  have f1 := code_mem_lQ ht hc ha (hconjA hxA) (hconjQ hx) (hne hx1)
  have f2 := code_mem_lQ ht hc ha (hconjA hyA) (hconjQ hy) (hne hy1)
  have hpc := pc2_conj ht hc ha (g := g) hx hy
  obtain ⟨i, hi, hNi⟩ := (na_facts hn).2 _ f1 _ f2 _ (mem_l6 (fin6_lt6 _)) _ (mem_l6 (fin6_lt6 _))
    (hpc 1) _ (mem_l6 (fin6_lt6 _)) (hpc 2) _ (mem_l6 (fin6_lt6 _)) (hpc 3) _
    (mem_l6 (fin6_lt6 _)) (hpc 4) _ (mem_l6 (fin6_lt6 _)) (hpc 5) (inj6_of g.perm)
  obtain ⟨hk, hw⟩ := (na_facts hn).1 i hi
  obtain ⟨a, haA, hae⟩ := AF_mem hb (Nat.mod_lt (rd 10 D.NW i) (by norm_num : 0 < 32))
  obtain ⟨l, hlL, hle⟩ := LF_mem hb (mem_l24 hk)
  have hperm : (a * l).perm = g.perm := by
    refine perm_eq_of_imCode ?_
    rw [encN_mul, hae, hle, hw, hNi, imCode_encN]
  have hq : g * (a * l)⁻¹ ∈ Eg := by
    rw [Eg_eq_Qns_of ht hc, mem_Qns, Mns.perm_mul, Mns.perm_inv, hperm, mul_inv_cancel]
  have : g = (g * (a * l)⁻¹) * (a * l) := by group
  rw [this]
  exact mul_mem (Eg_le_sup hb hq)
    (mul_mem (Subgroup.mem_sup_left haA) (Subgroup.mem_sup_right hlL))

theorem Ag_sup_Lg_of (ht : tabOK D = true) (hc : clOK D = true) (ha : aOK D = true)
    (hn : naOK D = true) (hb : bfsOK D = true) : Ag ⊔ Lg = NAg :=
  le_antisymm (sup_le Subgroup.le_normalizer (Lg_le_normalizer_of hb))
    (normalizer_le_sup ht hc ha hn hb)

end CFSG.KC.Stroth77MN
