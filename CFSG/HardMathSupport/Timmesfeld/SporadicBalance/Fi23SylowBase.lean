
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Three
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23ThreeInputs

@[expose] public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Sporadic.Fi23 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm
  CFSG.HardMathSupport.Foote.E27 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native

open scoped Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Fi23Sylow

section Tables

@[expose] noncomputable def qG (j : ℕ) : CFSG.Sporadic.Fi23.J := ((qWords[j]!).map (pairG gs)).prod

theorem qLettersT_nil (L : Array Table) : qLettersT L [] = idT 31671 := by
  unfold qLettersT
  exact List.foldr_nil

theorem qLettersT_cons (L : Array Table) (l : ℕ) (w : List ℕ) :
    qLettersT L (l :: w) = compT 31671 L[l]! (qLettersT L w) := by
  unfold qLettersT
  exact List.foldr_cons

theorem rep_qLettersT : ∀ w : List ℕ, (∀ z ∈ w, z < letters.size) →
    Rep 31671 (qLettersT letters w) (w.map (pairG gs)).prod
  | [], _ => by
    rw [qLettersT_nil, List.map_nil, List.prod_nil]
    exact Rep.idT (by norm_num)
  | l :: w, hw => by
    have hl := hw l List.mem_cons_self
    have ih := rep_qLettersT w fun z hz => hw z (List.mem_cons_of_mem _ hz)
    rw [qLettersT_cons, List.map_cons, List.prod_cons]
    exact (rep_pairG_all l hl).compT ih

theorem rep_qGens (hw : ∀ j, (h : j < qWords.size) → ∀ z ∈ qWords[j], z < letters.size) :
    ∀ j < (qGens letters).size, Rep 31671 (qGens letters)[j]! (qG j) := by
  intro j hj
  have hj' : j < qWords.size := by unfold qGens at hj; simpa using hj
  have e : (qGens letters)[j]! = qLettersT letters qWords[j]! := by
    unfold qGens
    rw [getElem!_pos _ j (by simpa using hj'), Array.getElem_map, getElem!_pos qWords j hj']
  rw [e, qG, getElem!_pos qWords j hj']
  exact rep_qLettersT _ (hw j hj')

theorem eq_of_base {x y : CFSG.Sporadic.Fi23.J} (h : ∀ t < 6, idx 31671 x t = idx 31671 y t) : x = y := by
  have hz : ∀ t < 6, idx 31671 (y⁻¹ * x) t = t := by
    intro t ht
    rw [idx_mul, h t ht, ← idx_mul, inv_mul_cancel, idx_one]
  have hlvl : ∀ i ≤ 6, y⁻¹ * x ∈ lvl i := by
    intro i
    induction i with
    | zero => exact fun _ => mem_lvl_zero _
    | succ i ih =>
      intro hi
      have hbase : CFSG.Sporadic.Fi23.Native.chainBase[i]! = i := by
        have : i < 6 := by omega
        interval_cases i <;> rfl
      refine (chain_facts'.2.1 i (by rw [chainBase_size]; omega) _ (ih (by omega))).1 ?_
      rw [hbase]
      exact hz i (by omega)
  have hcard : Nat.card (lvl 6) = 1 := by
    rw [chain_facts'.2.2 6 (by rw [chainBase_size]), chainBase_size]
    simp
  have h1 : y⁻¹ * x = 1 := by
    have := hlvl 6 le_rfl
    rw [Subgroup.card_eq_one.1 hcard] at this
    exact this
  rw [inv_mul_eq_one] at h1
  exact h1.symm

end Tables

section Enumeration

variable {G : Array Table} {P : Array (ℕ × ℕ)} {img : Array ℕ}
  {N : ℕ}

theorem img_spec (hG : ∀ j < G.size, Rep 31671 G[j]! (qG j)) (htree : qTreeOK G P img N = true) :
    ∀ i < N, ∀ t < 6, img[6 * i + t]! = idx 31671 (tabElt qG P i) t := by
  unfold qTreeOK at htree
  rw [Bool.and_eq_true, allIn_eq_true, allIn_eq_true] at htree
  obtain ⟨h0, h1⟩ := htree
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi t ht
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [tabElt_zero, idx_one]
      have := h0 t (Nat.zero_le _) ht
      rw [beq_iff_eq] at this
      simpa using this
    · have hc := h1 i hpos hi
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨hp, hj⟩, hc⟩ := hc
      rw [allIn_eq_true] at hc
      have e := hc t (Nat.zero_le _) ht
      rw [beq_iff_eq] at e
      rw [e, ih _ hp (by omega) t ht, tabElt_succ qG P hp, idx_mul]
      exact hG _ hj _ (idx_lt _ (by omega))

theorem qActPt_spec (hG : ∀ j < G.size, Rep 31671 G[j]! (qG j))
    (htree : qTreeOK G P img N = true) :
    ∀ r < N, ∀ x < 31671, qActPt P G r x = idx 31671 (tabElt qG P r) x := by
  unfold qTreeOK at htree
  rw [Bool.and_eq_true, allIn_eq_true, allIn_eq_true] at htree
  obtain ⟨-, h1⟩ := htree
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr x hx
    rcases Nat.eq_zero_or_pos r with rfl | hpos
    · rw [qActPt, tabElt_zero, idx_one]
      simp
    · have hc := h1 r hpos hr
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨hp, hj⟩, -⟩ := hc
      rw [qActPt, dite_eq_left hp, ih _ hp (by omega) x hx, tabElt_succ qG P hp, idx_mul]
      exact hG _ hj _ (idx_lt _ hx)

theorem qKeyAt_congr {s s' : ℕ} (h : ∀ t < 6, img[s + t]! = img[s' + t]!) :
    qKeyAt img s = qKeyAt img s' := by
  have h0 := h 0 (by norm_num)
  simp only [Nat.add_zero] at h0
  unfold qKeyAt
  rw [h0, h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 4 (by norm_num),
    h 5 (by norm_num)]

theorem tabData_of {L : Array (Array ℕ)} {H : Std.HashMap (UInt64 × UInt64) ℕ}
    (hG : ∀ j < G.size, Rep 31671 G[j]! (qG j)) (hsize : G.size = 3)
    (htree : qTreeOK G P img N = true) (hleft : qLeftOK G L img N = true)
    (hinj : qInjOK H img N = true) : TabData qG P L N 3 := by
  have hspec := img_spec hG htree
  refine ⟨fun i hi0 hi => ?_, fun j hj i hi => ?_, fun i hi k hk he => ?_⟩
  · unfold qTreeOK at htree
    rw [Bool.and_eq_true, allIn_eq_true, allIn_eq_true] at htree
    have hc := htree.2 i hi0 hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨hc.1.1, hsize ▸ hc.1.2⟩
  · unfold qLeftOK at hleft
    rw [allIn_eq_true] at hleft
    have hc := hleft j (Nat.zero_le _) (by omega)
    rw [allIn_eq_true] at hc
    have hc' := hc i (Nat.zero_le _) hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
    obtain ⟨hlt, hc'⟩ := hc'
    rw [allIn_eq_true] at hc'
    refine ⟨hlt, eq_of_base fun t ht => ?_⟩
    have e := hc' t (Nat.zero_le _) ht
    rw [beq_iff_eq, hspec _ hlt t ht, hspec i hi t ht] at e
    rw [idx_mul, e]
    exact (hG j (by omega) _ (idx_lt _ (by omega))).symm
  · unfold qInjOK at hinj
    rw [allIn_eq_true] at hinj
    have hi' := hinj i (Nat.zero_le _) hi
    have hk' := hinj k (Nat.zero_le _) hk
    rw [beq_iff_eq] at hi' hk'
    have hkey : qKeyAt img (6 * i) = qKeyAt img (6 * k) :=
      qKeyAt_congr fun t ht => by rw [hspec i hi t ht, hspec k hk t ht, he]
    rw [← hi', ← hk', hkey]

theorem factorization_three_pow_mul (k m : ℕ) (hm : ¬ 3 ∣ m) :
    (3 ^ k * m).factorization 3 = k := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 3)
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

theorem exists_sylow_of {L : Array (Array ℕ)} (hT : TabData qG P L qN 3) :
    ∃ T : Sylow 3 CFSG.Sporadic.Fi23.J, ∀ x, x ∈ (T : Subgroup CFSG.Sporadic.Fi23.J) ↔ ∃ i < qN, tabElt qG P i = x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, hTx, -⟩ := hT.exists_subgroup (by unfold qN; norm_num)
  have hcard : Nat.card T = 3 ^ (Nat.card CFSG.Sporadic.Fi23.J).factorization 3 := by
    rw [hT.card_subgroup hTx, card_J,
      show (4089470473293004800 : ℕ) = 3 ^ 13 * 2565020057600 by norm_num,
      factorization_three_pow_mul 13 _ (by norm_num)]
    rfl
  exact ⟨Sylow.ofCard T hcard, fun x => by rw [Sylow.coe_ofCard]; exact hTx x⟩

theorem fixed_of_mem {L : Array (Array ℕ)} {lab wit rep : Array ℕ}
    (hG : ∀ j < G.size, Rep 31671 G[j]! (qG j)) (htree : qTreeOK G P img qN = true)
    (hT : TabData qG P L qN 3) (hclass : qClassOK P L qN lab wit rep = true)
    (hfix : qFixOK P G rep fixHint = true) {i : ℕ} (hi : i < qN)
    (h3 : orderOf (tabElt qG P i) = 3) :
    ∃ e ∈ D23, e * tabElt qG P i = tabElt qG P i * e := by
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [tabElt_zero, orderOf_one] at h3
    exact absurd h3 (by norm_num)
  have hcube : tabMul P L i (tabMul P L i i) = 0 := by
    obtain ⟨hl1, e1⟩ := hT.mul i hi i hi
    obtain ⟨hl2, e2⟩ := hT.mul i hi _ hl1
    have hpow : tabElt qG P i ^ 3 = 1 := by
      have := pow_orderOf_eq_one (tabElt qG P i)
      rwa [h3] at this
    have : tabElt qG P (tabMul P L i (tabMul P L i i)) = tabElt qG P 0 := by
      rw [tabElt_zero, ← e2, ← e1, ← hpow, pow_three', mul_assoc]
    exact hT.inj _ hl2 0 (by unfold qN; omega) this
  unfold qClassOK at hclass
  rw [allIn_eq_true] at hclass
  have hc := hclass i (Nat.zero_le _) hi
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  rcases hc with (h0 | h0) | ⟨⟨⟨hl, hw⟩, hr⟩, he⟩
  · exact absurd h0 hi0
  · exact absurd hcube h0
  · set l := lab[i]! with hl'
    set w := wit[i]! with hw'
    set r := rep[l]! with hr'
    obtain ⟨-, e1⟩ := hT.mul _ hw _ hi
    obtain ⟨-, e2⟩ := hT.mul _ hr _ hw
    rw [he] at e1
    have e3 : tabElt qG P w * tabElt qG P i = tabElt qG P r * tabElt qG P w := by
      rw [e1, e2]
    unfold qFixOK at hfix
    rw [allIn_eq_true] at hfix
    have hf := hfix l (Nat.zero_le _) hl
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hf
    obtain ⟨hx, hxe⟩ := hf
    set x := fixHint[l]! with hx'
    rw [qActPt_spec hG htree r hr x hx, idx_of_lt _ hx] at hxe
    have hfx : tabElt qG P r • (⟨x, hx⟩ : Fin 31671) = ⟨x, hx⟩ := Fin.ext hxe
    have hc : tabElt qG P r * conjPt x * (tabElt qG P r)⁻¹ = conjPt x :=
      (smul_eq_iff _ ⟨x, hx⟩ ⟨x, hx⟩).1 hfx
    have hrc : tabElt qG P r * conjPt x = conjPt x * tabElt qG P r := by
      calc tabElt qG P r * conjPt x
          = tabElt qG P r * conjPt x * (tabElt qG P r)⁻¹ * tabElt qG P r := by group
        _ = conjPt x * tabElt qG P r := by rw [hc]
    refine ⟨(tabElt qG P w)⁻¹ * conjPt x * tabElt qG P w, ?_, ?_⟩
    · have hD : conjPt x ∈ D23 := (isConj_d_iff _).2 ⟨⟨x, hx⟩, rfl⟩
      have := D23_conj hD (tabElt qG P w)⁻¹
      simpa using this
    · have hiw : tabElt qG P i = (tabElt qG P w)⁻¹ * tabElt qG P r * tabElt qG P w := by
        rw [mul_assoc, ← e3, inv_mul_cancel_left]
      rw [hiw]
      calc (tabElt qG P w)⁻¹ * conjPt x * tabElt qG P w *
            ((tabElt qG P w)⁻¹ * tabElt qG P r * tabElt qG P w)
          = (tabElt qG P w)⁻¹ * (conjPt x * tabElt qG P r) * tabElt qG P w := by group
        _ = (tabElt qG P w)⁻¹ * (tabElt qG P r * conjPt x) * tabElt qG P w := by rw [hrc]
        _ = (tabElt qG P w)⁻¹ * tabElt qG P r * tabElt qG P w *
            ((tabElt qG P w)⁻¹ * conjPt x * tabElt qG P w) := by group

end Enumeration

section Main

end Main

end Fi23Sylow

open Fi23Sylow

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
