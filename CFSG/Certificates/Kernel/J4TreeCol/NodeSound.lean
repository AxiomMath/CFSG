module

public import CFSG.Certificates.Kernel.J4TreeCol.MatsSound
public import CFSG.Certificates.Kernel.J4TreeNode.Sound
public import CFSG.Milestones.ASVolI.C31.J4NP.VerdictColNode
public import CFSG.Milestones.ASVolI.C31.J4NP.Is2AGlue
public import CFSG.Milestones.ASVolI.C31.J4NP.VerdictColGen

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.J4TreeCol

open CFSG.KC.J4TreeN CFSG.KC.J4Tree CFSG.KC.J4Q CFSG.KC.Loop CFSG.J4Tree.Native
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.ASVolI

open scoped Classical in
@[expose] noncomputable def labJ (x : J) : ℕ :=
  if x = 1 then 0 else if burnsideJ4NP_Is2A x then 1 else 2

theorem is2A_conj (g x : J) : burnsideJ4NP_Is2A (g * x * g⁻¹) ↔ burnsideJ4NP_Is2A x := by
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨g⁻¹ * h, ?_⟩
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = g⁻¹ * h * CFSG.Quasithin.J4Loc.z0 * (g⁻¹ * h)⁻¹ := by rw [hh]; group
  · rintro ⟨h, rfl⟩
    exact ⟨g * h, by group⟩

theorem conj_eq_one_iff (g x : J) : g * x * g⁻¹ = 1 ↔ x = 1 := by
  constructor
  · intro h
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · rintro rfl
    group

theorem labJ_conj (g x : J) : labJ (g * x * g⁻¹) = labJ x := by
  classical
  unfold labJ
  by_cases h1 : x = 1
  · rw [if_pos h1, if_pos ((conj_eq_one_iff g x).2 h1)]
  · rw [if_neg h1, if_neg (fun h => h1 ((conj_eq_one_iff g x).1 h))]
    by_cases h2 : burnsideJ4NP_Is2A x
    · rw [if_pos h2, if_pos ((is2A_conj g x).2 h2)]
    · rw [if_neg h2, if_neg (fun h => h2 ((is2A_conj g x).1 h))]

@[expose] noncomputable def qProd (x w : J) : ℕ := labJ (x * w)

theorem qProd_conj (g x w : J) : qProd (g * x * g⁻¹) (g * w * g⁻¹) = qProd x w := by
  unfold qProd
  rw [show g * x * g⁻¹ * (g * w * g⁻¹) = g * (x * w) * g⁻¹ by group, labJ_conj]

theorem colPair_symm {x w : J} (h : x * w = w * x) :
    burnsideJ4NP_colPair x w = burnsideJ4NP_colPair w x := by
  unfold burnsideJ4NP_colPair
  have hc : Mx x * Mx w = Mx w * Mx x := by rw [← map_mul, h, map_mul]
  have e : (Mx x - 1) * (Mx w - 1) = (Mx w - 1) * (Mx x - 1) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hc]
    abel
  rw [e]

theorem fld_lt (x w m : ℕ) : fld x w m < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)

theorem labC_lt (D : CRec) (m : ℕ) : labC D m < 4 := fld_lt _ 2 _

theorem qC_lt (D : CRec) (n i j : ℕ) : qC D n i j < 128 := by
  unfold qC
  split_ifs
  · exact Nat.lt_of_lt_of_le (labC_lt D _) (by norm_num)
  · exact fld_lt _ 7 _
  · exact fld_lt _ 7 _

theorem rec_sum (f : ℕ → ℕ) : ∀ k : ℕ,
    Nat.rec (motive := fun _ => ℕ) 0 (fun j acc => acc + f j) k = ∑ j ∈ Finset.range k, f j
  | 0 => rfl
  | k + 1 => by
    rw [Finset.sum_range_succ, ← rec_sum f k]

theorem sigC_eq (D : CRec) (n i : ℕ) :
    sigC D n i = ∑ j ∈ Finset.range n, 2 ^ (10 * (113 * labC D j + qC D n i j)) :=
  rec_sum _ n

theorem sum_eq_of_counts (n : ℕ) (F : ℕ → ℕ → ℕ) (L Q Q' : ℕ → ℕ) (hL : ∀ j, L j < 4)
    (hQ : ∀ j, Q j < 128) (hQ' : ∀ j, Q' j < 128)
    (h : ∀ a b, ((Finset.range n).filter fun j => L j = a ∧ Q j = b).card =
      ((Finset.range n).filter fun j => L j = a ∧ Q' j = b).card) :
    ∑ j ∈ Finset.range n, F (L j) (Q j) = ∑ j ∈ Finset.range n, F (L j) (Q' j) := by
  have key : ∀ Q : ℕ → ℕ, (∀ j, Q j < 128) → ∑ j ∈ Finset.range n, F (L j) (Q j) =
      ∑ t ∈ Finset.range 4 ×ˢ Finset.range 128,
        ((Finset.range n).filter fun j => L j = t.1 ∧ Q j = t.2).card * F t.1 t.2 := by
    intro Q hQ
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun j => (L j, Q j))
      (t := Finset.range 4 ×ˢ Finset.range 128)
      (fun j _ => Finset.mem_product.2 ⟨Finset.mem_range.2 (hL j), Finset.mem_range.2 (hQ j)⟩)]
    refine Finset.sum_congr rfl fun t _ => ?_
    have e : ((Finset.range n).filter fun j => (L j, Q j) = t) =
        ((Finset.range n).filter fun j => L j = t.1 ∧ Q j = t.2) := by
      apply Finset.filter_congr
      intro j _
      exact Prod.ext_iff
    rw [e, ← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 hj
    rw [h1, h2]
  rw [key Q hQ, key Q' hQ']
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [h t.1 t.2]

theorem colCount_eq {bv : ℕ → J} {r : ℕ}
    (hinj : ∀ i < 2 ^ r, ∀ j < 2 ^ r, eta bv r i = eta bv r j → i = j) (hE : Elem bv r)
    (lab : J → ℕ) (q : J → J → ℕ) (L : ℕ → ℕ) (Q : ℕ → ℕ → ℕ)
    (hL : ∀ j < 2 ^ r, lab (eta bv r j) = L j)
    (hQ : ∀ i < 2 ^ r, ∀ j < 2 ^ r, q (eta bv r i) (eta bv r j) = Q i j) {i : ℕ} (hi : i < 2 ^ r)
    (a b : ℕ) :
    burnsideJ4NP_colCount (Eg bv r) lab q (eta bv r i) a b =
      ((Finset.range (2 ^ r)).filter fun j => L j = a ∧ Q i j = b).card := by
  unfold burnsideJ4NP_colCount
  have hset : {w : J | w ∈ Eg bv r ∧ lab w = a ∧ q (eta bv r i) w = b} =
      ↑(((Finset.range (2 ^ r)).filter fun j => L j = a ∧ Q i j = b).image (eta bv r)) := by
    ext w
    simp only [Set.mem_setOf_eq, Finset.coe_image, Finset.coe_filter, Finset.mem_range,
      Set.mem_image]
    constructor
    · rintro ⟨hw, hwa, hwb⟩
      obtain ⟨j, hj, rfl⟩ := (mem_Eg_iff hE).1 hw
      exact ⟨j, ⟨hj, by rw [← hL j hj, hwa], by rw [← hQ i hi j hj, hwb]⟩, rfl⟩
    · rintro ⟨j, ⟨hj, hja, hjb⟩, rfl⟩
      exact ⟨eta_mem_Eg r le_rfl j, by rw [hL j hj, hja], by rw [hQ i hi j hj, hjb]⟩
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injOn]
  intro j hj j' hj' e
  exact hinj j (Finset.mem_range.1 (Finset.mem_filter.1 hj).1) j'
    (Finset.mem_range.1 (Finset.mem_filter.1 hj').1) e

theorem sig_eq_of_counts {bv : ℕ → J} {r : ℕ} {D : CRec}
    (hinj : ∀ i < 2 ^ r, ∀ j < 2 ^ r, eta bv r i = eta bv r j → i = j) (hE : Elem bv r)
    (q : J → J → ℕ) (hL : ∀ j < 2 ^ r, labJ (eta bv r j) = labC D j)
    (hQ : ∀ i < 2 ^ r, ∀ j < 2 ^ r, q (eta bv r i) (eta bv r j) = qC D (2 ^ r) i j)
    {i y : ℕ} (hi : i < 2 ^ r) (hy : y < 2 ^ r)
    (h : ∀ a b, burnsideJ4NP_colCount (Eg bv r) labJ q (eta bv r i) a b =
      burnsideJ4NP_colCount (Eg bv r) labJ q (eta bv r y) a b) :
    sigC D (2 ^ r) i = sigC D (2 ^ r) y := by
  rw [sigC_eq, sigC_eq]
  refine sum_eq_of_counts (2 ^ r) (fun a b => 2 ^ (10 * (113 * a + b))) (labC D)
    (qC D (2 ^ r) i) (qC D (2 ^ r) y) (labC_lt D) (qC_lt D _ i) (qC_lt D _ y) fun a b => ?_
  rw [← colCount_eq hinj hE labJ q (labC D) (qC D (2 ^ r)) hL hQ hi,
    ← colCount_eq hinj hE labJ q (labC D) (qC D (2 ^ r)) hL hQ hy]
  exact h a b

section Codes


@[expose] def PKb (x : J) (X : ℕ) : Prop := PK x X ∧ X < 2 ^ 144

theorem codes_spec {T : Tabs} (hT : tabsOK T = true) {wv : List (ℕ × ℕ)}
    (hco : wv.all coordOK = true) :
    (codesOf (wv.map (ccT T))).length = 2 ^ wv.length ∧ ∀ m < 2 ^ wv.length,
      PKb (eta (bvOf wv) wv.length m) ((codesOf (wv.map (ccT T))).getD m oneK) := by
  have h := dbl_spec PKb M (fun hg hh => ⟨pk_mul hg.1 hh.1, M_lt _ _⟩) (bvOf wv) oneK
    (wv.map (ccT T)) 0 [oneK] rfl (fun m hm => by
      rw [pow_zero] at hm
      obtain rfl : m = 0 := by omega
      rw [eta_zero]
      exact ⟨pk_one, oneK_lt⟩) (fun i hi => by
      rw [List.length_map] at hi
      rw [Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some, bvOf,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact ⟨pk_cc hT (List.all_eq_true.1 hco _ (List.getElem_mem hi)), M_lt _ _⟩)
  rw [Nat.zero_add, List.length_map] at h
  exact h

theorem elem_of_codes {T : Tabs} (hT : tabsOK T = true) {wv : List (ℕ × ℕ)}
    (hco : wv.all coordOK = true)
    (hBc : (wv.map (ccT T)).all (fun b => sqOneK b && (wv.map (ccT T)).all fun b' => commK b b') =
      true) :
    Elem (bvOf wv) wv.length := by
  have hpk : ∀ i (hi : i < wv.length), PK (bvOf wv i) (ccT T (wv[i]'hi)) := by
    intro i hi
    have e : bvOf wv i = burnsideJ4NP_treeElt (wv[i]'hi) := by
      unfold bvOf
      rw [List.getD_eq_getElem _ _ hi]
    rw [e]
    exact pk_cc hT (List.all_eq_true.1 hco _ (List.getElem_mem hi))
  have hmem : ∀ i (hi : i < wv.length), ccT T wv[i] ∈ wv.map (ccT T) :=
    fun i hi => List.mem_map.2 ⟨_, List.getElem_mem hi, rfl⟩
  constructor
  · intro j hj
    have := List.all_eq_true.1 hBc _ (hmem j hj)
    rw [Bool.and_eq_true] at this
    exact (pk_sq (hpk j hj)).2 this.1
  · intro i hi j hj
    have := List.all_eq_true.1 hBc _ (hmem i hi)
    rw [Bool.and_eq_true] at this
    exact (pk_comm (hpk i hi) (hpk j hj)).2 (List.all_eq_true.1 this.2 _ (hmem j hj))


theorem labOK_spec {sx : ℕ} {D : CRec} {X m : ℕ} {w : J} (h : labOK sx D X m = true)
    (hw : PKb w X) (hsq : w * w = 1)
    (hsx : ∀ t < 2048, sx.testBit t = (burnsideJ4NP_sextArr ())[t]?.getD false) :
    labJ w = labC D m ∧ (labC D m = 0 ↔ m = 0) := by
  classical
  unfold labOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  by_cases hm : m = 0
  · subst hm
    have hl : labC D 0 = 0 := by simpa using h2
    have hX : Nat.beq X oneK = true := by simpa using h1
    have hw1 : w = 1 := pk_beq hw.1 pk_one hX
    refine ⟨?_, by simp [hl]⟩
    rw [hl, hw1]
    unfold labJ
    rw [if_pos rfl]
  · have hm0 : (m == 0) = false := Bool.eq_false_iff.2 fun e => hm (beq_iff_eq.1 e)
    have hl : labC D m ≠ 0 := by
      intro e
      rw [e, hm0] at h2
      exact Bool.noConfusion h2
    have hX : Nat.beq X oneK = false := h1.trans hm0
    have hw1 : w ≠ 1 := by
      intro e
      have := pk_canon hw.1 pk_one hw.2 oneK_lt e
      rw [this, Nat.beq_refl] at hX
      exact Bool.noConfusion hX
    refine ⟨?_, by simp [hl, hm]⟩
    have hiff0 := burnsideJ4NP_Is2A_iff_affine_H hw.1.1 hsq hw1
    rw [burnsideJ4NP_affine2A_eq_with, ← burnsideJ4NP_encJ_of_mem hw.1.1] at hiff0
    have hiff : burnsideJ4NP_Is2A w ↔ burnsideJ4NP_treeTest (burnsideJ4NP_encJ w) = true := hiff0
    unfold labJ
    rw [if_neg hw1]
    rcases h3 with (h3 | ⟨hl1, h3⟩) | ⟨hl2, h3⟩
    · exact absurd h3 hl
    · rw [if_pos (hiff.2 (is2AK_spec h3 hw.1.2 hsx)), hl1]
    · have hn := non2AK_spec h3 hw.1.2 hsx
      rw [if_neg (fun h => by rw [hiff.1 h] at hn; exact Bool.noConfusion hn), hl2]

theorem pk_uJ {j : ℕ} (hj : j < 11) : PK (uJ j) (UK.getD j oneK) := by
  have hl := uWord_letters.1 j hj
  have hm : uJ j ∈ Hj := wordProd_mem_Hj hl
  refine ⟨hm, ?_⟩
  rw [burnsideJ4NP_encJ_of_mem hm]
  have e : burnsideJ4NP_enc ⟨uJ j, hm⟩ = codeOfWord (uWord j) := burnsideJ4NP_enc_wordProd hl
  rw [e, burnsideJ4NP_uCode_eq hj]
  exact rc_get u_wf j

theorem pk_kJ {i : ℕ} (hi : i < 4) : PK (kJ i) (KK.getD i oneK) := by
  have hl := kJ_letters hi
  have hm : kJ i ∈ Hj := wordProd_mem_Hj hl
  refine ⟨hm, ?_⟩
  rw [burnsideJ4NP_encJ_of_mem hm]
  have e : burnsideJ4NP_enc ⟨kJ i, hm⟩ = codeOfWord (kWords.getD i []) :=
    burnsideJ4NP_enc_wordProd hl
  rw [e, burnsideJ4NP_kCode_eq hi]
  exact rc_get k_wf i

end Codes

theorem UK_length : UK.length = 11 := by decide

theorem KK_length : KK.length = 4 := by decide

theorem p0Codes_length : p0Codes.length = 15 := by
  rw [p0Codes, List.length_append, List.length_take, List.length_take, UK_length, KK_length]
  rfl

theorem eta_xorSel_mem {G : Type*} [Group G] {u : ℕ → G} {r : ℕ} (h : Elem u r) :
    ∀ (l : List ℕ) (mask : ℕ),
      eta u r (xorSel l mask) ∈ Subgroup.closure ((fun o => eta u r o) '' {o | o ∈ l})
  | [], mask => by
    rw [xorSel, eta_zero]
    exact Subgroup.one_mem _
  | o :: l, mask => by
    rw [xorSel, eta_xor h le_rfl]
    refine Subgroup.mul_mem _ ?_ ?_
    · split_ifs
      · exact Subgroup.subset_closure ⟨o, List.mem_cons_self .., rfl⟩
      · rw [eta_zero]
        exact Subgroup.one_mem _
    · refine Subgroup.closure_mono ?_ (eta_xorSel_mem h l (mask / 2))
      rintro _ ⟨o', ho', rfl⟩
      exact ⟨o', List.mem_cons_of_mem _ ho', rfl⟩

@[expose] def IsJ (m : ℕ) : Prop := ∃ g : J, PRc g m

section Words

variable {G : Mats} (hG : MatsOK G)
include hG

theorem getN_isJ {R : List ℕ} (hR : ∀ t, IsJ (getN G.one R t)) (x : ℕ) (hx : IsJ x) :
    ∀ t, IsJ (getN G.one (x :: R) t)
  | 0 => hx
  | t + 1 => hR t

theorem symJ_isJ {R : List ℕ} (hR : ∀ t, IsJ (getN G.one R t)) (nr s : ℕ) :
    IsJ (symJ G R nr s) := by
  unfold symJ
  split_ifs
  · exact ⟨_, hG.g5 _⟩
  · exact ⟨_, hG.g5i _⟩
  · exact hR _

theorem rulesJ_isJ : ∀ (l R : List ℕ) (nr : ℕ), (∀ t, IsJ (getN G.one R t)) →
    ∀ t, IsJ (getN G.one (rulesJ G l R nr) t)
  | [], R, _, hR => hR
  | x :: l, R, nr, hR => by
    unfold rulesJ
    rw [strictL_eq]
    obtain ⟨g, hg⟩ := symJ_isJ hG hR nr (x % 65536)
    obtain ⟨h, hh⟩ := symJ_isJ hG hR nr (x / 65536)
    exact rulesJ_isJ l _ (nr + 1) (getN_isJ hG hR _ ⟨_, prc_mul hG hg hh⟩)

theorem seqJ_isJ {R : List ℕ} (hR : ∀ t, IsJ (getN G.one R t)) (nr : ℕ) :
    ∀ (f sq acc : ℕ), IsJ acc → IsJ (seqJ G R nr f sq acc)
  | 0, _, _, h => h
  | f + 1, sq, acc, h => by
    unfold seqJ
    split_ifs
    · exact h
    · rw [strictN_eq]
      obtain ⟨g, hg⟩ := h
      obtain ⟨s, hs⟩ := symJ_isJ hG hR nr (sq % 65536)
      exact seqJ_isJ hR nr f _ _ ⟨_, prc_mul hG hg hs⟩

theorem wordE_isJ (D : CRec) :
    IsJ (seqJ G (rulesJ G D.rules [] 0) D.rules.length 4096 D.seq G.one) :=
  seqJ_isJ hG (rulesJ_isJ hG D.rules [] 0 (fun _ => ⟨1, prc_one hG⟩)) _ _ _ _ ⟨1, prc_one hG⟩

theorem p0_prc {s : J} (hs : s ∈ S0) : ∃ t < 15, PRc s ((G.us ++ G.ks).getD t 0) := by
  have hu := hG.us_len
  rcases hs with ⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩
  · refine ⟨j, by omega, ?_⟩
    rw [List.getD_append _ _ _ _ (by omega)]
    have := hG.us j hj
    rw [getN_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
      Option.getD_some] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact this
  · refine ⟨11 + i, by omega, ?_⟩
    rw [List.getD_append_right _ _ _ _ (by omega), hu, Nat.add_sub_cancel_left]
    have := hG.ks i
    have hk := hG.ks_len
    rw [getN_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
      Option.getD_some] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact this

end Words

theorem getD_irrel {α : Type*} {l : List α} {i : ℕ} (hi : i < l.length) (d d' : α) :
    l.getD i d = l.getD i d' := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi]

section Sound


theorem p0_pk {s : J} (hs : s ∈ S0) : ∃ t < 15, PK s (p0Codes.getD t 0) := by
  rcases hs with ⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩
  · refine ⟨j, by omega, ?_⟩
    have h := pk_uJ hj
    rw [p0Codes, List.getD_append _ _ _ _ (by rw [List.length_take, UK_length]; omega),
      List.getD_eq_getElem _ _ (by rw [List.length_take, UK_length]; omega), List.getElem_take,
      ← List.getD_eq_getElem _ oneK]
    exact h
  · refine ⟨11 + i, by omega, ?_⟩
    have h := pk_kJ hi
    rw [p0Codes, List.getD_append_right _ _ _ _ (by rw [List.length_take, UK_length]; omega),
      List.length_take, UK_length, show 11 + i - min 11 11 = i by omega,
      List.getD_eq_getElem _ _ (by rw [List.length_take, KK_length]; omega), List.getElem_take,
      ← List.getD_eq_getElem _ oneK]
    exact h

theorem colNode_sound {G : Mats} {T : Tabs} {D : CRec} (hG : MatsOK G) (hT : tabsOK T = true)
    (hsx : ∀ t < 2048, T.sx.testBit t = (burnsideJ4NP_sextArr ())[t]?.getD false)
    (h : colNodeOK G T D = true)
    (hpair : D.mode = 1 → ∀ a b, a ≤ b → b < 2 ^ (treeWv D.k).length →
      fld D.qp 7 (pIdx (2 ^ (treeWv D.k).length) a b) +
        gRank G (pairP G (packMs (matsOf G (treeWv D.k))) a b) = 112) :
    burnsideJ4NP_VerdictW (burnsideJ4NP_Wv D.k) := by
  classical
  unfold colNodeOK at h
  dsimp only at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, hco⟩, hBc⟩, hmode⟩, hlabs⟩, hk⟩ := h
  have hW : burnsideJ4NP_Wv D.k = Eg (bvOf (treeWv D.k)) (treeWv D.k).length :=
    burnsideJ4NP_col_Wv_eq_Eg D.k
  rw [hW]
  generalize hwv : treeWv D.k = wv at hco hBc hlabs hk hpair
  set r := wv.length with hr
  set bv := bvOf wv with hbv
  have hE : Elem bv r := elem_of_codes hT hco hBc
  obtain ⟨hClen, hC⟩ := codes_spec hT hco
  obtain ⟨hMlen, hMs⟩ := matsOf_spec hG wv
  have hlab' : ∀ m < 2 ^ r, labJ (eta bv r m) = labC D m ∧ (labC D m = 0 ↔ m = 0) := by
    intro m hm
    unfold labsOK at hlabs
    have hm' : m < ((codesOf (wv.map (ccT T))).zipIdx).length := by
      rw [List.length_zipIdx, hClen]
      exact hm
    have h1 := List.all_eq_true.1 hlabs _ (List.getElem_mem hm')
    rw [List.getElem_zipIdx, Nat.zero_add,
      ← List.getD_eq_getElem _ oneK] at h1
    exact labOK_spec h1 (hC m hm) (eta_sq hE m) hsx
  have hlab : ∀ m < 2 ^ r, labJ (eta bv r m) = labC D m := fun m hm => (hlab' m hm).1
  have hlab1 : labJ 1 = 0 := by
    unfold labJ
    rw [if_pos rfl]
  have hinj : ∀ i < 2 ^ r, ∀ j < 2 ^ r, eta bv r i = eta bv r j → i = j := by
    intro i hi j hj e
    have hx : i ^^^ j < 2 ^ r := Nat.xor_lt_two_pow hi hj
    have h1 : eta bv r (i ^^^ j) = 1 := by rw [eta_xor hE le_rfl, e, eta_sq hE]
    have h2 := hlab' _ hx
    rw [h1, hlab1] at h2
    exact burnsideJ4NP_col_eq_of_xor_eq_zero (h2.2.1 h2.1.symm)
  obtain ⟨q, hqc, hqn⟩ : ∃ q : J → J → ℕ, (∀ g x w : J, q (g * x * g⁻¹) (g * w * g⁻¹) = q x w) ∧
      ∀ i < 2 ^ r, ∀ j < 2 ^ r, q (eta bv r i) (eta bv r j) = qC D (2 ^ r) i j := by
    by_cases hm0 : D.mode = 0
    · refine ⟨qProd, qProd_conj, fun i hi j hj => ?_⟩
      unfold qC qProd
      rw [if_pos hm0, ← eta_xor hE le_rfl]
      exact hlab _ (Nat.xor_lt_two_pow hi hj)
    · have hm1 : D.mode = 1 := by
        have := Nat.le_of_ble_eq_true hmode
        omega
      refine ⟨burnsideJ4NP_colPair, burnsideJ4NP_colPair_conj, fun i hi j hj => ?_⟩
      unfold qC
      rw [if_neg hm0]
      split_ifs with hij
      · exact (pairP_label hG hE hi hj (hpair hm1 i j hij hj)).symm
      · rw [colPair_symm (eta_comm hE i j)]
        exact (pairP_label hG hE hj hi (hpair hm1 j i (by omega) hi)).symm
  have hsig : ∀ {i y : ℕ}, i < 2 ^ r → y < 2 ^ r →
      (∀ a b, burnsideJ4NP_colCount (Eg bv r) labJ q (eta bv r i) a b =
        burnsideJ4NP_colCount (Eg bv r) labJ q (eta bv r y) a b) →
      sigC D (2 ^ r) i = sigC D (2 ^ r) y :=
    fun hi hy hc => sig_eq_of_counts hinj hE q hlab hqn hi hy hc
  by_cases hk0 : D.kind = 0
  ·
    rw [if_pos hk0] at hk
    unfold uniqOK at hk
    dsimp only at hk
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      bne_iff_ne, ne_eq] at hk
    obtain ⟨⟨hy, hly⟩, huq⟩ := hk
    have hy' : D.y < 2 ^ r := Eq.mp Nat.blt_eq hy
    have h2A : burnsideJ4NP_Is2A (eta bv r D.y) := by
      have h1 := hlab _ hy'
      rw [hly] at h1
      unfold labJ at h1
      split_ifs at h1 with h3 h4
      all_goals first | assumption | omega
    refine burnsideJ4NP_verdictW_fixed h2A (burnsideJ4NP_fixed_of_colUnique (Eg bv r) labJ q
      labJ_conj hqc (eta_mem_Eg r le_rfl D.y) ?_)
    intro x hx hlx hcx
    obtain ⟨i, hi, rfl⟩ := (mem_Eg_iff hE).1 hx
    rcases huq i hi with (e | hl) | hs
    · rw [e]
    · exact absurd (by rw [← hlab i hi, hlx, hlab _ hy', hly]) hl
    · exact absurd (hsig hi hy' hcx) hs
  ·
    rw [if_neg hk0, Bool.and_eq_true] at hk
    obtain ⟨hun, hk⟩ := hk
    unfold unionOK at hun
    dsimp only at hun
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne,
      ne_eq, Bool.not_eq_true'] at hun
    obtain ⟨⟨⟨-, hbit0⟩, hne⟩, hall⟩ := hun
    set oL := bitsOf D.om (2 ^ r) with hoLdef
    have hoL : ∀ o, o ∈ oL ↔ o < 2 ^ r ∧ D.om.testBit o = true := by
      intro o
      rw [hoLdef, bitsOf, List.mem_filter, List.mem_range]
    set O : Set J := (fun o => eta bv r o) '' {o | o ∈ oL} with hOdef
    have hOW : O ⊆ Eg bv r := by
      rintro _ ⟨o, -, rfl⟩
      exact eta_mem_Eg r le_rfl o
    have hunion : ∀ x ∈ Eg bv r, ∀ o ∈ O, labJ x = labJ o →
        (∀ a b, burnsideJ4NP_colCount (Eg bv r) labJ q x a b =
          burnsideJ4NP_colCount (Eg bv r) labJ q o a b) → x ∈ O := by
      intro x hx o' ho' hl hc
      obtain ⟨i, hi, rfl⟩ := (mem_Eg_iff hE).1 hx
      obtain ⟨o, ho, rfl⟩ := ho'
      have hon := ((hoL o).1 ho).1
      rcases hall i hi with hb | hall'
      · exact ⟨i, (hoL i).2 ⟨hi, hb⟩, rfl⟩
      · exfalso
        rcases hall' _ (List.mem_map.2 ⟨o, ho, rfl⟩) with h1 | h1
        · exact h1 (by rw [← hlab o hon, ← hl, hlab i hi])
        · exact h1 (hsig hon hi fun a b => (hc a b).symm)
    have hNY := burnsideJ4NP_normalizer_le_of_colUnion (Eg bv r) labJ q labJ_conj hqc hOW hunion
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hW2 : IsPGroup 2 ↥(Eg bv r) := IsPGroup.of_card (card_Eg hE hinj)
    have hY2 : IsPGroup 2 ↥(Subgroup.closure O) := hW2.to_le ((Subgroup.closure_le _).2 hOW)
    have hY1 : Subgroup.closure O ≠ ⊥ := by
      obtain ⟨o, ho⟩ : ∃ o, o ∈ oL := by
        cases hl : oL with
        | nil => rw [hl] at hne; exact absurd hne (by decide)
        | cons o l => exact ⟨o, List.mem_cons_self⟩
      obtain ⟨hon, hob⟩ := (hoL o).1 ho
      have ho0 : o ≠ 0 := by
        rintro rfl
        rw [hob] at hbit0
        exact Bool.noConfusion hbit0
      intro hbot
      have hmem : eta bv r o ∈ Subgroup.closure O := Subgroup.subset_closure ⟨o, ho, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact ho0 (hinj o hon 0 (Nat.two_pow_pos r) (by rw [hmem, eta_zero]))
    have hconj : ∀ g : J, (∀ s ∈ S0, ∀ o ∈ oL, ∃ mask,
        (g * s * g⁻¹) * eta bv r o * (g * s * g⁻¹)⁻¹ = eta bv r (xorSel oL mask)) →
        P0.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer ((Subgroup.closure O) : Set J) := by
      intro g hg
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨s, hs, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      apply burnsideJ4NP_colMem_normalizer_closure
      rintro _ ⟨o, ho, rfl⟩
      obtain ⟨mask, e⟩ := hg s hs o ho
      rw [e]
      exact eta_xorSel_mem hE oL mask
    have hstep : ∀ (S : List ℕ) (f : ℕ → ℕ → ℕ → Bool), S.length = 15 → D.masks.length = 15 →
        (S.zip D.masks).all (fun p => (oL.zipIdx).all fun q =>
          f p.1 q.1 (xorSel oL (fld p.2 oL.length q.2))) = true →
        ∀ t < 15, ∀ o ∈ oL, ∃ mask, f (S.getD t 0) o (xorSel oL mask) = true := by
      intro S f hS hm hall t ht o ho
      have hz : t < (S.zip D.masks).length := by rw [List.length_zip, hS, hm]; omega
      have h1 := List.all_eq_true.1 hall _ (List.getElem_mem hz)
      rw [List.getElem_zip] at h1
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ho
      have hk' : k < (oL.zipIdx).length := by rw [List.length_zipIdx]; exact hk
      have h2 := List.all_eq_true.1 h1 _ (List.getElem_mem hk')
      rw [List.getElem_zipIdx, Nat.zero_add] at h2
      refine ⟨fld D.masks[t] oL.length k, ?_⟩
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact h2
    by_cases hk1 : D.kind = 1
    ·
      rw [if_pos hk1] at hk
      unfold normCodesOK at hk
      rw [Bool.and_eq_true, beq_iff_eq] at hk
      obtain ⟨hml, hk⟩ := hk
      refine burnsideJ4NP_verdictW_subnp hY2 hY1 hNY (g := 1) (hconj 1 fun s hs o ho => ?_)
      obtain ⟨t, ht, hst⟩ := p0_pk hs
      obtain ⟨mask, hm⟩ := hstep p0Codes
        (fun s o o' => Nat.blt o' (2 ^ r) &&
          Nat.beq (M s ((codesOf (wv.map (ccT T))).getD o 0))
            (M ((codesOf (wv.map (ccT T))).getD o' 0) s))
        p0Codes_length hml hk t ht o ho
      rw [Bool.and_eq_true] at hm
      obtain ⟨hlt, hb⟩ := hm
      have hlt' : _ < 2 ^ r := Eq.mp Nat.blt_eq hlt
      have hon := ((hoL o).1 ho).1
      rw [getD_irrel (l := codesOf (List.map (ccT T) wv)) (by rw [hClen]; exact hon) 0 oneK,
        getD_irrel (l := codesOf (List.map (ccT T) wv)) (by rw [hClen]; exact hlt') 0 oneK] at hb
      have e := pk_beq (pk_mul hst (hC o hon).1) (pk_mul (hC _ hlt').1 hst) hb
      refine ⟨mask, ?_⟩
      rw [inv_one, mul_one, one_mul, e]
      group
      all_goals rfl
    ·
      rw [if_neg hk1, Bool.and_eq_true] at hk
      obtain ⟨-, hk⟩ := hk
      obtain ⟨e, he⟩ := wordE_isJ hG D
      unfold normMatsOK at hk
      simp only [Bool.and_eq_true, beq_iff_eq] at hk
      obtain ⟨⟨⟨hml, hcan⟩, hEi⟩, hk⟩ := hk
      have hei := inv_of_canon hG he hcan hEi
      refine burnsideJ4NP_verdictW_subnp hY2 hY1 hNY (g := e) (hconj e fun s hs o ho => ?_)
      obtain ⟨t, ht, hst⟩ := p0_prc hG hs
      have hPl : (G.us ++ G.ks).length = 15 := by
        rw [List.length_append, hG.us_len, hG.ks_len]
      obtain ⟨mask, hm⟩ := hstep (G.us ++ G.ks)
        (fun s o o' => strictB (mulJ G.c G.rm (mulJ G.c G.rm
          (seqJ G (rulesJ G D.rules [] 0) D.rules.length 4096 D.seq G.one) s) D.ei) fun X =>
            Nat.blt o' (2 ^ r) && Nat.beq (mulJ G.c G.rm X (getN 0 (matsOf G wv) o))
              (mulJ G.c G.rm (getN 0 (matsOf G wv) o') X))
        hPl hml (by
          refine List.all_eq_true.2 fun p hp => ?_
          have h1 := List.all_eq_true.1 hk p hp
          rw [strictB_eq] at h1
          simp only [strictB_eq]
          exact h1) t ht o ho
      rw [strictB_eq, Bool.and_eq_true] at hm
      obtain ⟨hlt, hb⟩ := hm
      have hlt' : _ < 2 ^ r := Eq.mp Nat.blt_eq hlt
      have hon := ((hoL o).1 ho).1
      rw [getN_eq_getD, getN_eq_getD,
        getD_irrel (l := matsOf G wv) (by rw [hMlen]; exact hon) 0 G.one,
        getD_irrel (l := matsOf G wv) (by rw [hMlen]; exact hlt') 0 G.one] at hb
      have hX := prc_mul hG (prc_mul hG he hst) hei
      have e2 := prc_beq (prc_mul hG hX (hMs o hon)) (prc_mul hG (hMs _ hlt') hX) hb
      refine ⟨mask, ?_⟩
      rw [e2]
      group
      all_goals rfl

end Sound

end CFSG.KC.J4TreeCol

end
