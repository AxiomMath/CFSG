module

public import Certificates.Data.Kernel.AE6TwinK
public import CFSG.Certificates.Kernel.WrTwinSound
public import CFSG.ClassicalInvolution.Q3.AE.PermElt

public section

namespace CFSG.KC.AE6TwinK

open CFSG.KC.WrTwin CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117

variable {e pp : Nat}

theorem pm_enc (a b : Wr 6) : pm (enc a) (enc b) = enc (a * b) :=
  (enc_mul (by norm_num) a b).symm

theorem enc_inj {a b : Wr 6} (h : enc a = enc b) : a = b := enc_injective (by norm_num) h

theorem lvl_mul (σ τ : Equiv.Perm (Fin 6)) : pairMul (lvl σ) (lvl τ) = lvl (σ * τ) := by
  simp only [pairMul, lvl, pm_enc, ← mul_inv_rev, ofPerm_mul]

theorem prods_eq (he : enc (1 : Wr 6) = e) (L : List (List (Equiv.Perm (Fin 6)))) :
    prods e (L.map (·.map lvl)) = (chainProds L).map lvl := by
  induction L with
  | nil =>
    rw [List.map_nil, prods, chainProds, List.map_cons, List.map_nil, ← he]
    simp only [lvl, ofPerm_one, inv_one]
  | cons E L ih =>
    rw [List.map_cons, prods, chainProds, ih, List.flatMap_map, List.map_flatMap]
    congr 1
    funext σ
    simp only [List.map_map]
    exact List.map_congr_left fun τ _ => lvl_mul σ τ

theorem mem_prods_of_chainOK (he : enc (1 : Wr 6) = e) {mem : Equiv.Perm (Fin 6) → Bool}
    {bs : List (Fin 6)} {L : List (List (Equiv.Perm (Fin 6)))} (h : chainOK mem bs L = true)
    (hl : (L.map List.length).prod = 720) (σ : Equiv.Perm (Fin 6)) :
    lvl σ ∈ prods e (L.map (·.map lvl)) := by
  rw [prods_eq he]
  apply List.mem_map_of_mem
  have hnd := chainOK_nodup bs L h
  have hc : (chainProds L).toFinset.card = Fintype.card (Equiv.Perm (Fin 6)) := by
    rw [List.toFinset_card_of_nodup hnd, chainProds_length, hl, Fintype.card_perm, Fintype.card_fin]
    rfl
  have heq := Finset.eq_univ_of_card _ hc
  have hσ : σ ∈ (chainProds L).toFinset := by
    rw [heq]
    exact Finset.mem_univ σ
  exact List.mem_toFinset.1 hσ

theorem mem_allL : ∀ (n : Nat) (l : List (ZMod 2)), l.length = n → l ∈ allL n
  | 0, [], _ => List.mem_singleton_self _
  | n + 1, x :: l, h => by
    simp only [allL, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨l, mem_allL n l (by simpa using h), ?_⟩
    rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) x with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem vecL_ofFn (v : Fin 6 → ZMod 2) : vecL (List.ofFn v) = v := by
  funext i
  fin_cases i <;> rfl

theorem mem_V64 (v : Fin 6 → ZMod 2) : enc (ofVec v) ∈ V64 := by
  have h1 : List.ofFn v ∈ allL 6 := mem_allL 6 (List.ofFn v) List.length_ofFn
  refine List.mem_map.2 ⟨List.ofFn v, h1, ?_⟩
  rw [vecL_ofFn]

theorem mem_E32 {v : Fin 6 → ZMod 2} (hv : ∑ i, v i = 0) : ofVec v ∈ E32W := by
  have h1 : List.ofFn v ∈ allL 6 := mem_allL 6 (List.ofFn v) List.length_ofFn
  refine List.mem_map.2 ⟨List.ofFn v, List.mem_filter.2 ⟨h1, ?_⟩, ?_⟩
  · rw [vecL_ofFn]
    exact decide_eq_true hv
  · rw [vecL_ofFn]

theorem E32_eq : E32 = E32W.map enc := rfl

theorem eqPi_iff' {x y : Wr 6} : eqPi x y = true ↔ x = y ∨ x * allOnes 6 = y := by
  simp only [eqPi, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by rw [h, mul_assoc, allOnes_mul_self 6, mul_one])
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by rw [← h, mul_assoc, allOnes_mul_self 6, mul_one])

theorem eqPi_perm' {x y : Wr 6} (h : eqPi x y = true) : x.perm = y.perm := by
  rcases eqPi_iff'.1 h with h | h
  · rw [h]
  · rw [← h, mul_perm]
    exact (mul_one _).symm

theorem beq_enc (x y : Wr 6) : Nat.beq (enc x) (enc y) = decide (x = y) := by
  refine Bool.eq_iff_iff.2 ?_
  rw [Nat.beq_eq, decide_eq_true_eq]
  exact ⟨enc_inj, congrArg enc⟩

theorem eqPiP_enc (hp : enc (allOnes 6) = pp) (x y : Wr 6) :
    eqPiP pp (enc x) (enc y) = eqPi x y := by
  rw [← hp]
  unfold eqPiP eqPi
  rw [pm_enc, beq_enc, beq_enc]

theorem inModPi_iff (hp : enc (allOnes 6) = pp) (x : Wr 6) (B : List (Wr 6)) :
    inModPi pp (enc x) (B.map enc) = true ↔ ∃ y ∈ B, eqPi x y = true := by
  unfold inModPi
  rw [List.any_map, List.any_eq_true]
  simp only [Function.comp_apply, eqPiP_enc hp]

theorem nib_enc_perm (a : Wr 6) (i : Nat) (hi : i < 6) :
    nib (enc a) (2 * i) / 2 = (a.perm ⟨i, hi⟩).val := by
  have h1 : nib (enc a) (2 * i) = img a (2 * i) := nib_enc (by norm_num) a (by omega)
  have h2 : img a (2 * i) =
      2 * (a.perm ⟨i, hi⟩).val + ((0 : ZMod 2) + a.vec (a.perm ⟨i, hi⟩)).val := by
    have := img_pt a ⟨i, hi⟩ 0
    rwa [ZMod.val_zero, add_zero] at this
  have h3 := ZMod.val_lt ((0 : ZMod 2) + a.vec (a.perm ⟨i, hi⟩))
  rw [h1, h2]
  omega

theorem samePerm_iff (a b : Wr 6) : samePerm (enc a) (enc b) = true ↔ a.perm = b.perm := by
  simp only [samePerm, List.all_eq_true, List.mem_range, Nat.beq_eq]
  constructor
  · intro h
    refine Equiv.ext fun i => Fin.ext ?_
    have := h i.val i.isLt
    rw [nib_enc_perm a i.val i.isLt, nib_enc_perm b i.val i.isLt] at this
    exact this
  · intro h i hi
    rw [nib_enc_perm a i hi, nib_enc_perm b i hi, h]

theorem ofVec_mul_ofPerm (a : Wr 6) : ofVec a.vec * ofPerm a.perm = a := by
  refine Wr.ext (funext fun i => ?_) (one_mul _)
  change a.vec i + 0 = a.vec i
  rw [add_zero]

theorem lvl_fst (σ : Equiv.Perm (Fin 6)) : (lvl σ).1 = enc (ofPerm σ) := rfl

theorem lvl_snd (σ : Equiv.Perm (Fin 6)) : (lvl σ).2 = enc (ofPerm σ)⁻¹ := rfl

theorem pm_lvl (a : Wr 6) : pm (enc (ofVec a.vec)) (lvl a.perm).1 = enc a := by
  rw [lvl_fst, pm_enc, ofVec_mul_ofPerm]

theorem centOK_sound (hp : enc (allOnes 6) = pp) {P : List (Nat × Nat)} {V : List Nat}
    {G C : List (Wr 6)} (h : centOK pp (G.map enc) P V (C.map enc) = true) (a : Wr 6)
    (hP : lvl a.perm ∈ P) (hV : enc (ofVec a.vec) ∈ V)
    (hc : ∀ s ∈ G, eqPi (s * a) (a * s) = true) : ∃ c ∈ C, eqPi a c = true := by
  have h1 := List.all_eq_true.1 h _ hP
  beta_reduce at h1
  have hA : ((G.map enc).all fun s => samePerm (pm (lvl a.perm).1 s) (pm s (lvl a.perm).1)) =
      true := by
    rw [List.all_eq_true]
    intro s0 hs0
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hs0
    rw [lvl_fst, pm_enc, pm_enc, samePerm_iff, mul_perm, mul_perm]
    have h3 : (s * a).perm = (a * s).perm := eqPi_perm' (hc s hs)
    rw [mul_perm, mul_perm] at h3
    change a.perm * s.perm = s.perm * a.perm
    exact h3.symm
  rw [hA, Bool.not_true, Bool.false_or] at h1
  have h2 := List.all_eq_true.1 h1 _ hV
  dsimp only at h2
  rw [pm_lvl] at h2
  have hB : ((G.map enc).all fun s => eqPiP pp (pm s (enc a)) (pm (enc a) s)) = true := by
    rw [List.all_eq_true]
    intro s0 hs0
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hs0
    rw [pm_enc, pm_enc, eqPiP_enc hp]
    exact hc s hs
  rw [hB, Bool.not_true, Bool.false_or, inModPi_iff hp] at h2
  exact h2

theorem cw_enc (w : Wr 6) (hw : w * w = 1) (τ : Equiv.Perm (Fin 6)) :
    pm (pm (pm (enc w) (lvl τ).1) (enc w)) (lvl τ).2 = enc (w * ofPerm τ * w⁻¹ * (ofPerm τ)⁻¹) := by
  have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  rw [lvl_fst, lvl_snd, pm_enc, pm_enc, pm_enc, hw']

theorem tvOK_sound (he : enc (1 : Wr 6) = e) (hp : enc (allOnes 6) = pp) {P : List (Nat × Nat)}
    {E D : List (Wr 6)} {z : Wr 6} (h : tvOK e pp (enc z) P (E.map enc) (D.map enc) = true)
    (hE : ∀ w ∈ E, w * w = 1) (τ : Equiv.Perm (Fin 6)) (hP : lvl τ ∈ P)
    (h1 : ∀ w ∈ E, eqPi (w * ofPerm τ * w⁻¹ * (ofPerm τ)⁻¹) 1 = true ∨
      eqPi (w * ofPerm τ * w⁻¹ * (ofPerm τ)⁻¹) z = true)
    (h2 : ∃ w ∈ E, eqPi (w * ofPerm τ * w⁻¹ * (ofPerm τ)⁻¹) z = true) :
    ∀ d ∈ D, eqPi (ofPerm τ * d * (ofPerm τ)⁻¹) d = false := by
  intro d hd
  have h3 := List.all_eq_true.1 h _ hP
  dsimp only at h3
  have hA : ((E.map enc).all (fun w =>
      eqPiP pp (pm (pm (pm w (lvl τ).1) w) (lvl τ).2) e ||
        eqPiP pp (pm (pm (pm w (lvl τ).1) w) (lvl τ).2) (enc z)) &&
      (E.map enc).any (fun w => eqPiP pp (pm (pm (pm w (lvl τ).1) w) (lvl τ).2) (enc z))) =
        true := by
    rw [Bool.and_eq_true, List.all_eq_true, List.any_eq_true]
    refine ⟨fun w0 hw0 => ?_, ?_⟩
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hw0
      rw [cw_enc w (hE w hw), ← he, eqPiP_enc hp, eqPiP_enc hp, Bool.or_eq_true]
      exact h1 w hw
    · obtain ⟨w, hw, hz⟩ := h2
      refine ⟨enc w, List.mem_map_of_mem hw, ?_⟩
      rw [cw_enc w (hE w hw), eqPiP_enc hp]
      exact hz
  rw [hA, Bool.not_true, Bool.false_or, List.all_eq_true] at h3
  have h4 := h3 _ (List.mem_map_of_mem hd)
  rw [lvl_fst, lvl_snd, pm_enc, pm_enc, eqPiP_enc hp, Bool.not_eq_true'] at h4
  exact h4

theorem transOK_sound (hp : enc (allOnes 6) = pp) {b : Wr 6} {S : List (Equiv.Perm (Fin 6))}
    {X : List (Wr 6)} (h : transOK pp (enc b) (S.map lvl) (X.map enc) = true) :
    ∀ q ∈ X.zip S, eqPi (ofPerm q.2 * b * (ofPerm q.2)⁻¹) q.1 = true := by
  intro q hq
  have hm : (enc q.1, lvl q.2) ∈ (X.map enc).zip (S.map lvl) := by
    rw [List.zip_map]
    exact List.mem_map_of_mem (f := Prod.map enc lvl) hq
  have h1 := List.all_eq_true.1 h _ hm
  change eqPiP pp (pm (pm (lvl q.2).1 (enc b)) (lvl q.2).2) (enc q.1) = true at h1
  rw [lvl_fst, lvl_snd, pm_enc, pm_enc, eqPiP_enc hp] at h1
  exact h1

theorem centUOK_sound {z : Wr 6} {C : List (Wr 6)} (h : centUOK z C = true) :
    ∀ c ∈ C, c.perm = 1 → ∑ i, c.vec i = 0 → eqPi c 1 = true ∨ eqPi c z = true := by
  intro c hc h1 h2
  have h3 := List.all_eq_true.1 h c hc
  simp only [h1, h2, decide_true, Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true]
    at h3
  exact h3

theorem dlOK_sound {z : Wr 6} {C D : List (Wr 6)} (h : dlOK z C D = true) :
    ∀ c ∈ C, c.perm = 1 → eqPi c 1 = false → eqPi c z = false → ∃ d ∈ D, eqPi c d = true := by
  intro c hc h1 h2 h3
  have h4 := List.all_eq_true.1 h c hc
  simp only [h1, h2, h3, decide_true, Bool.not_false, Bool.and_self, Bool.not_true,
    Bool.false_or, List.any_eq_true] at h4
  exact h4

theorem twin3OK_sound {z : Wr 6} {C : List (Wr 6)} (h : twin3OK z C = true) :
    ∀ x ∈ C, ∀ y ∈ C, eqPi (x * x) z = true → eqPi (y * y) 1 = true →
      eqPi (y * x * y⁻¹) (x * z) = true → y.perm = 1 ∨ (y * x).perm = 1 := by
  intro x hx y hy h1 h2 h3
  have h4 := List.all_eq_true.1 h x hx
  simp only [h1, Bool.not_true, Bool.false_or, List.all_eq_true] at h4
  have h5 := h4 y hy
  simp only [h2, h3, Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    decide_eq_true_eq] at h5
  exact h5

theorem twin2OK_sound {L1 L2 : List (Wr 6)} (h : twin2OK L1 L2 = true) :
    L1.length = 8 ∧ L2.length = 8 ∧ ∀ i < 8,
      (L1.getD (2 * (i / 2)) 1 * L2.getD i 1).perm = 1 ∧ ∀ j < i,
        eqPi (L1.getD (2 * (i / 2)) 1 * L2.getD i 1) (L1.getD (2 * (j / 2)) 1 * L2.getD j 1) =
          false := by
  unfold twin2OK at h
  simp only [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem memAtL_α₀ (b : Bool) : memAtL ({0, 1, 2, 3} : Finset (Fin 6)) b = memLC 0 1 2 3 b := by
  unfold memAtL
  have hn : ([0, 1, 2, 3] : List (Fin 6)).Nodup := by decide
  have hs : ([0, 1, 2, 3] : List (Fin 6)).Pairwise (· ≤ ·) := by decide
  have hα : ({0, 1, 2, 3} : Finset (Fin 6)) = ([0, 1, 2, 3] : List (Fin 6)).toFinset := by decide
  rw [hα, (List.toFinset_sort (· ≤ ·) hn).2 hs]

end CFSG.KC.AE6TwinK

end
