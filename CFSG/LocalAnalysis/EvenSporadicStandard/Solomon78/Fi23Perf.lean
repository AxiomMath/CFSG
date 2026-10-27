module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Out1Data
public import CFSG.Sporadic.Fi23.InvCover
public import Certificates.Certificate25173

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Sporadic.Fi23 CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Blueprint
  CFSG.Blueprint.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def Good (X : Array W) (g : J) : Prop :=
  X.size = 253 ∧ RowsWF (toVM X) ∧ toMatW 253 X = mat g


theorem Good.mul {X Y : Array W} {g h : J} (hX : Good X g) (hY : Good Y h) :
    Good (mulW 253 X Y) (g * h) :=
  ⟨by rw [mulW_size]; exact hX.1, RowsWF.mulW hX.2.1 hY.2.1,
    by rw [toMatW_mulW hX.1 hX.2.1 hY.2.1, hX.2.2, hY.2.2, mat_mul]⟩

theorem good_one : Good (idW 253) 1 :=
  ⟨idW_size, rowsWF_idW, by rw [toMatW_idW, mat_one]⟩

theorem good_wm {w : List ℕ} (hw : ∀ x ∈ w, x < 2) : Good (wm w) (wordJ w) :=
  ⟨(prodW_facts w hw).1, (prodW_facts w hw).2.1, by
    rw [mat_wordJ]; exact (prodW_facts w hw).2.2⟩

theorem good_d : Good matD d := ⟨matD_facts.1, matD_facts.2.1, by rw [mat_d]⟩

theorem Good.eq {X Y : Array W} {g h : J} (hX : Good X g) (hY : Good Y h)
    (e : eqW 253 X Y = true) : g = h :=
  mat_injective (by rw [← hX.2.2, ← hY.2.2]; exact toMatW_eq_of_eqW e)

theorem Good.ne {X Y : Array W} {g h : J} (hX : Good X g) (hY : Good Y h)
    (hXc : canonW 253 X = true) (hYc : canonW 253 Y = true) (e : eqW 253 X Y = false) :
    g ≠ h := fun hgh => toMatW_ne_of_eqW hX.1 e hXc hYc (by rw [hX.2.2, hY.2.2, hgh])

theorem wordJ_append (u v : List ℕ) : wordJ (u ++ v) = wordJ u * wordJ v := by
  simp [wordJ, List.map_append, List.prod_append]

theorem wordJ_invLetters (w : List ℕ) : wordJ (invLetters w) = (wordJ w)⁻¹ := by
  have hb : b * (b * b) = 1 := mat_injective matrixFacts.B_inv
  have hbi : b⁻¹ = b * b := by
    rw [inv_eq_iff_mul_eq_one]; exact hb
  induction w with
  | nil => simp [invLetters, wordJ]
  | cons x w ih =>
    have e : wordJ (x :: w) = wordJ [x] * wordJ w := by
      rw [← wordJ_append]; rfl
    have h2 : wordJ (if x = 0 then [0] else [1, 1]) = (wordJ [x])⁻¹ := by
      by_cases hx : x = 0
      · simp [hx, wordJ, a_inv]
      · simp [hx, wordJ, hbi]
    rw [invLetters, wordJ_append, ih, e, mul_inv_rev, h2]

theorem invLetters_lt (w : List ℕ) : ∀ x ∈ invLetters w, x < 2 := by
  induction w with
  | nil => simp [invLetters]
  | cons y w ih =>
    intro x hx
    rw [invLetters, List.mem_append] at hx
    rcases hx with hx | hx
    · exact ih x hx
    · split_ifs at hx <;> simp at hx <;> omega

theorem good_conjW {g : List ℕ} (hg : ∀ x ∈ g, x < 2) :
    Good (conjW g) (wordJ g * d * (wordJ g)⁻¹) := by
  have := (Good.mul (Good.mul (good_wm hg) good_d) (good_wm (invLetters_lt g)))
  rwa [wordJ_invLetters] at this

theorem good_foldl {T : Array (Array W)} {e : ℕ → J} (hT : ∀ x < T.size, Good T[x]! (e x))
    (w : List ℕ) (hw : ∀ x ∈ w, x < T.size) (M : Array W) (g0 : J) (hM : Good M g0) :
    Good (w.foldl (fun M x => mulW 253 M T[x]!) M) (g0 * (w.map e).prod) := by
  induction w generalizing M g0 with
  | nil => simpa using hM
  | cons x w ih =>
    have h1 := hT x (hw x List.mem_cons_self)
    have := ih (fun y hy => hw y (List.mem_cons_of_mem _ hy)) _ _ (hM.mul h1)
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    exact this

theorem arr_getElem!_map {gs : List (List ℕ)} {x : ℕ} (hx : x < gs.length) :
    (gs.map conjW).toArray[x]! = conjW (gs.getD x []) := by
  rw [getElem!_pos (gs.map conjW).toArray x (by simpa using hx), List.getElem_toArray,
    List.getElem_map, List.getD_eq_getElem _ _ hx]

theorem perfCheckOf_sound {g1 g2 : List ℕ} {gs : List (List ℕ)} {wx wy : List ℕ}
    (h : perfCheckOf g1 g2 gs wx wy = true) :
    ∃ e1 c x1 y1 x2 y2 : J, e1 ∈ LocalClass D23 d ∧ c ∈ LocalClass D23 d ∧
      c ∈ LocalClass D23 e1 ∧
      (x1 * (d * e1) = d * e1 * x1 ∧ y1 * (d * e1) = d * e1 * y1 ∧
        x1 * y1 = d * e1 * (y1 * x1)) ∧
      (x2 * (d * e1 * c) = d * e1 * c * x2 ∧ y2 * (d * e1 * c) = d * e1 * c * y2 ∧
        x2 * y2 = d * e1 * c * (y2 * x2)) := by
  simp only [perfCheckOf, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlet, hwl⟩, hc01⟩, hc02⟩, hc12⟩, hcD⟩, hcD1⟩, hcC⟩, hn01⟩, hn02⟩, hn12⟩,
    hpB⟩, hT⟩, hpC⟩ := h
  rw [List.all_eq_true] at hlet hwl
  have hg1 : ∀ x ∈ g1, x < 2 := fun x hx => by
    simpa using (List.all_eq_true.1 (hlet g1 (by simp))) x hx
  have hg2 : ∀ x ∈ g2, x < 2 := fun x hx => by
    simpa using (List.all_eq_true.1 (hlet g2 (by simp))) x hx
  have hgs : ∀ g ∈ gs, ∀ x ∈ g, x < 2 := fun g hg x hx => by
    simpa using (List.all_eq_true.1 (hlet g (by simp [hg]))) x hx
  have gD : Good matD d := good_d
  have gD1 := good_conjW hg1
  have gC := good_conjW hg2
  have gRB := (gD.mul gD1)
  have gRC := (gRB.mul gC)
  have key : ∀ {X Y : Array W} {g h : J}, Good X g → Good Y h →
      commW X Y = true → g * h = h * g := fun hX hY hc => hX.mul hY |>.eq (hY.mul hX) hc
  have hgsT : ∀ x < gs.length, Good (gs.map conjW).toArray[x]!
      (wordJ (gs.getD x []) * d * (wordJ (gs.getD x []))⁻¹) := by
    intro x hx
    rw [arr_getElem!_map hx]
    exact good_conjW (hgs _ (by rw [List.getD_eq_getElem _ _ hx]; exact List.getElem_mem hx))
  have hTgood : ∀ x < (gs.map conjW).toArray.size, Good (gs.map conjW).toArray[x]!
      (wordJ (gs.getD x []) * d * (wordJ (gs.getD x []))⁻¹) := fun x hx =>
    hgsT x (by simpa using hx)
  have hprod : ∀ w : List ℕ, (∀ x ∈ w, x < gs.length) →
      Good (prodW 253 (gs.map conjW).toArray w)
        (w.map fun i => wordJ (gs.getD i []) * d * (wordJ (gs.getD i []))⁻¹).prod := by
    intro w hw
    have := good_foldl hTgood w (fun x hx => by simpa using hw x hx) (idW 253) 1 good_one
    rwa [one_mul] at this
  have hwx : ∀ x ∈ wx, x < gs.length := fun x hx => by
    simpa using hwl x (List.mem_append_left _ hx)
  have hwy : ∀ x ∈ wy, x < gs.length := fun x hx => by
    simpa using hwl x (List.mem_append_right _ hx)
  have hdc : ∀ g : J, IsConj d (g * d * g⁻¹) := fun g => isConj_iff.2 ⟨g, rfl⟩
  refine ⟨wordJ g1 * d * (wordJ g1)⁻¹, wordJ g2 * d * (wordJ g2)⁻¹, wordJ [0],
    wordJ g1 * d * (wordJ g1)⁻¹,
    (wx.map fun i => wordJ (gs.getD i []) * d * (wordJ (gs.getD i []))⁻¹).prod,
    (wy.map fun i => wordJ (gs.getD i []) * d * (wordJ (gs.getD i []))⁻¹).prod,
    ⟨hdc _, ?_, ?_⟩, ⟨hdc _, ?_, ?_⟩, ⟨hdc _, ?_, ?_⟩, ?_, ?_⟩
  · exact (gD.ne gD1 hcD hcD1 hn01).symm
  · exact (key gD gD1 hc01).symm
  · exact (gD.ne gC hcD hcC hn02).symm
  · exact (key gD gC hc02).symm
  · exact (gD1.ne gC hcD1 hcC hn12).symm
  · exact (key gD1 gC hc12).symm
  · unfold pairOK at hpB
    simp only [Bool.and_eq_true] at hpB
    obtain ⟨⟨hB1, hB2⟩, hB3⟩ := hpB
    have gX : Good (wm [0]) (wordJ [0]) := good_wm (by simp)
    exact ⟨key gX gRB hB1, key gD1 gRB hB2, (gX.mul gD1).eq (gRB.mul (gD1.mul gX)) hB3⟩
  · unfold pairOK at hpC
    simp only [Bool.and_eq_true] at hpC
    obtain ⟨⟨hC1, hC2⟩, hC3⟩ := hpC
    have gX := hprod wx hwx
    have gY := hprod wy hwy
    exact ⟨key gX gRC hC1, key gY gRC hC2, (gX.mul gY).eq (gRC.mul (gY.mul gX)) hC3⟩

theorem perfectInvolutions_J :
    PerfectInvolutions ↥J := by
  obtain ⟨e1, c, x1, y1, x2, y2, he1, hc, hce1, ⟨hx1, hy1, hxy1⟩, ⟨hx2, hy2, hxy2⟩⟩ :=
    perfCheckOf_sound Certificates.certificate25173
  intro g hg
  have hg2 : g ^ 2 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := fun h => by rw [h, orderOf_one] at hg; exact absurd hg (by norm_num)
  have hdD : d ∈ D23 := IsConj.refl d
  rcases involution_cover g hg2 hg1 with h | h | h
  · exact mem_commutator_centralizer_of_isConj' h.symm
      (le_commutator_of_commutator_eq_top commutator_C
        (Subgroup.mem_centralizer_singleton_iff.2 rfl))
  · exact mem_commutator_centralizer_of_isConj' (h.symm.trans (isConj_d_mul_d1_of_mem hdD he1))
      (mem_commutator_centralizer_of_comm_pair hx1 hy1 hxy1)
  · exact mem_commutator_centralizer_of_isConj' (h.symm.trans (isConj_t2_of_mem hdD he1 hc hce1))
      (mem_commutator_centralizer_of_comm_pair hx2 hy2 hxy2)

theorem perfectInvolutions_fi23 :
    PerfectInvolutions (NativeSporadic.Carrier .Fi23) :=
  @PerfectInvolutions.transport J NativeSporadic.Fi23 J.toGroup Units.instGroup
    fi23EquivJ.symm perfectInvolutions_J

end CFSG.EvenSporadicStandard.Solomon78
