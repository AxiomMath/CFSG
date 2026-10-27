module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om2.Basic

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check (reflTab wA wordOK eA)
open CFSG.ClassicalInvolution.Generic

set_option linter.unusedSectionVars false

theorem wordYOK_of_sub {ws : List (List ℕ)} (h : ∀ w ∈ ws, w ∈ allWordsY) :
    ∀ w ∈ ws, wordYOK w = true := fun w hw => (wordsCheckY_spec (h w hw)).1
theorem wT_sub : ∀ w ∈ wT, w ∈ allWordsY := by
  intro w hw
  simp only [wT, List.mem_append] at hw
  simp only [allWordsY, List.mem_append]
  tauto
theorem wCc_sub : ∀ w ∈ wCc, w ∈ allWordsY := by
  intro w hw
  simp only [wCc, List.mem_append] at hw
  simp only [allWordsY, List.mem_append]
  tauto
theorem wS0_sub : ∀ w ∈ wS0, w ∈ allWordsY := by
  intro w hw
  simp only [allWordsY, List.mem_append]
  tauto
theorem wP3_sub : ∀ w ∈ wP3, w ∈ allWordsY := by
  intro w hw
  simp only [allWordsY, List.mem_append]
  tauto
theorem wSc_sub : ∀ w ∈ wSc, w ∈ allWordsY := by
  intro w hw
  simp only [allWordsY, List.mem_append]
  tauto
theorem wPc_sub : ∀ w ∈ wPc, w ∈ allWordsY := by
  intro w hw
  simp only [allWordsY, List.mem_append]
  tauto
theorem wCR_sub : ∀ w ∈ wCR, w ∈ allWordsY := by
  intro w hw
  simp only [allWordsY, List.mem_append]
  tauto
theorem wSub_sub : ∀ w ∈ wSub, w ∈ allWordsY := by
  intro w hw
  simp only [allWordsY, List.mem_append]
  tauto
theorem wFuse0_sub : ∀ w ∈ wFuse0, w ∈ allWordsY := by
  intro w hw
  simp only [allWordsY, List.mem_append]
  tauto

private theorem rel_word {w : List ℕ} (hw : w ∈ allWordsY) :
    Rep 480 (wY (lettersY (reflTab ())) w) (phi (wordE w)) ∧
      CFSG.RankThree.Native.validA 480 (wY (lettersY (reflTab ())) w) = true :=
  ⟨rep_wordE (wordsCheckY_spec hw).1, (wordsCheckY_spec hw).2⟩

private theorem rel_compY {a b : Array ℕ} {x y : HY} (ha : Rep 480 a (phi x))
    (hb : Rep 480 b (phi y)) : Rep 480 (compA 480 a b) (phi (x * y)) := by
  rw [map_mul]
  exact rep_compA ha hb

private theorem rel_one : Rep 480 (idA 480) (phi 1) := by
  rw [map_one]
  exact rep_idA

private theorem rel_eq_of_eqA {a b : Array ℕ} {x y : HY} (ha : Rep 480 a (phi x))
    (hb : Rep 480 b (phi y)) (h : eqA 480 a b = true) : x = y :=
  phi_injective ((eqA_iff ha hb).1 h)

private theorem rel_conjY {g y : Array ℕ} {u x : HY} (hg : Rep 480 g (phi u))
    (hv : CFSG.RankThree.Native.validA 480 g = true) (hy : Rep 480 y (phi x)) :
    Rep 480 (CFSG.RankThree.Native.conjA 480 g y) (phi (u * x * u⁻¹)) := by
  rw [map_mul, map_mul, map_inv]
  have h := CFSG.RankThree.Native.rep_conjA hv hy
  rwa [CFSG.RankThree.Native.permOfArr_eq_of_rep hg] at h

private theorem rel_invY {a : Array ℕ} {x : HY} (ha : Rep 480 a (phi x))
    (hv : CFSG.RankThree.Native.validA 480 a = true) :
    Rep 480 (invCand 480 a) (phi x⁻¹) := by
  rw [map_inv]
  have h := CFSG.RankThree.Native.rep_inv_of_validA hv
  rwa [CFSG.RankThree.Native.permOfArr_eq_of_rep ha] at h

private theorem rel_fst {a : Array ℕ} {u : HY} (h : Rep 480 a (phi u)) :
    Rep 240 (fstA a) ((u : WP × WP).1 : Equiv.Perm (Fin 240)) := by
  refine fun i => ?_
  have hi : a[(i : ℕ)]! = ((phi u) (Fin.castAdd 240 i) : ℕ) := by
    have h' := h (Fin.castAdd 240 i)
    rwa [Fin.coe_castAdd] at h'
  have hval : ((phi u) (Fin.castAdd 240 i) : ℕ) =
      (((u : WP × WP).1 : Equiv.Perm (Fin 240)) i : ℕ) := by
    have e1 : (finSumFinEquiv (m := 240) (n := 240)).symm (Fin.castAdd 240 i) = Sum.inl i :=
      finSumFinEquiv_symm_apply_castAdd i
    show ((phiP _ _) (Fin.castAdd 240 i) : ℕ) = _
    rw [phiP, Equiv.permCongr_apply, e1, Equiv.sumCongr_apply, Sum.map_inl,
      finSumFinEquiv_apply_left, Fin.coe_castAdd]
  have hext : (fstA a)[(i : ℕ)]! = a[(i : ℕ)]! := by
    have hlt := i.isLt
    unfold fstA
    by_cases hs : (i : ℕ) < a.size
    · rw [getElem!_pos a _ hs, getElem!_pos (a.extract 0 240) _ (by simp; omega),
        Array.getElem_extract]
      simp
    · rw [getElem!_neg a _ hs, getElem!_neg (a.extract 0 240) _ (by simp; omega)]
  rw [hext, hi, hval]

private theorem rel_fst_eq {u : HY} {a : Array ℕ} {m : ℕ} (hm : m < 256 ∧ framePop m % 2 = 0)
    (hu : Rep 480 a (phi u)) (h : eqA 240 (fstA a) (eA m) = true) :
    ((u : WP × WP).1 : WP) = Om1.eW m := by
  apply Subtype.ext
  exact CFSG.Monster.B.Co2.eq_of_eqA (rel_fst hu) (Om1.rep_eW hm) h

private theorem rel_coe_cK (k : ℕ) :
    ((cK k : HY) : WP × WP) =
      ((if k = 1 then 1 else zPlus : WP), (if k = 0 then 1 else zPlus : WP)) := rfl

private theorem rel_zz : zPlus * zPlus = 1 := Subtype.ext zPerm_mul_self

private theorem rel_split :
    eqA 240 (fstA (wY (lettersY (reflTab ())) wT0)) (eA 15) = true ∧
    eqA 480 (compA 480 (wY (lettersY (reflTab ())) wT0) (wY (lettersY (reflTab ())) wT0))
      (idA 480) = true ∧
    q8RelY (wY (lettersY (reflTab ())) wT0) (wY (lettersY (reflTab ())) wI0)
      (wY (lettersY (reflTab ())) wJ0) = true ∧
    (∀ k ∈ List.range 3,
      eqA 480 (CFSG.RankThree.Native.conjA 480 (wY (lettersY (reflTab ())) (wFuse0.getD k []))
        (wY (lettersY (reflTab ())) wT0)) (compA 480 (wY (lettersY (reflTab ())) wT0) (cA k)) =
          true) ∧
    (∀ w ∈ wT,
      commY (wY (lettersY (reflTab ())) w) (wY (lettersY (reflTab ())) wT0) = true ∧
      inLY (q8ListY (wY (lettersY (reflTab ())) wI0) (wY (lettersY (reflTab ())) wJ0))
        (CFSG.RankThree.Native.conjA 480 (wY (lettersY (reflTab ())) w)
          (wY (lettersY (reflTab ())) wI0)) = true ∧
      inLY (q8ListY (wY (lettersY (reflTab ())) wI0) (wY (lettersY (reflTab ())) wJ0))
        (CFSG.RankThree.Native.conjA 480 (wY (lettersY (reflTab ())) w)
          (wY (lettersY (reflTab ())) wJ0)) = true) ∧
    eqA 240 (fstA (wY (lettersY (reflTab ())) wTc)) (eA 23) = true ∧
    eqA 480 (compA 480 (wY (lettersY (reflTab ())) wTc) (wY (lettersY (reflTab ())) wTc))
      (idA 480) = true ∧
    eqA 480 (CFSG.RankThree.Native.conjA 480 (wY (lettersY (reflTab ())) wFuseC)
      (wY (lettersY (reflTab ())) wTc)) (compA 480 (wY (lettersY (reflTab ())) wTc) (cA 1)) =
        true ∧
    (∀ w ∈ wCc,
      commY (wY (lettersY (reflTab ())) w) (wY (lettersY (reflTab ())) wTc) = true) ∧
    eqA 240 (fstA (wY (lettersY (reflTab ())) wLiftA)) (eA 3) = true ∧
    eqA 240 (fstA (wY (lettersY (reflTab ())) wLiftB)) (eA 252) = true ∧
    (∀ w ∈ [wLiftA, wLiftB],
      (!eqA 480 (compA 480 (wY (lettersY (reflTab ())) w) (wY (lettersY (reflTab ())) w))
        (idA 480)) = true ∧
      (!eqA 480 (compA 480 (compA 480 (wY (lettersY (reflTab ())) w) (cA 1))
        (compA 480 (wY (lettersY (reflTab ())) w) (cA 1))) (idA 480)) = true) ∧
    (∀ w ∈ wCR,
      commY (wY (lettersY (reflTab ())) w) (wY (lettersY (reflTab ())) wI0) = true ∧
      commY (wY (lettersY (reflTab ())) w) (wY (lettersY (reflTab ())) wJ0) = true) := by
  have h := om2A_parts.2.2.1
  simp only [relCheckY, Bool.and_eq_true, List.all_eq_true, and_assoc] at h
  exact h

private theorem rel_q8Rel {t x y : Array ℕ} (h : q8RelY t x y = true) :
    eqA 480 (compA 480 x x) t = true ∧ eqA 480 (compA 480 y y) t = true ∧
      eqA 480 (CFSG.RankThree.Native.conjA 480 y x) (invCand 480 x) = true := by
  simp only [q8RelY, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

private theorem rel_r0_check :
    (∀ a ∈ q8ListY (wY (lettersY (reflTab ())) wI0) (wY (lettersY (reflTab ())) wJ0),
      CFSG.RankThree.Native.validA 480 a = true) ∧
    (∀ a ∈ q8ListY (wY (lettersY (reflTab ())) wI0) (wY (lettersY (reflTab ())) wJ0),
      ∀ b ∈ q8ListY (wY (lettersY (reflTab ())) wI0) (wY (lettersY (reflTab ())) wJ0),
        inLY (q8ListY (wY (lettersY (reflTab ())) wI0) (wY (lettersY (reflTab ())) wJ0))
          (compA 480 a b) = true) ∧
    (∀ a ∈ q8ListY (wY (lettersY (reflTab ())) wI0) (wY (lettersY (reflTab ())) wJ0),
      inLY (q8ListY (wY (lettersY (reflTab ())) wI0) (wY (lettersY (reflTab ())) wJ0))
        (invCand 480 a) = true) := by
  have h := om2A_parts.2.2.2.2.2.2
  simp only [r0CheckY, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

private theorem rel_fuse0_mem {k : ℕ} (hk : k < 3) : wFuse0.getD k [] ∈ allWordsY := by
  apply wFuse0_sub
  interval_cases k <;> simp [wFuse0]

private noncomputable def rel_r0 : List HY :=
  [1, i0Y, i0Y * i0Y, i0Y * i0Y * i0Y, j0Y, j0Y * i0Y, j0Y * (i0Y * i0Y),
    j0Y * (i0Y * i0Y * i0Y)]

private theorem rel_q8 :
    List.Forall₂ (fun (a : Array ℕ) (x : HY) => Rep 480 a (phi x))
      (q8ListY (wY (lettersY (reflTab ())) wI0) (wY (lettersY (reflTab ())) wJ0)) rel_r0 := by
  have hi := (rel_word (w := wI0) (by simp [allWordsY])).1
  have hj := (rel_word (w := wJ0) (by simp [allWordsY])).1
  have h2 := rel_compY hi hi
  have h3 := rel_compY h2 hi
  simp only [q8ListY, rel_r0]
  exact List.Forall₂.cons rel_one (List.Forall₂.cons hi (List.Forall₂.cons h2
    (List.Forall₂.cons h3 (List.Forall₂.cons hj (List.Forall₂.cons (rel_compY hj hi)
      (List.Forall₂.cons (rel_compY hj h2) (List.Forall₂.cons (rel_compY hj h3)
        List.Forall₂.nil)))))))

private theorem rel_forall₂_left {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {a : α}, a ∈ l₁ → ∃ b ∈ l₂, R a b
  | _, _, List.Forall₂.nil, _, h => absurd h List.not_mem_nil
  | _, _, List.Forall₂.cons hab h, _, hm => by
    rcases List.mem_cons.1 hm with rfl | hm
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, h'⟩ := rel_forall₂_left h hm
      exact ⟨b, List.mem_cons_of_mem _ hb, h'⟩

private theorem rel_forall₂_right {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {b : β}, b ∈ l₂ → ∃ a ∈ l₁, R a b
  | _, _, List.Forall₂.nil, _, h => absurd h List.not_mem_nil
  | _, _, List.Forall₂.cons hab h, _, hm => by
    rcases List.mem_cons.1 hm with rfl | hm
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, h'⟩ := rel_forall₂_right h hm
      exact ⟨a, List.mem_cons_of_mem _ ha, h'⟩

private theorem rel_mem_r0 {a : Array ℕ} {x : HY} (ha : Rep 480 a (phi x))
    (h : inLY (q8ListY (wY (lettersY (reflTab ())) wI0) (wY (lettersY (reflTab ())) wJ0)) a =
      true) : x ∈ rel_r0 := by
  rw [inLY, List.any_eq_true] at h
  obtain ⟨b, hb, hab⟩ := h
  obtain ⟨y, hy, hby⟩ := rel_forall₂_left rel_q8 hb
  have hxy : x = y := rel_eq_of_eqA ha hby hab
  rw [hxy]
  exact hy

private noncomputable def rel_r0Sub : Subgroup HY where
  carrier := {x | x ∈ rel_r0}
  one_mem' := by simp [rel_r0]
  mul_mem' := by
    intro x y hx hy
    obtain ⟨-, hmul, -⟩ := rel_r0_check
    obtain ⟨a, ha, hax⟩ := rel_forall₂_right rel_q8 hx
    obtain ⟨b, hb, hby⟩ := rel_forall₂_right rel_q8 hy
    exact rel_mem_r0 (rel_compY hax hby) (hmul a ha b hb)
  inv_mem' := by
    intro x hx
    obtain ⟨hval, -, hinv⟩ := rel_r0_check
    obtain ⟨a, ha, hax⟩ := rel_forall₂_right rel_q8 hx
    exact rel_mem_r0 (rel_invY hax (hval a ha)) (hinv a ha)

private theorem rel_r0_sub {x : HY} (hx : x ∈ rel_r0) : x ∈ R0Y := by
  have hi : i0Y ∈ R0Y := by
    rw [R0Y]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hj : j0Y ∈ R0Y := by
    rw [R0Y]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  simp only [rel_r0, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact R0Y.one_mem
  · exact hi
  · exact R0Y.mul_mem hi hi
  · exact R0Y.mul_mem (R0Y.mul_mem hi hi) hi
  · exact hj
  · exact R0Y.mul_mem hj hi
  · exact R0Y.mul_mem hj (R0Y.mul_mem hi hi)
  · exact R0Y.mul_mem hj (R0Y.mul_mem (R0Y.mul_mem hi hi) hi)

private theorem rel_mem_R0Y {a : Array ℕ} {x : HY} (ha : Rep 480 a (phi x))
    (h : inLY (q8ListY (wY (lettersY (reflTab ())) wI0) (wY (lettersY (reflTab ())) wJ0)) a =
      true) : x ∈ R0Y :=
  rel_r0_sub (rel_mem_r0 ha h)

private theorem rel_conjSub_closure_eq {G : Type*} [Group G] [Finite G] (g : G) (S : Set G)
    (hS : ∀ x ∈ S, g * x * g⁻¹ ∈ Subgroup.closure S) :
    conjSub g (Subgroup.closure S) = Subgroup.closure S := by
  have key : conjSub g (Subgroup.closure S) ≤ Subgroup.closure S := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hK : Subgroup.closure S ≤ (Subgroup.closure S).comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro z hz
      exact hS z hz
    exact hK hy
  have hc : Nat.card (conjSub g (Subgroup.closure S)) = Nat.card (Subgroup.closure S) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  exact Subgroup.eq_of_le_of_card_ge key hc.ge

theorem cK_comm (k : ℕ) (x : HY) : x * cK k = cK k * x := by
  have hc : cK k ∈ qY.ker := by
    refine mem_ker_qY.2 ⟨?_, ?_⟩ <;> simp only [rel_coe_cK] <;> split_ifs <;> simp
  exact Subgroup.mem_center_iff.1 (ker_qY_le_center hc) x
theorem cK_mul_self (k : ℕ) : cK k * cK k = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_one, rel_coe_cK]
  split_ifs <;> simp [Prod.ext_iff, rel_zz]
theorem cK_ne_one {k : ℕ} (hk : k < 3) : cK k ≠ 1 := by
  intro h
  have h' := congrArg (fun u : HY => ((u : WP × WP))) h
  simp only [rel_coe_cK] at h'
  interval_cases k <;> simp [Prod.ext_iff, zPlus_ne_one] at h'
theorem cK_inj {k k' : ℕ} (hk : k < 3) (hk' : k' < 3) (h : cK k = cK k') : k = k' := by
  have h1 := congrArg (fun u : HY => ((u : WP × WP)).1) h
  have h2 := congrArg (fun u : HY => ((u : WP × WP)).2) h
  simp only [rel_coe_cK] at h1 h2
  clear h
  interval_cases k <;> interval_cases k' <;>
    simp_all [zPlus_ne_one, Ne.symm zPlus_ne_one]
theorem center_eq_ker : Subgroup.center HY = qY.ker := by
  refine le_antisymm ?_ ker_qY_le_center
  intro u hu
  have hc : qY u ∈ Subgroup.center omegaT := by
    rw [Subgroup.mem_center_iff]
    intro ω
    obtain ⟨g, rfl⟩ := qY_surjective ω
    have hug := Subgroup.mem_center_iff.1 hu g
    rw [← map_mul, ← map_mul, hug]
  rw [CFSG.EvenSmallLie.OmegaEight.center_omegaT, Subgroup.mem_bot] at hc
  exact MonoidHom.mem_ker.2 hc
theorem mul_cK_mem {k k' : ℕ} (hk : k < 3) (hk' : k' < 3) (h : k ≠ k') :
    ∃ k'' < 3, cK k * cK k' = cK k'' := by
  refine ⟨3 - k - k', by omega, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_mul]
  interval_cases k <;> interval_cases k' <;>
    simp_all [rel_coe_cK, Prod.ext_iff, rel_zz, zPlus_ne_one, Ne.symm zPlus_ne_one]

theorem fst_t0Y : ((t0Y : WP × WP).1 : WP) = Om1.t0 := by
  obtain ⟨h1, -⟩ := rel_split
  exact rel_fst_eq (m := 15) ⟨by norm_num, by decide⟩
    (rel_word (w := wT0) (by simp [allWordsY])).1 h1
theorem t0Y_mul_self : t0Y * t0Y = 1 := by
  obtain ⟨-, h2, -⟩ := rel_split
  have ht := rel_word (w := wT0) (by simp [allWordsY])
  exact rel_eq_of_eqA (rel_compY ht.1 ht.1) rel_one h2
theorem fuse0_conj {k : ℕ} (hk : k < 3) : fuse0 k * t0Y * (fuse0 k)⁻¹ = t0Y * cK k := by
  obtain ⟨-, -, -, h4, -⟩ := rel_split
  have hf := rel_word (rel_fuse0_mem hk)
  have ht := rel_word (w := wT0) (by simp [allWordsY])
  exact rel_eq_of_eqA (rel_conjY hf.1 hf.2 ht.1) (rel_compY ht.1 (rep_cK hk))
    (h4 k (List.mem_range.2 hk))
theorem i0Y_mul_self : i0Y * i0Y = t0Y := by
  obtain ⟨-, -, hq, -⟩ := rel_split
  obtain ⟨h1, -, -⟩ := rel_q8Rel hq
  have hi := rel_word (w := wI0) (by simp [allWordsY])
  have ht := rel_word (w := wT0) (by simp [allWordsY])
  exact rel_eq_of_eqA (rel_compY hi.1 hi.1) ht.1 h1
theorem comm_t0Y_of_mem {w : List ℕ} (hw : w ∈ wT) : wordE w * t0Y = t0Y * wordE w := by
  obtain ⟨-, -, -, -, h5, -⟩ := rel_split
  have hw' := rel_word (wT_sub w hw)
  have ht := rel_word (w := wT0) (by simp [allWordsY])
  exact rel_eq_of_eqA (rel_compY hw'.1 ht.1) (rel_compY ht.1 hw'.1) (h5 w hw).1
theorem conjSub_R0Y_of_mem {w : List ℕ} (hw : w ∈ wT) : conjSub (wordE w) R0Y = R0Y := by
  obtain ⟨-, -, -, -, h5, -⟩ := rel_split
  obtain ⟨-, hci, hcj⟩ := h5 w hw
  have hw' := rel_word (wT_sub w hw)
  have hi' := rel_word (w := wI0) (by simp [allWordsY])
  have hj' := rel_word (w := wJ0) (by simp [allWordsY])
  have hI : wordE w * i0Y * (wordE w)⁻¹ ∈ R0Y :=
    rel_mem_R0Y (rel_conjY hw'.1 hw'.2 hi'.1) hci
  have hJ : wordE w * j0Y * (wordE w)⁻¹ ∈ R0Y :=
    rel_mem_R0Y (rel_conjY hw'.1 hw'.2 hj'.1) hcj
  exact rel_conjSub_closure_eq (wordE w) ({i0Y, j0Y} : Set HY) (by
    rintro z (rfl | rfl)
    · exact hI
    · exact hJ)

theorem fst_tcY : ((tcY : WP × WP).1 : WP) = Om1.tc := by
  obtain ⟨-, -, -, -, -, h6, -⟩ := rel_split
  exact rel_fst_eq (m := 23) ⟨by norm_num, by decide⟩
    (rel_word (w := wTc) (by simp [allWordsY])).1 h6
theorem fuseC_conj : fuseC * tcY * fuseC⁻¹ = tcY * cK 1 := by
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := rel_split
  have hf := rel_word (w := wFuseC) (by simp [allWordsY])
  have htc := rel_word (w := wTc) (by simp [allWordsY])
  exact rel_eq_of_eqA (rel_conjY hf.1 hf.2 htc.1) (rel_compY htc.1 (rep_cK (k := 1) (by norm_num)))
    h8
theorem comm_tcY_of_mem {w : List ℕ} (hw : w ∈ wCc) : wordE w * tcY = tcY * wordE w := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := rel_split
  have hw' := rel_word (wCc_sub w hw)
  have htc := rel_word (w := wTc) (by simp [allWordsY])
  exact rel_eq_of_eqA (rel_compY hw'.1 htc.1) (rel_compY htc.1 hw'.1) (h9 w hw)

theorem fst_liftA : ((liftA : WP × WP).1 : WP) = Om1.ta := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, -⟩ := rel_split
  exact rel_fst_eq (m := 3) ⟨by norm_num, by decide⟩
    (rel_word (w := wLiftA) (by simp [allWordsY])).1 h10
theorem fst_liftB : ((liftB : WP × WP).1 : WP) = Om1.tb := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, -⟩ := rel_split
  exact rel_fst_eq (m := 252) ⟨by norm_num, by decide⟩
    (rel_word (w := wLiftB) (by simp [allWordsY])).1 h11
theorem liftA_sq_ne : liftA * liftA ≠ 1 ∧ (liftA * cK 1) * (liftA * cK 1) ≠ 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12, -⟩ := rel_split
  obtain ⟨h1, h2⟩ := h12 wLiftA (by simp)
  have hA := rel_word (w := wLiftA) (by simp [allWordsY])
  have hc : Rep 480 (cA 1) (phi (cK 1)) := rep_cK (k := 1) (by norm_num)
  constructor
  · intro h
    have he := (eqA_iff (rel_compY hA.1 hA.1) rel_one).2 (congrArg phi h)
    simp [he] at h1
  · intro h
    have he := (eqA_iff (rel_compY (rel_compY hA.1 hc) (rel_compY hA.1 hc)) rel_one).2
      (congrArg phi h)
    simp [he] at h2
theorem liftB_sq_ne : liftB * liftB ≠ 1 ∧ (liftB * cK 1) * (liftB * cK 1) ≠ 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12, -⟩ := rel_split
  obtain ⟨h1, h2⟩ := h12 wLiftB (by simp)
  have hB := rel_word (w := wLiftB) (by simp [allWordsY])
  have hc : Rep 480 (cA 1) (phi (cK 1)) := rep_cK (k := 1) (by norm_num)
  constructor
  · intro h
    have he := (eqA_iff (rel_compY hB.1 hB.1) rel_one).2 (congrArg phi h)
    simp [he] at h1
  · intro h
    have he := (eqA_iff (rel_compY (rel_compY hB.1 hc) (rel_compY hB.1 hc)) rel_one).2
      (congrArg phi h)
    simp [he] at h2

theorem comm_R0Y_of_mem {w : List ℕ} (hw : w ∈ wCR) :
    wordE w * i0Y = i0Y * wordE w ∧ wordE w * j0Y = j0Y * wordE w := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h13⟩ := rel_split
  obtain ⟨hi, hj⟩ := h13 w hw
  have hw' := rel_word (wCR_sub w hw)
  have hi' := rel_word (w := wI0) (by simp [allWordsY])
  have hj' := rel_word (w := wJ0) (by simp [allWordsY])
  exact ⟨rel_eq_of_eqA (rel_compY hw'.1 hi'.1) (rel_compY hi'.1 hw'.1) hi,
    rel_eq_of_eqA (rel_compY hw'.1 hj'.1) (rel_compY hj'.1 hw'.1) hj⟩
theorem card_R0Y_le : Nat.card R0Y ≤ 8 := by
  have hle : R0Y ≤ rel_r0Sub := by
    rw [R0Y, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · show i0Y ∈ rel_r0
      simp [rel_r0]
    · show j0Y ∈ rel_r0
      simp [rel_r0]
  have hcard : Nat.card rel_r0Sub ≤ 8 := by
    have : (rel_r0Sub : Set HY) = (rel_r0.toFinset : Set HY) := by
      ext x
      simp [rel_r0Sub]
    rw [← SetLike.coe_sort_coe, this, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    exact (List.toFinset_card_le _).trans (by simp [rel_r0])
  exact (Subgroup.card_le_of_le hle).trans hcard

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2
