module

public import CFSG.CGT.T75JM.L2FKlein
public import CFSG.CGT.T75JM.L2GModel

public section

namespace CFSG.CGT.T75JM

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

@[expose] def SwapFact : Prop :=
  ∀ u : Fin 2 → N0,
    (∀ i : Fin 2, ∀ p : Fin 2,
      u i * n0 (bGen p) * (u i)⁻¹ ∈ ({1, bb0, bb1, bb0 * bb1} : Set N0) ∧
      (u i)⁻¹ * n0 (bGen p) * u i ∈ ({1, bb0, bb1, bb0 * bb1} : Set N0)) →
    (([0, 0, 0, 0] : List (Fin 2)).map u).prod = 1 →
    (([1, 1, 1, 1] : List (Fin 2)).map u).prod = 1 →
    (([0, 1, 0, 1, 0, 1] : List (Fin 2)).map u).prod = 1 →
    (∀ w ∈ aWords, (w.map u).prod ∈ ({1, bb0, bb1, bb0 * bb1} : Set N0) ∧ (w.map u).prod ≠ 1) →
    (∀ w ∈ bWords, (∃ k < 16, (w.map u).prod = n0 (tw k)) ∧ (w.map u).prod ≠ 1) →
    ∃ j : N0,
      (∀ p : Fin 2,
        j * n0 (bGen p) * j⁻¹ ∈ ({1, bb0, bb1, bb0 * bb1} : Set N0) ∧
        j⁻¹ * n0 (bGen p) * j ∈ ({1, bb0, bb1, bb0 * bb1} : Set N0)) ∧
      ∀ i : Fin 2, j * u i * j⁻¹ = n0 (dTheta i)

structure L2Checks : Prop where
  t : tCheck = true
  b : bCheck = true
  n : TNormal
  inv : ∀ x : N0, x * x = 1 → (∀ k < 16, x ≠ n0 (tw k)) → ∃ n : N0, n * bb0 * n⁻¹ = x
  aRel : alphaRelCheck = true
  aInj : AlphaInj
  aT : alphaTCheck = true
  klein : KleinFact
  dMem : dMemCheck = true
  dRel : dRelCheck = true
  ab : abWordsCheck = true
  center : ∀ z : N0, (∀ i : Fin 2, z * n0 (bGen i) * z⁻¹ ∈ ({1, bb0, bb1, bb0 * bb1} : Set N0)) →
    (∀ i : Fin 2, z * n0 (dGen i) = n0 (dGen i) * z) → z = 1
  thetaSq : thetaSqCheck = true
  swap : SwapFact

section Model



theorem isTab_tdd (i : Fin 2) : IsTab (tdd i) (n0 (dGen i)) := IsTab.ofWord _

theorem isTab_tth (i : Fin 2) : IsTab (tth i) (n0 (dTheta i)) := IsTab.ofWord _

theorem isTab_evalT {u : Fin 2 → Table} {x : Fin 2 → N0} (hu : ∀ k, IsTab (u k) (x k))
    (w : List (Fin 2)) : IsTab (evalT u w) (w.map x).prod := by
  have key : ∀ (w : List (Fin 2)) (acc : Table) (a : N0), IsTab acc a →
      IsTab (w.foldl (fun acc k => compT 22 acc (u k)) acc) (a * (w.map x).prod) := by
    intro w
    induction w with
    | nil => intro acc a h; simpa using h
    | cons k w ih =>
      intro acc a h
      have := ih _ _ (h.mul (hu k))
      simpa [mul_assoc] using this
  simpa [evalT] using key w (idT 22) 1 IsTab.one

theorem n0_dEvalW (w : List (Fin 2)) :
    n0 (dEvalW w) = (w.map fun k => n0 (dGen k)).prod := by
  induction w with
  | nil => simp [dEvalW, n0_nil]
  | cons k w ih =>
    have h : dEvalW (k :: w) = dGen k ++ dEvalW w := by simp [dEvalW]
    rw [h, n0_append, ih, List.map_cons, List.prod_cons]

theorem d_mem_of_check (hb : bCheck = true) (ht : tCheck = true) (h : dMemCheck = true)
    (i : Fin 2) :
    n0 (dGen i) ∈ Subgroup.normalizer (n0B : Set N0) ∧
      n0 (dTheta i) ∈ Subgroup.normalizer (n0B : Set N0) := by
  simp only [dMemCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  have e0 := (normB_iff hb ht (isTab_tdd 0) (IsTab.of_word_inv (dGen 0))).1 h0
  have e1 := (normB_iff hb ht (isTab_tdd 1) (IsTab.of_word_inv (dGen 1))).1 h1
  have e2 := (normB_iff hb ht (isTab_tth 0) (IsTab.of_word_inv (dTheta 0))).1 h2
  have e3 := (normB_iff hb ht (isTab_tth 1) (IsTab.of_word_inv (dTheta 1))).1 h3
  fin_cases i
  · exact ⟨e0, e2⟩
  · exact ⟨e1, e3⟩

theorem mem_n0B_set (hb : bCheck = true) (ht : tCheck = true) (x : N0) :
    x ∈ n0B ↔ x ∈ ({1, bb0, bb1, bb0 * bb1} : Set N0) := by
  rw [mem_n0B_iff hb ht]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

theorem mem_normalizer_n0B (hb : bCheck = true) (ht : tCheck = true) (x : N0) :
    x ∈ Subgroup.normalizer (n0B : Set N0) ↔ ∀ p : Fin 2,
      x * n0 (bGen p) * x⁻¹ ∈ ({1, bb0, bb1, bb0 * bb1} : Set N0) ∧
      x⁻¹ * n0 (bGen p) * x ∈ ({1, bb0, bb1, bb0 * bb1} : Set N0) := by
  have hm := mem_n0B_iff hb ht
  have hs := mem_n0B_set hb ht
  rw [mem_normalizer_klein ((hm _).2 (Or.inr (Or.inl rfl))) ((hm _).2 (Or.inr (Or.inr (Or.inl rfl))))
    (fun y hy => (hm y).1 hy)]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩ p
    fin_cases p
    · exact ⟨(hs _).1 h1, (hs _).1 h3⟩
    · exact ⟨(hs _).1 h2, (hs _).1 h4⟩
  · intro h
    exact ⟨(hs _).2 (h 0).1, (hs _).2 (h 1).1, (hs _).2 (h 0).2, (hs _).2 (h 1).2⟩

theorem inv_class_of_check
    (hinv : ∀ x : N0, x * x = 1 → (∀ k < 16, x ≠ n0 (tw k)) → ∃ n : N0, n * bb0 * n⁻¹ = x)
    (x : N0) (hx : x * x = 1) (hxT : x ∉ n0T) : ∃ n : N0, n * bb0 * n⁻¹ = x := by
  refine hinv x hx fun k _ h => hxT ?_
  rw [h]
  exact n0_tw_mem k

theorem center_of_check (hb : bCheck = true) (ht : tCheck = true)
    (hc : ∀ z : N0, (∀ i : Fin 2, z * n0 (bGen i) * z⁻¹ ∈ ({1, bb0, bb1, bb0 * bb1} : Set N0)) →
      (∀ i : Fin 2, z * n0 (dGen i) = n0 (dGen i) * z) → z = 1)
    (z : N0) (hz : z ∈ Subgroup.normalizer (n0B : Set N0))
    (hcomm : ∀ i : Fin 2, z * n0 (dGen i) = n0 (dGen i) * z) : z = 1 :=
  hc z (fun i => ((mem_normalizer_n0B hb ht z).1 hz i).1) hcomm

theorem theta_words_of_check (h : thetaSqCheck = true) (i : Fin 2) :
    ((thWords i).map fun k => n0 (dGen k)).prod = n0 (dTheta i) ∧
      ((thWords i).map fun k => n0 (dTheta k)).prod = n0 (dGen i) := by
  simp only [thetaSqCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h i (List.mem_finRange i)
  exact ⟨((isTab_evalT isTab_tdd (thWords i)).eq_iff (isTab_tth i)).1 h1,
    ((isTab_evalT isTab_tth (thWords i)).eq_iff (isTab_tdd i)).1 h2⟩

theorem lift_mk_pos (f : Fin 2 → N0) (l : List (Fin 2)) :
    FreeGroup.lift f (FreeGroup.mk (l.map fun k => (k, true))) = (l.map f).prod := by
  simp [FreeGroup.lift_mk, List.map_map, Function.comp_def]

theorem map_one_of_mul {f : N0 → N0} {N : Subgroup N0}
    (hfmul : ∀ x ∈ N, ∀ y ∈ N, f (x * y) = f x * f y) : f 1 = 1 := by
  have := hfmul 1 N.one_mem 1 N.one_mem
  simpa using this

theorem map_prod_of_mul {f : N0 → N0} {N : Subgroup N0}
    (hfmul : ∀ x ∈ N, ∀ y ∈ N, f (x * y) = f x * f y) {d : Fin 2 → N0} (hd : ∀ k, d k ∈ N)
    (w : List (Fin 2)) :
    f (w.map d).prod = (w.map fun k => f (d k)).prod ∧ (w.map d).prod ∈ N := by
  induction w with
  | nil => exact ⟨map_one_of_mul hfmul, N.one_mem⟩
  | cons k w ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
    exact ⟨by rw [hfmul _ (hd k) _ ih.2, ih.1], N.mul_mem (hd k) ih.2⟩

theorem swap_of_check (hb : bCheck = true) (ht : tCheck = true) (hd : dMemCheck = true)
    (hrel : dRelCheck = true) (hab : abWordsCheck = true) (hsw : SwapFact) (f : N0 → N0)
    (hfD : ∀ x ∈ Subgroup.normalizer (n0B : Set N0), f x ∈ Subgroup.normalizer (n0B : Set N0))
    (hfmul : ∀ x ∈ Subgroup.normalizer (n0B : Set N0), ∀ y ∈ Subgroup.normalizer (n0B : Set N0),
      f (x * y) = f x * f y)
    (hfinj : ∀ x ∈ Subgroup.normalizer (n0B : Set N0), ∀ y ∈ Subgroup.normalizer (n0B : Set N0),
      f x = f y → x = y)
    (hfA : ∀ a ∈ Subgroup.normalizer (n0B : Set N0), a ∈ n0T → f a ∈ n0B)
    (hfB : ∀ b ∈ n0B, f b ∈ n0T) :
    ∃ e ∈ Subgroup.normalizer (n0B : Set N0), ∀ i : Fin 2,
      e * f (n0 (dGen i)) * e⁻¹ = n0 (dTheta i) := by
  set N := Subgroup.normalizer (n0B : Set N0) with hN
  have hdN : ∀ k : Fin 2, n0 (dGen k) ∈ N := fun k => (d_mem_of_check hb ht hd k).1
  have hf1 : f 1 = 1 := map_one_of_mul hfmul
  have hdw : ∀ w : List (Fin 2), IsTab (evalT tdd w) (w.map fun k => n0 (dGen k)).prod :=
    isTab_evalT isTab_tdd
  have hprod := fun w => map_prod_of_mul hfmul (d := fun k => n0 (dGen k)) hdN w
  have hrel1 : ∀ w : List (Fin 2), evalT tdd w = idT 22 →
      (w.map fun k => f (n0 (dGen k))).prod = 1 := by
    intro w hw
    have h1 : (w.map fun k => n0 (dGen k)).prod = 1 := ((hdw w).eq_iff IsTab.one).1 hw
    rw [← (hprod w).1, h1, hf1]
  have haW : ∀ w ∈ aWords, (w.map fun k => f (n0 (dGen k))).prod ∈
      ({1, bb0, bb1, bb0 * bb1} : Set N0) ∧ (w.map fun k => f (n0 (dGen k))).prod ≠ 1 := by
    intro w hw
    simp only [abWordsCheck, Bool.and_eq_true, List.all_eq_true] at hab
    have hw' := hab.1 w hw
    simp only [Bool.not_eq_true'] at hw'
    obtain ⟨⟨hnb, hcT⟩, hne⟩ := hw'
    have ha := hdw w
    have haN : (w.map fun k => n0 (dGen k)).prod ∈ N := by
      have := (normB_iff hb ht (IsTab.ofWord (dEvalW w)) (IsTab.of_word_inv (dEvalW w))).1 hnb
      rwa [n0_dEvalW] at this
    have haT := (tTabs_contains_iff ht ha).1 hcT
    have ha1 : (w.map fun k => n0 (dGen k)).prod ≠ 1 := fun h => by
      rw [(ha.eq_iff IsTab.one).2 h] at hne
      simp at hne
    have hfa := hfA _ haN haT
    have hfa1 : f (w.map fun k => n0 (dGen k)).prod ≠ 1 := fun h =>
      ha1 (hfinj _ haN 1 N.one_mem (h.trans hf1.symm))
    rw [← (hprod w).1]
    exact ⟨(mem_n0B_set hb ht _).1 hfa, hfa1⟩
  have hbW : ∀ w ∈ bWords, (∃ k < 16, (w.map fun k => f (n0 (dGen k))).prod = n0 (tw k)) ∧
      (w.map fun k => f (n0 (dGen k))).prod ≠ 1 := by
    intro w hw
    simp only [abWordsCheck, Bool.and_eq_true, List.all_eq_true] at hab
    have hw' := hab.2 w hw
    simp only [Bool.not_eq_true'] at hw'
    obtain ⟨hcB, hne⟩ := hw'
    have hb' := hdw w
    have hbB := (bTabs_contains_iff hb ht hb').1 hcB
    have hbN : (w.map fun k => n0 (dGen k)).prod ∈ N := Subgroup.le_normalizer hbB
    have hb1 : (w.map fun k => n0 (dGen k)).prod ≠ 1 := fun h => by
      rw [(hb'.eq_iff IsTab.one).2 h] at hne
      simp at hne
    have hfb := hfB _ hbB
    have hfb1 : f (w.map fun k => n0 (dGen k)).prod ≠ 1 := fun h =>
      hb1 (hfinj _ hbN 1 N.one_mem (h.trans hf1.symm))
    obtain ⟨k, hk, e⟩ := (mem_n0T_iff ht _).1 hfb
    rw [← (hprod w).1]
    exact ⟨⟨k, hk, e⟩, hfb1⟩
  simp only [dRelCheck, Bool.and_eq_true, beq_iff_eq] at hrel
  obtain ⟨⟨r1, r2⟩, r3⟩ := hrel
  obtain ⟨j, hj, hji⟩ := hsw (fun k => f (n0 (dGen k)))
    (fun i => (mem_normalizer_n0B hb ht _).1 (hfD _ (hdN i))) (hrel1 _ r1) (hrel1 _ r2)
    (hrel1 _ r3) haW hbW
  exact ⟨j, (mem_normalizer_n0B hb ht j).2 hj, hji⟩

end Model

@[expose] noncomputable def l2Model
    (h : L2Checks) : T1Model N0 2 1 where
  T0 := n0T
  B0 := n0B
  b0 := bb0
  d := fun i => n0 (dGen i)
  d0 := fun _ => 1
  theta := fun _ i => n0 (dTheta i)
  b0_mem := Subgroup.subset_closure (by simp)
  d_mem := fun i => (d_mem_of_check h.b h.t h.dMem i).1
  d0_mem := fun _ => Subgroup.one_mem _
  theta_mem := fun _ i => (d_mem_of_check h.b h.t h.dMem i).2
  inv_class := fun x hx hxT => inv_class_of_check h.inv x hx hxT
  klein_class := fun B' hb0 hexp hcard hbot _ _ hcent =>
    klein_class_of_checks h.t h.b h.n h.aRel h.aInj h.aT h.klein B' hb0 hexp hcard hbot hcent
  swap := fun f hfD hfmul hfinj hfA hfB => by
    obtain ⟨e, he, hk⟩ := swap_of_check h.b h.t h.dMem h.dRel h.ab h.swap f hfD hfmul hfinj hfA hfB
    exact ⟨e, he, 0, hk⟩
  center := fun z hz hc => center_of_check h.b h.t h.center z hz hc
  theta_sq := fun _ =>
    ⟨fun i => (thWords i).map fun j => (j, true), fun i => by
      refine ⟨?_, ?_⟩
      · rw [lift_mk_pos]
        exact (theta_words_of_check h.thetaSq i).1
      · rw [lift_mk_pos]
        simpa using (theta_words_of_check h.thetaSq i).2⟩

end CFSG.CGT.T75JM
