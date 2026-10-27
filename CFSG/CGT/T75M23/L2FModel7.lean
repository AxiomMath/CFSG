module

public import CFSG.CGT.T75M23.L2FKlein7
public import CFSG.CGT.T75JM.L2GModel

public section

namespace CFSG.CGT.T75M23

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.CGT.T75JM (T1Model)

@[expose] def SwapFact7 : Prop :=
  ∀ u : Fin 3 → N7,
    (∀ i : Fin 3, ∀ p : Fin 2,
      u i * n7 (bGen7 p) * (u i)⁻¹ ∈ ({1, bm0, bm1, bm0 * bm1} : Set N7) ∧
      (u i)⁻¹ * n7 (bGen7 p) * u i ∈ ({1, bm0, bm1, bm0 * bm1} : Set N7)) →
    (([0, 0] : List (Fin 3)).map u).prod = 1 →
    (([1, 1] : List (Fin 3)).map u).prod = 1 →
    (([2, 2, 2] : List (Fin 3)).map u).prod = 1 →
    (∀ w ∈ dRels7, (w.map u).prod = 1) →
    (∀ w ∈ aWords7, (w.map u).prod ∈ ({1, bm0, bm1, bm0 * bm1} : Set N7) ∧ (w.map u).prod ≠ 1) →
    (∀ w ∈ bWords7, (∃ k < 16, (w.map u).prod = n7 (tw7 k)) ∧ (w.map u).prod ≠ 1) →
    ∃ j : N7,
      (∀ p : Fin 2,
        j * n7 (bGen7 p) * j⁻¹ ∈ ({1, bm0, bm1, bm0 * bm1} : Set N7) ∧
        j⁻¹ * n7 (bGen7 p) * j ∈ ({1, bm0, bm1, bm0 * bm1} : Set N7)) ∧
      ∃ k : Fin 2, ∀ i : Fin 3, j * u i * j⁻¹ = n7 (thetaW7 k i)

structure L2Checks7 : Prop where
  t : tCheck7 = true
  b : bCheck7 = true
  n : normalCheck7 = true
  inv : ∀ x : N7, x * x = 1 → (∀ k < 16, x ≠ n7 (tw7 k)) → ∃ n : N7, n * bm0 * n⁻¹ = x
  klein : KleinFact7
  dMem : dMemCheck7 = true
  dRel : dRelCheck7 = true
  ab : abWordsCheck7 = true
  center : ∀ z : N7, (∀ i : Fin 2, z * n7 (bGen7 i) * z⁻¹ ∈ ({1, bm0, bm1, bm0 * bm1} : Set N7)) →
    (∀ i : Fin 3, z * n7 (dGen7 i) = n7 (dGen7 i) * z) → z = 1
  thetaSq : thetaSqCheck7 = true
  swap : SwapFact7

section Model



theorem isTab7_tdd (i : Fin 3) : IsTab7 (tdd7 i) (n7 (dGen7 i)) := IsTab7.ofWord _

theorem isTab7_tth (k : Fin 2) (i : Fin 3) : IsTab7 (tth7 k i) (n7 (thetaW7 k i)) :=
  IsTab7.ofWord _

theorem isTab7_td0 (k : Fin 2) : IsTab7 (td0_7 k) (n7 (d0W7 k)) := IsTab7.ofWord _

theorem isTab7_evalT {u : Fin 3 → Table} {x : Fin 3 → N7} (hu : ∀ k, IsTab7 (u k) (x k))
    (w : List (Fin 3)) : IsTab7 (evalT7 u w) (w.map x).prod := by
  have key : ∀ (w : List (Fin 3)) (acc : Table) (a : N7), IsTab7 acc a →
      IsTab7 (w.foldl (fun acc k => compT 23 acc (u k)) acc) (a * (w.map x).prod) := by
    intro w
    induction w with
    | nil => intro acc a h; simpa using h
    | cons k w ih =>
      intro acc a h
      have := ih _ _ (h.mul (hu k))
      simpa [mul_assoc] using this
  simpa [evalT7] using key w (idT 23) 1 IsTab7.one

theorem n7_dEvalW (w : List (Fin 3)) :
    n7 (dEvalW7 w) = (w.map fun k => n7 (dGen7 k)).prod := by
  induction w with
  | nil => simp [dEvalW7, n7_nil]
  | cons k w ih =>
    have h : dEvalW7 (k :: w) = dGen7 k ++ dEvalW7 w := by simp [dEvalW7]
    rw [h, n7_append, ih, List.map_cons, List.prod_cons]

theorem d_mem7_of_check (hb : bCheck7 = true) (ht : tCheck7 = true) (h : dMemCheck7 = true) :
    (∀ i : Fin 3, n7 (dGen7 i) ∈ Subgroup.normalizer (n7B : Set N7)) ∧
      (∀ (k : Fin 2) (i : Fin 3), n7 (thetaW7 k i) ∈ Subgroup.normalizer (n7B : Set N7)) ∧
      (∀ k : Fin 2, n7 (d0W7 k) ∈ Subgroup.normalizer (n7B : Set N7)) := by
  simp only [dMemCheck7, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    true_implies] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨fun i => (normB7_iff hb ht (isTab7_tdd i) (IsTab7.of_word_inv _)).1 (h1 i),
    fun k i => (normB7_iff hb ht (isTab7_tth k i) (IsTab7.of_word_inv _)).1 (h2 k i),
    fun k => (normB7_iff hb ht (isTab7_td0 k) (IsTab7.of_word_inv _)).1 (h3 k)⟩

theorem mem_n7B_set (hb : bCheck7 = true) (ht : tCheck7 = true) (x : N7) :
    x ∈ n7B ↔ x ∈ ({1, bm0, bm1, bm0 * bm1} : Set N7) := by
  rw [mem_n7B_iff hb ht]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

theorem mem_normalizer_n7B (hb : bCheck7 = true) (ht : tCheck7 = true) (x : N7) :
    x ∈ Subgroup.normalizer (n7B : Set N7) ↔ ∀ p : Fin 2,
      x * n7 (bGen7 p) * x⁻¹ ∈ ({1, bm0, bm1, bm0 * bm1} : Set N7) ∧
      x⁻¹ * n7 (bGen7 p) * x ∈ ({1, bm0, bm1, bm0 * bm1} : Set N7) := by
  have hm := mem_n7B_iff hb ht
  have hs := mem_n7B_set hb ht
  rw [mem_normalizer_klein7 ((hm _).2 (Or.inr (Or.inl rfl)))
    ((hm _).2 (Or.inr (Or.inr (Or.inl rfl)))) (fun y hy => (hm y).1 hy)]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩ p
    fin_cases p
    · exact ⟨(hs _).1 h1, (hs _).1 h3⟩
    · exact ⟨(hs _).1 h2, (hs _).1 h4⟩
  · intro h
    exact ⟨(hs _).2 (h 0).1, (hs _).2 (h 1).1, (hs _).2 (h 0).2, (hs _).2 (h 1).2⟩

theorem inv_class7_of_check
    (hinv : ∀ x : N7, x * x = 1 → (∀ k < 16, x ≠ n7 (tw7 k)) → ∃ n : N7, n * bm0 * n⁻¹ = x)
    (x : N7) (hx : x * x = 1) (hxT : x ∉ n7T) : ∃ n : N7, n * bm0 * n⁻¹ = x := by
  refine hinv x hx fun k _ h => hxT ?_
  rw [h]
  exact n7_tw_mem k

theorem center7_of_check (hb : bCheck7 = true) (ht : tCheck7 = true)
    (hc : ∀ z : N7, (∀ i : Fin 2, z * n7 (bGen7 i) * z⁻¹ ∈ ({1, bm0, bm1, bm0 * bm1} : Set N7)) →
      (∀ i : Fin 3, z * n7 (dGen7 i) = n7 (dGen7 i) * z) → z = 1)
    (z : N7) (hz : z ∈ Subgroup.normalizer (n7B : Set N7))
    (hcomm : ∀ i : Fin 3, z * n7 (dGen7 i) = n7 (dGen7 i) * z) : z = 1 :=
  hc z (fun i => ((mem_normalizer_n7B hb ht z).1 hz i).1) hcomm

theorem theta_words7_of_check (h : thetaSqCheck7 = true) (k : Fin 2) (i : Fin 3) :
    ((thWords7 k i).map fun j => n7 (dGen7 j)).prod = n7 (thetaW7 k i) ∧
      ((thWords7 k i).map fun j => n7 (thetaW7 k j)).prod =
        n7 (d0W7 k) * n7 (dGen7 i) * (n7 (d0W7 k))⁻¹ := by
  simp only [thetaSqCheck7, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, List.mem_finRange,
    true_implies] at h
  obtain ⟨h1, h2⟩ := h k i
  exact ⟨((isTab7_evalT isTab7_tdd (thWords7 k i)).eq_iff (isTab7_tth k i)).1 h1,
    ((isTab7_evalT (isTab7_tth k) (thWords7 k i)).eq_iff
      (IsTab7.conj (isTab7_td0 k) (IsTab7.of_word_inv _) (isTab7_tdd i))).1 h2⟩

theorem lift_mk_pos7 (f : Fin 3 → N7) (l : List (Fin 3)) :
    FreeGroup.lift f (FreeGroup.mk (l.map fun k => (k, true))) = (l.map f).prod := by
  simp [FreeGroup.lift_mk, List.map_map, Function.comp_def]

theorem map_one_of_mul7 {f : N7 → N7} {N : Subgroup N7}
    (hfmul : ∀ x ∈ N, ∀ y ∈ N, f (x * y) = f x * f y) : f 1 = 1 := by
  have := hfmul 1 N.one_mem 1 N.one_mem
  simpa using this

theorem map_prod_of_mul7 {f : N7 → N7} {N : Subgroup N7}
    (hfmul : ∀ x ∈ N, ∀ y ∈ N, f (x * y) = f x * f y) {d : Fin 3 → N7} (hd : ∀ k, d k ∈ N)
    (w : List (Fin 3)) :
    f (w.map d).prod = (w.map fun k => f (d k)).prod ∧ (w.map d).prod ∈ N := by
  induction w with
  | nil => exact ⟨map_one_of_mul7 hfmul, N.one_mem⟩
  | cons k w ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
    exact ⟨by rw [hfmul _ (hd k) _ ih.2, ih.1], N.mul_mem (hd k) ih.2⟩

theorem swap7_of_check (hb : bCheck7 = true) (ht : tCheck7 = true) (hd : dMemCheck7 = true)
    (hrel : dRelCheck7 = true) (hab : abWordsCheck7 = true) (hsw : SwapFact7)
    (f : N7 → N7)
    (hfD : ∀ x ∈ Subgroup.normalizer (n7B : Set N7), f x ∈ Subgroup.normalizer (n7B : Set N7))
    (hfmul : ∀ x ∈ Subgroup.normalizer (n7B : Set N7), ∀ y ∈ Subgroup.normalizer (n7B : Set N7),
      f (x * y) = f x * f y)
    (hfinj : ∀ x ∈ Subgroup.normalizer (n7B : Set N7), ∀ y ∈ Subgroup.normalizer (n7B : Set N7),
      f x = f y → x = y)
    (hfA : ∀ a ∈ Subgroup.normalizer (n7B : Set N7), a ∈ n7T → f a ∈ n7B)
    (hfB : ∀ b ∈ n7B, f b ∈ n7T) :
    ∃ e ∈ Subgroup.normalizer (n7B : Set N7), ∃ k : Fin 2, ∀ i : Fin 3,
      e * f (n7 (dGen7 i)) * e⁻¹ = n7 (thetaW7 k i) := by
  set N := Subgroup.normalizer (n7B : Set N7) with hN
  have hdN : ∀ k : Fin 3, n7 (dGen7 k) ∈ N := fun k => (d_mem7_of_check hb ht hd).1 k
  have hf1 : f 1 = 1 := map_one_of_mul7 hfmul
  have hdw : ∀ w : List (Fin 3), IsTab7 (evalT7 tdd7 w) (w.map fun k => n7 (dGen7 k)).prod :=
    isTab7_evalT isTab7_tdd
  have hprod := fun w => map_prod_of_mul7 hfmul (d := fun k => n7 (dGen7 k)) hdN w
  have hrelU : ∀ w : List (Fin 3), evalT7 tdd7 w = idT 23 →
      (w.map fun k => f (n7 (dGen7 k))).prod = 1 := by
    intro w hw
    have h1 : (w.map fun k => n7 (dGen7 k)).prod = 1 := ((hdw w).eq_iff IsTab7.one).1 hw
    rw [← (hprod w).1, h1, hf1]
  have haW : ∀ w ∈ aWords7, (w.map fun k => f (n7 (dGen7 k))).prod ∈
      ({1, bm0, bm1, bm0 * bm1} : Set N7) ∧ (w.map fun k => f (n7 (dGen7 k))).prod ≠ 1 := by
    intro w hw
    simp only [abWordsCheck7, Bool.and_eq_true, List.all_eq_true] at hab
    have hw' := hab.1 w hw
    simp only [Bool.not_eq_true'] at hw'
    obtain ⟨⟨hnb, hcT⟩, hne⟩ := hw'
    have ha := hdw w
    have haN : (w.map fun k => n7 (dGen7 k)).prod ∈ N := by
      have := (normB7_iff hb ht (IsTab7.ofWord (dEvalW7 w)) (IsTab7.of_word_inv _)).1 hnb
      rwa [n7_dEvalW] at this
    have haT := (tTabs7_contains_iff ht ha).1 hcT
    have ha1 : (w.map fun k => n7 (dGen7 k)).prod ≠ 1 := fun h => by
      rw [(ha.eq_iff IsTab7.one).2 h] at hne
      simp at hne
    have hfa := hfA _ haN haT
    have hfa1 : f (w.map fun k => n7 (dGen7 k)).prod ≠ 1 := fun h =>
      ha1 (hfinj _ haN 1 N.one_mem (h.trans hf1.symm))
    rw [← (hprod w).1]
    exact ⟨(mem_n7B_set hb ht _).1 hfa, hfa1⟩
  have hbW : ∀ w ∈ bWords7, (∃ k < 16, (w.map fun k => f (n7 (dGen7 k))).prod = n7 (tw7 k)) ∧
      (w.map fun k => f (n7 (dGen7 k))).prod ≠ 1 := by
    intro w hw
    simp only [abWordsCheck7, Bool.and_eq_true, List.all_eq_true] at hab
    have hw' := hab.2 w hw
    simp only [Bool.not_eq_true'] at hw'
    obtain ⟨hcB, hne⟩ := hw'
    have hb' := hdw w
    have hbB := (bTabs7_contains_iff hb ht hb').1 hcB
    have hbN : (w.map fun k => n7 (dGen7 k)).prod ∈ N := Subgroup.le_normalizer hbB
    have hb1 : (w.map fun k => n7 (dGen7 k)).prod ≠ 1 := fun h => by
      rw [(hb'.eq_iff IsTab7.one).2 h] at hne
      simp at hne
    have hfb := hfB _ hbB
    have hfb1 : f (w.map fun k => n7 (dGen7 k)).prod ≠ 1 := fun h =>
      hb1 (hfinj _ hbN 1 N.one_mem (h.trans hf1.symm))
    obtain ⟨k, hk, e⟩ := (mem_n7T_iff ht _).1 hfb
    rw [← (hprod w).1]
    exact ⟨⟨k, hk, e⟩, hfb1⟩
  simp only [dRelCheck7, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hrel
  obtain ⟨⟨⟨r0, r1⟩, r2⟩, r3⟩ := hrel
  obtain ⟨j, hj, k, hji⟩ := hsw (fun k => f (n7 (dGen7 k)))
    (fun i => (mem_normalizer_n7B hb ht _).1 (hfD _ (hdN i))) (hrelU _ r0) (hrelU _ r1)
    (hrelU _ r2) (fun w hw => hrelU w (r3 w hw)) haW hbW
  exact ⟨j, (mem_normalizer_n7B hb ht j).2 hj, k, hji⟩

end Model

@[expose] noncomputable def l2Model7
    (h : L2Checks7) : T1Model N7 3 2 where
  T0 := n7T
  B0 := n7B
  b0 := bm0
  d := fun i => n7 (dGen7 i)
  d0 := fun k => n7 (d0W7 k)
  theta := fun k i => n7 (thetaW7 k i)
  b0_mem := Subgroup.subset_closure (by simp)
  d_mem := fun i => (d_mem7_of_check h.b h.t h.dMem).1 i
  d0_mem := fun k => (d_mem7_of_check h.b h.t h.dMem).2.2 k
  theta_mem := fun k i => (d_mem7_of_check h.b h.t h.dMem).2.1 k i
  inv_class := fun x hx hxT => inv_class7_of_check h.inv x hx hxT
  klein_class := fun B' hb0 hexp hcard hbot _ _ hcent =>
    klein_class7_of_checks h.t h.b h.n h.klein B' hb0 hexp hcard hbot hcent
  swap := fun f hfD hfmul hfinj hfA hfB =>
    swap7_of_check h.b h.t h.dMem h.dRel h.ab h.swap f hfD hfmul hfinj hfA hfB
  center := fun z hz hc => center7_of_check h.b h.t h.center z hz hc
  theta_sq := fun k =>
    ⟨fun i => (thWords7 k i).map fun j => (j, true), fun i => by
      refine ⟨?_, ?_⟩
      · rw [lift_mk_pos7]
        exact (theta_words7_of_check h.thetaSq k i).1
      · rw [lift_mk_pos7]
        exact (theta_words7_of_check h.thetaSq k i).2⟩

end CFSG.CGT.T75M23
