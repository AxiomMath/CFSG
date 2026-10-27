module

public import Certificates.Data.Kernel.E6Syl3
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Order3Core
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Order3Defs

public section

namespace CFSG.KC.E6Syl3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LieType.SeitzGeneration.ExcWideThree.E6Order3 CFSG.HardMathSupport.Timmesfeld.CrossChar


noncomputable def wordW (w : List ℕ) : WeylGroup Tag.E6 :=
  (w.map fun i => if h : i < 6 then simple Tag.E6 ⟨i, h⟩ else 1).prod

theorem wordW_cons (i : ℕ) (w : List ℕ) (h : i < 6) :
    wordW (i :: w) = simple Tag.E6 ⟨i, h⟩ * wordW w := by
  simp only [wordW, List.map_cons, List.prod_cons, dif_pos h]

theorem rep_tImg {t : List ℕ} {x : WeylGroup Tag.E6} (hx : e6Certificate.Represents t x) {i : ℕ}
    (hi : i < 6) : e6Certificate.Represents (tImg i t) (simple Tag.E6 ⟨i, hi⟩ * x) :=
  RootCertificate.represents_tupleImage e6Certificate_check hx ⟨i, hi⟩

theorem rep_wordT {t : List ℕ} {x : WeylGroup Tag.E6} (hx : e6Certificate.Represents t x) :
    ∀ w : List ℕ, (∀ i ∈ w, i < 6) → e6Certificate.Represents (wordT w t) (wordW w * x)
  | [], _ => by simpa [wordT, wordW] using hx
  | i :: w, hw => by
    have hi : i < 6 := hw i List.mem_cons_self
    have ih := rep_wordT hx w fun j hj => hw j (List.mem_cons_of_mem _ hj)
    rw [wordW_cons i w hi, mul_assoc]
    exact rep_tImg ih hi

theorem rep_powT {w : List ℕ} (hw : ∀ i ∈ w, i < 6) {t : List ℕ} {x : WeylGroup Tag.E6}
    (hx : e6Certificate.Represents t x) :
    ∀ n : ℕ, e6Certificate.Represents (powT w n t) (wordW w ^ n * x)
  | 0 => by simpa [powT] using hx
  | n + 1 => by
    rw [pow_succ', mul_assoc]
    exact rep_wordT (rep_powT hw hx n) w hw

theorem tuple_unique {t t' : List ℕ} {x : WeylGroup Tag.E6} (h : e6Certificate.Represents t x)
    (h' : e6Certificate.Represents t' x) : t = t' := by
  have hl : t.length = 6 := h.1
  have hl' : t'.length = 6 := h'.1
  refine List.ext_getElem (by rw [hl, hl']) fun j hj hj' => ?_
  have hj6 : j < Tag.E6.rank := by rw [hl] at hj; exact hj
  have e1 := h.2 ⟨j, hj6⟩
  have e2 := h'.2 ⟨j, hj6⟩
  rw [← List.getD_eq_getElem t 0 hj, ← List.getD_eq_getElem t' 0 hj']
  exact root_inj (len72 ▸ e1.1) (len72 ▸ e2.1) (e1.2.trans e2.2.symm)

theorem nodup_of_nodupB : ∀ L : List (List ℕ), nodupB L = true → L.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.2 ⟨fun hx => ?_, nodup_of_nodupB xs h.2⟩
    have hc := List.contains_iff_mem.2 hx
    rw [h.1] at hc
    exact absurd hc (by decide)

noncomputable def qSub (gw : List (List ℕ)) : Subgroup (WeylGroup Tag.E6) :=
  Subgroup.closure {g | ∃ w ∈ gw, g = wordW w}

theorem qSub_le {gw : List (List ℕ)} {K : Subgroup (WeylGroup Tag.E6)}
    (h : ∀ w ∈ gw, wordW w ∈ K) : qSub gw ≤ K := by
  refine (Subgroup.closure_le K).2 ?_
  rintro g ⟨w, hw, rfl⟩
  exact h w hw

theorem wordW_getD_mem (gw : List (List ℕ)) (k : ℕ) : wordW (gw.getD k []) ∈ qSub gw := by
  by_cases hk : k < gw.length
  · rw [List.getD_eq_getElem _ _ hk]
    exact Subgroup.subset_closure ⟨_, List.getElem_mem hk, rfl⟩
  · rw [List.getD_eq_default _ _ (by omega)]
    simpa [wordW] using (qSub gw).one_mem

theorem letters_getD {gw : List (List ℕ)} (hl : ∀ w ∈ gw, ∀ i ∈ w, i < 6) (k : ℕ) :
    ∀ i ∈ gw.getD k [], i < 6 := by
  by_cases hk : k < gw.length
  · rw [List.getD_eq_getElem _ _ hk]
    exact hl _ (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ (by omega)]
    simp

theorem exists_mem_of_mem_qTups {gw : List (List ℕ)} (hl : ∀ w ∈ gw, ∀ i ∈ w, i < 6)
    {t : List ℕ} (ht : t ∈ qTups gw) : ∃ x ∈ qSub gw, e6Certificate.Represents t x := by
  simp only [qTups, List.mem_flatMap, List.mem_map, List.mem_range] at ht
  obtain ⟨a, -, b, -, c, -, d, -, rfl⟩ := ht
  have h1 := RootCertificate.represents_one (C := e6Certificate) e6Certificate_check
  refine ⟨wordW (gw.getD 0 []) ^ a * (wordW (gw.getD 1 []) ^ b * (wordW (gw.getD 2 []) ^ c *
    (wordW (gw.getD 3 []) ^ d * 1))), ?_, ?_⟩
  · have m := fun k => wordW_getD_mem gw k
    exact mul_mem (pow_mem (m 0) a) (mul_mem (pow_mem (m 1) b) (mul_mem (pow_mem (m 2) c)
      (mul_mem (pow_mem (m 3) d) (one_mem _))))
  · exact rep_powT (letters_getD hl 0) (rep_powT (letters_getD hl 1) (rep_powT (letters_getD hl 2)
      (rep_powT (letters_getD hl 3) h1 d) c) b) a

theorem exists_subgroup_of_qCheck {gw : List (List ℕ)} (h : qCheckWith gw (qTups gw) = true) :
    Nat.card (qSub gw) = 81 ∧ ∀ y ∈ qSub gw, ∃ t ∈ qTups gw, e6Certificate.Represents t y := by
  set Q := qTups gw with hQ
  simp only [qCheckWith, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨hl, hlen⟩, hnd⟩, hid⟩, hcl⟩ := h
  have hnodup := nodup_of_nodupB Q hnd
  have hstep : ∀ w ∈ gw, ∀ z : WeylGroup Tag.E6, (∃ t ∈ Q, e6Certificate.Represents t z) →
      ∃ t ∈ Q, e6Certificate.Represents t (wordW w * z) := by
    rintro w hw z ⟨t, ht, hrep⟩
    exact ⟨_, hcl t ht w hw, rep_wordT hrep w (hl w hw)⟩
  have hpow : ∀ w ∈ gw, ∀ m : ℕ, ∀ z : WeylGroup Tag.E6, (∃ t ∈ Q, e6Certificate.Represents t z) →
      ∃ t ∈ Q, e6Certificate.Represents t (wordW w ^ m * z) := by
    intro w hw m
    induction m with
    | zero => intro z hz; simpa using hz
    | succ m ih =>
      intro z hz
      rw [pow_succ', mul_assoc]
      exact hstep w hw _ (ih z hz)
  have hcover : ∀ g ∈ qSub gw, ∃ t ∈ Q, e6Certificate.Represents t g := by
    intro g hg
    induction hg using Subgroup.closure_induction_left with
    | one => exact ⟨_, hid, RootCertificate.represents_one e6Certificate_check⟩
    | mul_left x hx z _ ih =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact hstep w hw z ih
    | inv_mul_cancel x hx z _ ih =>
      obtain ⟨w, hw, rfl⟩ := hx
      obtain ⟨t, ht, hrep⟩ := hpow w hw (orderOf (wordW w) - 1) z ih
      refine ⟨t, ht, ?_⟩
      convert hrep using 2
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [← pow_succ, Nat.sub_add_cancel (isOfFinOrder_of_finite (wordW w)).orderOf_pos,
        pow_orderOf_eq_one]
  refine ⟨?_, hcover⟩
  have hex : ∀ i : Fin 81, ∃ x ∈ qSub gw,
      e6Certificate.Represents (Q[i]'(by rw [hlen]; exact i.2)) x :=
    fun i => exists_mem_of_mem_qTups hl (List.getElem_mem _)
  choose y hyS hyR using hex
  have e : Fin 81 ≃ qSub gw := Equiv.ofBijective (fun i => ⟨y i, hyS i⟩)
    ⟨fun i j hij => by
      have h1 : y i = y j := congrArg Subtype.val hij
      have h2 := tuple_unique (hyR i) (h1 ▸ hyR j)
      exact Fin.ext ((List.Nodup.getElem_inj_iff hnodup).1 h2),
    fun g => by
      obtain ⟨t, ht, hrep⟩ := hcover g g.2
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
      exact ⟨⟨i, hlen ▸ hi⟩, Subtype.ext (RootCertificate.represents_unique (hyR _) hrep)⟩⟩
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem range6 : List.range 6 = [0, 1, 2, 3, 4, 5] := rfl

theorem ofFn6 (v : Fin Tag.E6.rank → ℤ) :
    List.ofFn v = [v 0, v 1, v 2, v 3, v 4, v 5] :=
  rfl

theorem rvL_eq (k : ℕ) : rvL k = List.ofFn (e6Certificate.root k) := by
  rw [ofFn6]
  rfl

theorem eV_eq (j : Fin Tag.E6.rank) : eV j = List.ofFn (Pi.single j 1 : Fin Tag.E6.rank → ℤ) := by
  revert j
  decide

theorem addV_eq (u v : Fin Tag.E6.rank → ℤ) :
    addV (List.ofFn u) (List.ofFn v) = List.ofFn (u + v) := by
  simp only [ofFn6, addV, List.zipWith_cons_cons, List.zipWith_nil_right, Pi.add_apply]

theorem smulV_eq (c : ℤ) (v : Fin Tag.E6.rank → ℤ) :
    smulV c (List.ofFn v) = List.ofFn (c • v) := by
  simp only [ofFn6, smulV, List.map_cons, List.map_nil, Pi.smul_apply, smul_eq_mul]

theorem negV_eq (v : Fin Tag.E6.rank → ℤ) : negV (List.ofFn v) = List.ofFn (-v) := by
  simp only [ofFn6, negV, List.map_cons, List.map_nil, Pi.neg_apply]

theorem zeroV_eq : zeroV = List.ofFn (0 : Fin Tag.E6.rank → ℤ) := by
  rw [ofFn6]
  rfl

theorem ofFn_inj' {u v : Fin Tag.E6.rank → ℤ} (h : List.ofFn u = List.ofFn v) : u = v :=
  List.ofFn_injective h

theorem getD_ofFn6 (v : Fin Tag.E6.rank → ℤ) (j : Fin Tag.E6.rank) :
    (List.ofFn v).getD j 0 = v j := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem actV_ofFn {t : List ℕ} {w : WeylGroup Tag.E6} (hrep : e6Certificate.Represents t w)
    (v : Fin Tag.E6.rank → ℤ) : actV t (List.ofFn v) = List.ofFn (w • v) := by
  rw [← RootCertificate.tupleVec_eq hrep v]
  unfold actV RootCertificate.tupleVec
  rw [range6]
  simp only [List.foldr_cons, List.foldr_nil, rvL_eq, zeroV_eq]
  have g : ∀ k (hk : k < 6), (List.ofFn v).getD k 0 = v ⟨k, hk⟩ :=
    fun k hk => getD_ofFn6 v ⟨k, hk⟩
  simp only [g _ (by decide : 0 < 6), g _ (by decide : 1 < 6), g _ (by decide : 2 < 6),
    g _ (by decide : 3 < 6), g _ (by decide : 4 < 6), g _ (by decide : 5 < 6), smulV_eq, addV_eq]
  congr 1

theorem actV_rvL {t : List ℕ} {w : WeylGroup Tag.E6} (hrep : e6Certificate.Represents t w)
    (k : ℕ) : actV t (rvL k) = List.ofFn (w • e6Certificate.root k) := by
  rw [rvL_eq, actV_ofFn hrep]

theorem notOrd3_sound {t : List ℕ} {w : WeylGroup Tag.E6} (hrep : e6Certificate.Represents t w)
    (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) (h : notOrd3 t = true) : False := by
  simp only [notOrd3, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, bne_iff_ne, ne_eq] at h
  rcases h with h | ⟨j, hj, hne⟩
  · exact hw1 (RootCertificate.represents_unique hrep (h ▸
      RootCertificate.represents_one e6Certificate_check))
  · have hj6 : j < Tag.E6.rank := List.mem_range.1 hj
    apply hne
    rw [show j = ((⟨j, hj6⟩ : Fin Tag.E6.rank) : ℕ) from rfl, eV_eq, actV_ofFn hrep,
      actV_ofFn hrep, actV_ofFn hrep, ← mul_smul, ← mul_smul, ← pow_three', hw3, one_smul]

theorem normV_ofFn {t : List ℕ} {w : WeylGroup Tag.E6} (hrep : e6Certificate.Represents t w)
    (v : Fin Tag.E6.rank → ℤ) : normV t (List.ofFn v) = List.ofFn (v + w • v + w • w • v) := by
  rw [normV, actV_ofFn hrep, actV_ofFn hrep, addV_eq, addV_eq]

theorem k3B_sound {t : List ℕ} {w : WeylGroup Tag.E6} (hrep : e6Certificate.Represents t w)
    (h : k3B t = true) : E6Kind3A2 w := by
  refine norm_zero_of_single fun j => ?_
  simp only [k3B, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have hj := h j j.2
  rw [eV_eq, normV_ofFn hrep, zeroV_eq] at hj
  exact ofFn_inj' hj

theorem sumB_sound {a b c : ℕ} (h : sumB a b c = true) :
    a < 72 ∧ b < 72 ∧ c < 72 ∧
      e6Certificate.root c = e6Certificate.root a + e6Certificate.root b := by
  simp only [sumB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, rvL_eq, addV_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, ofFn_inj' h.2⟩

theorem kA2B_sound {t : List ℕ} {w : WeylGroup Tag.E6} (hrep : e6Certificate.Represents t w)
    {a b c : ℕ} (h : kA2B t a b c = true) : E6KindA2 w := by
  simp only [kA2B, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨ha, hb, hc, hsum⟩ := sumB_sound h.1
  refine ⟨e6Certificate.root a, e6Certificate.root b, isA2Pair_of_add ha hb hc hsum, ?_⟩
  refine ext_single fun j => ?_
  have hj72 : (j : ℕ) < 72 := by have := j.2; simp only [Tag.rank] at this; omega
  obtain ⟨h1lt, h1⟩ := reflIdx_spec 72 b (by omega) hb j hj72
  obtain ⟨-, h2⟩ := reflIdx_spec 72 a (by omega) ha _ h1lt
  rw [mul_smul, ← root_basis j, ← h1, ← h2, ← h.2 j j.2, root_basis j]
  exact ((hrep.2 j).2).symm

theorem k2B_sound {t : List ℕ} {w : WeylGroup Tag.E6} (hrep : e6Certificate.Represents t w)
    {a b c m : ℕ} (h : k2B t a b c m = true) :
    E6Kind2A2 w (e6Certificate.root a) (e6Certificate.root b) := by
  simp only [k2B, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hs, hm⟩, hfa⟩, hfb⟩, hfix⟩, hmu⟩, hrng⟩ := h
  obtain ⟨ha, hb, hc, hsum⟩ := sumB_sound hs
  rw [actV_rvL hrep, rvL_eq] at hfa hfb
  refine ⟨isA2Pair_of_add ha hb hc hsum, ofFn_inj' hfa, ofFn_inj' hfb, ?_, ?_, ?_⟩
  · intro γ hγ hwγ
    obtain ⟨k, hk, rfl⟩ := exists_root72 hγ
    have hk' := hfix k hk
    simp only [rvL_eq, actV_ofFn hrep, negV_eq, hwγ, not_true_eq_false, false_or] at hk'
    simp only [a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff, ← hsum]
    rcases hk' with (((((h | h) | h) | h) | h) | h) <;> have := ofFn_inj' h <;> tauto
  · refine ⟨e6Certificate.root m, ?_⟩
    rw [rvL_eq, normV_ofFn hrep, rvL_eq, rvL_eq, smulV_eq, addV_eq] at hmu
    rw [ofFn_inj' hmu, two_nsmul, two_zsmul]
  · intro j
    have hj := hrng j j.2
    rw [eV_eq, normV_ofFn hrep, rvL_eq, rvL_eq, smulV_eq, smulV_eq, addV_eq] at hj
    exact ⟨_, _, ofFn_inj' hj⟩

theorem kindOK_sound {t c : List ℕ} {w : WeylGroup Tag.E6} (hrep : e6Certificate.Represents t w)
    (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) (h : kindOK t c = true) :
    E6KindA2 w ∨ (∃ γ₁ γ₂, E6Kind2A2 w γ₁ γ₂) ∨ E6Kind3A2 w := by
  unfold kindOK at h
  split at h
  · exact (notOrd3_sound hrep hw3 hw1 h).elim
  · exact Or.inr (Or.inr (k3B_sound hrep h))
  · exact Or.inl (kA2B_sound hrep h)
  · exact Or.inr (Or.inl ⟨_, _, k2B_sound hrep h⟩)
  · exact absurd h (by simp)

theorem kindOK_of_mem {Q W : List (List ℕ)} (h : kindsCheck Q W = true) {t : List ℕ}
    (ht : t ∈ Q) : ∃ c, kindOK t c = true := by
  simp only [kindsCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
  refine ⟨W[i]'(h.1 ▸ hi), h.2 (Q[i], W[i]'(h.1 ▸ hi)) ?_⟩
  rw [List.mem_iff_getElem]
  exact ⟨i, by rw [List.length_zip, ← h.1, Nat.min_self]; exact hi, by rw [List.getElem_zip]⟩

end CFSG.KC.E6Syl3
