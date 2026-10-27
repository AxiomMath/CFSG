module

public import Certificates.Certificate38770
public import CFSG.GF2Type.SmithTypeE.DMod.StabOrbit
public import CFSG.GF2Type.SmithTypeE.E7.ModConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open CFSG.SmithD6 (wt adjW tvCols applyCols wtIdx mf7ChkWt mf7ChkTvAdj0 mf7Ap mf7All mf7Any
  mf7Ap_eq mf7_wt_wtIdx)
open CFSG.GF2Type.SmithTypeE.DMod

theorem wt7_forIn_flag (q : Nat → Bool) (b : Bool) (L : List Nat) :
    forIn L ((none : Option Bool), ()) (fun i _ => if q i = true then
        (pure (ForInStep.done ((some b : Option Bool), ())) : Id (ForInStep (Option Bool × Unit)))
      else pure (ForInStep.yield ((none : Option Bool), ()))) =
    (pure (if L.any q = true then ((some b : Option Bool), ()) else ((none : Option Bool), ())) :
      Id (Option Bool × Unit)) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.forIn_cons, List.any_cons]
    by_cases ha : q a = true
    · simp [ha]
    · simp only [ha, if_false, Bool.false_or] at ih ⊢
      simp [ha, ih]

theorem wt7_mf7All_eq (n : Nat) (p : Nat → Bool) :
    mf7All n p = !((List.range' 0 n).any fun i => !p i) := by
  unfold mf7All
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  simp only [wt7_forIn_flag, pure_bind]
  by_cases hA : (List.range' 0 n).any (fun i => !p i) = true
  · simp [hA] <;> rfl
  · simp [hA] <;> rfl

theorem wt7_mf7Any_eq (n : Nat) (p : Nat → Bool) :
    mf7Any n p = (List.range' 0 n).any p := by
  unfold mf7Any
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  simp only [wt7_forIn_flag, pure_bind]
  by_cases hA : (List.range' 0 n).any p = true
  · simp [hA] <;> rfl
  · simp [hA] <;> rfl

theorem wt7_all_iff (n : Nat) (p : Nat → Bool) :
    mf7All n p = true ↔ ∀ i < n, p i = true := by
  rw [wt7_mf7All_eq]
  simp [List.any_eq_true, List.mem_range'_1]

theorem wt7_any_iff (n : Nat) (p : Nat → Bool) :
    mf7Any n p = true ↔ ∃ i < n, p i = true := by
  rw [wt7_mf7Any_eq]
  simp [List.any_eq_true, List.mem_range'_1]

theorem wt7_check_wt :
    (∀ j < 75735, wtIdx (wt j) = j) ∧ (∀ i < 75735, wt i ≠ 0 ∧ wt i < 4294967296) ∧
      ∀ i < 75735, ∃ j < 75735, adjW i j = true ∧ wt j ≠ wt i := by
  have h := Certificates.certificate38770.1
  unfold mf7ChkWt at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun j hj => beq_iff_eq.mp ((wt7_all_iff _ _).mp h1 j hj), fun i hi => ?_,
    fun i hi => ?_⟩
  · have h4 := (wt7_all_iff _ _).mp h2 i hi
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h4
    exact h4
  · obtain ⟨j, hj, hpj⟩ := (wt7_any_iff _ _).mp ((wt7_all_iff _ _).mp h3 i hi)
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hpj
    exact ⟨j, hj, hpj⟩

theorem wt7_check_tv0 {i : Nat} (hi : i < 75735) :
    ∃ j < 75735, wt j = applyCols (tvCols 0) (wt i) ∧ adjW i j = true := by
  have h := Certificates.certificate38770.2
  unfold mf7ChkTvAdj0 at h
  dsimp only at h
  have h' := (wt7_all_iff _ _).mp h i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, mf7Ap_eq] at h'
  exact ⟨wtIdx (applyCols (tvCols 0) (wt i)), h'.1.1, h'.1.2, h'.2⟩

theorem wt7_check_tv0' (k0 : Nat) (hk0 : k0 = 0) {i : Nat}
    (hi : i < 75735) :
    ∃ j < 75735, wt j = applyCols (tvCols k0) (wt i) ∧ adjW i j = true := by
  subst hk0
  exact wt7_check_tv0 hi

theorem wt7_lt {i : Nat} (hi : i < 75735) : wt i < 2 ^ 32 :=
  (wt7_check_wt.2.1 i hi).2

theorem wt7_wtIdx {j : Nat} (hj : j < 75735) :
    wtIdx (wt j) = j :=
  wt7_check_wt.1 j hj

theorem wt7_adjW_iff {a b : Nat} (ha : a < 75735)
    (hb : b < 75735) :
    adjW a b = true ↔ wtV a = wtV b ∨ ∃ c < 75735, wtV c = wtV a + wtV b := by
  unfold adjW
  rw [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro (h | h)
    · exact Or.inl (congrArg decode32 h)
    · refine Or.inr ⟨wtIdx (wt a ^^^ wt b), h, ?_⟩
      rw [wtV, wtV, wtV, mf7_wt_wtIdx _ h, decode32_xor]
  · rintro (h | ⟨c, hc, h⟩)
    · exact Or.inl (eq_of_decode32_eq (wt7_lt ha) (wt7_lt hb) h)
    · have hx : wt c = wt a ^^^ wt b :=
        eq_of_decode32_eq (wt7_lt hc) (Nat.xor_lt_two_pow (wt7_lt ha) (wt7_lt hb))
          (by rw [decode32_xor]; exact h)
      right
      have e : wtIdx (wt a ^^^ wt b) = c := by
        rw [← hx]
        exact wt7_wtIdx hc
      rw [e]
      exact hc

theorem wt7_adjW_smul
    (g : TD6) {a b : Fin 75735} (h : adjW a b = true) :
    adjW (g • a).val (g • b).val = true := by
  rw [wt7_adjW_iff a.isLt b.isLt] at h
  rw [wt7_adjW_iff (g • a).isLt (g • b).isLt]
  rcases h with h | ⟨c, hc, hcw⟩
  · left
    rw [← rhoMod_wtV g a, ← rhoMod_wtV g b, h]
  · right
    refine ⟨(g • (⟨c, hc⟩ : Fin 75735)).val, (g • (⟨c, hc⟩ : Fin 75735)).isLt, ?_⟩
    have e1 : wtV (g • (⟨c, hc⟩ : Fin 75735)).val = rhoMod g (wtV c) :=
      (rhoMod_wtV g ⟨c, hc⟩).symm
    rw [e1, hcw, map_add, rhoMod_wtV g a, rhoMod_wtV g b]

theorem wt7_tvE_rho
    (g : TD6) {k0 k : Fin 365211}
    (hk : (g : Equiv.Perm (Fin 365211)) k0 = k) (v : V) :
    tvE k (rhoMod g v) = rhoMod g (tvE k0 v) := by
  subst hk
  rw [tvE_conj]
  show rhoMod g (tvE k0 ((rhoMod g).symm (rhoMod g v))) = rhoMod g (tvE k0 v)
  rw [LinearEquiv.symm_apply_apply]

theorem wt_ne_zero7 {i : Nat} (hi : i < 75735) : wt i ≠ 0 :=
  (wt7_check_wt.2.1 i hi).1

theorem exists_adj7 {i : Nat} (hi : i < 75735) :
    ∃ j < 75735, adjW i j = true ∧ wt j ≠ wt i :=
  wt7_check_wt.2.2 i hi

theorem wt_ne_xor7 {i j : Nat} (hi : i < 75735) (hj : j < 75735)
    (h : adjW i j = false) : ∀ k < 75735, wt k ≠ wt i ^^^ wt j := by
  intro k hk heq
  have h1 : wtIdx (wt i ^^^ wt j) < 75735 := by
    rw [← heq, wt7_wtIdx hk]
    exact hk
  have h2 : adjW i j = true := by
    simp [adjW, h1]
  rw [h] at h2
  exact absurd h2 (by decide)

theorem tv_wt7
    {k i : Nat} (hk : k < 365211) (hi : i < 75735) :
    ∃ j < 75735, wt j = applyCols (tvCols k) (wt i) ∧ adjW i j = true := by
  obtain ⟨g, hg, hg0⟩ := exists_mem_TD6_apply_zero_eq (⟨k, hk⟩ : Fin 365211)
  obtain ⟨G, hG0⟩ : ∃ G : TD6, (G : Equiv.Perm (Fin 365211)) 0 = ⟨k, hk⟩ := ⟨⟨g, hg⟩, hg0⟩
  obtain ⟨i', hi'⟩ : ∃ i' : Fin 75735, (G • i').val = i :=
    ⟨G⁻¹ • (⟨i, hi⟩ : Fin 75735), congrArg Fin.val (smul_inv_smul G (⟨i, hi⟩ : Fin 75735))⟩
  subst hi'
  obtain ⟨j', hj', hwj', hadj'⟩ := wt7_check_tv0' (0 : Fin 365211).val rfl i'.isLt
  have h0 : tvE 0 (wtV i'.val) = wtV j' := by
    unfold tvE
    rw [wtV, wtV, hwj', tvEquiv_decode (0 : Fin 365211).isLt]
  have hA : tvE ⟨k, hk⟩ (wtV (G • i').val) = wtV (G • (⟨j', hj'⟩ : Fin 75735)).val := by
    rw [← rhoMod_wtV G i', wt7_tvE_rho G hG0, h0]
    exact rhoMod_wtV G ⟨j', hj'⟩
  have hB : decode32 (wt (G • (⟨j', hj'⟩ : Fin 75735)).val) =
      decode32 (applyCols (tvCols k) (wt (G • i').val)) :=
    hA.symm.trans (tvEquiv_decode hk (wt (G • i').val))
  refine ⟨(G • (⟨j', hj'⟩ : Fin 75735)).val, (G • (⟨j', hj'⟩ : Fin 75735)).isLt, ?_, ?_⟩
  · exact eq_of_decode32_eq (wt7_lt (G • (⟨j', hj'⟩ : Fin 75735)).isLt)
      (applyCols_tv_lt hk _) hB
  · exact wt7_adjW_smul G hadj'

end CFSG.GF2Type.SmithTypeE.E7
