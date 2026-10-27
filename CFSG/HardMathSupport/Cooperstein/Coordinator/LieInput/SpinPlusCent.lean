module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinPlusMat
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.OrthPlus

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

section D131
open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary

section ShapeD

variable {F : Type} [Field F] [CharP F 2] {N : ℕ}

theorem exists_two_admissible (hN : 6 ≤ N) (hev : Even N) (j : Fin (N / 2)) (a : Fin N) :
    ∃ y1 y2 : Fin N, y1 ≠ y2 ∧ ¬ InA j y1 ∧ ¬ InA j y2 ∧ y1 ≠ Fin.rev a ∧ y2 ≠ Fin.rev a := by
  have hj := j.isLt
  obtain ⟨m, hm⟩ := hev
  let p1 : Fin N := ⟨N - 1, by omega⟩
  let p2 : Fin N := ⟨N - 2, by omega⟩
  let p3 : Fin N := ⟨N - 3, by omega⟩
  have h1 : ¬ InA j p1 := by simp only [InA, p1]; omega
  have h2 : ¬ InA j p2 := by simp only [InA, p2]; omega
  have h3 : ¬ InA j p3 := by simp only [InA, p3]; omega
  by_cases e1 : p1 = Fin.rev a
  · exact ⟨p2, p3, by simp [p2, p3, Fin.ext_iff]; omega, h2, h3, by
      intro e; have := congrArg Fin.val e; have := congrArg Fin.val e1
      simp only [p1, p2, Fin.val_rev] at *; omega, by
      intro e; have := congrArg Fin.val e; have := congrArg Fin.val e1
      simp only [p1, p3, Fin.val_rev] at *; omega⟩
  · by_cases e2 : p2 = Fin.rev a
    · exact ⟨p1, p3, by simp [p1, p3, Fin.ext_iff]; omega, h1, h3, e1, by
        intro e; have := congrArg Fin.val e; have := congrArg Fin.val e2
        simp only [p2, p3, Fin.val_rev] at *; omega⟩
    · exact ⟨p1, p2, by simp [p1, p2, Fin.ext_iff]; omega, h1, h2, e1, e2⟩


theorem two_others {N : ℕ} (j : Fin (N / 2)) (hj : 2 ≤ j.val) (w : Fin N) :
    ∃ x z : Fin N, x ≠ w ∧ z ≠ w ∧ x ≠ z ∧ InA j x ∧ InA j z := by
  have h2 : 2 < N := by have := j.isLt; omega
  by_cases h0 : w.val = 0
  · exact ⟨⟨1, by omega⟩, ⟨2, by omega⟩, by simp [Fin.ext_iff]; omega, by simp [Fin.ext_iff]; omega,
      by simp [Fin.ext_iff], by simp only [InA]; omega, by simp only [InA]; omega⟩
  · by_cases h1 : w.val = 1
    · exact ⟨⟨0, by omega⟩, ⟨2, by omega⟩, by simp [Fin.ext_iff]; omega, by simp [Fin.ext_iff]; omega,
        by simp [Fin.ext_iff], by simp only [InA]; omega, by simp only [InA]; omega⟩
    · exact ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]; omega, by simp [Fin.ext_iff]; omega,
        by simp [Fin.ext_iff], by simp only [InA]; omega, by simp only [InA]; omega⟩

theorem shape_of_comm_D (G : Matrix (Fin N) (Fin N) F) (j : Fin (N / 2)) (hN : 6 ≤ N)
    (hev : Even N) (hsize : 3 ≤ j.val + 1 ∨ j.val + 1 < N / 2)
    (hunit : ∀ a b, ∑ t, G t a * G (Fin.rev t) b = if b = Fin.rev a then 1 else 0)
    (hR : ∀ x y : Fin N, InA j x → ¬ InA j y → y ≠ Fin.rev x →
      G * rootMatrix (RingEquiv.refl F) x y (1 : F) = rootMatrix (RingEquiv.refl F) x y 1 * G) :
    ShS j 1 G := by
  have hjN := j.isLt
  have E : ∀ x y, InA j x → ¬ InA j y → y ≠ Fin.rev x → ∀ u v,
      (if v = y then G u x else 0) - (if v = Fin.rev x then G u (Fin.rev y) else 0) =
      (if u = x then G y v else 0) - (if u = Fin.rev y then G (Fin.rev x) v else 0) := by
    intro x y hx hy hyx u v
    have key := congrFun (congrFun (hR x y hx hy hyx) u) v
    simp only [mul_rootMatrix_apply, rootMatrix_mul_apply, RingEquiv.refl_apply, mul_one,
      one_mul] at key
    linear_combination key
  have C1 : ∀ x y, InA j x → ¬ InA j y → y ≠ Fin.rev x → ∀ u,
      G u x = (if u = x then G y y else 0) - (if u = Fin.rev y then G (Fin.rev x) y else 0) := by
    intro x y hx hy hyx u
    have := E x y hx hy hyx u y
    simpa [hyx] using this
  have colx : ∀ x, InA j x → ∀ u, u ≠ x → G u x = 0 := by
    intro x hx u hu
    obtain ⟨y1, y2, h12, hy1, hy2, hr1, hr2⟩ := exists_two_admissible hN hev j x
    by_cases hu1 : u = Fin.rev y1
    · have hu2 : u ≠ Fin.rev y2 := by
        intro e; exact h12 (Fin.rev_injective (hu1.symm.trans e))
      rw [C1 x y2 hx hy2 hr2 u, if_neg hu, if_neg hu2]; simp
    · rw [C1 x y1 hx hy1 hr1 u, if_neg hu, if_neg hu1]; simp
  have diagy : ∀ x y, InA j x → ¬ InA j y → y ≠ Fin.rev x → G y y = G x x := by
    intro x y hx hy hyx
    have := C1 x y hx hy hyx x
    have hne : x ≠ Fin.rev y := fun e => hyx (by rw [e, Fin.rev_rev])
    rw [if_pos rfl, if_neg hne] at this
    linear_combination -this
  have R1 : ∀ x y, InA j x → ¬ InA j y → y ≠ Fin.rev x → ∀ v,
      G y v = (if v = y then G x x else 0) - (if v = Fin.rev x then G x (Fin.rev y) else 0) := by
    intro x y hx hy hyx v
    have := E x y hx hy hyx x v
    have hne : x ≠ Fin.rev y := fun e => hyx (by rw [e, Fin.rev_rev])
    rw [if_pos rfl, if_neg hne] at this
    linear_combination -this
  have Rrow : ∀ x y, InA j x → ¬ InA j y → y ≠ Fin.rev x → ∀ v,
      G (Fin.rev x) v = if v = Fin.rev x then G (Fin.rev y) (Fin.rev y) else 0 := by
    intro x y hx hy hyx v
    have := E x y hx hy hyx (Fin.rev y) v
    have hne : Fin.rev y ≠ x := fun e => hyx (by rw [← e, Fin.rev_rev])
    have h0 : G (Fin.rev y) x = 0 := colx x hx _ hne
    simp only [h0, hne, if_false, if_true, ite_self, zero_sub] at this
    by_cases hv : v = Fin.rev x
    · simp only [hv, if_true] at this ⊢
      linear_combination this
    · simp only [hv, if_false] at this ⊢
      linear_combination this
  have gh : ∀ x, InA j x → G x x * G (Fin.rev x) (Fin.rev x) = 1 := by
    intro x hx
    have := hunit x (Fin.rev x)
    rw [if_pos rfl, Finset.sum_eq_single x] at this
    · exact this
    · intro t _ ht
      rw [colx x hx t ht, zero_mul]
    · intro h; exact absurd (Finset.mem_univ x) h
  have hh : ∀ x y, InA j x → ¬ InA j y → y ≠ Fin.rev x →
      G (Fin.rev y) (Fin.rev y) = G (Fin.rev x) (Fin.rev x) := by
    intro x y hx hy hyx
    have := Rrow x y hx hy hyx (Fin.rev x)
    rw [if_pos rfl] at this
    exact this.symm
  have hsq : ∀ g : F, g * g = 1 → g = 1 := by
    intro g hg
    have h2 : (g - 1) * (g - 1) = 0 := by
      have : (2 : F) = 0 := CharTwo.two_eq_zero
      linear_combination hg - g * this + this
    have := mul_self_eq_zero.mp h2
    linear_combination this
  have g1 : ∀ w, InA j w → G w w = 1 := by
    intro w hw
    rcases hsize with h3 | hB
    · obtain ⟨x, z, hxw, hzw, hxz, hx, hz⟩ := two_others j (by omega) w
      have hg : ∀ x z, InA j x → InA j z → z ≠ x → G z z = G (Fin.rev x) (Fin.rev x) := by
        intro x z hx hz hzx
        have hrz : ¬ InA j (Fin.rev z) := fun h => InA_not_InA' hz h
        have hne : Fin.rev z ≠ Fin.rev x := fun e => hzx (Fin.rev_injective e)
        have := hh x (Fin.rev z) hx hrz hne
        rwa [Fin.rev_rev] at this
      have e1 := hg x w hx hw hxw.symm
      have e2 := hg x z hx hz hxz.symm
      have e3 := hg z w hz hw hzw.symm
      have := gh z hz
      rw [e2, ← e3, ← e1] at this
      exact hsq _ this
    · let y0 : Fin N := ⟨j.val + 1, by omega⟩
      have hy0 : ¬ InA j y0 := by simp only [InA, y0]; omega
      have hy0' : ¬ InA' j y0 := by simp only [InA', y0, Fin.val_rev]; omega
      have hadm : ∀ x, InA j x → y0 ≠ Fin.rev x := fun x hx e => hy0' (by
        simp only [InA', e, Fin.rev_rev]; exact hx)
      have hrev0 : ¬ InA j (Fin.rev y0) := by simp only [InA, y0, Fin.val_rev]; omega
      have hadm' : ∀ x, InA j x → Fin.rev y0 ≠ Fin.rev x := fun x hx e => by
        have := Fin.rev_injective e
        exact hy0 (this ▸ hx)
      have d1 := diagy w y0 hw hy0 (hadm w hw)
      have d2 := diagy w (Fin.rev y0) hw hrev0 (hadm' w hw)
      have d3 := hh w y0 hw hy0 (hadm w hw)
      have := gh w hw
      rw [← d3, d2] at this
      exact hsq _ this
  have h1 : ∀ w, InA j w → G (Fin.rev w) (Fin.rev w) = 1 := by
    intro w hw
    have := gh w hw
    rwa [g1 w hw, one_mul] at this
  refine fun x y hxy => ?_
  by_cases hy : InA j y
  · by_cases hxy' : x = y
    · subst hxy'; rw [if_pos rfl, g1 x hy]
    · rw [if_neg hxy', colx y hy x hxy']
  · have hx : ¬ InA j x := fun hx => hxy (Or.inl ⟨hx, hy⟩)
    by_cases hx' : InA' j x
    · have hxa : InA j (Fin.rev x) := hx'
      obtain ⟨y1, y2, h12, hy1, hy2, hr1, hr2⟩ := exists_two_admissible hN hev j (Fin.rev x)
      have hx1 : G x x = 1 := by
        have := h1 _ hxa
        rwa [Fin.rev_rev] at this
      have hhy := hh (Fin.rev x) y1 hxa hy1 hr1
      rw [Fin.rev_rev, hx1] at hhy
      have := Rrow (Fin.rev x) y1 hxa hy1 hr1 y
      rw [Fin.rev_rev, hhy] at this
      rw [this]
      by_cases hyx : y = x
      · rw [if_pos hyx, if_pos hyx.symm]
      · rw [if_neg hyx, if_neg (Ne.symm hyx)]
    · have hy' : ¬ InA' j y := fun hy' => hxy (Or.inr ⟨hx, hx', hy'⟩)
      let x0 : Fin N := ⟨0, by omega⟩
      have hx0 : InA j x0 := by simp only [InA, x0]; omega
      have hxr : x ≠ Fin.rev x0 := fun e => hx' (by simp only [InA', e, Fin.rev_rev]; exact hx0)
      have hyr : y ≠ Fin.rev x0 := fun e => hy' (by simp only [InA', e, Fin.rev_rev]; exact hx0)
      have := R1 x0 x hx0 hx hxr y
      rw [this, if_neg hyr, sub_zero, g1 x0 hx0]
      by_cases hyx : y = x
      · rw [if_pos hyx, if_pos hyx.symm]
      · rw [if_neg hyx, if_neg (Ne.symm hyx)]

end ShapeD

end D131

section D132b
open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Spin QuadraticMap
  CFSG.LieType.Universal.Unitary
section StagesD

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
  (e : Equiv.Perm (Fin (n + n))) (he : ∀ t, e (Fin.rev t) = Fin.rev (e t))
  (j : Fin ((n + n) / 2)) (R : Subgroup (spinGroup (quadPlus n F)))
  (hroot : ∀ a b : Fin (n + n), InA j a → ¬ InA j b → b ≠ Fin.rev a → ∀ c : F,
    ∃ u ∈ R, matDe e u = rootMatrix (RingEquiv.refl F) a b c)

include he hroot

theorem stageY_D : ∀ g : spinGroup (quadPlus n F), ShS0 j 1 (matDe e g) → g ∈ R := by
  classical
  refine mem_of_peel R (fun g => ShS0 j 1 (matDe e g)) (fun g => cntYU j (matDe e g)) ?_ ?_
  · intro g hg h0
    set G := matDe e g with hG
    have hunit := hunit_refl e he g
    have hz : ∀ x y, InA j x → InA' j y → G x y = 0 := by
      intro x y hx hy
      rcases le_or_gt x.val (Fin.rev y).val with hle | hlt
      · exact card_zero_entries (p := fun q : Fin (n + n) × Fin (n + n) =>
          InA j q.1 ∧ InA' j q.2 ∧ q.1.val ≤ (Fin.rev q.2).val)
          (f := fun q : Fin (n + n) × Fin (n + n) => G q.1 q.2) h0 (x, y) ⟨hx, hy, hle⟩
      · have hd : InA j (Fin.rev y) := hy
        have hrel := relY (σ := RingEquiv.refl F) hg hunit hx hd
        rw [Fin.rev_rev] at hrel
        have h1 : G (Fin.rev y) (Fin.rev x) = 0 :=
          card_zero_entries (p := fun q : Fin (n + n) × Fin (n + n) =>
            InA j q.1 ∧ InA' j q.2 ∧ q.1.val ≤ (Fin.rev q.2).val)
            (f := fun q : Fin (n + n) × Fin (n + n) => G q.1 q.2) h0 (Fin.rev y, Fin.rev x)
            ⟨hd, InA_rev_InA' hx, by rw [Fin.rev_rev]; exact hlt.le⟩
        simp only [RingEquiv.refl_apply, one_mul, h1, mul_zero, add_zero] at hrel
        exact hrel
    have hmat : G = (1 : Matrix (Fin (n + n)) (Fin (n + n)) F) := by
      ext x y
      by_cases hxy : InA j x ∧ InA' j y
      · rw [hz x y hxy.1 hxy.2]
        have : x ≠ y := fun e => InA_not_InA' hxy.1 (by rw [e]; exact hxy.2)
        simp [Matrix.one_apply, this]
      · rw [hg x y hxy]
        by_cases e : x = y <;> simp [Matrix.one_apply, e]
    have : g = 1 := by
      apply matDe_injective e
      rw [map_one]; exact hmat
    rw [this]; exact R.one_mem
  · intro g hg h
    set G := matDe e g with hG
    have hunit := hunit_refl e he g
    obtain ⟨⟨a, b⟩, hab⟩ := Finset.card_pos.mp h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab
    obtain ⟨⟨ha, hb, hle⟩, hne⟩ := hab
    set c0 : F := -G a b with hc0
    have hcc : G a b + 1 * c0 = 0 := by rw [hc0]; ring
    have hbr : b ≠ Fin.rev a := by
      intro hbr
      subst hbr
      exact hne (matDe_diag_zero e he g j hg ha)
    have hbA : ¬ InA j b := InA'_not_InA hb
    obtain ⟨u, huR, hu⟩ := hroot a b ha hbA hbr c0
    have hmu : matDe e (g * u) = G * rootMatrix (RingEquiv.refl F) a b c0 := by
      rw [map_mul, hu]
    obtain ⟨hS', h0', hsame⟩ := stepY_root (σ := RingEquiv.refl F) G hg ha hb hbr c0 hcc
    refine ⟨u, huR, ?_, ?_⟩
    · rw [hmu]; exact hS'
    · rw [hmu]
      unfold cntYU
      apply card_lt_of_kill _ (fun q : Fin (n + n) × Fin (n + n) => G q.1 q.2)
        (fun q : Fin (n + n) × Fin (n + n) =>
          (G * rootMatrix (RingEquiv.refl F) a b c0) q.1 q.2) (a, b)
      · exact ⟨⟨ha, hb, hle⟩, hne⟩
      · exact h0'
      · intro q hq hq'
        refine hsame q.1 q.2 hq' ?_
        intro e
        obtain ⟨⟨hq1, hq2, hq3⟩⟩ := (⟨hq⟩ : Nonempty _)
        have e1 : q.1 = Fin.rev b := congrArg Prod.fst e
        have e2 : q.2 = Fin.rev a := congrArg Prod.snd e
        rw [e1, e2, Fin.rev_rev] at hq3
        have hlt : a.val < (Fin.rev b).val := by
          rcases hle.lt_or_eq with h1 | h1
          · exact h1
          · exact absurd (Fin.ext h1) (fun e' => hbr (by rw [e', Fin.rev_rev]))
        have : (Fin.rev b).val ≤ a.val := hq3
        omega

theorem stageX_D : ∀ g : spinGroup (quadPlus n F), ShS j 1 (matDe e g) → g ∈ R := by
  classical
  refine mem_of_peel R (fun g => ShS j 1 (matDe e g)) (fun g => cntXU j (matDe e g)) ?_ ?_
  · intro g hg h0
    exact stageY_D e he j R hroot g (sh0_of_xZero (σ₀ := RingEquiv.refl F) one_ne_zero hg
      (hunit_refl e he g) (fun x y hx hy hy' =>
      card_zero_entries (p := fun q : Fin (n + n) × Fin (n + n) =>
        InA j q.1 ∧ ¬ InA j q.2 ∧ ¬ InA' j q.2)
        (f := fun q : Fin (n + n) × Fin (n + n) => matDe e g q.1 q.2) h0 (x, y) ⟨hx, hy, hy'⟩))
  · intro g hg h
    set G := matDe e g with hG
    obtain ⟨⟨x, y⟩, hxy⟩ := Finset.card_pos.mp h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxy
    obtain ⟨⟨hx, hy, hy'⟩, hne⟩ := hxy
    have hxy : x ≠ y := fun e => hy (by rw [← e]; exact hx)
    have hyrx : y ≠ Fin.rev x := fun e => hy' (by rw [e]; exact InA_rev_InA' hx)
    set c : F := -G x y / 1 with hc
    obtain ⟨u, huR, hu⟩ := hroot x y hx hy hyrx c
    have hmu : matDe e (g * u) = G * rootMatrix (RingEquiv.refl F) x y c := by
      rw [map_mul, hu]
    obtain ⟨hS', h0', hsame⟩ := stepX_root (σ := RingEquiv.refl F) G one_ne_zero hg hx hy hy' c hc
    refine ⟨u, huR, ?_, ?_⟩
    · rw [hmu]; exact hS'
    · rw [hmu]
      unfold cntXU
      apply card_lt_of_kill _ (fun q : Fin (n + n) × Fin (n + n) => G q.1 q.2)
        (fun q : Fin (n + n) × Fin (n + n) => (G * rootMatrix (RingEquiv.refl F) x y c) q.1 q.2) (x, y)
      · exact ⟨⟨hx, hy, hy'⟩, hne⟩
      · exact h0'
      · intro q hq hq'
        exact hsame q.1 q.2 hq.1 hq.2.1 hq.2.2 hq'

end StagesD


section CentD

open CFSG.AGLEmbedding.LieOut CFSG.AGLEmbeddingD2.ParabLevi CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg.SpinPlus

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem centOb_spinPlus (hn : 3 ≤ n) {I : Set (Fin (plusDatum n F hn).rank)} (hI : I ≠ Set.univ) :
    CentOb (plusDatum n F hn) I := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : Fin (plusDatum n F hn).rank, j ∉ I := by
    by_contra h
    push Not at h
    exact hI (Set.eq_univ_of_forall h)
  let k0 : Fin n := j
  intro k hk
  have hkr : ∀ u ∈ radical (plusDatum n F hn) j, k * u = u * k :=
    fun u hu => hk u (radical_le_leviRad hj hu)
  set e := fE hn k0 with he_def
  have he : ∀ t, e (Fin.rev t) = Fin.rev (e t) := fE_rev hn k0
  set jj := jD n k0 with hjj
  have hroot : ∀ a b : Fin (n + n), InA jj a → ¬ InA jj b → b ≠ Fin.rev a → ∀ c : F,
      ∃ u ∈ radical (plusDatum n F hn) j, matDe e u = rootMatrix (RingEquiv.refl F) a b c := by
    intro a b ha hb hba c
    have hab : a ≠ b := fun h => hb (h ▸ ha)
    obtain ⟨u, hr, hu, hm⟩ := exists_rootElt_e hn e he hab hba c
    refine ⟨u, ?_, hm⟩
    have h1 : 0 < mvec ((posEquiv n).symm (e a)) k0 := (mvec_pos_iff hn k0 a).mpr ha
    have h2 : ¬ 0 < mvec ((posEquiv n).symm (e b)) k0 := fun h => hb ((mvec_pos_iff hn k0 b).mp h)
    have h3 := two_mul_Dgamma ((posEquiv n).symm (e a)) ((posEquiv n).symm (e b)) k0
    have hpos : 0 < Dgamma ((posEquiv n).symm (e a)) ((posEquiv n).symm (e b)) k0 := by omega
    exact rootGroup_le_radical (D := plusDatum n F hn) hr hpos hu
  have hmat : ∀ u ∈ radical (plusDatum n F hn) j, matDe e k * matDe e u = matDe e u * matDe e k :=
    fun u hu => by rw [← map_mul, ← map_mul, hkr u hu]
  have hjn := jj.isLt
  have hsh : ShS jj 1 (matDe e k) := by
    refine shape_of_comm_D (matDe e k) jj (by omega) ⟨n, rfl⟩ ?_ (hunit_refl e he k) ?_
    · have := k0.isLt
      simp only [hjj, jD_val]
      split_ifs <;> omega
    · intro x y hx hy hyx
      obtain ⟨u, huR, hu⟩ := hroot x y hx hy hyx 1
      rw [← hu]
      exact hmat u huR
  exact Subgroup.mem_sup_left (radical_le_leviRad hj (stageX_D e he jj _ hroot k hsh))

end CentD


end D132b


theorem orthPlusCentOb : OrthPlusCentOb :=
  fun _ _ _ _ _ _ _ hn _ _ hI => centOb_spinPlus hn hI

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
