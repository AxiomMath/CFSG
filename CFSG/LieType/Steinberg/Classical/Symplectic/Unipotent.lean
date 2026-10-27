module

public import CFSG.LieType.Universal.SymplecticExtras.Unipotent

public noncomputable section

namespace CFSG.LieType.Steinberg.Sp

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.RootSystem TauCeti.GLSymplecticFin
  CFSG.Assembly.LowTwoRank

variable {n : ℕ} {F : Type} [Field F]

theorem idBelow_mat_elt_of (μ : (Fin n → ℤ) →+ ℤ) {h : ℤ} {r : RootSubgroupIndex n}
    (hr : h ≤ μ (stdVec r)) (c : F) : IdBelow (fun a => -μ (wt a)) h (mat n F (elt r c)) := by
  intro a b hab
  have hE : E F r a b = 0 := by
    by_contra hE
    have h1 := hasDeg_E r a b hE
    have h2 : -μ (wt b) - -μ (wt a) = μ (stdVec r) := by
      rw [← h1, map_sub]
      ring
    simp only at hab
    linarith
  rw [mat_elt, Matrix.add_apply, Matrix.smul_apply, hE, smul_zero, add_zero]

theorem eq_of_list_prod_eq_of (μ : (Fin n → ℤ) →+ ℤ) {κ : Type*} (L : List κ) (hL : L.Nodup)
    (r : κ → RootSubgroupIndex n)
    (hinj : ∀ x ∈ L, ∀ y ∈ L, stdVec (r x) = stdVec (r y) → x = y)
    (hlev : ∀ x ∈ L, 1 ≤ μ (stdVec (r x)))
    (hsort : L.Pairwise fun x y => μ (stdVec (r x)) ≤ μ (stdVec (r y)))
    (c d : κ → F)
    (h : (L.map fun x => elt (r x) (c x)).prod = (L.map fun x => elt (r x) (d x)).prod) :
    ∀ x ∈ L, c x = d x := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.nodup_cons] at hL
    rw [List.pairwise_cons] at hsort
    have hx1 := hlev x List.mem_cons_self
    have hpq := pos1_ne (r x)
    have hlevpq : -μ (wt (pos1 (r x)).2) - -μ (wt (pos1 (r x)).1) = μ (stdVec (r x)) := by
      rw [← wt_pos1, map_sub]
      ring
    have htail : ∀ e : κ → F,
        IdBelow (fun a => -μ (wt a)) (μ (stdVec (r x)))
          (mat n F (L.map fun y => elt (r y) (e y)).prod) ∧
        mat n F (L.map fun y => elt (r y) (e y)).prod (pos1 (r x)).1 (pos1 (r x)).2 = 0 := by
      intro e
      rw [map_list_prod, List.map_map]
      obtain ⟨h1, h2⟩ := idBelow_list_prod (fun a => -μ (wt a)) (by omega) L
        (fun y => mat n F (elt (r y) (e y)))
        (fun y hy => idBelow_mat_elt_of μ (hsort.1 y hy) (e y))
      refine ⟨h1, ?_⟩
      rw [Function.comp_def, h2 _ _ hpq hlevpq.le]
      refine List.sum_eq_zero fun z hz => ?_
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      have hE : E F (r y) (pos1 (r x)).1 (pos1 (r x)).2 = 0 := by
        by_contra hE
        have hw := hasDeg_E (r y) _ _ hE
        rw [wt_pos1] at hw
        have hyx := hinj y (List.mem_cons_of_mem x hy) x List.mem_cons_self hw.symm
        exact hL.1 (hyx ▸ hy)
      rw [mat_elt, Matrix.add_apply, Matrix.one_apply_ne hpq, Matrix.smul_apply, hE, smul_zero,
        zero_add]
    have hentry : ∀ e : κ → F, mat n F (elt (r x) (e x) * (L.map fun y => elt (r y) (e y)).prod)
        (pos1 (r x)).1 (pos1 (r x)).2 = e x := by
      intro e
      obtain ⟨h1, h2⟩ := htail e
      rw [map_mul, mul_apply_of_idBelow (fun a => -μ (wt a)) (by omega)
        (idBelow_mat_elt_of μ le_rfl (e x)) h1 hpq hlevpq.le, h2, add_zero, mat_elt_apply_pos1]
    simp only [List.map_cons, List.prod_cons] at h
    have hcx : c x = d x := by rw [← hentry c, ← hentry d, h]
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hcx
    · refine ih hL.2 (fun a ha b hb => hinj a (List.mem_cons_of_mem x ha) b
        (List.mem_cons_of_mem x hb)) (fun a ha => hlev a (List.mem_cons_of_mem x ha)) hsort.2 ?_
        y hy
      rw [hcx] at h
      exact mul_left_cancel h

@[expose] def levelCoeff (f : (Fin n → ℤ) →+ ℤ) (a : Fin n) : ℤ :=
  ∑ j : Fin n, if a ≤ j then (if j.val + 1 = n then 1 else 2) * f (Pi.single j 1) else 0

@[expose] def levelFun (f : (Fin n → ℤ) →+ ℤ) : (Fin n → ℤ) →+ ℤ where
  toFun e := ∑ a, levelCoeff f a * e a
  map_zero' := by simp
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]

theorem levelFun_apply (f : (Fin n → ℤ) →+ ℤ) (e : Fin n → ℤ) :
    levelFun f e = ∑ a, levelCoeff f a * e a := rfl

theorem levelFun_single (f : (Fin n → ℤ) →+ ℤ) (k : Fin n) :
    levelFun f (Pi.single k 1) = levelCoeff f k := by
  rw [levelFun_apply, Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (by simp)]
  simp

theorem levelFun_toStd (f : (Fin n → ℤ) →+ ℤ) (v : Fin n → ℤ) :
    levelFun f (toStd n v) = 2 * f v := by
  let g : (Fin n → ℤ) →+ ℤ :=
    { toFun := fun v => levelFun f (toStd n v)
      map_zero' := by rw [toStd_zero', map_zero]
      map_add' := fun v w => by rw [toStd_add', map_add] }
  have hg : g = 2 • f := by
    refine AddMonoidHom.functions_ext _ g (2 • f) fun k x => ?_
    have hs : (Pi.single k x : Fin n → ℤ) = x • Pi.single k 1 := by
      ext j
      by_cases hj : j = k
      · subst hj
        simp
      · simp [hj]
    rw [hs, map_zsmul, map_zsmul]
    congr 1
    change levelFun f (toStd n (Pi.single k 1)) = 2 • f (Pi.single k 1)
    rw [nsmul_eq_mul, Nat.cast_ofNat]
    by_cases h : k.val + 1 < n
    · rw [toStd_single_of_lt' h, map_sub, levelFun_single, levelFun_single, levelCoeff,
        levelCoeff, ← Finset.sum_sub_distrib, Finset.sum_eq_single k]
      · have hk : ¬(⟨k.val + 1, h⟩ : Fin n) ≤ k := by
          rw [Fin.le_iff_val_le_val]
          simp
        simp only [le_refl, ite_true, hk, ite_false, sub_zero]
        rw [ite_eq_right (by omega), mul_comm]
      · intro j _ hjk
        have hle : k ≤ j ↔ (⟨k.val + 1, h⟩ : Fin n) ≤ j := by
          simp only [Fin.le_iff_val_le_val]
          have := Fin.val_ne_of_ne hjk
          omega
        by_cases hkj : k ≤ j
        · rw [ite_eq_left hkj, ite_eq_left (hle.1 hkj), sub_self]
        · rw [ite_eq_right hkj, ite_eq_right (fun h' => hkj (hle.2 h')), sub_self]
      · simp
    · rw [toStd_single_of_not_lt' h, map_nsmul, levelFun_single, levelCoeff,
        Finset.sum_eq_single k]
      · rw [ite_eq_left le_rfl, ite_eq_left (by omega), one_mul, nsmul_eq_mul]
        push_cast
        ring
      · intro j _ hjk
        refine ite_eq_right fun hkj => absurd (le_antisymm ?_ hkj) hjk
        rw [Fin.le_iff_val_le_val]
        have := j.2
        omega
      · simp
  have := DFunLike.congr_fun hg v
  rw [AddMonoidHom.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at this
  exact this

theorem prodInjective (f : (Fin n → ℤ) →+ ℤ) (L : List (Fin n → ℤ)) (hL : L.Nodup)
    (hpos : ∀ γ ∈ L, γ ∈ roots (isFiniteType_cartanC n) ∅ ∧ 0 < f γ)
    (hsort : L.Pairwise fun γ δ => f γ ≤ f δ) : ProdInjectiveFor (rootGroup n F) L := by
  intro g g' hg hg' hgg
  have hr : ∀ γ : {γ // γ ∈ L}, ∃ r : RootSubgroupIndex n, stdVec r = toStd n γ.1 :=
    fun γ => exists_stdVec_of_mem_roots (hpos γ.1 γ.2).1
  choose r hr using hr
  have hcoef : ∀ e : (Fin n → ℤ) → StatedSp n F, (∀ γ ∈ L, e γ ∈ rootGroup n F γ) →
      ∃ c : {γ // γ ∈ L} → F, ∀ γ, e γ.1 = elt (r γ) (c γ) := by
    intro e he
    have : ∀ γ : {γ // γ ∈ L}, ∃ c : F, e γ.1 = elt (r γ) c :=
      fun γ => (mem_rootGroup_iff (hr γ)).1 (he γ.1 γ.2)
    choose c hc using this
    exact ⟨c, hc⟩
  obtain ⟨c, hc⟩ := hcoef g hg
  obtain ⟨d, hd⟩ := hcoef g' hg'
  have hprod : ∀ (e : (Fin n → ℤ) → StatedSp n F) (c' : {γ // γ ∈ L} → F),
      (∀ γ, e γ.1 = elt (r γ) (c' γ)) →
      (L.map e).prod = (L.attach.map fun γ => elt (r γ) (c' γ)).prod := by
    intro e c' he
    calc (L.map e).prod = ((L.attach.map Subtype.val).map e).prod := by
          rw [List.attach_map_subtype_val]
      _ = (L.attach.map fun γ => elt (r γ) (c' γ)).prod := by
          rw [List.map_map]
          exact congrArg List.prod (List.map_congr_left fun γ _ => he γ)
  have hlvl : ∀ γ : {γ // γ ∈ L}, levelFun f (stdVec (r γ)) = 2 * f γ.1 :=
    fun γ => by rw [hr γ, levelFun_toStd]
  have hsort' : L.attach.Pairwise fun γ δ => f γ.1 ≤ f δ.1 := by
    have := hsort
    rw [← List.attach_map_subtype_val L, List.pairwise_map] at this
    exact this
  have hcd := eq_of_list_prod_eq_of (levelFun f) L.attach (List.nodup_attach.mpr hL) r
    (fun γ _ δ _ h => Subtype.ext (toStd_inj ((hr γ).symm.trans (h.trans (hr δ)))))
    (fun γ _ => by
      rw [hlvl]
      have := (hpos γ.1 γ.2).2
      omega)
    (hsort'.imp fun {γ δ} h => by
      rw [hlvl, hlvl]
      omega)
    c d ((hprod g c hc).symm.trans (hgg.trans (hprod g' d hd)))
  intro γ hγ
  rw [hc ⟨γ, hγ⟩, hd ⟨γ, hγ⟩, hcd ⟨γ, hγ⟩ (List.mem_attach _ _)]

end CFSG.LieType.Steinberg.Sp
