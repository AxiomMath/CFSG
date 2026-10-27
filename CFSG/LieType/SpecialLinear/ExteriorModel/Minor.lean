module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Matrix.Permutation

public section

open Module

namespace CFSG.LieType.SpecialLinear.ExteriorModel

open Matrix

variable {R : Type*} [CommRing R] {m : ℕ}

@[expose] noncomputable def minor (g : Matrix (Fin m) (Fin m) R) {n : ℕ}
    (s t : Set.powersetCard (Fin m) n) : R :=
  (g.submatrix (Set.powersetCard.ofFinEmbEquiv.symm s)
    (Set.powersetCard.ofFinEmbEquiv.symm t)).det

theorem repr_exteriorPower_map_eq_minor (g : Matrix (Fin m) (Fin m) R) {n : ℕ}
    (s t : Set.powersetCard (Fin m) n) :
    ((Pi.basisFun R (Fin m)).exteriorPower n).repr
        (exteriorPower.map n (Matrix.toLin' g)
          (((Pi.basisFun R (Fin m)).exteriorPower n) t)) s = minor g s t := by
  let b : Basis (Fin m) R (Fin m → R) := Pi.basisFun R (Fin m)
  let B : Basis (Set.powersetCard (Fin m) n) R (⋀[R]^n (Fin m → R)) := b.exteriorPower n
  have hB : ∀ x, B.repr x s = exteriorPower.ιMultiDual R n b s x :=
    fun x => exteriorPower.basis_repr_apply R n b x s
  calc B.repr (exteriorPower.map n (Matrix.toLin' g) (B t)) s
      = exteriorPower.ιMultiDual R n b s
          (exteriorPower.map n (Matrix.toLin' g) (B t)) :=
        hB _
    _ = exteriorPower.ιMultiDual R n b s
          (exteriorPower.map n (Matrix.toLin' g) (exteriorPower.ιMulti_family R n b t)) := by
        rw [exteriorPower.basis_apply]
    _ = exteriorPower.ιMultiDual R n b s (exteriorPower.ιMulti_family R n (Matrix.toLin' g ∘ b) t) := by
        rw [exteriorPower.map_apply_ιMulti_family]
    _ = (Matrix.of fun i j => b.coord (Set.powersetCard.ofFinEmbEquiv.symm s j)
          ((Matrix.toLin' g ∘ b) (Set.powersetCard.ofFinEmbEquiv.symm t i))).det := by
        rw [show exteriorPower.ιMulti_family R n (Matrix.toLin' g ∘ b) t =
            exteriorPower.ιMulti R n ((Matrix.toLin' g ∘ b) ∘
              Set.powersetCard.ofFinEmbEquiv.symm t) from rfl,
          exteriorPower.ιMultiDual_apply_ιMulti]
        simp only [Function.comp_apply]
    _ = minor g s t := by
        rw [minor, ← Matrix.det_transpose]
        congr 1
        ext i j
        simp [b, Matrix.toLin'_apply]

theorem minor_mul (g h : Matrix (Fin m) (Fin m) R) {n : ℕ} (s t : Set.powersetCard (Fin m) n) :
    minor (g * h) s t = ∑ u : Set.powersetCard (Fin m) n, minor g s u * minor h u t := by
  let b : Basis (Fin m) R (Fin m → R) := Pi.basisFun R (Fin m)
  let B : Basis (Set.powersetCard (Fin m) n) R (⋀[R]^n (Fin m → R)) := b.exteriorPower n
  rw [← repr_exteriorPower_map_eq_minor (g * h) s t, Matrix.toLin'_mul,
    exteriorPower.map_comp, LinearMap.comp_apply]
  have hdecomp : exteriorPower.map n (Matrix.toLin' h) (B t) =
      ∑ u, B.repr (exteriorPower.map n (Matrix.toLin' h) (B t)) u • B u :=
    (B.sum_repr _).symm
  rw [hdecomp]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [repr_exteriorPower_map_eq_minor g s u, repr_exteriorPower_map_eq_minor h u t, mul_comm]

theorem minor_one {n : ℕ} (s t : Set.powersetCard (Fin m) n) :
    minor (1 : Matrix (Fin m) (Fin m) R) s t = if s = t then 1 else 0 := by
  rw [← repr_exteriorPower_map_eq_minor (1 : Matrix (Fin m) (Fin m) R) s t,
    Matrix.toLin'_one, exteriorPower.map_id, LinearMap.id_apply]
  let b : Basis (Fin m) R (Fin m → R) := Pi.basisFun R (Fin m)
  let B : Basis (Set.powersetCard (Fin m) n) R (⋀[R]^n (Fin m → R)) := b.exteriorPower n
  rw [exteriorPower.basis_apply, exteriorPower.basis_repr]
  simp [Finsupp.single_apply, eq_comm]

theorem minor_transpose (g : Matrix (Fin m) (Fin m) R) {n : ℕ}
    (s t : Set.powersetCard (Fin m) n) : minor gᵀ s t = minor g t s := by
  rw [minor, minor,
    show gᵀ.submatrix (Set.powersetCard.ofFinEmbEquiv.symm s)
        (Set.powersetCard.ofFinEmbEquiv.symm t) =
        (g.submatrix (Set.powersetCard.ofFinEmbEquiv.symm t)
          (Set.powersetCard.ofFinEmbEquiv.symm s))ᵀ by
      ext i j
      simp [Matrix.transpose_apply],
    Matrix.det_transpose]

theorem minor_map {S : Type*} [CommRing S] (φ : R →+* S) (g : Matrix (Fin m) (Fin m) R) {n : ℕ}
    (s t : Set.powersetCard (Fin m) n) : minor (g.map φ) s t = φ (minor g s t) := by
  rw [minor, minor, Matrix.submatrix_map, RingHom.map_det]
  rfl

theorem prod_orderEmbOfFin {α : Type*} [LinearOrder α] {n : ℕ}
    (s : Finset α) (h : s.card = n) (f : α → R) :
    ∏ i : Fin n, f (s.orderEmbOfFin h i) = ∏ a ∈ s, f a := by
  refine Finset.prod_bij (fun i _ => s.orderEmbOfFin h i) (fun i _ => ?_)
    (fun i _ j _ hij => ?_) (fun a ha => ?_) (fun i _ => rfl)
  · exact Finset.orderEmbOfFin_mem s h i
  · exact (s.orderEmbOfFin h).injective hij
  · have hrange : a ∈ Set.range (s.orderEmbOfFin h) := by simpa using ha
    obtain ⟨i, hi⟩ := Set.mem_range.mp hrange
    exact ⟨i, Finset.mem_univ _, hi⟩

theorem minor_diagonal (d : Fin m → R) {n : ℕ} (s t : Set.powersetCard (Fin m) n) :
    minor (Matrix.diagonal d) s t = if s = t then ∏ a ∈ (s : Finset (Fin m)), d a else 0 := by
  by_cases hst : s = t
  · subst hst
    rw [if_pos rfl, minor,
      Matrix.submatrix_diagonal _ _ (Set.powersetCard.ofFinEmbEquiv.symm s).injective,
      Matrix.det_diagonal]
    simpa only [Set.powersetCard.ofFinEmbEquiv_symm_apply, Function.comp_apply] using
      prod_orderEmbOfFin s.val s.prop d
  · rw [if_neg hst, minor]
    obtain ⟨a, has, hat⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne s t).mp hst
    have has' : a ∈ (s : Finset (Fin m)) := has
    obtain ⟨i, hi⟩ := Set.mem_range.mp
      ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s a).mpr
        (Set.powersetCard.mem_coe_iff.mp has'))
    refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
    have het : (Set.powersetCard.ofFinEmbEquiv.symm t) j ∈ (t : Finset (Fin m)) := by
      simpa [Set.powersetCard.ofFinEmbEquiv_symm_apply] using
        Finset.orderEmbOfFin_mem t.val t.prop j
    have hne : (Set.powersetCard.ofFinEmbEquiv.symm s) i ≠
        (Set.powersetCard.ofFinEmbEquiv.symm t) j := by
      rw [hi]
      exact fun h => hat (h ▸ het)
    simp [Matrix.submatrix_apply, hne]

theorem exists_ofFinEmbEquiv_symm_eq_of_mem {n : ℕ} (s : Set.powersetCard (Fin m) n)
    {a : Fin m} (ha : a ∈ (s : Finset (Fin m))) :
    ∃ i : Fin n, Set.powersetCard.ofFinEmbEquiv.symm s i = a :=
  Set.mem_range.mp ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s a).mpr
    (Set.powersetCard.mem_coe_iff.mp ha))

theorem det_of_row_eq_ite_single_of_injective {n : ℕ} (f : Fin n → Fin n)
    (hf : Function.Injective f) :
    (Matrix.of fun i j => if j = f i then (1 : R) else 0).det =
      (Equiv.Perm.sign (Equiv.ofBijective f hf.bijective_of_finite) : R) := by
  rw [show (Matrix.of fun i j => if j = f i then (1 : R) else 0) =
      Equiv.Perm.permMatrix R (Equiv.ofBijective f hf.bijective_of_finite) by
    ext i j
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, eq_comm]]
  exact Matrix.det_permutation _

theorem det_of_row_eq_ite_single_of_not_injective {n : ℕ} (f : Fin n → Fin n)
    (hf : ¬ Function.Injective f) :
    (Matrix.of fun i j => if j = f i then (1 : R) else 0).det = 0 := by
  obtain ⟨i, i', heq, hne⟩ := Function.not_injective_iff.mp hf
  exact Matrix.det_zero_of_row_eq hne (funext fun j => by simp [heq])

theorem det_one_add_smul_single {n : ℕ} {i j : Fin n} (hij : i ≠ j) (x : R) :
    (1 + x • Matrix.single i j (1 : R) : Matrix (Fin n) (Fin n) R).det = 1 := by
  have hmat : (1 + x • Matrix.single i j (1 : R) : Matrix (Fin n) (Fin n) R) =
      Matrix.updateRow (1 : Matrix (Fin n) (Fin n) R) i
        (Pi.single i 1 + x • Pi.single j 1) := by
    ext a b
    by_cases ha : a = i
    · subst ha
      simp [Matrix.updateRow_self, Matrix.one_apply, Matrix.single_apply, Pi.single_apply,
        Matrix.add_apply, smul_eq_mul, eq_comm]
    · simp [Matrix.one_apply, Matrix.add_apply, smul_eq_mul, ha, Ne.symm ha]
  rw [hmat, Matrix.det_updateRow_add, Matrix.det_updateRow_smul]
  have h1 : (Matrix.updateRow (1 : Matrix (Fin n) (Fin n) R) i (Pi.single i 1)).det = 1 := by
    rw [show Matrix.updateRow (1 : Matrix (Fin n) (Fin n) R) i (Pi.single i 1) = 1 by
      ext a b
      by_cases ha : a = i <;>
        simp [Matrix.updateRow_apply, Matrix.one_apply, Pi.single_apply, ha, eq_comm],
      Matrix.det_one]
  have h2 : (Matrix.updateRow (1 : Matrix (Fin n) (Fin n) R) i (Pi.single j 1)).det = 0 := by
    refine Matrix.det_zero_of_row_eq hij ?_
    funext b
    simp [Matrix.updateRow_apply, Matrix.one_apply, Pi.single_apply, hij.symm, eq_comm]
  rw [h1, h2, mul_zero, add_zero]

theorem submatrix_one_add_single {m n : ℕ} (e f : Fin n → Fin m) (r c : Fin m) (x : R) :
    (1 + Matrix.single r c x : Matrix (Fin m) (Fin m) R).submatrix e f =
      (1 : Matrix (Fin m) (Fin m) R).submatrix e f +
        x • (Matrix.single r c (1 : R)).submatrix e f := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
    Matrix.single_apply, smul_eq_mul]
  by_cases hab : (e a = r ∧ f b = c) <;> simp [hab]

theorem submatrix_single_of_injective {m n : ℕ} {e f : Fin n → Fin m}
    (he : Function.Injective e) (hf : Function.Injective f) {r c : Fin m} {i j : Fin n}
    (hi : e i = r) (hj : f j = c) :
    (Matrix.single r c (1 : R)).submatrix e f = Matrix.single i j 1 := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.single_apply]
  have h1 : r = e a ↔ i = a := by rw [← hi, he.eq_iff]
  have h2 : c = f b ↔ j = b := by rw [← hj, hf.eq_iff]
  simp only [h1, h2]

theorem det_add_smul_single {n : ℕ} (I : Matrix (Fin n) (Fin n) R) (i j : Fin n) (x : R) :
    (I + x • Matrix.single i j (1 : R)).det =
      I.det + x * (Matrix.updateRow I i (Pi.single j 1)).det := by
  have hmat : (I + x • Matrix.single i j (1 : R) : Matrix (Fin n) (Fin n) R) =
      Matrix.updateRow I i (I i + x • Pi.single j 1) := by
    ext a b
    by_cases ha : a = i
    · subst ha
      simp [Matrix.updateRow_self, Matrix.single_apply, Pi.single_apply,
        Matrix.add_apply, smul_eq_mul, eq_comm]
    · simp [Matrix.add_apply, smul_eq_mul, ha, Ne.symm ha]
  rw [hmat, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]

theorem minor_one_add_single (h2 : (2 : R) = 0) {r c : Fin m} (hrc : r ≠ c) (x : R) {n : ℕ}
    (s t : Set.powersetCard (Fin m) n) :
    minor (1 + Matrix.single r c x) s t =
      if s = t then 1
      else if c ∈ (t : Finset (Fin m)) ∧ r ∉ (t : Finset (Fin m)) ∧
          (s : Finset (Fin m)) = insert r ((t : Finset (Fin m)).erase c) then x else 0 := by
  classical
  have hneg : (-1 : R) = 1 := by
    have h : (1 : R) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2
    exact neg_eq_of_add_eq_zero_left h
  have hsign : ∀ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : R) = 1 := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h]; simp
    · rw [h]; simpa using hneg
  by_cases hst : s = t
  ·
    subst hst
    rw [if_pos rfl, minor]
    set es : Fin n → Fin m := (Set.powersetCard.ofFinEmbEquiv.symm s : Fin n → Fin m) with hes
    have hes_inj : Function.Injective es := by
      rw [hes]
      exact (Set.powersetCard.ofFinEmbEquiv.symm s).injective
    have hes_mem : ∀ a, es a ∈ (s : Finset (Fin m)) := by
      intro a
      rw [hes]
      simpa [Set.powersetCard.ofFinEmbEquiv_symm_apply] using
        Finset.orderEmbOfFin_mem s.val s.prop a
    rw [submatrix_one_add_single]
    rw [Matrix.submatrix_one es hes_inj]
    by_cases hr : r ∈ (s : Finset (Fin m))
    · by_cases hc : c ∈ (s : Finset (Fin m))
      · obtain ⟨i, hi⟩ := exists_ofFinEmbEquiv_symm_eq_of_mem s hr
        obtain ⟨j, hj⟩ := exists_ofFinEmbEquiv_symm_eq_of_mem s hc
        rw [submatrix_single_of_injective hes_inj hes_inj hi hj]
        have hij : i ≠ j := by
          intro h
          exact hrc (by rw [← hi, ← hj, h])
        exact det_one_add_smul_single hij x
      · have hB : (Matrix.single r c (1 : R)).submatrix es es = 0 := by
          ext a b
          simp only [Matrix.submatrix_apply, Matrix.single_apply]
          have hne : ¬ (r = es a ∧ c = es b) := by
            rintro ⟨-, hc'⟩
            exact hc (by rw [hc']; exact hes_mem b)
          simp [hne]
        rw [hB, smul_zero, add_zero, Matrix.det_one]
    · have hB : (Matrix.single r c (1 : R)).submatrix es es = 0 := by
        ext a b
        simp only [Matrix.submatrix_apply, Matrix.single_apply]
        have hne : ¬ (r = es a ∧ c = es b) := by
          rintro ⟨hr', -⟩
          exact hr (by rw [hr']; exact hes_mem a)
        simp [hne]
      rw [hB, smul_zero, add_zero, Matrix.det_one]
  ·
    rw [if_neg hst, minor]
    set es : Fin n → Fin m := (Set.powersetCard.ofFinEmbEquiv.symm s : Fin n → Fin m) with hes
    set et : Fin n → Fin m := (Set.powersetCard.ofFinEmbEquiv.symm t : Fin n → Fin m) with het
    have hes_inj : Function.Injective es := by
      rw [hes]
      exact (Set.powersetCard.ofFinEmbEquiv.symm s).injective
    have het_inj : Function.Injective et := by
      rw [het]
      exact (Set.powersetCard.ofFinEmbEquiv.symm t).injective
    have hes_mem : ∀ a, es a ∈ (s : Finset (Fin m)) := by
      intro a
      rw [hes]
      simpa [Set.powersetCard.ofFinEmbEquiv_symm_apply] using
        Finset.orderEmbOfFin_mem s.val s.prop a
    have het_mem : ∀ a, et a ∈ (t : Finset (Fin m)) := by
      intro a
      rw [het]
      simpa [Set.powersetCard.ofFinEmbEquiv_symm_apply] using
        Finset.orderEmbOfFin_mem t.val t.prop a
    rw [submatrix_one_add_single]
    have hI : ((1 : Matrix (Fin m) (Fin m) R).submatrix es et).det = 0 := by
      have h := minor_one (n := n) (m := m) (R := R) s t
      rw [if_neg hst] at h
      simpa [minor, hes, het] using h
    by_cases hr : r ∈ (s : Finset (Fin m))
    · by_cases hc : c ∈ (t : Finset (Fin m))
      · obtain ⟨i_r, hi_r₀⟩ := exists_ofFinEmbEquiv_symm_eq_of_mem s hr
        obtain ⟨i_c, hi_c₀⟩ := exists_ofFinEmbEquiv_symm_eq_of_mem t hc
        have hi_r : es i_r = r := by rw [hes]; exact hi_r₀
        have hi_c : et i_c = c := by rw [het]; exact hi_c₀
        rw [submatrix_single_of_injective hes_inj het_inj hi_r hi_c]
        rw [det_add_smul_single, hI, zero_add]
        set Rmat : Matrix (Fin n) (Fin n) R :=
          Matrix.updateRow ((1 : Matrix (Fin m) (Fin m) R).submatrix es et) i_r
            (Pi.single i_c 1) with hRdef
        by_cases h1 : ∀ k, k ≠ i_r → es k ∈ (t : Finset (Fin m))
        · let p : Fin n → Fin n := fun a =>
            if ha : es a ∈ (t : Finset (Fin m)) then
              (t.val.orderIsoOfFin t.prop).symm ⟨es a, ha⟩ else i_c
          let f : Fin n → Fin n := fun a => if a = i_r then i_c else p a
          have hp : ∀ a (ha : es a ∈ (t : Finset (Fin m))), et (p a) = es a := by
            intro a ha
            have hx : (t.val.orderIsoOfFin t.prop) (p a) = ⟨es a, ha⟩ := by
              simp [p, ha]
            change (((t.val.orderIsoOfFin t.prop) (p a)) : Fin m) = es a
            exact congrArg Subtype.val hx
          have hf_i : f i_r = i_c := by simp [f]
          have hf_ne : ∀ k, k ≠ i_r → f k = p k := by
            intro k hk
            simp [f, hk]
          have hR : Rmat = Matrix.of (fun a b => if b = f a then (1 : R) else 0) := by
            rw [hRdef]
            ext a b
            by_cases ha : a = i_r
            · subst ha
              simp [f, Matrix.updateRow_self, Pi.single_apply, eq_comm]
            · have hmem : es a ∈ (t : Finset (Fin m)) := h1 a ha
              by_cases hb : b = p a
              · have hthis : es a = et b := by rw [hb, hp a hmem]
                simp [f, ha, Matrix.submatrix_apply, Matrix.one_apply, hthis, hb]
              · have hne : es a ≠ et b := by
                  intro h
                  exact hb (het_inj (by rw [hp a hmem]; exact h)).symm
                simp [f, ha, Matrix.submatrix_apply, hne, hb]
          by_cases hc' : c ∈ (s : Finset (Fin m))
          · obtain ⟨k, hk_eq₀⟩ := exists_ofFinEmbEquiv_symm_eq_of_mem s hc'
            have hk_eq : es k = c := by rw [hes]; exact hk_eq₀
            have hk_ne : k ≠ i_r := by
              intro h
              exact hrc (by rw [← hi_r, ← h, hk_eq])
            have hpk : p k = i_c := by
              apply het_inj
              rw [hp k (h1 k hk_ne), hk_eq, hi_c]
            have hf : ¬ Function.Injective f := by
              intro hinj
              have hfk : f k = i_c := by simp [f, hk_ne, hpk]
              have hfi : f i_r = i_c := by simp [f]
              exact hk_ne (hinj (by rw [hfk, hfi]))
            have hRdet : Rmat.det = 0 := by
              rw [hR, det_of_row_eq_ite_single_of_not_injective f hf]
            have hcond : ¬ (c ∈ (t : Finset (Fin m)) ∧ r ∉ (t : Finset (Fin m)) ∧
                (s : Finset (Fin m)) = insert r ((t : Finset (Fin m)).erase c)) := by
              rintro ⟨-, -, hs⟩
              have hcs : c ∉ (s : Finset (Fin m)) := by
                rw [hs]
                simp [hrc.symm]
              exact hcs hc'
            rw [hRdet, mul_zero, if_neg hcond]
          · have hf : Function.Injective f := by
              intro a b hab
              by_cases ha : a = i_r
              · rw [ha] at hab ⊢
                by_cases hb : b = i_r
                · exact hb.symm
                · exfalso
                  rw [hf_i, hf_ne b hb] at hab
                  have hc_eq : c = es b := by
                    calc c = et i_c := hi_c.symm
                      _ = et (p b) := by rw [hab]
                      _ = es b := hp b (h1 b hb)
                  exact hc' (by rw [hc_eq]; exact hes_mem b)
              · by_cases hb : b = i_r
                · rw [hb] at hab ⊢
                  exfalso
                  rw [hf_ne a ha, hf_i] at hab
                  have hc_eq : c = es a := by
                    calc c = et i_c := hi_c.symm
                      _ = et (p a) := by rw [hab]
                      _ = es a := hp a (h1 a ha)
                  exact hc' (by rw [hc_eq]; exact hes_mem a)
                · have hpa : p a = p b := by
                    rw [hf_ne a ha, hf_ne b hb] at hab
                    exact hab
                  have hes_eq : es a = es b := by
                    rw [← hp a (h1 a ha), ← hp b (h1 b hb), hpa]
                  exact hes_inj hes_eq
            have hRdet : Rmat.det = 1 := by
              rw [hR, det_of_row_eq_ite_single_of_injective f hf]
              exact hsign _
            have ht_eq : (t : Finset (Fin m)) = insert c ((s : Finset (Fin m)).erase r) := by
              ext a
              constructor
              · intro ha
                obtain ⟨q, hq⟩ := exists_ofFinEmbEquiv_symm_eq_of_mem t ha
                obtain ⟨a', ha'⟩ := hf.bijective_of_finite.2 q
                by_cases hia : a' = i_r
                · have hq_eq : q = i_c := by rw [← ha', hia, hf_i]
                  have ha_eq : a = c := by
                    calc a = et q := hq.symm
                      _ = et i_c := by rw [hq_eq]
                      _ = c := hi_c
                  rw [ha_eq]
                  exact Finset.mem_insert_self _ _
                · have hp_eq : p a' = q := by
                    rw [← ha', hf_ne a' hia]
                  have ha_eq : a = es a' := by
                    calc a = et q := hq.symm
                      _ = et (p a') := by rw [← hp_eq]
                      _ = es a' := hp a' (h1 a' hia)
                  refine Finset.mem_insert_of_mem ?_
                  rw [Finset.mem_erase]
                  refine ⟨?_, ?_⟩
                  · intro h
                    apply hia
                    apply hes_inj
                    calc es a' = a := ha_eq.symm
                      _ = r := h
                      _ = es i_r := hi_r.symm
                  · rw [ha_eq]; exact hes_mem a'
              · intro ha
                rcases Finset.mem_insert.mp ha with rfl | ha
                · exact hc
                · have hne : a ≠ r := (Finset.mem_erase.mp ha).1
                  have has : a ∈ (s : Finset (Fin m)) := (Finset.mem_erase.mp ha).2
                  obtain ⟨a', ha'⟩ := exists_ofFinEmbEquiv_symm_eq_of_mem s has
                  have hia : a' ≠ i_r := by
                    intro h
                    apply hne
                    calc a = es a' := ha'.symm
                      _ = es i_r := by rw [h]
                      _ = r := hi_r
                  rw [← ha']
                  exact h1 a' hia
            have hs_eq : (s : Finset (Fin m)) = insert r ((t : Finset (Fin m)).erase c) := by
              rw [ht_eq]
              rw [Finset.erase_insert (by simp [hc']), Finset.insert_erase hr]
            have hrt : r ∉ (t : Finset (Fin m)) := by
              rw [ht_eq]
              simp [hrc]
            have hcond : c ∈ (t : Finset (Fin m)) ∧ r ∉ (t : Finset (Fin m)) ∧
                (s : Finset (Fin m)) = insert r ((t : Finset (Fin m)).erase c) :=
              ⟨hc, hrt, hs_eq⟩
            rw [hRdet, mul_one, if_pos hcond]
        · obtain ⟨k, hk⟩ := not_forall.mp h1
          obtain ⟨hkir, hkt⟩ := not_imp.mp hk
          have hRdet : Rmat.det = 0 := by
            refine Matrix.det_eq_zero_of_row_eq_zero k (fun j => ?_)
            have hne : es k ≠ et j := fun h => hkt (h ▸ het_mem j)
            simp [hRdef, Matrix.updateRow_ne hkir, Matrix.submatrix_apply, hne]
          have hcond : ¬ (c ∈ (t : Finset (Fin m)) ∧ r ∉ (t : Finset (Fin m)) ∧
              (s : Finset (Fin m)) = insert r ((t : Finset (Fin m)).erase c)) := by
            rintro ⟨-, -, hs⟩
            have hks : es k ∈ (s : Finset (Fin m)) := hes_mem k
            rw [hs] at hks
            rcases Finset.mem_insert.mp hks with h | h
            · exact hkir (hes_inj (by rw [h, hi_r]))
            · exact hkt (Finset.mem_of_mem_erase h)
          rw [hRdet, mul_zero, if_neg hcond]
      · have hB : (Matrix.single r c (1 : R)).submatrix es et = 0 := by
          ext a b
          simp only [Matrix.submatrix_apply, Matrix.single_apply]
          have hne : ¬ (r = es a ∧ c = et b) := by
            rintro ⟨-, hc'⟩
            exact hc (by rw [hc']; exact het_mem b)
          simp [hne]
        have hcond : ¬ (c ∈ (t : Finset (Fin m)) ∧ r ∉ (t : Finset (Fin m)) ∧
            (s : Finset (Fin m)) = insert r ((t : Finset (Fin m)).erase c)) :=
          fun h => hc h.1
        rw [hB, smul_zero, add_zero, hI, if_neg hcond]
    · have hB : (Matrix.single r c (1 : R)).submatrix es et = 0 := by
        ext a b
        simp only [Matrix.submatrix_apply, Matrix.single_apply]
        have hne : ¬ (r = es a ∧ c = et b) := by
          rintro ⟨hr', -⟩
          exact hr (by rw [hr']; exact hes_mem a)
        simp [hne]
      have hcond : ¬ (c ∈ (t : Finset (Fin m)) ∧ r ∉ (t : Finset (Fin m)) ∧
          (s : Finset (Fin m)) = insert r ((t : Finset (Fin m)).erase c)) := by
        rintro ⟨-, -, hs⟩
        exact hr (by rw [hs]; exact Finset.mem_insert_self _ _)
      rw [hB, smul_zero, add_zero, hI, if_neg hcond]

end CFSG.LieType.SpecialLinear.ExteriorModel
