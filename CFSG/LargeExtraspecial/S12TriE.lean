module

public import CFSG.LargeExtraspecial.S12TriB
public import CFSG.Fischer.Classification.Orthogonal3.Mu

public section

namespace CFSG.LargeExtraspecial.S12Tri

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Subgroup CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification
open CFSG.Fischer.Classification.F3

variable {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

theorem nondegOn_perp_three (hf : IsF3Form f) {u v w : Fin m → ZMod 3} (hu : f u u = 1)
    (hv : f v v = 1) (hw : f w w = 1) (huv : f u v = 0) (huw : f u w = 0) (hvw : f v w = 0) :
    ∀ y ∈ perpSub f ![u, v, w], y ≠ 0 → ∃ y' ∈ perpSub f ![u, v, w], f y y' ≠ 0 := by
  have hvu : f v u = 0 := by rw [hf.symm]; exact huv
  have hwu : f w u = 0 := by rw [hf.symm]; exact huw
  have hwv : f w v = 0 := by rw [hf.symm]; exact hvw
  refine nondegOn_of_proj hf (fun y => y - f y u • u - f y v • v - f y w • w)
    (fun y => mem_perpSub_three.2 ⟨?_, ?_, ?_⟩) fun x hx y => ?_
  · simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hu, hvu, hwu]
    ring
  · simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hv, huv, hwv]
    ring
  · simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hw, huw, hvw]
    ring
  · obtain ⟨h1, h2, h3⟩ := mem_perpSub_three.1 hx
    simp only [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right, h1, h2, h3]
    ring

theorem exists_isotropic_perp_three (hf : IsF3Form f) (hm : 6 ≤ m) {u v w : Fin m → ZMod 3}
    (hu : f u u = 1) (hv : f v v = 1) (hw : f w w = 1) (huv : f u v = 0) (huw : f u w = 0)
    (hvw : f v w = 0) : ∃ z, z ≠ 0 ∧ f z z = 0 ∧ f z u = 0 ∧ f z v = 0 ∧ f z w = 0 := by
  obtain ⟨z, hz, hz0, hzz⟩ := exists_mem_isotropic hf (nondegOn_perp_three hf hu hv hw huv huw hvw)
    (perpSub_threeDim hf (k := 3) (by omega) _)
  obtain ⟨h1, h2, h3⟩ := mem_perpSub_three.1 hz
  exact ⟨z, hz0, hzz, h1, h2, h3⟩

theorem exists_orthonormal_of_anisotropic (hf : IsF3Form f) (hm : 5 ≤ m)
    {u v w : Fin m → ZMod 3} (hu : f u u = 1) (hv : f v v = 1) (hw : f w w = 1)
    (huv : f u v = 0) (huw : f u w = 0) (hvw : f v w = 0)
    (han : ∀ z ∈ perpSub f ![u, v, w], f z z = 0 → z = 0) :
    ∃ a b, f a a = 1 ∧ f b b = 1 ∧ f a b = 0 ∧ a ∈ perpSub f ![u, v, w] ∧
      b ∈ perpSub f ![u, v, w] := by
  have hnd := nondegOn_perp_three hf hu hv hw huv huw hvw
  have h2d := perpSub_twoDim hf (k := 3) (by omega) ![u, v, w]
  obtain ⟨a, ha, haa⟩ := exists_mem_norm_eq hf hnd h2d (one_ne_zero (α := ZMod 3))
  obtain ⟨b, hb, hb0, hab⟩ := h2d a ha
  have hbb : f b b ≠ 0 := fun h => hb0 (han b hb h)
  refine ⟨a, b, haa, ?_, hab, ha, hb⟩
  rcases (show f b b = 1 ∨ f b b = -1 by revert hbb; generalize f b b = c; revert c; decide)
    with h | h
  · exact h
  · exfalso
    have hba : f b a = 0 := by rw [hf.symm]; exact hab
    have hiso : f (a + b) (a + b) = 0 := by
      simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, haa, hab, hba, h]
      decide
    have h0 := han (a + b) ((perpSub f ![u, v, w]).add_mem ha hb) hiso
    have : f a (a + b) = 0 := by rw [h0, LinearMap.BilinForm.zero_right]
    rw [LinearMap.BilinForm.add_right, haa, hab, add_zero] at this
    exact one_ne_zero this

theorem refl_prod_eq_neg_one (hm : m = 5) {y : Fin 5 → Fin m → ZMod 3}
    (hy : ∀ i j, f (y i) (y j) = if i = j then 1 else 0) :
    refl f (y 0) * refl f (y 1) * refl f (y 2) * refl f (y 3) * refl f (y 4) = -1 := by
  have hy1 : ∀ i, f (y i) (y i) = 1 := fun i => by rw [hy]; simp
  have hli : LinearIndependent (ZMod 3) y := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := congrArg (fun x => f x (y i)) hg
    simp only [LinearMap.BilinForm.sum_left, LinearMap.BilinForm.smul_left, hy,
      LinearMap.BilinForm.zero_left, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
    exact h
  have hspan := hli.span_eq_top_of_card_eq_finrank (by simp [hm])
  have hexp : ∀ x, x = ∑ i, f x (y i) • y i := by
    intro x
    have hx : x ∈ Submodule.span (ZMod 3) (Set.range y) := hspan ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 3)).1 hx
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    simp only [LinearMap.BilinForm.sum_left, LinearMap.BilinForm.smul_left, hy,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  refine gl_ext fun x => ?_
  rw [act_neg_one]
  simp only [act_mul, act_refl (hy1 _), LinearMap.BilinForm.add_left,
    LinearMap.BilinForm.smul_left, hy]
  simp only [Fin.isValue, Fin.reduceEq, ite_false, mul_zero, add_zero]
  have hx := hexp x
  rw [Fin.sum_univ_five] at hx
  have h2 : x + x = -x := by
    ext i
    simp only [Pi.add_apply, Pi.neg_apply]
    generalize x i = c
    revert c
    decide
  calc x + f x (y 4) • y 4 + f x (y 3) • y 3 + f x (y 2) • y 2 + f x (y 1) • y 1 +
        f x (y 0) • y 0
      = x + (f x (y 0) • y 0 + f x (y 1) • y 1 + f x (y 2) • y 2 + f x (y 3) • y 3 +
        f x (y 4) • y 4) := by abel
    _ = -x := by rw [← hx, h2]

theorem reflBar_mem_commutator_of_orthonormal (hf : IsF3Form f) (hm : m = 5)
    {y : Fin 5 → Fin m → ZMod 3} (hy : ∀ i j, f (y i) (y j) = if i = j then 1 else 0) :
    reflBar f (y 0) ∈ commutator (R3 f) := by
  have hy1 : ∀ i, f (y i) (y i) = 1 := fun i => by rw [hy]; simp
  have hP := pair_R3 hf (by omega)
  set P := reflElt f (y 0) * reflElt f (y 1) * reflElt f (y 2) * reflElt f (y 3) *
    reflElt f (y 4) with hPdef
  have hPc : (P : GL (Fin m) (ZMod 3)) = -1 := by
    rw [hPdef]
    simp only [Subgroup.coe_mul, coe_reflElt]
    exact refl_prod_eq_neg_one hm hy
  clear_value P
  have hPZ : P ∈ center (F3.reflGroup f) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hPc, mul_neg_one, neg_one_mul]
  have h1 : reflBar f (y 0) * (reflBar f (y 1) * reflBar f (y 2) * (reflBar f (y 3) *
      reflBar f (y 4))) = 1 := by
    have : (QuotientGroup.mk P : R3 f) = 1 := (QuotientGroup.eq_one_iff P).2 hPZ
    rw [hPdef] at this
    simpa only [QuotientGroup.mk_mul, reflBar_def, mul_assoc] using this
  have hpair : ∀ i j, reflBar f (y i) * reflBar f (y j) ∈ commutator (R3 f) := fun i j => by
    have h := Pair.mul_inv_mem_commutator hP (reflBar_mem_D3 (hy1 j)) (reflBar_mem_D3 (hy1 i))
    rwa [Pair.inv_eq hP (reflBar_mem_D3 (hy1 j))] at h
  rw [eq_inv_of_mul_eq_one_left h1]
  exact inv_mem (mul_mem (hpair 1 2) (hpair 3 4))

theorem triGood_R3 (hf : IsF3Form f) (hm : 5 ≤ m) (hS : IsSimpleGroup (commutator (R3 f)))
    (hna : ∃ a b : commutator (R3 f), a * b ≠ b * a) {v : Fin m → ZMod 3} (hv : f v v = 1)
    (hX : reflBar f v ∉ commutator (R3 f)) : TriGood (R3 f) (reflBar f v) := by
  have hm4 : 4 ≤ m := by omega
  have hP := pair_R3 hf hm4
  have hZ := center_R3_eq_bot hf hm4
  have hH : Hyp (R3 f) (D3 f) := ⟨hP, hZ, hS⟩
  have hd := reflBar_mem_D3 hv
  have hloc := localClass_D3 hf hm4 hv
  have hsym : ∀ {x y : Fin m → ZMod 3}, f x y = 0 → f y x = 0 := fun h => by
    rw [hf.symm]; exact h
  have hmem : ∀ {w}, f w w = 1 → f w v = 0 → reflBar f w ∈ LocalClass (D3 f) (reflBar f v) :=
    fun hw hwv => by rw [hloc]; exact ⟨_, hw, hwv, rfl⟩
  have hmem' : ∀ q ∈ LocalClass (D3 f) (reflBar f v),
      ∃ w, f w w = 1 ∧ f w v = 0 ∧ reflBar f w = q := fun q hq => by
    rw [hloc] at hq; exact hq
  refine triGood_of_local hH hna hd hX ?_ ?_ ?_
  · exact fun y hyd hyD =>
      Pair.eq_one_or_eq_of_centralizes hP hZ hS hna (tripleProperty_D3 hf hm) hd hyd hyD
  · obtain ⟨w₁, hw₁, hw₁v⟩ := exists_norm_eq_perp hf (by omega) hv (one_ne_zero (α := ZMod 3))
    obtain ⟨w₂, hw₂, hw₂v, hw₂w₁⟩ :=
      exists_norm_eq_perp_two hf hm4 hv hw₁ (hsym hw₁v) (one_ne_zero (α := ZMod 3))
    refine ⟨_, hmem hw₁ hw₁v, _, hmem hw₂ hw₂v, fun h => ?_, ?_⟩
    · rcases (reflBar_eq_reflBar_iff hf hm4 hw₁ hw₂).1 h with h' | h'
      · rw [h', hw₁] at hw₂w₁
        exact one_ne_zero hw₂w₁
      · rw [h', LinearMap.BilinForm.neg_left, hw₁] at hw₂w₁
        exact one_ne_zero (neg_eq_zero.1 hw₂w₁)
    · exact (reflBar_commute_iff hf hm4 hw₁ hw₂).2 (Or.inl (hsym hw₂w₁))
  · intro x hx y hy hxy hc
    obtain ⟨w₁, hw₁, hw₁v, rfl⟩ := hmem' x hx
    obtain ⟨w₂, hw₂, hw₂v, rfl⟩ := hmem' y hy
    have h12 : f w₁ w₂ = 0 := by
      rcases (reflBar_commute_iff hf hm4 hw₁ hw₂).1 hc with h | h | h
      · exact h
      · exact absurd (by rw [h]) hxy
      · exact absurd (by rw [h, reflBar_neg]) hxy
    obtain ⟨z, hz0, hzz, hzv, hz1, hz2⟩ :
        ∃ z, z ≠ 0 ∧ f z z = 0 ∧ f z v = 0 ∧ f z w₁ = 0 ∧ f z w₂ = 0 := by
      rcases (show m = 5 ∨ 6 ≤ m by omega) with h5 | h6
      · by_contra hno
        have han : ∀ z ∈ perpSub f ![v, w₁, w₂], f z z = 0 → z = 0 := by
          intro z hz hzz
          obtain ⟨h1, h2, h3⟩ := mem_perpSub_three.1 hz
          by_contra hz0
          exact hno ⟨z, hz0, hzz, h1, h2, h3⟩
        obtain ⟨a, b, haa, hbb, hab, ha, hb⟩ := exists_orthonormal_of_anisotropic hf hm hv hw₁
          hw₂ (hsym hw₁v) (hsym hw₂v) h12 han
        obtain ⟨ha1, ha2, ha3⟩ := mem_perpSub_three.1 ha
        obtain ⟨hb1, hb2, hb3⟩ := mem_perpSub_three.1 hb
        apply hX
        have hy : ∀ i j, f (![v, w₁, w₂, a, b] i) (![v, w₁, w₂, a, b] j) =
            if i = j then 1 else 0 := by
          intro i j
          fin_cases i <;> fin_cases j <;>
            simp [hv, hw₁, hw₂, haa, hbb, hab, hw₁v, hw₂v, h12, ha1, ha2, ha3, hb1, hb2, hb3,
              hsym hw₁v, hsym hw₂v, hsym h12, hsym ha1, hsym ha2, hsym ha3, hsym hb1, hsym hb2,
              hsym hb3, hsym hab]
        exact reflBar_mem_commutator_of_orthonormal hf h5 hy
      · exact exists_isotropic_perp_three hf h6 hv hw₁ hw₂ (hsym hw₁v) (hsym hw₂v) h12
    have huu : f (w₁ + z) (w₁ + z) = 1 := by
      simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hw₁, hz1,
        hsym hz1, hzz, add_zero]
    have huv : f (w₁ + z) v = 0 := by
      rw [LinearMap.BilinForm.add_left, hw₁v, hzv, add_zero]
    have hu2 : f (w₁ + z) w₂ = 0 := by
      rw [LinearMap.BilinForm.add_left, h12, hz2, add_zero]
    have hu1 : f (w₁ + z) w₁ = 1 := by
      rw [LinearMap.BilinForm.add_left, hw₁, hz1, add_zero]
    refine ⟨reflBar f (w₁ + z), hmem huu huv,
      (reflBar_commute_iff hf hm4 huu hw₂).2 (Or.inl hu2), fun h => ?_⟩
    rcases (reflBar_commute_iff hf hm4 huu hw₁).1 h with h' | h' | h'
    · rw [hu1] at h'
      exact one_ne_zero h'
    · exact hz0 (by simpa using (congrArg (· - w₁) h').symm)
    · have h3 : z = w₁ := by
        ext i
        have := congrFun h' i
        simp only [Pi.neg_apply, Pi.add_apply] at this
        revert this
        generalize w₁ i = a
        generalize z i = b
        revert a b
        decide
      rw [h3, hw₁] at hz1
      exact one_ne_zero hz1

theorem triGood_case5 {G : Type} [Group G] {D : Set G} (hH : Hyp G D)
    (hna : ∃ a b : commutator G, a * b ≠ b * a) {t : G} (ht : t ∈ D) (htG : t ∉ commutator G)
    (h5 : ∃ m : ℕ, 5 ≤ m ∧ ∃ f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3),
      (∀ x y, f x y = f y x) ∧ (∀ x, (∀ y, f x y = 0) → x = 0) ∧
      CFSG.Open.fischerCentralQuotientModel D
        (Subgroup.closure (CFSG.Open.fischerTransvections (fun x y => f x y) fun v => f v v = 1))
        (CFSG.Open.fischerTransvections (fun x y => f x y) fun v => f v v = 1)) :
    TriGood G t := by
  obtain ⟨m, hm, f, hsymm, hnd, hmodel⟩ := h5
  have hf : IsF3Form f := ⟨hsymm, hnd⟩
  obtain ⟨ψ, hψ⟩ := (fischerCentralQuotientModel_iff D).1 hmodel
  obtain ⟨v, hv, hvd⟩ := mem_D3_iff.1 ((hψ t).1 ht)
  have := hH.simple
  have hS : IsSimpleGroup (commutator (R3 f)) := (commutatorEquiv ψ).symm.isSimpleGroup
  refine TriGood.of_mulEquiv ψ ?_
  rw [← hvd]
  refine triGood_R3 hf hm hS (nonabelian_map ψ hna) hv ?_
  rw [hvd, apply_mem_commutator_iff]
  exact htG

end CFSG.LargeExtraspecial.S12Tri
