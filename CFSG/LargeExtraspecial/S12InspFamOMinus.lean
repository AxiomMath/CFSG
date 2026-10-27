module

public import CFSG.Fischer.Classification.Symplectic.OrthoGen
public import CFSG.LargeExtraspecial.S12InspFamDefs
public import CFSG.LargeExtraspecial.S12InspFamTools

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap Matrix CFSG.RankThree.OrthogonalInvolutions
  CFSG.Fischer.Classification CFSG.ClassicalGroups.Orthogonal

namespace S12Insp5

@[expose] def q4Minus (x : Fin (2 * 2) → ZMod 2) : ZMod 2 :=
  x 0 * x 1 + x 2 * x 2 + x 2 * x 3 + x 3 * x 3

@[expose] def q4Plus (x : Fin (2 * 2) → ZMod 2) : ZMod 2 := x 0 * x 1 + x 2 * x 3

@[expose] def b4 (x y : Fin (2 * 2) → ZMod 2) : ZMod 2 :=
  x 0 * y 1 + x 1 * y 0 + x 2 * y 3 + x 3 * y 2

noncomputable def quadMinusFour : QuadraticForm (ZMod 2) (Fin (2 * 2) → ZMod 2) :=
  QuadraticMap.proj 0 1 + QuadraticMap.proj 2 2 + QuadraticMap.proj 2 3 + QuadraticMap.proj 3 3

noncomputable def quadPlusFour : QuadraticForm (ZMod 2) (Fin (2 * 2) → ZMod 2) :=
  QuadraticMap.proj 0 1 + QuadraticMap.proj 2 3

theorem quadMinusFour_apply (x : Fin (2 * 2) → ZMod 2) : quadMinusFour x = q4Minus x := by
  simp only [quadMinusFour, _root_.add_apply, proj_apply, q4Minus]

theorem quadPlusFour_apply (x : Fin (2 * 2) → ZMod 2) : quadPlusFour x = q4Plus x := by
  simp only [quadPlusFour, _root_.add_apply, proj_apply, q4Plus]

theorem polar_quadMinusFour (x y : Fin (2 * 2) → ZMod 2) :
    polar quadMinusFour x y = b4 x y := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  simp only [polar, quadMinusFour_apply, q4Minus, b4, Pi.add_apply]
  linear_combination (x 2 * y 2 + x 3 * y 3) * h2

theorem polar_quadPlusFour (x y : Fin (2 * 2) → ZMod 2) : polar quadPlusFour x y = b4 x y := by
  simp only [polar, quadPlusFour_apply, q4Plus, b4, Pi.add_apply]
  ring

theorem b4_nondeg : ∀ x : Fin (2 * 2) → ZMod 2, b4 x ![0, 1, 0, 0] = 0 → b4 x ![1, 0, 0, 0] = 0 →
    b4 x ![0, 0, 0, 1] = 0 → b4 x ![0, 0, 1, 0] = 0 → x = 0 := by
  decide

theorem quadMinusFour_nondeg : ∀ x, (∀ y, polar quadMinusFour x y = 0) → x = 0 := fun x hx => by
  simp only [polar_quadMinusFour] at hx
  exact b4_nondeg x (hx _) (hx _) (hx _) (hx _)

theorem quadPlusFour_nondeg : ∀ x, (∀ y, polar quadPlusFour x y = 0) → x = 0 := fun x hx => by
  simp only [polar_quadPlusFour] at hx
  exact b4_nondeg x (hx _) (hx _) (hx _) (hx _)

theorem ncard_quadMinusFour : {v | quadMinusFour v = 1}.ncard = 10 := by
  simp only [quadMinusFour_apply]
  rw [Set.ncard_eq_toFinset_card']
  decide

theorem ncard_quadPlusFour : {v | quadPlusFour v = 1}.ncard = 6 := by
  simp only [quadPlusFour_apply]
  rw [Set.ncard_eq_toFinset_card']
  decide

noncomputable def plusPlane : Submodule (ZMod 2) (Fin (2 * 2) → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range ![(![1, 0, 0, 0] : Fin (2 * 2) → ZMod 2), ![0, 0, 1, 0]])

theorem finrank_plusPlane : finrank (ZMod 2) plusPlane = 2 := by
  rw [plusPlane, finrank_span_eq_card (LinearIndependent.pair_iff.mpr (by decide)),
    Fintype.card_fin]

theorem quadPlusFour_plusPlane : ∀ w ∈ plusPlane, quadPlusFour w = 0 := by
  intro w hw
  rw [plusPlane, Submodule.mem_span_range_iff_exists_fun] at hw
  obtain ⟨c, rfl⟩ := hw
  rw [quadPlusFour_apply]
  revert c
  decide

theorem ncard_eq_ten_of_minus {Q : QuadraticForm (ZMod 2) (Fin (2 * 2) → ZMod 2)}
    (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0)
    (hmin : ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * 2) → ZMod 2),
      finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0) :
    {v | Q v = 1}.ncard = 10 := by
  have h2 := LocalSymp.two_mul_ncard_quadratic Q hnd (m := 2) (by simp)
  rcases h2 with h | h
  · exfalso
    have hN6 : {v | Q v = 1}.ncard = 6 := by omega
    obtain ⟨L, hL⟩ := exists_linearEquiv_fin_of_ncard_eq Q quadPlusFour hnd quadPlusFour_nondeg
      (hN6.trans ncard_quadPlusFour.symm)
    refine hmin ⟨plusPlane.map L.symm.toLinearMap, by
      rw [LinearEquiv.finrank_map_eq, finrank_plusPlane], ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    rw [← hL, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact quadPlusFour_plusPlane w hw
  · omega

@[expose] def uPath : Fin 4 → (Fin (2 * 2) → ZMod 2) :=
  ![![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 1, 0, 1], ![1, 1, 0, 0]]

theorem q4Minus_cover : ∀ v : Fin (2 * 2) → ZMod 2, q4Minus v = 1 →
    v = uPath 0 ∨ v = uPath 1 ∨ v = uPath 2 ∨ v = uPath 3 ∨ v = uPath 0 + uPath 1 ∨
      v = uPath 1 + uPath 2 ∨ v = uPath 2 + uPath 3 ∨ v = uPath 0 + uPath 1 + uPath 2 ∨
      v = uPath 1 + uPath 2 + uPath 3 ∨ v = uPath 0 + uPath 1 + uPath 2 + uPath 3 := by
  decide

theorem uPath_values : q4Minus (uPath 0) = 1 ∧ q4Minus (uPath 1) = 1 ∧ q4Minus (uPath 2) = 1 ∧
    q4Minus (uPath 3) = 1 ∧ b4 (uPath 0) (uPath 1) = 1 ∧ b4 (uPath 1) (uPath 2) = 1 ∧
    b4 (uPath 2) (uPath 3) = 1 ∧ b4 (uPath 0 + uPath 1) (uPath 2) = 1 ∧
    b4 (uPath 1 + uPath 2) (uPath 3) = 1 ∧ b4 (uPath 0 + uPath 1 + uPath 2) (uPath 3) = 1 := by
  decide

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem orthTransvectionGL_reflect (Q : QuadraticForm (ZMod 2) (ι → ZMod 2))
    (a w : ι → ZMod 2) :
    orthTransvectionGL Q (reflect Q a w) =
      orthTransvectionGL Q a * orthTransvectionGL Q w * (orthTransvectionGL Q a)⁻¹ := by
  apply (toLinEquiv ι (ZMod 2)).injective
  rw [map_mul, map_mul, map_inv, toLinEquiv_orthTransvectionGL, toLinEquiv_orthTransvectionGL,
    toLinEquiv_orthTransvectionGL]
  exact (reflect_conj (reflect_mem_orthogonalGroup Q a) w).symm

theorem orthTransvectionGL_add_mem {Q : QuadraticForm (ZMod 2) (ι → ZMod 2)}
    {K : Subgroup (GL ι (ZMod 2))} {a w : ι → ZMod 2} (ha : Q a = 1) (hpol : polar Q w a = 1)
    (hra : orthTransvectionGL Q a ∈ K) (hrw : orthTransvectionGL Q w ∈ K) :
    orthTransvectionGL Q (w + a) ∈ K := by
  have e : reflect Q a w = w + a := by rw [reflect_apply_of_map_eq_one ha, hpol, one_smul]
  rw [← e, orthTransvectionGL_reflect]
  exact K.mul_mem (K.mul_mem hra hrw) (K.inv_mem hra)

theorem exists_path_minus_four {Q : QuadraticForm (ZMod 2) (Fin (2 * 2) → ZMod 2)}
    (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0)
    (hmin : ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * 2) → ZMod 2),
      finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0) :
    ∃ v : Fin 4 → (Fin (2 * 2) → ZMod 2), (∀ i, Q (v i) = 1) ∧ ∀ w, Q w = 1 →
      orthTransvectionGL Q w ∈
        Subgroup.closure (Set.range fun i => orthTransvectionGL Q (v i)) := by
  obtain ⟨L, hL⟩ := exists_linearEquiv_fin_of_ncard_eq Q quadMinusFour hnd quadMinusFour_nondeg
    ((ncard_eq_ten_of_minus hnd hmin).trans ncard_quadMinusFour.symm)
  have hLpol : ∀ x y, polar Q x y = b4 (L x) (L y) := fun x y => by
    rw [← polar_quadMinusFour, polar, polar, ← map_add, hL, hL, hL]
  set v : Fin 4 → (Fin (2 * 2) → ZMod 2) := fun i => L.symm (uPath i) with hv
  have hLv : ∀ i, L (v i) = uPath i := fun i => L.apply_symm_apply _
  obtain ⟨q0, q1, q2, q3, b01, b12, b23, b012, b123, b0123⟩ := uPath_values
  have hvQ : ∀ i, Q (v i) = 1 := fun i => by
    rw [← hL, hLv, quadMinusFour_apply]
    fin_cases i
    · exact q0
    · exact q1
    · exact q2
    · exact q3
  set K := Subgroup.closure (Set.range fun i => orthTransvectionGL Q (v i)) with hK
  have hb : ∀ i, orthTransvectionGL Q (v i) ∈ K := fun i => subset_closure ⟨i, rfl⟩
  have h01 : orthTransvectionGL Q (v 0 + v 1) ∈ K := orthTransvectionGL_add_mem (hvQ 1)
    (by rw [hLpol, hLv, hLv]; exact b01) (hb 1) (hb 0)
  have h12 : orthTransvectionGL Q (v 1 + v 2) ∈ K := orthTransvectionGL_add_mem (hvQ 2)
    (by rw [hLpol, hLv, hLv]; exact b12) (hb 2) (hb 1)
  have h23 : orthTransvectionGL Q (v 2 + v 3) ∈ K := orthTransvectionGL_add_mem (hvQ 3)
    (by rw [hLpol, hLv, hLv]; exact b23) (hb 3) (hb 2)
  have h012 : orthTransvectionGL Q (v 0 + v 1 + v 2) ∈ K := orthTransvectionGL_add_mem (hvQ 2)
    (by rw [hLpol, map_add, hLv, hLv, hLv]; exact b012) (hb 2) h01
  have h123 : orthTransvectionGL Q (v 1 + v 2 + v 3) ∈ K := orthTransvectionGL_add_mem (hvQ 3)
    (by rw [hLpol, map_add, hLv, hLv, hLv]; exact b123) (hb 3) h12
  have h0123 : orthTransvectionGL Q (v 0 + v 1 + v 2 + v 3) ∈ K :=
    orthTransvectionGL_add_mem (hvQ 3)
      (by rw [hLpol, map_add, map_add, hLv, hLv, hLv, hLv]; exact b0123) (hb 3) h012
  refine ⟨v, hvQ, fun w hw => ?_⟩
  have hw' : q4Minus (L w) = 1 := by rw [← quadMinusFour_apply, hL]; exact hw
  have hw_eq : w = L.symm (L w) := (L.symm_apply_apply w).symm
  rcases q4Minus_cover (L w) hw' with h | h | h | h | h | h | h | h | h | h <;>
    rw [hw_eq, h] <;> try simp only [map_add]
  · exact hb 0
  · exact hb 1
  · exact hb 2
  · exact hb 3
  · exact h01
  · exact h12
  · exact h23
  · exact h012
  · exact h123
  · exact h0123

end S12Insp5

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem false_of_orth_minus_four {g : G} (hn : 5 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (hred : ¬ S.IsReducible12)
    {Q : QuadraticForm (ZMod 2) (Fin (2 * 2) → ZMod 2)}
    (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0)
    (hmin : ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * 2) → ZMod 2),
      finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0)
    (hmod : CFSG.Open.fischerLinearModel (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
      (CFSG.Open.fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (CFSG.Open.fischerTransvections (polar Q) fun v => Q v = 1)) : False := by
  set H := CFSG.Open.fischerMatrixGroup fun A : Matrix (Fin (2 * 2)) (Fin (2 * 2)) (ZMod 2) =>
    ∀ x, Q (A *ᵥ x) = Q x with hH
  obtain ⟨φ, hφ⟩ := hmod
  obtain ⟨v, hvQ, hcov⟩ := S12Insp5.exists_path_minus_four hnd hmin
  have hrH : ∀ i, orthTransvectionGL Q (v i) ∈ H := fun i =>
    fischerTransvections_polar_subset (orthTransvectionGL_mem_fischerTransvections (hvQ i))
  set r : Fin 4 → H := fun i => ⟨orthTransvectionGL Q (v i), hrH i⟩ with hr
  set d : Fin 4 → S.O := fun i => ((φ.symm (r i) : S.Xbar12 g) : S.O) with hd
  have hdE : ∀ i, d i ∈ S.Ebar12 g := fun i => (hφ (φ.symm (r i))).mpr (by
    rw [MulEquiv.apply_symm_apply]
    exact orthTransvectionGL_mem_fischerTransvections (hvQ i))
  have hdA : ∀ i, IsTypeA S.q (d i : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 := fun i =>
    isTypeA_of_mem_Ebar12 (hdE i)
  have key : ∀ y ∈ Subgroup.closure (Set.range r),
      ((φ.symm y : S.Xbar12 g) : S.O) ∈ Subgroup.closure (Set.range d) := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Subgroup.subset_closure ⟨i, rfl⟩
    | one => simp
    | mul y z _ _ hy hz =>
      rw [map_mul, Subgroup.coe_mul]
      exact mul_mem hy hz
    | inv y _ hy =>
      rw [map_inv, Subgroup.coe_inv]
      exact inv_mem hy
  have hmap : (Subgroup.closure (Set.range r)).map H.subtype =
      Subgroup.closure (Set.range fun i => orthTransvectionGL Q (v i)) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hgen : S.Xbar12 g ≤ Subgroup.closure (Set.range d) := by
    show Subgroup.closure (S.Ebar12 g) ≤ _
    rw [Subgroup.closure_le]
    intro e he
    have hx : (⟨e, subset_Xbar12 he⟩ : S.Xbar12 g) ∈
        (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) := he
    obtain ⟨w, hw, hweq⟩ := eq_orthTransvectionGL_of_mem_fischerTransvections ((hφ _).mp hx)
    have h1 := hcov w hw
    rw [← hweq, ← hmap] at h1
    obtain ⟨y, hy, hyeq⟩ := h1
    have hy' : y = φ ⟨e, subset_Xbar12 he⟩ := Subtype.ext hyeq
    rw [hy'] at hy
    have := key _ hy
    simpa using this
  set U := commSpace (d 0 : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔ commSpace (d 1 : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔
    commSpace (d 2 : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔ commSpace (d 3 : S.Qt ≃ₗ[ZMod 2] S.Qt) with hUdef
  have hU : finrank (ZMod 2) U ≤ 8 := by
    rw [hUdef]
    have e1 := Submodule.finrank_add_le_finrank_add_finrank
      (commSpace (d 0 : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔ commSpace (d 1 : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔
        commSpace (d 2 : S.Qt ≃ₗ[ZMod 2] S.Qt)) (commSpace (d 3 : S.Qt ≃ₗ[ZMod 2] S.Qt))
    have e2 := Submodule.finrank_add_le_finrank_add_finrank
      (commSpace (d 0 : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔ commSpace (d 1 : S.Qt ≃ₗ[ZMod 2] S.Qt))
      (commSpace (d 2 : S.Qt ≃ₗ[ZMod 2] S.Qt))
    have e3 := Submodule.finrank_add_le_finrank_add_finrank
      (commSpace (d 0 : S.Qt ≃ₗ[ZMod 2] S.Qt)) (commSpace (d 1 : S.Qt ≃ₗ[ZMod 2] S.Qt))
    rw [(hdA 0).2.2.2.1, (hdA 1).2.2.2.1] at e3
    rw [(hdA 2).2.2.2.1] at e2
    rw [(hdA 3).2.2.2.1] at e1
    omega
  have hle : S.commSub12 (S.Xbar12 g) ≤ U := by
    refine (commSub12_mono hgen).trans ((commSub12_closure_le _).trans
      (commSubSet12_le ?_))
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact le_sup_of_le_left (le_sup_of_le_left le_sup_left)
    · exact le_sup_of_le_left (le_sup_of_le_left le_sup_right)
    · exact le_sup_of_le_left le_sup_right
    · exact le_sup_right
  apply hred
  have htX : t ∈ S.Xbar12 g := subset_Xbar12 (mem_Ebar12_of_mem_Lbar ht htA)
  have ht1 : t ≠ 1 := fun e => htA.2.1 (by rw [e]; rfl)
  refine S.s12_isReducible12_of_finrank_lt Mbar_le_normalizer_Xbar12 htX ht1 ?_
  rw [S.finrank_Qt_eq_two_mul_width]
  have := Submodule.finrank_mono hle
  omega

end Setting

open CFSG.Open in
@[expose] def FischerO3 (G : Type) [Group G] (D : Set G) : Prop :=
  ∃ m : ℕ, 3 ≤ m ∧ ∃ Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2),
    (∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) ∧
    fischerLinearModel D
      (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)

@[expose] def InspOTv3 : Prop := InspFor fun (X : Type) [Group X] (D : Set X) =>
  ¬ InspNondeg X D ∧ FischerO3 X D

theorem inspOTv_of (h3 : InspOTv3) : InspOTv := by
  intro G _ _ _ S g t haQ hne hn ht htA hS hred h
  obtain ⟨hND, m, hm, Q, hnd, hmin, hmod⟩ := h
  by_cases hm3 : 3 ≤ m
  · exact h3 G S g t haQ hne hn ht htA hS hred ⟨hND, m, hm3, Q, hnd, hmod⟩
  obtain rfl : m = 2 := by omega
  exact (Setting.false_of_orth_minus_four hn ht htA hred hnd (hmin rfl) hmod).elim

end CFSG.LargeExtraspecial
