module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.D4Levi

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.Lie

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement

variable {F : Type} [Field F]

noncomputable abbrev frame4 (F : Type) [Field F] : HypFrame (quadPlus 4 F) 4 :=
  plusFrame 4 F three_le_four

structure LeviFrame where
  ι : Fin 3 → Fin 4
  σ : Fin 3 → Bool
  m : Fin 4
  inj : Function.Injective ι
  ne_m : ∀ k, ι k ≠ m
  cover : ∀ i, i = m ∨ ∃ k, ι k = i

namespace LeviFrame

variable (L : LeviFrame)

noncomputable abbrev b (F : Type) [Field F] (k : Fin 3) : Fin 4 ⊕ Fin 4 → F :=
  (frame4 F).vec (L.ι k) (L.σ k)

noncomputable abbrev b' (F : Type) [Field F] (k : Fin 3) : Fin 4 ⊕ Fin 4 → F :=
  (frame4 F).vec (L.ι k) (!L.σ k)

theorem polar_b_b' (m k : Fin 3) :
    polar (quadPlus 4 F) (L.b F m) (L.b' F k) = if m = k then 1 else 0 := by
  rw [HypFrame.polar_vec_vec, Bool.not_not]
  by_cases h : m = k
  · subst h; simp
  · rw [ite_eq_right (fun h' => h (L.inj h'.1)), ite_eq_right h]

theorem polar_b'_b (m k : Fin 3) :
    polar (quadPlus 4 F) (L.b' F m) (L.b F k) = if m = k then 1 else 0 := by
  rw [polar_comm, polar_b_b']
  by_cases h : m = k
  · subst h; simp
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]

theorem polar_b_b (m k : Fin 3) : polar (quadPlus 4 F) (L.b F m) (L.b F k) = 0 := by
  rw [HypFrame.polar_vec_vec, ite_eq_right]
  rintro ⟨h1, h2⟩
  rw [L.inj h1] at h2
  cases h : L.σ k <;> simp_all

theorem polar_b'_b' (m k : Fin 3) : polar (quadPlus 4 F) (L.b' F m) (L.b' F k) = 0 := by
  rw [HypFrame.polar_vec_vec, ite_eq_right]
  rintro ⟨h1, h2⟩
  rw [L.inj h1] at h2
  cases h : L.σ k <;> simp_all

theorem polar_m_b (s : Bool) (k : Fin 3) :
    polar (quadPlus 4 F) ((frame4 F).vec L.m s) (L.b F k) = 0 :=
  (frame4 F).polar_vec_of_ne (L.ne_m k).symm _ _

theorem polar_m_b' (s : Bool) (k : Fin 3) :
    polar (quadPlus 4 F) ((frame4 F).vec L.m s) (L.b' F k) = 0 :=
  (frame4 F).polar_vec_of_ne (L.ne_m k).symm _ _

noncomputable abbrev W (F : Type) [Field F] : Submodule F (Fin 4 ⊕ Fin 4 → F) :=
  Submodule.span F (Set.range (L.b F))

noncomputable abbrev W' (F : Type) [Field F] : Submodule F (Fin 4 ⊕ Fin 4 → F) :=
  Submodule.span F (Set.range (L.b' F))

theorem eq_sum_of_mem_W {w : Fin 4 ⊕ Fin 4 → F} (hw : w ∈ L.W F) :
    w = ∑ k, polar (quadPlus 4 F) w (L.b' F k) • L.b F k := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hw
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [← polarBilin_apply_apply, map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, polarBilin_apply_apply, polar_b_b', smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem eq_sum_of_mem_W' {w : Fin 4 ⊕ Fin 4 → F} (hw : w ∈ L.W' F) :
    w = ∑ k, polar (quadPlus 4 F) w (L.b F k) • L.b' F k := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hw
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [← polarBilin_apply_apply, map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, polarBilin_apply_apply, polar_b'_b, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem polar_W_b {w : Fin 4 ⊕ Fin 4 → F} (hw : w ∈ L.W F) (k : Fin 3) :
    polar (quadPlus 4 F) w (L.b F k) = 0 := by
  rw [L.eq_sum_of_mem_W hw, ← polarBilin_apply_apply, map_sum, LinearMap.sum_apply]
  simp [polar_b_b]

theorem polar_W'_b' {w : Fin 4 ⊕ Fin 4 → F} (hw : w ∈ L.W' F) (k : Fin 3) :
    polar (quadPlus 4 F) w (L.b' F k) = 0 := by
  rw [L.eq_sum_of_mem_W' hw, ← polarBilin_apply_apply, map_sum, LinearMap.sum_apply]
  simp [polar_b'_b']

@[expose] noncomputable def y {k l : Fin 3} (hkl : k ≠ l) (c : F) : spinGroup (quadPlus 4 F) :=
  (frame4 F).longRoot (L.inj.ne hkl) (L.σ k) (!L.σ l) (.ofAdd c)

theorem spinAction_y {k l : Fin 3} (hkl : k ≠ l) (c : F) (v : Fin 4 ⊕ Fin 4 → F) :
    spinAction (quadPlus 4 F) (L.y hkl c) v =
      v + (c * polar (quadPlus 4 F) v (L.b' F l)) • L.b F k -
        (c * polar (quadPlus 4 F) v (L.b F k)) • L.b' F l :=
  (frame4 F).spinAction_longRoot _ _ _ c v

theorem y_inv {k l : Fin 3} (hkl : k ≠ l) (c : F) : (L.y hkl c)⁻¹ = L.y hkl (-c) := by
  rw [y, y, ← map_inv]
  rfl

@[expose] def Pres (g : spinGroup (quadPlus 4 F)) : Prop :=
  (∀ w ∈ L.W F, spinAction (quadPlus 4 F) g w ∈ L.W F) ∧
    (∀ w ∈ L.W' F, spinAction (quadPlus 4 F) g w ∈ L.W' F) ∧
    ∀ s, spinAction (quadPlus 4 F) g ((frame4 F).vec L.m s) = (frame4 F).vec L.m s

theorem pres_one : L.Pres (1 : spinGroup (quadPlus 4 F)) :=
  ⟨fun w hw => by simpa using hw, fun w hw => by simpa using hw, fun s => by simp⟩

theorem Pres.mul {L : LeviFrame} {g h : spinGroup (quadPlus 4 F)} (hg : L.Pres g)
    (hh : L.Pres h) : L.Pres (g * h) := by
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun s => ?_⟩
  · rw [map_mul, LinearEquiv.mul_apply]
    exact hg.1 _ (hh.1 w hw)
  · rw [map_mul, LinearEquiv.mul_apply]
    exact hg.2.1 _ (hh.2.1 w hw)
  · rw [map_mul, LinearEquiv.mul_apply, hh.2.2, hg.2.2]

theorem pres_y {k l : Fin 3} (hkl : k ≠ l) (c : F) : L.Pres (L.y hkl c) := by
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun s => ?_⟩
  · rw [spinAction_y, L.polar_W_b hw, mul_zero, zero_smul, sub_zero]
    exact add_mem hw (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  · rw [spinAction_y, L.polar_W'_b' hw, mul_zero, zero_smul, add_zero]
    exact sub_mem hw (Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))
  · rw [spinAction_y, L.polar_m_b', L.polar_m_b, mul_zero, zero_smul, zero_smul, add_zero,
      sub_zero]

variable (F) in
@[expose] def stab : Subgroup (spinGroup (quadPlus 4 F)) where
  carrier := {g | L.Pres g ∧ L.Pres g⁻¹}
  mul_mem' := fun {_ _} ha hb => ⟨ha.1.mul hb.1, by rw [mul_inv_rev]; exact hb.2.mul ha.2⟩
  one_mem' := ⟨L.pres_one, by rw [inv_one]; exact L.pres_one⟩
  inv_mem' := fun {_} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

theorem y_mem_stab {k l : Fin 3} (hkl : k ≠ l) (c : F) : L.y hkl c ∈ L.stab F :=
  ⟨L.pres_y hkl c, by rw [y_inv]; exact L.pres_y hkl (-c)⟩

@[expose] noncomputable def mat (g : spinGroup (quadPlus 4 F)) : Matrix (Fin 3) (Fin 3) F :=
  Matrix.of fun k l => polar (quadPlus 4 F) (spinAction (quadPlus 4 F) g (L.b F l)) (L.b' F k)

theorem mat_one : L.mat (1 : spinGroup (quadPlus 4 F)) = 1 := by
  ext k l
  simp only [mat, Matrix.of_apply, map_one, LinearEquiv.coe_one, id_eq, polar_b_b',
    Matrix.one_apply]
  by_cases h : k = l
  · subst h; simp
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]

theorem mat_mul {g h : spinGroup (quadPlus 4 F)} (hh : L.Pres h) :
    L.mat (g * h) = L.mat g * L.mat h := by
  ext k l
  have hw : spinAction (quadPlus 4 F) h (L.b F l) ∈ L.W F :=
    hh.1 _ (Submodule.subset_span ⟨l, rfl⟩)
  simp only [mat, Matrix.of_apply, Matrix.mul_apply, map_mul, LinearEquiv.mul_apply]
  conv_lhs => rw [L.eq_sum_of_mem_W hw]
  rw [map_sum, ← polarBilin_apply_apply, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, map_smul, LinearMap.smul_apply, polarBilin_apply_apply, smul_eq_mul, mul_comm]

variable (F) in
@[expose] noncomputable def rho : L.stab F →* Matrix (Fin 3) (Fin 3) F where
  toFun g := L.mat g
  map_one' := L.mat_one
  map_mul' _ h := L.mat_mul h.2.1

theorem mat_y {k l : Fin 3} (hkl : k ≠ l) (c : F) :
    L.mat (L.y hkl c) = Matrix.transvection k l c := by
  ext a d
  simp only [mat, Matrix.of_apply, spinAction_y, polar_b_b', polar_b_b, Matrix.transvection,
    Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, polar_add_left, polar_sub_left,
    polar_smul_left, smul_eq_mul]
  by_cases had : a = d <;> by_cases hka : k = a <;> by_cases hdl : d = l <;> simp_all [eq_comm]

theorem rho_injective (h2 : (2 : F) = 0) : Function.Injective (L.rho F) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmat : L.mat (g : spinGroup (quadPlus 4 F)) = 1 := hg
  have hb : ∀ l, spinAction (quadPlus 4 F) (g : spinGroup (quadPlus 4 F)) (L.b F l) = L.b F l := by
    intro l
    have hw := g.2.1.1 _ (Submodule.subset_span ⟨l, rfl⟩)
    have hk : ∀ k, polar (quadPlus 4 F) (spinAction (quadPlus 4 F) (g : spinGroup (quadPlus 4 F))
        (L.b F l)) (L.b' F k) = if k = l then 1 else 0 := fun k => by
      have := congrFun (congrFun hmat k) l
      simpa [mat, Matrix.one_apply] using this
    rw [L.eq_sum_of_mem_W hw]
    simp [hk, ite_smul, Finset.sum_ite_eq']
  have hb' : ∀ l, spinAction (quadPlus 4 F) (g : spinGroup (quadPlus 4 F)) (L.b' F l) =
      L.b' F l := by
    intro l
    have hw := g.2.1.2.1 _ (Submodule.subset_span ⟨l, rfl⟩)
    have hk : ∀ k, polar (quadPlus 4 F) (spinAction (quadPlus 4 F) (g : spinGroup (quadPlus 4 F))
        (L.b' F l)) (L.b F k) = if l = k then 1 else 0 := fun k => by
      conv_lhs => rw [← hb k]
      rw [polar_spinAction, polar_b'_b]
    rw [L.eq_sum_of_mem_W' hw]
    simp [hk, ite_smul, Finset.sum_ite_eq]
  have hvec : ∀ i s, spinAction (quadPlus 4 F) (g : spinGroup (quadPlus 4 F))
      ((frame4 F).vec i s) = (frame4 F).vec i s := by
    intro i s
    rcases L.cover i with rfl | ⟨k, rfl⟩
    · exact g.2.1.2.2 s
    · by_cases hs : s = L.σ k
      · subst hs
        exact hb k
      · have hs' : s = !L.σ k := by
          cases s <;> cases h : L.σ k <;> simp_all
        subst hs'
        exact hb' k
  have hone : spinAction (quadPlus 4 F) (g : spinGroup (quadPlus 4 F)) = 1 := by
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.pi_ext
    intro a x
    have key : spinAction (quadPlus 4 F) (g : spinGroup (quadPlus 4 F)) (Pi.single a (1 : F)) =
        Pi.single a 1 := by
      rcases a with i | i
      · exact hvec i true
      · exact hvec i false
    have hx : (Pi.single a x : Fin 4 ⊕ Fin 4 → F) = x • Pi.single a 1 := by
      rw [← Pi.single_smul', smul_eq_mul, mul_one]
    simp only [LinearEquiv.coe_coe, LinearEquiv.coe_one, id_eq, hx, map_smul, key]
  have := isCentral_cliffordAlgebra_quadPlus F 4
  have hker : (g : spinGroup (quadPlus 4 F)) ∈ (spinAction (quadPlus 4 F)).ker :=
    MonoidHom.mem_ker.mpr hone
  rw [ker_spinAction_eq_bot_of_isCentral _ h2, Subgroup.mem_bot] at hker
  exact Subtype.ext hker

variable (F) in
@[expose] noncomputable def levi : Subgroup (spinGroup (quadPlus 4 F)) :=
  Subgroup.closure {g | ∃ (k l : Fin 3) (hkl : k ≠ l) (c : F), g = L.y hkl c}

theorem y_mem_levi {k l : Fin 3} (hkl : k ≠ l) (c : F) : L.y hkl c ∈ L.levi F :=
  Subgroup.subset_closure ⟨k, l, hkl, c, rfl⟩

theorem levi_le_stab : L.levi F ≤ L.stab F :=
  (Subgroup.closure_le _).mpr fun _ ⟨_, _, hkl, c, he⟩ => he ▸ L.y_mem_stab hkl c

theorem y_eq_commutator {k l m : Fin 3} (hkl : k ≠ l) (hlm : l ≠ m) (hkm : k ≠ m) (a b : F) :
    L.y hkm (a * b) = ⁅L.y hkl a, L.y hlm b⁆ := by
  have h := (frame4 F).commutator_longRoot_longRoot (L.inj.ne hkl) (L.inj.ne hlm) (L.inj.ne hkm)
    (L.σ k) (!L.σ l) (!L.σ m) a b
  rw [Bool.not_not] at h
  exact h.symm

theorem eq_one_of_ne_zero_of_card_two {c : F} [Fintype F] (hF : Fintype.card F = 2) (hc : c ≠ 0) :
    c = 1 := by
  have h := FiniteField.pow_card c
  rw [hF, _root_.sq] at h
  exact mul_right_cancel₀ hc (h.trans (one_mul c).symm)

theorem exists_mat_eq [Fintype F] (hF : Fintype.card F = 2)
    (M : Matrix.SpecialLinearGroup (Fin 3) F) : ∃ g ∈ L.levi F, L.mat g = M.1 := by
  refine Matrix.SpecialLinearGroup.diagonal_transvection_induction'
    (fun N => ∃ g ∈ L.levi F, L.mat g = N.1) M ?_ ?_ ?_
  · intro i j hij c hc
    refine ⟨1, one_mem _, ?_⟩
    rw [L.mat_one, Matrix.SpecialLinearGroup.diag2n_coe, eq_one_of_ne_zero_of_card_two hF hc]
    ext a d
    simp [Matrix.diagonal_apply, Matrix.one_apply]
  · intro i j hij a
    exact ⟨L.y hij a, L.y_mem_levi hij a, L.mat_y hij a⟩
  · rintro A B ⟨g, hg, hgA⟩ ⟨h, hh, hhB⟩
    refine ⟨g * h, mul_mem hg hh, ?_⟩
    rw [L.mat_mul (L.levi_le_stab hh).1, hgA, hhB]
    rfl

variable (F) in
@[expose] noncomputable def leviHom : L.levi F →* GL (Fin 3) F :=
  ((L.rho F).comp (Subgroup.inclusion L.levi_le_stab)).toHomUnits

theorem leviHom_bijective [Fintype F] (hF : Fintype.card F = 2) (h2 : (2 : F) = 0) :
    Function.Bijective (L.leviHom F) := by
  refine ⟨fun g h hgh => ?_, fun M => ?_⟩
  · have h1 : L.rho F (Subgroup.inclusion L.levi_le_stab g) =
        L.rho F (Subgroup.inclusion L.levi_le_stab h) := by
      have := congrArg (fun U : GL (Fin 3) F => (U : Matrix (Fin 3) (Fin 3) F)) hgh
      exact this
    exact Subgroup.inclusion_injective _ (L.rho_injective h2 h1)
  · have hdet : (M : Matrix (Fin 3) (Fin 3) F).det = 1 :=
      eq_one_of_ne_zero_of_card_two hF (M.isUnit.map Matrix.detMonoidHom).ne_zero
    obtain ⟨g, hg, hgM⟩ := L.exists_mat_eq hF ⟨M, hdet⟩
    exact ⟨⟨g, hg⟩, Units.ext hgM⟩

end LeviFrame

end CFSG.AGLEmbeddingD2.McLaughlin.Lie
