module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Defs
public import CFSG.RankThree.Literature.FSmithOrthogonal
public import CFSG.LargeExtraspecial.S12DWSetting

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81.Sec2Omega

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

section General

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem two_mul_finrank_le_of_polar_eq_zero (hQ : (polarBilin Q).Nondegenerate)
    {U : Submodule (ZMod 2) V} (hU : ∀ u ∈ U, ∀ w ∈ U, polar Q u w = 0) :
    2 * finrank (ZMod 2) U ≤ finrank (ZMod 2) V := by
  have hle : U ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) U := fun w hw =>
    (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun u hu => by
      show polarBilin Q u w = 0
      rw [polarBilin_apply_apply]
      exact hU u hu w hw
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hQ] at h1
  have h2 := Submodule.finrank_le U
  omega

theorem exists_mem_add_polar_eq_one (hQ : (polarBilin Q).Nondegenerate)
    {U : Submodule (ZMod 2) V} (hU : finrank (ZMod 2) V < 2 * finrank (ZMod 2) U) (c : V) :
    ∃ u ∈ U, Q u + polar Q c u = 1 := by
  by_contra h
  push Not at h
  have h0 : ∀ u ∈ U, Q u = polar Q c u := fun u hu => by
    rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one (Q u + polar Q c u) with h' | h'
    · rw [eq_neg_of_add_eq_zero_left h', ZMod.neg_eq_self_mod_two]
    · exact absurd h' (h u hu)
  have hiso : ∀ u ∈ U, ∀ w ∈ U, polar Q u w = 0 := fun u hu w hw => by
    rw [polar, h0 _ (U.add_mem hu hw), h0 u hu, h0 w hw, polar_add_right]
    ring
  have := two_mul_finrank_le_of_polar_eq_zero hQ hiso
  omega

theorem finrank_ker_polar_add_one (x : V) :
    finrank (ZMod 2) V ≤ finrank (ZMod 2) (LinearMap.ker (polarBilin Q x)) + 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (polarBilin Q x)
  have h1 : finrank (ZMod 2) (LinearMap.range (polarBilin Q x)) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range (polarBilin Q x))
    rwa [Module.finrank_self] at this
  omega

theorem finrank_ker_inf_ker_add_two (x y : V) :
    finrank (ZMod 2) V ≤
      finrank (ZMod 2) (LinearMap.ker (polarBilin Q x) ⊓ LinearMap.ker (polarBilin Q y) :
        Submodule (ZMod 2) V) + 2 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (polarBilin Q x))
    (LinearMap.ker (polarBilin Q y))
  have h1 := finrank_ker_polar_add_one (Q := Q) x
  have h2 := finrank_ker_polar_add_one (Q := Q) y
  have h3 := Submodule.finrank_le (LinearMap.ker (polarBilin Q x) ⊔ LinearMap.ker (polarBilin Q y))
  omega

omit [FiniteDimensional (ZMod 2) V] in
theorem mem_ker_polarBilin {x v : V} : v ∈ LinearMap.ker (polarBilin Q x) ↔ polar Q x v = 0 := by
  rw [LinearMap.mem_ker, polarBilin_apply_apply]

theorem exists_map_eq_one_polar_eq_zero (hQ : (polarBilin Q).Nondegenerate)
    (h3 : 3 ≤ finrank (ZMod 2) V) (w : V) : ∃ b, Q b = 1 ∧ polar Q w b = 0 := by
  have h := finrank_ker_polar_add_one (Q := Q) w
  obtain ⟨u, hu, hu1⟩ := exists_mem_add_polar_eq_one hQ
    (U := LinearMap.ker (polarBilin Q w)) (by omega) 0
  rw [polar_zero_left, add_zero] at hu1
  exact ⟨u, hu1, mem_ker_polarBilin.mp hu⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem exists_polar_eq_one (hQ : (polarBilin Q).Nondegenerate) {w : V} (hw : w ≠ 0) :
    ∃ v, polar Q w v = 1 := by
  by_contra h
  push Not at h
  apply hw
  apply hQ.1 w
  intro v
  rw [polarBilin_apply_apply]
  rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one (polar Q w v) with h' | h'
  · exact h'
  · exact absurd h' (h v)

theorem exists_map_eq_one_polar_eq_one (hQ : (polarBilin Q).Nondegenerate)
    (h3 : 3 ≤ finrank (ZMod 2) V) {w : V} (hw : w ≠ 0) : ∃ a, Q a = 1 ∧ polar Q w a = 1 := by
  obtain ⟨v, hv⟩ := exists_polar_eq_one hQ hw
  rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one (Q v) with hQv | hQv
  · have h := finrank_ker_polar_add_one (Q := Q) w
    obtain ⟨u, hu, hu1⟩ := exists_mem_add_polar_eq_one hQ
      (U := LinearMap.ker (polarBilin Q w)) (by omega) v
    refine ⟨v + u, ?_, ?_⟩
    · rw [QuadraticMap.map_add Q v u, hQv, zero_add, hu1]
    · rw [polar_add_right, hv, mem_ker_polarBilin.mp hu, add_zero]
  · exact ⟨v, hQv, hv⟩

theorem exists_map_eq_one_polar_eq_one_polar_eq_one (hQ : (polarBilin Q).Nondegenerate)
    (h5 : 5 ≤ finrank (ZMod 2) V) {a a' : V} (ha : a ≠ 0) (ha' : a' ≠ 0) :
    ∃ c, Q c = 1 ∧ polar Q a c = 1 ∧ polar Q a' c = 1 := by
  obtain ⟨v, hv, hv'⟩ : ∃ v, polar Q a v = 1 ∧ polar Q a' v = 1 := by
    obtain ⟨v₁, hv₁⟩ := exists_polar_eq_one hQ ha
    obtain ⟨v₂, hv₂⟩ := exists_polar_eq_one hQ ha'
    rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one (polar Q a' v₁) with h1 | h1
    · rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one (polar Q a v₂) with h2 | h2
      · exact ⟨v₁ + v₂, by rw [polar_add_right, hv₁, h2, add_zero],
          by rw [polar_add_right, h1, hv₂, zero_add]⟩
      · exact ⟨v₂, h2, hv₂⟩
    · exact ⟨v₁, hv₁, h1⟩
  have h := finrank_ker_inf_ker_add_two (Q := Q) a a'
  rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one (Q v) with hQv | hQv
  · obtain ⟨u, hu, hu1⟩ := exists_mem_add_polar_eq_one hQ
      (U := LinearMap.ker (polarBilin Q a) ⊓ LinearMap.ker (polarBilin Q a')) (by omega) v
    refine ⟨v + u, ?_, ?_, ?_⟩
    · rw [QuadraticMap.map_add Q v u, hQv, zero_add, hu1]
    · rw [polar_add_right, hv, mem_ker_polarBilin.mp hu.1, add_zero]
    · rw [polar_add_right, hv', mem_ker_polarBilin.mp hu.2, add_zero]
  · exact ⟨v, hQv, hv, hv'⟩

theorem eq_bot_or_eq_top_of_reflect_mul_reflect (hQ : (polarBilin Q).Nondegenerate)
    (h5 : 5 ≤ finrank (ZMod 2) V) {W : Submodule (ZMod 2) V}
    (hW : ∀ a b : V, Q a = 1 → Q b = 1 → ∀ w ∈ W, (reflect Q a * reflect Q b) w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hne : ∀ {a : V}, Q a = 1 → a ≠ 0 := fun ha h0 => by
    rw [h0, QuadraticMap.map_zero] at ha
    exact zero_ne_one ha
  have key : ∀ x ∈ W, ∀ a, Q a = 1 → polar Q x a = 1 → a ∈ W := by
    intro x hx a ha hxa
    obtain ⟨b, hb, hxb⟩ := exists_map_eq_one_polar_eq_zero hQ (by omega) x
    have h := hW a b ha hb x hx
    rw [LinearEquiv.mul_apply, reflect_apply_of_map_eq_one hb, hxb, zero_smul, add_zero,
      reflect_apply_of_map_eq_one ha, hxa, one_smul] at h
    have := W.sub_mem h hx
    rwa [add_sub_cancel_left] at this
  obtain ⟨a₀, ha₀, hwa₀⟩ := exists_map_eq_one_polar_eq_one hQ (by omega) hw0
  have ha₀W := key w hwW a₀ ha₀ hwa₀
  have hns : ∀ a, Q a = 1 → a ∈ W := by
    intro a ha
    obtain ⟨c, hc, hac, hc'⟩ :=
      exists_map_eq_one_polar_eq_one_polar_eq_one hQ h5 (hne ha₀) (hne ha)
    have hcW := key a₀ ha₀W c hc hac
    exact key c hcW a ha (by rw [polar_comm]; exact hc')
  refine eq_top_iff.mpr fun v _ => ?_
  rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one (Q v) with hv | hv
  · obtain ⟨b, hb, hvb⟩ := exists_map_eq_one_polar_eq_zero hQ (by omega) v
    have h1 : Q (v + b) = 1 := by rw [QuadraticMap.map_add Q v b, hv, hb, hvb, zero_add, add_zero]
    have := W.sub_mem (hns _ h1) (hns b hb)
    rwa [add_sub_cancel_right] at this
  · exact hns v hv

end General

@[expose] def qMinusMat : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 1]

@[expose] noncomputable def qMinusForm : QuadraticForm (ZMod 2) (Fin 6 → ZMod 2) :=
  LinearMap.BilinMap.toQuadraticMap (Matrix.toLinearMap₂' (ZMod 2) qMinusMat)

theorem qMinusForm_apply (v : Fin 6 → ZMod 2) : qMinusForm v = qMinus v := by
  simp only [qMinusForm, LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply,
    Fin.sum_univ_succ, Fin.sum_univ_zero, qMinusMat, qMinus, smul_eq_mul]
  simp
  ring

theorem coe_qMinusForm : ⇑qMinusForm = qMinus := funext qMinusForm_apply

@[expose] def polarMinus (u v : Fin 6 → ZMod 2) : ZMod 2 :=
  u 0 * v 1 + u 1 * v 0 + u 2 * v 3 + u 3 * v 2 + u 4 * v 5 + u 5 * v 4

theorem polar_qMinusForm (u v : Fin 6 → ZMod 2) : polar qMinusForm u v = polarMinus u v := by
  rw [polar, qMinusForm_apply, qMinusForm_apply, qMinusForm_apply]
  simp only [qMinus, polarMinus, Pi.add_apply]
  ring_nf
  reduce_mod_char

theorem qMinusForm_nondegenerate : (polarBilin qMinusForm).Nondegenerate := by
  refine LargeExtraspecial.s12_polarBilin_nondegenerate fun u hu => ?_
  have h0 := hu (Pi.single 1 1)
  have h1 := hu (Pi.single 0 1)
  have h2 := hu (Pi.single 3 1)
  have h3 := hu (Pi.single 2 1)
  have h4 := hu (Pi.single 5 1)
  have h5 := hu (Pi.single 4 1)
  simp only [polar_qMinusForm, polarMinus, Pi.single_apply] at h0 h1 h2 h3 h4 h5
  simp at h0 h1 h2 h3 h4 h5
  funext i
  fin_cases i <;> simp_all

theorem finrank_fin_six : finrank (ZMod 2) (Fin 6 → ZMod 2) = 6 := Module.finrank_fin_fun _

theorem timmesfeldOmega_qMinus :
    Open.timmesfeldOmega qMinus = ⁅TauCeti.QuadraticMap.orthogonalGroup qMinusForm,
      TauCeti.QuadraticMap.orthogonalGroup qMinusForm⁆ := by
  rw [← coe_qMinusForm, LargeExtraspecial.s12_timmesfeldOmega_eq qMinusForm
    qMinusForm_nondegenerate,
    CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup
      qMinusForm_nondegenerate (by rw [finrank_fin_six])]

theorem reflect_mul_reflect_mem_timmesfeldOmega {a b : Fin 6 → ZMod 2} (ha : qMinus a = 1)
    (hb : qMinus b = 1) :
    reflect qMinusForm a * reflect qMinusForm b ∈ Open.timmesfeldOmega qMinus := by
  rw [timmesfeldOmega_qMinus]
  exact CFSG.RankThree.Literature.FSmith.reflect_mul_reflect_mem_commutator
    qMinusForm_nondegenerate (by rw [finrank_fin_six]; norm_num)
    (by rw [qMinusForm_apply]; exact ha) (by rw [qMinusForm_apply]; exact hb)

theorem eq_bot_or_eq_top_of_timmesfeldOmega {W : Submodule (ZMod 2) (Fin 6 → ZMod 2)}
    (hW : ∀ g ∈ Open.timmesfeldOmega qMinus, ∀ w ∈ W, g w ∈ W) : W = ⊥ ∨ W = ⊤ :=
  eq_bot_or_eq_top_of_reflect_mul_reflect qMinusForm_nondegenerate
    (by rw [finrank_fin_six]; norm_num) fun a b ha hb w hw =>
      hW _ (reflect_mul_reflect_mem_timmesfeldOmega (by rwa [← qMinusForm_apply])
        (by rwa [← qMinusForm_apply])) w hw

@[expose] def reflMat (a : Fin 6 → ZMod 2) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun i j => (Pi.single j 1 : Fin 6 → ZMod 2) i + polarMinus (Pi.single j 1) a * a i

theorem toMatrix'_reflect {a : Fin 6 → ZMod 2} (ha : qMinus a = 1) :
    LinearMap.toMatrix' (reflect qMinusForm a : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) =
      reflMat a := by
  ext i j
  rw [LinearMap.toMatrix'_apply, LinearEquiv.coe_coe,
    reflect_apply_of_map_eq_one (by rw [qMinusForm_apply]; exact ha), polar_qMinusForm]
  simp [reflMat]

theorem toMatrix'_mul (f g : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) :
    LinearMap.toMatrix' ((f * g : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) :
      (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) =
      LinearMap.toMatrix' (f : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) *
        LinearMap.toMatrix' (g : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) := by
  rw [← LinearMap.toMatrix'_mul]
  rfl

@[expose] def matR1 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0; 1, 1, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0; 1, 0, 0, 0, 0, 1; 1, 0, 0, 0, 1, 0]

@[expose] def matR2 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0; 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1]

@[expose] def matR3 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]

@[expose] def matR4 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 1, 1, 0, 1, 1; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0;
    0, 1, 1, 1, 1, 1; 0, 1, 1, 0, 0, 1; 0, 1, 1, 0, 1, 0]

@[expose] def matR5 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0;
    0, 0, 1, 1, 0, 1; 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1]

@[expose] def matR6 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 1, 1, 1, 1; 1, 0, 1, 1, 1, 1; 1, 1, 0, 1, 1, 1;
    1, 1, 1, 0, 1, 1; 1, 1, 1, 1, 0, 1; 1, 1, 1, 1, 1, 0]

@[expose] def matS22 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 1, 1, 1, 1; 1, 0, 1, 1, 1, 1; 1, 1, 0, 1, 1, 1;
    1, 1, 0, 0, 1, 0; 1, 1, 0, 1, 0, 0; 1, 1, 1, 1, 1, 0]

@[expose] def matS21 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 1, 1, 1, 1; 1, 1, 1, 0, 1, 0; 1, 1, 0, 1, 1, 1;
    1, 1, 0, 0, 1, 0; 1, 0, 0, 0, 0, 1; 1, 0, 1, 0, 1, 1]

@[expose] def matS20 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 1, 1, 1, 0; 1, 1, 1, 0, 1, 0; 1, 1, 0, 1, 1, 1;
    1, 1, 0, 0, 1, 0; 1, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 1]

@[expose] def matS19 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 1, 1, 1, 0; 1, 1, 1, 0, 1, 0; 1, 1, 0, 1, 1, 1;
    1, 0, 1, 1, 1, 0; 1, 0, 1, 1, 0, 0; 1, 0, 1, 0, 1, 1]

@[expose] def matS18 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 1;
    0, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1]

@[expose] def matS17 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 1, 1, 1, 0; 0, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 1;
    0, 0, 1, 1, 1, 0; 0, 0, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1]

@[expose] def matS16 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 1, 1, 1, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0;
    0, 1, 1, 1, 0, 1; 0, 0, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1]

@[expose] def matS15 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 1, 1, 1, 0; 1, 1, 1, 0, 0, 1; 0, 0, 1, 1, 1, 0;
    0, 1, 1, 1, 0, 1; 1, 0, 0, 1, 0, 1; 1, 0, 0, 0, 1, 0]

@[expose] def matS14 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 1, 0, 1, 0, 1; 1, 1, 1, 0, 0, 1; 0, 0, 1, 1, 1, 0;
    0, 1, 1, 1, 0, 1; 1, 1, 1, 1, 1, 0; 1, 0, 0, 0, 1, 0]

@[expose] def matS13 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 1, 0, 1, 0, 1; 1, 1, 1, 0, 0, 1; 0, 1, 1, 1, 0, 1;
    0, 0, 1, 1, 1, 0; 1, 1, 1, 1, 1, 0; 1, 0, 0, 0, 1, 0]

@[expose] def matS12 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 1, 1, 0, 1; 1, 1, 1, 0, 0, 1; 0, 1, 1, 1, 0, 1;
    1, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0; 0, 1, 1, 0, 1, 0]

@[expose] def matS11 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 1, 1, 1, 0; 1, 1, 1, 0, 1, 0; 0, 1, 1, 1, 1, 0;
    1, 1, 0, 1, 0, 1; 0, 0, 0, 1, 0, 1; 0, 1, 1, 0, 0, 1]

@[expose] def matS10 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 1, 1, 1, 0; 1, 1, 1, 0, 1, 0; 0, 1, 1, 1, 1, 0;
    1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 1, 0; 0, 1, 1, 0, 0, 1]

@[expose] def matS9 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 1, 1, 0, 1; 1, 1, 1, 0, 1, 0; 0, 1, 1, 1, 1, 0;
    1, 1, 0, 0, 1, 0; 1, 0, 0, 0, 0, 1; 0, 1, 1, 0, 0, 1]

@[expose] def matS8 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 1, 1, 0, 1; 1, 0, 1, 1, 1, 1; 0, 1, 1, 1, 1, 0;
    1, 1, 0, 0, 1, 0; 1, 1, 0, 1, 0, 0; 0, 0, 1, 1, 0, 0]

@[expose] def matS7 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 1, 1, 0, 1; 1, 0, 1, 1, 1, 1; 0, 1, 1, 1, 1, 0;
    1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0; 0, 0, 1, 1, 0, 0]

@[expose] def matS6 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 1, 1, 0, 1, 1; 1, 1, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0;
    1, 1, 0, 1, 1, 0; 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0]

@[expose] def matS5 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0;
    1, 0, 1, 1, 0, 1; 1, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1]

@[expose] def matS4 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 1; 1, 0, 1, 1, 0, 1;
    0, 0, 1, 0, 0, 0; 1, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1]

@[expose] def matS3 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 1, 0, 0, 0; 1, 1, 1, 0, 0, 1; 1, 0, 1, 1, 0, 1;
    0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1]

@[expose] def matS2 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 1, 0, 0, 0; 1, 1, 0, 0, 1, 1; 1, 0, 1, 1, 0, 1;
    0, 0, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1; 0, 0, 1, 0, 1, 1]

@[expose] def matS1 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 1, 0, 0, 0; 1, 1, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0;
    1, 0, 1, 1, 0, 1; 0, 1, 1, 0, 0, 1; 0, 0, 1, 0, 1, 1]

@[expose] def matS0 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0; 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 0]

@[expose] def matX : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0; 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 0]

theorem exists_eq_commutator_conj :
    ∃ x ∈ Open.timmesfeldOmega qMinus, x ≠ 1 ∧ ∃ α ∈ Open.timmesfeldOmega qMinus,
      ∃ β ∈ Open.timmesfeldOmega qMinus, ⁅α⁻¹ * x * α, β⁻¹ * x * β⁆ = x := by
  have h1 : qMinus ![0, 1, 0, 0, 1, 1] = 1 := by decide
  have h2 : qMinus ![1, 0, 0, 0, 1, 0] = 1 := by decide
  have h3 : qMinus ![0, 0, 1, 1, 0, 0] = 1 := by decide
  have h4 : qMinus ![1, 0, 0, 1, 1, 1] = 1 := by decide
  have h5 : qMinus ![0, 0, 0, 1, 1, 0] = 1 := by decide
  have h6 : qMinus ![1, 1, 1, 1, 1, 1] = 1 := by decide
  have r1 : reflMat ![0, 1, 0, 0, 1, 1] = matR1 := by decide
  have r2 : reflMat ![1, 0, 0, 0, 1, 0] = matR2 := by decide
  have r3 : reflMat ![0, 0, 1, 1, 0, 0] = matR3 := by decide
  have r4 : reflMat ![1, 0, 0, 1, 1, 1] = matR4 := by decide
  have r5 : reflMat ![0, 0, 0, 1, 1, 0] = matR5 := by decide
  have r6 : reflMat ![1, 1, 1, 1, 1, 1] = matR6 := by decide
  have hX : matR1 * matR2 = matX := by decide
  refine ⟨reflect qMinusForm ![0, 1, 0, 0, 1, 1] * reflect qMinusForm ![1, 0, 0, 0, 1, 0],
    reflect_mul_reflect_mem_timmesfeldOmega h1 h2, ?_,
    reflect qMinusForm ![0, 0, 1, 1, 0, 0] * reflect qMinusForm ![1, 0, 0, 1, 1, 1],
    reflect_mul_reflect_mem_timmesfeldOmega h3 h4,
    reflect qMinusForm ![0, 0, 0, 1, 1, 0] * reflect qMinusForm ![1, 1, 1, 1, 1, 1],
    reflect_mul_reflect_mem_timmesfeldOmega h5 h6, ?_⟩
  · intro h
    have h' := congrArg (fun f : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2) =>
      LinearMap.toMatrix' (f : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2))) h
    simp only [toMatrix'_mul, toMatrix'_reflect h1, toMatrix'_reflect h2, r1, r2, hX] at h'
    revert h'
    decide
  · apply LinearEquiv.toLinearMap_injective
    apply LinearMap.toMatrix'.injective
    have key : ∀ a b c d e f : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2),
        ⁅(c * d)⁻¹ * (a * b) * (c * d), (e * f)⁻¹ * (a * b) * (e * f)⁆ =
          d⁻¹ * (c⁻¹ * (a * (b * (c * (d * (f⁻¹ * (e⁻¹ * (a * (b * (e * (f * (d⁻¹ * (c⁻¹ *
            (b⁻¹ * (a⁻¹ * (c * (d * (f⁻¹ * (e⁻¹ * (b⁻¹ * (a⁻¹ * (e *
            f)))))))))))))))))))))) :=
      fun a b c d e f => by simp only [commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc]
    rw [key]
    simp only [reflect_inv, toMatrix'_mul, toMatrix'_reflect h1, toMatrix'_reflect h2,
      toMatrix'_reflect h3, toMatrix'_reflect h4, toMatrix'_reflect h5, toMatrix'_reflect h6]
    rw [r1, r2, r3, r4, r5, r6, hX]
    have s22 : matR5 * matR6 = matS22 := by decide
    have s21 : matR1 * matS22 = matS21 := by decide
    have s20 : matR2 * matS21 = matS20 := by decide
    have s19 : matR5 * matS20 = matS19 := by decide
    have s18 : matR6 * matS19 = matS18 := by decide
    have s17 : matR4 * matS18 = matS17 := by decide
    have s16 : matR3 * matS17 = matS16 := by decide
    have s15 : matR1 * matS16 = matS15 := by decide
    have s14 : matR2 * matS15 = matS14 := by decide
    have s13 : matR3 * matS14 = matS13 := by decide
    have s12 : matR4 * matS13 = matS12 := by decide
    have s11 : matR6 * matS12 = matS11 := by decide
    have s10 : matR5 * matS11 = matS10 := by decide
    have s9 : matR2 * matS10 = matS9 := by decide
    have s8 : matR1 * matS9 = matS8 := by decide
    have s7 : matR5 * matS8 = matS7 := by decide
    have s6 : matR6 * matS7 = matS6 := by decide
    have s5 : matR4 * matS6 = matS5 := by decide
    have s4 : matR3 * matS5 = matS4 := by decide
    have s3 : matR2 * matS4 = matS3 := by decide
    have s2 : matR1 * matS3 = matS2 := by decide
    have s1 : matR3 * matS2 = matS1 := by decide
    have s0 : matR4 * matS1 = matS0 := by decide
    rw [s22, s21, s20, s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5,
      s4, s3, s2, s1, s0]
    decide

theorem mem_derivedSeries_of_eq_commutator_conj {Γ : Type*} [Group Γ] {x α β : Γ}
    (h : ⁅α⁻¹ * x * α, β⁻¹ * x * β⁆ = x) (n : ℕ) : x ∈ derivedSeries Γ n := by
  induction n with
  | zero => exact Subgroup.mem_top x
  | succ n ih =>
    rw [derivedSeries_succ, ← h]
    have hN := derivedSeries_normal Γ n
    refine Subgroup.commutator_mem_commutator ?_ ?_
    · simpa using hN.conj_mem x ih α⁻¹
    · simpa using hN.conj_mem x ih β⁻¹

theorem exists_mem_derivedSeries_ne_one {M : Type*} [Group M]
    (ρ : M →* ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)))
    (hρ : ρ.range = Open.timmesfeldOmega qMinus) (n : ℕ) :
    ∃ k ∈ derivedSeries M n, ρ k ≠ 1 := by
  obtain ⟨x, hx, hx1, α, hα, β, hβ, h⟩ := exists_eq_commutator_conj
  rw [← hρ] at hx hα hβ
  have h' : ⁅(⟨α, hα⟩ : ρ.range)⁻¹ * ⟨x, hx⟩ * ⟨α, hα⟩,
      (⟨β, hβ⟩ : ρ.range)⁻¹ * ⟨x, hx⟩ * ⟨β, hβ⟩⁆ = ⟨x, hx⟩ := Subtype.ext h
  have hmem := mem_derivedSeries_of_eq_commutator_conj h' n
  rw [← map_derivedSeries_eq ρ.rangeRestrict_surjective] at hmem
  obtain ⟨k, hk, hkx⟩ := hmem
  refine ⟨k, hk, fun h1 => hx1 ?_⟩
  have := congrArg Subtype.val hkx
  rw [MonoidHom.coe_rangeRestrict, h1] at this
  exact this.symm

end CFSG.ComponentClassification.AS81.Sec2Omega
