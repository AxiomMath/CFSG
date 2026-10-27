module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95LinBlocks
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95LinGlue
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95LinCore
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Z

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
open CFSG.ComponentClassification.CatalogueBGeneralLinear (specialLinear_quasisimple specialLinear_perfect
  generalLinear_small_solvable)
open CFSG.LocalAnalysis.ComponentInitial (finite_odd_field_two_squares sl2_exists_anticommuting_pair)
open scoped MatrixGroups commutatorElement Matrix

section Contradictions

variable {k : Type} [Field k] {m : ℕ} {J : Type} [Group J] {π : SL(m, k) →* J}

theorem ivk95l_false_big [Finite k] (hπ : IsCentralQuot π) {g : SL(m, k)}
    (hU : ∀ v ∈ Ez (π g), v * v = 1 → v = 1 ∨ v = π g) (h2 : (2 : k) ≠ 0) {d : ℕ} (hd : 3 ≤ d)
    (ξ : SL(d, k) →* SL(m, k)) (hcomm : ∀ x, ξ x * g = g * ξ x)
    (hnorm : ∀ n : SL(m, k), n * g = g * n → ∀ x, ∃ x', n * ξ x * n⁻¹ = ξ x')
    (hcen : ∀ x, ξ x ∈ Subgroup.center SL(m, k) → x = 1) : False := by
  obtain ⟨u, v, hu2, hv2, hu1, hv1, huv⟩ := ivk95l_two_involutions h2 hd
  have hqs : CFSG.IsQuasisimple SL(d, k) :=
    specialLinear_quasisimple d k (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  have hπξ1 : ∀ x, π (ξ x) = 1 → x = 1 := fun x hx => hcen x ((hπ.ker_eq _).1 hx)
  have hE := hπ.range_le_Ez hqs ξ hcomm hnorm ⟨u, fun h => hu1 (hπξ1 u h)⟩
  have key : ∀ w : SL(d, k), w * w = 1 → w ≠ 1 → π (ξ w) = π g := by
    intro w hw2 hw1
    have hsq : π (ξ w) * π (ξ w) = 1 := by rw [← map_mul, ← map_mul, hw2, map_one, map_one]
    rcases hU _ (hE w) hsq with h | h
    · exact absurd (hπξ1 w h) hw1
    · exact h
  have heq := (key u hu2 hu1).trans (key v hv2 hv1).symm
  apply huv
  have h3 : π (ξ (u⁻¹ * v)) = 1 := by
    rw [map_mul, map_mul, map_inv, map_inv, heq, inv_mul_cancel]
  exact inv_mul_eq_one.1 (hπξ1 _ h3)

theorem ivk95l_false_pair [Finite k] (hπ : IsCentralQuot π) {g : SL(m, k)}
    (hU : ∀ v ∈ Ez (π g), v * v = 1 → v = 1 ∨ v = π g) (h2 : (2 : k) ≠ 0) (hk : 4 ≤ Nat.card k)
    (ξ₁ ξ₂ : SL(2, k) →* SL(m, k))
    (h1 : (∀ x, ξ₁ x * g = g * ξ₁ x) ∧
      (∀ n : SL(m, k), n * g = g * n → ∀ x, ∃ x', n * ξ₁ x * n⁻¹ = ξ₁ x') ∧
      (∀ x, ξ₁ x ∈ Subgroup.center SL(m, k) → x = 1))
    (h2' : (∀ x, ξ₂ x * g = g * ξ₂ x) ∧
      (∀ n : SL(m, k), n * g = g * n → ∀ x, ∃ x', n * ξ₂ x * n⁻¹ = ξ₂ x') ∧
      (∀ x, ξ₂ x ∈ Subgroup.center SL(m, k) → x = 1))
    (hcomm : ∀ x y, ξ₁ x * ξ₂ y = ξ₂ y * ξ₁ x)
    (hscal : ∀ (c : kˣ) (u v : SL(2, k)), Matrix.SpecialLinearGroup.toGL u =
      Matrix.GeneralLinearGroup.scalar (Fin 2) c → Matrix.SpecialLinearGroup.toGL v =
      Matrix.GeneralLinearGroup.scalar (Fin 2) c → ξ₁ u * ξ₂ v ∈ Subgroup.center SL(m, k))
    (hind : ∀ x y, ξ₁ x * ξ₂ y ∈ Subgroup.center SL(m, k) →
      ∃ c : kˣ, Matrix.SpecialLinearGroup.toGL x = Matrix.GeneralLinearGroup.scalar (Fin 2) c) :
    False := by
  obtain ⟨w, hw2, hwc⟩ := ivk95l_order_four (k := k)
  have hqs : CFSG.IsQuasisimple SL(2, k) :=
    specialLinear_quasisimple 2 k le_rfl (Or.inr (by omega)) (Or.inr (by omega))
  have hw1 : w ≠ 1 := fun h => hwc (h ▸ Subgroup.one_mem _)
  have hπ1 : ∀ x, π (ξ₁ x) = 1 → x = 1 := fun x hx => h1.2.2 x ((hπ.ker_eq _).1 hx)
  have hπ2 : ∀ y, π (ξ₂ y) = 1 → y = 1 := fun y hy => h2'.2.2 y ((hπ.ker_eq _).1 hy)
  have hE1 := hπ.range_le_Ez hqs ξ₁ h1.1 h1.2.1 ⟨w, fun h => hw1 (hπ1 w h)⟩
  have hE2 := hπ.range_le_Ez hqs ξ₂ h2'.1 h2'.2.1 ⟨w, fun h => hw1 (hπ2 w h)⟩
  have hm1 : (-1 : SL(2, k)) ≠ 1 := ivk95l_neg_one_ne_one h2
  have hwinv : w⁻¹ * w⁻¹ = -1 := by
    have : (-1 : SL(2, k)) * (-1) = 1 := by
      apply Subtype.ext
      change (-1 : Matrix (Fin 2) (Fin 2) k) * (-1) = 1
      simp
    rw [← mul_inv_rev, hw2]
    exact inv_eq_of_mul_eq_one_right this
  have hsq : ∀ v : SL(2, k), v * v = -1 → π (ξ₁ w * ξ₂ v) * π (ξ₁ w * ξ₂ v) = 1 := by
    intro v hv
    rw [← map_mul]
    refine (hπ.ker_eq _).2 ?_
    have : ξ₁ w * ξ₂ v * (ξ₁ w * ξ₂ v) = ξ₁ (-1) * ξ₂ (-1) := by
      calc ξ₁ w * ξ₂ v * (ξ₁ w * ξ₂ v) = ξ₁ w * (ξ₂ v * ξ₁ w) * ξ₂ v := by group
        _ = ξ₁ w * (ξ₁ w * ξ₂ v) * ξ₂ v := by rw [hcomm w v]
        _ = ξ₁ (w * w) * ξ₂ (v * v) := by simp only [map_mul]; group
        _ = ξ₁ (-1) * ξ₂ (-1) := by rw [hw2, hv]
    rw [this]
    exact hscal (-1) (-1) (-1) ivk95l_toGL_neg_one ivk95l_toGL_neg_one
  have hne : ∀ v : SL(2, k), π (ξ₁ w * ξ₂ v) ≠ 1 := by
    intro v h
    obtain ⟨c, hc⟩ := hind w v ((hπ.ker_eq _).1 h)
    exact hwc (ivk95l_mem_center_of_scalar hc)
  have hmem : ∀ v : SL(2, k), π (ξ₁ w * ξ₂ v) ∈ Ez (π g) := fun v => by
    rw [map_mul]
    exact (Ez (π g)).mul_mem (hE1 w) (hE2 v)
  have e1 : π (ξ₁ w * ξ₂ w) = π g := by
    rcases hU _ (hmem w) (hsq w hw2) with h | h
    · exact absurd h (hne w)
    · exact h
  have e2 : π (ξ₁ w * ξ₂ w⁻¹) = π g := by
    rcases hU _ (hmem w⁻¹) (hsq w⁻¹ hwinv) with h | h
    · exact absurd h (hne w⁻¹)
    · exact h
  have e3 : π (ξ₂ w) = π (ξ₂ w⁻¹) := by
    have := e1.trans e2.symm
    rw [map_mul, map_mul] at this
    exact mul_left_cancel this
  have e4 : π (ξ₂ (-1)) = 1 := by
    have : ξ₂ (-1) = (ξ₂ w)⁻¹ * ξ₂ w⁻¹ := by
      rw [← map_inv, ← map_mul, ← hwinv]
    rw [this, map_mul, map_inv, e3, inv_mul_cancel]
  exact hm1 (hπ2 _ e4)

theorem ivk95l_centralizer_solvable [Finite k] (hk : Nat.card k = 3) {a b : ℕ} (ha : a = 2) (hb : b = 2)
    {g : SL(m, k)} (Θ : Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k)) ≃*
      GL (Fin a) k × GL (Fin b) k) :
    Group.IsSolvable ↥(Subgroup.centralizer ({g} : Set SL(m, k))) := by
  let fN : ↥(Subgroup.centralizer ({g} : Set SL(m, k))) →*
      ↥(Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))) :=
    { toFun := fun n => ⟨Matrix.SpecialLinearGroup.toGL (n : SL(m, k)), by
        rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
        exact congrArg _ (Subgroup.mem_centralizer_singleton_iff.1 n.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  have hfN : Function.Injective fN := fun x y h =>
    Subtype.ext (Matrix.SpecialLinearGroup.toGL_injective (congrArg Subtype.val h))
  have hsa : Group.IsSolvable (GL (Fin a) k) :=
    generalLinear_small_solvable a k (Or.inr ⟨ha, Or.inr hk⟩)
  have hsb : Group.IsSolvable (GL (Fin b) k) :=
    generalLinear_small_solvable b k (Or.inr ⟨hb, Or.inr hk⟩)
  exact Group.isSolvable_of_isSolvable_injective (f := Θ.toMonoidHom.comp fN)
    (Θ.injective.comp hfN)

theorem ivk95l_false_quad [Finite k] {E : Type} [Field E] [Algebra k E] [Finite E]
    (hπ : IsCentralQuot π) {g : SL(m, k)} (hU : ∀ v ∈ Ez (π g), v * v = 1 → v = 1 ∨ v = π g)
    (h2E : (2 : E) ≠ 0) (hE : 4 ≤ Nat.card E) (ξ : SL(2, E) →* SL(m, k))
    (hcomm : ∀ x, ξ x * g = g * ξ x)
    (hnorm : ∀ n : SL(m, k), n * g = g * n → ∀ x, ∃ x', n * ξ x * n⁻¹ = ξ x')
    (hcen : ∀ x, ξ x ∈ Subgroup.center SL(m, k) → x ∈ Subgroup.center SL(2, E))
    (hscal : ∀ (c : kˣ) (x : SL(2, E)), Matrix.SpecialLinearGroup.toGL x =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap k E).toMonoidHom c) →
      ξ x ∈ Subgroup.center SL(m, k)) : False := by
  have hrc : ringChar E ≠ 2 := by
    intro h
    apply h2E
    have : CharP E 2 := h ▸ ringChar.charP E
    exact CharTwo.two_eq_zero
  obtain ⟨a, b, hab⟩ := finite_odd_field_two_squares hrc (-1 : E)
  obtain ⟨x₁, y₁, -, -, hx2, hy2, hxy⟩ := sl2_exists_anticommuting_pair hab
  have hm1 : (-1 : SL(2, E)) ≠ 1 := ivk95l_neg_one_ne_one h2E
  have hnc : x₁ * y₁ ≠ y₁ * x₁ := by
    intro h
    rw [h] at hxy
    apply hm1
    have h1 : (-1 : SL(2, E)) * (y₁ * x₁) = 1 * (y₁ * x₁) := by rw [one_mul]; exact hxy.symm
    exact mul_right_cancel h1
  have hx1c : x₁ ∉ Subgroup.center SL(2, E) := fun h =>
    hnc (Subgroup.mem_center_iff.1 h y₁).symm
  have hy1c : y₁ ∉ Subgroup.center SL(2, E) := fun h =>
    hnc (Subgroup.mem_center_iff.1 h x₁)
  have hqs : CFSG.IsQuasisimple SL(2, E) :=
    specialLinear_quasisimple 2 E le_rfl (Or.inr (by omega)) (Or.inr (by omega))
  have hπ1 : ∀ x, π (ξ x) = 1 → x ∈ Subgroup.center SL(2, E) := fun x hx =>
    hcen x ((hπ.ker_eq _).1 hx)
  have hE1 := hπ.range_le_Ez hqs ξ hcomm hnorm ⟨x₁, fun h => hx1c (hπ1 x₁ h)⟩
  have hm1E : Matrix.SpecialLinearGroup.toGL (-1 : SL(2, E)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap k E).toMonoidHom (-1 : kˣ)) := by
    apply Units.ext
    simp only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, Matrix.GeneralLinearGroup.coe_scalar, Units.coe_map,
      Units.val_neg, Units.val_one]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  have hneg : π (ξ (-1)) = 1 := (hπ.ker_eq _).2 (hscal (-1) (-1) hm1E)
  have key : ∀ w : SL(2, E), w * w = -1 → w ∉ Subgroup.center SL(2, E) → π (ξ w) = π g := by
    intro w hw hwc
    have hsq : π (ξ w) * π (ξ w) = 1 := by rw [← map_mul, ← map_mul, hw, hneg]
    rcases hU _ (hE1 w) hsq with h | h
    · exact absurd (hπ1 w h) hwc
    · exact h
  have hx1 := key x₁ (by simpa [sq] using hx2) hx1c
  have hy1 := key y₁ (by simpa [sq] using hy2) hy1c
  have h3 : π (ξ (x₁⁻¹ * y₁)) = 1 := by
    rw [map_mul, map_mul, map_inv, map_inv, hx1, hy1, inv_mul_cancel]
  have h4 := hπ1 _ h3
  apply hnc
  have h5 := Subgroup.mem_center_iff.1 h4 x₁
  have h6 : y₁ = x₁⁻¹ * y₁ * x₁ := by
    calc y₁ = x₁ * (x₁⁻¹ * y₁) := by group
      _ = x₁⁻¹ * y₁ * x₁ := h5
  calc x₁ * y₁ = x₁ * (x₁⁻¹ * y₁ * x₁) := by rw [← h6]
    _ = y₁ * x₁ := by group

theorem ivk95l_main [Finite k] (hm : m = 4 ∨ m = 5) (hkodd : Odd (Nat.card k)) [Finite J]
    (hπ : IsCentralQuot π) {z : J} (hz : orderOf z = 2)
    (hU : ∀ v ∈ Ez z, v * v = 1 → v = 1 ∨ v = z) (hKperf : ⁅Ez z, Ez z⁆ = Ez z) (hKne : Ez z ≠ ⊥) :
    False := by
  have hm0 : 0 < m := by omega
  have h2 : (2 : k) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hkodd
  have hk3 : 3 ≤ Nat.card k := by
    have := Nat.succ_le_iff.2 (Finite.one_lt_card (α := k))
    obtain ⟨t, ht⟩ := hkodd
    omega
  obtain ⟨g, hg, hgc, hg2⟩ := hπ.lift_involution hz
  subst hg
  obtain ⟨μ, hμ⟩ := ivk95l_center_scalar hm0 hg2
  have hT2 : (Matrix.SpecialLinearGroup.toGL g) ^ 2 = Matrix.GeneralLinearGroup.scalar (Fin m) μ := by
    rw [← map_pow]; exact hμ
  have hns : ∀ c : kˣ, Matrix.SpecialLinearGroup.toGL g ≠ Matrix.GeneralLinearGroup.scalar (Fin m) c :=
    fun c hc => hgc (ivk95l_mem_center_of_scalar hc)
  by_cases hsq : IsSquare (μ : k)
  · obtain ⟨c₀', hc₀'⟩ := hsq
    have hc00 : c₀' ≠ 0 := fun h => μ.ne_zero (by rw [hc₀', h, mul_zero])
    let c₀ : kˣ := Units.mk0 c₀' hc00
    have hsq' : (Matrix.SpecialLinearGroup.toGL g) ^ 2 =
        Matrix.GeneralLinearGroup.scalar (Fin m) (c₀ ^ 2) := by
      rw [hT2]
      congr 1
      apply Units.ext
      simp [c₀, hc₀', sq]
    obtain ⟨a, b, hab, ha, hb, Θ, hΘ⟩ := ivk95l_split h2 hm0 hsq' hns
    have hperf : ∀ n : ℕ, 3 ≤ n → Group.IsPerfect SL(n, k) := fun n hn =>
      specialLinear_perfect n k (by omega) (Or.inl (by omega)) (Or.inl (by omega))
    by_cases ha3 : 3 ≤ a
    · obtain ⟨ξ, -, hξ1, hξ2, hξ3⟩ := ivk95l_block_fst hb Θ hΘ (hperf a ha3) hm0
      exact ivk95l_false_big hπ hU h2 ha3 ξ hξ1 hξ2 hξ3
    by_cases hb3 : 3 ≤ b
    · let Θ' := Θ.trans MulEquiv.prodComm
      have hΘ' : ∀ (c : kˣ) (hc : Matrix.GeneralLinearGroup.scalar (Fin m) c ∈
            Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL g} : Set (GL (Fin m) k))),
          Θ' ⟨Matrix.GeneralLinearGroup.scalar (Fin m) c, hc⟩ =
            (Matrix.GeneralLinearGroup.scalar (Fin b) c, Matrix.GeneralLinearGroup.scalar (Fin a) c) := by
        intro c hc
        show Prod.swap (Θ ⟨Matrix.GeneralLinearGroup.scalar (Fin m) c, hc⟩) = _
        rw [hΘ c hc]
        rfl
      obtain ⟨ξ, -, hξ1, hξ2, hξ3⟩ := ivk95l_block_fst ha Θ' hΘ' (hperf b hb3) hm0
      exact ivk95l_false_big hπ hU h2 hb3 ξ hξ1 hξ2 hξ3
    have ha2 : a = 2 := by omega
    have hb2 : b = 2 := by omega
    subst ha2 hb2
    by_cases hk4 : 4 ≤ Nat.card k
    · have hp2 : Group.IsPerfect SL(2, k) :=
        specialLinear_perfect 2 k le_rfl (Or.inr (by omega)) (Or.inr (by omega))
      obtain ⟨ξ₁, ξ₂, h1, h2', hcomm, hscal, hind⟩ :=
        ivk95l_block_pair ha hb Θ hΘ hp2 hp2 hm0
      exact ivk95l_false_pair hπ hU h2 hk4 ξ₁ ξ₂ h1 h2' hcomm hscal hind
    · have hk3' : Nat.card k = 3 := by omega
      exact ivk95l_false_solvable hπ (Ez_le_centralizer (π g)) hKperf hKne
        (ivk95l_centralizer_solvable hk3' rfl rfl Θ)
  · have : Fact (¬ IsSquare (μ : k)) := ⟨hsq⟩
    obtain ⟨E, hEf, hEfin, hEalg, d, hmd, hcard, Θ, hΘ⟩ := ivk95l_quad hsq hT2
    have hd2 : d = 2 := by omega
    subst hd2
    have hE4 : 4 ≤ Nat.card E := by rw [hcard]; nlinarith
    have h2E : (2 : E) ≠ 0 := by
      intro h
      apply h2
      apply (algebraMap k E).injective
      rw [map_ofNat, map_zero]
      exact h
    have hp2 : Group.IsPerfect SL(2, E) :=
      specialLinear_perfect 2 E le_rfl (Or.inr (by omega)) (Or.inr (by omega))
    obtain ⟨ξ, hξ1, hξ2, hξ3, hξ4⟩ := ivk95l_block_quad Θ hΘ hp2 hm0
    exact ivk95l_false_quad hπ hU h2E hE4 ξ hξ1 hξ2 hξ3 hξ4

end Contradictions

end CFSG.GH74.GLS.IVK.Proofs2
