module

public import CFSG.LocalAnalysis.EvenBN.U5.ModelA2N2Two
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3FThree

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem Vsub_inf_centralizer_N₁sub :
    Vsub h ⊓ centralizer (N₁sub h : Set (hypSU h 2 1)) = ⊥ := by
  have := h.charP
  rw [eq_bot_iff]
  rintro v ⟨hv, hvc⟩
  rw [mem_bot, eq_one_iff_Yof_eq_zero h hv]
  have hfix : ∀ A : Matrix (Fin 2) (Fin 2) K, A.det = 1 →
      Yof v = A * Yof v * (A.map h.bar)ᵀ := by
    intro A hA
    have hA' : IsUnit A.det := by rw [hA]; exact isUnit_one
    obtain ⟨-, e⟩ := lev_conj_Yof h A hA' hv
    have hmem : lev (hK := h) A hA' ∈ N₁sub h := by
      have e' : lev (hK := h) A hA' = UnitaryHigher.leviSU h 1 ⟨A, hA⟩ :=
        lev_eq_leviSU ⟨A, hA⟩ hA'
      rw [e']
      exact ⟨_, rfl⟩
    have hcomm := mem_centralizer_iff.1 hvc _ hmem
    rwa [hcomm, mul_inv_cancel_right] at e
  set Y := Yof v with hY
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  have e1 := hfix !![1, 1; 0, 1] (by simp [det_fin_two])
  have e2 := hfix !![1, c; 0, 1] (by simp [det_fin_two])
  have e3 := hfix !![1, 0; 1, 1] (by simp [det_fin_two])
  have a01 := congrFun (congrFun e1 0) 1
  have a00 := congrFun (congrFun e1 0) 0
  have b00 := congrFun (congrFun e2 0) 0
  have c11 := congrFun (congrFun e3 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at a01 a00 b00 c11
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hY10 : Y 1 0 = Y 0 1 := by linear_combination -a00 - a01 - Y 0 1 * h2
  have hne : c + h.bar c ≠ 0 := fun e => hc (by linear_combination e - c * h2)
  have hm : Y 0 1 * (c + h.bar c) = 0 := by
    linear_combination -b00 - c * hY10 - c * h.bar c * a01
  have hY01 : Y 0 1 = 0 := (mul_eq_zero.1 hm).resolve_right hne
  have hY00 : Y 0 0 = 0 := by linear_combination -c11 - hY10 - 2 * hY01
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using hY00
  · simpa using hY01
  · simpa [hY01] using hY10
  · simpa using a01

section Commutator

variable {G' : Type*} [Group G']

omit [Field K] in
theorem commutatorElement_mul_mul_of_commute {y y' z z' : G'} (h1 : Commute z y')
    (h2 : Commute z z') (h3 : Commute z' y) :
    ⁅y * z, y' * z'⁆ = ⁅y, y'⁆ := by
  have e1 : z * y' * z' * z⁻¹ = y' * z' := by
    calc z * y' * z' * z⁻¹ = y' * (z * z') * z⁻¹ := by rw [h1.eq]; group
      _ = y' * (z' * z) * z⁻¹ := by rw [h2.eq]
      _ = y' * z' := by group
  have e2 : z' * y⁻¹ * z'⁻¹ = y⁻¹ := by
    rw [(h3.inv_right).eq, mul_inv_cancel_right]
  calc ⁅y * z, y' * z'⁆ = y * (z * y' * z' * z⁻¹) * y⁻¹ * z'⁻¹ * y'⁻¹ := by
        rw [commutatorElement_def]
        group
    _ = y * y' * (z' * y⁻¹ * z'⁻¹) * y'⁻¹ := by rw [e1]; group
    _ = ⁅y, y'⁆ := by rw [e2, commutatorElement_def]

end Commutator

theorem commutator_A₂sub_Isub_inf_N₂sub : ⁅A₂sub h, Isub h ⊓ N₂sub h⁆ = A₂sub h := by
  have := h.charP
  have := finite_hypSU (hK := h)
  set Y := ⁅A₂sub h, Isub h ⊓ N₂sub h⁆ with hY
  have hnorm : ∀ j ∈ Isub h ⊓ N₂sub h, j ∈ normalizer (A₂sub h : Set (hypSU h 2 1)) :=
    fun j hj => N₂sub_sup_Isub_le_normalizer_A₂sub (mem_sup_right (Subgroup.mem_inf.1 hj).1)
  have hYA : Y ≤ A₂sub h := commutator_le.2 fun a ha j hj => by
    have h1 : j * a⁻¹ * j⁻¹ ∈ A₂sub h := (mem_normalizer_iff.1 (hnorm j hj) a⁻¹).1 (inv_mem ha)
    rw [show ⁅a, j⁆ = a * (j * a⁻¹ * j⁻¹) by rw [commutatorElement_def]; group]
    exact mul_mem ha h1
  obtain ⟨a, ha⟩ := h.exists_bar_ne
  have ha0 : a ≠ 0 := fun e => ha (by rw [e, map_zero])
  have ha1 : a ≠ 1 := fun e => ha (by rw [e, map_one])
  obtain ⟨τ, hτN, hτI, hτ⟩ := exists_torus_N₂sub h ha0
  have hτJ : τ ∈ Isub h ⊓ N₂sub h := Subgroup.mem_inf.2 ⟨hτI, hτN⟩
  have key : ∀ x ∈ A₂sub h, x⁻¹ * (τ * x * τ⁻¹) ∈ Y ∧
      mat (x⁻¹ * (τ * x * τ⁻¹)) ιe₁ ιe₂ = mat x ιe₁ ιe₂ * (1 + a⁻¹) ∧
      mat (x⁻¹ * (τ * x * τ⁻¹)) ιe₁ ιz = mat x ιe₁ ιz * (1 + (h.bar a / a)⁻¹) ∧
      mat (x⁻¹ * (τ * x * τ⁻¹)) ιe₁ ιf₂ = mat x ιe₁ ιf₂ * (1 + h.bar a) := by
    intro x hx
    obtain ⟨hxA, t1, t2, t3⟩ := hτ x hx
    obtain ⟨m1, m2, m3⟩ := A₂_inv_mul hx hxA
    refine ⟨?_, by rw [m1, t1]; ring, by rw [m2, t2]; ring, by rw [m3, t3]; ring⟩
    have := commutator_mem_commutator (inv_mem hx) hτJ
    rw [commutatorElement_def, inv_inv] at this
    simpa only [mul_assoc] using this
  have hne1 : (1 : K) + a⁻¹ ≠ 0 := fun e => ha1 (by
    have : a⁻¹ = 1 := by linear_combination e - CharTwo.two_eq_zero (R := K) * 1
    rwa [inv_eq_one] at this)
  have hne2 : (1 : K) + (h.bar a / a)⁻¹ ≠ 0 := fun e => ha (by
    have h3 : (h.bar a / a)⁻¹ = 1 := by linear_combination e - CharTwo.two_eq_zero (R := K) * 1
    rw [inv_eq_one, div_eq_one_iff_eq ha0] at h3
    exact h3)
  have hne3 : (1 : K) + h.bar a ≠ 0 := fun e => ha1 (by
    have h3 : h.bar a = 1 := by linear_combination e - CharTwo.two_eq_zero (R := K) * 1
    have := congrArg h.bar h3
    rwa [h.bar_bar, map_one] at this)
  have hYZ : Y ⊔ ZPsub h = A₂sub h := by
    refine eq_A₂sub_of_coords le_sup_right (sup_le hYA (ZPsub_le_Z₂Psub.trans Z₂Psub_le_A₂sub))
      (fun b => ?_) (fun b => ?_) (fun b => ?_)
    · obtain ⟨x, hx, x1, x2, x3⟩ := exists_A₂sub_coord h (b / (1 + a⁻¹)) 0 0
      obtain ⟨hy, y1, y2, y3⟩ := key x hx
      exact ⟨_, mem_sup_left hy, by rw [y1, x1, div_mul_cancel₀ _ hne1], by rw [y2, x2, zero_mul],
        by rw [y3, x3, zero_mul]⟩
    · obtain ⟨x, hx, x1, x2, x3⟩ := exists_A₂sub_coord h 0 (b / (1 + (h.bar a / a)⁻¹)) 0
      obtain ⟨hy, y1, y2, y3⟩ := key x hx
      exact ⟨_, mem_sup_left hy, by rw [y1, x1, zero_mul], by rw [y2, x2, div_mul_cancel₀ _ hne2],
        by rw [y3, x3, zero_mul]⟩
    · obtain ⟨x, hx, x1, x2, x3⟩ := exists_A₂sub_coord h 0 0 (b / (1 + h.bar a))
      obtain ⟨hy, y1, y2, y3⟩ := key x hx
      exact ⟨_, mem_sup_left hy, by rw [y1, x1, zero_mul], by rw [y2, x2, zero_mul],
        by rw [y3, x3, div_mul_cancel₀ _ hne3]⟩
  have hZY : ZPsub h ≤ Y := by
    refine ZPsub_le_commutator_A₂sub.trans ?_
    rw [← hYZ]
    refine commutator_le.2 fun u hu v hv => ?_
    have hZn : ZPsub h ≤ normalizer (Y : Set (hypSU h 2 1)) := fun z hz =>
      mem_normalizer_fintype fun y hy => by
        rw [ZPsub_commute hz (A₂sub_le_U (hYA hy)), mul_inv_cancel_right]
        exact hy
    obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hZn hu
    obtain ⟨y', hy', z', hz', rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hZn hv
    rw [commutatorElement_mul_mul_of_commute (ZPsub_commute hz (A₂sub_le_U (hYA hy')))
      (ZPsub_commute hz (ZPsub_le_U hz')) (ZPsub_commute hz' (A₂sub_le_U (hYA hy)))]
    exact commutator_mem_commutator hy hy' |> fun h' => commutator_le_self' Y h'
  exact le_antisymm hYA (by rw [← hYZ]; exact sup_le le_rfl hZY)

namespace Data

variable {G : Type} [Group G] (d : Data G h)

theorem A₁_inf_centralizer_N₁ : d.A₁ ⊓ centralizer (d.N₁ : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨v, hv, rfl⟩, hc⟩
  have hvU : v ∈ hypUnitriangular h 2 1 := Ssub_le_Usub (Vsub_le_Ssub hv)
  have hvc : v ∈ Vsub h ⊓ centralizer (N₁sub h : Set (hypSU h 2 1)) := by
    refine Subgroup.mem_inf.2 ⟨hv, mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨B, rfl⟩
    have hB : IsUnit (B : Matrix (Fin 2) (Fin 2) K).det := by
      rw [Matrix.SpecialLinearGroup.det_coe]
      exact isUnit_one
    have hlev := lev_eq_leviSU (h := h) B hB
    rw [← hlev]
    obtain ⟨hmem, -⟩ := lev_conj_Yof h _ hB hv
    have hmemN : d.η (lev (hK := h) (B : Matrix (Fin 2) (Fin 2) K) hB) ∈ d.N₁ :=
      ⟨_, hlev ▸ ⟨B, rfl⟩, rfl⟩
    have e : d.η (lev (hK := h) (B : Matrix (Fin 2) (Fin 2) K) hB * v *
        (lev (hK := h) (B : Matrix (Fin 2) (Fin 2) K) hB)⁻¹) = d.η v := by
      rw [map_mul, map_mul, map_inv, mem_centralizer_iff.1 hc _ hmemN, mul_inv_cancel_right]
    have e2 := d.η_injOn (Ssub_le_Usub (Vsub_le_Ssub hmem)) hvU e
    calc lev (hK := h) (B : Matrix (Fin 2) (Fin 2) K) hB * v =
        (lev (hK := h) (B : Matrix (Fin 2) (Fin 2) K) hB * v *
          (lev (hK := h) (B : Matrix (Fin 2) (Fin 2) K) hB)⁻¹) *
          lev (hK := h) (B : Matrix (Fin 2) (Fin 2) K) hB := by group
      _ = v * lev (hK := h) (B : Matrix (Fin 2) (Fin 2) K) hB := by rw [e2]
  rw [Vsub_inf_centralizer_N₁sub, mem_bot] at hvc
  rw [hvc, map_one]
  exact one_mem _

theorem commutator_A₂_I_inf_N₂ : ⁅d.A₂, d.I ⊓ d.N₂⁆ = d.A₂ := by
  have e : d.I ⊓ d.N₂ = d.pull (Isub h ⊓ N₂sub h) :=
    (d.pull_inf_of_scalars_le hypScalars_le_Isub).symm
  rw [e, Data.A₂, pull, pull, ← Subgroup.map_commutator, commutator_A₂sub_Isub_inf_N₂sub]

variable [Finite G] {d}

theorem Hyp.F_inf_centralizer_N₁ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.F ⊓ centralizer (d.N₁ : Set G) = ⊥ := by
  obtain ⟨ψ, -, -, hψ, -⟩ := hd.exists_crossedHom_F hGMS
  rw [eq_bot_iff]
  rintro x ⟨hxF, hxc⟩
  have hcr : x⁻¹ * d.t * x * d.t ∈ d.A₁ ⊓ centralizer (d.N₁ : Set G) := by
    refine Subgroup.mem_inf.2 ⟨?_, mem_centralizer_iff.2 fun n hn => ?_⟩
    · rw [← hψ ⟨x, hxF⟩]
      exact (ψ ⟨x, hxF⟩).2
    · have hnx : Commute n x := mem_centralizer_iff.1 hxc n hn
      have hnt : Commute n d.t := mem_centralizer_singleton_iff.1 (hd.N₁_le hn).2
      exact ((hnx.inv_right.mul_right hnt).mul_right hnx).mul_right hnt
  rw [d.A₁_inf_centralizer_N₁, mem_bot] at hcr
  have e1 : d.t * x * d.t = x := by
    calc d.t * x * d.t = x * (x⁻¹ * d.t * x * d.t) := by group
      _ = x := by rw [hcr, mul_one]
  have hxt : x ∈ d.F ⊓ centralizer ({d.t} : Set G) := by
    refine Subgroup.mem_inf.2 ⟨hxF, mem_centralizer_singleton_iff.2 ?_⟩
    calc x * d.t = (d.t * x * d.t) * d.t := by rw [e1]
      _ = d.t * x * (d.t * d.t) := by group
      _ = d.t * x := by rw [hd.t_mul_t, mul_one]
  rw [hd.F_inf_centralizer_t hGMS] at hxt
  have : x ∈ d.A₁ ⊓ centralizer (d.N₁ : Set G) := Subgroup.mem_inf.2 ⟨hxt, hxc⟩
  rwa [d.A₁_inf_centralizer_N₁] at this

end Data

end CFSG.LocalAnalysis.EvenBN.U5
