module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8GapE3
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8GapMat

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup
open scoped Matrix

namespace Sec8

open Sec7

namespace MB

@[expose] def inE0 (x : MB) : Bool := !bit x 0 && !bit x 1 && !bit x 2 && !bit x 3 && !bit x 6

@[expose] def inQ0 (x : MB) : Bool := !bit x 1 && !bit x 3 && !bit x 6

theorem inE0_coord_aux : ∀ x y w : ZMod 4, (2 * x = 0 ∧ 2 * y = 0 ∧ 2 * w = 0) →
    inE0 (coord ![x, y, w]) = true := by
  decide +kernel

theorem coord_of_inE0 : ∀ x : MB, inE0 x = true →
    ∃ a b c : ZMod 4, 2 * a = 0 ∧ 2 * b = 0 ∧ 2 * c = 0 ∧ coord ![a, b, c] = x := by
  decide +kernel

theorem E0_span : ∀ x : MB, inE0 x = true → InSpan [z, y, k] x := by
  decide +kernel

theorem inQ0_coord_aux : ∀ x y w : ZMod 4, inQ0 (coord ![x, y, w]) = true → 2 * w = 0 := by
  decide +kernel

@[expose] def E0h : Subgroup MB := ofPred inE0 (by decide +kernel) (by decide +kernel)
  (by decide +kernel)

@[expose] def Q0h : Subgroup MB := ofPred inQ0 (by decide +kernel) (by decide +kernel)
  (by decide +kernel)

theorem z_mem_E0h : z ∈ E0h := (by decide +kernel : inE0 z = true)
theorem y_mem_E0h : y ∈ E0h := (by decide +kernel : inE0 y = true)
theorem k_mem_E0h : k ∈ E0h := (by decide +kernel : inE0 k = true)
theorem E0h_le_Q0h : E0h ≤ Q0h := fun x (hx : inE0 x = true) => by
  change inQ0 x = true
  revert x; decide +kernel
theorem Q0h_le_QC : Q0h ≤ QC := fun x (hx : inQ0 x = true) => by
  change inQC x = true
  revert x; decide +kernel
theorem w₁_mem_Q0h : w₁ ∈ Q0h := (by decide +kernel : inQ0 w₁ = true)
theorem w₂_mem_Q0h : w₂ ∈ Q0h := (by decide +kernel : inQ0 w₂ = true)

end MB

@[expose] def blk (a b c d : ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![a, b, 0; c, d, 0; 0, 0, 1]

theorem blk_pow_nine : ∀ a b c d : ZMod 2, blk a b c d ^ 9 = blk a b c d ^ 3 := by
  decide +kernel

theorem blk_pow_three_pow (a b c d : ZMod 2) :
    ∀ m : ℕ, blk a b c d ^ 3 ^ (m + 1) = blk a b c d ^ 3
  | 0 => by rw [zero_add, pow_one]
  | m + 1 => by
    rw [pow_succ 3 (m + 1), pow_mul, blk_pow_three_pow a b c d m, ← pow_mul, blk_pow_nine]

theorem blk_cases : ∀ a b c d : ZMod 2, blk a b c d ^ 3 = 1 → (a, c) ≠ (1, 0) →
    (a = 0 ∧ b = 1 ∧ c = 1 ∧ d = 1) ∨ (a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 0) := by
  decide +kernel

@[expose] def r2 : ZMod 4 →+* ZMod 2 := ZMod.castHom (by norm_num) (ZMod 2)

@[expose] def redM (M : Matrix (Fin 3) (Fin 3) (ZMod 4)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  M.map r2

@[expose] def redV (v : Fin 3 → ZMod 4) : Fin 3 → ZMod 2 := fun i => r2 (v i)

theorem redV_mulVec (M : Matrix (Fin 3) (Fin 3) (ZMod 4)) (v : Fin 3 → ZMod 4) :
    redV (M *ᵥ v) = redM M *ᵥ redV v :=
  funext fun i => r2.map_mulVec M v i

theorem redM_mul (M N : Matrix (Fin 3) (Fin 3) (ZMod 4)) : redM (M * N) = redM M * redM N :=
  Matrix.map_mul

theorem redM_one : redM 1 = 1 := Matrix.map_one _ (map_zero r2) (map_one r2)

theorem redM_pow (M : Matrix (Fin 3) (Fin 3) (ZMod 4)) (n : ℕ) : redM (M ^ n) = redM M ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, redM_one]
  | succ n ih => rw [pow_succ, pow_succ, redM_mul, ih]

theorem r2_eq_zero_iff : ∀ x : ZMod 4, r2 x = 0 ↔ 2 * x = 0 := by decide

theorem redV_add (v w : Fin 3 → ZMod 4) : redV (v + w) = redV v + redV w :=
  funext fun i => map_add r2 (v i) (w i)

theorem redV_sub (v w : Fin 3 → ZMod 4) : redV (v - w) = redV v - redV w :=
  funext fun i => map_sub r2 (v i) (w i)

theorem redV_eq_zero_iff (v : Fin 3 → ZMod 4) : redV v = 0 ↔ ∀ i, 2 * v i = 0 := by
  constructor
  · intro h i
    exact (r2_eq_zero_iff _).mp (congrFun h i)
  · intro h
    funext i
    exact (r2_eq_zero_iff _).mpr (h i)

theorem blk_orbit₁ : ∀ a b : ZMod 2, (a, b) ≠ (0, 0) →
    ∃ i < 3, blk 0 1 1 1 ^ i *ᵥ ![1, 0, 0] = ![a, b, 0] := by decide

theorem blk_orbit₂ : ∀ a b : ZMod 2, (a, b) ≠ (0, 0) →
    ∃ i < 3, blk 1 1 1 0 ^ i *ᵥ ![1, 0, 0] = ![a, b, 0] := by decide

theorem map_conj_conj {X : Type} [Group X] (H : Subgroup X) (a b : X) :
    (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      H.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

namespace BData

variable (A : BData S F T₁)

include A in
theorem E₁_eq_E0t : F.E₁ = E0t F 1 := by
  rw [E0t, mul_one, A7Base.Frame.E₁, E_eq, A.V₁.B_eq, E0_eq]
  change zpowers S.z ⊔ zpowers F.kF ⊔ zpowers S.t ⊔ zpowers F.yF =
    zpowers S.z ⊔ zpowers F.kF ⊔ zpowers F.yF ⊔ zpowers S.t
  rw [sup_right_comm]

theorem Φ_mem_E0 {v : Fin 3 → ZMod 4} (hv : ∀ i, 2 * v i = 0) : A.Φ v ∈ S.E0 F.yF F.kF := by
  have h1 : MB.inE0 (MB.coord v) = true := by
    rw [MB.vec_eta v]; exact MB.inE0_coord_aux _ _ _ ⟨hv 0, hv 1, hv 2⟩
  rw [Φ_def]
  refine map_mem_of_inSpan A.ι (MB.E0_span _ h1) fun g hg => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · rw [A.ι_z]; exact z_mem_E0 _ _
  · rw [A.ι_y]; exact yi_mem_E0 _ _
  · rw [A.ι_k]; exact ki_mem_E0 _ _

theorem E0_le_map : S.E0 F.yF F.kF ≤ MB.E0h.map A.ι := by
  rw [A7Base.E0, closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact ⟨_, MB.z_mem_E0h, A.ι_z⟩
  · exact ⟨_, MB.y_mem_E0h, A.ι_y⟩
  · exact ⟨_, MB.k_mem_E0h, A.ι_k⟩

theorem exists_of_mem_E0 {g : X} (hg : g ∈ S.E0 F.yF F.kF) :
    ∃ v : Fin 3 → ZMod 4, (∀ i, 2 * v i = 0) ∧ A.Φ v = g := by
  obtain ⟨x, hx, rfl⟩ := A.E0_le_map hg
  obtain ⟨a, b, c, ha, hb, hc, hx'⟩ := MB.coord_of_inE0 x hx
  refine ⟨![a, b, c], fun i => ?_, by rw [Φ_def, hx']⟩
  fin_cases i <;> assumption

theorem E0_le_AA : S.E0 F.yF F.kF ≤ A.AA := fun g hg => by
  obtain ⟨v, -, rfl⟩ := A.exists_of_mem_E0 hg
  exact A.Φ_mem v

theorem Q0_le_map : S.Q0 F.yF F.kF A.D₁.w₁ A.D₁.w₂ ≤ MB.Q0h.map A.ι := by
  have hE : S.E0 F.yF F.kF ≤ MB.Q0h.map A.ι :=
    A.E0_le_map.trans (map_mono MB.E0h_le_Q0h)
  refine sup_le (sup_le hE (zpowers_le.mpr ?_)) (zpowers_le.mpr ⟨_, MB.w₂_mem_Q0h, A.ι_w₂⟩)
  obtain ⟨c, hc, hw⟩ := A.V₁.w₁_eq
  change A.D₁.w₁ = A.V₁.w₁N * c at hw
  rw [hw]
  exact mul_mem ⟨_, MB.w₁_mem_Q0h, A.ι_w₁⟩ (hE hc)

theorem two_mul_two_of_mem_Q0 {v : Fin 3 → ZMod 4}
    (h : A.Φ v ∈ S.Q0 F.yF F.kF A.D₁.w₁ A.D₁.w₂) : 2 * v 2 = 0 := by
  obtain ⟨x, hx, hxv⟩ := A.Q0_le_map h
  have : x = MB.coord v := A.ι_injective (hxv.trans (A.Φ_def v))
  subst this
  rw [MB.vec_eta v] at hx
  exact MB.inQ0_coord_aux _ _ _ hx

theorem E0t_mul {a e : X} (he : e ∈ S.E0 F.yF F.kF) : E0t F (a * e) = E0t F a := by
  apply le_antisymm
  · refine sup_le le_sup_left (zpowers_le.mpr ?_)
    rw [← mul_assoc]
    exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left he)
  · refine sup_le le_sup_left (zpowers_le.mpr ?_)
    have : S.t * a = S.t * (a * e) * e⁻¹ := by group
    rw [this]
    exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left (inv_mem he))

theorem map_E0t {n a b : X}
    (hn : (S.E0 F.yF F.kF).map (MulAut.conj n).toMonoidHom = S.E0 F.yF F.kF)
    (hab : n * (S.t * a) * n⁻¹ = S.t * b) :
    (E0t F a).map (MulAut.conj n).toMonoidHom = E0t F b := by
  rw [E0t, Subgroup.map_sup, hn, MonoidHom.map_zpowers]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [hab, E0t]

theorem D₁₁_comm_t {δ : X} (hδ : δ ∈ A.D₁.D₁₁) : δ * S.t = S.t * δ :=
  (mem_centralizer_singleton_iff.mp (A.D₁.D₁₁_le hδ).2)

theorem D₁₁_comm_vN {δ : X} (hδ : δ ∈ A.D₁.D₁₁) : δ * A.V₁.vN = A.V₁.vN * δ :=
  (mem_centralizer_iff.mp (A.V₁.vN_mem_C).2) δ hδ

theorem D₁₁_conj_c {δ : X} (hδ : δ ∈ A.D₁.D₁₁) :
    δ * (S.t * A.V₁.vN) * δ⁻¹ = S.t * A.V₁.vN := by
  rw [show δ * (S.t * A.V₁.vN) * δ⁻¹ = (δ * S.t) * (A.V₁.vN * δ⁻¹) by group, A.D₁₁_comm_t hδ,
    show S.t * δ * (A.V₁.vN * δ⁻¹) = S.t * (δ * A.V₁.vN) * δ⁻¹ by group, A.D₁₁_comm_vN hδ]
  group

theorem D₁₁_conj_Q0 {δ : X} (hδ : δ ∈ A.D₁.D₁₁) {q : X}
    (hq : q ∈ S.Q0 F.yF F.kF A.D₁.w₁ A.D₁.w₂) :
    δ * q * δ⁻¹ ∈ S.Q0 F.yF F.kF A.D₁.w₁ A.D₁.w₂ := by
  have h := A.D₁.Q0_invariant δ ⟨(A.D₁.D₁₁_le hδ).1.1, (A.D₁.D₁₁_le hδ).1.2⟩
  rw [← h]
  exact ⟨q, hq, rfl⟩

theorem D₁₁_conj_AA {δ : X} (hδ : δ ∈ A.D₁.D₁₁) {g : X} (hg : g ∈ A.AA) :
    δ * g * δ⁻¹ ∈ A.AA := by
  obtain ⟨v, rfl⟩ := A.mem_AA.mp hg
  have hQ : ∀ q ∈ S.Q0 F.yF F.kF A.D₁.w₁ A.D₁.w₂, δ * q * δ⁻¹ ∈ A.AA := fun q hq => by
    obtain ⟨x, hx, hxq⟩ := A.Q0_le_map (A.D₁₁_conj_Q0 hδ hq)
    rw [← hxq]; exact ⟨x, MB.Q0h_le_QC hx, rfl⟩
  have h1 := hQ _ A.V₁.w₁N_mem_Q0
  have h2 := hQ _ (w₂_mem_Q0 _ _ _ _)
  have h3 : δ * (S.t * A.V₁.vN) * δ⁻¹ ∈ A.AA := by
    rw [A.D₁₁_conj_c hδ, ← A.Φ_e2]; exact A.Φ_mem _
  rw [Φ_def, MB.coord, map_mul, map_mul, map_pow, map_pow, map_pow, A.ι_w₁, A.ι_w₂, MB.c,
    map_mul, A.ι_t, A.ι_v]
  have hpow : ∀ (g : X) (n : ℕ), δ * g ^ n * δ⁻¹ = (δ * g * δ⁻¹) ^ n := fun g n => by
    rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_pow]
  rw [show δ * (A.V₁.w₁N ^ (v 0).val * A.D₁.w₂ ^ (v 1).val * (S.t * A.V₁.vN) ^ (v 2).val) * δ⁻¹ =
    (δ * A.V₁.w₁N ^ (v 0).val * δ⁻¹) * (δ * A.D₁.w₂ ^ (v 1).val * δ⁻¹) *
      (δ * (S.t * A.V₁.vN) ^ (v 2).val * δ⁻¹) by group, hpow, hpow, hpow]
  exact mul_mem (mul_mem (pow_mem h1 _) (pow_mem h2 _)) (pow_mem h3 _)

theorem D₁₁_le_NA : A.D₁.D₁₁ ≤ A.NA := by
  intro δ hδ
  rw [NA, mem_normalizer_iff]
  intro g
  refine ⟨A.D₁₁_conj_AA hδ, fun h => ?_⟩
  have := A.D₁₁_conj_AA (inv_mem hδ) h
  rwa [inv_inv, show δ⁻¹ * (δ * g * δ⁻¹) * δ = g by group] at this

theorem D₁₁_map_E0 {δ : X} (hδ : δ ∈ A.D₁.D₁₁) :
    (S.E0 F.yF F.kF).map (MulAut.conj δ).toMonoidHom = S.E0 F.yF F.kF := by
  have key : ∀ n ∈ A.D₁.D₁₁, ∀ e ∈ S.E0 F.yF F.kF, n * e * n⁻¹ ∈ S.E0 F.yF F.kF :=
    fun n hn e he => A.V₁.conj_mem_E0 (A.V₁.D₁₁_mem_normalizer hn) he
  apply le_antisymm
  · rintro _ ⟨e, he, rfl⟩; exact key δ hδ e he
  · intro e he
    refine ⟨δ⁻¹ * e * δ, ?_, by simp [mul_assoc]⟩
    have := key δ⁻¹ (inv_mem hδ) e he
    rwa [inv_inv] at this

theorem exists_kappa : ∃ δ ∈ A.D₁.D₁₁, δ * S.z * δ⁻¹ ≠ S.z := by
  by_contra h
  push Not at h
  exact A.V₁.not_fix_z h

theorem kbar_cases {δ : X} (hδ : δ ∈ A.D₁.D₁₁) (hz : δ * S.z * δ⁻¹ ≠ S.z) :
    redM (A.mat ⟨δ, A.D₁₁_le_NA hδ⟩) = blk 0 1 1 1 ∨
      redM (A.mat ⟨δ, A.D₁₁_le_NA hδ⟩) = blk 1 1 1 0 := by
  set K := A.mat ⟨δ, A.D₁₁_le_NA hδ⟩ with hK
  have hconj : ∀ v, δ * A.Φ v * δ⁻¹ = A.Φ (K *ᵥ v) := fun v =>
    A.conj_Φ ⟨δ, A.D₁₁_le_NA hδ⟩ v
  have h2 : K *ᵥ ![0, 0, 1] = ![0, 0, 1] := by
    apply A.Φ_injective
    rw [← hconj, A.Φ_e2, A.D₁₁_conj_c hδ]
  have hQ : ∀ v, A.Φ v ∈ S.Q0 F.yF F.kF A.D₁.w₁ A.D₁.w₂ → 2 * (K *ᵥ v) 2 = 0 := fun v hv => by
    apply A.two_mul_two_of_mem_Q0
    rw [← hconj]; exact A.D₁₁_conj_Q0 hδ hv
  have h0 := hQ ![1, 0, 0] (by rw [A.Φ_e0]; exact A.V₁.w₁N_mem_Q0)
  have h1 := hQ ![0, 1, 0] (by rw [A.Φ_e1]; exact w₂_mem_Q0 _ _ _ _)
  have hz2 : S.z = A.Φ ![1, 0, 0] * A.Φ ![1, 0, 0] := by
    rw [← A.Φ_add, ← A.Φ_z]; congr 1; decide
  have hz' : redV (K *ᵥ ![1, 0, 0]) ≠ redV ![1, 0, 0] := by
    intro h
    apply hz
    have hsub : redV (K *ᵥ ![1, 0, 0] - ![1, 0, 0]) = 0 := by rw [redV_sub, h, sub_self]
    rw [redV_eq_zero_iff] at hsub
    have e : (K *ᵥ ![1, 0, 0]) + (K *ᵥ ![1, 0, 0]) = ![1, 0, 0] + ![1, 0, 0] := by
      funext i
      have := hsub i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this ⊢ <;>
        linear_combination this
    rw [hz2, show δ * (A.Φ ![1, 0, 0] * A.Φ ![1, 0, 0]) * δ⁻¹ =
        (δ * A.Φ ![1, 0, 0] * δ⁻¹) * (δ * A.Φ ![1, 0, 0] * δ⁻¹) by group, hconj, ← A.Φ_add, e,
      A.Φ_add]
  have e02 : K 0 2 = 0 := by
    have := congrFun h2 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have e12 : K 1 2 = 0 := by
    have := congrFun h2 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have e22 : K 2 2 = 1 := by
    have := congrFun h2 2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have e20 : 2 * K 2 0 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h0
  have e21 : 2 * K 2 1 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h1
  have hred : redM K = blk (r2 (K 0 0)) (r2 (K 0 1)) (r2 (K 1 0)) (r2 (K 1 1)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [redM, blk, e02, e12, e22, map_one, map_zero,
      (r2_eq_zero_iff _).mpr e20, (r2_eq_zero_iff _).mpr e21]
  have hac : (r2 (K 0 0), r2 (K 1 0)) ≠ (1, 0) := by
    intro hac
    apply hz'
    simp only [Prod.mk.injEq] at hac
    funext i
    fin_cases i <;> simp [redV, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hac.1, hac.2,
      (r2_eq_zero_iff _).mpr e20, map_one, map_zero]
  obtain ⟨m, hm⟩ := A.D₁.isPGroup_D₁₁ ⟨δ, hδ⟩
  have hK3 : K ^ 3 ^ m = 1 := by
    have hδm : (⟨δ, A.D₁₁_le_NA hδ⟩ : A.NA) ^ 3 ^ m = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hm)
    rw [hK, ← matHom_apply, ← map_pow, hδm, map_one]
  have hB : blk (r2 (K 0 0)) (r2 (K 0 1)) (r2 (K 1 0)) (r2 (K 1 1)) ^ 3 ^ m = 1 := by
    rw [← hred, ← redM_pow, hK3, redM_one]
  rcases m with _ | m
  · exfalso
    rw [pow_zero, pow_one] at hB
    apply hac
    have h00 : r2 (K 0 0) = 1 := by simpa [blk] using congrFun (congrFun hB 0) 0
    have h10 : r2 (K 1 0) = 0 := by simpa [blk] using congrFun (congrFun hB 1) 0
    rw [h00, h10]
  · rw [blk_pow_three_pow] at hB
    rcases blk_cases _ _ _ _ hB hac with ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
    · left; rw [hred, ha, hb, hc, hd]
    · right; rw [hred, ha, hb, hc, hd]


theorem not_conj_E0t (hnc : ¬ SubConj F.E₁ F.E₂) {v : Fin 3 → ZMod 4} (hv2 : 2 * v 2 = 0)
    (hv : ¬ (2 * v 0 = 0 ∧ 2 * v 1 = 0)) {g : X}
    (hg : F.E₁.map (MulAut.conj g).toMonoidHom = E0t F (A.Φ v)) : False := by
  obtain ⟨δ, hδ, hz⟩ := A.exists_kappa
  set κ : A.NA := ⟨δ, A.D₁₁_le_NA hδ⟩ with hκ
  set K := A.mat κ with hK
  have hab : (r2 (v 0), r2 (v 1)) ≠ (0, 0) := by
    intro h
    simp only [Prod.mk.injEq] at h
    exact hv ⟨(r2_eq_zero_iff _).mp h.1, (r2_eq_zero_iff _).mp h.2⟩
  have hvred : redV v = ![r2 (v 0), r2 (v 1), 0] := by
    funext i; fin_cases i <;> simp [redV, (r2_eq_zero_iff _).mpr hv2]
  obtain ⟨i, -, hi⟩ : ∃ i < 3, redM K ^ i *ᵥ ![1, 0, 0] = redV v := by
    rw [hvred]
    rcases A.kbar_cases hδ hz with h | h <;> rw [← hK] at h <;> rw [h]
    · exact blk_orbit₁ _ _ hab
    · exact blk_orbit₂ _ _ hab
  have hsub : redV (v - K ^ i *ᵥ ![1, 0, 0]) = 0 := by
    rw [redV_sub, redV_mulVec, redM_pow, show redV ![1, 0, 0] = ![1, 0, 0] by
      funext j; fin_cases j <;> rfl, hi, sub_self]
  have hE : E0t F (A.Φ v) = E0t F (A.Φ (K ^ i *ᵥ ![1, 0, 0])) := by
    rw [show v = K ^ i *ᵥ ![1, 0, 0] + (v - K ^ i *ᵥ ![1, 0, 0]) by abel, Φ_add,
      E0t_mul (A.Φ_mem_E0 ((redV_eq_zero_iff _).mp hsub))]
  have hmat : A.mat (κ ^ i) = K ^ i := by rw [hK, ← matHom_apply, map_pow]; rfl
  have hδi : δ ^ i ∈ A.D₁.D₁₁ := pow_mem hδ i
  have hmap : (E0t F A.V₁.w₁N).map (MulAut.conj (δ ^ i)).toMonoidHom =
      E0t F (A.Φ (K ^ i *ᵥ ![1, 0, 0])) := by
    refine map_E0t (A.D₁₁_map_E0 hδi) ?_
    have h1 := A.conj_Φ (κ ^ i) ![1, 0, 0]
    rw [hmat, A.Φ_e0] at h1
    have h2 : (↑(κ ^ i) : X) = δ ^ i := by rw [SubgroupClass.coe_pow]
    rw [h2] at h1
    rw [← h1, show δ ^ i * (S.t * A.V₁.w₁N) * (δ ^ i)⁻¹ =
      (δ ^ i * S.t) * A.V₁.w₁N * (δ ^ i)⁻¹ by group, A.D₁₁_comm_t hδi]
    group
  rw [hE, ← hmap] at hg
  have := congrArg (fun H : Subgroup X => H.map (MulAut.conj (δ ^ i)⁻¹).toMonoidHom) hg
  simp only [map_conj_conj] at this
  rw [inv_mul_cancel, show (MulAut.conj (1 : X)).toMonoidHom = MonoidHom.id X by ext; simp,
    map_id] at this
  exact A.not_conj_E₃ hnc this

end BData

end Sec8

end CFSG.ComponentClassification.HSFLit
