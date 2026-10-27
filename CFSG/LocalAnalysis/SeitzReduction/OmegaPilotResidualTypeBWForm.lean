module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeBCLift

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module

section Range

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  (N : (Fin d → K) →ₗ[K] (Fin d → K))
  (hadj : ∀ x y, QuadraticMap.polarBilin Q (N x) y = QuadraticMap.polarBilin Q x (N y))
  (hNN : ∀ v, N (N v) = 0)

include hadj hNN in
theorem quad_add_of_mem_range {w w' : Fin d → K} (hw : w ∈ LinearMap.range N)
    (hw' : w' ∈ LinearMap.range N) : Q (w + w') = Q w + Q w' := by
  rw [quad_add_eq, polar_mem_range_ker N hadj hw (range_le_ker N hNN hw'), add_zero]

include hadj hNN in
@[expose] def wallSing : Submodule K (Fin d → K) where
  carrier := {v | v ∈ LinearMap.range N ∧ Q v = 0}
  add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, by
    rw [quad_add_of_mem_range N hadj hNN ha.1 hb.1, ha.2, hb.2, add_zero]⟩
  zero_mem' := ⟨zero_mem _, QuadraticMap.map_zero Q⟩
  smul_mem' := fun c {v} hv => ⟨Submodule.smul_mem _ c hv.1, by
    rw [QuadraticMap.map_smul, hv.2, smul_zero]⟩

theorem mem_wallSing {v : Fin d → K} :
    v ∈ wallSing N hadj hNN ↔ v ∈ LinearMap.range N ∧ Q v = 0 :=
  Iff.rfl

theorem wallSing_le_range : wallSing N hadj hNN ≤ LinearMap.range N :=
  fun _ hv => ((mem_wallSing N hadj hNN).mp hv).1

include hadj hNN in
@[expose] def wallSingOne (zy : Fin d → K) : Submodule K (Fin d → K) where
  carrier := {v | v ∈ LinearMap.range N ∧ Q v = 0 ∧ QuadraticMap.polar Q v zy = 0}
  add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1,
    by rw [quad_add_of_mem_range N hadj hNN ha.1 hb.1, ha.2.1, hb.2.1, add_zero],
    by rw [QuadraticMap.polar_add_left, ha.2.2, hb.2.2, add_zero]⟩
  zero_mem' := ⟨zero_mem _, QuadraticMap.map_zero Q, QuadraticMap.polar_zero_left Q zy⟩
  smul_mem' := fun c {v} hv => ⟨Submodule.smul_mem _ c hv.1,
    by rw [QuadraticMap.map_smul, hv.2.1, smul_zero],
    by rw [QuadraticMap.polar_smul_left, hv.2.2, smul_zero]⟩

theorem mem_wallSingOne {zy v : Fin d → K} :
    v ∈ wallSingOne N hadj hNN zy ↔
      v ∈ LinearMap.range N ∧ Q v = 0 ∧ QuadraticMap.polar Q v zy = 0 :=
  Iff.rfl

theorem wallSingOne_le_wallSing (zy : Fin d → K) :
    wallSingOne N hadj hNN zy ≤ wallSing N hadj hNN :=
  fun _ hv => ⟨((mem_wallSingOne N hadj hNN).mp hv).1, ((mem_wallSingOne N hadj hNN).mp hv).2.1⟩

theorem wallSingOne_le_range (zy : Fin d → K) :
    wallSingOne N hadj hNN zy ≤ LinearMap.range N :=
  (wallSingOne_le_wallSing N hadj hNN zy).trans (wallSing_le_range N hadj hNN)

include hadj in
@[expose] noncomputable def wallRestrict (U : Submodule K (Fin d → K))
    (hU : U ≤ LinearMap.range N) : LinearMap.BilinForm K U :=
  (wallForm (QuadraticMap.polarBilin Q) N hadj).compl₁₂ (Submodule.inclusion hU)
    (Submodule.inclusion hU)

theorem wallRestrict_apply (U : Submodule K (Fin d → K)) (hU : U ≤ LinearMap.range N)
    (u u' : U) {z : Fin d → K} (hz : N z = (u' : Fin d → K)) :
    wallRestrict N hadj U hU u u' = QuadraticMap.polar Q (u : Fin d → K) z := by
  obtain ⟨x, hx⟩ := hU u.2
  have h1 : Submodule.inclusion hU u = ⟨N x, LinearMap.mem_range_self N x⟩ :=
    Subtype.ext hx.symm
  have h2 : Submodule.inclusion hU u' = ⟨N z, LinearMap.mem_range_self N z⟩ :=
    Subtype.ext hz.symm
  rw [wallRestrict, LinearMap.compl₁₂_apply, h1, h2, wallForm_apply,
    QuadraticMap.polarBilin_apply_apply, hx]

theorem wallRestrict_isSymm (U : Submodule K (Fin d → K)) (hU : U ≤ LinearMap.range N) :
    (wallRestrict N hadj U hU).IsSymm := by
  refine ⟨fun u u' => ?_⟩
  obtain ⟨a, ha⟩ := hU u.2
  obtain ⟨b, hb⟩ := hU u'.2
  have e : QuadraticMap.polar Q (N a) b = QuadraticMap.polar Q (N b) a := by
    rw [← QuadraticMap.polarBilin_apply_apply, hadj, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar_comm]
  rw [wallRestrict_apply N hadj U hU u u' hb, wallRestrict_apply N hadj U hU u' u ha, ← ha, ← hb]
  exact e

theorem wallRestrict_isAlt (hQN : ∀ a, QuadraticMap.polar Q (N a) a = Q (N a))
    (U : Submodule K (Fin d → K)) (hU : U ≤ LinearMap.range N) (hQU : ∀ u ∈ U, Q u = 0) :
    (wallRestrict N hadj U hU).IsAlt := by
  intro u
  obtain ⟨a, ha⟩ := hU u.2
  rw [wallRestrict_apply N hadj U hU u u ha, ← ha, hQN, ha, hQU u u.2]

theorem wallRestrict_nondegenerate_of (hB : (QuadraticMap.polarBilin Q).Nondegenerate)
    (U : Submodule K (Fin d → K)) (hU : U ≤ LinearMap.range N)
    (hproj : ∀ z', ∃ z'', N z'' ∈ U ∧
      ∀ u ∈ U, QuadraticMap.polar Q u z' = QuadraticMap.polar Q u z'') :
    (wallRestrict N hadj U hU).Nondegenerate := by
  have key : ∀ u : U, (∀ u' : U, wallRestrict N hadj U hU u u' = 0) → u = 0 := by
    intro u hu
    refine Submodule.coe_eq_zero.mp (hB.1 _ fun z' => ?_)
    obtain ⟨z'', hz''U, hz''⟩ := hproj z'
    rw [QuadraticMap.polarBilin_apply_apply, hz'' u u.2,
      ← wallRestrict_apply N hadj U hU u ⟨N z'', hz''U⟩ rfl]
    exact hu _
  refine ⟨key, fun u hu => key u fun u' => ?_⟩
  rw [(wallRestrict_isSymm N hadj U hU).eq u u']
  exact hu u'

theorem wallRestrict_wallSingOne_isAlt (hQN : ∀ a, QuadraticMap.polar Q (N a) a = Q (N a))
    (zy : Fin d → K) :
    (wallRestrict N hadj (wallSingOne N hadj hNN zy) (wallSingOne_le_range N hadj hNN zy)).IsAlt :=
  wallRestrict_isAlt N hadj hQN _ _ fun _ hu => ((mem_wallSingOne N hadj hNN).mp hu).2.1

theorem wallSing_inf_span_of_one {z : Fin d → K} (h1 : Q (N z) = 1) :
    wallSing N hadj hNN ⊓ K ∙ (N z) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv2
  have h := ((mem_wallSing N hadj hNN).mp hv1).2
  rw [QuadraticMap.map_smul, h1, smul_eq_mul, mul_one, mul_self_eq_zero] at h
  rw [h, zero_smul]
  exact zero_mem _

theorem mem_span_of_mem_compl_of_mem_wallSing {z zy : Fin d → K} (h0 : Q (N z) = 0)
    (hy : Q (N zy) = 1) {C : Submodule K (Fin d → K)}
    (hCW : C ⊓ LinearMap.range N = Submodule.span K {N z, N zy}) {v : Fin d → K}
    (hvC : v ∈ C) (hv : v ∈ wallSing N hadj hNN) : v ∈ K ∙ (N z) := by
  have hmem : v ∈ Submodule.span K {N z, N zy} := by
    rw [← hCW]
    exact Submodule.mem_inf.mpr ⟨hvC, wallSing_le_range N hadj hNN hv⟩
  obtain ⟨α, γ, rfl⟩ := Submodule.mem_span_pair.mp hmem
  have hQ := ((mem_wallSing N hadj hNN).mp hv).2
  rw [quad_add_of_mem_range N hadj hNN (Submodule.smul_mem _ _ (LinearMap.mem_range_self N z))
    (Submodule.smul_mem _ _ (LinearMap.mem_range_self N zy)), QuadraticMap.map_smul,
    QuadraticMap.map_smul, h0, hy, smul_zero, zero_add, smul_eq_mul, mul_one,
    mul_self_eq_zero] at hQ
  rw [hQ, zero_smul, add_zero]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end Range

section Compl

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem exists_kerCompl (N : V →ₗ[K] V) (hNN : ∀ v, N (N v) = 0) (U D : Submodule K V)
    (hinf : U ⊓ D = ⊥) (hsup : U ⊔ D = LinearMap.range N) :
    ∃ C : Submodule K V, D ≤ C ∧ C ≤ LinearMap.ker N ∧ U ⊓ C = ⊥ ∧
      U ⊔ C = LinearMap.ker N ∧ C ⊓ LinearMap.range N = D := by
  have hRK : LinearMap.range N ≤ LinearMap.ker N := range_le_ker N hNN
  have hUR : U ≤ LinearMap.range N := by
    rw [← hsup]
    exact le_sup_left
  have hDR : D ≤ LinearMap.range N := by
    rw [← hsup]
    exact le_sup_right
  obtain ⟨C'', hC''⟩ := (LinearMap.range N).exists_isCompl
  have h0 : C'' ⊓ LinearMap.ker N ⊓ LinearMap.range N = ⊥ := by
    rw [eq_bot_iff, ← hC''.inf_eq_bot]
    intro v hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
    exact Submodule.mem_inf.mpr ⟨hv2, (Submodule.mem_inf.mp hv1).1⟩
  have hCR : (D ⊔ C'' ⊓ LinearMap.ker N) ⊓ LinearMap.range N = D := by
    rw [sup_inf_assoc_of_le _ hDR, h0, sup_bot_eq]
  refine ⟨D ⊔ C'' ⊓ LinearMap.ker N, le_sup_left, sup_le (hDR.trans hRK) inf_le_right, ?_, ?_,
    hCR⟩
  · rw [eq_bot_iff, ← hinf]
    intro v hv
    obtain ⟨hvU, hvC⟩ := Submodule.mem_inf.mp hv
    refine Submodule.mem_inf.mpr ⟨hvU, ?_⟩
    rw [← hCR]
    exact Submodule.mem_inf.mpr ⟨hvC, hUR hvU⟩
  · rw [← sup_assoc, hsup, ← sup_inf_assoc_of_le _ hRK, hC''.sup_eq_top, top_inf_eq]

end Compl

section Sqrt

variable {K : Type} [Field K] [CharP K 2] [PerfectRing K 2] {d : ℕ}
  {Q : QuadraticForm K (Fin d → K)} (N : (Fin d → K) →ₗ[K] (Fin d → K))
  (hadj : ∀ x y, QuadraticMap.polarBilin Q (N x) y = QuadraticMap.polarBilin Q x (N y))
  (hNN : ∀ v, N (N v) = 0)

include hadj hNN in
@[expose] noncomputable def sqrtQuadRange : LinearMap.range N →ₗ[K] K where
  toFun w := sqrtTwo K (Q w)
  map_add' w w' := by
    rw [Submodule.coe_add, quad_add_of_mem_range N hadj hNN w.2 w'.2, map_add]
  map_smul' c w := by
    rw [Submodule.coe_smul, QuadraticMap.map_smul, smul_eq_mul (c * c), sqrtTwo_mul_self_mul,
      RingHom.id_apply, smul_eq_mul]

include hadj hNN in
theorem exists_wallDual (hB : (QuadraticMap.polarBilin Q).Nondegenerate) :
    ∃ z : Fin d → K, ∀ w ∈ LinearMap.range N, QuadraticMap.polar Q w z = sqrtTwo K (Q w) := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (sqrtQuadRange N hadj hNN)
  refine ⟨(LinearMap.BilinForm.toDual (QuadraticMap.polarBilin Q) hB).symm g, fun w hw => ?_⟩
  have h1 := LinearMap.BilinForm.apply_toDual_symm_apply (B := QuadraticMap.polarBilin Q)
    (hB := hB) g w
  rw [QuadraticMap.polarBilin_apply_apply] at h1
  rw [QuadraticMap.polar_comm, h1]
  exact LinearMap.congr_fun hg ⟨w, hw⟩

variable {z : Fin d → K}
  (hz : ∀ w ∈ LinearMap.range N, QuadraticMap.polar Q w z = sqrtTwo K (Q w))
  (hQN : ∀ a, QuadraticMap.polar Q (N a) a = Q (N a))

include hz hQN in
theorem quad_wallDual : Q (N z) = 0 ∨ Q (N z) = 1 := by
  have h1 := hz (N z) (LinearMap.mem_range_self N z)
  rw [hQN] at h1
  have h2 : Q (N z) * Q (N z) = Q (N z) := by
    have h3 := sqrtTwo_mul_self (Q (N z))
    rwa [← h1] at h3
  have h4 : Q (N z) * (Q (N z) - 1) = 0 := by rw [mul_sub, mul_one, h2, sub_self]
  rcases mul_eq_zero.mp h4 with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

include hz in
theorem polar_wallDual_of_mem_wallSing {v : Fin d → K} (hv : v ∈ wallSing N hadj hNN) :
    QuadraticMap.polar Q v z = 0 := by
  rw [hz v ((mem_wallSing N hadj hNN).mp hv).1, ((mem_wallSing N hadj hNN).mp hv).2, map_zero]

include hz in
theorem polar_wallDual_of_mem_wallSingOne {zy v : Fin d → K}
    (hv : v ∈ wallSingOne N hadj hNN zy) : QuadraticMap.polar Q v z = 0 :=
  polar_wallDual_of_mem_wallSing N hadj hNN hz (wallSingOne_le_wallSing N hadj hNN zy hv)

theorem add_smul_mem_wallSing_of_one (h1 : Q (N z) = 1) {w : Fin d → K}
    (hw : w ∈ LinearMap.range N) : w + sqrtTwo K (Q w) • N z ∈ wallSing N hadj hNN := by
  have hc : sqrtTwo K (Q w) • N z ∈ LinearMap.range N :=
    Submodule.smul_mem _ _ (LinearMap.mem_range_self N z)
  refine (mem_wallSing N hadj hNN).mpr ⟨add_mem hw hc, ?_⟩
  rw [quad_add_of_mem_range N hadj hNN hw hc, QuadraticMap.map_smul, h1, smul_eq_mul, mul_one,
    sqrtTwo_mul_self, CharTwo.add_self_eq_zero]

theorem wallSing_sup_span_of_one (h1 : Q (N z) = 1) :
    wallSing N hadj hNN ⊔ K ∙ (N z) = LinearMap.range N := by
  refine le_antisymm (sup_le (wallSing_le_range N hadj hNN)
    ((Submodule.span_singleton_le_iff_mem _ _).mpr (LinearMap.mem_range_self N z)))
    fun w hw => ?_
  have h : w + sqrtTwo K (Q w) • N z - sqrtTwo K (Q w) • N z ∈
      wallSing N hadj hNN ⊔ K ∙ (N z) :=
    sub_mem (Submodule.mem_sup_left (add_smul_mem_wallSing_of_one N hadj hNN h1 hw))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
  rwa [add_sub_cancel_right] at h

theorem finrank_wallSing_add_one (h1 : Q (N z) = 1) :
    finrank K (wallSing N hadj hNN) + 1 = finrank K (LinearMap.range N) := by
  have hNz : N z ≠ 0 := fun h => by
    rw [h, QuadraticMap.map_zero] at h1
    exact zero_ne_one h1
  have h := Submodule.finrank_sup_add_finrank_inf_eq (wallSing N hadj hNN) (K ∙ (N z))
  rw [wallSing_sup_span_of_one N hadj hNN h1, wallSing_inf_span_of_one N hadj hNN h1,
    finrank_bot, add_zero, finrank_span_singleton hNz] at h
  exact h.symm

include hz in
theorem wallRestrict_wallSing_nondegenerate (h1 : Q (N z) = 1)
    (hB : (QuadraticMap.polarBilin Q).Nondegenerate) :
    (wallRestrict N hadj (wallSing N hadj hNN) (wallSing_le_range N hadj hNN)).Nondegenerate := by
  refine wallRestrict_nondegenerate_of N hadj hB _ _ fun z' =>
    ⟨z' + sqrtTwo K (Q (N z')) • z, ?_, fun u hu => ?_⟩
  · rw [map_add, map_smul]
    exact add_smul_mem_wallSing_of_one N hadj hNN h1 (LinearMap.mem_range_self N z')
  · rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
      polar_wallDual_of_mem_wallSing N hadj hNN hz hu, smul_zero, add_zero]

include hadj hz in
theorem polar_wallDual_eq_one {zy : Fin d → K} (hy : Q (N zy) = 1) :
    QuadraticMap.polar Q (N z) zy = 1 := by
  rw [← QuadraticMap.polarBilin_apply_apply, hadj, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar_comm, hz _ (LinearMap.mem_range_self N zy), hy, map_one]

include hadj hz in
theorem wallDual_ne_zero_of_zero {zy : Fin d → K} (hy : Q (N zy) = 1) : N z ≠ 0 := by
  intro h
  have h1 := polar_wallDual_eq_one N hadj hz hy
  rw [h, QuadraticMap.polar_zero_left] at h1
  exact zero_ne_one h1

include hz in
theorem add_smul_mem_wallSingOne (h0 : Q (N z) = 0) {zy : Fin d → K} (hy : Q (N zy) = 1)
    {w : Fin d → K} (hw : w ∈ wallSing N hadj hNN) :
    w + QuadraticMap.polar Q w zy • N z ∈ wallSingOne N hadj hNN zy := by
  obtain ⟨hwW, hQw⟩ := (mem_wallSing N hadj hNN).mp hw
  have hc : QuadraticMap.polar Q w zy • N z ∈ LinearMap.range N :=
    Submodule.smul_mem _ _ (LinearMap.mem_range_self N z)
  refine (mem_wallSingOne N hadj hNN).mpr ⟨add_mem hwW hc, ?_, ?_⟩
  · rw [quad_add_of_mem_range N hadj hNN hwW hc, QuadraticMap.map_smul, h0, hQw, smul_zero,
      add_zero]
  · rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
      polar_wallDual_eq_one N hadj hz hy, smul_eq_mul, mul_one, CharTwo.add_self_eq_zero]

include hz in
theorem wallSingOne_sup_span (h0 : Q (N z) = 0) {zy : Fin d → K} (hy : Q (N zy) = 1) :
    wallSingOne N hadj hNN zy ⊔ K ∙ (N z) = wallSing N hadj hNN := by
  refine le_antisymm (sup_le (wallSingOne_le_wallSing N hadj hNN zy)
    ((Submodule.span_singleton_le_iff_mem _ _).mpr
      ((mem_wallSing N hadj hNN).mpr ⟨LinearMap.mem_range_self N z, h0⟩))) fun w hw => ?_
  have h : w + QuadraticMap.polar Q w zy • N z - QuadraticMap.polar Q w zy • N z ∈
      wallSingOne N hadj hNN zy ⊔ K ∙ (N z) :=
    sub_mem (Submodule.mem_sup_left (add_smul_mem_wallSingOne N hadj hNN hz h0 hy hw))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
  rwa [add_sub_cancel_right] at h

include hz in
theorem wallSingOne_inf_span {zy : Fin d → K} (hy : Q (N zy) = 1) :
    wallSingOne N hadj hNN zy ⊓ K ∙ (N z) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv2
  have h := ((mem_wallSingOne N hadj hNN).mp hv1).2.2
  rw [QuadraticMap.polar_smul_left, polar_wallDual_eq_one N hadj hz hy, smul_eq_mul,
    mul_one] at h
  rw [h, zero_smul]
  exact zero_mem _

include hz hQN in
theorem add_smul_add_smul_mem_wallSingOne (h0 : Q (N z) = 0) {zy : Fin d → K}
    (hy : Q (N zy) = 1) {w : Fin d → K} (hw : w ∈ LinearMap.range N) :
    w + (QuadraticMap.polar Q w zy + sqrtTwo K (Q w)) • N z + sqrtTwo K (Q w) • N zy ∈
      wallSingOne N hadj hNN zy := by
  have hp1 : (QuadraticMap.polar Q w zy + sqrtTwo K (Q w)) • N z ∈ LinearMap.range N :=
    Submodule.smul_mem _ _ (LinearMap.mem_range_self N z)
  have hp2 : sqrtTwo K (Q w) • N zy ∈ LinearMap.range N :=
    Submodule.smul_mem _ _ (LinearMap.mem_range_self N zy)
  refine (mem_wallSingOne N hadj hNN).mpr ⟨add_mem (add_mem hw hp1) hp2, ?_, ?_⟩
  · rw [quad_add_of_mem_range N hadj hNN (add_mem hw hp1) hp2,
      quad_add_of_mem_range N hadj hNN hw hp1, QuadraticMap.map_smul, QuadraticMap.map_smul, h0,
      hy, smul_zero, add_zero, smul_eq_mul, mul_one, sqrtTwo_mul_self, CharTwo.add_self_eq_zero]
  · rw [QuadraticMap.polar_add_left, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_smul_left, polar_wallDual_eq_one N hadj hz hy, hQN, hy, smul_eq_mul,
      smul_eq_mul, mul_one, mul_one]
    linear_combination CharTwo.add_self_eq_zero (QuadraticMap.polar Q w zy) +
      CharTwo.add_self_eq_zero (sqrtTwo K (Q w))

include hz hQN in
theorem wallSingOne_sup_span_pair (h0 : Q (N z) = 0) {zy : Fin d → K} (hy : Q (N zy) = 1) :
    wallSingOne N hadj hNN zy ⊔ Submodule.span K {N z, N zy} = LinearMap.range N := by
  refine le_antisymm (sup_le (wallSingOne_le_range N hadj hNN zy) ?_) fun w hw => ?_
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact LinearMap.mem_range_self N z
    · exact LinearMap.mem_range_self N zy
  · have hp : (QuadraticMap.polar Q w zy + sqrtTwo K (Q w)) • N z + sqrtTwo K (Q w) • N zy ∈
        Submodule.span K {N z, N zy} :=
      Submodule.mem_span_pair.mpr ⟨_, _, rfl⟩
    have h : w + (QuadraticMap.polar Q w zy + sqrtTwo K (Q w)) • N z + sqrtTwo K (Q w) • N zy -
        ((QuadraticMap.polar Q w zy + sqrtTwo K (Q w)) • N z + sqrtTwo K (Q w) • N zy) ∈
        wallSingOne N hadj hNN zy ⊔ Submodule.span K {N z, N zy} :=
      sub_mem (Submodule.mem_sup_left
        (add_smul_add_smul_mem_wallSingOne N hadj hNN hz hQN h0 hy hw))
        (Submodule.mem_sup_right hp)
    rwa [add_assoc, add_sub_cancel_right] at h

include hz in
theorem eq_zero_of_smul_add_smul_mem_wallSingOne (h0 : Q (N z) = 0) {zy : Fin d → K}
    (hy : Q (N zy) = 1) {α γ : K} (h : α • N z + γ • N zy ∈ wallSingOne N hadj hNN zy) :
    α = 0 ∧ γ = 0 := by
  obtain ⟨-, hQ, hP⟩ := (mem_wallSingOne N hadj hNN).mp h
  rw [quad_add_of_mem_range N hadj hNN (Submodule.smul_mem _ _ (LinearMap.mem_range_self N z))
    (Submodule.smul_mem _ _ (LinearMap.mem_range_self N zy)), QuadraticMap.map_smul,
    QuadraticMap.map_smul, h0, hy, smul_zero, zero_add, smul_eq_mul, mul_one,
    mul_self_eq_zero] at hQ
  subst hQ
  rw [zero_smul, add_zero, QuadraticMap.polar_smul_left, polar_wallDual_eq_one N hadj hz hy,
    smul_eq_mul, mul_one] at hP
  exact ⟨hP, rfl⟩

include hz in
theorem wallSingOne_inf_span_pair (h0 : Q (N z) = 0) {zy : Fin d → K} (hy : Q (N zy) = 1) :
    wallSingOne N hadj hNN zy ⊓ Submodule.span K {N z, N zy} = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
  obtain ⟨α, γ, rfl⟩ := Submodule.mem_span_pair.mp hv2
  obtain ⟨rfl, rfl⟩ := eq_zero_of_smul_add_smul_mem_wallSingOne N hadj hNN hz h0 hy hv1
  rw [zero_smul, zero_smul, add_zero]
  exact zero_mem _

include hz hQN in
theorem wallRestrict_wallSingOne_nondegenerate (h0 : Q (N z) = 0) {zy : Fin d → K}
    (hy : Q (N zy) = 1) (hB : (QuadraticMap.polarBilin Q).Nondegenerate) :
    (wallRestrict N hadj (wallSingOne N hadj hNN zy)
      (wallSingOne_le_range N hadj hNN zy)).Nondegenerate := by
  refine wallRestrict_nondegenerate_of N hadj hB _ _ fun z' =>
    ⟨z' + (QuadraticMap.polar Q (N z') zy + sqrtTwo K (Q (N z'))) • z +
      sqrtTwo K (Q (N z')) • zy, ?_, fun u hu => ?_⟩
  · rw [map_add, map_add, map_smul, map_smul]
    exact add_smul_add_smul_mem_wallSingOne N hadj hNN hz hQN h0 hy
      (LinearMap.mem_range_self N z')
  · rw [QuadraticMap.polar_add_right, QuadraticMap.polar_add_right,
      QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right,
      polar_wallDual_of_mem_wallSingOne N hadj hNN hz hu,
      ((mem_wallSingOne N hadj hNN).mp hu).2.2, smul_zero, smul_zero, add_zero, add_zero]

include hz hQN in
theorem finrank_wallSingOne_add_two (h0 : Q (N z) = 0) {zy : Fin d → K} (hy : Q (N zy) = 1) :
    finrank K (wallSingOne N hadj hNN zy) + 2 = finrank K (LinearMap.range N) := by
  have hli : LinearIndependent K ![N z, N zy] := by
    rw [LinearIndependent.pair_iff]
    intro α γ h
    refine eq_zero_of_smul_add_smul_mem_wallSingOne N hadj hNN hz h0 hy ?_
    rw [h]
    exact zero_mem _
  have hfin : finrank K (Submodule.span K {N z, N zy}) = 2 := by
    have := finrank_span_eq_card hli
    rwa [show Set.range ![N z, N zy] = {N z, N zy} by
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union]] at this
  have h := Submodule.finrank_sup_add_finrank_inf_eq (wallSingOne N hadj hNN zy)
    (Submodule.span K {N z, N zy})
  rw [wallSingOne_sup_span_pair N hadj hNN hz hQN h0 hy,
    wallSingOne_inf_span_pair N hadj hNN hz h0 hy, finrank_bot, add_zero, hfin] at h
  exact h.symm

include hadj hNN hz hQN in
theorem even_finrank_range_of_zero (h0 : Q (N z) = 0) {zy : Fin d → K} (hy : Q (N zy) = 1)
    (hB : (QuadraticMap.polarBilin Q).Nondegenerate) :
    Even (finrank K (LinearMap.range N)) := by
  obtain ⟨r, -, hr, -⟩ := CFSG.RankThree.PartOne.KCAlternating.exists_isSymplecticBasis
    (wallRestrict_wallSingOne_isAlt N hadj hNN hQN zy)
    (wallRestrict_wallSingOne_nondegenerate N hadj hNN hz hQN h0 hy hB)
  refine ⟨r + 1, ?_⟩
  rw [← finrank_wallSingOne_add_two N hadj hNN hz hQN h0 hy, hr]
  ring

include hz in
theorem polar_eq_zero_of_mem_wallSing_of_mem_compl {C : Submodule K (Fin d → K)}
    (hCW : C ⊓ LinearMap.range N = K ∙ (N z)) {u : Fin d → K} (hu : u ∈ wallSing N hadj hNN)
    {z' : Fin d → K} (hz' : N z' ∈ C) : QuadraticMap.polar Q u z' = 0 := by
  have hmem : N z' ∈ K ∙ (N z) := by
    rw [← hCW]
    exact Submodule.mem_inf.mpr ⟨hz', LinearMap.mem_range_self N z'⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hker : z' - c • z ∈ LinearMap.ker N := by
    rw [LinearMap.mem_ker, map_sub, map_smul, hc, sub_self]
  have h := polar_mem_range_ker N hadj ((mem_wallSing N hadj hNN).mp hu).1 hker
  rwa [QuadraticMap.polar_sub_right, QuadraticMap.polar_smul_right,
    polar_wallDual_of_mem_wallSing N hadj hNN hz hu, smul_zero, sub_zero] at h

include hz in
theorem polar_eq_zero_of_mem_wallSingOne_of_mem_compl {zy : Fin d → K}
    {C : Submodule K (Fin d → K)} (hCW : C ⊓ LinearMap.range N = Submodule.span K {N z, N zy})
    {u : Fin d → K} (hu : u ∈ wallSingOne N hadj hNN zy) {z' : Fin d → K} (hz' : N z' ∈ C) :
    QuadraticMap.polar Q u z' = 0 := by
  have hmem : N z' ∈ Submodule.span K {N z, N zy} := by
    rw [← hCW]
    exact Submodule.mem_inf.mpr ⟨hz', LinearMap.mem_range_self N z'⟩
  obtain ⟨α, γ, hαγ⟩ := Submodule.mem_span_pair.mp hmem
  have hker : z' - (α • z + γ • zy) ∈ LinearMap.ker N := by
    rw [LinearMap.mem_ker, map_sub, map_add, map_smul, map_smul, hαγ, sub_self]
  obtain ⟨hu1, -, hu3⟩ := (mem_wallSingOne N hadj hNN).mp hu
  have h := polar_mem_range_ker N hadj hu1 hker
  rwa [QuadraticMap.polar_sub_right, QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
    QuadraticMap.polar_smul_right, polar_wallDual_of_mem_wallSingOne N hadj hNN hz hu, hu3,
    smul_zero, smul_zero, add_zero, sub_zero] at h

end Sqrt

end CFSG.SeitzReduction.OmegaPilot
