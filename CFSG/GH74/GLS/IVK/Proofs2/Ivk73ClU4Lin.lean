module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClU4Pair
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClU4Mod

public section

namespace CFSG.GH74.GLS.IVK

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]
  {h : UnitaryFieldData p f E} {B : V →ₛₗ[h.bar] V →ₗ[E] E} {Y : Subgroup (sesqUnitaryGroup B)}

namespace PairedSL

variable (P : PairedSL h B Y)

theorem sq_eq_one_of_comm {S : sesqUnitaryGroup B} (d : E)
    (hST : ∀ v, unitaryOp S (unitaryOp P.T v) = d • unitaryOp P.T (unitaryOp S v)) :
    d * d = 1 := by
  obtain ⟨v₀, hv₀, hv₀0⟩ := P.exists_ne_zero
  have hSv : unitaryOp S v₀ ≠ 0 := fun h0 =>
    hv₀0 (unitaryOp_injective S (h0.trans (map_zero _).symm))
  have h1 : unitaryOp S (unitaryOp P.T (unitaryOp P.T v₀)) =
      (d * d) • unitaryOp P.T (unitaryOp P.T (unitaryOp S v₀)) := by
    rw [hST (unitaryOp P.T v₀), hST v₀, map_smul, smul_smul]
  rw [P.T_sq, P.T_sq, map_smul] at h1
  have h2 : (P.l ^ 2 - (d * d) * P.l ^ 2) • unitaryOp S v₀ = 0 := by
    rw [sub_smul, mul_smul, ← h1, sub_self]
  have h3 := (smul_eq_zero.mp h2).resolve_right hSv
  have h3' : P.l ^ 2 * (1 - d * d) = 0 := by linear_combination h3
  have h4 : 1 - d * d = 0 := (mul_eq_zero.mp h3').resolve_left (pow_ne_zero 2 P.l_ne)
  linear_combination -h4

theorem not_swap {S : sesqUnitaryGroup B}
    (hSY : ∀ y ∈ Y, ∀ v, unitaryOp S (unitaryOp y v) = unitaryOp y (unitaryOp S v))
    (hswap : ∀ v ∈ P.Vp, unitaryOp S v ∈ P.Vm) : False := by
  let γ : (Fin 2 → E) → (Fin 2 → E) → E := fun u w => B (P.vec u) (unitaryOp S (P.vec w))
  have hadd₁ : ∀ u u' w, γ (u + u') w = γ u w + γ u' w := by
    intro u u' w
    simp only [γ, vec_add, map_add, LinearMap.add_apply]
  have hadd₂ : ∀ u w w', γ u (w + w') = γ u w + γ u w' := by
    intro u w w'
    simp only [γ, vec_add, map_add]
  have hs₁ : ∀ (a : E) u w, γ (a • u) w = barEquiv h a * γ u w := by
    intro a u w
    simp only [γ, vec_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, barEquiv_apply]
  have hs₂ : ∀ (a : E) u w, γ u (a • w) = a * γ u w := by
    intro a u w
    simp only [γ, vec_smul, map_smul, smul_eq_mul]
  have hinv : ∀ g : SpecialLinearGroup (Fin 2) E, ∀ u v : Fin 2 → E,
      γ ((g : Matrix (Fin 2) (Fin 2) E) *ᵥ u) ((g : Matrix (Fin 2) (Fin 2) E) *ᵥ v) = γ u v := by
    intro g u v
    obtain ⟨y, hy, hyv⟩ := P.surj_vec g
    simp only [γ, hyv]
    rw [hSY y hy]
    exact y.2 _ _
  have hzero := sl2_sesquilinear_invariant_zero (barEquiv h) (barEquiv_ne_one h) γ hadd₁ hadd₂ hs₁ hs₂
    hinv
  obtain ⟨w₀, hw₀, hw₀0⟩ := P.exists_ne_zero
  obtain ⟨u₀, hu₀⟩ := P.exists_vec hw₀
  have h3 : unitaryOp S w₀ = 0 := by
    apply P.pair_m _ (hswap w₀ hw₀)
    intro v hv
    obtain ⟨u, hu⟩ := P.exists_vec hv
    have := hzero u u₀
    simp only [γ, hu, hu₀] at this
    exact this
  exact hw₀0 (unitaryOp_injective S (h3.trans (map_zero _).symm))

theorem keep_diag (h2 : (2 : E) ≠ 0) {S : sesqUnitaryGroup B}
    (hSY : ∀ y ∈ Y, ∀ v, unitaryOp S (unitaryOp y v) = unitaryOp y (unitaryOp S v))
    (hcomm : ∀ v, unitaryOp S (unitaryOp P.T v) = unitaryOp P.T (unitaryOp S v)) :
    ∃ c : E, c ≠ 0 ∧ (∀ v ∈ P.Vp, unitaryOp S v = c • v) ∧
      (∀ w ∈ P.Vm, unitaryOp S w = (h.bar c)⁻¹ • w) := by
  have hSp : ∀ v ∈ P.Vp, unitaryOp S v ∈ P.Vp := by
    intro v hv
    apply P.mem_Vp_of_eigen h2
    rw [← hcomm v, P.T_p v hv, map_smul]
  have hSm : ∀ w ∈ P.Vm, unitaryOp S w ∈ P.Vm := by
    intro w hw
    apply P.mem_Vm_of_eigen h2
    rw [← hcomm w, P.T_m w hw, map_neg, map_smul]
  let S₀ : (Fin 2 → E) →ₗ[E] (Fin 2 → E) :=
    P.cp.toLinearMap ∘ₗ (unitaryOp S).restrict hSp ∘ₗ P.cp.symm.toLinearMap
  have hvecS₀ : ∀ u, P.vec (S₀ u) = unitaryOp S (P.vec u) := by
    intro u
    exact P.vec_cp ⟨unitaryOp S (P.vec u), hSp _ (P.vec_mem u)⟩
  let M : Matrix (Fin 2) (Fin 2) E := LinearMap.toMatrix' S₀
  have hM : ∀ u, M *ᵥ u = S₀ u := by
    intro u
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  have hMc : ∀ g : SpecialLinearGroup (Fin 2) E,
      M * (g : Matrix (Fin 2) (Fin 2) E) = (g : Matrix (Fin 2) (Fin 2) E) * M := by
    intro g
    refine Matrix.ext_iff_mulVec.mpr fun u => ?_
    obtain ⟨y, hy, hyv⟩ := P.surj_vec g
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hM, hM]
    apply P.vec_injective
    rw [hvecS₀, hyv, hyv, hvecS₀, hSY y hy]
  obtain ⟨c, hc⟩ := sl2_commutant_scalar M hMc
  have hS₀ : ∀ u, S₀ u = c • u := by
    intro u
    rw [← hM, hc]
    funext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have hSc : ∀ v ∈ P.Vp, unitaryOp S v = c • v := by
    intro v hv
    obtain ⟨u, rfl⟩ := P.exists_vec hv
    rw [← hvecS₀, hS₀, vec_smul]
  obtain ⟨v₀, hv₀, hv₀0⟩ := P.exists_ne_zero
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hv₀0
    apply unitaryOp_injective S
    rw [hSc v₀ hv₀, zero_smul, map_zero]
  refine ⟨c, hc0, hSc, fun w hw => ?_⟩
  have hbc : h.bar c ≠ 0 := fun h0 => hc0 (h.bar.injective (by rw [h0, map_zero]))
  have hsub : unitaryOp S w - (h.bar c)⁻¹ • w ∈ P.Vm :=
    Submodule.sub_mem _ (hSm w hw) (Submodule.smul_mem _ _ hw)
  have h0 := P.pair_m _ hsub (by
    intro v hv
    have h1 := S.2 v w
    have h2' : B (unitaryOp S v) (unitaryOp S w) = h.bar c * B v (unitaryOp S w) := by
      rw [hSc v hv, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
    rw [h2'] at h1
    rw [map_sub, map_smul, smul_eq_mul]
    have : B v (unitaryOp S w) = (h.bar c)⁻¹ * B v w := by
      field_simp
      linear_combination h1
    rw [this, sub_self])
  exact sub_eq_zero.mp h0

theorem linear_cases (h2 : (2 : E) ≠ 0) {S : sesqUnitaryGroup B}
    (hSY : ∀ y ∈ Y, ∀ v, unitaryOp S (unitaryOp y v) = unitaryOp y (unitaryOp S v))
    (d : E) (hST : ∀ v, unitaryOp S (unitaryOp P.T v) = d • unitaryOp P.T (unitaryOp S v))
    (hSS : S * S ∈ sesqNormOneScalars h B) :
    S ∈ sesqNormOneScalars h B ∨ S * P.T⁻¹ ∈ sesqNormOneScalars h B := by
  have hdd := P.sq_eq_one_of_comm d hST
  rcases mul_self_eq_one_iff.mp hdd with hd | hd
  ·
    have hcomm : ∀ v, unitaryOp S (unitaryOp P.T v) = unitaryOp P.T (unitaryOp S v) := fun v => by
      rw [hST v, hd, one_smul]
    obtain ⟨c, hc0, hSc, hSm⟩ := P.keep_diag h2 hSY hcomm
    obtain ⟨z, hz, hzS⟩ := hSS
    have hzS' : ∀ v, unitaryOp S (unitaryOp S v) = z • v := by
      intro v
      have := LinearMap.congr_fun hzS v
      change (unitaryOp S * unitaryOp S) v = (z • (1 : Module.End E V)) v at this
      simpa using this
    obtain ⟨v₀, hv₀, hv₀0⟩ := P.exists_ne_zero
    obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.Vm_ne
    have hbc : h.bar c ≠ 0 := fun h0 => hc0 (h.bar.injective (by rw [h0, map_zero]))
    have hz1 : z = c * c := by
      have h3 := hzS' v₀
      rw [hSc v₀ hv₀, map_smul, hSc v₀ hv₀, smul_smul] at h3
      have h4 : (c * c - z) • v₀ = 0 := by rw [sub_smul, h3, sub_self]
      exact (sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_right hv₀0)).symm
    have hz2 : z = (h.bar c)⁻¹ * (h.bar c)⁻¹ := by
      have h3 := hzS' w₀
      rw [hSm w₀ hw₀, map_smul, hSm w₀ hw₀, smul_smul] at h3
      have h4 : ((h.bar c)⁻¹ * (h.bar c)⁻¹ - z) • w₀ = 0 := by rw [sub_smul, h3, sub_self]
      exact (sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_right hw₀0)).symm
    have hN2 : (c * h.bar c) * (c * h.bar c) = 1 := by
      have : c * c = (h.bar c)⁻¹ * (h.bar c)⁻¹ := hz1.symm.trans hz2
      field_simp at this ⊢
      linear_combination this
    rcases mul_self_eq_one_iff.mp hN2 with hN | hN
    · left
      have hbc' : (h.bar c)⁻¹ = c := inv_eq_of_mul_eq_one_right (by rw [mul_comm]; exact hN)
      refine ⟨c, hN, LinearMap.ext fun v => ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := P.decomp v
      rw [map_add, hSc a ha, hSm b hb, hbc', LinearMap.smul_apply, Module.End.one_apply, smul_add]
    · right
      have hbc' : (h.bar c)⁻¹ = -c := inv_eq_of_mul_eq_one_right (by linear_combination -hN)
      have hnorm : h.norm (c * P.l⁻¹) = 1 := by
        have hl := P.norm_l
        simp only [UnitaryFieldData.norm, map_mul, map_inv₀] at hl ⊢
        have e : c * P.l⁻¹ * (h.bar c * (h.bar P.l)⁻¹) = (c * h.bar c) * (P.l * h.bar P.l)⁻¹ := by
          rw [mul_inv]
          ring
        rw [e, hN, hl]
        norm_num
      refine ⟨c * P.l⁻¹, hnorm, LinearMap.ext fun v => ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := P.decomp v
      have hTa : unitaryOp P.T⁻¹ a = P.l⁻¹ • a := by
        have : unitaryOp P.T (P.l⁻¹ • a) = a := by
          rw [map_smul, P.T_p a ha, smul_smul, inv_mul_cancel₀ P.l_ne, one_smul]
        conv_lhs => rw [← this]
        exact unitaryOp_inv_apply P.T _
      have hTb : unitaryOp P.T⁻¹ b = -(P.l⁻¹ • b) := by
        have : unitaryOp P.T (-(P.l⁻¹ • b)) = b := by
          rw [map_neg, map_smul, P.T_m b hb, smul_neg, smul_smul, inv_mul_cancel₀ P.l_ne,
            one_smul, neg_neg]
        conv_lhs => rw [← this]
        exact unitaryOp_inv_apply P.T _
      change unitaryOp S (unitaryOp P.T⁻¹ (a + b)) = ((c * P.l⁻¹) • (1 : Module.End E V)) (a + b)
      rw [map_add, hTa, hTb, map_add, map_smul, map_neg, map_smul, hSc a ha, hSm b hb, hbc',
        LinearMap.smul_apply, Module.End.one_apply]
      module
  ·
    exfalso
    apply P.not_swap hSY
    intro v hv
    apply P.mem_Vm_of_eigen h2
    have h3 := hST v
    rw [P.T_p v hv, map_smul, hd, neg_smul, one_smul] at h3
    exact (neg_eq_iff_eq_neg.mp h3.symm)

end PairedSL

end CFSG.GH74.GLS.IVK
