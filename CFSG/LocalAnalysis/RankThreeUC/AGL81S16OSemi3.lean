module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OPlane

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus nondegenerate_polarBilin_quadMinus_of_finite)

theorem semi_involution_fixed_point {S : Type} [Finite S] (f : S → S) (hf : ∀ s, f (f s) = s)
    (hodd : ¬ 2 ∣ Nat.card S) : ∃ s, f s = s := by
  classical
  haveI := Fintype.ofFinite S
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  push Not at hno
  let f' : Function.End S := f
  have hf2 : f' ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    funext s
    exact hf s
  have h := Equiv.Perm.card_fixedPoints_modEq (f := f') (p := 2) (n := 1) hf2
  have h0 : Fintype.card (Function.fixedPoints f') = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun x => hno x.1 x.2⟩
  rw [h0] at h
  apply hodd
  rw [Nat.card_eq_fintype_card]
  exact (Nat.modEq_zero_iff_dvd).mp h

section SemiInvol

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

structure SemiInvol (b c : F) (θ : F →+* F) (σ : OW F → OW F) : Prop where
  add : ∀ x y, σ (x + y) = σ x + σ y
  smul : ∀ (r : F) x, σ (r • x) = θ r • σ x
  invol : ∀ x, σ (σ x) = x
  quad : ∀ x, quadMinus 3 F b c (σ x) = θ (quadMinus 3 F b c x)

variable {θ : F →+* F} {σ : OW F → OW F}

theorem SemiInvol.map_zero' (h : SemiInvol b c θ σ) : σ 0 = 0 := by
  have h1 := h.add 0 0
  rw [add_zero] at h1
  have h' : σ 0 + 0 = σ 0 + σ 0 := by rw [add_zero]; exact h1
  exact (add_left_cancel h').symm

theorem SemiInvol.ne_zero (h : SemiInvol b c θ σ) {x : OW F} (hx : x ≠ 0) : σ x ≠ 0 := by
  intro h0
  apply hx
  rw [← h.invol x, h0, h.map_zero']

theorem SemiInvol.polar_eq (h : SemiInvol b c θ σ) (x y : OW F) :
    polar (quadMinus 3 F b c) (σ x) (σ y) = θ (polar (quadMinus 3 F b c) x y) := by
  show quadMinus 3 F b c (σ x + σ y) - quadMinus 3 F b c (σ x) - quadMinus 3 F b c (σ y) =
    θ (quadMinus 3 F b c (x + y) - quadMinus 3 F b c x - quadMinus 3 F b c y)
  rw [← h.add, h.quad, h.quad, h.quad, map_sub, map_sub]

theorem SemiInvol.conj (h : SemiInvol b c θ σ) (G : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F)
    (hG : ∀ v : OW F, quadMinus 3 F b c (gv G v) = quadMinus 3 F b c v) :
    SemiInvol b c θ (fun x => gv G⁻¹ (σ (gv G x))) := by
  have hGinv : ∀ v : OW F, quadMinus 3 F b c (gv G⁻¹ v) = quadMinus 3 F b c v := by
    intro v
    conv_rhs => rw [← gv_gv_inv G v]
    rw [hG]
  refine ⟨fun x y => ?_, fun r x => ?_, fun x => ?_, fun x => ?_⟩
  · simp only [gv_add, h.add]
  · simp only [gv_smul, h.smul]
  · simp only [gv_gv_inv, h.invol, gv_inv_gv]
  · simp only [hGinv, h.quad, hG]

end SemiInvol

section Plane

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F} {θ : F →+* F} {σ : OW F → OW F}

theorem SemiInvol.y0_apply (h : SemiInvol b c θ σ) (he : σ (eV F idx0) = eV F idx0) (v : OW F) :
    σ v (Sum.inr (Sum.inl idx0)) = θ (v (Sum.inr (Sum.inl idx0))) := by
  have := h.polar_eq v (eV F idx0)
  rw [he, polar_e_right, polar_e_right] at this
  exact this

theorem SemiInvol.actSP_mem (h : SemiInvol b c θ σ) (he : σ (eV F idx0) = eV F idx0) {v : OW F}
    (hv : v (Sum.inl idx0) = 0 ∧ v (Sum.inr (Sum.inl idx0)) = 0 ∧ v ≠ 0 ∧
      quadMinus 3 F b c v = 0) :
    proj0 (σ v) (Sum.inl idx0) = 0 ∧ proj0 (σ v) (Sum.inr (Sum.inl idx0)) = 0 ∧
      proj0 (σ v) ≠ 0 ∧ quadMinus 3 F b c (proj0 (σ v)) = 0 := by
  obtain ⟨hv1, hv2, hv3, hv4⟩ := hv
  have hy : σ v (Sum.inr (Sum.inl idx0)) = 0 := by
    rw [h.y0_apply he, hv2, map_zero]
  refine ⟨proj0_apply_inl0 _, ?_, ?_, ?_⟩
  · rw [proj0_apply_of_ne _ (by simp)]
    exact hy
  · intro h0
    have h1 := eq_proj0_add (σ v)
    rw [h0, zero_add] at h1
    have h2 := congrArg σ h1
    rw [h.invol, h.smul, he] at h2
    apply hv3
    have h3 := congrFun h2 (Sum.inl idx0)
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h3
    rw [hv1] at h3
    rw [h2, ← h3, zero_smul]
  · rw [quad_proj0 hy, h.quad, hv4, map_zero]

theorem SemiInvol.proj0_invol (h : SemiInvol b c θ σ) (he : σ (eV F idx0) = eV F idx0) {v : OW F}
    (hv : v (Sum.inl idx0) = 0) : proj0 (σ (proj0 (σ v))) = v := by
  set P := σ (proj0 (σ v)) with hP
  have h1 := eq_proj0_add (σ v)
  have h2 := congrArg σ h1
  rw [h.invol, h.add, h.smul, he] at h2
  rw [← hP] at h2
  have h3 := congrArg proj0 h2
  rw [proj0_add, proj0_smul_eV, add_zero, proj0_of_apply_eq_zero hv] at h3
  exact h3.symm

theorem semi_exists_fixed_v1 (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) (h : SemiInvol b c θ σ)
    (he : σ (eV F idx0) = eV F idx0) :
    ∃ v₁ : OW F, v₁ (Sum.inl idx0) = 0 ∧ v₁ (Sum.inr (Sum.inl idx0)) = 0 ∧ v₁ ≠ 0 ∧
      quadMinus 3 F b c v₁ = 0 ∧ ∃ t : F, σ v₁ = v₁ + t • eV F idx0 := by
  let S₄ := {v : OW F // v (Sum.inl idx0) = 0 ∧ v (Sum.inr (Sum.inl idx0)) = 0 ∧ v ≠ 0 ∧
    quadMinus 3 F b c v = 0}
  let f : S₄ → S₄ := fun v => ⟨proj0 (σ v.1), h.actSP_mem he v.2⟩
  have hf : ∀ v, f (f v) = v := fun v => Subtype.ext (h.proj0_invol he v.2.1)
  obtain ⟨v, hv⟩ := semi_involution_fixed_point f hf (not_two_dvd_card_singPerpSet hirr hF hn)
  refine ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2, σ v.1 (Sum.inl idx0), ?_⟩
  have h2 := eq_proj0_add (σ v.1)
  have h3 : proj0 (σ v.1) = v.1 := congrArg Subtype.val hv
  rw [h3] at h2
  exact h2

theorem semi_exists_plane (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) (h : SemiInvol b c θ σ) :
    ∃ σ' : OW F → OW F, SemiInvol b c θ σ' ∧ σ' (eV F idx0) = eV F idx0 ∧
      ∃ v₁ : OW F, v₁ (Sum.inl idx0) = 0 ∧ v₁ (Sum.inr (Sum.inl idx0)) = 0 ∧ v₁ ≠ 0 ∧
        quadMinus 3 F b c v₁ = 0 ∧ ∃ t : F, σ' v₁ = v₁ + t • eV F idx0 := by
  let S₁ := {v : OW F // v ≠ 0 ∧ quadMinus 3 F b c v = 0}
  let g : S₁ → S₁ := fun v => ⟨σ v.1, h.ne_zero v.2.1, by rw [h.quad, v.2.2, map_zero]⟩
  have hg : ∀ v, g (g v) = v := fun v => Subtype.ext (h.invol v.1)
  obtain ⟨w, hw⟩ := semi_involution_fixed_point g hg
    (not_two_dvd_card_nonzero_singular hirr hF hn)
  have hwf : σ w.1 = w.1 := congrArg Subtype.val hw
  obtain ⟨G, hG, hGe⟩ := exists_gl_isometry_apply_eq hirr (eV_ne_zero (F := F)) w.2.1
    (by rw [w.2.2, quad_eV idx0])
  have hσ' := h.conj G hG
  refine ⟨fun x => gv G⁻¹ (σ (gv G x)), hσ', ?_, ?_⟩
  · show gv G⁻¹ (σ (gv G (eV F idx0))) = eV F idx0
    rw [hGe, hwf, ← hGe]
    exact gv_inv_gv G _
  · refine semi_exists_fixed_v1 hirr hF hn hσ' ?_
    show gv G⁻¹ (σ (gv G (eV F idx0))) = eV F idx0
    rw [hGe, hwf, ← hGe]
    exact gv_inv_gv G _

end Plane

end CFSG.LocalAnalysis.RankThreeUC
