module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OPlaneCnt
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OFixW

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus nondegenerate_polarBilin_quadMinus_of_finite)

section Plane

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

abbrev eV (F : Type) [Field F] (i : Fin (3 - 1)) : OW F := Pi.single (Sum.inl i) 1

abbrev fV (F : Type) [Field F] (i : Fin (3 - 1)) : OW F := Pi.single (Sum.inr (Sum.inl i)) 1

abbrev nVec (F : Type) [Field F] (j : Fin 2) : OW F := Pi.single (Sum.inr (Sum.inr j)) 1

abbrev gv (g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) (v : OW F) : OW F :=
  (g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ v

theorem gv_add (g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) (v w : OW F) :
    gv g (v + w) = gv g v + gv g w := Matrix.mulVec_add _ _ _

theorem gv_smul (g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) (t : F) (v : OW F) :
    gv g (t • v) = t • gv g v := Matrix.mulVec_smul _ _ _

theorem gv_sub (g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) (v w : OW F) :
    gv g (v - w) = gv g v - gv g w := Matrix.mulVec_sub _ _ _

theorem gv_zero (g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) : gv g (0 : OW F) = 0 :=
  Matrix.mulVec_zero _

theorem gv_mul (g h : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) (v : OW F) :
    gv (g * h) v = gv g (gv h v) := by
  simp [gv, Units.val_mul, Matrix.mulVec_mulVec]

theorem gv_one (v : OW F) : gv (1 : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) v = v := by
  simp [gv]

theorem gv_inv_gv (g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) (v : OW F) :
    gv g⁻¹ (gv g v) = v := by
  rw [← gv_mul, inv_mul_cancel, gv_one]

theorem gv_gv_inv (g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) (v : OW F) :
    gv g (gv g⁻¹ v) = v := by
  rw [← gv_mul, mul_inv_cancel, gv_one]

theorem polar_gv {g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F}
    (hg : ∀ v : OW F, quadMinus 3 F b c (gv g v) = quadMinus 3 F b c v) (x y : OW F) :
    polar (quadMinus 3 F b c) (gv g x) (gv g y) = polar (quadMinus 3 F b c) x y := by
  show quadMinus 3 F b c (gv g x + gv g y) - quadMinus 3 F b c (gv g x) - quadMinus 3 F b c (gv g y)
    = quadMinus 3 F b c (x + y) - quadMinus 3 F b c x - quadMinus 3 F b c y
  rw [← gv_add, hg, hg, hg]

theorem exists_gl_isometry_apply_eq (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {w₀ w : OW F}
    (hw₀ : w₀ ≠ 0) (hw : w ≠ 0) (hQ : quadMinus 3 F b c w = quadMinus 3 F b c w₀) :
    ∃ G : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F,
      (∀ v : OW F, quadMinus 3 F b c (gv G v) = quadMinus 3 F b c v) ∧ gv G w₀ = w := by
  obtain ⟨g, hg, hgw⟩ := exists_isometry_apply_eq hirr hw₀ hw
    (by rw [← quadMinus_eq_stated, ← quadMinus_eq_stated]; exact hQ)
  refine ⟨(toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).symm g, fun v => ?_, ?_⟩
  · have e : gv ((toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).symm g) v = g v := by
      show (((toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).symm g : GL _ F) : Matrix _ _ F) *ᵥ v
        = g v
      rw [← toLinEquiv_apply, MulEquiv.apply_symm_apply]
    rw [e]
    exact map_of_mem hg v
  · have e : gv ((toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).symm g) w₀ = g w₀ := by
      show (((toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).symm g : GL _ F) : Matrix _ _ F) *ᵥ w₀
        = g w₀
      rw [← toLinEquiv_apply, MulEquiv.apply_symm_apply]
    rw [e]
    exact hgw


abbrev proj0 (x : OW F) : OW F := x - x (Sum.inl idx0) • eV F idx0

theorem proj0_apply_inl0 (x : OW F) : proj0 x (Sum.inl idx0) = 0 := by
  simp [proj0]

theorem proj0_apply_of_ne (x : OW F) {k : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2}
    (hk : k ≠ Sum.inl idx0) : proj0 x k = x k := by
  simp only [proj0, eV, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [Pi.single_eq_of_ne hk, mul_zero, sub_zero]

theorem proj0_of_apply_eq_zero {x : OW F} (hx : x (Sum.inl idx0) = 0) : proj0 x = x := by
  ext k
  simp only [proj0, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hx, zero_mul, sub_zero]

theorem proj0_add (x y : OW F) : proj0 (x + y) = proj0 x + proj0 y := by
  ext k
  simp only [proj0, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem proj0_smul_eV (t : F) : proj0 (t • eV F idx0) = 0 := by
  ext k
  simp [proj0]

theorem eq_proj0_add (x : OW F) : x = proj0 x + x (Sum.inl idx0) • eV F idx0 := by
  simp [proj0]

theorem quad_eV (i : Fin (3 - 1)) : quadMinus 3 F b c (eV F i) = 0 := quadMinus_single_inl i

theorem quad_proj0 {w : OW F} (hw : w (Sum.inr (Sum.inl idx0)) = 0) :
    quadMinus 3 F b c (proj0 w) = quadMinus 3 F b c w := by
  have h : proj0 w = w + (w (Sum.inl idx0)) • eV F idx0 := by
    simp only [proj0]
    rw [sub_eq_add_neg, CharTwo.neg_eq]
  rw [h, QuadraticMap.map_add (quadMinus 3 F b c), map_smul_eq_sq, quad_eV idx0, mul_zero,
    polar_smul_right_eq, polar_e_right, hw]
  ring

theorem gv_apply_y0 {g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F}
    (hg : ∀ v : OW F, quadMinus 3 F b c (gv g v) = quadMinus 3 F b c v)
    (hfix : gv g (eV F idx0) = eV F idx0) (v : OW F) :
    gv g v (Sum.inr (Sum.inl idx0)) = v (Sum.inr (Sum.inl idx0)) := by
  have h1 := polar_gv hg v (eV F idx0)
  rw [hfix, polar_e_right, polar_e_right] at h1
  exact h1

theorem actSP_mem {g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F}
    (hg : ∀ v : OW F, quadMinus 3 F b c (gv g v) = quadMinus 3 F b c v)
    (hfix : gv g (eV F idx0) = eV F idx0) {v : OW F}
    (hv : v (Sum.inl idx0) = 0 ∧ v (Sum.inr (Sum.inl idx0)) = 0 ∧ v ≠ 0 ∧
      quadMinus 3 F b c v = 0) :
    proj0 (gv g v) (Sum.inl idx0) = 0 ∧ proj0 (gv g v) (Sum.inr (Sum.inl idx0)) = 0 ∧
      proj0 (gv g v) ≠ 0 ∧ quadMinus 3 F b c (proj0 (gv g v)) = 0 := by
  obtain ⟨hv1, hv2, hv3, hv4⟩ := hv
  have hy : gv g v (Sum.inr (Sum.inl idx0)) = 0 := by
    rw [gv_apply_y0 hg hfix, hv2]
  refine ⟨proj0_apply_inl0 _, ?_, ?_, ?_⟩
  · rw [proj0_apply_of_ne _ (by simp)]
    exact hy
  · intro h0
    have h1 := eq_proj0_add (gv g v)
    rw [h0, zero_add] at h1
    have hgi : gv g⁻¹ (eV F idx0) = eV F idx0 := by
      conv_lhs => rw [← hfix]
      exact gv_inv_gv g _
    have h2 : v = (gv g v (Sum.inl idx0)) • eV F idx0 := by
      have := congrArg (gv g⁻¹) h1
      rw [gv_inv_gv, gv_smul, hgi] at this
      exact this
    apply hv3
    have h3 := congrFun h2 (Sum.inl idx0)
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h3
    rw [hv1] at h3
    rw [h2, ← h3, zero_smul]
  · rw [quad_proj0 hy, hg, hv4]


theorem exists_fixed_plane_std (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    {E : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F)}
    (hEO : ∀ g ∈ E, ∀ v : OW F, quadMinus 3 F b c (gv g v) = quadMinus 3 F b c v)
    (hE : IsPGroup 2 E) (hfix : ∀ g ∈ E, gv g (eV F idx0) = eV F idx0) :
    ∃ v₁ : OW F, v₁ (Sum.inl idx0) = 0 ∧ v₁ (Sum.inr (Sum.inl idx0)) = 0 ∧ v₁ ≠ 0 ∧
      quadMinus 3 F b c v₁ = 0 ∧ ∀ g ∈ E, ∃ t : F, gv g v₁ = v₁ + t • eV F idx0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI act : MulAction E {v : OW F // v (Sum.inl idx0) = 0 ∧ v (Sum.inr (Sum.inl idx0)) = 0 ∧
      v ≠ 0 ∧ quadMinus 3 F b c v = 0} :=
    { smul := fun g v => ⟨proj0 (gv (g : GL _ F) v.1), actSP_mem (hEO g g.2) (hfix g g.2) v.2⟩
      one_smul := fun v => Subtype.ext (by
        show proj0 (gv ((1 : E) : GL _ F) v.1) = v.1
        rw [Subgroup.coe_one, gv_one]
        exact proj0_of_apply_eq_zero v.2.1)
      mul_smul := fun g h v => Subtype.ext (by
        show proj0 (gv ((g * h : E) : GL _ F) v.1) =
          proj0 (gv (g : GL _ F) (proj0 (gv (h : GL _ F) v.1)))
        rw [Subgroup.coe_mul, gv_mul]
        set w := gv (h : GL _ F) v.1 with hw
        conv_lhs => rw [eq_proj0_add w]
        rw [gv_add, gv_smul, hfix g g.2, proj0_add, proj0_smul_eV, add_zero]) }
  have hS := not_two_dvd_card_singPerpSet hirr hF hn
  obtain ⟨v, hv⟩ := hE.nonempty_fixed_point_of_prime_not_dvd_card _ hS
  refine ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2, fun g hg => ?_⟩
  have h := congrArg Subtype.val (MulAction.mem_fixedPoints.mp hv ⟨g, hg⟩)
  refine ⟨gv g v.1 (Sum.inl idx0), ?_⟩
  have h2 := eq_proj0_add (gv g v.1)
  have h3 : proj0 (gv g v.1) = v.1 := h
  rw [h3] at h2
  exact h2

theorem not_two_dvd_card_nonzero_singular (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) :
    ¬ 2 ∣ Nat.card {v : OW F // v ≠ 0 ∧ quadMinus 3 F b c v = 0} := by
  have hcard : (Nat.card {v : OW F // quadMinus 3 F b c v = 0} : ℤ) =
      1 + ((Nat.card F : ℤ) ^ 3 + 1) * ((Nat.card F : ℤ) ^ 2 - 1) :=
    (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus 2 hirr).1
  have hsucc : Nat.card {v : OW F // quadMinus 3 F b c v = 0} =
      Nat.card {v : OW F // v ≠ 0 ∧ quadMinus 3 F b c v = 0} + 1 :=
    CFSG.StandardType.OrthRestEnd.card_singular_eq_succ (quadMinus 3 F b c)
  have hN : (Nat.card {v : OW F // v ≠ 0 ∧ quadMinus 3 F b c v = 0} : ℤ) =
      ((Nat.card F : ℤ) ^ 3 + 1) * ((Nat.card F : ℤ) ^ 2 - 1) := by
    have h := hcard
    rw [hsucc] at h
    push_cast at h
    linarith
  have hev : Even (Nat.card F) := by
    rw [hF]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hevZ : Even (Nat.card F : ℤ) := (Int.even_coe_nat _).mpr hev
  have hodd : Odd (((Nat.card F : ℤ) ^ 3 + 1) * ((Nat.card F : ℤ) ^ 2 - 1)) :=
    Odd.mul ((hevZ.pow_of_ne_zero (by norm_num)).add_one)
      ((hevZ.pow_of_ne_zero (by norm_num)).sub_odd odd_one)
  intro hdvd
  have h2 : (2 : ℤ) ∣ (Nat.card {v : OW F // v ≠ 0 ∧ quadMinus 3 F b c v = 0} : ℤ) := by
    exact_mod_cast hdvd
  rw [hN] at h2
  exact (Int.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem exists_fixed_singular_iso (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    {E : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F)}
    (hEO : ∀ g ∈ E, ∀ v : OW F, quadMinus 3 F b c (gv g v) = quadMinus 3 F b c v)
    (hE : IsPGroup 2 E) :
    ∃ w : OW F, w ≠ 0 ∧ quadMinus 3 F b c w = 0 ∧ ∀ g ∈ E, gv g w = w := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.StandardType.OrthRestEnd.exists_fixed_singular (quadMinus 3 F b c) E hE hEO
    (not_two_dvd_card_nonzero_singular hirr hF hn)


theorem eV_ne_zero : eV F idx0 ≠ 0 := by
  intro h
  have := congrFun h (Sum.inl idx0)
  simp at this

theorem exists_fixed_plane (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    {E : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F)}
    (hEO : ∀ g ∈ E, ∀ v : OW F, quadMinus 3 F b c (gv g v) = quadMinus 3 F b c v)
    (hE : IsPGroup 2 E) :
    ∃ w u : OW F, w ≠ 0 ∧ LinearIndependent F ![w, u] ∧ quadMinus 3 F b c w = 0 ∧
      quadMinus 3 F b c u = 0 ∧ polar (quadMinus 3 F b c) w u = 0 ∧
      ∀ g ∈ E, ∃ t : F, gv g w = w ∧ gv g u = u + t • w := by
  obtain ⟨w, hw0, hw, hwfix⟩ := exists_fixed_singular_iso hirr hF hn hEO hE
  obtain ⟨G, hG, hGe⟩ := exists_gl_isometry_apply_eq hirr (eV_ne_zero (F := F)) hw0
    (by rw [hw, quad_eV idx0])
  let E' : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :=
    E.map (MulAut.conj G⁻¹).toMonoidHom
  have hGinv : ∀ v : OW F, quadMinus 3 F b c (gv G⁻¹ v) = quadMinus 3 F b c v := by
    intro v
    conv_rhs => rw [← gv_gv_inv G v]
    rw [hG]
  have hE'O : ∀ g ∈ E', ∀ v : OW F, quadMinus 3 F b c (gv g v) = quadMinus 3 F b c v := by
    rintro _ ⟨g, hg, rfl⟩ v
    show quadMinus 3 F b c (gv (G⁻¹ * g * G⁻¹⁻¹) v) = quadMinus 3 F b c v
    rw [inv_inv, gv_mul, gv_mul, hGinv, hEO g hg, hG]
  have hE'p : IsPGroup 2 E' := hE.map _
  have hE'fix : ∀ g ∈ E', gv g (eV F idx0) = eV F idx0 := by
    rintro _ ⟨g, hg, rfl⟩
    show gv (G⁻¹ * g * G⁻¹⁻¹) (eV F idx0) = eV F idx0
    rw [inv_inv, gv_mul, gv_mul, hGe, hwfix g hg]
    rw [← hGe]
    exact gv_inv_gv G _
  obtain ⟨v₁, h1, h2, h3, h4, h5⟩ := exists_fixed_plane_std hirr hF hn hE'O hE'p hE'fix
  refine ⟨w, gv G v₁, hw0, ?_, hw, ?_, ?_, fun g hg => ?_⟩
  ·
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h0 := congrArg (gv G⁻¹) hst
    rw [gv_add, gv_smul, gv_smul, gv_inv_gv, ← hGe, gv_inv_gv, gv_zero] at h0
    have hx := congrFun h0 (Sum.inl idx0)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one, h1, mul_zero,
      add_zero, Pi.zero_apply] at hx
    refine ⟨hx, ?_⟩
    rw [hx, zero_smul, zero_add] at h0
    rcases smul_eq_zero.mp h0 with ht | ht
    · exact ht
    · exact absurd ht h3
  · rw [hG]
    exact h4
  · rw [← hGe, polar_gv hG]
    rw [polar_comm, polar_e_right, h2]
  · obtain ⟨t, ht⟩ := h5 (G⁻¹ * g * G) ⟨g, hg, by simp [MulAut.conj_apply]⟩
    refine ⟨t, hwfix g hg, ?_⟩
    have e : gv G (gv (G⁻¹ * g * G) v₁) = gv g (gv G v₁) := by
      rw [← gv_mul, show G * (G⁻¹ * g * G) = g * G by group, gv_mul]
    rw [← e, ht, gv_add, gv_smul, hGe]

end Plane

end CFSG.LocalAnalysis.RankThreeUC
