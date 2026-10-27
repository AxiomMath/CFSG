module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OOutA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16ONorm

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus nondegenerate_polarBilin_quadMinus_of_finite
  quadMinus_apply polar_quadMinus)

namespace OutLin

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem outIsoConj_mem_omega {G : GL6 F}
    (hG : ∀ v : OW F, quadMinus 3 F b c (gv G v) = quadMinus 3 F b c v) {h : GL6 F}
    (hh : h ∈ StatedOmega (StatedQuadMinus 3 F b c)) :
    G * h * G⁻¹ ∈ StatedOmega (StatedQuadMinus 3 F b c) := by
  rw [mem_statedOmega_iff] at hh ⊢
  set T := toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F with hT
  set O := orthogonalGroup (quadMinus 3 F b c) with hO
  have hγ : T G ∈ O := by
    rw [hO, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    rw [hT, toLinEquiv_apply]
    exact hG x
  have hmap : Subgroup.map (MulAut.conj (T G)).toMonoidHom O = O := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact O.mul_mem (O.mul_mem hγ hy) (O.inv_mem hγ)
    · intro hx
      refine ⟨(T G)⁻¹ * x * (T G), O.mul_mem (O.mul_mem (O.inv_mem hγ) hx) hγ, ?_⟩
      show T G * ((T G)⁻¹ * x * (T G)) * (T G)⁻¹ = x
      group
  have hcomm := Subgroup.map_commutator O O (MulAut.conj (T G)).toMonoidHom
  rw [hmap] at hcomm
  have hmem : (MulAut.conj (T G)).toMonoidHom (T h) ∈ ⁅O, O⁆ := by
    rw [← hcomm]
    exact Subgroup.mem_map_of_mem _ hh
  rw [map_mul, map_mul, map_inv]
  exact hmem


theorem exists_eichler_move (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {u y : OW F}
    (hu : quadMinus 3 F b c u = 0) (hy : quadMinus 3 F b c y = 0)
    (hux : polar (quadMinus 3 F b c) u (eV F idx1) = 1) (huy : polar (quadMinus 3 F b c) u y = 1)
    (hu0 : u (Sum.inr (Sum.inl idx0)) = 0) (hy0 : y (Sum.inr (Sum.inl idx0)) = 0) :
    ∃ G₂ : GL6 F, (∀ v : OW F, quadMinus 3 F b c (gv G₂ v) = quadMinus 3 F b c v) ∧
      gv G₂ (eV F idx0) = eV F idx0 ∧ gv G₂ (eV F idx1) = y := by
  set w : OW F := (1 : F)⁻¹ • (y - eV F idx1) with hw
  obtain ⟨A, hA, hAx⟩ := eichler_mem_statedOmega hirr u w
  have hmove := eichler_apply_eq_of_polar_eq (Q := quadMinus 3 F b c) hu (x := eV F idx1) (y := y)
    (by rw [quad_eV, hy]) hux huy one_ne_zero
  refine ⟨A, fun v => quadMinus_mulVec_of_mem_statedOmega hA v, ?_, ?_⟩
  · have h1 : polar (quadMinus 3 F b c) (eV F idx0) u = 0 := by
      rw [polar_comm, polar_e_right, hu0]
    have h2 : polar (quadMinus 3 F b c) (eV F idx0) w = 0 := by
      rw [hw, polar_smul_right_eq, polar_sub_right, polar_comm _ (eV F idx0) y, polar_e_right, hy0,
        polar_e_right]
      simp [eV_inr]
    show (A : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
      eV F idx0 = eV F idx0
    rw [hAx, eichler_apply_of_polar_eq_zero (hxu := h1) (hxw := h2)]
  · show (A : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
      eV F idx1 = y
    rw [hAx]
    exact hmove

theorem exists_plane_iso (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {u' : OW F}
    (hy0 : u' (Sum.inr (Sum.inl idx0)) = 0) (hQ : quadMinus 3 F b c u' = 0)
    (hne : u' (Sum.inl idx1) ≠ 0 ∨ u' (Sum.inr (Sum.inl idx1)) ≠ 0) :
    ∃ (G₂ : GL6 F) (lam : F), lam ≠ 0 ∧
      (∀ v : OW F, quadMinus 3 F b c (gv G₂ v) = quadMinus 3 F b c v) ∧
      gv G₂ (eV F idx0) = eV F idx0 ∧ gv G₂ (eV F idx1) = lam • u' := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  by_cases hx : u' (Sum.inl idx1) = 0
  ·
    have hy : u' (Sum.inr (Sum.inl idx1)) ≠ 0 := hne.resolve_left (not_not.mpr hx)
    have hn : u' (Sum.inr (Sum.inr 0)) = 0 ∧ u' (Sum.inr (Sum.inr 1)) = 0 := by
      have hQ' := hQ
      rw [Q_coords, hy0, hx] at hQ'
      exact binary_eq_zero_of_irreducible hirr (by linear_combination hQ')
    obtain ⟨hn0, hn1⟩ := hn
    set u : OW F := eV F idx1 + fV F idx1 + nVec F 0 with hu
    have hne01 : idx0 ≠ idx1 := by decide
    have hne10 : idx1 ≠ idx0 := by decide
    have hu1 : u (Sum.inl idx0) = 0 := by
      simp [hu, eV_ne (i := idx1) (k := idx0) hne01, fV_inl, nVec_inl]
    have hu2 : u (Sum.inl idx1) = 1 := by simp [hu, eV_self, fV_inl, nVec_inl]
    have hu3 : u (Sum.inr (Sum.inl idx0)) = 0 := by
      simp [hu, eV_inr, fV_ne hne10, nVec_inr_inl]
    have hu4 : u (Sum.inr (Sum.inl idx1)) = 1 := by
      simp [hu, eV_inr, fV_self, nVec_inr_inl]
    have hu5 : u (Sum.inr (Sum.inr 0)) = 1 := by simp [hu, eV_inr, fV_inr_inr, nVec_00]
    have hu6 : u (Sum.inr (Sum.inr 1)) = 0 := by simp [hu, eV_inr, fV_inr_inr, nVec_01]
    set y : OW F := (u' (Sum.inr (Sum.inl idx1)))⁻¹ • u' with hyd
    have hQu : quadMinus 3 F b c u = 0 := by
      rw [Q_coords, hu1, hu2, hu3, hu4, hu5, hu6]
      linear_combination h2
    have hQy : quadMinus 3 F b c y = 0 := by rw [hyd, map_smul_eq_sq, hQ, mul_zero]
    have hy0' : y (Sum.inr (Sum.inl idx0)) = 0 := by
      rw [hyd, Pi.smul_apply, smul_eq_mul, hy0, mul_zero]
    have hux : polar (quadMinus 3 F b c) u (eV F idx1) = 1 := by rw [polar_e_right, hu4]
    have hpol : polar (quadMinus 3 F b c) u u' = u' (Sum.inr (Sum.inl idx1)) := by
      rw [polar_coords, hu1, hu2, hu3, hu4, hu5, hu6, hy0, hx, hn0, hn1]
      ring
    have huy : polar (quadMinus 3 F b c) u y = 1 := by
      rw [hyd, polar_smul_right_eq, hpol, inv_mul_cancel₀ hy]
    obtain ⟨G₂, hG₂, hG₂0, hG₂1⟩ := exists_eichler_move hirr hQu hQy hux huy hu3 hy0'
    exact ⟨G₂, (u' (Sum.inr (Sum.inl idx1)))⁻¹, inv_ne_zero hy, hG₂, hG₂0, hG₂1⟩
  · set y : OW F := (u' (Sum.inl idx1))⁻¹ • u' with hyd
    have hQy : quadMinus 3 F b c y = 0 := by rw [hyd, map_smul_eq_sq, hQ, mul_zero]
    have hy0' : y (Sum.inr (Sum.inl idx0)) = 0 := by
      rw [hyd, Pi.smul_apply, smul_eq_mul, hy0, mul_zero]
    have hQu : quadMinus 3 F b c (fV F idx1) = 0 := quadMinus_single_inr idx1
    have hux : polar (quadMinus 3 F b c) (fV F idx1) (eV F idx1) = 1 := by
      rw [polar_e_right, fV_self]
    have huy : polar (quadMinus 3 F b c) (fV F idx1) y = 1 := by
      rw [hyd, polar_smul_right_eq, polar_comm, polar_f_right, inv_mul_cancel₀ hx]
    have hu0 : (fV F idx1) (Sum.inr (Sum.inl idx0)) = 0 := fV_ne (by decide)
    obtain ⟨G₂, hG₂, hG₂0, hG₂1⟩ := exists_eichler_move hirr hQu hQy hux huy hu0 hy0'
    exact ⟨G₂, (u' (Sum.inl idx1))⁻¹, inv_ne_zero hx, hG₂, hG₂0, hG₂1⟩


theorem exists_std_conj (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : 1 ≤ n) {E : Subgroup (GL6 F)}
    (hEO : ∀ g ∈ E, ∀ v : OW F, quadMinus 3 F b c (gv g v) = quadMinus 3 F b c v)
    (hE : IsPGroup 2 E) :
    ∃ G : GL6 F, (∀ v : OW F, quadMinus 3 F b c (gv G v) = quadMinus 3 F b c v) ∧
      ∀ g ∈ E, PEl b c (G⁻¹ * g * G) := by
  obtain ⟨w, u, hw0, hli, hwQ, huQ, hwu, hfix⟩ := exists_fixed_plane hirr hF hn hEO hE
  obtain ⟨G₁, hG₁, hG₁e⟩ := exists_gl_isometry_apply_eq hirr (eV_ne_zero (F := F)) hw0
    (by rw [hwQ, quad_eV idx0])
  have hG₁inv : ∀ v : OW F, quadMinus 3 F b c (gv G₁⁻¹ v) = quadMinus 3 F b c v := by
    intro v
    conv_rhs => rw [← gv_gv_inv G₁ v]
    rw [hG₁]
  have hG₁w : gv G₁⁻¹ w = eV F idx0 := by rw [← hG₁e, gv_inv_gv]
  set u' : OW F := gv G₁⁻¹ u with hu'
  have hQu' : quadMinus 3 F b c u' = 0 := by rw [hu', hG₁inv, huQ]
  have hy0 : u' (Sum.inr (Sum.inl idx0)) = 0 := by
    have h1 := polar_gv hG₁inv u w
    rw [hG₁w, polar_e_right, polar_comm, hwu] at h1
    exact h1
  have hne : u' (Sum.inl idx1) ≠ 0 ∨ u' (Sum.inr (Sum.inl idx1)) ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    obtain ⟨hx, hy⟩ := hcon
    have hn : u' (Sum.inr (Sum.inr 0)) = 0 ∧ u' (Sum.inr (Sum.inr 1)) = 0 := by
      have hQ' := hQu'
      rw [Q_coords, hy0, hx, hy] at hQ'
      have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
      exact binary_eq_zero_of_irreducible hirr (by linear_combination hQ')
    obtain ⟨hn0, hn1⟩ := hn
    have hu'e : u' = u' (Sum.inl idx0) • eV F idx0 := by
      have := vec_decomp u'
      rw [hx, hy0, hy, hn0, hn1] at this
      simpa using this
    have hu_eq : u = u' (Sum.inl idx0) • w := by
      have := congrArg (gv G₁) hu'e
      rw [hu', gv_gv_inv, gv_smul, hG₁e] at this
      exact this
    have := (LinearIndependent.pair_iff.mp hli) (u' (Sum.inl idx0)) (-1) (by
      rw [hu_eq]
      module)
    exact absurd this.2 (neg_ne_zero.mpr one_ne_zero)
  obtain ⟨G₂, lam, hlam, hG₂, hG₂e0, hG₂e1⟩ := exists_plane_iso hirr hy0 hQu' hne
  set G : GL6 F := G₁ * G₂ with hGdef
  have hGiso : ∀ v : OW F, quadMinus 3 F b c (gv G v) = quadMinus 3 F b c v := fun v => by
    rw [hGdef, gv_mul, hG₁, hG₂]
  have hGinv : ∀ v : OW F, quadMinus 3 F b c (gv G⁻¹ v) = quadMinus 3 F b c v := by
    intro v
    conv_rhs => rw [← gv_gv_inv G v]
    rw [hGiso]
  have hGe0 : gv G (eV F idx0) = w := by rw [hGdef, gv_mul, hG₂e0, hG₁e]
  have hGe1 : gv G (eV F idx1) = lam • u := by
    rw [hGdef, gv_mul, hG₂e1, gv_smul, hu', gv_gv_inv]
  refine ⟨G, hGiso, fun g hg => ?_⟩
  obtain ⟨t, hgw, hgu⟩ := hfix g hg
  have hG'w : gv G⁻¹ w = eV F idx0 := by rw [← hGe0, gv_inv_gv]
  have hG'u : gv G⁻¹ (lam • u) = eV F idx1 := by rw [← hGe1, gv_inv_gv]
  refine PEl.mk' (t := lam * t) ?_ ?_ ?_
  · intro v
    rw [gv_mul, gv_mul, hGinv, hEO g hg, hGiso]
  · rw [gv_mul, gv_mul, hGe0, hgw, hG'w]
  · rw [gv_mul, gv_mul, hGe1, gv_smul, hgu, smul_add, smul_smul, gv_add, hG'u, gv_smul, hG'w]

end OutLin

end CFSG.LocalAnalysis.RankThreeUC
