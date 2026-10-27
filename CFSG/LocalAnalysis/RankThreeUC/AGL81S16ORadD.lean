module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16ORad
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16ONorm

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus nondegenerate_polarBilin_quadMinus_of_finite
  quadMinus_apply polar_quadMinus)

section RadD

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

@[expose] def nMap (a b' c' d : F) : OW F →ₗ[F] OW F where
  toFun x := nvec F (a * x (Sum.inr (Sum.inr 0)) + b' * x (Sum.inr (Sum.inr 1)))
    (c' * x (Sum.inr (Sum.inr 0)) + d * x (Sum.inr (Sum.inr 1)))
  map_add' x y := by
    have hj : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
    ext k
    rcases k with i | i | j
    · simp only [Pi.add_apply, nvec_inl, add_zero]
    · simp only [Pi.add_apply, nvec_inr_inl, add_zero]
    · rcases hj j with rfl | rfl
      · simp only [Pi.add_apply, nvec_n0]; ring
      · simp only [Pi.add_apply, nvec_n1]; ring
  map_smul' r x := by
    have hj : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
    ext k
    rcases k with i | i | j
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, nvec_inl, mul_zero]
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, nvec_inr_inl, mul_zero]
    · rcases hj j with rfl | rfl
      · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, nvec_n0]; ring
      · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, nvec_n1]; ring

theorem nMap_inl (a b' c' d : F) (x : OW F) (i : Fin (3 - 1)) :
    nMap a b' c' d x (Sum.inl i) = 0 := nvec_inl _ _ i

theorem nMap_inr_inl (a b' c' d : F) (x : OW F) (i : Fin (3 - 1)) :
    nMap a b' c' d x (Sum.inr (Sum.inl i)) = 0 := nvec_inr_inl _ _ i

theorem nMap_n0 (a b' c' d : F) (x : OW F) :
    nMap a b' c' d x (Sum.inr (Sum.inr 0)) =
      a * x (Sum.inr (Sum.inr 0)) + b' * x (Sum.inr (Sum.inr 1)) := nvec_n0 _ _

theorem nMap_n1 (a b' c' d : F) (x : OW F) :
    nMap a b' c' d x (Sum.inr (Sum.inr 1)) =
      c' * x (Sum.inr (Sum.inr 0)) + d * x (Sum.inr (Sum.inr 1)) := nvec_n1 _ _

theorem exists_ell (ν00 ν01 ν10 ν11 : F)
    (hnil : ν00 * ν00 + ν01 * ν10 = 0 ∧ ν00 * ν01 + ν01 * ν11 = 0 ∧
      ν10 * ν00 + ν11 * ν10 = 0 ∧ ν10 * ν01 + ν11 * ν11 = 0)
    (hiso : ∀ p q : F, (p + (ν00 * p + ν01 * q)) ^ 2 + b * (p + (ν00 * p + ν01 * q)) *
        (q + (ν10 * p + ν11 * q)) + c * (q + (ν10 * p + ν11 * q)) ^ 2 =
      p ^ 2 + b * p * q + c * q ^ 2) :
    ∃ L : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F,
      (∀ x, gv L x = x + nMap ν00 ν01 ν10 ν11 x) ∧
        ∀ v : OW F, quadMinus 3 F b c (gv L v) = quadMinus 3 F b c v := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨n1, n2, n3, n4⟩ := hnil
  have hj : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
  let Llin : OW F →ₗ[F] OW F := LinearMap.id + nMap ν00 ν01 ν10 ν11
  have hLapp : ∀ x, Llin x = x + nMap ν00 ν01 ν10 ν11 x := fun x => rfl
  have hinv : Function.Involutive Llin := by
    intro x
    rw [hLapp, hLapp]
    ext k
    rcases k with i | i | j
    · simp only [Pi.add_apply, nMap_inl, add_zero]
    · simp only [Pi.add_apply, nMap_inr_inl, add_zero]
    · rcases hj j with rfl | rfl
      · simp only [Pi.add_apply, nMap_n0, nMap_n1]
        linear_combination (x (Sum.inr (Sum.inr 0))) * n1 + (x (Sum.inr (Sum.inr 1))) * n2 +
          (ν00 * x (Sum.inr (Sum.inr 0)) + ν01 * x (Sum.inr (Sum.inr 1))) * h2
      · simp only [Pi.add_apply, nMap_n0, nMap_n1]
        linear_combination (x (Sum.inr (Sum.inr 0))) * n3 + (x (Sum.inr (Sum.inr 1))) * n4 +
          (ν10 * x (Sum.inr (Sum.inr 0)) + ν11 * x (Sum.inr (Sum.inr 1))) * h2
  let Leq : OW F ≃ₗ[F] OW F := LinearEquiv.ofInvolutive Llin hinv
  refine ⟨(toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).symm Leq, fun x => ?_, fun v => ?_⟩
  · show gv ((toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).symm Leq) x = _
    show (((toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).symm Leq :
      GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
        (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x = _
    rw [← toLinEquiv_apply, MulEquiv.apply_symm_apply]
    rfl
  · have e : gv ((toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).symm Leq) v =
        v + nMap ν00 ν01 ν10 ν11 v := by
      show (((toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).symm Leq :
        GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ v = _
      rw [← toLinEquiv_apply, MulEquiv.apply_symm_apply]
      rfl
    rw [e, Q_coords, Q_coords]
    simp only [Pi.add_apply, nMap_inl, nMap_inr_inl, nMap_n0, nMap_n1, add_zero]
    linear_combination hiso (v (Sum.inr (Sum.inr 0))) (v (Sum.inr (Sum.inr 1)))


theorem nMap_eq (a b' c' d : F) (x : OW F) :
    nMap a b' c' d x = x (Sum.inr (Sum.inr 0)) • nvec F a c' + x (Sum.inr (Sum.inr 1)) • nvec F b' d := by
  have hj : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
  ext k
  rcases k with i | i | j
  · simp only [nMap_inl, Pi.add_apply, Pi.smul_apply, smul_eq_mul, nvec_inl, mul_zero, add_zero]
  · simp only [nMap_inr_inl, Pi.add_apply, Pi.smul_apply, smul_eq_mul, nvec_inr_inl, mul_zero,
      add_zero]
  · rcases hj j with rfl | rfl
    · simp only [nMap_n0, Pi.add_apply, Pi.smul_apply, smul_eq_mul, nvec_n0]; ring
    · simp only [nMap_n1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, nvec_n1]; ring

theorem nvec_zero : nvec F (0 : F) 0 = 0 := by
  ext k
  rcases k with i | i | j
  · exact nvec_inl _ _ i
  · exact nvec_inr_inl _ _ i
  · have hj : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
    rcases hj j with rfl | rfl
    · rw [nvec_n0]; rfl
    · rw [nvec_n1]; rfl

theorem ell_trivial (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {L : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F} (hLΩ : L ∈ StatedOmega (StatedQuadMinus 3 F b c))
    (ν00 ν01 ν10 ν11 : F)
    (hnil : ν00 * ν00 + ν01 * ν10 = 0 ∧ ν00 * ν01 + ν01 * ν11 = 0 ∧
      ν10 * ν00 + ν11 * ν10 = 0 ∧ ν10 * ν01 + ν11 * ν11 = 0)
    (hL : ∀ x, gv L x = x + nMap ν00 ν01 ν10 ν11 x) :
    ν00 = 0 ∧ ν01 = 0 ∧ ν10 = 0 ∧ ν11 = 0 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨n1, n2, n3, n4⟩ := hnil
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr
  have hLo := (mem_statedOmega_iff L).mp hLΩ
  rw [← omegaGroup_eq_commutator hQ (quadMinus_three_derived hirr).1] at hLo
  have hev := hLo.2
  have hcomm : CFSG.RankThree.OrthogonalInvolutions.commSpace
      (toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F L) =
      LinearMap.range (nMap ν00 ν01 ν10 ν11) := by
    show LinearMap.range (((toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F L :
      OW F ≃ₗ[F] OW F) : OW F →ₗ[F] OW F) - 1) = _
    refine congrArg LinearMap.range (LinearMap.ext fun x => ?_)
    show (toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F L) x - x = nMap ν00 ν01 ν10 ν11 x
    rw [toLinEquiv_apply]
    show gv L x - x = _
    rw [hL x, add_sub_cancel_left]
  rw [hcomm] at hev
  have hdiag : ν00 = ν11 := by
    have hsq : (ν00 + ν11) ^ 2 = 0 := by
      linear_combination n1 + n4 + (ν00 * ν11 - ν01 * ν10) * h2
    have hsum : ν00 + ν11 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hsq
    linear_combination hsum - ν11 * h2
  have hdet : ν00 * ν11 = ν01 * ν10 := by
    rw [← hdiag]
    linear_combination n1 - ν01 * ν10 * h2
  have hspan : ∃ (w : OW F) (s t : F), ∀ x : OW F, nMap ν00 ν01 ν10 ν11 x =
      (x (Sum.inr (Sum.inr 0)) * s + x (Sum.inr (Sum.inr 1)) * t) • w := by
    by_cases hA : ν00 = 0
    · by_cases hB : ν10 = 0
      · refine ⟨nvec F ν01 ν11, 0, 1, fun x => ?_⟩
        rw [nMap_eq, hA, hB]
        have h0 : nvec F (0 : F) 0 = 0 := nvec_zero
        rw [h0, smul_zero, zero_add, mul_zero, mul_one, zero_add]
      · have hB' : ν01 = 0 := by
          have : ν01 * ν10 = 0 := by rw [hA] at n1; linear_combination n1
          exact (mul_eq_zero.mp this).resolve_right hB
        have hC : ν11 = 0 := by rw [← hdiag]; exact hA
        refine ⟨nvec F ν00 ν10, 1, 0, fun x => ?_⟩
        rw [nMap_eq, hB', hC]
        have h0 : nvec F (0 : F) 0 = 0 := nvec_zero
        rw [h0, smul_zero, add_zero, mul_zero, mul_one, add_zero]
    · refine ⟨nvec F ν00 ν10, 1, ν01 / ν00, fun x => ?_⟩
      rw [nMap_eq, add_smul]
      have hv : nvec F ν01 ν11 = (ν01 / ν00) • nvec F ν00 ν10 := by
        have hj : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
        ext k
        rcases k with i | i | j
        · simp only [nvec_inl, Pi.smul_apply, smul_eq_mul, mul_zero]
        · simp only [nvec_inr_inl, Pi.smul_apply, smul_eq_mul, mul_zero]
        · rcases hj j with rfl | rfl
          · simp only [nvec_n0, Pi.smul_apply, smul_eq_mul]
            field_simp
          · simp only [nvec_n1, Pi.smul_apply, smul_eq_mul]
            field_simp
            linear_combination hdet
      rw [hv, smul_smul, mul_one]
  have hle : Module.finrank F (LinearMap.range (nMap ν00 ν01 ν10 ν11)) ≤ 1 := by
    obtain ⟨w, s, t, hw⟩ := hspan
    have hsub : LinearMap.range (nMap ν00 ν01 ν10 ν11) ≤ Submodule.span F {w} := by
      rintro _ ⟨x, rfl⟩
      rw [hw x]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
    calc Module.finrank F (LinearMap.range (nMap ν00 ν01 ν10 ν11))
        ≤ Module.finrank F (Submodule.span F ({w} : Set (OW F))) := Submodule.finrank_mono hsub
      _ ≤ 1 := by simpa using finrank_span_le_card ({w} : Set (OW F))
  have h0 : Module.finrank F (LinearMap.range (nMap ν00 ν01 ν10 ν11)) = 0 := by
    obtain ⟨k, hk⟩ := hev
    rw [hk] at hle ⊢
    omega
  have hbot : LinearMap.range (nMap ν00 ν01 ν10 ν11) = ⊥ := Submodule.finrank_eq_zero.mp h0
  have hz : nMap ν00 ν01 ν10 ν11 = 0 := LinearMap.range_eq_bot.mp hbot
  have e0 := congrArg (fun f : OW F →ₗ[F] OW F => f (nVec F 0)) hz
  have e1 := congrArg (fun f : OW F →ₗ[F] OW F => f (nVec F 1)) hz
  simp only [LinearMap.zero_apply] at e0 e1
  have a0 := congrFun e0 (Sum.inr (Sum.inr 0))
  have a1 := congrFun e0 (Sum.inr (Sum.inr 1))
  have b0 := congrFun e1 (Sum.inr (Sum.inr 0))
  have b1 := congrFun e1 (Sum.inr (Sum.inr 1))
  rw [nMap_n0, nVec_00, nVec_01] at a0
  rw [nMap_n1, nVec_00, nVec_01] at a1
  rw [nMap_n0, nVec_10, nVec_11] at b0
  rw [nMap_n1, nVec_10, nVec_11] at b1
  refine ⟨by simpa using a0, by simpa using b0, by simpa using a1, by simpa using b1⟩


theorem rho_trivial (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F} (hgΩ : g ∈ StatedOmega (StatedQuadMinus 3 F b c))
    (hg2 : g * g = 1) (hfix : ∀ i : Fin (3 - 1), gv g (eV F i) = eV F i) :
    ∀ z : OW F, (∀ i : Fin (3 - 1), z (Sum.inr (Sum.inl i)) = 0) →
      ∀ j : Fin 2, (gv g z - z) (Sum.inr (Sum.inr j)) = 0 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hne01 : idx0 ≠ idx1 := by decide
  have hiso : ∀ v : OW F, quadMinus 3 F b c (gv g v) = quadMinus 3 F b c v :=
    fun v => quadMinus_mulVec_of_mem_statedOmega hgΩ v
  have hV : ∀ (x : OW F) (i : Fin (3 - 1)),
      gv g x (Sum.inr (Sum.inl i)) = x (Sum.inr (Sum.inl i)) := by
    intro x i
    have h1 := polar_gv hiso x (eV F i)
    rw [hfix, polar_e_right, polar_e_right] at h1
    exact h1
  have hinv : ∀ x : OW F, gv g (gv g x) = x := fun x => by rw [← gv_mul, hg2, gv_one]
  have hn : ∀ z : OW F, (∀ i : Fin (3 - 1), z (Sum.inr (Sum.inl i)) = 0) → ∀ j : Fin 2,
      gv g z (Sum.inr (Sum.inr j)) =
      z (Sum.inr (Sum.inr 0)) * gv g (nVec F 0) (Sum.inr (Sum.inr j)) +
        z (Sum.inr (Sum.inr 1)) * gv g (nVec F 1) (Sum.inr (Sum.inr j)) := by
    intro z hz j
    rw [gv_apply_decomp, hfix, hfix, hz idx0, hz idx1]
    simp only [eV_inr, zero_mul, mul_zero, add_zero, zero_add]
  have hnV : ∀ j : Fin 2, ∀ i : Fin (3 - 1), nVec F j (Sum.inr (Sum.inl i)) = 0 :=
    fun j i => nVec_inr_inl j i
  have hZg : ∀ j : Fin 2, ∀ i : Fin (3 - 1), gv g (nVec F j) (Sum.inr (Sum.inl i)) = 0 := fun j i => by
    rw [hV, nVec_inr_inl]
  have hQn0 : (gv g (nVec F 0) (Sum.inr (Sum.inr 0))) ^ 2 +
      b * gv g (nVec F 0) (Sum.inr (Sum.inr 0)) * gv g (nVec F 0) (Sum.inr (Sum.inr 1)) +
      c * (gv g (nVec F 0) (Sum.inr (Sum.inr 1))) ^ 2 = 1 := by
    have h := hiso (nVec F 0)
    rw [Q_coords, Q_coords, hV (nVec F 0) idx0, hV (nVec F 0) idx1] at h
    simp only [nVec_inl, nVec_inr_inl, nVec_00, nVec_01] at h
    linear_combination h
  have hQn1 : (gv g (nVec F 1) (Sum.inr (Sum.inr 0))) ^ 2 +
      b * gv g (nVec F 1) (Sum.inr (Sum.inr 0)) * gv g (nVec F 1) (Sum.inr (Sum.inr 1)) +
      c * (gv g (nVec F 1) (Sum.inr (Sum.inr 1))) ^ 2 = c := by
    have h := hiso (nVec F 1)
    rw [Q_coords, Q_coords, hV (nVec F 1) idx0, hV (nVec F 1) idx1] at h
    simp only [nVec_inl, nVec_inr_inl, nVec_10, nVec_11] at h
    linear_combination h
  have hpol : b * (gv g (nVec F 0) (Sum.inr (Sum.inr 0)) * gv g (nVec F 1) (Sum.inr (Sum.inr 1)) +
      gv g (nVec F 1) (Sum.inr (Sum.inr 0)) * gv g (nVec F 0) (Sum.inr (Sum.inr 1))) = b := by
    have h := polar_gv hiso (nVec F 0) (nVec F 1)
    rw [polar_coords, polar_coords, hV (nVec F 0) idx0, hV (nVec F 0) idx1, hV (nVec F 1) idx0,
      hV (nVec F 1) idx1] at h
    simp only [nVec_inl, nVec_inr_inl, nVec_00, nVec_01, nVec_10, nVec_11] at h
    linear_combination h
  have hI1 : gv g (nVec F 0) (Sum.inr (Sum.inr 0)) * gv g (nVec F 0) (Sum.inr (Sum.inr 0)) +
      gv g (nVec F 0) (Sum.inr (Sum.inr 1)) * gv g (nVec F 1) (Sum.inr (Sum.inr 0)) = 1 := by
    have h := congrFun (hinv (nVec F 0)) (Sum.inr (Sum.inr 0))
    rw [hn _ (hZg 0) 0, nVec_00] at h
    exact h
  have hI2 : gv g (nVec F 0) (Sum.inr (Sum.inr 0)) * gv g (nVec F 0) (Sum.inr (Sum.inr 1)) +
      gv g (nVec F 0) (Sum.inr (Sum.inr 1)) * gv g (nVec F 1) (Sum.inr (Sum.inr 1)) = 0 := by
    have h := congrFun (hinv (nVec F 0)) (Sum.inr (Sum.inr 1))
    rw [hn _ (hZg 0) 1, nVec_01] at h
    exact h
  have hI3 : gv g (nVec F 1) (Sum.inr (Sum.inr 0)) * gv g (nVec F 0) (Sum.inr (Sum.inr 0)) +
      gv g (nVec F 1) (Sum.inr (Sum.inr 1)) * gv g (nVec F 1) (Sum.inr (Sum.inr 0)) = 0 := by
    have h := congrFun (hinv (nVec F 1)) (Sum.inr (Sum.inr 0))
    rw [hn _ (hZg 1) 0, nVec_10] at h
    exact h
  have hI4 : gv g (nVec F 1) (Sum.inr (Sum.inr 0)) * gv g (nVec F 0) (Sum.inr (Sum.inr 1)) +
      gv g (nVec F 1) (Sum.inr (Sum.inr 1)) * gv g (nVec F 1) (Sum.inr (Sum.inr 1)) = 1 := by
    have h := congrFun (hinv (nVec F 1)) (Sum.inr (Sum.inr 1))
    rw [hn _ (hZg 1) 1, nVec_11] at h
    exact h
  have hn0 : ∀ z : OW F, (∀ i : Fin (3 - 1), z (Sum.inr (Sum.inl i)) = 0) →
      gv g z (Sum.inr (Sum.inr 0)) = z (Sum.inr (Sum.inr 0)) *
        gv g (nVec F 0) (Sum.inr (Sum.inr 0)) + z (Sum.inr (Sum.inr 1)) *
        gv g (nVec F 1) (Sum.inr (Sum.inr 0)) := fun z hz => hn z hz 0
  have hn1 : ∀ z : OW F, (∀ i : Fin (3 - 1), z (Sum.inr (Sum.inl i)) = 0) →
      gv g z (Sum.inr (Sum.inr 1)) = z (Sum.inr (Sum.inr 0)) *
        gv g (nVec F 0) (Sum.inr (Sum.inr 1)) + z (Sum.inr (Sum.inr 1)) *
        gv g (nVec F 1) (Sum.inr (Sum.inr 1)) := fun z hz => hn z hz 1
  clear hn
  generalize gv g (nVec F 0) (Sum.inr (Sum.inr 0)) = r00 at hn0 hn1 hQn0 hQn1 hpol hI1 hI2 hI3 hI4
  generalize gv g (nVec F 0) (Sum.inr (Sum.inr 1)) = r10 at hn0 hn1 hQn0 hQn1 hpol hI1 hI2 hI3 hI4
  generalize gv g (nVec F 1) (Sum.inr (Sum.inr 0)) = r01 at hn0 hn1 hQn0 hQn1 hpol hI1 hI2 hI3 hI4
  generalize gv g (nVec F 1) (Sum.inr (Sum.inr 1)) = r11 at hn0 hn1 hQn0 hQn1 hpol hI1 hI2 hI3 hI4
  have hj : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
  have hnil : (r00 - 1) * (r00 - 1) + r01 * r10 = 0 ∧ (r00 - 1) * r01 + r01 * (r11 - 1) = 0 ∧
      r10 * (r00 - 1) + (r11 - 1) * r10 = 0 ∧ r10 * r01 + (r11 - 1) * (r11 - 1) = 0 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination hI1 + (1 - r00) * h2
    · linear_combination hI3 - r01 * h2
    · linear_combination hI2 - r10 * h2
    · linear_combination hI4 + (1 - r11) * h2
  have hisoL : ∀ p q : F, (p + ((r00 - 1) * p + r01 * q)) ^ 2 + b * (p + ((r00 - 1) * p + r01 * q)) *
      (q + (r10 * p + (r11 - 1) * q)) + c * (q + (r10 * p + (r11 - 1) * q)) ^ 2 =
      p ^ 2 + b * p * q + c * q ^ 2 := by
    intro p q
    linear_combination p ^ 2 * hQn0 + q ^ 2 * hQn1 + p * q * hpol +
      p * q * (r00 * r01 + c * r10 * r11) * h2
  obtain ⟨L, hL, hLiso⟩ := exists_ell (b := b) (c := c) (r00 - 1) r01 r10 (r11 - 1) hnil hisoL
  have hRad : RadHyp b c (L * g) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro v
      rw [gv_mul, hLiso, hiso]
    · intro i
      rw [gv_mul, hfix, hL, nMap_eq, eV_inr, eV_inr, zero_smul, zero_smul, add_zero, add_zero]
    · intro x i
      rw [gv_mul, hL]
      simp only [Pi.sub_apply, Pi.add_apply, nMap_inr_inl, hV, add_zero, sub_self]
    · intro z hz j
      have hz' : ∀ i : Fin (3 - 1), z (Sum.inr (Sum.inl i)) = 0 := hz
      rw [gv_mul, hL]
      rcases hj j with rfl | rfl
      · simp only [Pi.sub_apply, Pi.add_apply, nMap_n0, hn0 z hz', hn1 z hz']
        linear_combination z (Sum.inr (Sum.inr 0)) * hI1 + z (Sum.inr (Sum.inr 1)) * hI3
      · simp only [Pi.sub_apply, Pi.add_apply, nMap_n1, hn0 z hz', hn1 z hz']
        linear_combination z (Sum.inr (Sum.inr 0)) * hI2 + z (Sum.inr (Sum.inr 1)) * hI4
  have hLg : L * g ∈ StatedOmega (StatedQuadMinus 3 F b c) := rad_mem_omega hirr hRad
  have hLΩ : L ∈ StatedOmega (StatedQuadMinus 3 F b c) := by
    have e : L = (L * g) * g⁻¹ := by group
    rw [e]
    exact mul_mem hLg (inv_mem hgΩ)
  obtain ⟨e00, e01, e10, e11⟩ := ell_trivial hirr hLΩ (r00 - 1) r01 r10 (r11 - 1) hnil hL
  intro z hz j
  rcases hj j with rfl | rfl
  · simp only [Pi.sub_apply, hn0 z hz]
    linear_combination z (Sum.inr (Sum.inr 0)) * e00 + z (Sum.inr (Sum.inr 1)) * e01
  · simp only [Pi.sub_apply, hn1 z hz]
    linear_combination z (Sum.inr (Sum.inr 0)) * e10 + z (Sum.inr (Sum.inr 1)) * e11

end RadD

end CFSG.LocalAnalysis.RankThreeUC
