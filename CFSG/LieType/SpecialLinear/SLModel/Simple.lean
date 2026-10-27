module

public import CFSG.LieType.SpecialLinear.SLModel.Basic

public section

namespace CFSG.LieType.SpecialLinear.SLModel

open Matrix Polynomial CFSG.LieType.SpecialLinear.ExteriorModel
  CFSG.LieType.SpecialLinear CFSG.Quasithin.SmithCurtis
open scoped MatrixGroups

noncomputable section

section Separation

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {k : Type} [Field k] [CharP k 2]
  [Algebra F k] {f : ℕ}

theorem mem_of_forall_sum_frobTwist_smul_mem (hF : Fintype.card F = 2 ^ f)
    {V : Type*} [AddCommGroup V] [Module k V] (S : Submodule k V) (v : Fin f → V)
    (h : ∀ t : F, ∑ r, frobTwist F k f r t • v r ∈ S) (r : Fin f) : v r ∈ S := by
  classical
  have hinj : Function.Injective (algebraMap F k) := by
    have hzero : ∀ x : F, algebraMap F k x = 0 → x = 0 := by
      intro x hx
      by_contra hx0
      exact (isUnit_iff_ne_zero.mpr hx0).map (algebraMap F k) |>.ne_zero hx
    intro a b hab
    exact sub_eq_zero.mp (hzero (a - b) (by rw [map_sub, hab, sub_self]))
  have hpow_inj : Function.Injective (fun r : Fin f => 2 ^ (r : ℕ)) := by
    intro a b hab
    exact Fin.ext (Nat.pow_right_injective (le_refl 2) hab)
  have hbound : ∀ r : Fin f, 2 ^ (r : ℕ) < Fintype.card F := by
    intro r
    rw [hF]
    exact Nat.pow_lt_pow_right (by norm_num) r.isLt
  have key : ∀ φ : Module.Dual k (V ⧸ S), φ (Submodule.mkQ S (v r)) = 0 := by
    intro φ
    let P : k[X] := ∑ r : Fin f, C (φ (Submodule.mkQ S (v r))) * X ^ (2 ^ (r : ℕ))
    have hPeval : ∀ t : F, P.eval (algebraMap F k t) = 0 := by
      intro t
      have h1 : Submodule.mkQ S (∑ r, frobTwist F k f r t • v r) = 0 := by
        rw [Submodule.mkQ_apply]
        exact (Submodule.Quotient.mk_eq_zero S).mpr (h t)
      have h2 := congrArg φ h1
      have h2' : ∑ x : Fin f, frobTwist F k f x t * φ (Submodule.mkQ S (v x)) = 0 := by
        simpa only [map_sum, map_smul, smul_eq_mul, map_zero] using h2
      simp only [P, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      rw [← h2']
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [frobTwist_apply, map_pow, mul_comm]
    have hPzero : P = 0 := by
      have hdeg : P.natDegree ≤ Finset.univ.sup (fun r : Fin f => 2 ^ (r : ℕ)) := by
        simp only [P]
        refine Polynomial.natDegree_sum_le_of_forall_le (s := Finset.univ)
          (n := Finset.univ.sup (fun r : Fin f => 2 ^ (r : ℕ)))
          (f := fun r => C (φ (Submodule.mkQ S (v r))) * X ^ (2 ^ (r : ℕ))) fun r _ => ?_
        refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
        rw [Polynomial.natDegree_X_pow]
        exact Finset.le_sup (f := fun r : Fin f => 2 ^ (r : ℕ)) (Finset.mem_univ r)
      have hsup : Finset.univ.sup (fun r : Fin f => 2 ^ (r : ℕ)) < Fintype.card F := by
        rw [Finset.sup_lt_iff (by simpa using Fintype.card_pos)]
        exact fun r _ => hbound r
      have hcard : P.natDegree < (Finset.univ.image (algebraMap F k)).card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
        exact lt_of_le_of_lt hdeg hsup
      refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P
        (Finset.univ.image (algebraMap F k)) ?_ hcard
      intro x hx
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hx
      exact hPeval t
    have hcoeff := congrArg (fun p : k[X] => p.coeff (2 ^ (r : ℕ))) hPzero
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at hcoeff
    rw [Finset.sum_eq_single r (fun b _ hb => by simp [hpow_inj.ne hb.symm])
      (fun hr => absurd (Finset.mem_univ r) hr)] at hcoeff
    simpa using hcoeff
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff k]
  exact fun φ => key φ

end Separation

section FirstOrder

variable {k : Type} [Field k] {n : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ]

theorem bFirst_one_add_single (ε : τ → Finset (Fin n)) (c : τ → k) {a b : Fin n}
    (hab : (b : ℕ) = a + 1) :
    bFirst (k := k) ε (fun r => 1 + Matrix.single a b (c r)) =
      ∑ r, c r • bDer (k := k) ε (r, a, b) := by
  classical
  have hsuper : ∀ r, bSuper (k := k) ε (fun r => 1 + Matrix.single a b (c r)) r =
      c r • Matrix.single a b (1 : k) := by
    intro r
    ext i j
    rw [bSuper_apply]
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply]
    by_cases hij : (j : ℕ) = i + 1
    · rw [if_pos hij]
      by_cases h1 : i = j
      · exfalso
        rw [h1] at hij
        omega
      · rw [if_neg h1, zero_add]
        by_cases h2 : a = i ∧ b = j
        · obtain ⟨h2a, h2b⟩ := h2
          rw [if_pos ⟨h2a, h2b⟩, if_pos ⟨h2a, h2b⟩, mul_one]
        · rw [if_neg h2, if_neg h2, mul_zero]
    · rw [if_neg hij, if_neg]
      · rw [mul_zero]
      · rintro ⟨rfl, rfl⟩
        exact hij hab
  rw [bFirst_eq_sum_kronDer]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hsuper r, kronDer_smul, ← bDer_mk]

end FirstOrder

section TwistedTransvection

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {k : Type} [Field k] [CharP k 2]
  [Algebra F k] {m f : ℕ}

theorem coe_twist_transvection (s : Fin m) (t : F) (r : Fin f) :
    ((twistHom (frobTwist F k f) (SpecialLinearGroup.transvection
      (Fin.castSucc_lt_succ (i := s)).ne t)) r :
        Matrix (Fin (m + 1)) (Fin (m + 1)) k) =
      1 + Matrix.single s.castSucc s.succ (frobTwist F k f r t) := by
  rw [twistHom_apply, Matrix.SpecialLinearGroup.map_apply_coe,
    Matrix.SpecialLinearGroup.transvection_coe, map_add, map_one, RingHom.mapMatrix_apply,
    Matrix.map_single]

theorem bFirst_twist_transvection (ε : Fin f → Finset (Fin (m + 1))) (s : Fin m) (t : F) :
    bFirst (k := k) ε (fun r => ((twistHom (frobTwist F k f)
      (SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := s)).ne t)) r :
        Matrix (Fin (m + 1)) (Fin (m + 1)) k)) =
      ∑ r, frobTwist F k f r t • bDer (k := k) ε (r, s.castSucc, s.succ) := by
  have hfam : (fun r => ((twistHom (frobTwist F k f)
      (SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := s)).ne t)) r :
        Matrix (Fin (m + 1)) (Fin (m + 1)) k)) =
      fun r => 1 + Matrix.single s.castSucc s.succ (frobTwist F k f r t) :=
    funext fun r => coe_twist_transvection s t r
  rw [hfam]
  exact bFirst_one_add_single ε _ (by simp [Fin.succ, Fin.castSucc])

end TwistedTransvection

section FixedLine

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {k : Type} [Field k] [CharP k 2]
  [Algebra F k] {m f : ℕ}

theorem bDer_mulVec_homComp_mem_bRad_of_fixed (hF : Fintype.card F = 2 ^ f)
    (ε : Fin f → Finset (Fin (m + 1))) {w : BIdx ε → k}
    (hfix : ∀ u ∈ (curtisDatum m F 2).U,
      bMat ε (fun r => ((twistHom (frobTwist F k f) u) r :
        Matrix (Fin (m + 1)) (Fin (m + 1)) k)) *ᵥ w - w ∈ bRad (k := k) ε)
    (e : ℤ) (htop : ∀ e' : ℤ, e < e' →
      homComp (fun s : BIdx ε => (kdeg s : ℤ)) e' w ∈ bRad (k := k) ε)
    (r : Fin f) (s : Fin m) :
    bDer (k := k) ε (r, s.castSucc, s.succ) *ᵥ
      homComp (fun s : BIdx ε => (kdeg s : ℤ)) e w ∈ bRad (k := k) ε := by
  classical
  have hne : s.castSucc ≠ s.succ := (Fin.castSucc_lt_succ (i := s)).ne
  have hsum : ∀ t : F, ∑ r, frobTwist F k f r t •
      (bDer (k := k) ε (r, s.castSucc, s.succ) *ᵥ
        homComp (fun s : BIdx ε => (kdeg s : ℤ)) e w) ∈ bRad (k := k) ε := by
    intro t
    have hU : SpecialLinearGroup.transvection hne t ∈ (curtisDatum m F 2).U := by
      rw [mem_curtisDatum_U_iff]
      refine ⟨fun i => ?_, fun i j hji => ?_⟩
      · rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply,
          Matrix.one_apply_eq, Matrix.single_apply,
          if_neg (by rintro ⟨h1, h2⟩; exact hne (h1.symm ▸ h2.symm)), add_zero]
      · rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply,
          Matrix.one_apply_ne hji.ne', Matrix.single_apply,
          if_neg (by
            rintro ⟨rfl, rfl⟩
            exact absurd hji (not_lt.mpr (le_of_lt (Fin.castSucc_lt_succ (i := s))))),
          add_zero]
    have htri : ∀ (q : Fin f) (i j : Fin (m + 1)), j < i →
        ((twistHom (frobTwist F k f) (SpecialLinearGroup.transvection hne t)) q :
          Matrix (Fin (m + 1)) (Fin (m + 1)) k) i j = 0 := by
      intro q i j hji
      rw [coe_twist_transvection s t q, Matrix.add_apply, Matrix.one_apply_ne hji.ne',
        Matrix.single_apply,
        if_neg (by
          rintro ⟨rfl, rfl⟩
          exact absurd hji (not_lt.mpr (le_of_lt (Fin.castSucc_lt_succ (i := s))))),
        add_zero]
    have hdiag : ∀ (q : Fin f) (i : Fin (m + 1)),
        ((twistHom (frobTwist F k f) (SpecialLinearGroup.transvection hne t)) q :
          Matrix (Fin (m + 1)) (Fin (m + 1)) k) i i = 1 := by
      intro q i
      rw [coe_twist_transvection s t q, Matrix.add_apply, Matrix.one_apply_eq,
        Matrix.single_apply,
        if_neg (by rintro ⟨h1, h2⟩; exact hne (h1.symm ▸ h2.symm)), add_zero]
    have hdiff : bMat ε (fun q => ((twistHom (frobTwist F k f)
        (SpecialLinearGroup.transvection hne t)) q :
          Matrix (Fin (m + 1)) (Fin (m + 1)) k)) *ᵥ w - w ∈ bRad (k := k) ε :=
      hfix _ hU
    have hex := bFirst_mulVec_homComp_mem_bRad (k := k) (n := m + 1) (τ := Fin f) ε
      (h := twistHom (frobTwist F k f) (SpecialLinearGroup.transvection hne t))
      htri hdiag hdiff e htop
    rw [bFirst_twist_transvection, Matrix.sum_mulVec] at hex
    simpa only [Matrix.smul_mulVec] using hex
  exact mem_of_forall_sum_frobTwist_smul_mem hF (bRad (k := k) ε)
    (fun q => bDer (k := k) ε (q, s.castSucc, s.succ) *ᵥ
      homComp (fun s : BIdx ε => (kdeg s : ℤ)) e w) hsum r

theorem exists_eq_smul_bTop_of_fixed (hF : Fintype.card F = 2 ^ f)
    (ε : Fin f → Finset (Fin (m + 1))) {x : BModel k ε}
    (hx : ∀ u ∈ (curtisDatum m F 2).U, slModelRep (F := F) (k := k) ε u x = x) :
    ∃ c : k, x = c • bTop ε := by
  classical
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective
    (p := (bRad (k := k) ε).comap (bCyc (k := k) ε).subtype) x
  have hfix : ∀ u ∈ (curtisDatum m F 2).U,
      bMat ε (fun r => ((twistHom (frobTwist F k f) u) r :
        Matrix (Fin (m + 1)) (Fin (m + 1)) k)) *ᵥ (w : BIdx ε → k) -
        (w : BIdx ε → k) ∈ bRad (k := k) ε := by
    intro u hu
    have h := hx u hu
    rw [slModelRep_mk] at h
    have h' := (Submodule.Quotient.eq (p :=
      (bRad (k := k) ε).comap (bCyc (k := k) ε).subtype)).mp h
    have hfam : (fun r => ((twistHom (frobTwist F k f) u) r :
        Matrix (Fin (m + 1)) (Fin (m + 1)) k)) =
        fun r => (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map (frobTwist F k f r) := by
      funext r
      rw [twistHom_apply, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    rw [hfam]
    simpa [Submodule.mem_comap] using h'
  have hcrit : ∀ e : ℤ, (∀ e' : ℤ, e < e' →
      homComp (fun s : BIdx ε => (kdeg s : ℤ)) e' (w : BIdx ε → k) ∈
        bRad (k := k) ε) →
      ∀ (r : Fin f) (a b : Fin (m + 1)), (b : ℕ) = a + 1 →
        bDer (k := k) ε (r, a, b) *ᵥ
          homComp (fun s : BIdx ε => (kdeg s : ℤ)) e (w : BIdx ε → k) ∈
            bRad (k := k) ε := by
    intro e htop r a b hb
    have ha : (a : ℕ) < m := by
      have hb' : (b : ℕ) ≤ m := by
        have := b.isLt
        omega
      omega
    let s : Fin m := ⟨(a : ℕ), ha⟩
    have hsa : (s.castSucc : Fin (m + 1)) = a := Fin.ext rfl
    have hsb : (s.succ : Fin (m + 1)) = b := by
      apply Fin.ext
      show (a : ℕ) + 1 = (b : ℕ)
      omega
    rw [← hsa, ← hsb]
    exact bDer_mulVec_homComp_mem_bRad_of_fixed hF ε hfix e htop r s
  have hfixed := sub_smul_bvec_mem_bRad_of_homComp ε w.2 hcrit
  refine ⟨(w : BIdx ε → k) ⬝ᵥ bvec ε, ?_⟩
  have h1 : (Submodule.Quotient.mk (p :=
      (bRad (k := k) ε).comap (bCyc (k := k) ε).subtype) w) =
      Submodule.Quotient.mk (p :=
        (bRad (k := k) ε).comap (bCyc (k := k) ε).subtype)
        ⟨((w : BIdx ε → k) ⬝ᵥ bvec ε) • bvec ε,
          Submodule.smul_mem _ ((w : BIdx ε → k) ⬝ᵥ bvec ε)
            (bvec_mem_bCyc (k := k) ε)⟩ := by
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    simpa using hfixed
  rw [h1, bTop, ← Submodule.Quotient.mk_smul]
  rfl

theorem isSimpleRep_slModelRep (hF : Fintype.card F = 2 ^ f)
    (ε : Fin f → Finset (Fin (m + 1))) :
    IsSimpleRep (slModelRep (F := F) (k := k) ε) := by
  classical
  refine ⟨?_, ?_⟩
  · exact (nontrivial_iff_exists_ne (0 : BModel k ε)).mpr ⟨bTop ε, bTop_ne_zero ε⟩
  · intro W hW
    by_cases hbot : W = ⊥
    · exact Or.inl hbot
    · right
      obtain ⟨x, hxW, hxne, hxfix⟩ := exists_fixed_mem (slModelRep (F := F) (k := k) ε)
        (p := 2) (curtisDatum m F 2).isPGroup_U (W := W) hW hbot
      obtain ⟨c, hc⟩ := exists_eq_smul_bTop_of_fixed hF ε hxfix
      have hcne : c ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hc
        exact hxne hc
      have htop : bTop ε ∈ W := by
        have hc' : bTop (k := k) ε = c⁻¹ • (c • bTop (k := k) ε) := by
          rw [smul_smul, inv_mul_cancel₀ hcne, one_smul]
        rw [hc', ← hc]
        exact Submodule.smul_mem _ _ hxW
      have hle : orbitSpan (slModelRep (F := F) (k := k) ε) (bTop ε) ≤ W := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨g, rfl⟩
        exact hW g (bTop ε) htop
      have hgen : orbitSpan (slModelRep (F := F) (k := k) ε) (bTop ε) = ⊤ := by
        refine orbitSpan_bTop_eq_top (k := k) (n := m + 1) (τ := Fin f) ε
          (twistHom (frobTwist F k f)) ?_ (curtisDatum m F 2).isPGroup_U ?_
        · intro g
          refine ⟨SpecialLinearGroup.transpose g, fun r => ?_⟩
          rw [twistHom_apply, twistHom_apply, Matrix.SpecialLinearGroup.map_apply_coe,
            Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.coe_transpose,
            RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.transpose_map]
        · intro x hx
          exact exists_eq_smul_bTop_of_fixed hF ε hx
      rw [hgen] at hle
      exact top_le_iff.mp hle

end FixedLine

end

end CFSG.LieType.SpecialLinear.SLModel

end
