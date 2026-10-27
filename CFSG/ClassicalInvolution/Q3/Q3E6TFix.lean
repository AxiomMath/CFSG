module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptOrth
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptBar
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptSkew

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3E6T

open Matrix CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.RouteD.NonClassical Module
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open scoped MatrixGroups

section Refl

variable {K : Type*} [Field K] {σ : K ≃+* K} {m : ℕ}

@[expose] noncomputable def uReflMat (σ : K ≃+* K) (u : Fin m → K) (e : K) :
    Matrix (Fin m) (Fin m) K :=
  1 - (2 * e⁻¹) • Matrix.vecMulVec u (fun j => σ (u j))

theorem uReflMat_mulVec (u x : Fin m → K) (e : K) :
    uReflMat σ u e *ᵥ x = x - (2 * e⁻¹ * herm σ u x) • u := by
  unfold uReflMat
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    op_smul_eq_smul, smul_smul]
  rfl

theorem uReflMat_mul_self {u : Fin m → K} {e : K} (he : herm σ u u = e) (he0 : e ≠ 0) :
    uReflMat σ u e * uReflMat σ u e = 1 := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  simp only [uReflMat_mulVec, herm_sub_right, herm_smul_right, he]
  have h1 : 2 * e⁻¹ * (herm σ u x - 2 * e⁻¹ * herm σ u x * e) = -(2 * e⁻¹ * herm σ u x) := by
    field_simp
    ring
  rw [h1, neg_smul, sub_neg_eq_add, sub_add_cancel]

theorem conjTr_uReflMat (hσ : ∀ c, σ (σ c) = c) {u : Fin m → K} {e : K} (hσe : σ e = e) :
    conjTr σ (uReflMat σ u e) = uReflMat σ u e := by
  ext i j
  have h2 : σ (2 * e⁻¹) = 2 * e⁻¹ := by rw [map_mul, map_inv₀, hσe, map_ofNat]
  simp only [conjTr, uReflMat, Matrix.transpose_apply, Matrix.map_apply, Matrix.sub_apply,
    Matrix.one_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, map_sub, map_mul,
    h2, hσ]
  by_cases hij : i = j
  · subst hij
    simp [mul_comm]
  · simp [hij, Ne.symm hij, mul_comm]

theorem det_uReflMat {u : Fin m → K} {e : K} (he : herm σ u u = e) (he0 : e ≠ 0) :
    (uReflMat σ u e).det = -1 := by
  have h : uReflMat σ u e = 1 + Matrix.replicateCol Unit (-(2 * e⁻¹) • u) *
      Matrix.replicateRow Unit (fun j => σ (u j)) := by
    ext i j
    simp [uReflMat, Matrix.one_apply, Matrix.vecMulVec_apply, Matrix.mul_apply,
      Matrix.replicateCol_apply, Matrix.replicateRow_apply, sub_eq_add_neg, neg_mul, mul_assoc]
  rw [h, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have : (fun j => σ (u j)) ⬝ᵥ (-(2 * e⁻¹) • u) = -(2 * e⁻¹) * herm σ u u := by
    simp [dotProduct, herm_def, Finset.mul_sum, mul_left_comm]
  rw [this, he]
  field_simp
  ring

theorem uReflMat_mulVec_of_orth {u w : Fin m → K} {e : K} (h : herm σ u w = 0) :
    uReflMat σ u e *ᵥ w = w := by
  rw [uReflMat_mulVec, h, mul_zero, zero_smul, sub_zero]

theorem uReflMat_comm_tau (T : RealStr σ m) {u : Fin m → K} (hu : T.IsReal u) {e : K}
    (hσe : σ e = e) (x : Fin m → K) :
    uReflMat σ u e *ᵥ T.τ x = T.τ (uReflMat σ u e *ᵥ x) := by
  have h2 : σ (2 * e⁻¹) = 2 * e⁻¹ := by rw [map_mul, map_inv₀, hσe, map_ofNat]
  have h1 : herm σ u (T.τ x) = σ (herm σ u x) := by
    have := T.herm_τ u x
    have hu' : T.τ u = u := hu
    rw [hu'] at this
    exact this
  have hu' : T.τ u = u := hu
  rw [uReflMat_mulVec, uReflMat_mulVec, T.τ_sub, T.map_smul, hu', h1, map_mul, h2]

theorem exists_rot_of_real_pair (hσ : ∀ c, σ (σ c) = c) (T : RealStr σ m)
    {a b : Fin m → K} (haR : T.IsReal a) (hbR : T.IsReal b) (hab : herm σ a b = 0)
    {d : K} (hd : d ≠ 0) (hdσ : σ d = d) (h2 : (2 : K) ≠ 0) (haa : herm σ a a = d)
    (hbb : herm σ b b = d) :
    ∃ M : Matrix (Fin m) (Fin m) K, M.det = 1 ∧ conjTr σ M * M = 1 ∧
      (∀ w, herm σ a w = 0 → herm σ b w = 0 → M *ᵥ w = w) ∧
      (∀ x, M *ᵥ T.τ x = T.τ (M *ᵥ x)) ∧ M *ᵥ (M *ᵥ a) = -a := by
  have hba : herm σ b a = 0 := herm_eq_zero_comm σ hσ hab
  have hs : herm σ (a + b) (a + b) = 2 * d := by
    rw [herm_add_left, herm_add_right, herm_add_right, haa, hab, hba, hbb]
    ring
  have he₂ : (2 * d : K) ≠ 0 := mul_ne_zero h2 hd
  have hσ₂ : σ (2 * d) = 2 * d := by rw [map_mul, map_ofNat, hdσ]
  have hsR : T.IsReal (a + b) := T.isReal_add_real haR hbR
  set R₁ := uReflMat σ a d with hR₁
  set R₂ := uReflMat σ (a + b) (2 * d) with hR₂
  have hR₂a : R₂ *ᵥ a = -b := by
    rw [hR₂, uReflMat_mulVec, herm_add_left, haa, hba]
    have : 2 * (2 * d)⁻¹ * (d + 0) = 1 := by rw [add_zero]; field_simp
    rw [this, one_smul]
    abel
  have hR₂b : R₂ *ᵥ b = -a := by
    rw [hR₂, uReflMat_mulVec, herm_add_left, hab, hbb]
    have : 2 * (2 * d)⁻¹ * (0 + d) = 1 := by rw [zero_add]; field_simp
    rw [this, one_smul]
    abel
  have hR₁a : R₁ *ᵥ a = -a := by
    rw [hR₁, uReflMat_mulVec, haa]
    have : 2 * d⁻¹ * d = 2 := by field_simp
    rw [this, two_smul]
    abel
  have hR₁b : R₁ *ᵥ b = b := by
    rw [hR₁, uReflMat_mulVec_of_orth hab]
  refine ⟨R₁ * R₂, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, hR₁, hR₂, det_uReflMat haa hd, det_uReflMat hs he₂]
    norm_num
  · rw [conjTr_mul, hR₁, hR₂, conjTr_uReflMat hσ hdσ, conjTr_uReflMat hσ hσ₂, Matrix.mul_assoc,
      ← Matrix.mul_assoc (uReflMat σ a d), uReflMat_mul_self haa hd, Matrix.one_mul,
      uReflMat_mul_self hs he₂]
  · intro w hw1 hw2
    have : herm σ (a + b) w = 0 := by rw [herm_add_left, hw1, hw2, add_zero]
    rw [← Matrix.mulVec_mulVec, hR₂, uReflMat_mulVec_of_orth this, hR₁,
      uReflMat_mulVec_of_orth hw1]
  · intro x
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hR₂, hR₁,
      uReflMat_comm_tau T hsR hσ₂ x, uReflMat_comm_tau T haR hdσ]
  · have e1 : (R₁ * R₂) *ᵥ a = -b := by
      rw [← Matrix.mulVec_mulVec, hR₂a, Matrix.mulVec_neg, hR₁b]
    have e2 : (R₁ * R₂) *ᵥ b = a := by
      rw [← Matrix.mulVec_mulVec, hR₂b, Matrix.mulVec_neg, hR₁a, neg_neg]
    rw [e1, Matrix.mulVec_neg, e2]

end Refl


section Plane

variable {p f : ℕ} [Fact p.Prime]

theorem exists_stable_aniso_plane_rot (hf : 1 ≤ f) (hp2 : p ≠ 2) (hq3 : p ^ f = 3)
    {g : GL (Fin 6) (GaloisField p (2 * f))}
    {α : Su (GaloisField p (2 * f)) p f 6 →* Su (GaloisField p (2 * f)) p f 6}
    (hmat : ∀ x : Su (GaloisField p (2 * f)) p f 6,
      ((α x : GL (Fin 6) (GaloisField p (2 * f))) :
        Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) =
        (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
          (unitaryInvolution (GaloisField p (2 * f)) p f).mapMatrix
            ((x : GL (Fin 6) (GaloisField p (2 * f))) :
              Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
          ((g⁻¹ : GL (Fin 6) (GaloisField p (2 * f))) :
            Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))))
    (hiso : conjTr (unitaryInvolution (GaloisField p (2 * f)) p f)
      (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
        (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) = 1)
    (hμ : (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
      (unitaryInvolution (GaloisField p (2 * f)) p f).mapMatrix
        (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) = 1)
    (hW : (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) * suMat (te6Inv p f) =
      suMat (te6Inv p f) * (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)))) :
    ∃ P : Submodule (GaloisField p (2 * f)) (Fin 6 → GaloisField p (2 * f)),
      Nondeg (unitaryInvolution (GaloisField p (2 * f)) p f) P ∧
        finrank (GaloisField p (2 * f)) P = 2 ∧ P ≤ te6Plus p f ∧
        (∀ y ∈ planeGroupU (GaloisField p (2 * f)) p f P,
          α y ∈ planeGroupU (GaloisField p (2 * f)) p f P) ∧
        ∃ y ∈ planeGroupU (GaloisField p (2 * f)) p f P, α y = y ∧ y * y ≠ 1 ∧ y ^ 4 = 1 := by
  classical
  have : NeZero (2 * f) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p f hf
  have hσ := isUnitaryInvolution_unitaryInvolution (p := p) (f := f) hK
  have hσq : ∀ c : GaloisField p (2 * f), unitaryInvolution (GaloisField p (2 * f)) p f c =
      c ^ p ^ f := fun c => unitaryInvolution_apply _ _ _ c
  have hEnd := te6Plus_nondeg (p := p) (f := f) hp2 hf
  have hdim4 := finrank_te6Plus (p := p) (f := f) hp2 hf
  have hodd : p ^ f % 2 = 1 := by rw [hq3]
  have h2 : (2 : GaloisField p (2 * f)) ≠ 0 := two_ne_zero_of_char hp2
  obtain ⟨κ, hκ0, hκq, hκ⟩ := exists_fixed_nonsquare hp2 hf hK
  have hκ1 : κ = -1 := by
    rw [hq3] at hκ
    simpa using hκ
  set σ := unitaryInvolution (GaloisField p (2 * f)) p f with hσdef
  set Gm : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)) :=
    ((g : GL (Fin 6) (GaloisField p (2 * f))) : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)))
    with hGm
  set Gi : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)) :=
    ((g⁻¹ : GL (Fin 6) (GaloisField p (2 * f))) :
      Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) with hGi
  have hGiG : Gi * Gm = 1 := by rw [hGi, hGm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hGGi : Gm * Gi = 1 := by rw [hGi, hGm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hσGm : σ.mapMatrix Gm = Gi := mapMatrix_eq_inv σ hGiG hμ
  let T : RealStr σ 6 := realStrOfMatrix hσ.invol Gm hμ hiso
  have hτ : ∀ u, T.τ u = Gm *ᵥ (fun i => σ (u i)) := fun u => rfl
  have hEm : T.IsStable (te6Minus p f) := by
    intro s hs
    have hs' : suMat (te6Inv p f) *ᵥ s = -s := mem_minusSpaceSU.mp hs
    refine mem_minusSpaceSU.mpr ?_
    rw [hτ, Matrix.mulVec_mulVec, ← hW, ← Matrix.mulVec_mulVec]
    have h1 := conjVec_mulVec σ (suMat (te6Inv p f)) s
    rw [mapMatrix_suMat_te6Inv σ, hs'] at h1
    have h2 : suMat (te6Inv p f) *ᵥ (fun i => σ (s i)) = -(fun i => σ (s i)) := by
      rw [← h1]
      funext i
      simp
    rw [h2, Matrix.mulVec_neg]
  have hEp : T.IsStable (te6Plus p f) := T.isStable_perp hEm
  have hκσ : σ κ = κ := by rw [hσq]; exact hκq
  obtain ⟨a, b, haU, hbU, haR, hbR, hab, d, hd, hdσ, haa, hbb⟩ :=
    exists_aniso_pair T hσ hp2 hκσ hEnd hEp (by rw [hdim4]; norm_num)
  have hbb' : herm σ b b = d := by rw [hbb, hκ1]; ring
  have had : herm σ a a ≠ 0 := by rw [haa]; exact hd
  have hbd : herm σ b b ≠ 0 := by rw [hbb']; exact hd
  set P : Submodule (GaloisField p (2 * f)) (Fin 6 → GaloisField p (2 * f)) :=
    Submodule.span _ {a, b} with hP
  have haP : a ∈ P := Submodule.subset_span (Set.mem_insert a {b})
  have hbP : b ∈ P := Submodule.subset_span (by simp)
  have hPst : T.IsStable P := by
    intro u hu
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hu
    have haR' : T.τ a = a := haR
    have hbR' : T.τ b = b := hbR
    rw [T.map_add, T.map_smul, T.map_smul, haR', hbR']
    exact P.add_mem (P.smul_mem _ haP) (P.smul_mem _ hbP)
  have hPperp : T.IsStable (perp σ P) := T.isStable_perp hPst
  have hpow : ∀ y ∈ planeGroupU (GaloisField p (2 * f)) p f P, α y = y →
      y ^ (p ^ f + 1) = 1 := by
    intro y hy hαy
    have hfixy : ∀ w ∈ perp σ P, suMat y *ᵥ w = w := by
      intro w hw
      rw [← suMat_smul]
      exact ((mem_fixingSubgroup_iff _).mp hy) w hw
    have hisoy : ∀ u w, herm σ (suMat y *ᵥ u) (suMat y *ᵥ w) = herm σ u w := fun u w => by
      rw [← suMat_smul, ← suMat_smul]
      exact herm_smul_smul σ y u w
    have e : suMat y = Gm * σ.mapMatrix (suMat y) * Gi := by
      have := hmat y
      rw [hαy] at this
      exact this
    have e2 : suMat y * Gm = Gm * σ.mapMatrix (suMat y) := by
      calc suMat y * Gm = (Gm * σ.mapMatrix (suMat y) * Gi) * Gm := by rw [← e]
        _ = Gm * σ.mapMatrix (suMat y) := by rw [Matrix.mul_assoc, hGiG, Matrix.mul_one]
    have hcommy : ∀ u, suMat y *ᵥ (T.τ u) = T.τ (suMat y *ᵥ u) := by
      intro u
      rw [hτ, hτ, Matrix.mulVec_mulVec, e2, ← Matrix.mulVec_mulVec,
        ← conjVec_mulVec σ (suMat y) u]
    have hpow := pow_eq_one_of_fix T hσ hσq hp2 hodd hκ0 hκ hd haR hbR haa hbb hab
      (Matrix.toLinAlgEquiv' (suMat y)) (fun u w => by simpa using hisoy u w)
      (fun w hw => by simpa using hfixy w hw) (fun u => by simpa using hcommy u)
    have hpow' : suMat y ^ (p ^ f + 1) = 1 := by
      rw [← map_pow] at hpow
      have h1 : Matrix.toLinAlgEquiv' (suMat y ^ (p ^ f + 1)) = Matrix.toLinAlgEquiv' 1 := by
        rw [map_one]
        exact hpow
      exact Matrix.toLinAlgEquiv'.injective h1
    have hsp : ∀ n : ℕ, suMat (y ^ n) = suMat y ^ n := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, suMat_mul, ih, pow_succ]
    apply suMat_injective
    rw [hsp, suMat_one]
    exact hpow'
  obtain ⟨M, hMdet, hMu, hMfix, hMτ, hMsq⟩ :=
    exists_rot_of_real_pair hσ.invol T haR hbR hab hd hdσ h2 haa hbb'
  have hMGm : M * Gm = Gm * σ.mapMatrix M := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    have h := hMτ (fun i => σ (v i))
    have e1 : T.τ (fun i => σ (v i)) = Gm *ᵥ v := by
      rw [hτ]
      congr 1
      funext i
      exact hσ.invol (v i)
    have e2 : T.τ (M *ᵥ fun i => σ (v i)) = Gm *ᵥ (σ.mapMatrix M *ᵥ v) := by
      rw [hτ, conjVec_mulVec σ M (fun i => σ (v i))]
      congr 2
      funext i
      exact hσ.invol (v i)
    rw [e1, e2] at h
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact h
  set y : Su (GaloisField p (2 * f)) p f 6 :=
    Models.mkSU (GaloisField p (2 * f)) p f M hMdet hMu with hy
  have hsy : suMat y = M := rfl
  have hyP : y ∈ planeGroupU (GaloisField p (2 * f)) p f P := by
    rw [planeGroupU, mem_fixingSubgroup_iff]
    intro w hw
    rw [suMat_smul, hsy]
    exact hMfix w (herm_eq_zero_comm σ hσ.invol (hw a haP))
      (herm_eq_zero_comm σ hσ.invol (hw b hbP))
  have hαy : α y = y := by
    apply suMat_injective
    have e : suMat (α y) = Gm * σ.mapMatrix (suMat y) * Gi := hmat y
    rw [e, hsy, ← hMGm, Matrix.mul_assoc, hGGi, Matrix.mul_one]
  have hyy : y * y ≠ 1 := by
    intro h
    have h1 : M * M = 1 := by rw [← hsy, ← suMat_mul, h, suMat_one]
    have h3 : M *ᵥ (M *ᵥ a) = a := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    rw [hMsq] at h3
    have h4 : (2 : GaloisField p (2 * f)) • a = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h3]
      exact neg_add_cancel a
    have ha0 : a = 0 := (smul_eq_zero.mp h4).resolve_left h2
    exact had (by rw [ha0, herm_zero_left])
  refine ⟨P, nondeg_span_pair_of_orth hσ had hbd hab, finrank_span_pair_of_orth hσ had hbd hab,
    ?_, ?_, y, hyP, hαy, hyy, ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro _ (rfl | rfl)
    · exact haU
    · exact hbU
  · intro y' hy'
    rw [planeGroupU, mem_fixingSubgroup_iff] at hy' ⊢
    intro w hw
    have hw' : T.τ w ∈ perp σ P := hPperp w hw
    have hY : suMat y' *ᵥ (T.τ w) = T.τ w := by
      rw [← suMat_smul]
      exact hy' _ hw'
    have hGiw : Gi *ᵥ w = fun i => σ ((T.τ w) i) := by
      rw [← hσGm]
      have := conjVec_mulVec σ Gm (fun i => σ (w i))
      simp only [hσ.invol] at this
      rw [hτ]
      exact this.symm
    have e : suMat (α y') = Gm * σ.mapMatrix (suMat y') * Gi := hmat y'
    rw [suMat_smul, e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hGiw,
      ← conjVec_mulVec σ (suMat y') (T.τ w), hY]
    show T.τ (T.τ w) = w
    exact T.invol w
  · have := hpow y hyP hαy
    rwa [hq3] at this

end Plane

end CFSG.ClassicalInvolution.Q3.Q3E6T
