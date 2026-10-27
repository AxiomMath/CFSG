module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptFix
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptBar

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open Matrix CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic Module
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open scoped MatrixGroups

section Plane

theorem nondeg_span_pair_of_orth {K : Type} [Field K] {σ : K ≃+* K} (hσ : IsUnitaryInvolution σ)
    {m : ℕ} {a b : Fin m → K} (ha : herm σ a a ≠ 0) (hb : herm σ b b ≠ 0)
    (hab : herm σ a b = 0) : Nondeg σ (Submodule.span K {a, b}) := by
  have : Submodule.span K {a, b} = K ∙ a ⊔ K ∙ b := by rw [Submodule.span_insert]
  rw [this]
  exact Nondeg.sup_of_orth hσ (nondeg_span_singleton ha) (nondeg_span_singleton hb)
    (orth_span_singleton_iff.mpr hab)

theorem finrank_span_pair_of_orth {K : Type} [Field K] {σ : K ≃+* K}
    (hσ : IsUnitaryInvolution σ) {m : ℕ} {a b : Fin m → K} (ha : herm σ a a ≠ 0)
    (hb : herm σ b b ≠ 0) (hab : herm σ a b = 0) :
    finrank K (Submodule.span K {a, b}) = 2 := by
  have hba : herm σ b a = 0 := herm_eq_zero_comm σ hσ.invol hab
  have hli : LinearIndependent K ![a, b] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 := congrArg (herm σ a) h
    have h2 := congrArg (herm σ b) h
    simp only [herm_add_right, herm_smul_right, hab, hba, herm_zero_right, mul_zero, add_zero,
      zero_add] at h1 h2
    exact ⟨(mul_eq_zero.mp h1).resolve_right ha, (mul_eq_zero.mp h2).resolve_right hb⟩
  have := finrank_span_eq_card hli
  have hr : Set.range ![a, b] = {a, b} := by
    ext x
    simp [eq_comm, or_comm]
  rw [hr] at this
  simpa using this

end Plane

section Orth

variable {p f : ℕ} [Fact p.Prime]

theorem conjVec_mulVec {K : Type*} [Field K] (σ : K ≃+* K) {m : ℕ} (M : Matrix (Fin m) (Fin m) K)
    (u : Fin m → K) :
    (fun i => σ ((M *ᵥ u) i)) = σ.mapMatrix M *ᵥ (fun i => σ (u i)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rfl

theorem mapMatrix_eq_inv {K : Type*} [Field K] (σ : K ≃+* K) {m : ℕ}
    {Gm Gi : Matrix (Fin m) (Fin m) K} (hGiG : Gi * Gm = 1)
    (hμ : Gm * σ.mapMatrix Gm = 1) : σ.mapMatrix Gm = Gi := by
  calc σ.mapMatrix Gm = (Gi * Gm) * σ.mapMatrix Gm := by rw [hGiG, Matrix.one_mul]
    _ = Gi * (Gm * σ.mapMatrix Gm) := by rw [Matrix.mul_assoc]
    _ = Gi := by rw [hμ, Matrix.mul_one]

theorem exists_stable_aniso_plane (hf : 1 ≤ f) (hp2 : p ≠ 2)
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
        (∀ y ∈ planeGroupU (GaloisField p (2 * f)) p f P, α y ∈ planeGroupU
          (GaloisField p (2 * f)) p f P) ∧
        ∀ y ∈ planeGroupU (GaloisField p (2 * f)) p f P, α y = y → y ^ (p ^ f + 1) = 1 := by
  classical
  have : NeZero (2 * f) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p f hf
  have hσ := isUnitaryInvolution_unitaryInvolution (p := p) (f := f) hK
  have hσq : ∀ c : GaloisField p (2 * f), unitaryInvolution (GaloisField p (2 * f)) p f c =
      c ^ p ^ f := fun c => unitaryInvolution_apply _ _ _ c
  have hEnd := te6Plus_nondeg (p := p) (f := f) hp2 hf
  have hdim4 := finrank_te6Plus (p := p) (f := f) hp2 hf
  have hodd : p ^ f % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact absurd h hp2
    · rw [Nat.pow_mod, h]; simp
  obtain ⟨κ, hκ0, hκq, hκ⟩ := exists_fixed_nonsquare hp2 hf hK
  set σ := unitaryInvolution (GaloisField p (2 * f)) p f with hσdef
  set Gm : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)) :=
    ((g : GL (Fin 6) (GaloisField p (2 * f))) : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)))
    with hGm
  set Gi : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)) :=
    ((g⁻¹ : GL (Fin 6) (GaloisField p (2 * f))) :
      Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) with hGi
  have hGiG : Gi * Gm = 1 := by rw [hGi, hGm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
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
  have had : herm σ a a ≠ 0 := by rw [haa]; exact hd
  have hbd : herm σ b b ≠ 0 := by
    rw [hbb]
    exact neg_ne_zero.mpr (mul_ne_zero hκ0 hd)
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
  refine ⟨P, nondeg_span_pair_of_orth hσ had hbd hab, finrank_span_pair_of_orth hσ had hbd hab,
    ?_, ?_, ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro _ (rfl | rfl)
    · exact haU
    · exact hbU
  · intro y hy
    rw [planeGroupU, mem_fixingSubgroup_iff] at hy ⊢
    intro w hw
    have hw' : T.τ w ∈ perp σ P := hPperp w hw
    have hY : suMat y *ᵥ (T.τ w) = T.τ w := by
      rw [← suMat_smul]
      exact hy _ hw'
    have hGiw : Gi *ᵥ w = fun i => σ ((T.τ w) i) := by
      rw [← hσGm]
      have := conjVec_mulVec σ Gm (fun i => σ (w i))
      simp only [hσ.invol] at this
      rw [hτ]
      exact this.symm
    have e : suMat (α y) = Gm * σ.mapMatrix (suMat y) * Gi := hmat y
    rw [suMat_smul, e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hGiw,
      ← conjVec_mulVec σ (suMat y) (T.τ w), hY]
    show T.τ (T.τ w) = w
    exact T.invol w
  · intro y hy hαy
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

end Orth

end CFSG.ClassicalInvolution.RouteD.NonClassical
