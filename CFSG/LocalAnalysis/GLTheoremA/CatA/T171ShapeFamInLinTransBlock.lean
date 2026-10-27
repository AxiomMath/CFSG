module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154LinCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Open.StatedAPI CFSG.LieType.SemisimpleCentralizers
open CFSG.LieType.SemisimpleCentralizers.Held CFSG.StandardType.LinNonsplit
open CFSG.LocalAnalysis.GLTheoremA.K155X
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.PComp
open scoped commutatorElement MatrixGroups

theorem exists_linComp_block {F : Type} [Field F] [Finite F] (h2 : (2 : F) = 0) {d : ℕ}
    (A : GL (Fin d) F) (hA : (orderOf A : F) ≠ 0) {p : ℕ} {M : Subgroup (GL (Fin d) F)}
    (hM : GLAPComponent p (Subgroup.centralizer ({A} : Set (GL (Fin d) F)) ⊓ StatedSL d F) M) :
    ∃ (d₁ : ℕ) (D₁ : Type) (_ : Field D₁) (_ : Finite D₁) (ι : GL (Fin d₁) D₁ →* GL (Fin d) F),
      (2 : D₁) = 0 ∧ 2 ≤ d₁ ∧ (d₁ ≠ 2 ∨ Nat.card D₁ ≠ 2) ∧ (d₁ ≠ 2 ∨ Nat.card D₁ ≠ 3) ∧
      Function.Injective ι ∧ M = (StatedSL d₁ D₁).map ι ∧
      (∀ B ∈ Subgroup.centralizer ({A} : Set (GL (Fin d) F)), ∃ B₁ : GL (Fin d₁) D₁,
        ∀ g : ↥(StatedSL d₁ D₁),
          B * (ι g : GL (Fin d) F) * B⁻¹ = ι (B₁ * (g : GL (Fin d₁) D₁) * B₁⁻¹)) ∧
      (∀ g : ↥(StatedSL d₁ D₁), (∃ z : Fˣ, ι g = Matrix.GeneralLinearGroup.scalar (Fin d) z) →
        ∃ w : D₁ˣ, (g : GL (Fin d₁) D₁) = Matrix.GeneralLinearGroup.scalar (Fin d₁) w) ∧
      ∃ E : Matrix (Fin d) (Fin d) F, E ≠ 0 ∧ ∀ c : F, ∃ t ∈ StatedSL d₁ D₁,
        ((ι t : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1 + c • E := by
  classical
  have hA' : (Nat.card (Subgroup.zpowers A) : F) ≠ 0 := by
    rw [Nat.card_zpowers]
    exact hA
  obtain ⟨r, D, dd, hFld, hFin, hAlg, Φ, θ, _hNZ, hΦinj, _hΦrange, hθinj, hθrange, hθapply⟩ :=
    exists_piMat_commutant (Subgroup.zpowers A) hA'
  letI : ∀ i, Field (D i) := hFld
  haveI : ∀ i, Finite (D i) := hFin
  letI : ∀ i, Algebra F (D i) := hAlg
  have hcent : Subgroup.centralizer ((Subgroup.zpowers A : Subgroup (GL (Fin d) F)) :
      Set (GL (Fin d) F)) = Subgroup.centralizer ({A} : Set (GL (Fin d) F)) := by
    ext g
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hg h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hg _ (Subgroup.mem_zpowers _)
    · intro hg h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hc : Commute A g := hg A (Set.mem_singleton A)
      exact (hc.zpow_left k).eq
  have hCeq : Subgroup.centralizer ({A} : Set (GL (Fin d) F)) ⊓ StatedSL d F =
      ((StatedSL d F).comap θ).map θ := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      have hxr : x ∈ θ.range := by
        rw [hθrange, hcent]
        exact hx1
      obtain ⟨w, rfl⟩ := MonoidHom.mem_range.mp hxr
      exact Subgroup.mem_map.mpr ⟨w, hx2, rfl⟩
    · intro hx
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
      refine ⟨?_, hw⟩
      rw [← hcent, ← hθrange]
      exact MonoidHom.mem_range.mpr ⟨w, rfl⟩
  rw [hCeq] at hM
  obtain ⟨i, h2d, h22, h23, hMi⟩ := linear_pcomp_core' θ hθinj p M hM
  have hd0 : 0 < dd i := by omega
  have hd1 : 1 < dd i := by omega
  set a0 : Fin (dd i) := ⟨0, hd0⟩ with ha0
  set a1 : Fin (dd i) := ⟨1, hd1⟩ with ha1
  have ha : a0 ≠ a1 := by simp [ha0, ha1, Fin.ext_iff]
  refine ⟨dd i, D i, hFld i, hFin i,
    θ.comp (MonoidHom.mulSingle (fun j => GL (Fin (dd j)) (D j)) i),
    ?_, h2d, h22, h23, hθinj.comp (mulSingle_injective' i), ?_, ?_, ?_, ?_⟩
  · have := map_ofNat (algebraMap F (D i)) 2
    rw [h2, map_zero] at this
    exact this.symm
  · rw [hMi, factorSL', Subgroup.map_map]
  ·
    intro B hB
    have hBmem : B ∈ θ.range := by
      rw [hθrange, hcent]
      exact hB
    obtain ⟨β, hβ⟩ := MonoidHom.mem_range.mp hBmem
    refine ⟨β i, fun g => ?_⟩
    rw [← hβ]
    show (θ β * θ (MonoidHom.mulSingle (fun j => GL (Fin (dd j)) (D j)) i
        (g : GL (Fin (dd i)) (D i))) * (θ β)⁻¹) =
      θ (MonoidHom.mulSingle (fun j => GL (Fin (dd j)) (D j)) i
        (β i * (g : GL (Fin (dd i)) (D i)) * (β i)⁻¹))
    rw [← map_inv, ← map_mul, ← map_mul, mulSingle_conj']
  ·
    intro g hg
    obtain ⟨z, hz⟩ := hg
    have hΦM : Φ (fun j => (((MonoidHom.mulSingle (fun j => GL (Fin (dd j)) (D j)) i
        (g : GL (Fin (dd i)) (D i))) j : GL (Fin (dd j)) (D j)) :
          Matrix (Fin (dd j)) (Fin (dd j)) (D j))) =
        (z : F) • (1 : Matrix (Fin d) (Fin d) F) := by
      rw [← hθapply]
      rw [show ((θ (MonoidHom.mulSingle (fun j => GL (Fin (dd j)) (D j)) i
          (g : GL (Fin (dd i)) (D i))) : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
          ((Matrix.GeneralLinearGroup.scalar (Fin d) z : GL (Fin d) F) :
            Matrix (Fin d) (Fin d) F) from congrArg Units.val hz]
      ext a b
      rw [Matrix.smul_apply, Matrix.one_apply, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply]
      by_cases hab : a = b <;> simp [hab]
    have hcoord : (fun j => ((algebraMap F (D j) z) • (1 : Matrix (Fin (dd j)) (Fin (dd j)) (D j)))) =
        (fun j => (((MonoidHom.mulSingle (fun j => GL (Fin (dd j)) (D j)) i
          (g : GL (Fin (dd i)) (D i))) j : GL (Fin (dd j)) (D j)) :
            Matrix (Fin (dd j)) (Fin (dd j)) (D j))) := by
      apply hΦinj
      have hsmul : ∀ (j : Fin r) (c : F), (c • (1 : Matrix (Fin (dd j)) (Fin (dd j)) (D j)))
          = algebraMap F (D j) c • (1 : Matrix (Fin (dd j)) (Fin (dd j)) (D j)) := by
        intro j c
        ext a b
        by_cases hab : a = b <;>
          simp [Matrix.smul_apply, Matrix.one_apply, Algebra.smul_def, hab]
      have e1 : (fun j => (algebraMap F (D j) (z : F)) •
          (1 : Matrix (Fin (dd j)) (Fin (dd j)) (D j))) =
          (algebraMap F (Π j, Matrix (Fin (dd j)) (Fin (dd j)) (D j))) (z : F) := by
        rw [Algebra.algebraMap_eq_smul_one]
        funext j
        exact (hsmul j (z : F)).symm
      calc Φ (fun j => (algebraMap F (D j) (z : F)) •
            (1 : Matrix (Fin (dd j)) (Fin (dd j)) (D j)))
          = Φ ((algebraMap F (Π j, Matrix (Fin (dd j)) (Fin (dd j)) (D j))) (z : F)) := by
            rw [e1]
        _ = (algebraMap F (Matrix (Fin d) (Fin d) F)) (z : F) := AlgHom.commutes Φ (z : F)
        _ = (z : F) • (1 : Matrix (Fin d) (Fin d) F) :=
            Algebra.algebraMap_eq_smul_one (z : F)
        _ = Φ (fun j => (((MonoidHom.mulSingle (fun j => GL (Fin (dd j)) (D j)) i
              (g : GL (Fin (dd i)) (D i))) j : GL (Fin (dd j)) (D j)) :
                Matrix (Fin (dd j)) (Fin (dd j)) (D j))) := hΦM.symm
    have hgi : ((g : GL (Fin (dd i)) (D i)) : Matrix (Fin (dd i)) (Fin (dd i)) (D i)) =
        (algebraMap F (D i) z) • (1 : Matrix (Fin (dd i)) (Fin (dd i)) (D i)) := by
      have := congrFun hcoord i
      simpa [MonoidHom.mulSingle_apply] using this.symm
    have hμ0 : algebraMap F (D i) z ≠ 0 := by
      rintro h0
      have hzero : ((g : GL (Fin (dd i)) (D i)) : Matrix (Fin (dd i)) (Fin (dd i)) (D i)) = 0 := by
        rw [hgi, h0, zero_smul]
      exact Units.ne_zero (u := (g : GL (Fin (dd i)) (D i))) hzero
    refine ⟨Units.mk0 (algebraMap F (D i) z) hμ0, ?_⟩
    apply Units.ext
    rw [hgi, Matrix.GeneralLinearGroup.coe_scalar]
    ext a b
    rw [Matrix.smul_apply, Matrix.one_apply, Matrix.scalar_apply]
    by_cases hab : a = b <;> simp [hab, Units.val_mk0]
  ·
    let e01 : Matrix (Fin (dd i)) (Fin (dd i)) (D i) := Matrix.single a0 a1 1
    refine ⟨Φ (Pi.single i e01), ?_, fun c => ?_⟩
    · intro h0
      have h1 : (Pi.single i e01 : ∀ j, Matrix (Fin (dd j)) (Fin (dd j)) (D j)) = 0 :=
        hΦinj (by rw [h0, map_zero])
      have h3 := congrFun h1 i
      have h4 := congrFun (congrFun h3 a0) a1
      simp [e01] at h4
    · refine ⟨l154TransvecGL a0 a1 ha (algebraMap F (D i) c), l154TransvecGL_mem a0 a1 ha _, ?_⟩
      show ((θ (MonoidHom.mulSingle (fun j => GL (Fin (dd j)) (D j)) i
        (l154TransvecGL a0 a1 ha (algebraMap F (D i) c))) : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = _
      rw [hθapply]
      have hce : c • e01 = Matrix.single a0 a1 (algebraMap F (D i) c) := by
        ext x y
        rw [Matrix.smul_apply]
        simp [e01, Matrix.single_apply, Algebra.smul_def]
      have hfun : (fun j => (((MonoidHom.mulSingle (fun j => GL (Fin (dd j)) (D j)) i
          (l154TransvecGL a0 a1 ha (algebraMap F (D i) c))) j : GL (Fin (dd j)) (D j)) :
            Matrix (Fin (dd j)) (Fin (dd j)) (D j))) =
          1 + c • (Pi.single i e01 : ∀ j, Matrix (Fin (dd j)) (Fin (dd j)) (D j)) := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same, Pi.add_apply, Pi.one_apply,
            Pi.smul_apply, Pi.single_eq_same]
          show Matrix.transvection a0 a1 (algebraMap F (D j) c) = 1 + c • e01
          rw [hce]
          rfl
        · simp [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj, Pi.single_eq_of_ne hj]
      rw [hfun, map_add, map_one, map_smul]

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
