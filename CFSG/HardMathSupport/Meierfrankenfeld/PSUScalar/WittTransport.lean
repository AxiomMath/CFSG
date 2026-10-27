module

public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.LieType.Universal.Unitary.Extras.Basic
public import CFSG.HardMathSupport.GuralnickMalle.SLnNatural2F
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.KroneckerFixed
public import CFSG.HardMathSupport.GuralnickMalle.BasicGeneral

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

open Matrix Module CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.HardMathSupport.GuralnickMalle
open CFSG.Open

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

@[expose] noncomputable def wittMat (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ) : GL (Fin n) F :=
  (exists_wittMatrix hF n).choose

theorem wittMat_spec (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ) :
    conjTr (unitaryInvolution F p f) (wittMat hF n : Matrix (Fin n) (Fin n) F) *
      (wittMat hF n : Matrix (Fin n) (Fin n) F) = antidiag n :=
  (exists_wittMatrix hF n).choose_spec

@[expose] noncomputable def suToStated (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ) :
    SU (unitaryInvolution F p f) n ≃* StatedSU n (p ^ f) F :=
  (conjEquiv (wittMat hF n) (wittMat_spec hF n)).trans
    (MulEquiv.subgroupCongr (SUid_eq_statedSU hF n))

theorem coe_suToStated (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ)
    (g : SU (unitaryInvolution F p f) n) :
    ((suToStated hF n g : StatedSU n (p ^ f) F) : GL (Fin n) F) =
      wittMat hF n * (g : GL (Fin n) F) * (wittMat hF n)⁻¹ :=
  rfl

theorem coe_suToStated_symm (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ)
    (g : StatedSU n (p ^ f) F) :
    (((suToStated hF n).symm g : SU (unitaryInvolution F p f) n) : GL (Fin n) F) =
      (wittMat hF n)⁻¹ * (g : GL (Fin n) F) * wittMat hF n := by
  have h := coe_suToStated hF n ((suToStated hF n).symm g)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h]
  group

theorem scalar_mem_SU_of_mem_statedSU (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ} {c : Fˣ}
    (hc : GeneralLinearGroup.scalar (Fin n) c ∈ StatedSU n (p ^ f) F) :
    GeneralLinearGroup.scalar (Fin n) c ∈ SU (unitaryInvolution F p f) n := by
  let x : SU (unitaryInvolution F p f) n :=
    (suToStated hF n).symm ⟨GeneralLinearGroup.scalar (Fin n) c, hc⟩
  have hcoe := coe_suToStated_symm hF n ⟨GeneralLinearGroup.scalar (Fin n) c, hc⟩
  have hcomm := GeneralLinearGroup.scalar_commute (n := Fin n) c (wittMat hF n)
  have hx : (x : GL (Fin n) F) = GeneralLinearGroup.scalar (Fin n) c := by
    rw [hcoe]
    calc (wittMat hF n)⁻¹ * GeneralLinearGroup.scalar (Fin n) c * wittMat hF n
        = (wittMat hF n)⁻¹ *
            (GeneralLinearGroup.scalar (Fin n) c * wittMat hF n) := by
          rw [mul_assoc]
      _ = (wittMat hF n)⁻¹ *
            (wittMat hF n * GeneralLinearGroup.scalar (Fin n) c) := by
          rw [hcomm]
      _ = GeneralLinearGroup.scalar (Fin n) c := by
          rw [← mul_assoc, inv_mul_cancel, one_mul]
  rw [← hx]
  exact x.2

theorem suToStated_scalar (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ} {c : Fˣ}
    (hc : GeneralLinearGroup.scalar (Fin n) c ∈ StatedSU n (p ^ f) F) :
    suToStated hF n ⟨_, scalar_mem_SU_of_mem_statedSU hF hc⟩ = ⟨_, hc⟩ := by
  apply Subtype.ext
  rw [coe_suToStated]
  show wittMat hF n * GeneralLinearGroup.scalar (Fin n) c * (wittMat hF n)⁻¹ =
    GeneralLinearGroup.scalar (Fin n) c
  have hcomm := GeneralLinearGroup.scalar_commute (n := Fin n) c (wittMat hF n)
  calc wittMat hF n * GeneralLinearGroup.scalar (Fin n) c * (wittMat hF n)⁻¹
      = (wittMat hF n * GeneralLinearGroup.scalar (Fin n) c) * (wittMat hF n)⁻¹ := by
        rw [mul_assoc]
    _ = (GeneralLinearGroup.scalar (Fin n) c * wittMat hF n) * (wittMat hF n)⁻¹ := by
        rw [← hcomm]
    _ = GeneralLinearGroup.scalar (Fin n) c := by
        rw [mul_assoc, mul_inv_cancel, mul_one]

variable {k : Type} [Field k]

@[expose] noncomputable def suNaturalRep (φ : F →+* k) (σ : F ≃+* F) (n : ℕ) :
    Representation k (SU σ n) (Fin n → k) :=
  (glNaturalRep n k).comp ((GeneralLinearGroup.map φ).comp (SU σ n).subtype)

omit [Finite F] in
theorem suNaturalRep_apply (φ : F →+* k) (σ : F ≃+* F) (n : ℕ) (g : SU σ n)
    (v : Fin n → k) :
    suNaturalRep φ σ n g v = (SUExtras.mat σ n g).map φ *ᵥ v := by
  have hmapval (x : GL (Fin n) F) :
      ((GeneralLinearGroup.map φ x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
        (x : Matrix (Fin n) (Fin n) F).map φ := rfl
  simp only [suNaturalRep, glNaturalRep, MonoidHom.comp_apply, Units.coeHom_apply,
    MulEquiv.coe_toMonoidHom, Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply,
    SUExtras.mat_apply]
  exact congrArg (fun M => M *ᵥ v) (hmapval ((SU σ n).subtype g))

theorem finrank_fixSubGen_suNaturalRep (hF : Nat.card F = (p ^ f) ^ 2) (φ : F →+* k) {n : ℕ}
    (P : Subgroup (StatedSU n (p ^ f) F)) :
    finrank k (fixSubGen (suNaturalRep φ (unitaryInvolution F p f) n)
        (P.comap (suToStated hF n).toMonoidHom)) =
      finrank F (fixSubGen (glNaturalRep n F) (P.map (StatedSU n (p ^ f) F).subtype)) := by
  classical
  let σ := unitaryInvolution F p f
  let q := p ^ f
  let eQS : SU σ n ≃* StatedSU n q F := suToStated hF n
  let P' : Subgroup (SU σ n) := P.comap eQS.toMonoidHom
  let P'GL : Subgroup (GL (Fin n) F) := P'.map (SU σ n).subtype
  let e : P' ≃ Fin (Nat.card P') := Finite.equivFin P'
  let T : Fin (Nat.card P') → Matrix (Fin n) (Fin n) F :=
    fun i => SUExtras.mat σ n ((e.symm i : P') : SU σ n)
  let W : GL (Fin n) F := wittMat hF n
  have hgl : ∀ (x : GL (Fin n) F) (v : Fin n → F),
      glNaturalRep n F x v = (x : Matrix (Fin n) (Fin n) F) *ᵥ v := by
    intro x v
    simp only [glNaturalRep, MonoidHom.comp_apply, Units.coeHom_apply,
      MulEquiv.coe_toMonoidHom, Matrix.GeneralLinearGroup.toLin_apply,
      Matrix.mulVecLin_apply]
  have hfixK : fixSubGen (suNaturalRep φ σ n) P' =
      matFix (fun i : Fin (Nat.card P') => (T i).map φ) := by
    ext v
    rw [mem_fixSubGen, mem_matFix]
    constructor
    · intro h i
      have h' := h (e.symm i) (e.symm i).2
      rwa [suNaturalRep_apply] at h'
    · intro h g hg
      have h' := h (e ⟨g, hg⟩)
      rw [show T (e ⟨g, hg⟩) = SUExtras.mat σ n g by simp [T]] at h'
      rwa [suNaturalRep_apply]
  have hfixF : fixSubGen (glNaturalRep n F) P'GL = matFix T := by
    ext v
    rw [mem_fixSubGen, mem_matFix]
    constructor
    · intro h i
      have h' := h (↑(e.symm i) : GL (Fin n) F)
        (Subgroup.mem_map_of_mem (SU σ n).subtype (e.symm i).2)
      rw [hgl] at h'
      simpa [T, SUExtras.mat_apply] using h'
    · intro h x hx
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
      have h' := h (e ⟨g, hg⟩)
      rw [show T (e ⟨g, hg⟩) = SUExtras.mat σ n g by simp [T]] at h'
      rw [hgl]
      simpa [SUExtras.mat_apply] using h'
  have hmap : P.map (StatedSU n q F).subtype =
      P'GL.map (MulAut.conj W).toMonoidHom := by
    ext x
    constructor
    · intro hx
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hx
      have hmem : (↑(eQS.symm p) : GL (Fin n) F) ∈ P'GL := by
        change (SU σ n).subtype (eQS.symm p) ∈ P'.map (SU σ n).subtype
        exact Subgroup.mem_map_of_mem (SU σ n).subtype (by
          show eQS (eQS.symm p) ∈ P
          rw [MulEquiv.apply_symm_apply]
          exact hp)
      refine Subgroup.mem_map.2 ⟨↑(eQS.symm p), hmem, ?_⟩
      · have h := coe_suToStated hF n (eQS.symm p)
        rw [MulEquiv.apply_symm_apply] at h
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact h.symm
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hy
      refine Subgroup.mem_map.2 ⟨eQS g, ?_, ?_⟩
      · show eQS g ∈ P
        exact hg
      · have h := coe_suToStated hF n g
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact h
  have hfin : finrank k (fixSubGen (suNaturalRep φ σ n) P') = finrank F (matFix T) := by
    rw [hfixK, finrank_matFix_map]
  change finrank k (fixSubGen (suNaturalRep φ σ n) P') =
    finrank F (fixSubGen (glNaturalRep n F) (P.map (StatedSU n q F).subtype))
  rw [hfin, hmap, fixSubGen_map_conj]
  let E : (Fin n → F) ≃ₗ[F] (Fin n → F) :=
    LinearEquiv.ofBijective ((glNaturalRep n F) W) ((glNaturalRep n F).apply_bijective W)
  have hE : (fixSubGen (glNaturalRep n F) P'GL).map ((glNaturalRep n F) W) =
      (fixSubGen (glNaturalRep n F) P'GL).map E.toLinearMap := rfl
  rw [hE, LinearEquiv.finrank_map_eq, hfixF]

end CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
