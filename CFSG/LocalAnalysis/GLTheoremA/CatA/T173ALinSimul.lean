module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinDefs
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open scoped MatrixGroups IsMulCommutative

private theorem hasEnoughRootsOfUnity_of_dvd_card_sub_one {F : Type} [Field F] [Finite F]
    {n : ℕ} [NeZero n] (hn : n ∣ Nat.card F - 1) : HasEnoughRootsOfUnity F n := by
  set N := Nat.card F - 1 with hN
  have hNu : Nat.card Fˣ = N := Nat.card_units F
  have hNpos : 0 < N := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    omega
  haveI : NeZero N := ⟨by omega⟩
  have htop : rootsOfUnity N F = ⊤ := by
    ext x
    simp only [mem_rootsOfUnity, Subgroup.mem_top, iff_true]
    rw [← hNu]
    exact pow_card_eq_one'
  have hNcard : N ≤ Nat.card (rootsOfUnity N F) := by
    rw [htop, Subgroup.card_top, hNu]
  haveI : HasEnoughRootsOfUnity F N := HasEnoughRootsOfUnity.of_card_le hNcard
  exact HasEnoughRootsOfUnity.of_dvd F hn

theorem lin_simul_diag {p n d : ℕ} {F : Type} [Field F] [Finite F] (h : LinArith p n d F)
    {A₀ : Subgroup (GL (Fin d) F)} (hA : IsElemAbelian p A₀) :
    ∃ g : GL (Fin d) F, ∀ a ∈ A₀, ∀ i j : Fin d, i ≠ j →
      ((g * a * g⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i j = 0 := by
  classical
  obtain ⟨hp, hpne2, hpdvd, hpd, hcardF, hn, hd⟩ := h
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : IsMulCommutative ↥A₀ := hA.1
  let ρ : ↥A₀ →* Module.End F (Fin d → F) :=
    { toFun := fun a => Matrix.toLinAlgEquiv' ((a : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)
      map_one' := by
        show Matrix.toLinAlgEquiv' (((1 : ↥A₀) : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1
        rw [show ((1 : ↥A₀) : GL (Fin d) F) = 1 from map_one (Subgroup.subtype A₀),
          Units.val_one, map_one]
      map_mul' := by
        intro a b
        show Matrix.toLinAlgEquiv'
            ((((a * b : ↥A₀) : GL (Fin d) F)) : Matrix (Fin d) (Fin d) F) =
          Matrix.toLinAlgEquiv' ((a : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
            Matrix.toLinAlgEquiv' ((b : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)
        rw [show ((a * b : ↥A₀) : GL (Fin d) F) =
            (a : GL (Fin d) F) * (b : GL (Fin d) F) from
          map_mul (Subgroup.subtype A₀) a b, Units.val_mul, map_mul] }
  have hEnoughP : HasEnoughRootsOfUnity F p := by
    have hdvd : p ∣ Nat.card F - 1 := by rw [hcardF]; exact hpdvd
    exact hasEnoughRootsOfUnity_of_dvd_card_sub_one hdvd
  have hExpDvd : Monoid.exponent ↥A₀ ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
      apply Subtype.ext
      change (a : GL (Fin d) F) ^ p = 1
      exact hA.2 (a : GL (Fin d) F) a.2
  haveI : HasEnoughRootsOfUnity F p := hEnoughP
  haveI : HasEnoughRootsOfUnity F (Monoid.exponent ↥A₀) :=
    HasEnoughRootsOfUnity.of_dvd F hExpDvd
  have hchar2 : ringChar F = 2 := by
    letI : Fintype F := Fintype.ofFinite F
    rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card, hcardF]
    exact Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega : n ≠ 0))
  haveI hCharP : CharP F 2 := ringChar.of_eq hchar2
  haveI : Fact p.Prime := ⟨hp⟩
  have hIsP : IsPGroup p ↥A₀ := fun a => ⟨1, by
    have hp1 : a ^ p = 1 := by
      apply Subtype.ext
      change (a : GL (Fin d) F) ^ p = 1
      exact hA.2 (a : GL (Fin d) F) a.2
    simpa using hp1⟩
  have hcardUnit : IsUnit (Nat.card ↥A₀ : F) := by
    rw [isUnit_iff_ne_zero]
    intro hzero
    have h2dvd : 2 ∣ Nat.card ↥A₀ := (CharP.cast_eq_zero_iff F 2 _).mp hzero
    obtain ⟨k, hk⟩ := hIsP.exists_card_eq
    have hpodd : Odd p := hp.odd_of_ne_two hpne2
    rw [hk] at h2dvd
    exact (Nat.not_even_iff_odd.mpr hpodd.pow) (even_iff_two_dvd.mpr h2dvd)
  let W : (↥A₀ →* Fˣ) → Submodule F (Fin d → F) := fun χ => ⨅ a, (ρ a).eigenspace (χ a)
  have hind : iSupIndep W := TauCeti.iSupIndep_iInf_eigenspace_unitHom (ρ := ρ)
  have htop : ⨆ χ, W χ = ⊤ :=
    TauCeti.iSup_iInf_eigenspace_unitHom_eq_top_of_commGroup (ρ := ρ) hcardUnit
  have hint : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  let b₀ := hint.collectedBasis (fun χ => Module.finBasis F (W χ))
  let e := b₀.indexEquiv (Pi.basisFun F (Fin d))
  let bas : Module.Basis (Fin d) F (Fin d → F) := b₀.reindex e
  have hbas_mem : ∀ j : Fin d, bas j ∈ W (e.symm j).1 := by
    intro j
    rw [Module.Basis.reindex_apply]
    exact hint.collectedBasis_mem _ (e.symm j)
  have heig : ∀ (a : ↥A₀) (j : Fin d),
      ρ a (bas j) = ((e.symm j).1 a : F) • bas j := by
    intro a j
    exact Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp (hbas_mem j) a)
  let hlin : (Fin d → F) →ₗ[F] (Fin d → F) := bas.equivFun
  let hlin' : (Fin d → F) →ₗ[F] (Fin d → F) := bas.equivFun.symm
  have hbas_std : ∀ j : Fin d, hlin (bas j) = Pi.single j (1 : F) := by
    intro j
    funext i
    show bas.equivFun (bas j) i = (Pi.single j (1 : F) : Fin d → F) i
    rw [Module.Basis.equivFun_self]
    by_cases hji : j = i
    · subst hji
      simp
    · rw [if_neg hji, Pi.single_eq_of_ne' hji]
  have hsymm_std : ∀ j : Fin d, hlin' (Pi.single j (1 : F)) = bas j := by
    intro j
    rw [← hbas_std j]
    show bas.equivFun.symm (bas.equivFun (bas j)) = bas j
    exact bas.equivFun.symm_apply_apply (bas j)
  have hcomp : hlin' * hlin = 1 := by
    apply LinearMap.ext
    intro v
    rw [Module.End.mul_apply, Module.End.one_apply]
    show bas.equivFun.symm (bas.equivFun v) = v
    exact bas.equivFun.symm_apply_apply v
  set H : Matrix (Fin d) (Fin d) F := LinearMap.toMatrixAlgEquiv' hlin with hHdef
  set H' : Matrix (Fin d) (Fin d) F := LinearMap.toMatrixAlgEquiv' hlin' with hH'def
  have hH'H : H' * H = 1 := by
    rw [hH'def, hHdef, ← map_mul, hcomp, map_one]
  have hdetH : IsUnit H.det := Matrix.isUnit_det_of_left_inverse hH'H
  let g : GL (Fin d) F := Matrix.GeneralLinearGroup.mk'' H hdetH
  refine ⟨g, ?_⟩
  intro a ha i j hij
  have hmat : ((g * a * g⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i j =
      (LinearMap.toMatrixAlgEquiv' (hlin * (ρ ⟨a, ha⟩) * hlin')) i j := by
    apply congrArg (fun M : Matrix (Fin d) (Fin d) F => M i j)
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_inv, show (g : Matrix (Fin d) (Fin d) F) = H from rfl,
      show H⁻¹ = H' from Matrix.inv_eq_left_inv hH'H,
      show (a : Matrix (Fin d) (Fin d) F) = LinearMap.toMatrixAlgEquiv' (ρ ⟨a, ha⟩) from
        (LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' _).symm,
      hHdef, hH'def]
    rw [← map_mul, ← map_mul]
  rw [hmat, LinearMap.toMatrixAlgEquiv'_apply]
  rw [Module.End.mul_apply, Module.End.mul_apply, hsymm_std j, heig ⟨a, ha⟩ j,
    map_smul, hbas_std j]
  simp [hij, Ne.symm hij]

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
