module

public import CFSG.CGT.Foote82.T66.BranchBBasic
public import CFSG.CGT.Foote82.T66.CitedBB
public import CFSG.ClassicalGroups.Orthogonal.Matrix
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
public import CFSG.LieType.Universal.Spin.Forms

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.PGLModel Matrix

namespace BranchB

section ConjMat

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

noncomputable def conjMat (ψ : W ≃ₗ[ZMod 2] (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2)) :
    GLV W →* GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) where
  toFun g := (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)).symm
    (ψ.symm.trans (g.trans ψ))
  map_one' := by
    apply (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)).injective
    rw [MulEquiv.apply_symm_apply, map_one]
    exact LinearEquiv.ext fun x => ψ.apply_symm_apply x
  map_mul' g h := by
    apply (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)).injective
    rw [MulEquiv.apply_symm_apply, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    refine LinearEquiv.ext fun x => ?_
    show ψ (g (h (ψ.symm x))) = ψ (g (ψ.symm (ψ (h (ψ.symm x)))))
    rw [ψ.symm_apply_apply]

theorem conjMat_mulVec (ψ : W ≃ₗ[ZMod 2] (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2)) (g : GLV W)
    (x : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2) :
    ((conjMat ψ g : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ x =
      ψ (g (ψ.symm x)) := by
  have := congrArg (fun f => f x)
    ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)).apply_symm_apply
      (ψ.symm.trans (g.trans ψ)))
  exact this

theorem gl_ext {A B : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)}
    (h : ∀ x, (A : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ x =
      (B : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ x) : A = B := by
  apply (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)).injective
  exact LinearEquiv.ext fun x => h x

end ConjMat

section Dickson

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem dickson_mul (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {g t : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    (Module.finrank (ZMod 2)
        ↥(LinearMap.range (((g * t : V ≃ₗ[ZMod 2] V) : Module.End (ZMod 2) V) - 1)) : ZMod 2) =
      Module.finrank (ZMod 2) ↥(LinearMap.range ((g : Module.End (ZMod 2) V) - 1)) +
        Module.finrank (ZMod 2) ↥(LinearMap.range ((t : Module.End (ZMod 2) V) - 1)) :=
  CFSG.RankThree.OrthogonalInvolutions.natCast_finrank_commSpace_mul hQ hg ht

theorem mem_commutator_iff_even (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (h6 : 6 ≤ Module.finrank (ZMod 2) V) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ↔
      Even (Module.finrank (ZMod 2) ↥(LinearMap.range ((g : Module.End (ZMod 2) V) - 1))) := by
  rw [CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup hQ h6,
    CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup]
  exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩

end Dickson

noncomputable abbrev dimComm (g : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) : ℕ :=
  Module.finrank (ZMod 2) ↥(LinearMap.range (Matrix.mulVecLin
    ((g : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) - 1)))

theorem dimComm_eq (g : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
    dimComm g = Module.finrank (ZMod 2) ↥(LinearMap.range
      (((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) g) :
        Module.End (ZMod 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2)) - 1)) := by
  have e : Matrix.mulVecLin
      ((g : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) - 1) =
      (((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) g) :
        Module.End (ZMod 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2)) - 1) := by
    refine LinearMap.ext fun x => ?_
    rw [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec, LinearMap.sub_apply,
      Module.End.one_apply, LinearEquiv.coe_coe,
      CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
  show Module.finrank (ZMod 2) ↥(LinearMap.range (Matrix.mulVecLin
    ((g : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) - 1))) = _
  rw [e]

private theorem coe_quadMinus₆ :
    ⇑(CFSG.LieType.Universal.Spin.quadMinus (2 + 1) (ZMod 2) (1 : ZMod 2) 1) =
      CFSG.Open.StatedQuadMinus (2 + 1) (ZMod 2) 1 1 :=
  CFSG.LieType.Universal.Spin.coe_quadMinus (2 + 1) (ZMod 2) 1 1

private theorem nondeg₆ : (QuadraticMap.polarBilin
    (CFSG.LieType.Universal.Spin.quadMinus (2 + 1) (ZMod 2) (1 : ZMod 2) 1)).Nondegenerate :=
  CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (2 + 1) (ZMod 2)
    CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.irreducible_one_one

theorem mem_orthogonalMinus_iff {g : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)} :
    g ∈ orthogonalMinus 2 (ZMod 2) 1 1 ↔
      CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) g ∈
        TauCeti.QuadraticMap.orthogonalGroup
          (CFSG.LieType.Universal.Spin.quadMinus (2 + 1) (ZMod 2) (1 : ZMod 2) 1) := by
  have := CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap coe_quadMinus₆
  exact SetLike.ext_iff.1 this g

theorem mem_omegaMinusTwo_iff {g : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)}
    (hg : g ∈ orthogonalMinus 2 (ZMod 2) 1 1) :
    g ∈ omegaMinusTwo 2 ↔ Even (dimComm g) := by
  have h6 : 6 ≤ Module.finrank (ZMod 2) (Fin (2 + 1 - 1) ⊕ Fin (2 + 1 - 1) ⊕ Fin 2 → ZMod 2) := by
    rw [CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.finrank_minus]
  have hΩ : omegaMinusTwo 2 =
      ⁅TauCeti.QuadraticMap.orthogonalGroup
          (CFSG.LieType.Universal.Spin.quadMinus (2 + 1) (ZMod 2) (1 : ZMod 2) 1),
        TauCeti.QuadraticMap.orthogonalGroup
          (CFSG.LieType.Universal.Spin.quadMinus (2 + 1) (ZMod 2) (1 : ZMod 2) 1)⁆.comap
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2)
          (ZMod 2)).toMonoidHom := by
    rw [CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.omegaMinusTwo_eq_statedOmega,
      CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap coe_quadMinus₆]
  rw [hΩ, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
    mem_commutator_iff_even nondeg₆ h6 (mem_orthogonalMinus_iff.1 hg), dimComm_eq]

theorem mem_omega_or_mul_mem {g t : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)}
    (hg : g ∈ orthogonalMinus 2 (ZMod 2) 1 1) (ht : t ∈ orthogonalMinus 2 (ZMod 2) 1 1)
    (ht1 : dimComm t = 1) : g ∈ omegaMinusTwo 2 ∨ g * t ∈ omegaMinusTwo 2 := by
  rw [mem_omegaMinusTwo_iff hg,
    mem_omegaMinusTwo_iff ((orthogonalMinus 2 (ZMod 2) 1 1).mul_mem hg ht)]
  have hadd := dickson_mul nondeg₆ (mem_orthogonalMinus_iff.1 hg) (mem_orthogonalMinus_iff.1 ht)
  rw [← map_mul (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) g t,
    ← dimComm_eq, ← dimComm_eq, ← dimComm_eq, ht1] at hadd
  rcases Nat.even_or_odd (dimComm g) with he | ho
  · exact Or.inl he
  · right
    rw [← ZMod.natCast_eq_zero_iff_even, hadd]
    rw [← ZMod.natCast_eq_one_iff_odd] at ho
    rw [ho]
    decide

theorem isQuasisimple_omegaMinusTwo_two : CFSG.Open.IsQuasisimple ↥(omegaMinusTwo 2) := by
  obtain ⟨hs, hc, hna⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.isSimpleGroup_statedOmega_quadMinus_small
      (K := ZMod 2) (n := 2 + 1) (Or.inr rfl)
      CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.irreducible_one_one
  have hs' : IsSimpleGroup ↥(omegaMinusTwo 2) := hs
  have hc' : commutator ↥(omegaMinusTwo 2) = ⊤ := hc
  have hna' : ¬ ∀ x y : ↥(omegaMinusTwo 2), x * y = y * x := hna
  refine ⟨hc', ?_⟩
  have hZ : Subgroup.center ↥(omegaMinusTwo 2) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(omegaMinusTwo 2)) with
      h0 | h0
    · exact h0
    · exact absurd (fun x y => Subgroup.mem_center_iff.1 (h0 ▸ Subgroup.mem_top y) x) hna'
  have e : ↥(omegaMinusTwo 2) ⧸ Subgroup.center ↥(omegaMinusTwo 2) ≃* ↥(omegaMinusTwo 2) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact e.isSimpleGroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

namespace Hyp

variable {G L : Subgroup (GLV V)} {z : GLV V} {v : V} (h : Hyp G L z v)

include h

theorem caseIIData (hN : OmegaMinusSixNormalizer) (hG1 : OmegaMinusSixA6Centralizer)
    (eL : Nonempty (↥((L.subgroupOf (bbH₁ G L z v)).map (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁)) ≃*
      alternatingGroup (Fin 6)))
    (hΩ : IsOmegaMinusFor (layerIn (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range) 2) :
    ∃ ψ : ↥(bbH₁ G L z v) ≃* ↥(orthogonalMinus 2 (ZMod 2) 1 1),
      CaseIIData G L z v (bbH₁ G L z v) ψ := by
  obtain ⟨eL⟩ := eL
  set φ := sectHom (bbH₁ G L z v) h.inv₀ h.inv₁ with hφ
  obtain ⟨φΩ, ψW, hψW⟩ := hΩ
  obtain ⟨z₁, hz₁⟩ : ∃ z₁ : ↥(bbH₁ G L z v), z₁ = ⟨z, h.z_mem_H₁⟩ := ⟨_, rfl⟩
  let M : ↥(bbH₁ G L z v) →* GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) := (conjMat ψW).comp φ
  have hMx : ∀ g x, ((M g : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ x =
      ψW (φ g (ψW.symm x)) := fun g x => conjMat_mulVec ψW (φ g) x
  have hML₀ : ∀ (a : ↥(bbH₁ G L z v)) (ha : (a : GLV V) ∈ bbL₀ G L v),
      M a = (φΩ ⟨_, h.map_mem_layerIn ha⟩ : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) := by
    intro a ha
    refine gl_ext fun x => ?_
    rw [hMx]
    have := hψW ⟨_, h.map_mem_layerIn ha⟩ (ψW.symm x)
    rwa [LinearEquiv.apply_symm_apply] at this
  have hMinj : Function.Injective M := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hfix : φ g = 1 := by
      refine LinearEquiv.ext fun y => ?_
      have h1 := hMx g (ψW y)
      rw [hg, Units.val_one, Matrix.one_mulVec, LinearEquiv.symm_apply_apply] at h1
      exact ψW.injective h1.symm
    exact h.injective (hfix.trans (map_one φ).symm)
  have hMΩ : ((bbL₀ G L v).subgroupOf (bbH₁ G L z v)).map M = omegaMinusTwo 2 := by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      rw [hML₀ a ha]
      exact (φΩ _).2
    · intro x hx
      obtain ⟨w, hw⟩ := φΩ.surjective ⟨x, hx⟩
      have hw' : (w : GLV (Sect (bbW₀ G L v) (bbW₁ G L v))) ∈
          ((bbL₀ G L v).subgroupOf (bbH₁ G L z v)).map φ := by
        rw [← h.layerIn_range]
        exact w.2
      obtain ⟨a, ha, haw⟩ := hw'
      refine ⟨a, ha, ?_⟩
      rw [hML₀ a ha]
      have : (⟨_, h.map_mem_layerIn ha⟩ :
          ↥(layerIn (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range)) = w := Subtype.ext haw
      rw [this, hw]
  have hzz : z₁ * z₁ = 1 := Subtype.ext (by rw [hz₁]; exact h.zz)
  have hMzO : M z₁ ∈ orthogonalMinus 2 (ZMod 2) 1 1 := by
    refine hN _ (by rw [← map_mul M, hzz, map_one]) fun x hx => ?_
    rw [← hMΩ] at hx ⊢
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨z₁ * a * z₁⁻¹, h.conj_mem_L₀ z₁.2 ha, ?_⟩
    rw [map_mul M (z₁ * a) z₁⁻¹, map_mul M z₁ a, map_inv M z₁]
  have hMO : ∀ g, M g ∈ orthogonalMinus 2 (ZMod 2) 1 1 := by
    have hle : M.range ≤ orthogonalMinus 2 (ZMod 2) 1 1 := by
      obtain ⟨K, hO⟩ := h.orbitData
      rw [MonoidHom.range_eq_map, ← hO.sup_eq, Subgroup.map_sup]
      refine sup_le (hMΩ.le.trans ?_) ?_
      · refine Subgroup.commutator_le.2 fun g hg k hk => ?_
        exact (orthogonalMinus 2 (ZMod 2) 1 1).mul_mem
          ((orthogonalMinus 2 (ZMod 2) 1 1).mul_mem
            ((orthogonalMinus 2 (ZMod 2) 1 1).mul_mem hg hk)
            ((orthogonalMinus 2 (ZMod 2) 1 1).inv_mem hg))
          ((orthogonalMinus 2 (ZMod 2) 1 1).inv_mem hk)
      · rintro _ ⟨r, hr, rfl⟩
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (show (r : GLV V) ∈ Subgroup.zpowers z from hr)
        have hrk : r = z₁ ^ k := Subtype.ext (by rw [Subgroup.coe_zpow, hz₁]; exact hk.symm)
        rw [hrk, map_zpow]
        exact zpow_mem hMzO k
    exact fun g => hle ⟨g, rfl⟩
  have hz1 : z₁ ≠ 1 := by
    intro hz
    have : z = 1 := by rw [hz₁] at hz; exact congrArg Subtype.val hz
    have h2 := h.std.orderOf_s
    rw [this, orderOf_one] at h2
    exact absurd h2 (by decide)
  have hrefl : dimComm (M z₁) = 1 := by
    refine hG1 ((L.subgroupOf (bbH₁ G L z v)).map M)
      ((Subgroup.map_mono (Subgroup.comap_mono h.L_le_L₀)).trans hMΩ.le)
      ⟨(((L.subgroupOf (bbH₁ G L z v)).equivMapOfInjective M hMinj).symm.trans
        (((L.subgroupOf (bbH₁ G L z v)).equivMapOfInjective φ h.injective).trans eL))⟩
      (M z₁) hMzO (fun h1 => hz1 (hMinj (h1.trans (map_one M).symm))) ?_
    rintro _ ⟨l, hl, rfl⟩
    have hlz : z₁ * l = l * z₁ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hz₁]
      exact Subgroup.mem_centralizer_iff.1 (h.setup6.component.1 hl).2 z (Subgroup.mem_zpowers z)
    rw [← map_mul M, ← map_mul M, hlz]
  let ψ₀ : ↥(bbH₁ G L z v) →* ↥(orthogonalMinus 2 (ZMod 2) 1 1) := M.codRestrict _ hMO
  have hψ₀ : ∀ g, ((ψ₀ g : ↥(orthogonalMinus 2 (ZMod 2) 1 1)) :
      GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) = M g := fun _ => rfl
  have hψ₀inj : Function.Injective ψ₀ := fun g g' hgg' =>
    hMinj (by rw [← hψ₀, ← hψ₀, hgg'])
  have hψ₀surj : Function.Surjective ψ₀ := by
    rintro ⟨g, hg⟩
    rcases mem_omega_or_mul_mem hg (hMO z₁) hrefl with hΩg | hΩg
    · rw [← hMΩ] at hΩg
      obtain ⟨a, -, ha⟩ := hΩg
      exact ⟨a, Subtype.ext ha⟩
    · rw [← hMΩ] at hΩg
      obtain ⟨a, -, ha⟩ := hΩg
      refine ⟨a * z₁⁻¹, Subtype.ext ?_⟩
      rw [hψ₀, map_mul M, map_inv M, ha, mul_inv_cancel_right]
  let ψ : ↥(bbH₁ G L z v) ≃* ↥(orthogonalMinus 2 (ZMod 2) 1 1) :=
    MulEquiv.ofBijective ψ₀ ⟨hψ₀inj, hψ₀surj⟩
  have hψ : ∀ g, ((ψ g : ↥(orthogonalMinus 2 (ZMod 2) 1 1)) :
      GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) = M g := fun _ => rfl
  refine ⟨ψ, ?_⟩
  have hq : CFSG.Open.IsQuasisimple ↥(bbL₀ G L v) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv
      (((Subgroup.subgroupOfEquivOfLe h.L₀_le_H₁).symm.trans
        (((bbL₀ G L v).subgroupOf (bbH₁ G L z v)).equivMapOfInjective M hMinj)).trans
        (MulEquiv.subgroupCongr hMΩ))
      isQuasisimple_omegaMinusTwo_two
  refine
    { le := h.H₁_le_H₀
      z_mem := h.z_mem_H₁
      ψ_z := by
        show dimComm ((ψ ⟨z, h.z_mem_H₁⟩ : ↥(orthogonalMinus 2 (ZMod 2) 1 1)) :
          GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) = 1
        rw [hψ, ← hz₁]
        exact hrefl
      L_le := h.L_le_H₁
      L_iso := ⟨(Subgroup.subgroupOfEquivOfLe h.L_le_H₁).symm.trans
        (((L.subgroupOf (bbH₁ G L z v)).equivMapOfInjective φ h.injective).trans eL)⟩
      ψ_H := by
        have hc : ((omegaMinusTwo 2).subgroupOf (orthogonalMinus 2 (ZMod 2) 1 1)).comap
            ψ.toMonoidHom = (bbL₀ G L v).subgroupOf (bbH₁ G L z v) := by
          ext g
          rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
          show M g ∈ omegaMinusTwo 2 ↔ _
          rw [← hMΩ]
          exact Subgroup.mem_map_iff_mem hMinj
        rw [hc, Subgroup.map_subgroupOf_eq_of_le h.L₀_le_H₁]
      component := ⟨h.L₀_le_H₀, h.isSubnormal_L₀, hq⟩
      natural := ?_ }
  let mk : ↥(bbW₁ G L v) →+ Sect (bbW₀ G L v) (bbW₁ G L v) :=
    ((bbW₀ G L v).comap (bbW₁ G L v).subtype).mkQ.toAddMonoidHom
  let β : ↥(bbW₁ G L v) →+ (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2) :=
    ψW.toLinearMap.toAddMonoidHom.comp mk
  have hβ : ∀ w, β w = ψW (Submodule.Quotient.mk w) := fun _ => rfl
  refine ⟨β, fun x => ?_, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (ψW.symm x)
    exact ⟨w, by rw [hβ, hw, LinearEquiv.apply_symm_apply]⟩
  · ext w
    rw [AddMonoidHom.mem_ker, hβ, Submodule.mem_toAddSubgroup, Submodule.mem_comap,
      LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
    exact ⟨fun h0 => h0.1, fun h0 => ⟨h0, w.2⟩⟩
  · intro g w w' hww'
    have hmk : (Submodule.Quotient.mk w' : Sect (bbW₀ G L v) (bbW₁ G L v)) =
        φ g (Submodule.Quotient.mk w) := by
      rw [hφ, sectHom_mk]
      congr 1
      exact Subtype.ext hww'
    rw [hβ, hβ, hmk, hψ, hMx, LinearEquiv.symm_apply_apply]

end Hyp

end BranchB

end CFSG.CGT.Foote82
