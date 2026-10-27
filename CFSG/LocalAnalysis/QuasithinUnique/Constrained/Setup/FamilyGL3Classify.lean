module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Flags
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Chain

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace Matrix

noncomputable local instance fintypeDualVec3 : Fintype (Module.Dual (ZMod 2) Vec3) :=
  @Fintype.ofFinite _ finite_dual_vec3

theorem irreducible_binary_GL3_classification {E : Type*} [AddCommMonoid E] [Module (ZMod 2) E]
    [Finite E] (ρ : GL32 →* (E ≃ₗ[ZMod 2] E)) (hρ : IsIrrRep ρ) :
    ModIso repTriv ρ ∨ ModIso repV ρ ∨ ModIso repDual ρ ∨ ModIso repA ρ := by
  classical
  have hV : Module.finrank (ZMod 2) Vec3 = 3 := by simp
  have hV' : Module.finrank (ZMod 2) (Module.Dual (ZMod 2) Vec3) = 3 := finrank_dual hV
  obtain ⟨π, hπ, hπ0⟩ := exists_flagMap ρ hρ
  have hK : IsIrrAct (fun (_ : GL32) (x : ZMod 2) => x) := isIrr_repTriv
  have key := classify_skeleton (G := GL32) (E := E) (F := Flags Vec3 → ZMod 2)
    (K := ZMod 2) (U := augmentation Vec3) (W := augmentation (Module.Dual (ZMod 2) Vec3))
    (A := traceZeroEnd Vec3) (Y := Module.Dual (ZMod 2) Vec3) (X := Vec3)
    (Y' := Module.Dual (ZMod 2) (Module.Dual (ZMod 2) Vec3)) (X' := Module.Dual (ZMod 2) Vec3)
    (actE := fun g x => ρ g x) (actF := fun g z => flagPermAct (repV g) z)
    (actK := fun _ x => x) (actU := fun g x => permActU (repV g) x)
    (actW := fun g x => permActU ((repV g).symm.dualMap) x) (actA := actA)
    (actY := fun g f => dualAct (repV g) f) (actX := fun g v => repV g v)
    (actY' := fun g φ => dualAct ((repV g).symm.dualMap) φ)
    (actX' := fun g f => (repV g).symm.dualMap f)
    (fun g => rfl) (fun g => rfl) hρ isIrrAct_actA hK
    isIrrAct_dualAct isIrr_repV isIrrAct_bidual isIrrAct_dualAct π hπ hπ0 (flagIota Vec3)
    (fun g t => flagIota_equivariant (repV g) t) (flagPsi Vec3) (flagPsi_surjective hV)
    (fun g z => Subtype.ext ((flagPsi_equivariant (repV g) z).trans (actA_coe g _).symm))
    (ker_flagPsi_eq hV).le (kappa hV) (fun g f => Subtype.ext (kappa_equivariant hV (repV g) f))
    (theta Vec3) (theta_surjective hV) (fun g x => theta_equivariant (repV g) x)
    (ker_theta_eq hV).le (kappa hV') (fun g f => Subtype.ext (kappa_equivariant hV' _ f))
    (theta (Module.Dual (ZMod 2) Vec3)) (theta_surjective hV')
    (fun g x => theta_equivariant _ x) (ker_theta_eq hV').le
  rcases key with h | h | h | h | h | h
  · exact Or.inr (Or.inr (Or.inr (actIso_actA_repA.symm.trans h)))
  · exact Or.inl (ActIso.trans ⟨LinearEquiv.refl (ZMod 2) (ZMod 2), fun g x => rfl⟩ h)
  · exact Or.inr (Or.inr (Or.inl (actIso_dualAct_repDual.symm.trans h)))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inl (actIso_repV_bidual.trans h))
  · exact Or.inr (Or.inr (Or.inl (actIso_dualAct_repDual.symm.trans h)))

theorem no_dual_iso : ∀ a b c d e f g h i : ZMod 2,
    Matrix.det !![a, b, c; d, e, f; g, h, i] = 1 →
    !![a, b, c; d, e, f; g, h, i] * unitri 0 1 0 =
      (unitri 0 (0 * 0 + 1) 0)ᵀ * !![a, b, c; d, e, f; g, h, i] →
    !![a, b, c; d, e, f; g, h, i] * unitri 0 0 1 =
      (unitri 0 (0 * 1 + 0) 1)ᵀ * !![a, b, c; d, e, f; g, h, i] → False := by
  decide

theorem toMatrix'_repDual (g : GL32) :
    LinearMap.toMatrix' (repDual g : Vec3 →ₗ[ZMod 2] Vec3) = ((g⁻¹ : GL32) : Mat3)ᵀ :=
  toMatrix'_repV (tauHom g)

theorem not_modIso_repV_repDual : ¬ ModIso repV repDual := by
  rintro ⟨φ, hφ⟩
  let M : Mat3 := LinearMap.toMatrix' (φ : Vec3 →ₗ[ZMod 2] Vec3)
  have hM : ∀ g : GL32, M * (g : Mat3) = ((g⁻¹ : GL32) : Mat3)ᵀ * M := by
    intro g
    have h1 : (φ : Vec3 →ₗ[ZMod 2] Vec3) ∘ₗ (repV g : Vec3 →ₗ[ZMod 2] Vec3) =
        (repDual g : Vec3 →ₗ[ZMod 2] Vec3) ∘ₗ (φ : Vec3 →ₗ[ZMod 2] Vec3) :=
      LinearMap.ext fun x => hφ g x
    have h2 := congrArg LinearMap.toMatrix' h1
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, toMatrix'_repV,
      toMatrix'_repDual] at h2
    exact h2
  have hdet : M.det = 1 := by
    have h1 : M * LinearMap.toMatrix' (φ.symm : Vec3 →ₗ[ZMod 2] Vec3) = 1 := by
      rw [← LinearMap.toMatrix'_comp]
      have : (φ : Vec3 →ₗ[ZMod 2] Vec3) ∘ₗ (φ.symm : Vec3 →ₗ[ZMod 2] Vec3) = LinearMap.id :=
        LinearMap.ext fun x => φ.apply_symm_apply x
      rw [this, LinearMap.toMatrix'_id]
    have h2 : M.det * (LinearMap.toMatrix' (φ.symm : Vec3 →ₗ[ZMod 2] Vec3)).det = 1 := by
      rw [← Matrix.det_mul, h1, Matrix.det_one]
    exact eq_one_of_isUnit_zmod_two (isUnit_iff_exists_inv.2 ⟨_, h2⟩)
  have e := Matrix.eta_fin_three M
  have k1' : M * unitri 0 1 0 = (unitri 0 (0 * 0 + 1) 0)ᵀ * M := hM (unitriGL 0 1 0)
  have k2' : M * unitri 0 0 1 = (unitri 0 (0 * 1 + 0) 1)ᵀ * M := hM (unitriGL 0 0 1)
  rw [e] at hdet k1' k2'
  exact no_dual_iso _ _ _ _ _ _ _ _ _ hdet k1' k2'

theorem card_eq_of_modIso {E E' : Type*} [AddCommMonoid E] [Module (ZMod 2) E]
    [AddCommMonoid E'] [Module (ZMod 2) E'] {ρ : GL32 →* (E ≃ₗ[ZMod 2] E)}
    {ρ' : GL32 →* (E' ≃ₗ[ZMod 2] E')} (h : ModIso ρ ρ') : Nat.card E = Nat.card E' := by
  obtain ⟨f, -⟩ := h
  exact Nat.card_congr f.toEquiv

theorem natCard_Vec3 : Nat.card Vec3 = 8 := by
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

theorem natCard_traceZero : Nat.card traceZero = 256 :=
  (Nat.card_congr matEnd.toEquiv).symm.trans (natCard_traceZeroEnd (by simp))

end CFSG.QuasithinUnique.Setup.Family
