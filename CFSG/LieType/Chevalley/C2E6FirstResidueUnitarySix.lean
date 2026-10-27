module

public import CFSG.LieType.Chevalley.C2E6FirstResidueGeometry
public import CFSG.LieType.Chevalley.C2E6A5ExteriorCubeModel

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap Matrix
  CFSG.LieType.Chevalley.ExteriorCube CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Chevalley.CosetBuilding

theorem standard_first_residue_unitary_six_flags :
    (∀ v w : Fin 6 → K, herm6 v w = ∑ i, v i * bar (w (Fin.rev i))) ∧
    (∀ h : SpecialLinearGroup (Fin 6) K, h ∈ SU6 ↔ ∀ v w : Fin 6 → K,
      herm6 ((h : Matrix (Fin 6) (Fin 6) K) *ᵥ v) ((h : Matrix (Fin 6) (Fin 6) K) *ᵥ w) =
        herm6 v w) ∧
    (∀ z : SpecialLinearGroup (Fin 6) K, z ∈ LinearFlag.scalars 6 K ↔
      ∃ l : Kˣ, (z : Matrix (Fin 6) (Fin 6) K) = scalar (Fin 6) (l : K)) ∧
    stdLevi firstJ = groupA ⊓ stdFixedGroup ∧
    (∀ (l : stdLevi firstJ) (h : SU6),
      psiA ⟨(l : ModGL Tag.E6 K), stdLevi_firstJ_le_groupA l.2⟩ =
        cubeHom (h : SpecialLinearGroup (Fin 6) K) →
      leviSUEquiv l = (h : SU6 ⧸ (LinearFlag.scalars 6 K).subgroupOf SU6)) ∧
    (∀ k : Fin 3, baseFlag.sub k = Submodule.span K (uVec '' {j | (j : ℕ) ≤ k})) ∧
    (∀ (l : stdLevi firstJ) (h : SU6),
      psiA ⟨(l : ModGL Tag.E6 K), stdLevi_firstJ_le_groupA l.2⟩ =
        cubeHom (h : SpecialLinearGroup (Fin 6) K) →
      ((l : ModGL Tag.E6 K) ∈ stdLeviBorel firstJ ↔ h • baseFlag = baseFlag)) ∧
    residueFlag (QuotientGroup.mk 1) = baseFlag ∧
    (∀ (p : nativeParabolic firstJ) (h : SU6),
      psiA ⟨((leviProj two_mem_firstJ p : stdLevi firstJ) : ModGL Tag.E6 K),
        stdLevi_firstJ_le_groupA (leviProj two_mem_firstJ p).2⟩ =
          cubeHom (h : SpecialLinearGroup (Fin 6) K) →
      ∀ x : ParabolicCosets firstJ, residueFlag (p • x) = h • residueFlag x) ∧
    (typeDim 1 = 2 ∧ typeDim 2 = 1 ∧ typeDim 3 = 0) ∧
    (∀ i ∈ firstJ, ∀ x y : nativeParabolic firstJ,
      ((x⁻¹ * y : nativeParabolic firstJ) : ModGL Tag.E6 K) ∈ nativeParabolic {i} ↔
        ∀ k, k ≠ typeDim i → (residueFlag (QuotientGroup.mk x)).sub k =
          (residueFlag (QuotientGroup.mk y)).sub k) ∧
    (∀ p : nativeParabolic firstJ,
      (∀ x : ParabolicCosets firstJ, p • x = x) ↔ (p : ModGL Tag.E6 K) ∈ stdRadical firstJ) ∧
    (∀ v w : Fin 6 → K, nativeHerm (nativeCoord v) (nativeCoord w) = herm6 v w) ∧
    (∀ k : Fin 3, (baseFlag.sub k).map (nativeCoord : (Fin 6 → K) →ₗ[K] (Fin 6 → K)) =
      Submodule.span K (uVec '' (nativeBaseIdx k : Set (Fin 6)))) ∧
    (∀ k : Fin 3, oppFlag.sub k = Submodule.span K (uVec '' {j | 5 - (k : ℕ) ≤ (j : ℕ)})) ∧
    residueFlag (QuotientGroup.mk ⟨_, canonicalRep_longest_mem⟩) = oppFlag ∧
    (∀ k : Fin 3, (oppFlag.sub k).map (nativeCoord : (Fin 6 → K) →ₗ[K] (Fin 6 → K)) =
      Submodule.span K (uVec '' (nativeOppIdx k : Set (Fin 6)))) ∧
    (∀ p : nativeParabolic firstJ,
      residueFlag (QuotientGroup.mk ⟨betaGL p, betaGL_mem_nativeParabolic p.2⟩) =
        frobFlag (residueFlag (QuotientGroup.mk p))) ∧
    (∀ (v : Fin 6 → K) (i : Fin 6), frob6 v i = bar (v i)) ∧
    (∀ v : Fin 6 → K, nativeCoord (frob6 v) = frob6 (nativeCoord v)) ∧
    Function.Injective parabolicToChamber ∧
    Set.range parabolicToChamber =
      residue nativeCoxeterSystem stdDistance firstJ ((1 : stdGroup) : stdChamber) ∧
    Nat.card (ParabolicCosets firstJ) = 93555 ∧
    Nat.card (stdLeviBorel firstJ) = 3 * 2 ^ 15 ∧
    Nat.card (stdLevi firstJ) = 9196830720 :=
  ⟨fun _ _ => rfl, mem_SU6_iff_herm6, mem_scalars_iff, stdLevi_firstJ,
    fun _ _ e => leviSUEquiv_apply e, baseFlag_sub_eq_span,
    fun l h e => by rw [← liftSU_eq_iff.mpr e]; exact liftSU_mem_stdLeviBorel_iff h,
    residueFlag_one, fun p _ hp x => residueFlag_smul p hp x, ⟨rfl, rfl, rfl⟩,
    fun _ hi x y => mem_nativeParabolic_singleton_iff hi x y, smul_eq_self_iff,
    nativeHerm_nativeCoord, nativeCoord_baseFlag, oppFlag_sub, residueFlag_longest,
    nativeCoord_oppFlag, residueFlag_betaGL, fun _ _ => rfl, nativeCoord_frob6,
    parabolicToChamber_injective, range_parabolicToChamber, card_parabolicCosets_firstJ,
    card_stdLeviBorel_firstJ, card_stdLevi_firstJ⟩

end CFSG.LieType.Chevalley.C2E6Std
