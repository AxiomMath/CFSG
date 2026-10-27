module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf10U1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

namespace TwinDisc

@[expose] def DiscZT (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    Setting n R S t₀ K K' z u J t W →
      ¬ SecConnU (CoreAssembly.conjClass (tightCore R)) u →
        (∀ y ∈ coreLayer (CoreAssembly.conjClass (tightCore R)) u,
            z * y * z⁻¹ * y⁻¹ ∈ oddCoreOf (coreLayer (CoreAssembly.conjClass (tightCore R)) u)) ∨
          (∀ y ∈ coreLayer (CoreAssembly.conjClass (tightCore R)) u,
            (t * z) * y * (t * z)⁻¹ * y⁻¹ ∈
              oddCoreOf (coreLayer (CoreAssembly.conjClass (tightCore R)) u))

section Y

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem rLayer_le_coreLayer (hΩ : HypOmegaGen Ω)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) : rLayer Ω c ≤ coreLayer Ω c := by
  unfold rLayer
  refine iSup₂_le fun R hR => iSup_le fun hRc => ?_
  obtain ⟨J, hJΩ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  have hJtq : J ∈ tqMembers3 Ω c :=
    ⟨hJΩ, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJΩ ⟨R, hRJ, hRc⟩⟩
  exact ((TwinADescent.isSylow2In_coreAt_iff hc2 hJtq.2).mpr ⟨hRJ, hRc⟩).1.trans
    (coreAt_le_coreLayer hJtq)

theorem coreLayer_le_sigmaGen_of_le_centralizer_z (hΩ : HypOmegaGen Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {K : Subgroup G} {z : G} (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (hY : coreLayer Ω c ≤ Subgroup.centralizer ({z} : Set G)) :
    coreLayer Ω c ≤ sigmaGen Ω K := by
  refine coreLayer_le_of_forall fun J hJ => ?_
  obtain ⟨R, hR, hRc⟩ := TwinADescent.exists_sylow_centralizer_of_tq hc2 hJ.2
  have hRK : R ≤ TwinADescent.coreAt c J :=
    ((TwinADescent.isSylow2In_coreAt_iff hc2 hJ.2).mpr ⟨hR, hRc⟩).1
  have hRz : R ≤ Subgroup.centralizer ({z} : Set G) := hRK.trans ((coreAt_le_coreLayer hJ).trans hY)
  have hJd : J ∈ dComp Ω K := by
    by_cases hJK : J = K
    · rw [hJK]
      exact Relation.ReflTransGen.refl
    · have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hJ.1 hR
      have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hRset
      have hRN : R ≤ Subgroup.normalizer (K : Set G) :=
        Sec6Gen.le_normalizer_of_le_centralizer hΩ hK hJ.1 (Ne.symm hJK) hz hR.1 hR.2.1
          (by omega) hRz
      exact T7A.mem_dComp_of_mem_omegaNbr ⟨hJ.1, hJK, R, hRset, hR.1, hRN⟩
  exact (TwinADescent.coreAt_le_left c J).trans (le_iSup₂_of_le J hJd le_rfl)

end Y

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
