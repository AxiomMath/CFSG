module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma45c
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitAssembly411

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

variable {X : Type} [Group X]

structure IsLemma45 (t : X) (L S : Subgroup X) (w z : X) (p f : ℕ) (β : X) : Prop where
  perfectResidual_M : (perfectResidual ↥(centralizer ({t} : Set X) ⊓ centralizer {β})).map
    (centralizer ({t} : Set X) ⊓ centralizer {β}).subtype = centralizerResidual L β
  oddCore_M : (pPrimeCore 2 ↥(centralizer ({t} : Set X) ⊓ centralizer {β})).map
      (centralizer ({t} : Set X) ⊓ centralizer {β}).subtype =
    (centralizer ({t} : Set X) ⊓ centralizer {β}) ⊓
      (pPrimeCore 2 ↥(centralizer ({t} : Set X))).map (centralizer ({t} : Set X)).subtype
  oddCore_K : (pPrimeCore 2 ↥(centralizerResidual L β)).map (centralizerResidual L β).subtype =
    centralizerResidual L β ⊓
      (pPrimeCore 2 ↥(centralizer ({t} : Set X))).map (centralizer ({t} : Set X)).subtype
  commutator_eq : ∀ y ∈ closure {t, β},
    ⁅centralizerResidual L β, zpowers (y * z)⁆ = centralizerResidual L β
  lieModel : Blueprint.LieModel (Bar (centralizerResidual L β)) .PSL 2 p (f / 2)
  isSylowOf_T : IsSylowOf 2 (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w)
    (centralizer ({t} : Set X) ⊓ centralizer {β})
  isSylowOf_D : IsSylowOf 2 (S ⊓ L) (L ⊓ centralizer {β})
  oddCore_CL : (pPrimeCore 2 ↥(L ⊓ centralizer {β})).map (L ⊓ centralizer {β}).subtype =
    (L ⊓ centralizer {β}) ⊓
      (pPrimeCore 2 ↥(centralizer ({t} : Set X))).map (centralizer ({t} : Set X)).subtype
  isSylowOf_Dstar : IsSylowOf 2 (S ⊓ L ⊓ centralizerResidual L β) (centralizerResidual L β)
  relIndex_Dstar : (S ⊓ L ⊓ centralizerResidual L β).relIndex (S ⊓ L) = 2
  z_mem : z ∈ S ⊓ L ⊓ centralizerResidual L β
  dihedral_Dstar : ∃ m : ℕ, 2 ≤ m ∧
    Nonempty (↥(S ⊓ L ⊓ centralizerResidual L β) ≃* DihedralGroup (2 ^ m))
  isSylowOf_tβ : IsSylowOf 2 (closure {t, β})
    (centralizer ({t} : Set X) ⊓ coreActionKernel (centralizerResidual L β))
  sylow_kernel : ∀ R : Subgroup X, IsSylowOf 2 R (coreActionKernel (centralizerResidual L β)) →
    closure {t, β} ≤ R → R = closure {t, β} ∨
      (∃ k : ℕ, 2 ≤ k ∧ Nonempty (↥R ≃* DihedralGroup (2 ^ k))) ∨
      ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥R ≃* CFSG.Open.SemidihedralGroup n)

variable [Finite X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing.Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem isLemma45 (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) :
    IsLemma45 t L S w z p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) where
  perfectResidual_M := h.perfectResidual_M _
  oddCore_M := hσ.oddCore_M hFC hKC i j
  oddCore_K := hσ.oddCore_K_H hFC hKC i j
  commutator_eq := fun _ hy => hσ.commutator_K_mul_z hFC hKC i j hy
  lieModel := hσ.lieModel_bar_K hFC hKC i j
  isSylowOf_T := hσ.isSylowOf_T_M hKC i j
  isSylowOf_D := hσ.isSylowOf_D_CL i j
  oddCore_CL := by
    rw [hσ.oddCore_CL hFC hKC i j, h.oddCore_L_eq, ← inf_assoc,
      inf_eq_left.mpr (inf_le_left : L ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} ≤ L)]
  isSylowOf_Dstar := hσ.isSylowOf_Dstar i j
  relIndex_Dstar := hσ.relIndex_Dstar hFC hKC i j
  z_mem := hσ.z_mem_Dstar hFC hKC i j
  dihedral_Dstar := hσ.dihedral_Dstar hFC hKC i j
  isSylowOf_tβ := hσ.isSylowOf_tβ hFC hKC i j
  sylow_kernel := fun _ hR hUR => hσ.dihedral_or_semidihedral hFC hKC i j hR hUR

end Standing.Setup42

@[expose] def SectionFourAfter45 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ) (h : Standing t L p f),
      (∀ (t' : X) (L' : Subgroup X) (p' f' : ℕ), Config t' L' p' f' →
        twoPart (centralizer ({t'} : Set X)) ≤ twoPart (centralizer ({t} : Set X))) →
      ∀ (S : Subgroup X) (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) (w z : X),
        Standing.Setup42 h hS w z →
      ∀ V : Subgroup X,
        IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)) →
        S ≤ V →
      ∀ β : X, IsBeta411 t L S w z V β →
        (∀ β' : X, IsBeta411 t L S w z V β' →
          twoPart (centralizer ({β'} : Set X)) ≤ twoPart (centralizer ({β} : Set X))) →
        (IsBeta411 t L S w z V (w ^ (orderOf w / 2)) ∧
          twoPart (centralizer ({β} : Set X)) ≤
            twoPart (centralizer ({w ^ (orderOf w / 2)} : Set X)) →
          β = w ^ (orderOf w / 2)) →
        IsLemma45 t L S w z p f β → False

theorem sectionFourAfter411_of_after45 (hFC : AutPSL2FieldCentralizerInput)
    (hKC : AutPSL2CentralizerInput) (h45 : SectionFourAfter45) : SectionFourAfter411 := by
  intro X _ _ _ hnonab hK hcat t L p f h hmax S hS w z hσ V hV hSV β hβ hβmax hu
  obtain ⟨i, j, rfl⟩ := hσ.mem_X_not_tD hβ.mem_X hβ.not_mem
  exact h45 X hnonab hK hcat t L p f h hmax S hS w z hσ V hV hSV _ hβ hβmax hu
    (hσ.isLemma45 hFC hKC i j)

theorem harrislit_of_inputs_45 (hCU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hGH : UFrontier.GH74ModelsInput) (hHSF : GSLit.HarrisSolomonFritzInput)
    (hHS : HarrisSolomonDihedralInput) (hKG : AutPSL2SylowInput)
    (hKC : AutPSL2CentralizerInput) (hKF : AutPSL2FusionInput)
    (hFC : AutPSL2FieldCentralizerInput) (h45 : SectionFourAfter45) : GSLit.HarrisInput :=
  harrislit_of_inputs_411 hCU hGH hHSF hHS hKG hKC hKF
    (sectionFourAfter411_of_after45 hFC hKC h45)

end CFSG.ComponentClassification.HarrisLit
