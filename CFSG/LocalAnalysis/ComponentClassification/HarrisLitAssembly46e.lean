module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitAssembly46
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma45f
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46e
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma45e

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

variable {X : Type} [Group X] [Finite X]

structure Setting46e (t : X) (L : Subgroup X) (p f : ℕ) (S : Subgroup X) (w z : X)
    (V : Subgroup X) (i j : ℕ) : Prop extends Setting46 t L p f S w z V i j where
  lemma45c_beta : ∀ d ∈ S ⊓ L, d ^ 2 = 1 →
    ((∃ l ∈ L, l * (d * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * l⁻¹ =
        w ^ (orderOf w / 2) * t ^ i * z ^ j) ↔
      (d = 1 ∨ d ∉ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
  lemma45c_Dstar : ∀ d ∈ S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j),
    ∀ d' ∈ S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j),
      d ≠ 1 → d ^ 2 = 1 → d' ≠ 1 → d' ^ 2 = 1 →
        ∃ k ∈ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j),
          k * (d * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * k⁻¹ =
            d' * (w ^ (orderOf w / 2) * t ^ i * z ^ j)
  lemma45e : (solvableRadical ↥(centralizer ({t} : Set X) ⊓
        centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})).map
      (centralizer ({t} : Set X) ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}).subtype =
    ((centralizer ({t} : Set X) ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) ⊓
      (pPrimeCore 2 ↥(centralizer ({t} : Set X))).map (centralizer ({t} : Set X)).subtype) ⊔
      closure {t, w ^ (orderOf w / 2) * t ^ i * z ^ j}
  lemma46e : ∀ g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j),
    ⁅Standing.Setup42.KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j),
      (Standing.Setup42.KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)).map
        (MulAut.conj g).toMonoidHom⁆ ≠ ⊥

@[expose] def Harris413Input46e : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ) (S : Subgroup X) (w z : X) (V : Subgroup X) (i j : ℕ),
      Setting46e t L p f S w z V i j →
        ¬ IsSimpleGroup ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))

@[expose] def Harris414Input46e : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ) (S : Subgroup X) (w z : X) (V : Subgroup X) (i j : ℕ),
      Setting46e t L p f S w z V i j →
        ¬ IsSimpleGroup ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →
        ¬ IsQuasisimple ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))

@[expose] def Harris415Input46e : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ) (S : Subgroup X) (w z : X) (V : Subgroup X) (i j : ℕ),
      Setting46e t L p f S w z V i j →
        IsQuasisimple ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))

theorem Setting46.setting46e {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X} {w z : X}
    {V : Subgroup X} {i j : ℕ} (hs : Setting46 t L p f S w z V i j)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hFL : ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → Even f → 16 ∣ p ^ f - 1 →
        Blueprint.LieModel Y .PSL 2 p f → ∀ k : MulAut Y, IsFieldAutPSL2 k → ∀ y ∈ fixedPoints k, y
        ^ 2 = 1 → ((∃ g : Y, MulAut.conj g * k * (MulAut.conj g)⁻¹ = MulAut.conj y * k) ↔ (y = 1 ∨ y
        ∉ (perfectResidual ↥(fixedPoints k)).map (fixedPoints
        k).subtype))) : Setting46e t L p f S w z V i j where
  toSetting46 := hs
  lemma45c_beta := fun _ hd hd2 => hs.setup.conj_beta_iff hKC hFL i j hd hd2
  lemma45c_Dstar := fun _ hd _ hd' hd1 hd2 hd'1 hd'2 =>
    hs.setup.conj_of_mem_Dstar hFC hKC i j hd hd' hd1 hd2 hd'1 hd'2
  lemma45e := hs.setup.solvableRadical_M hFC hKC i j
  lemma46e := hs.setup.commutator_KBar_conj_ne_bot hFC hKC i j

theorem sectionFourAfter411_of_46e (hFC : AutPSL2FieldCentralizerInput)
    (hKC : AutPSL2CentralizerInput) (hKF : AutPSL2FusionInput) (hI : AutPSL2InvolutionInput)
    (hFL : ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → Even f → 16 ∣ p ^ f - 1 →
        Blueprint.LieModel Y .PSL 2 p f → ∀ k : MulAut Y, IsFieldAutPSL2 k → ∀ y ∈ fixedPoints k, y
        ^ 2 = 1 → ((∃ g : Y, MulAut.conj g * k * (MulAut.conj g)⁻¹ = MulAut.conj y * k) ↔ (y = 1 ∨ y
        ∉ (perfectResidual ↥(fixedPoints k)).map (fixedPoints k).subtype)))
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (h413 : Harris413Input46e) (h414 : Harris414Input46e) (h415 : Harris415Input46e) :
    SectionFourAfter411 := by
  intro X _ _ _ hnonab hK hcat t L p f h hmax S hS w z hσ V hV hSV β hβ hβmax hu
  obtain ⟨i, j, rfl⟩ := hσ.mem_X_not_tD hβ.mem_X hβ.not_mem
  have hset := (setting46_of hnonab hK hFC hKC hKF hI hSch h hmax hS hσ hV hSV hβ hβmax
    hu).setting46e hFC hKC hFL
  exact h414 X hnonab hK hcat t L p f S w z V i j hset
    (h413 X hnonab hK hcat t L p f S w z V i j hset)
    (h415 X hnonab hK hcat t L p f S w z V i j hset)

theorem harrislit_of_inputs_46e (hCU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hGH : UFrontier.GH74ModelsInput) (hHSF : GSLit.HarrisSolomonFritzInput)
    (hHS : HarrisSolomonDihedralInput) (hKG : AutPSL2SylowInput)
    (hKC : AutPSL2CentralizerInput) (hKF : AutPSL2FusionInput)
    (hFC : AutPSL2FieldCentralizerInput) (hI : AutPSL2InvolutionInput)
    (hFL : ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → Even f → 16 ∣ p ^ f - 1 →
        Blueprint.LieModel Y .PSL 2 p f → ∀ k : MulAut Y, IsFieldAutPSL2 k → ∀ y ∈ fixedPoints k, y
        ^ 2 = 1 → ((∃ g : Y, MulAut.conj g * k * (MulAut.conj g)⁻¹ = MulAut.conj y * k) ↔ (y = 1 ∨ y
        ∉ (perfectResidual ↥(fixedPoints k)).map (fixedPoints k).subtype)))
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (h413 : Harris413Input46e) (h414 : Harris414Input46e) (h415 : Harris415Input46e) :
    GSLit.HarrisInput :=
  harrislit_of_inputs_411 hCU hGH hHSF hHS hKG hKC hKF
    (sectionFourAfter411_of_46e hFC hKC hKF hI hFL hSch h413 h414 h415)

end CFSG.ComponentClassification.HarrisLit
