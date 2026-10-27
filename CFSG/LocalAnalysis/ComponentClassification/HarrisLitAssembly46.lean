module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitAssembly45
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma44e
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46f

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

variable {X : Type} [Group X] [Finite X]

structure Setting46 (t : X) (L : Subgroup X) (p f : ℕ) (S : Subgroup X) (w z : X)
    (V : Subgroup X) (i j : ℕ) : Prop where
  standing : Standing t L p f
  max_config : ∀ (t' : X) (L' : Subgroup X) (p' f' : ℕ), Config t' L' p' f' →
    twoPart (centralizer ({t'} : Set X)) ≤ twoPart (centralizer ({t} : Set X))
  sylow : IsSylowOf 2 S (centralizer ({t} : Set X))
  setup : Standing.Setup42 standing sylow w z
  sylow_V : IsSylowOf 2 V
    (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X))
  le_V : S ≤ V
  beta : IsBeta411 t L S w z V (w ^ (orderOf w / 2) * t ^ i * z ^ j)
  max_beta : ∀ β' : X, IsBeta411 t L S w z V β' →
    twoPart (centralizer ({β'} : Set X)) ≤
      twoPart (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
  pref_u : IsBeta411 t L S w z V (w ^ (orderOf w / 2)) ∧
      twoPart (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) ≤
        twoPart (centralizer ({w ^ (orderOf w / 2)} : Set X)) →
    w ^ (orderOf w / 2) * t ^ i * z ^ j = w ^ (orderOf w / 2)
  lemma45 : IsLemma45 t L S w z p f (w ^ (orderOf w / 2) * t ^ i * z ^ j)
  pLayer_M : (pLayer ↥(centralizer ({t} : Set X) ⊓
      centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) 2).map
      (centralizer ({t} : Set X) ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}).subtype =
    centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)
  lemma44a_z : IsPGroup 2 (↥(centralizer ({t} : Set X) ⊓ centralizer {z}) ⧸
      pPrimeCore 2 ↥(centralizer ({t} : Set X) ⊓ centralizer {z})) ∧
    IsSylowOf 2 S (centralizer ({t} : Set X) ⊓ centralizer {z})
  lemma44a_X : IsPGroup 2 (↥(centralizer ((closure {t, w ^ (orderOf w / 2), z} :
      Subgroup X) : Set X)) ⧸ pPrimeCore 2 ↥(centralizer ((closure
        {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X))) ∧
    IsSylowOf 2 (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w)
      (centralizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X))
  lemma44a_T : IsPGroup 2 (↥(centralizer ({t} : Set X) ⊓
      normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)) ⧸
    pPrimeCore 2 ↥(centralizer ({t} : Set X) ⊓
      normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X))) ∧
    IsSylowOf 2 S (centralizer ({t} : Set X) ⊓
      normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X))
  lemma44b : ∀ τ ∈ S, τ ^ 2 = 1 → τ ≠ 1 → τ ≠ t →
    ¬ IsPGroup 2 (↥(centralizer ({t} : Set X) ⊓ centralizer {τ}) ⧸
      pPrimeCore 2 ↥(centralizer ({t} : Set X) ⊓ centralizer {τ})) →
    ∃ g ∈ centralizer ({t} : Set X), ∃ i' j' : ℕ,
      g * τ * g⁻¹ = w ^ (orderOf w / 2) * t ^ i' * z ^ j' ∧
      twoPart (centralizer ({t} : Set X) ⊓ centralizer {τ}) =
        Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X)
  lemma44e : ∀ τ ∈ S, τ ∉ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w → τ ^ 2 = 1 →
    Nonempty (↥(L ⊓ centralizer {τ}) ⧸ (barMap L (inf_le_left : L ⊓ centralizer {τ} ≤ L)).ker ≃*
      DihedralGroup ((p ^ f + 1) / 2)) ∧
    IsSylowOf 2 (zpowers z) (L ⊓ centralizer {τ}) ∧
    IsPGroup 2 (↥(centralizer ({t} : Set X) ⊓ centralizer {τ}) ⧸
      pPrimeCore 2 ↥(centralizer ({t} : Set X) ⊓ centralizer {τ}))
  lemma46a : GSThmB.layerIn (centralizer ({setup.tBar i j} :
        Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) =
      Standing.Setup42.KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∧
    GSThmB.layerIn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
        centralizer ({setup.tBar i j} : Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) =
      Standing.Setup42.KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)
  lemma46b : (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∈
        centralizer (Standing.Setup42.KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) :
          Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ∧
      betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∈
        center (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ∧
    ∀ R : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), IsSylowOf 2 R
        (centralizer (Standing.Setup42.KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) :
          Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) →
      Nat.card R = 4 ∨ (∃ k : ℕ, 2 ≤ k ∧ Nonempty (↥R ≃* DihedralGroup (2 ^ k))) ∨
        ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥R ≃* CFSG.Open.SemidihedralGroup n)
  lemma46f : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔ zpowers (setup.tBar i j) ≤
        centralizer (Standing.Setup42.KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) :
          Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ∧
      (Nat.card ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
          zpowers (setup.tBar i j)) = 4 ∨
        (∃ k : ℕ, 2 ≤ k ∧ Nonempty (↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
          zpowers (setup.tBar i j)) ≃* DihedralGroup (2 ^ k))) ∨
        ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
          zpowers (setup.tBar i j)) ≃* CFSG.Open.SemidihedralGroup n)) ∧
      betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∈
        pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {setup.tBar i j} ∧
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {setup.tBar i j} ≤
        closure {setup.tBar i j, betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)}

@[expose] def Harris413Input46 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ) (S : Subgroup X) (w z : X) (V : Subgroup X) (i j : ℕ),
      Setting46 t L p f S w z V i j →
        ¬ IsSimpleGroup ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))

@[expose] def Harris414Input46 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ) (S : Subgroup X) (w z : X) (V : Subgroup X) (i j : ℕ),
      Setting46 t L p f S w z V i j →
        ¬ IsSimpleGroup ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →
        ¬ IsQuasisimple ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))

@[expose] def Harris415Input46 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ Blueprint.Catalog X →
    ∀ (t : X) (L : Subgroup X) (p f : ℕ) (S : Subgroup X) (w z : X) (V : Subgroup X) (i j : ℕ),
      Setting46 t L p f S w z V i j →
        IsQuasisimple ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))

omit [Finite X] in
theorem setting46_of [IsSimpleGroup X] [Finite X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hKF : AutPSL2FusionInput) (hI : AutPSL2InvolutionInput)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    {t : X} {L : Subgroup X} {p f : ℕ} (h : Standing t L p f)
    (hmax : ∀ (t' : X) (L' : Subgroup X) (p' f' : ℕ), Config t' L' p' f' →
      twoPart (centralizer ({t'} : Set X)) ≤ twoPart (centralizer ({t} : Set X)))
    {S : Subgroup X} (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) {w z : X}
    (hσ : Standing.Setup42 h hS w z) {V : Subgroup X}
    (hV : IsSylowOf 2 V
      (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) {i j : ℕ}
    (hβ : IsBeta411 t L S w z V (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    (hβmax : ∀ β' : X, IsBeta411 t L S w z V β' →
      twoPart (centralizer ({β'} : Set X)) ≤
        twoPart (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hu : IsBeta411 t L S w z V (w ^ (orderOf w / 2)) ∧
      twoPart (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) ≤
        twoPart (centralizer ({w ^ (orderOf w / 2)} : Set X)) →
      w ^ (orderOf w / 2) * t ^ i * z ^ j = w ^ (orderOf w / 2)) :
    Setting46 t L p f S w z V i j where
  standing := h
  max_config := hmax
  sylow := hS
  setup := hσ
  sylow_V := hV
  le_V := hSV
  beta := hβ
  max_beta := hβmax
  pref_u := hu
  lemma45 := hσ.isLemma45 hFC hKC i j
  pLayer_M := hσ.pLayer_M hFC hKC i j
  lemma44a_z := hσ.isPGroup_quot_centralizer_z hI
  lemma44a_X := hσ.isPGroup_quot_centralizer_X hI hKC
  lemma44a_T := hσ.isPGroup_quot_normalizer_T hI
  lemma44b := fun _ hτS hτ2 hτ1 hτt hτ => hσ.lemma44b hI hKF hKC hτS hτ2 hτ1 hτt hτ
  lemma44e := fun _ hτS hτT hτ2 => ⟨hσ.dihedral_CL_of_not_mem_T hI hτS hτT hτ2,
    hσ.isSylowOf_z_CL_of_not_mem_T hI hτS hτT hτ2, hσ.isPGroup_quot_of_not_mem_T hI hτS hτT hτ2⟩
  lemma46a := ⟨hσ.layerIn_centralizer_tBar hFC hKC i j,
    hσ.layerIn_layer_centralizer_tBar hnonab hK hSch hFC hKC i j⟩
  lemma46b := hσ.lemma46b hFC hKC i j
  lemma46f := hσ.lemma46f hnonab hK hSch hFC hKC i j

theorem sectionFourAfter411_of_46 (hFC : AutPSL2FieldCentralizerInput)
    (hKC : AutPSL2CentralizerInput) (hKF : AutPSL2FusionInput) (hI : AutPSL2InvolutionInput)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (h413 : Harris413Input46) (h414 : Harris414Input46) (h415 : Harris415Input46) :
    SectionFourAfter411 := by
  intro X _ _ _ hnonab hK hcat t L p f h hmax S hS w z hσ V hV hSV β hβ hβmax hu
  obtain ⟨i, j, rfl⟩ := hσ.mem_X_not_tD hβ.mem_X hβ.not_mem
  have hset := setting46_of hnonab hK hFC hKC hKF hI hSch h hmax hS hσ hV hSV hβ hβmax hu
  exact h414 X hnonab hK hcat t L p f S w z V i j hset
    (h413 X hnonab hK hcat t L p f S w z V i j hset)
    (h415 X hnonab hK hcat t L p f S w z V i j hset)

theorem harrislit_of_inputs_46 (hCU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hGH : UFrontier.GH74ModelsInput) (hHSF : GSLit.HarrisSolomonFritzInput)
    (hHS : HarrisSolomonDihedralInput) (hKG : AutPSL2SylowInput)
    (hKC : AutPSL2CentralizerInput) (hKF : AutPSL2FusionInput)
    (hFC : AutPSL2FieldCentralizerInput) (hI : AutPSL2InvolutionInput)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (h413 : Harris413Input46) (h414 : Harris414Input46) (h415 : Harris415Input46) :
    GSLit.HarrisInput :=
  harrislit_of_inputs_411 hCU hGH hHSF hHS hKG hKC hKF
    (sectionFourAfter411_of_46 hFC hKC hKF hI hSch h413 h414 h415)

end CFSG.ComponentClassification.HarrisLit
