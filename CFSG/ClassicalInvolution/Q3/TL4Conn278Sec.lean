module

public import CFSG.ClassicalInvolution.Q3.TL4Conn278Pair
public import CFSG.ClassicalInvolution.Asc77.AscIHSectF

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Def

variable (Ω : Set (Subgroup G)) (x : G)

abbrev SecQuot : Type := ↥(layerY Ω x) ⧸ classicalInvolutionOddCore ↥(layerY Ω x)

@[expose] def secFam : Set (Subgroup (SecQuot Ω x)) :=
  quotFamily (pairFam Ω x) (classicalInvolutionOddCore ↥(layerY Ω x))

@[expose] noncomputable def secImg (L : Subgroup G) : Subgroup (SecQuot Ω x) :=
  ((coreAt x L).subgroupOf (layerY Ω x)).map
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)))

end Def

variable {r : ℕ} {Ω : Set (Subgroup G)} {x : G}

omit [Finite G] in
theorem secImg_mem {L : Subgroup G} (hL : XMem Ω x L) : secImg Ω x L ∈ secFam Ω x :=
  map_mem_quotFamily (subgroupOf_mem_pairFam hL)

omit [Finite G] in
theorem mem_secFam_iff {Lb : Subgroup (SecQuot Ω x)} :
    Lb ∈ secFam Ω x ↔ ∃ L, XMem Ω x L ∧ secImg Ω x L = Lb := by
  constructor
  · rintro ⟨_, ⟨_, ⟨L, hL, rfl⟩, -, rfl⟩, rfl⟩
    exact ⟨L, hL, rfl⟩
  · rintro ⟨L, hL, rfl⟩
    exact secImg_mem hL

theorem TypeRFam.secFam (h : TypeRFam r Ω) : TypeRFam r (secFam Ω x) :=
  h.pairFam.quotFamily (CFSG.ComponentClassification.OddCore.odd_card _)

theorem secQuot_oddCore_eq_bot : classicalInvolutionOddCore (SecQuot Ω x) = ⊥ :=
  CFSG.ComponentClassification.OddCore.quotient_corefree _

omit [Finite G] in
theorem omegaGen_secFam : omegaGen (secFam Ω x) = ⊤ := by
  have hY : omegaGen (pairFam Ω x) = ⊤ := omegaGen_restrictFamily_eq_top _ _ rfl
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective _
    (QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥(layerY Ω x))), ← hY,
    Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun K hK => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_omegaGen (map_mem_quotFamily hK)

theorem aEmpty_of_noTwins {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    (hΦ : HypOmegaGen Φ) {K : Subgroup X} (hK : K ∈ Φ) (hnt : ∀ K' ∈ twinSet Φ K, K' = K) :
    AEmpty Φ K := by
  intro J hJ hJn zK zJ hzK hzJ
  by_contra hcon
  have hInA : InA Φ K J := ⟨hJ, hJn, zK, zJ, hzK, hzJ, hcon⟩
  obtain ⟨u, v, r, t', Kstar, ustar, rstar, -, -, -, -, -, -, -, -, -, -, -, hne, htw, -⟩ :=
    Sec6Gen.l6_4ThreeGen X _ hΦ _ hK J hJ.1 hInA zK zJ hzK hzJ _ _ rfl rfl
  have hmem : Kstar ∈ twinSet Φ K := by
    rw [htw]
    exact Or.inr rfl
  exact hne (hnt _ hmem)

theorem aEmpty_secFam (h : TypeRFam r Ω) : ∀ Lb ∈ secFam Ω x, AEmpty (secFam Ω x) Lb :=
  fun _ hLb => aEmpty_of_noTwins h.secFam.hyp hLb (h.secFam.noTwins _ hLb)

theorem natCard_secQuot_lt (hx : ∃ g : G, g * x ≠ x * g) :
    Nat.card (SecQuot Ω x) < Nat.card G := by
  obtain ⟨g, hg⟩ := hx
  have hlt : Subgroup.centralizer ({x} : Set G) ≠ ⊤ := fun htop =>
    hg (Subgroup.mem_centralizer_singleton_iff.mp (htop ▸ Subgroup.mem_top g))
  have h1 : Nat.card (SecQuot Ω x) ≤ Nat.card ↥(layerY Ω x) :=
    Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
  have h2 : Nat.card ↥(layerY Ω x) ≤ Nat.card ↥(Subgroup.centralizer ({x} : Set G)) :=
    Subgroup.card_le_of_le layerY_le_centralizer
  have h3 : Nat.card ↥(Subgroup.centralizer ({x} : Set G)) < Nat.card G := by
    rw [← Subgroup.card_top (G := G)]
    exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hlt)
  omega

end CFSG.ClassicalInvolution.Q3.TL4
