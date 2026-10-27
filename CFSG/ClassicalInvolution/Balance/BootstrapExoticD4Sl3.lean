module

public import CFSG.ClassicalInvolution.Balance.BootstrapExoticG2Sl3
public import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2Tags
public import CFSG.ClassicalInvolution.ModelFacts.StandardPair
public import CFSG.LieType.Steinberg.TwistedD4.Perfect
public import CFSG.LieType.Steinberg.TwistedD4.RankOne
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectPSU
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.RouteD.LocalLift
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Chevalley.RootWalk CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.Timmesfeld CFSG.ClassicalInvolution.WeakCT
open scoped commutatorElement MatrixGroups

section Roots

@[expose] def d4Hex : Fin 6 → Fin d4.rank → ℤ :=
  ![![0, 0, 1, 0], ![1, 1, 2, 1], ![1, 1, 1, 1], ![0, 0, -1, 0], ![-1, -1, -2, -1],
    ![-1, -1, -1, -1]]

@[expose] def d4HexPos : Fin 6 → ℕ := ![2, 22, 19, 8, 23, 21]

theorem d4Root_d4Pos (k : Fin 6) : d4Root (d4HexPos k) = d4Hex k := by
  revert k
  decide +kernel

theorem d4HexPos_lt (k : Fin 6) : d4HexPos k < (Tag.rootCertificate d4).roots.length := by
  revert k
  decide +kernel

theorem isRoot_d4Hex (k : Fin 6) : IsRoot d4 (d4Hex k) := by
  rw [← d4Root_d4Pos]
  exact isRoot_d4Root (d4HexPos_lt k)

theorem rho_d4Hex (k : Fin 6) : rho (d4Hex k) = d4Hex k := by
  revert k
  decide +kernel

theorem proj_d4Hex (k : Fin 6) : proj (d4Hex k) = g2Hex k := by
  revert k
  decide +kernel

theorem d4Hex_rot (k : Fin 6) :
    reflect d4 (nd 2) (reflect d4 (nd 0) (reflect d4 (nd 1) (reflect d4 (nd 3) (d4Hex k)))) =
      d4Hex (k + 1) := by
  revert k
  decide +kernel

theorem isRoot_d4_iff {v : Fin d4.rank → ℤ} : IsRoot d4 v ↔ ∃ k < 24, d4Root k = v := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check d4),
    show (Tag.rootCertificate d4).roots.length = 24 by decide]

theorem not_isRoot_d4Hex_zero_one : ¬IsRoot d4 (d4Hex 0 + d4Hex 1) := by
  rw [isRoot_d4_iff]
  decide +kernel

theorem d4Hex_zero_ne_one : d4Hex 0 ≠ d4Hex 1 := by decide +kernel

theorem d4Hex_zero_ne_neg_one : d4Hex 0 ≠ -d4Hex 1 := by decide +kernel

end Roots

section Elements

local notation "𝕩" => xPar (rootOperatorFamily d4)

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

@[expose] noncomputable def d4X (k : Fin 6) (c : fixedField σ) : ↥(twistedGroup σ) :=
  ⟨𝕩 (d4Hex k) (c : K), twistedRootSubgroupD4_le_twistedGroup σ
    (isRoot_proj (isRoot_d4Hex k)) (xPar_mem_of_fixed hσ (isRoot_d4Hex k) (rho_d4Hex k) c.2)⟩

variable {hσ}

theorem d4X_add (k : Fin 6) (s t : fixedField σ) :
    d4X hσ k (s + t) = d4X hσ k s * d4X hσ k t :=
  Subtype.ext (xPar_add _ _ _)

theorem d4X_injective (k : Fin 6) : Function.Injective (d4X hσ k) := fun _ _ h =>
  Subtype.ext (xPar_injective (isRoot_d4Hex k) (congrArg Subtype.val h))

theorem d4X_zero (k : Fin 6) : d4X hσ k 0 = 1 := Subtype.ext (xPar_zero _)

theorem d4X_commutator_coe (j k : Fin 6) (s t : fixedField σ) :
    ((⁅d4X hσ j s, d4X hσ k t⁆ : ↥(twistedGroup σ)) : adjointGroup d4 K) =
      ⁅𝕩 (d4Hex j) (s : K), 𝕩 (d4Hex k) (t : K)⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  rfl

theorem d4X_comm_one (s t : fixedField σ) : ⁅d4X hσ 0 s, d4X hσ 1 t⁆ = 1 :=
  Subtype.ext (by
    rw [d4X_commutator_coe]
    exact commutatorElement_eq_one_iff_commute.2
      (CFSG.LieType.Steinberg.TwistedD4.commute_xPar (isRoot_d4Hex 0)
      (isRoot_d4Hex 1) d4Hex_zero_ne_one d4Hex_zero_ne_neg_one not_isRoot_d4Hex_zero_one _ _))

theorem commutator_xPar_d4Hex (s t : K) :
    ⁅𝕩 (d4Hex 0) s, 𝕩 (d4Hex 2) t⁆ = 𝕩 (d4Hex 1) (s * t) := by
  have h2 : d4HexPos 0 < (Tag.rootCertificate d4).roots.length := d4HexPos_lt 0
  have h19 : d4HexPos 2 < (Tag.rootCertificate d4).roots.length := d4HexPos_lt 2
  have h22 : d4HexPos 1 < (Tag.rootCertificate d4).roots.length := d4HexPos_lt 1
  have hcheck : RootOps.repCheck d4 2 19 [(1, 1, 22, 1)] = true := by decide +kernel
  have key := commutator_eltElement_of_repCheck (τ := d4)
    (RootOps.d4_allValid : RootOps.allValid d4 = true) hcheck h22
    (α := ⟨d4Hex 0, isRoot_d4Hex 0⟩) (β := ⟨d4Hex 2, isRoot_d4Hex 2⟩)
    (RootOps.rootPos_eq h2 (d4Root_d4Pos 0)) (RootOps.rootPos_eq h19 (d4Root_d4Pos 2)) s t
  have hr : RootOps.rootAt d4 22 h22 = ⟨d4Hex 1, isRoot_d4Hex 1⟩ :=
    Subtype.ext (d4Root_d4Pos 1)
  rw [commutatorElement_def, xPar_of_isRoot (isRoot_d4Hex 0), xPar_of_isRoot (isRoot_d4Hex 2),
    xPar_of_isRoot (isRoot_d4Hex 1), key, hr]
  congr 1
  push_cast
  ring

theorem d4X_comm_two (s t : fixedField σ) :
    ⁅d4X hσ 0 s, d4X hσ 2 t⁆ = d4X hσ 1 (((1 : ℤ) : fixedField σ) * s * t) :=
  Subtype.ext (by
    rw [d4X_commutator_coe, commutator_xPar_d4Hex]
    simp [d4X])

end Elements

section Rotation

local notation "𝕩" => xPar (rootOperatorFamily d4)

variable {K : Type} [Field K] {σ : K →+* K}

theorem d4_weylConj (i : Fin d4.rank) {β : Fin d4.rank → ℤ} (hβ : IsRoot d4 β) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ u : K,
      CFSG.LieType.Chevalley.weylElement d4 K i * 𝕩 β u *
          (CFSG.LieType.Chevalley.weylElement d4 K i)⁻¹ = 𝕩 (reflect d4 i β) ((ε : K) * u) := by
  obtain ⟨ε, hε, h⟩ := weylElement_xPar_conj (F := rootOperatorFamily d4) (K := K) i hβ
  refine ⟨ε, hε, fun u => ?_⟩
  have h1 := h 1 u
  rw [← weylElement_eq_xPar (rootOperatorFamily d4) i] at h1
  rw [h1]
  have hrefl : CFSG.LieType.RootSystem.reflection d4.cartan i β = reflect d4 i β := by
    rw [CFSG.LieType.RootSystem.reflection_apply]
    rfl
  rw [hrefl]
  simp

theorem d4_rotConj (k : Fin 6) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ u : K,
      (CFSG.LieType.Chevalley.weylElement d4 K (nd 2) *
          (CFSG.LieType.Chevalley.weylElement d4 K (nd 0) *
            CFSG.LieType.Chevalley.weylElement d4 K (nd 1) *
            CFSG.LieType.Chevalley.weylElement d4 K (nd 3))) * 𝕩 (d4Hex k) u *
        (CFSG.LieType.Chevalley.weylElement d4 K (nd 2) *
          (CFSG.LieType.Chevalley.weylElement d4 K (nd 0) *
            CFSG.LieType.Chevalley.weylElement d4 K (nd 1) *
            CFSG.LieType.Chevalley.weylElement d4 K (nd 3)))⁻¹ =
        𝕩 (d4Hex (k + 1)) ((ε : K) * u) := by
  obtain ⟨ε₃, h₃, c₃⟩ := d4_weylConj (K := K) (nd 3) (isRoot_d4Hex k)
  obtain ⟨ε₁, h₁, c₁⟩ := d4_weylConj (K := K) (nd 1) (IsRoot.reflect (nd 3) (isRoot_d4Hex k))
  obtain ⟨ε₀, h₀, c₀⟩ := d4_weylConj (K := K) (nd 0)
    (IsRoot.reflect (nd 1) (IsRoot.reflect (nd 3) (isRoot_d4Hex k)))
  obtain ⟨ε₂, h₂, c₂⟩ := d4_weylConj (K := K) (nd 2)
    (IsRoot.reflect (nd 0) (IsRoot.reflect (nd 1) (IsRoot.reflect (nd 3) (isRoot_d4Hex k))))
  refine ⟨ε₂ * ε₀ * ε₁ * ε₃, ?_, fun u => ?_⟩
  · rcases h₂ with rfl | rfl <;> rcases h₀ with rfl | rfl <;> rcases h₁ with rfl | rfl <;>
      rcases h₃ with rfl | rfl <;> simp
  · have e : ∀ a b c d x : adjointGroup d4 K,
        (a * (b * c * d)) * x * (a * (b * c * d))⁻¹ =
          a * (b * (c * (d * x * d⁻¹) * c⁻¹) * b⁻¹) * a⁻¹ :=
      fun a b c d x => by group
    rw [e, c₃, c₁, c₀, c₂, d4Hex_rot k]
    congr 1
    push_cast
    ring

variable (hσ : ∀ c, σ (σ (σ c)) = c)

theorem d4_exists_rotation :
    ∃ κ : Fin 6 → fixedField σ, (∀ k, κ k * κ k = 1) ∧ ∀ (k : Fin 6) (u : fixedField σ),
      nHat σ (ng 0) * nHat σ (ng 1) * d4X hσ k u * (nHat σ (ng 0) * nHat σ (ng 1))⁻¹ =
        d4X hσ (k + 1) (κ k * u) := by
  choose ε hε hconj using fun k : Fin 6 => d4_rotConj (K := K) k
  refine ⟨fun k => ((ε k : ℤ) : fixedField σ), fun k => ?_, fun k u => ?_⟩
  · rcases hε k with h | h <;> simp [h]
  · apply Subtype.ext
    have h := hconj k (u : K)
    change (nHatE K (ng 0) * nHatE K (ng 1)) * 𝕩 (d4Hex k) (u : K) *
        (nHatE K (ng 0) * nHatE K (ng 1))⁻¹ = _
    rw [nHatE_zero, nHatE_one, h]
    simp [d4X]

end Rotation

section Sl3

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

theorem d4_exists_sl3 [Finite K] :
    ∃ (ρ : SL(3, fixedField σ) →* ↥(twistedGroup σ)) (l : Fin 6 → fixedField σ),
      (∀ k, l k * l k = 1) ∧ ∀ c,
      ρ (tv 0 1 c) = d4X hσ 0 (l 0 * c) ∧ ρ (tv 1 2 c) = d4X hσ 2 (l 2 * c) ∧
      ρ (tv 0 2 c) = d4X hσ 1 (l 1 * c) ∧ ρ (tv 1 0 c) = d4X hσ 3 (l 3 * c) ∧
      ρ (tv 2 1 c) = d4X hσ 5 (l 5 * c) ∧ ρ (tv 2 0 c) = d4X hσ 4 (l 4 * c) := by
  obtain ⟨κ, hκ, hrot⟩ := d4_exists_rotation hσ
  exact exists_sl3_of_rotation (x := d4X hσ) (g := nHat σ (ng 0) * nHat σ (ng 1)) (κ := κ)
    (fun k s t => d4X_add k s t) (d4X_injective 1) hκ hrot (N := ((1 : ℤ) : fixedField σ))
    (by simp) d4X_comm_one d4X_comm_two

theorem mem_rootGroup_d4Hex_iff (k : Fin 6) {x : ↥(twistedGroup σ)} :
    x ∈ (twistedDatum σ).rootGroup (g2Hex k) ↔ ∃ c : fixedField σ, x = d4X hσ k c := by
  change x ∈ twistedRootGroup σ (g2Hex k) ↔ _
  rw [mem_twistedRootGroup]
  constructor
  · intro hx
    obtain ⟨c, hc, hxc⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ (isRoot_d4Hex k)
      (proj_d4Hex k) (rho_d4Hex k) _).1 hx
    exact ⟨⟨c, hc⟩, Subtype.ext hxc⟩
  · rintro ⟨c, rfl⟩
    exact (mem_twistedRootSubgroupD4_iff_of_fixed hσ (isRoot_d4Hex k) (proj_d4Hex k)
      (rho_d4Hex k) _).2 ⟨c, c.2, rfl⟩

theorem twistedDatum_rootGroup_hex_eq_range (k : Fin 6) {u : fixedField σ} (hu : u * u = 1) :
    ((twistedDatum σ).rootGroup (g2Hex k) : Set ↥(twistedGroup σ)) =
      Set.range fun c => d4X hσ k (u * c) := by
  have hu0 : u ≠ 0 := fun h => by
    rw [h, mul_zero] at hu
    exact zero_ne_one hu
  ext x
  rw [SetLike.mem_coe, mem_rootGroup_d4Hex_iff hσ k]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨u⁻¹ * c, by
      show d4X hσ k (u * (u⁻¹ * c)) = d4X hσ k c
      rw [mul_inv_cancel_left₀ hu0]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨u * c, rfl⟩

include hσ in
theorem d4_standardPair_base [Finite K] :
    ∃ W, LinearBlockStandardPair (fixedField σ) W
      ((twistedDatum σ).rootGroup (g2Hex 0) ⊔ (twistedDatum σ).rootGroup (-g2Hex 0))
      ((twistedDatum σ).rootGroup (g2Hex 2) ⊔ (twistedDatum σ).rootGroup (-g2Hex 2)) := by
  obtain ⟨ρ, l, hl, hρ⟩ := d4_exists_sl3 hσ
  have hl0 : l 0 ≠ 0 := fun h => by
    have := hl 0
    rw [h, mul_zero] at this
    exact zero_ne_one this
  have hnt : ∃ g, ρ g ≠ 1 := ⟨tv 0 1 1, fun h => by
    rw [(hρ 1).1] at h
    have h2 := d4X_injective 0 (h.trans (d4X_zero 0).symm)
    exact hl0 (by simpa using h2)⟩
  have hker : ρ.ker ≤ Subgroup.center SL(3, fixedField σ) :=
    ker_le_center_of_isQuasisimple (SpecialLinear.isQuasisimple 2 (fixedField σ) le_rfl) hnt
  rw [g2Hex_neg_zero, g2Hex_neg_two]
  exact ⟨_, ModelFacts.linearBlockStandardPair_sup (K := ↥(twistedGroup σ))
    (twistedDatum_rootGroup_hex_eq_range hσ 0 (hl 0))
    (twistedDatum_rootGroup_hex_eq_range hσ 3 (hl 3))
    (twistedDatum_rootGroup_hex_eq_range hσ 2 (hl 2))
    (twistedDatum_rootGroup_hex_eq_range hσ 5 (hl 5))
    ρ hker fun c => ⟨(hρ c).1, (hρ c).2.2.2.1, (hρ c).2.1, (hρ c).2.2.2.2.1⟩⟩

end Sl3

end CFSG.ClassicalInvolution.Balance
