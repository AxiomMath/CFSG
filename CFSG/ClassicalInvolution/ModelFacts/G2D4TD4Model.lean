module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Twin
public import CFSG.ClassicalInvolution.ModelFacts.G2D4Max
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Steinberg.TwistedD4.RankOne
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Count
public import CFSG.ClassicalInvolution.RouteD.G2D4E189Rest
public import CFSG.ClassicalInvolution.Asc77.AscIHD4
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
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952
public import CFSG.ClassicalInvolution.Asc77.AscE184Basic
public import CFSG.ClassicalInvolution.Asc77.AscSixZW
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairBoot
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE6
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE7
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsH
public import CFSG.Goldschmidt.StatementsX
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.QuasisimpleNormalizerCommutator

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Asc77

section Torus

variable {K : Type} [Field K]

theorem torusElt_long_neg_one : torusElt d4 K (nd 2) (-1) = rootDiagUnit d4 (aLongTD4 K) := by
  rw [torusElt_eq_rootDiagUnit]
  congr 1
  funext j
  fin_cases j
  · show (-1 : Kˣ) ^ d4.cartan (nd 2) (nd 0) = -1
    rw [show d4.cartan (nd 2) (nd 0) = -1 by decide]
    simp
  · show (-1 : Kˣ) ^ d4.cartan (nd 2) (nd 1) = -1
    rw [show d4.cartan (nd 2) (nd 1) = -1 by decide]
    simp
  · show (-1 : Kˣ) ^ d4.cartan (nd 2) (nd 2) = 1
    rw [show d4.cartan (nd 2) (nd 2) = 2 by decide]
    simp
  · show (-1 : Kˣ) ^ d4.cartan (nd 2) (nd 3) = -1
    rw [show d4.cartan (nd 2) (nd 3) = -1 by decide]
    simp

theorem torusElt_short_neg_one : torusElt d4 K (nd 0) (-1) * torusElt d4 K (nd 1) (-1) *
    torusElt d4 K (nd 3) (-1) = rootDiagUnit d4 (aShortTD4 K) := by
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit,
    ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  congr 1
  funext j
  simp only [Pi.mul_apply, ← zpow_add]
  fin_cases j
  · show (-1 : Kˣ) ^ (d4.cartan (nd 0) (nd 0) + d4.cartan (nd 1) (nd 0) + d4.cartan (nd 3) (nd 0))
      = 1
    rw [show d4.cartan (nd 0) (nd 0) + d4.cartan (nd 1) (nd 0) + d4.cartan (nd 3) (nd 0) = 2 by
      decide]
    simp
  · show (-1 : Kˣ) ^ (d4.cartan (nd 0) (nd 1) + d4.cartan (nd 1) (nd 1) + d4.cartan (nd 3) (nd 1))
      = 1
    rw [show d4.cartan (nd 0) (nd 1) + d4.cartan (nd 1) (nd 1) + d4.cartan (nd 3) (nd 1) = 2 by
      decide]
    simp
  · show (-1 : Kˣ) ^ (d4.cartan (nd 0) (nd 2) + d4.cartan (nd 1) (nd 2) + d4.cartan (nd 3) (nd 2))
      = -1
    rw [show d4.cartan (nd 0) (nd 2) + d4.cartan (nd 1) (nd 2) + d4.cartan (nd 3) (nd 2) = -3 by
      decide]
    rw [zpow_neg, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast,
      Odd.neg_one_pow (by decide), inv_neg_one]
  · show (-1 : Kˣ) ^ (d4.cartan (nd 0) (nd 3) + d4.cartan (nd 1) (nd 3) + d4.cartan (nd 3) (nd 3))
      = 1
    rw [show d4.cartan (nd 0) (nd 3) + d4.cartan (nd 1) (nd 3) + d4.cartan (nd 3) (nd 3) = 2 by
      decide]
    simp

theorem aLongTD4_mul_self : aLongTD4 K * aLongTD4 K = 1 := by
  funext j
  rw [Pi.mul_apply, Pi.one_apply]
  fin_cases j
  · show aLongTD4 K (nd 0) * aLongTD4 K (nd 0) = 1
    rw [show aLongTD4 K (nd 0) = -1 from rfl]
    simp
  · show aLongTD4 K (nd 1) * aLongTD4 K (nd 1) = 1
    rw [show aLongTD4 K (nd 1) = -1 from rfl]
    simp
  · show aLongTD4 K (nd 2) * aLongTD4 K (nd 2) = 1
    rw [show aLongTD4 K (nd 2) = 1 from rfl]
    simp
  · show aLongTD4 K (nd 3) * aLongTD4 K (nd 3) = 1
    rw [show aLongTD4 K (nd 3) = -1 from rfl]
    simp

theorem aShortTD4_mul_self : aShortTD4 K * aShortTD4 K = 1 := by
  funext j
  rw [Pi.mul_apply, Pi.one_apply]
  fin_cases j
  · show aShortTD4 K (nd 0) * aShortTD4 K (nd 0) = 1
    rw [show aShortTD4 K (nd 0) = 1 from rfl]
    simp
  · show aShortTD4 K (nd 1) * aShortTD4 K (nd 1) = 1
    rw [show aShortTD4 K (nd 1) = 1 from rfl]
    simp
  · show aShortTD4 K (nd 2) * aShortTD4 K (nd 2) = 1
    rw [show aShortTD4 K (nd 2) = -1 from rfl]
    simp
  · show aShortTD4 K (nd 3) * aShortTD4 K (nd 3) = 1
    rw [show aShortTD4 K (nd 3) = 1 from rfl]
    simp

theorem aLongTD4_ne_one (hK : (-1 : Kˣ) ≠ 1) : aLongTD4 K ≠ 1 := fun h =>
  hK (by have := congrFun h (nd 0); exact this)

theorem aShortTD4_ne_one (hK : (-1 : Kˣ) ≠ 1) : aShortTD4 K ≠ 1 := fun h =>
  hK (by have := congrFun h (nd 2); exact this)

end Torus

section Core

variable {K : Type} [Field K]

@[expose] def twistedIncl (σ : K →+* K) : twistedGroup σ →* ModGL d4 K :=
  (adjointGroup d4 K).subtype.comp (twistedGroup σ).subtype

theorem twistedIncl_injective (σ : K →+* K) : Function.Injective (twistedIncl σ) :=
  Subtype.val_injective.comp Subtype.val_injective

theorem twistedIncl_apply (σ : K →+* K) (x : twistedGroup σ) :
    twistedIncl σ x = ((x : adjointGroup d4 K) : ModGL d4 K) := rfl

theorem mem_normalizer_of_map_injective {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) {L : Subgroup G} {g : G}
    (h : f g ∈ Subgroup.normalizer ((L.map f : Subgroup H) : Set H)) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at h ⊢
  intro y
  have := h (f y)
  rw [Subgroup.mem_map_iff_mem hf, show f g * f y * (f g)⁻¹ = f (g * y * g⁻¹) by simp,
    Subgroup.mem_map_iff_mem hf] at this
  exact this

theorem map_twistedRootGroup (σ : K →+* K) {β : Fin (Tag.rank .G2) → ℤ} (hβ : IsRoot .G2 β) :
    (twistedRootGroup σ β).map (twistedIncl σ) =
      (twistedRootSubgroupD4 σ β).map (adjointGroup d4 K).subtype := by
  unfold twistedRootGroup twistedIncl
  rw [← Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le (twistedRootSubgroupD4_le_twistedGroup σ hβ)]

theorem map_rankOne_long (σ : K →+* K) :
    (rankOne (twistedRootGroup σ) (ng 0)).map (twistedIncl σ) =
      nodeGroupTD4 σ (Pi.single (nd 2) 1) := by
  rw [rankOne, Subgroup.map_sup, map_twistedRootGroup σ (isRoot_single .G2 (ng 0)),
    map_twistedRootGroup σ (isRoot_neg_single .G2 (ng 0)), ← proj_neg_single_two,
    ← proj_single_two, map_twistedRootSubgroupD4_eq σ (isRoot_single d4 (nd 2)),
    map_twistedRootSubgroupD4_eq σ (IsRoot.neg (isRoot_single d4 (nd 2)))]
  rfl

theorem map_rankOne_short (σ : K →+* K) :
    (rankOne (twistedRootGroup σ) (ng 1)).map (twistedIncl σ) =
      nodeGroupTD4 σ (Pi.single (nd 0) 1) := by
  rw [rankOne, Subgroup.map_sup, map_twistedRootGroup σ (isRoot_single .G2 (ng 1)),
    map_twistedRootGroup σ (isRoot_neg_single .G2 (ng 1)), ← proj_neg_single_zero,
    ← proj_single_zero, map_twistedRootSubgroupD4_eq σ (isRoot_single d4 (nd 0)),
    map_twistedRootSubgroupD4_eq σ (IsRoot.neg (isRoot_single d4 (nd 0)))]
  rfl

theorem exists_involution_long (σ : K →+* K) :
    ∃ τ ∈ rankOne (twistedRootGroup σ) (ng 0),
      twistedIncl σ τ = rootDiagUnit d4 (aLongTD4 K) := by
  have hfix : (-1 : Kˣ) ∈ fixedUnits σ := (mem_fixedUnits σ).2 (by simp)
  obtain ⟨τ, hτL, hτ⟩ := exists_hLong (σ := σ) ⟨-1, hfix⟩
  refine ⟨τ, hτL, ?_⟩
  rw [twistedIncl_apply, hτ]
  exact torusElt_long_neg_one

theorem exists_involution_short {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c) :
    ∃ τ ∈ rankOne (twistedRootGroup σ) (ng 1),
      twistedIncl σ τ = rootDiagUnit d4 (aShortTD4 K) := by
  have hmem : hShortHom σ (-1) ∈ hHatE σ (ng 1) := ⟨-1, rfl⟩
  have hΓ : hShortHom σ (-1) ∈ twistedGroup σ := hHatE_le_twistedGroup hσ (ng 1) hmem
  refine ⟨⟨hShortHom σ (-1), hΓ⟩, hHat_le_rankOne hσ (ng 1) ?_, ?_⟩
  · rw [hHat, Subgroup.mem_subgroupOf]
    exact hmem
  · rw [twistedIncl_apply]
    have hmap : Units.map σ.toMonoidHom (-1 : Kˣ) = -1 := Units.ext (by simp)
    show ((hShortHom σ (-1) : adjointGroup d4 K) : ModGL d4 K) = _
    rw [hShortHom_apply, hmap, hmap]
    exact torusElt_short_neg_one

theorem centralizer_le_normalizer_long {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)
    (hK : (-1 : Kˣ) ≠ 1)
    (hgF : ∀ g : twistedGroup σ, twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K σ)
    {c : twistedGroup σ} (hc : IsUniqueInvolution (rankOne (twistedRootGroup σ) (ng 0)) c)
    {g : twistedGroup σ} (hgc : g * c = c * g) :
    g ∈ Subgroup.normalizer (rankOne (twistedRootGroup σ) (ng 0) : Set (twistedGroup σ)) := by
  obtain ⟨τ, hτL, hτ⟩ := exists_involution_long σ
  have hτsq : τ * τ = 1 := by
    apply twistedIncl_injective σ
    rw [map_mul, hτ, ← rootDiagUnit_mul, aLongTD4_mul_self, rootDiagUnit_one, map_one]
  have hτne : τ ≠ 1 := by
    intro h
    rw [h, map_one, ← rootDiagUnit_one] at hτ
    exact aLongTD4_ne_one hK (rootDiagUnit_injective hτ.symm)
  have hτc : τ = c := (hc.unique τ hτL hτsq).resolve_left hτne
  subst hτc
  have hga : twistedIncl σ g ∈
      Subgroup.centralizer ({rootDiagUnit d4 (aLongTD4 K)} : Set (ModGL d4 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hτ, ← map_mul, ← map_mul, hgc]
  have h := mem_normalizer_nodeGroup_long σ hσ hK (hgF g) hga
  rw [← map_rankOne_long] at h
  exact mem_normalizer_of_map_injective (twistedIncl_injective σ) h

theorem centralizer_le_normalizer_short {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)
    (hK : (-1 : Kˣ) ≠ 1)
    (hgF : ∀ g : twistedGroup σ, twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K σ)
    {c : twistedGroup σ} (hc : IsUniqueInvolution (rankOne (twistedRootGroup σ) (ng 1)) c)
    {g : twistedGroup σ} (hgc : g * c = c * g) :
    g ∈ Subgroup.normalizer (rankOne (twistedRootGroup σ) (ng 1) : Set (twistedGroup σ)) := by
  obtain ⟨τ, hτL, hτ⟩ := exists_involution_short hσ
  have hτsq : τ * τ = 1 := by
    apply twistedIncl_injective σ
    rw [map_mul, hτ, ← rootDiagUnit_mul, aShortTD4_mul_self, rootDiagUnit_one, map_one]
  have hτne : τ ≠ 1 := by
    intro h
    rw [h, map_one, ← rootDiagUnit_one] at hτ
    exact aShortTD4_ne_one hK (rootDiagUnit_injective hτ.symm)
  have hτc : τ = c := (hc.unique τ hτL hτsq).resolve_left hτne
  subst hτc
  have hga : twistedIncl σ g ∈
      Subgroup.centralizer ({rootDiagUnit d4 (aShortTD4 K)} : Set (ModGL d4 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hτ, ← map_mul, ← map_mul, hgc]
  have h := mem_normalizer_nodeGroup_short σ hσ hK (hgF g) hga
  rw [← map_rankOne_short] at h
  exact mem_normalizer_of_map_injective (twistedIncl_injective σ) h

end Core

section Model

variable {p : ℕ} [Fact p.Prime]

theorem conjSub_eq_of_standard {G : Type} [Group G] {L : Subgroup G} (g₀ : G)
    (hL : ∀ c, IsUniqueInvolution L c → ∀ x, x * c = c * x →
      x ∈ Subgroup.normalizer (L : Set G))
    {c g : G} (hc : IsUniqueInvolution (conjSub g₀ L) c)
    (hg : IsUniqueInvolution (conjSub g (conjSub g₀ L)) c) :
    conjSub g (conjSub g₀ L) = conjSub g₀ L := by
  have hgc : g * c * g⁻¹ = c := (hg.eq (hc.conj g)).symm
  have hc₀ : IsUniqueInvolution L (g₀⁻¹ * c * g₀) := by
    have h := hc.conj g₀⁻¹
    rwa [← conjSub_mul, inv_mul_cancel, conjSub_one, inv_inv] at h
  have hx : g₀⁻¹ * g * g₀ ∈ Subgroup.normalizer (L : Set G) := by
    refine hL _ hc₀ _ ?_
    have h1 : g * c = c * g := by
      calc g * c = g * c * g⁻¹ * g := by group
        _ = c * g := by rw [hgc]
    calc g₀⁻¹ * g * g₀ * (g₀⁻¹ * c * g₀) = g₀⁻¹ * (g * c) * g₀ := by group
      _ = g₀⁻¹ * (c * g) * g₀ := by rw [h1]
      _ = g₀⁻¹ * c * g₀ * (g₀⁻¹ * g * g₀) := by group
  have hxL : conjSub (g₀⁻¹ * g * g₀) L = L := normalizer_iff_conjSub_eq.mp hx
  calc conjSub g (conjSub g₀ L) = conjSub (g * g₀) L := (conjSub_mul g g₀ L).symm
    _ = conjSub (g₀ * (g₀⁻¹ * g * g₀)) L := by congr 1; group
    _ = conjSub g₀ (conjSub (g₀⁻¹ * g * g₀) L) := conjSub_mul _ _ _
    _ = conjSub g₀ L := by rw [hxL]

theorem conjSub_eq_of_nodes {K : Type} [Field K] {σ : K →+* K}
    (hσ : ∀ c, σ (σ (σ c)) = c) (hK : (-1 : Kˣ) ≠ 1)
    (hgF : ∀ g : twistedGroup σ, twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K σ)
    {i : Fin (Tag.rank .G2)} {g₀ c g : twistedGroup σ}
    (hc : IsUniqueInvolution (conjSub g₀ (rankOne (twistedRootGroup σ) i)) c)
    (hg : IsUniqueInvolution (conjSub g (conjSub g₀ (rankOne (twistedRootGroup σ) i))) c) :
    conjSub g (conjSub g₀ (rankOne (twistedRootGroup σ) i)) =
      conjSub g₀ (rankOne (twistedRootGroup σ) i) := by
  refine conjSub_eq_of_standard g₀ (fun c hc x hx => ?_) hc hg
  match i with
  | ⟨0, _⟩ => exact centralizer_le_normalizer_long hσ hK hgF hc hx
  | ⟨1, _⟩ => exact centralizer_le_normalizer_short hσ hK hgF hc hx

theorem noTwinsFund_td4 (hp2 : p ≠ 2) {e : ℕ} (hadm : StatedLieAdmissible .trialityD4 0 p e) :
    NoTwinsFund p e .trialityD4 0 := by
  have he : 1 ≤ e := hadm.2.1
  have hK3 : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  have hfin : Finite (GaloisField p (3 * e)) := Nat.finite_of_card_ne_zero (by
    rw [hK3]
    exact (pow_pos (pow_pos (Fact.out : p.Prime).pos e) _).ne')
  have hσ : ∀ c, iterateFrobenius (GaloisField p (3 * e)) p e
      (iterateFrobenius (GaloisField p (3 * e)) p e
        (iterateFrobenius (GaloisField p (3 * e)) p e c)) = c :=
    sigma_three_of_card hK3 (fun c => iterateFrobenius_def p e c)
  have hK1 : (-1 : (GaloisField p (3 * e))ˣ) ≠ 1 := by
    intro h
    have hK2 : ringChar (GaloisField p (3 * e)) ≠ 2 := by
      rw [ringChar.eq (GaloisField p (3 * e)) p]
      exact hp2
    exact Ring.neg_one_ne_one_of_char_ne_two hK2 (by simpa using congrArg Units.val h)
  have hgF : ∀ g : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e),
      twistedIncl (iterateFrobenius (GaloisField p (3 * e)) p e) g ∈
        graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e))
          (iterateFrobenius (GaloisField p (3 * e)) p e) := fun g => by
    rw [← CFSG.ClassicalInvolution.RouteD.G2D4.map_twistedGroup_eq_graphFixedRootGroup p e hp2 he]
    exact Subgroup.mem_map_of_mem _ g.2
  intro F hF c hc g hg
  obtain ⟨i, g₀, rfl⟩ := exists_conj_rankOne_node_of_trialityD4 0 p e hadm hF
  exact conjSub_eq_of_nodes hσ hK1 hgF hc hg

theorem e189ModelAt_td4 (hp2 : p ≠ 2) {e : ℕ} (hadm : StatedLieAdmissible .trialityD4 0 p e) :
    E189ModelAt p e .trialityD4 0 :=
  e189ModelAt_of_noTwinsFund
    (CFSG.ClassicalInvolution.RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 (Or.inr rfl) 0
      hadm.2.1)
    (noTwinsFund_td4 hp2 hadm)

theorem e189Rest_unconditional : E189Rest p where
  g2 _ hp2 hadm := e189ModelAt_g2_odd hp2 hadm
  td4 _ hp2 hadm := e189ModelAt_td4 hp2 hadm

end Model

end CFSG.ClassicalInvolution.G2D4Models
