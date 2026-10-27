module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotFieldNormalizeE7
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAlignFieldTriangle

public section

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore)
open E6Pilot (modelToG mem_modelToG symm_mem_modelToG)

local instance e8PilotFieldNormalizeExistsNeZeroRank : NeZero Tag.E8.rank := ⟨by decide⟩

section Models

variable (K : Type) [Field K]

@[expose] noncomputable def neighbourLeviEquiv (N : E8Neighbour) : ↥(e7Levi K) ≃* ↥(N.levi K) :=
  ((MulAut.conj (N.rep K)).subgroupMap (e7Levi K)).trans
    (MulEquiv.subgroupCongr (map_conj_rep_e7Levi N))

variable {K}

theorem coe_neighbourLeviEquiv (N : E8Neighbour) (g : e7Levi K) :
    (((neighbourLeviEquiv K N g : N.levi K) : adjointGroup .E8 K) : ModGL .E8 K) =
      (N.rep K : ModGL .E8 K) * ((g : adjointGroup .E8 K) : ModGL .E8 K) *
        (N.rep K : ModGL .E8 K)⁻¹ :=
  rfl

theorem leviBaseChange_neighbourLeviEquiv {k : Type} [Field k] (ι : k →+* K) (N : E8Neighbour)
    (g : e7Levi k) :
    leviBaseChange ι N (neighbourLeviEquiv k N g) =
      neighbourLeviEquiv K N (e7LeviBaseChange ι g) := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [coe_leviBaseChange, coe_neighbourLeviEquiv, coe_neighbourLeviEquiv, map_mul, map_mul, map_inv,
    baseChangeGL_rep, coe_e7LeviBaseChange]

end Models

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .E8 (fixSubfield σ)}

theorem nonempty_fieldNeighbourIso (N : E8Neighbour)
    (hψ : Nonempty (N.levi K ≃* neighbourCore e N)) {t : G} (htL : t ∈ centralizer (L : Set G))
    (ht2 : orderOf t = 2) (hσ : orderOf σ = 2)
    (hfix : perfectCore (neighbourCore e N ⊓ centralizer ({t} : Set G)) =
      modelToG e ((N.levi (fixSubfield σ)).map (adjointGroup .E8 (fixSubfield σ)).subtype)) :
    Nonempty (FieldNeighbourIso σ e N) := by
  obtain ⟨ψ₀⟩ := hψ
  have hN : t ∈ normalizer (neighbourCore e N : Set G) := le_normalizer_neighbourCore e htL N
  have ht : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have hθθ : (neighbourCore e N).normalizerMonoidHom ⟨t, hN⟩ *
      (neighbourCore e N).normalizerMonoidHom ⟨t, hN⟩ = 1 := by
    rw [← map_mul, show (⟨t, hN⟩ : normalizer (neighbourCore e N : Set G)) * ⟨t, hN⟩ = 1 from
      Subtype.ext ht, map_one]
  have hD : modelToG e ((N.levi (fixSubfield σ)).map (adjointGroup .E8 (fixSubfield σ)).subtype) ≤
      neighbourCore e N := by
    rw [← hfix]
    exact (CFSG.Quasithin.perfectCore_le _).trans inf_le_left
  set ε₀ : e7Levi (fixSubfield σ) →* G := L.subtype.comp (e.symm.toMonoidHom.comp
    ((N.levi (fixSubfield σ)).subtype.comp (neighbourLeviEquiv (fixSubfield σ) N).toMonoidHom))
    with hε₀
  have hε₀M : ∀ g, ε₀ g ∈ neighbourCore e N := fun g =>
    hD (symm_mem_modelToG e ⟨_, (neighbourLeviEquiv (fixSubfield σ) N g).2, rfl⟩)
  set ε : e7Levi (fixSubfield σ) →* neighbourCore e N := ε₀.codRestrict _ hε₀M with hε
  have hεinj : Function.Injective ε := by
    intro g₁ g₂ h
    apply (neighbourLeviEquiv (fixSubfield σ) N).injective
    apply Subtype.ext
    apply e.symm.injective
    apply Subtype.ext
    exact congrArg (fun z : neighbourCore e N => (z : G)) h
  have hεrange : ε.range.map (neighbourCore e N).subtype =
      modelToG e ((N.levi (fixSubfield σ)).map (adjointGroup .E8 (fixSubfield σ)).subtype) := by
    ext g
    constructor
    · rintro ⟨_, ⟨g', rfl⟩, rfl⟩
      exact symm_mem_modelToG e ⟨_, (neighbourLeviEquiv (fixSubfield σ) N g').2, rfl⟩
    · intro hg
      obtain ⟨x, ⟨y, hy, hyx⟩, rfl⟩ := (mem_modelToG e).1 hg
      have hxy : x = y := Subtype.ext hyx.symm
      subst hxy
      obtain ⟨g', hg'⟩ := (neighbourLeviEquiv (fixSubfield σ) N).surjective ⟨x, hy⟩
      refine ⟨ε g', ⟨g', rfl⟩, ?_⟩
      change ((e.symm ((neighbourLeviEquiv (fixSubfield σ) N g' : N.levi (fixSubfield σ)) :
        adjointGroup .E8 (fixSubfield σ)) : L) : G) = _
      rw [hg']
  have hεr : ε.range = perfectCore (MonoidHom.eqLocus
      ((neighbourCore e N).normalizerMonoidHom ⟨t, hN⟩).toMonoidHom (MonoidHom.id _)) := by
    apply map_injective (neighbourCore e N).subtype_injective
    rw [CFSG.Quasithin.map_perfectCore, F4Pilot.map_eqLocus_normalizerMonoidHom hN, hfix,
      hεrange]
  obtain ⟨ψ', hψ'⟩ := exists_mulEquiv_e7LeviBaseChange_eq (fixSubfield σ).subtype hσ
    (F4Pilot.apply_eq_iff_mem_range_fixSubfield_subtype σ) ((neighbourLeviEquiv K N).trans ψ₀)
    hθθ ε hεinj hεr
  refine ⟨⟨(neighbourLeviEquiv K N).symm.trans ψ', fun x => ?_⟩⟩
  obtain ⟨g, rfl⟩ := (neighbourLeviEquiv (fixSubfield σ) N).surjective x
  rw [MulEquiv.trans_apply, leviInclusion, leviBaseChange_neighbourLeviEquiv,
    MulEquiv.symm_apply_apply, hψ']
  rfl

theorem exists_aligned_normalized_fieldNeighbourIso
    (hψ : Nonempty (E8Neighbour.high.levi K ≃* neighbourCore e .high)) {t : G}
    (htL : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) (hσ : orderOf σ = 2)
    (hfix : perfectCore (neighbourCore e .high ⊓ centralizer ({t} : Set G)) =
      modelToG e ((E8Neighbour.high.levi (fixSubfield σ)).map
        (adjointGroup .E8 (fixSubfield σ)).subtype))
    (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    ∃ (hX : FieldNeighbourIso σ e .high) (hY : FieldNeighbourIso σ e .two)
      (hZ : FieldNeighbourIso σ e .six),
      (∀ {J : Finset (Fin (Tag.rank .E8))}, J ⊆ E8Neighbour.high.nodes → J.card ≤ 2 →
        ((leviPiece K .high J).map hX.Φ.toMonoidHom).map (neighbourCore e .high).subtype =
          pieceCore e J) ∧
      (∀ {J : Finset (Fin (Tag.rank .E8))}, J ⊆ E8Neighbour.two.nodes → J.card ≤ 2 →
        ((leviPiece K .two J).map hY.Φ.toMonoidHom).map (neighbourCore e .two).subtype =
          pieceCore e J) ∧
      (∀ {J : Finset (Fin (Tag.rank .E8))}, J ⊆ E8Neighbour.six.nodes → J.card ≤ 2 →
        ((leviPiece K .six J).map hZ.Φ.toMonoidHom).map (neighbourCore e .six).subtype =
          pieceCore e J) ∧
      (∀ {J : Finset (Fin (Tag.rank .E8))}, J ⊆ {0, 2, 4, 5, 6} →
        ∀ (x : E8Neighbour.high.levi K) (x' : E8Neighbour.two.levi K),
          (x : adjointGroup .E8 K) = x' → x ∈ leviPiece K .high J →
            ((hX.Φ x : neighbourCore e .high) : G) = hY.Φ x') ∧
      (∀ {J : Finset (Fin (Tag.rank .E8))}, J ⊆ {0, 1, 2, 3} →
        ∀ (x : E8Neighbour.high.levi K) (x' : E8Neighbour.six.levi K),
          (x : adjointGroup .E8 K) = x' → x ∈ leviPiece K .high J →
            ((hX.Φ x : neighbourCore e .high) : G) = hZ.Φ x') ∧
      (∀ {J : Finset (Fin (Tag.rank .E8))}, J ⊆ {0, 2, 7} →
        ∀ (x : E8Neighbour.two.levi K) (x' : E8Neighbour.six.levi K),
          (x : adjointGroup .E8 K) = x' → x ∈ leviPiece K .two J →
            ((hY.Φ x : neighbourCore e .two) : G) = hZ.Φ x') := by
  obtain ⟨hX⟩ := nonempty_fieldNeighbourIso .high hψ htL ht2 hσ hfix
  obtain ⟨hY, hZ, h1, h2, h3⟩ :=
    exists_aligned_fieldNeighbourIso_eq_on_leviPiece hX (hX.toNeighbour .two)
      (hX.toNeighbour .six) hq
  exact ⟨hX, hY, hZ, fun hJ hJ2 => hX.map_leviPiece hq hJ hJ2,
    fun hJ hJ2 => hY.map_leviPiece hq hJ hJ2, fun hJ hJ2 => hZ.map_leviPiece hq hJ hJ2, h1, h2, h3⟩

end Main

end CFSG.SeitzReduction.E8Pilot
