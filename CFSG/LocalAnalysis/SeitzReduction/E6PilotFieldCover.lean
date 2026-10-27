module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotFieldCoverLift

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (F4Work QuadraticFrobenius)
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut)

section Normalize


variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

theorem center_levi_eq_bot (N : E6Neighbour) : center (N.levi K) = ⊥ := by
  rw [← Subgroup.map_center_eq (neighbourLeviEquiv K N), center_a5Levi_eq_bot, Subgroup.map_bot]

set_option maxHeartbeats 400000 in
theorem exists_normalized_of_surjective (hσ : orderOf σ = 2) (N : E6Neighbour) {E : Subgroup G}
    {t : G} (hN : t ∈ normalizer (E : Set G)) (ht2 : orderOf t = 2)
    (hfix : perfectCore (E ⊓ centralizer ({t} : Set G)) =
      modelToG e ((N.levi (fixSubfield σ)).map (adjointGroup .E6 (fixSubfield σ)).subtype))
    (p : E →* N.levi K) (hp : Function.Surjective p) (hker : p.ker ≤ center E)
    (hodd : Odd (Nat.card p.ker)) :
    ∃ p' : E →* N.levi K, Function.Surjective p' ∧ p'.ker = center E ∧ Odd (Nat.card p'.ker) ∧
      ∀ x : N.levi (fixSubfield σ), ∃ y : E,
        (y : G) = ((e.symm (x : adjointGroup .E6 (fixSubfield σ)) : L) : G) ∧
          p' y = leviInclusion σ N x := by
  have : Finite (adjointGroup .E6 K) := by
    have : Finite (ModGL Tag.E6 K) := finite_modGL
    infer_instance
  have hkerZ : p.ker = center E := by
    refine le_antisymm hker fun z hz => ?_
    rw [MonoidHom.mem_ker]
    have hpz : p z ∈ center (N.levi K) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := hp y
      rw [← map_mul, ← map_mul, mem_center_iff.1 hz x]
    rw [center_levi_eq_bot N] at hpz
    exact hpz
  have hZodd : Odd (Nat.card (center E)) := hkerZ ▸ hodd
  set eb : E ⧸ center E ≃* N.levi K :=
    (QuotientGroup.quotientMulEquivOfEq hkerZ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective p hp) with hebdef
  set θ : MulAut (N.levi K) := normalizerQuotMulAut eb ⟨t, hN⟩ with hθdef
  have hθθ : θ * θ = 1 := by
    rw [← sq]
    exact normalizerQuotMulAut_sq_eq_one eb ht2 hN
  have hD : modelToG e ((N.levi (fixSubfield σ)).map (adjointGroup .E6 (fixSubfield σ)).subtype) ≤
      E := by
    rw [← hfix]
    exact (CFSG.Quasithin.perfectCore_le _).trans inf_le_left
  set ε₀ : a5Levi (fixSubfield σ) →* G := L.subtype.comp (e.symm.toMonoidHom.comp
    ((N.levi (fixSubfield σ)).subtype.comp (neighbourLeviEquiv (fixSubfield σ) N).toMonoidHom))
    with hε₀
  have hε₀M : ∀ g, ε₀ g ∈ E := fun g =>
    hD (symm_mem_modelToG e ⟨_, (neighbourLeviEquiv (fixSubfield σ) N g).2, rfl⟩)
  set εE : a5Levi (fixSubfield σ) →* E := ε₀.codRestrict _ hε₀M with hεE
  have hεEinj : Function.Injective εE := by
    intro g₁ g₂ h
    apply (neighbourLeviEquiv (fixSubfield σ) N).injective
    apply Subtype.ext
    apply e.symm.injective
    apply Subtype.ext
    exact congrArg (fun z : E => (z : G)) h
  have hεErange : εE.range.map E.subtype =
      modelToG e ((N.levi (fixSubfield σ)).map (adjointGroup .E6 (fixSubfield σ)).subtype) := by
    ext g
    constructor
    · rintro ⟨_, ⟨g', rfl⟩, rfl⟩
      exact symm_mem_modelToG e ⟨_, (neighbourLeviEquiv (fixSubfield σ) N g').2, rfl⟩
    · intro hg
      obtain ⟨x, ⟨y, hy, hyx⟩, rfl⟩ := (mem_modelToG e).1 hg
      have hxy : x = y := Subtype.ext hyx.symm
      subst hxy
      obtain ⟨g', hg'⟩ := (neighbourLeviEquiv (fixSubfield σ) N).surjective ⟨x, hy⟩
      refine ⟨εE g', ⟨g', rfl⟩, ?_⟩
      change ((e.symm ((neighbourLeviEquiv (fixSubfield σ) N g' : N.levi (fixSubfield σ)) :
        adjointGroup .E6 (fixSubfield σ)) : L) : G) = _
      rw [hg']
  set π₀ : E →* N.levi K := eb.toMonoidHom.comp (QuotientGroup.mk' (center E)) with hπ₀
  set ε : a5Levi (fixSubfield σ) →* N.levi K := π₀.comp εE with hεdef
  have hεinj : Function.Injective ε := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have hgZ : εE g ∈ center E := by
      rw [← QuotientGroup.ker_mk' (center E), MonoidHom.mem_ker]
      have h1 : eb (QuotientGroup.mk' (center E) (εE g)) = 1 := hg
      exact eb.injective (h1.trans (map_one eb).symm)
    have hgc : g ∈ center (a5Levi (fixSubfield σ)) := by
      rw [mem_center_iff]
      intro h
      apply hεEinj
      rw [map_mul, map_mul]
      exact mem_center_iff.1 hgZ (εE h)
    rw [center_a5Levi_eq_bot] at hgc
    exact hgc
  have hPcore : perfectCore ((centralizer ({t} : Set G)).subgroupOf E) = εE.range := by
    apply map_injective E.subtype_injective
    rw [CFSG.Quasithin.map_perfectCore, subgroupOf_map_subtype, inf_comm, hfix, hεErange]
  have hεr : ε.range = perfectCore (MonoidHom.eqLocus θ.toMonoidHom (MonoidHom.id _)) := by
    have hfixθ : MonoidHom.eqLocus θ.toMonoidHom (MonoidHom.id _) =
        ((centralizer ({t} : Set G)).subgroupOf E).map π₀ :=
      (map_subgroupOf_centralizer_eq_fixSubgroup hZodd eb ht2 hN).symm
    rw [hfixθ, ← CFSG.Quasithin.map_perfectCore, hPcore, hεdef, MonoidHom.range_comp]
  obtain ⟨ψ', hψ'⟩ := exists_mulEquiv_a5LeviBaseChange_eq (fixSubfield σ).subtype hσ
    (F4Pilot.apply_eq_iff_mem_range_fixSubfield_subtype σ) (neighbourLeviEquiv K N) hθθ ε hεinj
    hεr
  set p' : E →* N.levi K :=
    ((neighbourLeviEquiv K N).toMonoidHom.comp ψ'.symm.toMonoidHom).comp π₀ with hp'
  have hp'ker : p'.ker = center E := by
    ext z
    rw [MonoidHom.mem_ker, hp', MonoidHom.comp_apply, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      MulEquiv.map_eq_one_iff, hπ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  refine ⟨p', ((neighbourLeviEquiv K N).surjective.comp ψ'.symm.surjective).comp
      (eb.surjective.comp (QuotientGroup.mk'_surjective _)), hp'ker, hp'ker ▸ hZodd, fun x => ?_⟩
  obtain ⟨g, rfl⟩ := (neighbourLeviEquiv (fixSubfield σ) N).surjective x
  refine ⟨εE g, rfl, ?_⟩
  have h1 : ψ'.symm (ε g) = a5LeviBaseChange (fixSubfield σ).subtype g := by
    rw [MulEquiv.symm_apply_eq, hψ']
  change neighbourLeviEquiv K N (ψ'.symm (ε g)) = _
  rw [h1, leviInclusion, leviBaseChange_neighbourLeviEquiv]

theorem nonempty_fieldNeighbourCover_of_surjective (hσ : orderOf σ = 2) (N : E6Neighbour)
    {t : G} (htL : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hfix : perfectCore (neighbourCore e N ⊓ centralizer ({t} : Set G)) =
      modelToG e ((N.levi (fixSubfield σ)).map (adjointGroup .E6 (fixSubfield σ)).subtype))
    (p : neighbourCore e N →* N.levi K) (hp : Function.Surjective p)
    (hker : p.ker ≤ center (neighbourCore e N)) (hodd : Odd (Nat.card p.ker)) :
    Nonempty (FieldNeighbourCover σ e N) := by
  obtain ⟨p', hp's, hp'ker, hp'odd, hp'fix⟩ := exists_normalized_of_surjective hσ N
    (le_normalizer_neighbourCore e htL N) ht2 hfix p hp hker hodd
  exact ⟨⟨p', hp's, hp'ker.le, hp'odd, hp'fix⟩⟩

end Normalize

section Input


theorem e6FieldCoverInput_holds : E6FieldCoverInput := by
  intro G _ _ L K₂ _ _ _ σ f hq hf e t hw hk
  have := F4Pilot.finite_of_natCard_eq_two_pow hw.card_eq
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hw.card_eq
  obtain ⟨p₀, hp₀s, hp₀ker, hp₀odd⟩ :=
    exists_surjective_neighbourCore_high_of_rootFieldKind hw hf e hk K₂ hq.card_eq
  set φ : a5Levi K₂ ≃* E6Neighbour.high.levi K₂ :=
    MulEquiv.subgroupCongr (E6Neighbour.levi_high K₂).symm with hφ
  set p : neighbourCore e .high →* E6Neighbour.high.levi K₂ := φ.toMonoidHom.comp p₀ with hp
  have hpker : p.ker = p₀.ker := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hp, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  exact nonempty_fieldNeighbourCover_of_surjective hq.orderOf_eq .high hw.mem_centralizer
    hw.orderOf_eq (perfectCore_neighbourCore_high_inf_centralizer hw hf e) p
    (φ.surjective.comp hp₀s) (hpker ▸ hp₀ker) (hpker ▸ hp₀odd)

end Input

end CFSG.SeitzReduction.E6Pilot
