module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotFieldNormalizeTorus
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignLevi
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignCores
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6Hom

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore)

local instance e6PilotFieldNormalizeNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section BaseChange

variable {k K : Type} [Field k] [Field K]

theorem baseChangeGL_mem_map_levi (ι : k →+* K) (N : E6Neighbour) {g : ModGL .E6 k}
    (hg : g ∈ (N.levi k).map (adjointGroup .E6 k).subtype) :
    baseChangeGL ι g ∈ (N.levi K).map (adjointGroup .E6 K).subtype := by
  rw [map_subtype_levi] at hg ⊢
  exact F4Pilot.map_rootSpan_baseChangeGL_le ι _ ⟨g, hg, rfl⟩

theorem baseChangeGL_mem_torus (ι : k →+* K) (N : E6Neighbour) {d : ModGL .E6 k}
    (hd : d ∈ N.torus k) : baseChangeGL ι d ∈ N.torus K := by
  obtain ⟨c, rfl⟩ := mem_corootLine.1 hd
  rw [F4Pilot.baseChangeGL_rootDiagUnit_eq_map, ← corootTuple_unitsMap]
  exact rootDiagUnit_corootTuple_mem_corootLine _ _

@[expose] noncomputable def leviBaseChange (ι : k →+* K) (N : E6Neighbour) :
    N.levi k →* N.levi K :=
  (((baseChangeGL ι).comp ((adjointGroup .E6 k).subtype.comp (N.levi k).subtype)).codRestrict
      (adjointGroup .E6 K) fun g =>
        map_subtype_le _ (baseChangeGL_mem_map_levi ι N ⟨g, g.2, rfl⟩)).codRestrict
    (N.levi K) fun g => mem_levi_of_coe_mem (baseChangeGL_mem_map_levi ι N ⟨g, g.2, rfl⟩)

theorem coe_leviBaseChange (ι : k →+* K) (N : E6Neighbour) (x : N.levi k) :
    (((leviBaseChange ι N x : N.levi K) : adjointGroup .E6 K) : ModGL .E6 K) =
      baseChangeGL ι ((x : adjointGroup .E6 k) : ModGL .E6 k) :=
  rfl

theorem leviBaseChange_injective (ι : k →+* K) (N : E6Neighbour) :
    Function.Injective (leviBaseChange ι N) := fun _ _ h => Subtype.ext (Subtype.ext
  (baseChangeGL_injective ι (congrArg (fun x : N.levi K => ((x : adjointGroup .E6 K) :
    ModGL .E6 K)) h)))

variable (σ : K ≃+* K)

@[expose] noncomputable def leviInclusion (N : E6Neighbour) :
    N.levi (fixSubfield σ) →* N.levi K :=
  leviBaseChange (fixSubfield σ).subtype N

theorem coe_leviInclusion (N : E6Neighbour) (x : N.levi (fixSubfield σ)) :
    (((leviInclusion σ N x : N.levi K) : adjointGroup .E6 K) : ModGL .E6 K) =
      baseChangeGL (fixSubfield σ).subtype ((x : adjointGroup .E6 (fixSubfield σ)) :
        ModGL .E6 (fixSubfield σ)) :=
  rfl

variable {G : Type} [Group G] {L : Subgroup G} (e : L ≃* adjointGroup .E6 (fixSubfield σ))

structure FieldNeighbourIso (N : E6Neighbour) where
  Φ : N.levi K ≃* neighbourCore e N
  fix : ∀ x : N.levi (fixSubfield σ), ((Φ (leviInclusion σ N x) : neighbourCore e N) : G) =
    ((e.symm (x : adjointGroup .E6 (fixSubfield σ)) : L) : G)

end BaseChange

section Equivariance

variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

theorem FieldNeighbourIso.map_conj [Finite K] [CharP K 2] {N : E6Neighbour}
    (h : FieldNeighbourIso σ e N) {d : adjointGroup .E6 (fixSubfield σ)}
    (hd : (d : ModGL .E6 (fixSubfield σ)) ∈ torusGroup .E6 (fixSubfield σ)) {x y : N.levi K}
    (hy : ((y : adjointGroup .E6 K) : ModGL .E6 K) =
      baseChangeGL (fixSubfield σ).subtype (d : ModGL .E6 (fixSubfield σ)) *
        ((x : adjointGroup .E6 K) : ModGL .E6 K) *
          (baseChangeGL (fixSubfield σ).subtype (d : ModGL .E6 (fixSubfield σ)))⁻¹) :
    ((h.Φ y : neighbourCore e N) : G) =
      ((e.symm d : L) : G) * (h.Φ x : G) * ((e.symm d : L) : G)⁻¹ := by
  obtain ⟨d₁, hd₁, d₂, ⟨x₂, hx₂, rfl⟩, he⟩ := exists_eq_mul_of_mem_torusGroup N hd
  simp only [Subgroup.coe_subtype] at he
  have hdd : d = ⟨d₁, N.torus_le_adjointGroup hd₁⟩ * x₂ := Subtype.ext he
  have hι₁ := baseChangeGL_mem_torus (fixSubfield σ).subtype N hd₁
  have hc₁ : ∀ z : N.levi K, Commute (baseChangeGL (fixSubfield σ).subtype d₁)
      ((z : adjointGroup .E6 K) : ModGL .E6 K) := by
    intro z
    have hz : ((z : adjointGroup .E6 K) : ModGL .E6 K) ∈
        (N.levi K).map (adjointGroup .E6 K).subtype := ⟨z, z.2, rfl⟩
    exact mem_centralizer_iff.1 (levi_le_centralizer_torus N hz) _ hι₁
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = leviInclusion σ N ⟨x₂, hx₂⟩ := ⟨_, rfl⟩
  have hξc : ((ξ : adjointGroup .E6 K) : ModGL .E6 K) =
      baseChangeGL (fixSubfield σ).subtype (x₂ : ModGL .E6 (fixSubfield σ)) := by
    rw [hξ]
    rfl
  have hy' : y = ξ * x * ξ⁻¹ := by
    refine Subtype.ext (Subtype.ext ?_)
    show ((y : adjointGroup .E6 K) : ModGL .E6 K) = ((ξ : adjointGroup .E6 K) : ModGL .E6 K) *
      ((x : adjointGroup .E6 K) : ModGL .E6 K) * (((ξ : adjointGroup .E6 K) : ModGL .E6 K))⁻¹
    have hcomm := ((hc₁ ξ).mul_right (hc₁ x)).mul_right (hc₁ ξ).inv_right
    rw [hy, he, map_mul, ← hξc]
    calc baseChangeGL (fixSubfield σ).subtype d₁ * ((ξ : adjointGroup .E6 K) : ModGL .E6 K) *
          ((x : adjointGroup .E6 K) : ModGL .E6 K) *
            (baseChangeGL (fixSubfield σ).subtype d₁ *
              ((ξ : adjointGroup .E6 K) : ModGL .E6 K))⁻¹ =
        baseChangeGL (fixSubfield σ).subtype d₁ * (((ξ : adjointGroup .E6 K) : ModGL .E6 K) *
          ((x : adjointGroup .E6 K) : ModGL .E6 K) * (((ξ : adjointGroup .E6 K) :
            ModGL .E6 K))⁻¹) * (baseChangeGL (fixSubfield σ).subtype d₁)⁻¹ := by group
      _ = _ := by rw [hcomm.eq, mul_inv_cancel_right]
  have hd₁G := symm_mem_modelToG e (x := ⟨d₁, N.torus_le_adjointGroup hd₁⟩) hd₁
  have hc₂ : ∀ z : neighbourCore e N, Commute
      ((e.symm ⟨d₁, N.torus_le_adjointGroup hd₁⟩ : L) : G) (z : G) := by
    intro z
    exact mem_centralizer_iff.1 (F4Pilot.centralizerPerfectCore_le_centralizer _ z.2) _ hd₁G
  have hfix : ((h.Φ ξ : neighbourCore e N) : G) = ((e.symm x₂ : L) : G) := by
    rw [hξ]
    exact h.fix ⟨x₂, hx₂⟩
  have hΦy : ((h.Φ y : neighbourCore e N) : G) =
      ((e.symm x₂ : L) : G) * (h.Φ x : G) * ((e.symm x₂ : L) : G)⁻¹ := by
    rw [hy', map_mul, map_mul, map_inv, coe_mul, coe_mul, coe_inv, hfix]
  have hcomm := ((hc₂ (h.Φ ξ)).mul_right (hc₂ (h.Φ x))).mul_right (hc₂ (h.Φ ξ)).inv_right
  rw [hfix] at hcomm
  rw [hΦy, hdd, map_mul, L.coe_mul]
  calc ((e.symm x₂ : L) : G) * (h.Φ x : G) * ((e.symm x₂ : L) : G)⁻¹ =
      ((e.symm ⟨d₁, N.torus_le_adjointGroup hd₁⟩ : L) : G) * (((e.symm x₂ : L) : G) *
        (h.Φ x : G) * ((e.symm x₂ : L) : G)⁻¹) *
          ((e.symm ⟨d₁, N.torus_le_adjointGroup hd₁⟩ : L) : G)⁻¹ := by
        rw [hcomm.eq, mul_inv_cancel_right]
    _ = _ := by group

theorem baseChangeGL_conj_mem_map_levi {k : Type} [Field k] [Finite k] [CharP k 2]
    (ι : k →+* K) (N : E6Neighbour) {d : ModGL .E6 k} (hd : d ∈ torusGroup .E6 k)
    {g : ModGL .E6 K} (hg : g ∈ (N.levi K).map (adjointGroup .E6 K).subtype) :
    baseChangeGL ι d * g * (baseChangeGL ι d)⁻¹ ∈ (N.levi K).map (adjointGroup .E6 K).subtype := by
  obtain ⟨d₁, hd₁, d₂, hd₂, he⟩ := exists_eq_mul_of_mem_torusGroup N hd
  have hι₁ := baseChangeGL_mem_torus ι N hd₁
  have hι₂ := baseChangeGL_mem_map_levi ι N hd₂
  have hc : Commute (baseChangeGL ι d₁) (baseChangeGL ι d₂ * g * (baseChangeGL ι d₂)⁻¹) :=
    mem_centralizer_iff.1 (levi_le_centralizer_torus N
      (mul_mem (mul_mem hι₂ hg) (inv_mem hι₂))) _ hι₁
  have h1 : baseChangeGL ι d * g * (baseChangeGL ι d)⁻¹ =
      baseChangeGL ι d₂ * g * (baseChangeGL ι d₂)⁻¹ := by
    rw [he, map_mul]
    calc baseChangeGL ι d₁ * baseChangeGL ι d₂ * g * (baseChangeGL ι d₁ * baseChangeGL ι d₂)⁻¹ =
        baseChangeGL ι d₁ * (baseChangeGL ι d₂ * g * (baseChangeGL ι d₂)⁻¹) *
          (baseChangeGL ι d₁)⁻¹ := by group
      _ = _ := by rw [hc.eq, mul_inv_cancel_right]
  rw [h1]
  exact mul_mem (mul_mem hι₂ hg) (inv_mem hι₂)

theorem FieldNeighbourIso.commute_iff [Finite K] [CharP K 2] {N : E6Neighbour}
    (h : FieldNeighbourIso σ e N) {d : adjointGroup .E6 (fixSubfield σ)}
    (hd : (d : ModGL .E6 (fixSubfield σ)) ∈ torusGroup .E6 (fixSubfield σ)) (x : N.levi K) :
    Commute ((h.Φ x : neighbourCore e N) : G) ((e.symm d : L) : G) ↔
      Commute ((x : adjointGroup .E6 K) : ModGL .E6 K)
        (baseChangeGL (fixSubfield σ).subtype (d : ModGL .E6 (fixSubfield σ))) := by
  have hmem := baseChangeGL_conj_mem_map_levi (fixSubfield σ).subtype N hd
    (g := ((x : adjointGroup .E6 K) : ModGL .E6 K)) ⟨x, x.2, rfl⟩
  obtain ⟨y₀, hy₀, hy₀e⟩ := hmem
  set y : N.levi K := ⟨y₀, hy₀⟩ with hydef
  have hy : ((y : adjointGroup .E6 K) : ModGL .E6 K) =
      baseChangeGL (fixSubfield σ).subtype (d : ModGL .E6 (fixSubfield σ)) *
        ((x : adjointGroup .E6 K) : ModGL .E6 K) *
          (baseChangeGL (fixSubfield σ).subtype (d : ModGL .E6 (fixSubfield σ)))⁻¹ := hy₀e
  have hΦ := h.map_conj hd hy
  constructor
  · intro hc
    have h1 : ((h.Φ y : neighbourCore e N) : G) = (h.Φ x : G) := by
      rw [hΦ, ← hc.eq, mul_inv_cancel_right]
    have h2 : y = x := h.Φ.injective (Subtype.ext h1)
    have h3 : ((y : adjointGroup .E6 K) : ModGL .E6 K) = ((x : adjointGroup .E6 K) : ModGL .E6 K) :=
      by rw [h2]
    rw [hy, mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  · intro hc
    have h1 : y = x := by
      refine Subtype.ext (Subtype.ext ?_)
      show ((y : adjointGroup .E6 K) : ModGL .E6 K) = ((x : adjointGroup .E6 K) : ModGL .E6 K)
      rw [hy, ← hc.eq, mul_inv_cancel_right]
    rw [h1] at hΦ
    have h2 : ((e.symm d : L) : G) * (h.Φ x : G) = (h.Φ x : G) * ((e.symm d : L) : G) := by
      calc ((e.symm d : L) : G) * (h.Φ x : G) =
          ((e.symm d : L) : G) * (h.Φ x : G) * ((e.symm d : L) : G)⁻¹ *
            ((e.symm d : L) : G) := by group
        _ = _ := by rw [← hΦ]
    exact h2.symm

theorem FieldNeighbourIso.commute_iff_of_mem_leviTorus
    [Finite K] [CharP K 2]
    {N : E6Neighbour} (h : FieldNeighbourIso σ e N) {J : Finset (Fin (Tag.rank .E6))}
    {d : adjointGroup .E6 (fixSubfield σ)}
    (hd : (d : ModGL .E6 (fixSubfield σ)) ∈ leviTorus (fixSubfield σ) J) (x : N.levi K) :
    Commute ((h.Φ x : neighbourCore e N) : G) ((e.symm d : L) : G) ↔
      Commute ((x : adjointGroup .E6 K) : ModGL .E6 K)
        (baseChangeGL (fixSubfield σ).subtype (d : ModGL .E6 (fixSubfield σ))) :=
  h.commute_iff (leviTorus_inf_adjointGroup_le_torusGroup J ⟨hd, d.2⟩) x

end Equivariance

end CFSG.SeitzReduction.E6Pilot
