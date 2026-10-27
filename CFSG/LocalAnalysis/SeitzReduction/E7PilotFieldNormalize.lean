module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotAlignLevi
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotAlignCores
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourLevi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6Hom

public section

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore)
open E6Pilot (modelToG mem_modelToG symm_mem_modelToG modelToG_commutator)
open scoped Pointwise

local instance e7PilotFieldNormalizeNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

section Perfect

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem commutator_rootSpan_perpRoots_eq_of_charTwo :
    ⁅rootSpan .E7 K (EPilot.perpRoots .E7), rootSpan .E7 K (EPilot.perpRoots .E7)⁆ =
      rootSpan .E7 K (EPilot.perpRoots .E7) := by
  have h0 : ⁅(⊤ : Subgroup (EPilot.perpLevi .E7 K)), ⊤⁆ = ⊤ :=
    (isQuasisimple_perpLevi_E7 (K := K)).1.commutator_eq_top
  have h := congrArg (fun H : Subgroup (EPilot.perpLevi .E7 K) =>
    (H.map (EPilot.perpLevi .E7 K).subtype).map (adjointGroup .E7 K).subtype) h0
  simp only [Subgroup.map_commutator] at h
  rwa [← MonoidHom.range_eq_map, range_subtype, map_subtype_perpLevi_E7] at h

theorem commutator_rootSpan_orthRoots_eq_of_charTwo (N : E7Neighbour) :
    ⁅rootSpan .E7 K (orthRoots N.root), rootSpan .E7 K (orthRoots N.root)⁆ =
      rootSpan .E7 K (orthRoots N.root) := by
  have h := congrArg (fun H => H.map (MulAut.conj (N.rep K : ModGL .E7 K)).toMonoidHom)
    (commutator_rootSpan_perpRoots_eq_of_charTwo (K := K))
  simp only [Subgroup.map_commutator] at h
  rwa [perpRoots_eq_orthRoots, map_conj_rep_rootSpan N (fun γ hγ => hγ.1),
    image_weyl_orthRoots_highRoot] at h

variable {G : Type} [Group G] {L : Subgroup G} (e : L ≃* adjointGroup .E7 K)

theorem modelToG_rootSpan_orthRoots_le_neighbourCore_all (N : E7Neighbour) :
    modelToG e (rootSpan .E7 K (orthRoots N.root)) ≤ neighbourCore e N :=
  modelToG_rootSpan_orthRoots_le_neighbourCore e N (commutator_rootSpan_orthRoots_eq_of_charTwo N)

theorem modelToG_rootSpan_perpRoots_le_neighbourCore_high :
    modelToG e (rootSpan .E7 K (EPilot.perpRoots .E7)) ≤ neighbourCore e .high := by
  rw [perpRoots_eq_orthRoots]
  exact modelToG_rootSpan_orthRoots_le_neighbourCore_all e .high

end Perfect

section Neighbour

variable {K : Type} [Field K]

theorem map_subtype_levi
    (N : E7Neighbour) :
    (N.levi K).map (adjointGroup .E7 K).subtype = rootSpan .E7 K (orthRoots N.root) := by
  rw [E7Neighbour.levi, subgroupOf_map_subtype,
    inf_of_le_left (EPilot.rootSpan_le_adjointGroup' _)]

theorem mem_levi_of_coe_mem
    {N : E7Neighbour} {g : adjointGroup .E7 K}
    (h : (g : ModGL .E7 K) ∈ (N.levi K).map (adjointGroup .E7 K).subtype) : g ∈ N.levi K := by
  obtain ⟨y, hy, hyg⟩ := h
  rwa [show y = g from Subtype.ext hyg] at hy

theorem levi_le_centralizer_torus (N : E7Neighbour) :
    (N.levi K).map (adjointGroup .E7 K).subtype ≤
      centralizer (N.torus K : Set (ModGL .E7 K)) := by
  rw [map_subtype_levi]
  exact rootSpan_orthRoots_le_centralizer_torus N

theorem coe_torus_sup_eq_mul (N : E7Neighbour) :
    ((N.torus K ⊔ rootSpan .E7 K (orthRoots N.root) : Subgroup (ModGL .E7 K)) :
        Set (ModGL .E7 K)) =
      (N.torus K : Set (ModGL .E7 K)) * (rootSpan .E7 K (orthRoots N.root) : Set (ModGL .E7 K)) :=
  Subgroup.coe_mul_of_left_le_normalizer_right _ _
    ((le_centralizer_iff.1 (rootSpan_orthRoots_le_centralizer_torus N)).trans
      (centralizer_le_normalizer _))

end Neighbour

section Decomp

variable {k : Type} [Field k]

theorem coe_rep_mem_monomialSubgroup (N : E7Neighbour) :
    (N.rep k : ModGL .E7 k) ∈ monomialSubgroup .E7 k := by
  rw [E7Neighbour.coe_rep]
  refine Subgroup.mem_sup_right (list_prod_mem fun x hx => ?_)
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨i, rfl⟩

theorem rep_inv_mul_mul_rep_mem_torusGroup (N : E7Neighbour)
    {h : ModGL .E7 k} (hh : h ∈ torusGroup .E7 k) :
    (N.rep k : ModGL .E7 k)⁻¹ * h * (N.rep k : ModGL .E7 k) ∈ torusGroup .E7 k := by
  have hnorm := (triangular_borel_structure.{0, 0} .E7 k).2.2.2.2.2.2.2.2.2.2.1
  have hnM := coe_rep_mem_monomialSubgroup (k := k) N
  have h1 := hnorm.conj_mem ⟨h, Subgroup.mem_sup_left hh⟩ (mem_subgroupOf.2 hh)
    (⟨_, hnM⟩ : monomialSubgroup .E7 k)⁻¹
  rw [mem_subgroupOf] at h1
  simpa only [inv_inv, Subgroup.coe_mul, Subgroup.coe_inv] using h1

theorem exists_eq_mul_of_mem_torusGroup [Finite k] [CharP k 2]
    (N : E7Neighbour) {h : ModGL .E7 k} (hh : h ∈ torusGroup .E7 k) :
    ∃ d₁ ∈ N.torus k, ∃ d₂ ∈ (N.levi k).map (adjointGroup .E7 k).subtype, h = d₁ * d₂ := by
  have hsq : ∀ t : kˣ, ∃ v : kˣ, v ^ 2 = t :=
    F4Pilot.exists_sq_eq_of_ringChar_eq_two (ringChar.eq k 2)
  have hhigh : ∀ h' ∈ torusGroup .E7 k, ∃ d₁ ∈ E7Neighbour.high.torus k,
      ∃ d₂ ∈ rootSpan .E7 k (orthRoots (highRoot .E7)), h' = d₁ * d₂ := by
    intro h' hh'
    have h1 := EPilot.torusGroup_le_highTorusLine_sup (Or.inr (Or.inl rfl)) hsq hh'
    rw [perpRoots_eq_orthRoots, ← E7Neighbour.torus_high] at h1
    have h2 : h' ∈ ((E7Neighbour.high.torus k ⊔ rootSpan .E7 k (orthRoots (highRoot .E7)) :
        Subgroup (ModGL .E7 k)) : Set (ModGL .E7 k)) := h1
    rw [show highRoot .E7 = E7Neighbour.high.root from rfl, coe_torus_sup_eq_mul] at h2
    obtain ⟨d₁, hd₁, d₂, hd₂, he⟩ := h2
    exact ⟨d₁, hd₁, d₂, hd₂, he.symm⟩
  set n : ModGL .E7 k := (N.rep k : ModGL .E7 k) with hn
  obtain ⟨d₁, hd₁, d₂, hd₂, he⟩ := hhigh _ (rep_inv_mul_mul_rep_mem_torusGroup N hh)
  refine ⟨n * d₁ * n⁻¹, ?_, n * d₂ * n⁻¹, ?_, ?_⟩
  · rw [← E7Neighbour.map_conj_rep_torus_high N]
    exact ⟨d₁, hd₁, rfl⟩
  · rw [map_subtype_levi, ← image_weyl_orthRoots_highRoot N,
      ← map_conj_rep_rootSpan N fun γ hγ => hγ.1]
    exact ⟨d₂, hd₂, rfl⟩
  · have h1 : h = n * (n⁻¹ * h * n) * n⁻¹ := by group
    rw [h1, he]
    group

end Decomp

section BaseChange

variable {k K : Type} [Field k] [Field K]

theorem baseChangeGL_mem_map_levi (ι : k →+* K) (N : E7Neighbour) {g : ModGL .E7 k}
    (hg : g ∈ (N.levi k).map (adjointGroup .E7 k).subtype) :
    baseChangeGL ι g ∈ (N.levi K).map (adjointGroup .E7 K).subtype := by
  rw [map_subtype_levi] at hg ⊢
  exact F4Pilot.map_rootSpan_baseChangeGL_le ι _ ⟨g, hg, rfl⟩

theorem baseChangeGL_mem_torus (ι : k →+* K) (N : E7Neighbour) {d : ModGL .E7 k}
    (hd : d ∈ N.torus k) : baseChangeGL ι d ∈ N.torus K := by
  obtain ⟨c, rfl⟩ := mem_corootLine.1 hd
  rw [F4Pilot.baseChangeGL_rootDiagUnit_eq_map, ← corootTuple_unitsMap]
  exact rootDiagUnit_corootTuple_mem_corootLine _ _

@[expose] noncomputable def leviBaseChange (ι : k →+* K) (N : E7Neighbour) :
    N.levi k →* N.levi K :=
  (((baseChangeGL ι).comp ((adjointGroup .E7 k).subtype.comp (N.levi k).subtype)).codRestrict
      (adjointGroup .E7 K) fun g =>
        map_subtype_le _ (baseChangeGL_mem_map_levi ι N ⟨g, g.2, rfl⟩)).codRestrict
    (N.levi K) fun g => mem_levi_of_coe_mem (baseChangeGL_mem_map_levi ι N ⟨g, g.2, rfl⟩)

theorem coe_leviBaseChange (ι : k →+* K) (N : E7Neighbour) (x : N.levi k) :
    (((leviBaseChange ι N x : N.levi K) : adjointGroup .E7 K) : ModGL .E7 K) =
      baseChangeGL ι ((x : adjointGroup .E7 k) : ModGL .E7 k) :=
  rfl

theorem leviBaseChange_injective (ι : k →+* K) (N : E7Neighbour) :
    Function.Injective (leviBaseChange ι N) := fun _ _ h => Subtype.ext (Subtype.ext
  (baseChangeGL_injective ι (congrArg (fun x : N.levi K => ((x : adjointGroup .E7 K) :
    ModGL .E7 K)) h)))

variable (σ : K ≃+* K)

@[expose] noncomputable def leviInclusion (N : E7Neighbour) :
    N.levi (fixSubfield σ) →* N.levi K :=
  leviBaseChange (fixSubfield σ).subtype N

theorem coe_leviInclusion (N : E7Neighbour) (x : N.levi (fixSubfield σ)) :
    (((leviInclusion σ N x : N.levi K) : adjointGroup .E7 K) : ModGL .E7 K) =
      baseChangeGL (fixSubfield σ).subtype ((x : adjointGroup .E7 (fixSubfield σ)) :
        ModGL .E7 (fixSubfield σ)) :=
  rfl

variable {G : Type} [Group G] {L : Subgroup G} (e : L ≃* adjointGroup .E7 (fixSubfield σ))

structure FieldNeighbourIso (N : E7Neighbour) where
  Φ : N.levi K ≃* neighbourCore e N
  fix : ∀ x : N.levi (fixSubfield σ), ((Φ (leviInclusion σ N x) : neighbourCore e N) : G) =
    ((e.symm (x : adjointGroup .E7 (fixSubfield σ)) : L) : G)

end BaseChange

section Equivariance

variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E7 (fixSubfield σ)}

theorem FieldNeighbourIso.map_conj [Finite K] [CharP K 2] {N : E7Neighbour}
    (h : FieldNeighbourIso σ e N) {d : adjointGroup .E7 (fixSubfield σ)}
    (hd : (d : ModGL .E7 (fixSubfield σ)) ∈ torusGroup .E7 (fixSubfield σ)) {x y : N.levi K}
    (hy : ((y : adjointGroup .E7 K) : ModGL .E7 K) =
      baseChangeGL (fixSubfield σ).subtype (d : ModGL .E7 (fixSubfield σ)) *
        ((x : adjointGroup .E7 K) : ModGL .E7 K) *
          (baseChangeGL (fixSubfield σ).subtype (d : ModGL .E7 (fixSubfield σ)))⁻¹) :
    ((h.Φ y : neighbourCore e N) : G) =
      ((e.symm d : L) : G) * (h.Φ x : G) * ((e.symm d : L) : G)⁻¹ := by
  obtain ⟨d₁, hd₁, d₂, ⟨x₂, hx₂, rfl⟩, he⟩ := exists_eq_mul_of_mem_torusGroup N hd
  simp only [Subgroup.coe_subtype] at he
  have hdd : d = ⟨d₁, N.torus_le_adjointGroup hd₁⟩ * x₂ := Subtype.ext he
  have hι₁ := baseChangeGL_mem_torus (fixSubfield σ).subtype N hd₁
  have hc₁ : ∀ z : N.levi K, Commute (baseChangeGL (fixSubfield σ).subtype d₁)
      ((z : adjointGroup .E7 K) : ModGL .E7 K) := by
    intro z
    have hz : ((z : adjointGroup .E7 K) : ModGL .E7 K) ∈
        (N.levi K).map (adjointGroup .E7 K).subtype := ⟨z, z.2, rfl⟩
    exact mem_centralizer_iff.1 (levi_le_centralizer_torus N hz) _ hι₁
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = leviInclusion σ N ⟨x₂, hx₂⟩ := ⟨_, rfl⟩
  have hξc : ((ξ : adjointGroup .E7 K) : ModGL .E7 K) =
      baseChangeGL (fixSubfield σ).subtype (x₂ : ModGL .E7 (fixSubfield σ)) := by
    rw [hξ]
    rfl
  have hy' : y = ξ * x * ξ⁻¹ := by
    refine Subtype.ext (Subtype.ext ?_)
    show ((y : adjointGroup .E7 K) : ModGL .E7 K) = ((ξ : adjointGroup .E7 K) : ModGL .E7 K) *
      ((x : adjointGroup .E7 K) : ModGL .E7 K) * (((ξ : adjointGroup .E7 K) : ModGL .E7 K))⁻¹
    have hcomm := ((hc₁ ξ).mul_right (hc₁ x)).mul_right (hc₁ ξ).inv_right
    rw [hy, he, map_mul, ← hξc]
    calc baseChangeGL (fixSubfield σ).subtype d₁ * ((ξ : adjointGroup .E7 K) : ModGL .E7 K) *
          ((x : adjointGroup .E7 K) : ModGL .E7 K) *
            (baseChangeGL (fixSubfield σ).subtype d₁ *
              ((ξ : adjointGroup .E7 K) : ModGL .E7 K))⁻¹ =
        baseChangeGL (fixSubfield σ).subtype d₁ * (((ξ : adjointGroup .E7 K) : ModGL .E7 K) *
          ((x : adjointGroup .E7 K) : ModGL .E7 K) * (((ξ : adjointGroup .E7 K) :
            ModGL .E7 K))⁻¹) * (baseChangeGL (fixSubfield σ).subtype d₁)⁻¹ := by group
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
    (ι : k →+* K) (N : E7Neighbour) {d : ModGL .E7 k} (hd : d ∈ torusGroup .E7 k)
    {g : ModGL .E7 K} (hg : g ∈ (N.levi K).map (adjointGroup .E7 K).subtype) :
    baseChangeGL ι d * g * (baseChangeGL ι d)⁻¹ ∈ (N.levi K).map (adjointGroup .E7 K).subtype := by
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

theorem FieldNeighbourIso.commute_iff [Finite K] [CharP K 2] {N : E7Neighbour}
    (h : FieldNeighbourIso σ e N) {d : adjointGroup .E7 (fixSubfield σ)}
    (hd : (d : ModGL .E7 (fixSubfield σ)) ∈ torusGroup .E7 (fixSubfield σ)) (x : N.levi K) :
    Commute ((h.Φ x : neighbourCore e N) : G) ((e.symm d : L) : G) ↔
      Commute ((x : adjointGroup .E7 K) : ModGL .E7 K)
        (baseChangeGL (fixSubfield σ).subtype (d : ModGL .E7 (fixSubfield σ))) := by
  have hmem := baseChangeGL_conj_mem_map_levi (fixSubfield σ).subtype N hd
    (g := ((x : adjointGroup .E7 K) : ModGL .E7 K)) ⟨x, x.2, rfl⟩
  obtain ⟨y₀, hy₀, hy₀e⟩ := hmem
  set y : N.levi K := ⟨y₀, hy₀⟩ with hydef
  have hy : ((y : adjointGroup .E7 K) : ModGL .E7 K) =
      baseChangeGL (fixSubfield σ).subtype (d : ModGL .E7 (fixSubfield σ)) *
        ((x : adjointGroup .E7 K) : ModGL .E7 K) *
          (baseChangeGL (fixSubfield σ).subtype (d : ModGL .E7 (fixSubfield σ)))⁻¹ := hy₀e
  have hΦ := h.map_conj hd hy
  constructor
  · intro hc
    have h1 : ((h.Φ y : neighbourCore e N) : G) = (h.Φ x : G) := by
      rw [hΦ, ← hc.eq, mul_inv_cancel_right]
    have h2 : y = x := h.Φ.injective (Subtype.ext h1)
    have h3 : ((y : adjointGroup .E7 K) : ModGL .E7 K) = ((x : adjointGroup .E7 K) : ModGL .E7 K) :=
      by rw [h2]
    rw [hy, mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  · intro hc
    have h1 : y = x := by
      refine Subtype.ext (Subtype.ext ?_)
      show ((y : adjointGroup .E7 K) : ModGL .E7 K) = ((x : adjointGroup .E7 K) : ModGL .E7 K)
      rw [hy, ← hc.eq, mul_inv_cancel_right]
    rw [h1] at hΦ
    have h2 : ((e.symm d : L) : G) * (h.Φ x : G) = (h.Φ x : G) * ((e.symm d : L) : G) := by
      calc ((e.symm d : L) : G) * (h.Φ x : G) =
          ((e.symm d : L) : G) * (h.Φ x : G) * ((e.symm d : L) : G)⁻¹ *
            ((e.symm d : L) : G) := by group
        _ = _ := by rw [← hΦ]
    exact h2.symm

theorem FieldNeighbourIso.commute_iff_of_mem_leviTorus [Finite K] [CharP K 2]
    {N : E7Neighbour} (h : FieldNeighbourIso σ e N) {J : Finset (Fin (Tag.rank .E7))}
    {d : adjointGroup .E7 (fixSubfield σ)}
    (hd : (d : ModGL .E7 (fixSubfield σ)) ∈ leviTorus (fixSubfield σ) J) (x : N.levi K) :
    Commute ((h.Φ x : neighbourCore e N) : G) ((e.symm d : L) : G) ↔
      Commute ((x : adjointGroup .E7 K) : ModGL .E7 K)
        (baseChangeGL (fixSubfield σ).subtype (d : ModGL .E7 (fixSubfield σ))) :=
  h.commute_iff (leviTorus_le_torusGroup_of_ringChar_eq_two (ringChar.eq _ 2) J hd) x

end Equivariance

end CFSG.SeitzReduction.E7Pilot
