module

public import CFSG.GH74.GLS.Stage2.Final.LayerLift

public section

namespace CFSG.GH74.GLS.Stage2.Final.LayerLiftN

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
open CFSG.GH74.GLS.Stage2.Final.LayerLift
open scoped commutatorElement

section General

variable {X : Type*} [Group X]

omit [Group X] in
theorem map_subtype_top' {X : Type*} [Group X] (L : Subgroup X) : (⊤ : Subgroup ↥L).map L.subtype = L := by
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem commutator_isSubnormal {L : Subgroup X} (hL : L.IsSubnormal) : ⁅L, L⁆.IsSubnormal := by
  have hle : ⁅L, L⁆ ≤ L := commutator_le_self L
  refine Subgroup.IsSubnormal.trans hle ?_ hL
  have h : ⁅L, L⁆.subgroupOf L = commutator ↥L := by
    have h1 : (commutator ↥L).map L.subtype = ⁅L, L⁆ := by
      rw [commutator_def, Subgroup.map_commutator, map_subtype_top']
    rw [← h1]
    show Subgroup.comap L.subtype _ = _
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  rw [h]
  exact Subgroup.Normal.isSubnormal inferInstance

end General

section Perfect

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem isPerfect_of_isPComponent {L : Subgroup X} (hL : IsPComponent 2 L) : ⁅L, L⁆ = L := by
  obtain ⟨Kc, hKc, hsub, hmap, hmin⟩ := hL
  have hle : ⁅L, L⁆ ≤ L := commutator_le_self L
  by_contra hne
  have hlt : ⁅L, L⁆ < L := lt_of_le_of_ne hle hne
  have hmapc : (⁅L, L⁆).map (QuotientGroup.mk' (pPrimeCore 2 X)) = Kc := by
    rw [Subgroup.map_commutator, hmap]
    exact Subgroup.isPerfect_iff.mp hKc.1.1
  exact hmin _ hlt (commutator_isSubnormal hsub) hmapc

end Perfect


section Comm

theorem commutatorElement_mul_right_of_commute {G : Type*} [Group G] {x y n : G} (hn : Commute n y) :
    ⁅x * n, y⁆ = ⁅x, y⁆ := by
  simp only [commutatorElement_def, mul_inv_rev]
  calc x * n * y * (n⁻¹ * x⁻¹) * y⁻¹ = x * (n * y) * n⁻¹ * x⁻¹ * y⁻¹ := by group
    _ = x * (y * n) * n⁻¹ * x⁻¹ * y⁻¹ := by rw [hn.eq]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem commutatorElement_mul_left_of_commute {G : Type*} [Group G] {x y n : G} (hn : Commute n x) :
    ⁅x, y * n⁆ = ⁅x, y⁆ := by
  simp only [commutatorElement_def, mul_inv_rev]
  calc x * (y * n) * x⁻¹ * (n⁻¹ * y⁻¹) = x * y * (n * x⁻¹) * n⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * n) * n⁻¹ * y⁻¹ := by rw [hn.inv_right.eq]
    _ = x * y * x⁻¹ * y⁻¹ := by group

end Comm

section Cyc

variable {X : Type*} [Group X] (N : Subgroup X) [N.Normal] [IsCyclic ↥N]

theorem isComponent_map_of_cyclic {J : Subgroup X} (hJ : IsComponent J) :
    IsComponent (J.map (QuotientGroup.mk' N)) := by
  have hnot : ¬ J ≤ (QuotientGroup.mk' N).ker := by
    rw [QuotientGroup.ker_mk']
    intro hle
    have hsolvN : Group.IsSolvable ↥N := inferInstance
    have hsolvJ : Group.IsSolvable ↥J :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    have := CFSG.LocalCores.isQuasisimple_nontrivial hJ.1
    have := hJ.1.1
    exact Group.IsPerfect.not_isSolvable ↥J hsolvJ
  exact ⟨CFSG.LocalCores.isQuasisimple_map hJ.1 _ hnot, hJ.2.map (QuotientGroup.mk'_surjective _)⟩

end Cyc

section TwoComp

variable {X : Type*} [Group X] [IsCyclic ↥(pPrimeCore 2 X)]

theorem isQuasisimple_of_isPComponent_cyclic {L : Subgroup X} (hL : IsPComponent 2 L) : IsQuasisimple ↥L := by
  have hperf : ⁅L, L⁆ = L := isPerfect_of_isPComponent hL
  obtain ⟨Kc, hKc, hsub, hmap, -⟩ := hL
  let π : X →* X ⧸ pPrimeCore 2 X := QuotientGroup.mk' (pPrimeCore 2 X)
  let φ : ↥L →* ↥Kc := (π.comp L.subtype).codRestrict Kc fun l => by
    rw [← hmap]
    exact ⟨l, l.2, rfl⟩
  have hφ : Function.Surjective φ := by
    intro k
    have hk : (k : X ⧸ pPrimeCore 2 X) ∈ L.map π := by
      rw [hmap]
      exact k.2
    obtain ⟨c, hc, hck⟩ := hk
    exact ⟨⟨c, hc⟩, Subtype.ext hck⟩
  have hperfq : ⁅L.map π, L.map π⁆ = L.map π := by
    rw [hmap]
    exact Subgroup.isPerfect_iff.mp hKc.1.1
  have hker : φ.ker ≤ center ↥L := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 : π (x : X) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hxN : (x : X) ∈ pPrimeCore 2 X := (QuotientGroup.eq_one_iff _).mp h1
    exact Subtype.ext (centralizes_of_perfect_quotient (pPrimeCore 2 X) L hperfq y.2 hxN)
  have hLperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
  exact (CFSG.LocalCores.isQuasisimple_iff_of_surjective hLperf φ hφ hker).mpr hKc.1

theorem isComponent_of_isPComponent_cyclic {L : Subgroup X} (hL : IsPComponent 2 L) : IsComponent L :=
  ⟨isQuasisimple_of_isPComponent_cyclic hL, hL.choose_spec.2.1⟩

theorem component_le_of_map_eq {J L : Subgroup X} (hJ : IsComponent J) (hL : IsPComponent 2 L)
    (h : J.map (QuotientGroup.mk' (pPrimeCore 2 X)) = L.map (QuotientGroup.mk' (pPrimeCore 2 X))) : J ≤ L := by
  set N := pPrimeCore 2 X with hN
  set π : X →* X ⧸ N := QuotientGroup.mk' N with hπ
  have hKc := hL
  obtain ⟨Kc, hKcq, -, hmap, -⟩ := hKc
  have hLperfq : ⁅L.map π, L.map π⁆ = L.map π := by
    rw [hmap]
    exact Subgroup.isPerfect_iff.mp hKcq.1.1
  have hJperfq : ⁅J.map π, J.map π⁆ = J.map π := by
    rw [h]
    exact hLperfq
  have hJperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJ.1.1
  have hdecomp : ∀ x ∈ J, ∃ l ∈ L, ∃ n ∈ N, x = l * n := by
    intro x hx
    have hx' : π x ∈ L.map π := h ▸ Subgroup.mem_map_of_mem _ hx
    obtain ⟨l, hl, hlx⟩ := hx'
    refine ⟨l, hl, l⁻¹ * x, ?_, by group⟩
    rw [← QuotientGroup.eq]
    exact hlx
  have hcomm : ∀ a ∈ L, ∀ n ∈ N, Commute n a := fun a ha n hn =>
    (centralizes_of_perfect_quotient N L hLperfq ha hn).symm
  have hcommN : ∀ n ∈ N, ∀ m ∈ N, Commute n m := fun n hn m hm =>
    (Subgroup.mem_centralizer_iff.mp (le_centralizer_self_of_cyclic N hn) m hm).symm
  have hle : ⁅J, J⁆ ≤ L := by
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    obtain ⟨l₁, hl₁, n₁, hn₁, rfl⟩ := hdecomp a ha
    obtain ⟨l₂, hl₂, n₂, hn₂, rfl⟩ := hdecomp b hb
    have c1 : Commute n₁ (l₂ * n₂) := (hcomm l₂ hl₂ n₁ hn₁).mul_right (hcommN n₁ hn₁ n₂ hn₂)
    rw [commutatorElement_mul_right_of_commute c1, commutatorElement_mul_left_of_commute (hcomm l₁ hl₁ n₂ hn₂)]
    exact commutator_le_self L (Subgroup.commutator_mem_commutator hl₁ hl₂)
  rw [hJperf] at hle
  exact hle


theorem layer_eq_sup_of_two_components {L₁ L₂ : Subgroup X} (h₁ : IsPComponent 2 L₁) (h₂ : IsPComponent 2 L₂)
    (hne : L₁ ≠ L₂) {M₁ M₂ : Subgroup (X ⧸ pPrimeCore 2 X)}
    (hcomps : {K : Subgroup (X ⧸ pPrimeCore 2 X) | IsComponent K} = {M₁, M₂}) : layer X = L₁ ⊔ L₂ := by
  set N := pPrimeCore 2 X with hN
  set π : X →* X ⧸ N := QuotientGroup.mk' N with hπ
  have q₁ : IsComponent L₁ := isComponent_of_isPComponent_cyclic h₁
  have q₂ : IsComponent L₂ := isComponent_of_isPComponent_cyclic h₂
  have hc₁ : IsComponent (L₁.map π) := by
    obtain ⟨Kc, hKc, -, hmap, -⟩ := h₁
    rw [hmap]
    exact hKc
  have hc₂ : IsComponent (L₂.map π) := by
    obtain ⟨Kc, hKc, -, hmap, -⟩ := h₂
    rw [hmap]
    exact hKc
  have hm₁ : L₁.map π ∈ ({M₁, M₂} : Set (Subgroup (X ⧸ N))) := by rw [← hcomps]; exact hc₁
  have hm₂ : L₂.map π ∈ ({M₁, M₂} : Set (Subgroup (X ⧸ N))) := by rw [← hcomps]; exact hc₂
  have hne' : L₁.map π ≠ L₂.map π := by
    intro h
    exact hne (le_antisymm (component_le_of_map_eq q₁ h₂ h) (component_le_of_map_eq q₂ h₁ h.symm))
  apply le_antisymm
  · refine sSup_le fun J hJ => ?_
    have hJbar : J.map π ∈ ({M₁, M₂} : Set (Subgroup (X ⧸ N))) := by
      rw [← hcomps]
      exact isComponent_map_of_cyclic N hJ
    have hcase : J.map π = L₁.map π ∨ J.map π = L₂.map π := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm₁ hm₂ hJbar
      rcases hm₁ with h1 | h1 <;> rcases hm₂ with h2 | h2 <;> rcases hJbar with h3 | h3
      all_goals first
        | exact absurd (h1.trans h2.symm) hne'
        | exact Or.inl (h3.trans h1.symm)
        | exact Or.inr (h3.trans h2.symm)
    rcases hcase with h | h
    · exact (component_le_of_map_eq hJ h₁ h).trans le_sup_left
    · exact (component_le_of_map_eq hJ h₂ h).trans le_sup_right
  · exact sup_le (CFSG.LocalCores.component_le_layer q₁) (CFSG.LocalCores.component_le_layer q₂)

end TwoComp


section Stage2

variable {G : Type} [Group G] [Finite G]

theorem layerTimesSylow_eq_of_two_components {z : G} {S K₁ K₂ : Subgroup G} (hS : IsPGroup 2 ↥S)
    (hSC : S ≤ Cen z) (hcyc : IsCyclic ↥(pPrimeCore 2 ↥(Cen z)))
    (hK₁ : IsPCompIn 2 (Cen z) K₁) (hK₂ : IsPCompIn 2 (Cen z) K₂) (hne : K₁ ≠ K₂)
    {M₁ M₂ : Subgroup (CentralizerBar z)} (hcomps : {K | IsComponent K} = {M₁, M₂})
    (hEC : (layer ↥(Cen z)).map (Cen z).subtype ⊓ OddCore z = ⊥) :
    layerTimesSylow z S = K₁ ⊔ K₂ ⊔ S ∧ (K₁ ⊔ K₂ ⊔ S) ⊓ OddCore z = ⊥ := by
  haveI := hcyc
  have hne' : K₁.subgroupOf (Cen z) ≠ K₂.subgroupOf (Cen z) := by
    intro h
    apply hne
    have h' := congrArg (Subgroup.map (Cen z).subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hK₁.1, Subgroup.map_subgroupOf_eq_of_le hK₂.1] at h'
  have hlayer : layer ↥(Cen z) = K₁.subgroupOf (Cen z) ⊔ K₂.subgroupOf (Cen z) :=
    layer_eq_sup_of_two_components hK₁.2 hK₂.2 hne' hcomps
  have hE : (layer ↥(Cen z)).map (Cen z).subtype = K₁ ⊔ K₂ := by
    rw [hlayer, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hK₁.1,
      Subgroup.map_subgroupOf_eq_of_le hK₂.1]
  have hLT : layerTimesSylow z S = K₁ ⊔ K₂ ⊔ S := by
    unfold layerTimesSylow
    rw [hE]
  refine ⟨hLT, ?_⟩
  rw [← hLT]
  exact layerTimesSylow_inf_oddCore_eq_bot hS hSC hEC

end Stage2

end CFSG.GH74.GLS.Stage2.Final.LayerLiftN
