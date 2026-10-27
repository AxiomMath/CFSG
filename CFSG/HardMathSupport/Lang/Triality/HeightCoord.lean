module

public import CFSG.LieType.Chevalley.LargeReeAmbientPositiveCentralizer
public import CFSG.LieType.Chevalley.E6GraphInvertedRootRotation

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Lang.Triality

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


variable {τ : Tag} {K : Type} [Field K]

theorem map_heightSeries_le (F : ModGL τ K →* ModGL τ K) (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))
    (hρR : ∀ γ, IsRoot τ γ → IsRoot τ (ρ γ)) (hρh : ∀ γ, height (ρ γ) = height γ)
    (hF : ∀ γ, IsRoot τ γ → ∀ c : K, ∃ d : K, F (pinnedX τ K γ c) = pinnedX τ K (ρ γ) d)
    (h : ℤ) {g : ModGL τ K} (hg : g ∈ heightSeries τ K h) : F g ∈ heightSeries τ K h := by
  have hle : heightSeries τ K h ≤ (heightSeries τ K h).comap F := by
    refine iSup₂_le fun γ hγ => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    obtain ⟨d, hd⟩ := hF γ hγ.1 c
    change F (pinnedX τ K γ c) ∈ heightSeries τ K h
    rw [hd]
    exact pinnedX_mem_rootSpan (S := {γ | IsRoot τ γ ∧ 0 < height γ ∧ h ≤ height γ})
      ⟨hρR γ hγ.1, by rw [hρh]; exact hγ.2.1, by rw [hρh]; exact hγ.2.2⟩ d
  exact hle hg

theorem map_rootSpan_le (F : ModGL τ K →* ModGL τ K) (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))
    (hF : ∀ γ, IsRoot τ γ → ∀ c : K, ∃ d : K, F (pinnedX τ K γ c) = pinnedX τ K (ρ γ) d)
    {S S' : Set (Fin τ.rank → ℤ)} (hS : ∀ γ ∈ S, IsRoot τ γ ∧ ρ γ ∈ S')
    {g : ModGL τ K} (hg : g ∈ rootSpan τ K S) : F g ∈ rootSpan τ K S' := by
  have hle : rootSpan τ K S ≤ (rootSpan τ K S').comap F := by
    refine iSup₂_le fun γ hγ => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    obtain ⟨d, hd⟩ := hF γ (hS γ hγ).1 c
    change F (pinnedX τ K γ c) ∈ rootSpan τ K S'
    rw [hd]
    exact pinnedX_mem_rootSpan (S := S') (hS γ hγ).2 d
  exact hle hg

variable [Finite K]

theorem rootCoord_map (F : ModGL τ K →* ModGL τ K) (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))
    (hρR : ∀ γ, IsRoot τ γ → IsRoot τ (ρ γ)) (hρh : ∀ γ, height (ρ γ) = height γ)
    (hρinj : ∀ γ γ', IsRoot τ γ → IsRoot τ γ' → ρ γ = ρ γ' → γ = γ')
    (hF : ∀ γ, IsRoot τ γ → ∀ c : K, ∃ d : K, F (pinnedX τ K γ c) = pinnedX τ K (ρ γ) d)
    (φ : K →+ K) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α ∧ 0 < height α)
    (hα' : IsRoot τ (ρ α) ∧ 0 < height (ρ α)) (ε : K)
    (hFα : ∀ c : K, F (pinnedX τ K α c) = pinnedX τ K (ρ α) (ε * φ c))
    {g : ModGL τ K} (hg : g ∈ heightSeries τ K (height α)) :
    rootCoord hα' (F g) = ε * φ (rootCoord hα g) := by
  classical
  set c := rootCoord hα g with hc
  have hmk := rootCoordHom_rootCoord hα hg
  rw [rootCoordHom_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hmk
  set n : ModGL τ K := (pinnedX τ K α c)⁻¹ * g with hn
  have hnN : n ∈ rootSpan τ K (coordKerRoots α) := hmk
  have hg_eq : g = pinnedX τ K α c * n := by rw [hn]; group
  have hFn : F n ∈ rootSpan τ K (coordKerRoots (ρ α)) := by
    refine map_rootSpan_le F ρ hF (fun γ hγ => ⟨hγ.1, ?_⟩) hnN
    obtain ⟨hr, hp, hle, hne⟩ := hγ
    refine ⟨hρR γ hr, by rw [hρh]; exact hp, by rw [hρh, hρh]; exact hle, fun h => hne ?_⟩
    exact hρinj γ α hr hα.1 h
  have h1 : pinnedX τ K (ρ α) (ε * φ c) ∈ heightSeries τ K (height (ρ α)) :=
    pinnedX_mem_heightSeries_height hα' _
  have h2 : F n ∈ heightSeries τ K (height (ρ α)) := coordKer_le_heightSeries _ hFn
  rw [hg_eq, map_mul, hFα, rootCoord_mul hα' h1 h2, rootCoord_self hα',
    rootCoord_of_mem_coordKer hα' hFn, add_zero]

theorem rootCoord_twistHom (t : TwistTag) (σ : K →+* K) {α : Fin t.tag.rank → ℤ}
    (hα : IsRoot t.tag α ∧ 0 < height α)
    (hα' : IsRoot t.tag (permLattice t.perm α) ∧ 0 < height (permLattice t.perm α)) :
    ∃ ε : K, ∀ g ∈ heightSeries t.tag K (height α),
      rootCoord hα' (twistHom t K σ g) = ε * σ (rootCoord hα g) := by
  have hF : ∀ γ, IsRoot t.tag γ → ∀ c : K, ∃ d : K,
      twistHom t K σ (pinnedX t.tag K γ c) = pinnedX t.tag K (permLattice t.perm γ) d := by
    intro γ hγ c
    obtain ⟨ε, -, hε⟩ := diagramMap_conj_pinnedX (K := K) t hγ
    refine ⟨ε * σ c, ?_⟩
    have : twistHom t K σ (pinnedX t.tag K γ c) =
        diagramMap t K * Units.map (entrywiseHom σ) (pinnedX t.tag K γ c) *
          (diagramMap t K)⁻¹ := rfl
    rw [this, show Units.map (entrywiseHom σ) (pinnedX t.tag K γ c) = pinnedX t.tag K γ (σ c) from
      Units.ext (entrywise_pinnedX σ γ c), hε]
  obtain ⟨ε, -, hε⟩ := diagramMap_conj_pinnedX (K := K) t hα.1
  refine ⟨ε, fun g hg => ?_⟩
  refine rootCoord_map (twistHom t K σ) (permLattice t.perm)
    (fun γ hγ => hγ.permLattice t.cartan_perm) (fun γ => height_permLattice _ _)
    (fun γ γ' _ _ h => ?_) hF σ.toAddMonoidHom hα hα' ε (fun c => ?_) hg
  · have h' : γ ∘ ⇑(Equiv.symm t.perm) = γ' ∘ ⇑(Equiv.symm t.perm) := h
    funext x
    simpa using congrFun h' (t.perm x)
  · have : twistHom t K σ (pinnedX t.tag K α c) =
        diagramMap t K * Units.map (entrywiseHom σ) (pinnedX t.tag K α c) *
          (diagramMap t K)⁻¹ := rfl
    rw [this, show Units.map (entrywiseHom σ) (pinnedX t.tag K α c) = pinnedX t.tag K α (σ c) from
      Units.ext (entrywise_pinnedX σ α c), hε]
    rfl

theorem rootCoord_entrywise (σ : K →+* K) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α ∧ 0 < height α) {g : ModGL τ K} (hg : g ∈ heightSeries τ K (height α)) :
    rootCoord hα (Units.map (entrywiseHom σ) g) = σ (rootCoord hα g) := by
  have h := rootCoord_map (Units.map (entrywiseHom σ)) id (fun γ hγ => hγ) (fun γ => rfl)
    (fun γ γ' _ _ h => h)
    (fun γ _ c => ⟨σ c, Units.ext (entrywise_pinnedX σ γ c)⟩) σ.toAddMonoidHom hα hα 1
    (fun c => by simpa using Units.ext (entrywise_pinnedX σ α c)) hg
  simpa using h

theorem mem_heightSeries_succ_of_coord_eq_zero {h : ℤ} {x : ModGL τ K}
    (hx : x ∈ heightSeries τ K h)
    (hcoord : ∀ (α : Fin τ.rank → ℤ) (hα : IsRoot τ α ∧ 0 < height α), height α = h →
      rootCoord hα x = 0) : x ∈ heightSeries τ K (h + 1) := by
  classical
  set S : Set (Fin τ.rank → ℤ) := {γ | IsRoot τ γ ∧ 0 < height γ ∧ h ≤ height γ} with hS
  have hfin : S.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1
  let e := hfin.toFinset.equivFin
  let α : Fin hfin.toFinset.card → Fin τ.rank → ℤ := fun i => (e.symm i : _)
  have hαinj : Function.Injective α := fun i j hij => e.symm.injective (Subtype.ext hij)
  have hαrange : Set.range α = S := by
    ext γ
    constructor
    · rintro ⟨i, rfl⟩
      exact hfin.mem_toFinset.1 (e.symm i).2
    · intro hγ
      exact ⟨e ⟨γ, hfin.mem_toFinset.2 hγ⟩, by simp [α]⟩
  have hbij := bijOn_prod_pinnedX K (S := S) (fun γ hγ => ⟨hγ.1, hγ.2.1⟩)
    (fun a ha b hb m n hm hn hr => heightSeriesSet_closed a ha b hb m n hm hn hr) α hαinj hαrange
  have hxS : x ∈ rootSpan τ K S := hx
  obtain ⟨c, -, hc⟩ := hbij.surjOn hxS
  have hfac : ∀ i, pinnedX τ K (α i) (c i) ∈ heightSeries τ K h := fun i =>
    pinnedX_mem_rootSpan (S := S) (hfin.mem_toFinset.1 (e.symm i).2) _
  have hci : ∀ i, height (α i) = h → c i = 0 := by
    intro i hi
    have hαi : IsRoot τ (α i) ∧ 0 < height (α i) :=
      ⟨(hfin.mem_toFinset.1 (e.symm i).2).1, (hfin.mem_toFinset.1 (e.symm i).2).2.1⟩
    have h1 := hcoord (α i) hαi hi
    rw [← hc] at h1
    have hmem : ∀ g ∈ List.ofFn (fun j => pinnedX τ K (α j) (c j)),
        g ∈ heightSeries τ K (height (α i)) := by
      intro g hg
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hg
      rw [hi]
      exact hfac j
    rw [rootCoord_list_prod hαi _ hmem] at h1
    have hterm : ∀ j, rootCoord hαi (pinnedX τ K (α j) (c j)) = if j = i then c j else 0 := by
      intro j
      have hj := hfin.mem_toFinset.1 (e.symm j).2
      by_cases hji : j = i
      · subst hji
        rw [rootCoord_self hαi]
        simp
      · have hne : α j ≠ α i := fun h' => hji (hαinj h')
        rw [rootCoord_pinnedX_of_ne hαi ⟨hj.1, hj.2.1⟩ (by rw [hi]; exact hj.2.2) hne]
        simp [hji]
    simp only [List.map_ofFn, Function.comp_def, hterm, List.sum_ofFn] at h1
    simpa using h1
  rw [← hc]
  refine list_prod_mem fun g hg => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
  by_cases hi : height (α i) = h
  · rw [hci i hi, pinnedX_zero]; exact one_mem _
  · have hj := hfin.mem_toFinset.1 (e.symm i).2
    have hj1 : IsRoot τ (α i) := hj.1
    have hj2 : 0 < height (α i) := hj.2.1
    have hge : h ≤ height (α i) := hj.2.2
    have key : h + 1 ≤ height (α i) := by omega
    exact pinnedX_mem_rootSpan (S := {γ | IsRoot τ γ ∧ 0 < height γ ∧ h + 1 ≤ height γ})
      ⟨hj1, hj2, key⟩ _

end CFSG.HardMathSupport.Lang.Triality
