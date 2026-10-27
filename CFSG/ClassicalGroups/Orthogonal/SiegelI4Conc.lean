module

public import CFSG.ClassicalGroups.Orthogonal.SiegelI4ConcDim

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.ClassicalGroups.Alternating CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {N : Type*} [AddCommGroup N] [Module K N] [FiniteDimensional K N]
  {BN : LinearMap.BilinForm K N}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {hBN : BN.IsAlt} {Qf : QuadraticForm K V} {ρ : Gsp BN →* (V ≃ₗ[K] V)}

section Conc

variable (hs : I4Setting hBN Qf ρ) (hconc : ∀ π, IsPlane BN π → Conc (planeFamily hBN ρ π))

include hs

theorem exists_lineElt_ne_of_ne_bot (U : AddSubgroup V) (hU0 : U ≠ ⊥) :
    ∃ a c : N, BN a c = 0 ∧ LinearIndependent K ![a, c] ∧ ∃ x ∈ U, ρ (lineElt hBN a c) x ≠ x := by
  by_contra hcon
  push Not at hcon
  let T : Subgroup (Gsp BN) :=
    { carrier := {g | ∀ x ∈ U, ρ g x = x}
      one_mem' := fun x _ => by simp
      mul_mem' := fun {g h} hg hh x hx => by
        rw [map_mul, LinearEquiv.mul_apply, hh x hx, hg x hx]
      inv_mem' := fun {g} hg x hx => by
        calc ρ g⁻¹ x = ρ g⁻¹ (ρ g x) := by rw [hg x hx]
          _ = x := by rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
  have hT : T = ⊤ := eq_top_of_forall_lineElt_mem hs T fun a c hac hind x hx =>
    hcon a c hac hind x hx
  apply hU0
  rw [eq_bot_iff]
  intro x hx
  have := hs.fix x fun g => (hT ▸ Subgroup.mem_top g : g ∈ T) x hx
  simp [this]

include hconc

theorem exists_mem_planeGroup_smul_sub {ℓ : Submodule K N} (hℓ : IsLine BN ℓ) {g : Gsp BN}
    (hg : g ∈ planeGroup hBN ℓ) (x : V) (hx : ρ g x ≠ x) (t : K) :
    ∃ g' ∈ planeGroup hBN ℓ, ρ g' x - x = t • (ρ g x - x) := by
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : V, w₀ = ρ g x - x := ⟨_, rfl⟩
  have hw₀0 : w₀ ≠ 0 := by
    rw [hw₀]
    exact sub_ne_zero.mpr hx
  have hw₀A : w₀ ∈ famSpace hBN ρ ℓ := by
    rw [hw₀]
    exact movedSpace_le_famSpace hBN ρ hg (sub_mem_movedSpace _ x)
  have hP1 : finrank K (Submodule.span K {w₀}) = 1 := finrank_span_singleton hw₀0
  have hPA : Submodule.span K {w₀} ≤ famSpace hBN ρ ℓ :=
    (Submodule.span_singleton_le_iff_mem w₀ _).mpr hw₀A
  have hfam := conc_planeFamily_eq_piGroup hs hconc hℓ hP1 hPA
  have hAs := qf_eq_zero_of_mem_famSpace_isLine_conc hs hconc hℓ
  have hmem : ρ g ∈ piGroup Qf (Submodule.span K {w₀}) (famSpace hBN ρ ℓ) := by
    rw [← hfam]
    exact ⟨g, hg, rfl⟩
  obtain ⟨w, hw, hρg⟩ := (mem_piGroup_iff hs.nondeg hAs hw₀0 hw₀A).mp hmem
  have htw : t • w ∈ famSpace hBN ρ ℓ := (famSpace hBN ρ ℓ).smul_mem t hw
  have hmem' : eichler Qf w₀ (t • w) ∈
      piGroup Qf (Submodule.span K {w₀}) (famSpace hBN ρ ℓ) :=
    (mem_piGroup_iff hs.nondeg hAs hw₀0 hw₀A).mpr ⟨t • w, htw, rfl⟩
  rw [← hfam] at hmem'
  obtain ⟨g', hg', hρg'⟩ := hmem'
  refine ⟨g', hg', ?_⟩
  have hp : Qf w₀ = 0 := hAs w₀ hw₀A
  have e1 : ρ g x = x + polar Qf x w₀ • w + polar Qf x w • w₀ := by
    rw [hρg, eichler_apply_of_qf_eq_zero hp (polar_eq_zero_of_totallySingular hAs hw₀A hw)
      (hAs w hw)]
  have e2 : ρ g' x = x + polar Qf x w₀ • (t • w) + polar Qf x (t • w) • w₀ := by
    rw [hρg', eichler_apply_of_qf_eq_zero hp (polar_eq_zero_of_totallySingular hAs hw₀A htw)
      (hAs _ htw)]
  have e3 : w₀ = polar Qf x w₀ • w + polar Qf x w • w₀ := by
    linear_combination (norm := module) hw₀ + e1
  rw [e2, polar_smul_right, ← hw₀]
  linear_combination (norm := module) (-t) • e3

theorem conc_irreducible (U : AddSubgroup V) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  by_cases hU0 : U = ⊥
  · exact Or.inl hU0
  refine Or.inr ?_
  have hdim := conc_finrank_eq_six hs hconc
  obtain ⟨a, c, hac, hind, x, hxU, hx⟩ := exists_lineElt_ne_of_ne_bot hs U hU0
  have hℓ := isLine_span_pair hBN hac hind
  have hg₀ : lineElt hBN a c ∈ planeGroup hBN (Submodule.span K {a, c}) :=
    lineElt_mem_planeGroup hBN (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
  have hmul : ∀ t : K, t • (ρ (lineElt hBN a c) x - x) ∈ U := by
    intro t
    obtain ⟨g', hg', h'⟩ := exists_mem_planeGroup_smul_sub hs hconc hℓ hg₀ x hx t
    rw [← h']
    exact U.sub_mem (hU g' x hxU) hxU
  have hw₀0 : ρ (lineElt hBN a c) x - x ≠ 0 := sub_ne_zero.mpr hx
  have hw₀A : ρ (lineElt hBN a c) x - x ∈ famSpace hBN ρ (Submodule.span K {a, c}) :=
    movedSpace_le_famSpace hBN ρ hg₀ (sub_mem_movedSpace _ x)
  obtain ⟨π, hπ, -, hπP⟩ := conc_exists_plane_concPt_eq hs hconc hdim hℓ
    (finrank_span_singleton hw₀0) ((Submodule.span_singleton_le_iff_mem _ _).mpr hw₀A)
  have hπU : ∀ v ∈ concPt hBN ρ π, v ∈ U := by
    intro v hv
    rw [hπP] at hv
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
    exact hmul t
  have hplane : ∀ π' : Submodule K N, IsPlane BN π' → ∀ v ∈ concPt hBN ρ π', v ∈ U := by
    intro π' hπ' v hv
    obtain ⟨g, hg⟩ := exists_gsp_map_eq_of_isPlane hBN hs.nondegN hπ hπ'
    rw [← hg, concPt_map] at hv
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
    exact hU g u (hπU u hu)
  let T : Submodule K V :=
    { carrier := {v | ∀ t : K, t • v ∈ U}
      add_mem' := fun {u v} hu hv t => by rw [smul_add]; exact U.add_mem (hu t) (hv t)
      zero_mem' := fun t => by rw [smul_zero]; exact U.zero_mem
      smul_mem' := fun r v hv t => by rw [smul_smul]; exact hv (t * r) }
  have hline : ∀ ℓ' : Submodule K N, IsLine BN ℓ' → famSpace hBN ρ ℓ' ≤ T := by
    intro ℓ' hℓ' v hv t
    by_cases hv0 : v = 0
    · rw [hv0, smul_zero]
      exact U.zero_mem
    · obtain ⟨π', hπ', -, hπ'v⟩ := conc_exists_plane_concPt_eq hs hconc hdim hℓ'
        (finrank_span_singleton hv0) ((Submodule.span_singleton_le_iff_mem v _).mpr hv)
      refine hplane π' hπ' _ ?_
      rw [hπ'v]
      exact Submodule.smul_mem _ t (Submodule.mem_span_singleton_self v)
  have htop : (⊤ : Submodule K V) ≤ T := by
    rw [← iSup_famSpace_isLine hs]
    exact iSup₂_le fun ℓ' hℓ' => hline ℓ' hℓ'
  rw [eq_top_iff]
  intro v _
  have := htop (Submodule.mem_top (x := v)) 1
  simpa using this

theorem conc_all_conclusion : finrank K N = 6 ∧ finrank K V = 8 ∧
    ∀ U : AddSubgroup V, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤ :=
  ⟨conc_finrank_eq_six hs hconc,
    le_antisymm (conc_finrank_le_eight hs hconc (conc_finrank_eq_six hs hconc))
      (conc_eight_le_finrank hs hconc),
    fun U hU => conc_irreducible hs hconc U hU⟩

end Conc

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
