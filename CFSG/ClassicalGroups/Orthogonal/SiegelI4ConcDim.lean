module

public import CFSG.ClassicalGroups.Orthogonal.SiegelI4ConcPlane
public import CFSG.ClassicalGroups.Alternating.I4SpQuad

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
  {π : Submodule K N}

include hs hconc

theorem famSpace_eq_iSup_isLine_conc (hπ : IsPlane BN π) :
    famSpace hBN ρ π =
      ⨆ ℓ : {ℓ : Submodule K N // IsLine BN ℓ ∧ ℓ ≤ π}, famSpace hBN ρ ℓ.1 := by
  refine le_antisymm ?_ (iSup_le fun ℓ => famSpace_mono hBN ρ ℓ.2.2)
  refine commutatorSpace_le_of_forall_axes_le fun A hA => ?_
  obtain ⟨s, ⟨g, hg, rfl⟩, hs1, rfl⟩ := hA
  have hg1 : g ≠ 1 := fun h => hs1 (by rw [h, map_one])
  obtain ⟨ℓ, hℓπ, hℓ, hgℓ⟩ := exists_isLine_of_mem_planeGroup hBN hs.nondegN hπ hg hg1
  rw [conc_movedSpace_eq_famSpace hs hconc hℓ hgℓ hg1]
  exact le_iSup (fun ℓ : {ℓ : Submodule K N // IsLine BN ℓ ∧ ℓ ≤ π} => famSpace hBN ρ ℓ.1)
    ⟨ℓ, hℓ, hℓπ⟩

theorem conc_finrank_famSpace_plane (hπ : IsPlane BN π) :
    finrank K (famSpace hBN ρ π) = 4 := by
  have hE := hs.isSiegelFamily_planeFamily hπ
  have hP1 := finrank_concPt hs hconc hπ
  obtain ⟨p, hp0, hpP⟩ := exists_ne_zero_span_eq_of_finrank_eq_one hP1
  have hW0 : ∀ w ∈ famSpace hBN ρ π, Qf w = 0 :=
    hE.qf_eq_zero_of_mem_commutatorSpace hs.nondeg
  obtain ⟨A₀, hA₀⟩ := hE.nonempty_axes hs.nondeg
  have hPW : concPt hBN ρ π ≤ famSpace hBN ρ π :=
    (axisInf_le hA₀).trans (le_commutatorSpace_of_mem_axes hA₀)
  obtain ⟨s, ⟨g, hg, rfl⟩, hs1, -⟩ := hA₀
  obtain ⟨ℓ₀, hℓ₀π, hℓ₀, -⟩ :=
    exists_isLine_of_mem_planeGroup hBN hs.nondegN hπ hg fun h => hs1 (by rw [h, map_one])
  have : Nonempty {ℓ : Submodule K N // IsLine BN ℓ ∧ ℓ ≤ π} := ⟨⟨ℓ₀, hℓ₀, hℓ₀π⟩⟩
  have hiSup := famSpace_eq_iSup_isLine_conc hs hconc hπ
  have hpW : ∀ i : {ℓ : Submodule K N // IsLine BN ℓ ∧ ℓ ≤ π}, p ∈ famSpace hBN ρ i.1 := fun i =>
    concPt_le_famSpace hs hconc i.2.1 i.2.2 (hpP ▸ Submodule.mem_span_singleton_self p)
  have hW0' : ∀ w ∈ ⨆ i : {ℓ : Submodule K N // IsLine BN ℓ ∧ ℓ ≤ π}, famSpace hBN ρ i.1,
      Qf w = 0 := by
    rw [← hiSup]
    exact hW0
  have hpi := piGroup_iSup (W := fun i : {ℓ : Submodule K N // IsLine BN ℓ ∧ ℓ ≤ π} =>
    famSpace hBN ρ i.1) hs.nondeg hW0' hp0 hpW
  have hpiE : piGroup Qf (Submodule.span K {p}) (famSpace hBN ρ π) = planeFamily hBN ρ π := by
    refine le_antisymm ?_ ?_
    · rw [hiSup, hpi]
      refine iSup_le fun i => ?_
      rw [← hpP, ← conc_planeFamily_eq_piGroup hs hconc i.2.1 hP1
        (concPt_le_famSpace hs hconc i.2.1 i.2.2)]
      exact Subgroup.map_mono (planeGroup_mono hBN i.2.2)
    · have h2 : planeFamily hBN ρ π ≤ piGroup Qf (concPt hBN ρ π) (famSpace hBN ρ π) :=
        hE.le_piGroup_axisInf hs.nondeg
      rwa [hpP] at h2
  have hcard := natCard_piGroup hs.nondeg hW0 hP1 hPW
  rw [hpP] at hcard
  rw [hpiE, hE.card] at hcard
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have h3 := Nat.pow_right_injective (by omega : 2 ≤ Nat.card K) hcard
  have hge : 1 ≤ finrank K (famSpace hBN ρ π) := by
    have := Submodule.finrank_mono hPW
    omega
  omega

theorem conc_eight_le_finrank : 8 ≤ finrank K V := by
  have hNpos : 0 < finrank K N := by have := hs.dimN; omega
  have : Nontrivial N := Module.nontrivial_of_finrank_pos hNpos
  obtain ⟨a, ha⟩ := exists_ne (0 : N)
  obtain ⟨π, hπ, -⟩ := exists_isPlane_mem hs ha
  have h4 := conc_finrank_famSpace_plane hs hconc hπ
  have hW0 : ∀ w ∈ famSpace hBN ρ π, Qf w = 0 :=
    (hs.isSiegelFamily_planeFamily hπ).qf_eq_zero_of_mem_commutatorSpace hs.nondeg
  have h1 := Submodule.finrank_mono (le_orthogonal_of_totallySingular hW0)
  have h2 := finrank_orthogonal_polar hs.nondeg (famSpace hBN ρ π)
  have h3 := Submodule.finrank_le (famSpace hBN ρ π)
  omega

theorem conc_finrank_le_eight (hdim : finrank K N = 6) : finrank K V ≤ 8 := by
  obtain ⟨π₀, π₀', h, hπ₀, hπ₀'⟩ := exists_isCompl_isPlane hBN hs.nondegN hdim
  set Y : Submodule K V := famSpace hBN ρ π₀ ⊔ famSpace hBN ρ π₀' with hYdef
  have hY : finrank K Y ≤ 8 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq (famSpace hBN ρ π₀) (famSpace hBN ρ π₀')
    rw [conc_finrank_famSpace_plane hs hconc hπ₀, conc_finrank_famSpace_plane hs hconc hπ₀',
      ← hYdef] at this
    omega
  have hS : planeGroup hBN π₀ ⊔ planeGroup hBN π₀' ≤ trivMod ρ Y := by
    refine sup_le (fun g hg v => ?_) (fun g hg v => ?_)
    · exact Submodule.mem_sup_left (movedSpace_le_famSpace hBN ρ hg (sub_mem_movedSpace _ v))
    · exact Submodule.mem_sup_right (movedSpace_le_famSpace hBN ρ hg (sub_mem_movedSpace _ v))
  have hsing : ∀ ℓ : Submodule K N, IsLine BN ℓ → (∀ x ∈ ℓ, quadPlus BN h x = 0) →
      famSpace hBN ρ ℓ ≤ Y := by
    intro ℓ hℓ hs0
    have hsub := planeGroup_le_sup_of_singular hBN hs.nondegN h hπ₀ hπ₀' hℓ hs0
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨g, hg, rfl⟩, v, rfl⟩
    exact hS (hsub hg) v
  have hplane : ∀ π : Submodule K N, IsPlane BN π → concPt hBN ρ π ≤ Y := by
    intro π hπ
    obtain ⟨ℓ, hℓπ, hℓ, hs0⟩ := exists_isLine_le_singular hBN h hπ₀ hπ₀' hπ
    exact (concPt_le_famSpace hs hconc hℓ hℓπ).trans (hsing ℓ hℓ hs0)
  have hline : ∀ ℓ : Submodule K N, IsLine BN ℓ → famSpace hBN ρ ℓ ≤ Y := by
    intro ℓ hℓ v hv
    by_cases hv0 : v = 0
    · rw [hv0]
      exact Y.zero_mem
    · obtain ⟨π, hπ, hℓπ, hπv⟩ := conc_exists_plane_concPt_eq hs hconc hdim hℓ
        (finrank_span_singleton hv0) ((Submodule.span_singleton_le_iff_mem v _).mpr hv)
      have := hplane π hπ
      rw [hπv] at this
      exact this (Submodule.mem_span_singleton_self v)
  have htop : (⊤ : Submodule K V) ≤ Y := by
    rw [← iSup_famSpace_isLine hs]
    exact iSup₂_le fun ℓ hℓ => hline ℓ hℓ
  calc finrank K V = finrank K (⊤ : Submodule K V) := finrank_top K V |>.symm
    _ ≤ finrank K Y := Submodule.finrank_mono htop
    _ ≤ 8 := hY

end Conc

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
