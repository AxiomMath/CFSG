module

public import CFSG.ClassicalGroups.Orthogonal.SiegelI4CoplSetup
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalGroups.Alternating.I4SpLevi

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.ClassicalGroups.Alternating CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {N : Type*} [AddCommGroup N] [Module K N] [FiniteDimensional K N]
  {BN : LinearMap.BilinForm K N}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

section Existence

variable (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate) (hdim : 6 ≤ finrank K N)
include hBN hBNnd hdim

theorem exists_isLine_of_ne_zero {a : N} (ha : a ≠ 0) : ∃ ℓ, IsLine BN ℓ ∧ a ∈ ℓ := by
  have hperp : finrank K ↥(BN.orthogonal (Submodule.span K {a})) = finrank K N - 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hBNnd, finrank_span_singleton ha]
  have h2 : 2 ≤ finrank K ↥(BN.orthogonal (Submodule.span K {a})) := by omega
  have haperp : a ∈ BN.orthogonal (Submodule.span K {a}) := by
    intro n hn
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hn
    simp [hBN.self_eq_zero]
  obtain ⟨c, hcperp, hind⟩ := exists_mem_linearIndependent_pair h2 haperp ha
  have hac : BN a c = 0 := hcperp a (Submodule.subset_span rfl)
  refine ⟨Submodule.span K {a, c}, ⟨isotropic_span_pair hBN hac, ?_⟩,
    Submodule.subset_span (by simp)⟩
  rw [← Matrix.range_cons_cons_empty a c ![], finrank_span_eq_card hind, Fintype.card_fin]

theorem exists_two_planes_through {ℓ : Submodule K N} (hℓ : IsLine BN ℓ) :
    ∃ π π' : Submodule K N, IsPlane BN π ∧ IsPlane BN π' ∧ ℓ ≤ π ∧ ℓ ≤ π' ∧ π ≠ π' := by
  obtain ⟨H, hH⟩ := exists_isLeviSpace hBN hBNnd hℓ
  have hW : 2 ≤ finrank K ↥(BN.orthogonal H) := by
    rw [hH.finrank_orthogonal hBNnd]
    omega
  have hWpos : 0 < finrank K ↥(BN.orthogonal H) := by omega
  haveI : Nontrivial ↥(BN.orthogonal H) := Module.nontrivial_of_finrank_pos hWpos
  obtain ⟨n, hn⟩ := exists_ne (0 : ↥(BN.orthogonal H))
  have hn0 : (n : N) ≠ 0 := fun h => hn (Subtype.ext h)
  obtain ⟨n', hn'W, hind⟩ := exists_mem_linearIndependent_pair hW n.2 hn0
  have hn'0 : n' ≠ 0 := by simpa using hind.ne_zero (1 : Fin 2)
  refine ⟨ℓ ⊔ Submodule.span K {(n : N)}, ℓ ⊔ Submodule.span K {n'},
    isPlane_sup_span hBN hH n.2 hn0, isPlane_sup_span hBN hH hn'W hn'0, le_sup_left, le_sup_left,
    fun h => ?_⟩
  have hsn : Submodule.span K {(n : N)} ≤ BN.orthogonal H :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr n.2
  have hsn' : Submodule.span K {n'} ≤ BN.orthogonal H :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr hn'W
  have h2 := sup_inf_orthogonal_eq hBN hH hsn
  rw [h, sup_inf_orthogonal_eq hBN hH hsn'] at h2
  have hmem : n' ∈ Submodule.span K {(n : N)} := h2 ▸ Submodule.mem_span_singleton_self n'
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hmem
  have := LinearIndependent.pair_iff.mp hind s (-1) (by rw [hs]; module)
  exact one_ne_zero (neg_eq_zero.mp this.2)

end Existence

theorem exists_ne_one_mem_planeGroup (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate)
    {ℓ : Submodule K N} (hℓ : IsLine BN ℓ) : ∃ g ∈ planeGroup hBN ℓ, g ≠ 1 := by
  obtain ⟨a, c, hac, hind, rfl⟩ := hℓ.exists_pair
  exact ⟨lineElt hBN a c, lineElt_mem_planeGroup hBN (Submodule.subset_span (by simp))
    (Submodule.subset_span (by simp)), lineElt_ne_one hBN hBNnd hac hind⟩

@[expose] noncomputable def famSpace (hBN : BN.IsAlt) (ρ : Gsp BN →* (V ≃ₗ[K] V))
    (σ : Submodule K N) : Submodule K V :=
  commutatorSpace (planeFamily hBN ρ σ)

theorem famSpace_map (hBN : BN.IsAlt) (ρ : Gsp BN →* (V ≃ₗ[K] V)) (g : Gsp BN)
    (σ : Submodule K N) :
    famSpace hBN ρ (σ.map g.lin) = (famSpace hBN ρ σ).map (ρ g : V →ₗ[K] V) := by
  unfold famSpace
  rw [planeFamily_map, commutatorSpace_conjSubgroup]

theorem movedSpace_le_famSpace (hBN : BN.IsAlt) (ρ : Gsp BN →* (V ≃ₗ[K] V))
    {σ : Submodule K N} {g : Gsp BN} (hg : g ∈ planeGroup hBN σ) :
    movedSpace (ρ g) ≤ famSpace hBN ρ σ :=
  movedSpace_le_commutatorSpace ⟨g, hg, rfl⟩

theorem famSpace_mono (hBN : BN.IsAlt) (ρ : Gsp BN →* (V ≃ₗ[K] V)) {σ σ' : Submodule K N}
    (h : σ ≤ σ') : famSpace hBN ρ σ ≤ famSpace hBN ρ σ' := by
  refine commutatorSpace_le_of_forall_axes_le fun A hA => ?_
  obtain ⟨s, ⟨g, hg, rfl⟩, -, rfl⟩ := hA
  exact movedSpace_le_famSpace hBN ρ (planeGroup_mono hBN h hg)

section Axis

variable {hBN : BN.IsAlt} {Qf : QuadraticForm K V} {ρ : Gsp BN →* (V ≃ₗ[K] V)}
  (hs : I4Setting hBN Qf ρ) (hcopl : ∀ π, IsPlane BN π → Copl (planeFamily hBN ρ π))

include hs hcopl

theorem finrank_famSpace_of_isPlane {π : Submodule K N} (hπ : IsPlane BN π) :
    finrank K (famSpace hBN ρ π) = 3 :=
  (hs.isSiegelFamily_planeFamily hπ).finrank_commutatorSpace_of_copl hs.nondeg (hcopl π hπ)

theorem qf_eq_zero_of_mem_famSpace_isPlane {π : Submodule K N} (hπ : IsPlane BN π) :
    ∀ w ∈ famSpace hBN ρ π, Qf w = 0 :=
  (hs.isSiegelFamily_planeFamily hπ).qf_eq_zero_of_mem_commutatorSpace hs.nondeg

theorem planeFamily_eq_sigmaGroup {π : Submodule K N} (hπ : IsPlane BN π) :
    planeFamily hBN ρ π = sigmaGroup Qf (famSpace hBN ρ π) :=
  (hs.isSiegelFamily_planeFamily hπ).eq_sigmaGroup_of_copl hs.nondeg (hcopl π hπ)

theorem famSpace_ne_of_isPlane {π π' : Submodule K N} (hπ : IsPlane BN π) (hπ' : IsPlane BN π')
    (hne : π ≠ π') : famSpace hBN ρ π ≠ famSpace hBN ρ π' := by
  intro h
  apply hne
  have h1 : planeFamily hBN ρ π = planeFamily hBN ρ π' := by
    rw [planeFamily_eq_sigmaGroup hs hcopl hπ, planeFamily_eq_sigmaGroup hs hcopl hπ', h]
  have h2 : planeGroup hBN π = planeGroup hBN π' := Subgroup.map_injective hs.inj h1
  exact eq_of_planeGroup_eq hBN hs.nondegN (Or.inr hπ) (Or.inr hπ') h2

theorem famSpace_eq_inf_of_isLine {ℓ π π' : Submodule K N} (hℓ : IsLine BN ℓ)
    (hπ : IsPlane BN π) (hπ' : IsPlane BN π') (hℓπ : ℓ ≤ π) (hℓπ' : ℓ ≤ π') (hne : π ≠ π') :
    famSpace hBN ρ ℓ = famSpace hBN ρ π ⊓ famSpace hBN ρ π' ∧
      ∀ g ∈ planeGroup hBN ℓ, g ≠ 1 → movedSpace (ρ g) = famSpace hBN ρ π ⊓ famSpace hBN ρ π' := by
  have hU := finrank_famSpace_of_isPlane hs hcopl hπ
  have hU' := finrank_famSpace_of_isPlane hs hcopl hπ'
  have hUU' := famSpace_ne_of_isPlane hs hcopl hπ hπ' hne
  have hfin : finrank K ↥(famSpace hBN ρ π ⊓ famSpace hBN ρ π') ≤ 2 := by
    by_contra hcon
    have h3 : finrank K ↥(famSpace hBN ρ π ⊓ famSpace hBN ρ π') = 3 := by
      have := Submodule.finrank_mono (inf_le_left : famSpace hBN ρ π ⊓ famSpace hBN ρ π' ≤ _)
      omega
    have e1 := Submodule.eq_of_le_of_finrank_eq
      (inf_le_left : famSpace hBN ρ π ⊓ famSpace hBN ρ π' ≤ _) (by rw [h3, hU])
    have e2 := Submodule.eq_of_le_of_finrank_eq
      (inf_le_right : famSpace hBN ρ π ⊓ famSpace hBN ρ π' ≤ _) (by rw [h3, hU'])
    exact hUU' (e1.symm.trans e2)
  have hmoved : ∀ g ∈ planeGroup hBN ℓ, g ≠ 1 →
      movedSpace (ρ g) = famSpace hBN ρ π ⊓ famSpace hBN ρ π' := by
    intro g hg hg1
    have hle : movedSpace (ρ g) ≤ famSpace hBN ρ π ⊓ famSpace hBN ρ π' :=
      le_inf (movedSpace_le_famSpace hBN ρ (planeGroup_mono hBN hℓπ hg))
        (movedSpace_le_famSpace hBN ρ (planeGroup_mono hBN hℓπ' hg))
    have h2 := (hs.isLongRootElement_map_of_isLine hℓ hg hg1).finrank_movedSpace hs.nondeg
    exact Submodule.eq_of_le_of_finrank_le hle (by omega)
  refine ⟨le_antisymm ?_ ?_, hmoved⟩
  · refine commutatorSpace_le_of_forall_axes_le fun A hA => ?_
    obtain ⟨s, ⟨g, hg, rfl⟩, hs1, rfl⟩ := hA
    exact (hmoved g hg fun h => hs1 (by rw [h, map_one])).le
  · obtain ⟨g₀, hg₀, hg₀1⟩ := exists_ne_one_mem_planeGroup hBN hs.nondegN hℓ
    rw [← hmoved g₀ hg₀ hg₀1]
    exact movedSpace_le_famSpace hBN ρ hg₀

theorem movedSpace_eq_famSpace_of_isLine {ℓ : Submodule K N} (hℓ : IsLine BN ℓ) {g : Gsp BN}
    (hg : g ∈ planeGroup hBN ℓ) (hg1 : g ≠ 1) : movedSpace (ρ g) = famSpace hBN ρ ℓ := by
  obtain ⟨π, π', hπ, hπ', hℓπ, hℓπ', hne⟩ := exists_two_planes_through hBN hs.nondegN hs.dimN hℓ
  obtain ⟨h1, h2⟩ := famSpace_eq_inf_of_isLine hs hcopl hℓ hπ hπ' hℓπ hℓπ' hne
  rw [h1]
  exact h2 g hg hg1

theorem finrank_famSpace_of_isLine {ℓ : Submodule K N} (hℓ : IsLine BN ℓ) :
    finrank K (famSpace hBN ρ ℓ) = 2 := by
  obtain ⟨g, hg, hg1⟩ := exists_ne_one_mem_planeGroup hBN hs.nondegN hℓ
  rw [← movedSpace_eq_famSpace_of_isLine hs hcopl hℓ hg hg1]
  exact (hs.isLongRootElement_map_of_isLine hℓ hg hg1).finrank_movedSpace hs.nondeg

theorem qf_eq_zero_of_mem_famSpace_isLine {ℓ : Submodule K N} (hℓ : IsLine BN ℓ) :
    ∀ w ∈ famSpace hBN ρ ℓ, Qf w = 0 := by
  obtain ⟨g, hg, hg1⟩ := exists_ne_one_mem_planeGroup hBN hs.nondegN hℓ
  rw [← movedSpace_eq_famSpace_of_isLine hs hcopl hℓ hg hg1]
  exact fun w hw => (hs.isLongRootElement_map_of_isLine hℓ hg hg1).qf_eq_zero_of_mem_movedSpace hw

theorem planeFamily_eq_piGroup_of_isLine {ℓ : Submodule K N} (hℓ : IsLine BN ℓ)
    {P : Submodule K V} (hP : finrank K P = 1) (hPA : P ≤ famSpace hBN ρ ℓ) :
    planeFamily hBN ρ ℓ = piGroup Qf P (famSpace hBN ρ ℓ) := by
  have hA2 := finrank_famSpace_of_isLine hs hcopl hℓ
  have hAs := qf_eq_zero_of_mem_famSpace_isLine hs hcopl hℓ
  have hcard : Nat.card (piGroup Qf P (famSpace hBN ρ ℓ)) = Nat.card K := by
    rw [natCard_piGroup hs.nondeg hAs hP hPA, hA2]
    simp
  have hcardℓ : Nat.card (planeFamily hBN ρ ℓ) = Nat.card K := by
    rw [planeFamily, Subgroup.card_map_of_injective hs.inj,
      card_planeGroup_of_isLine hBN hs.nondegN hℓ]
  have hle : planeFamily hBN ρ ℓ ≤ piGroup Qf P (famSpace hBN ρ ℓ) := by
    rintro _ ⟨g, hg, rfl⟩
    by_cases hg1 : g = 1
    · rw [hg1, map_one]
      exact one_mem _
    · have hax := movedSpace_eq_famSpace_of_isLine hs hcopl hℓ hg hg1
      exact isLongRootElement_mem_piGroup (hs.isLongRootElement_map_of_isLine hℓ hg hg1)
        (hax ▸ hPA) hax.le
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hfin : Finite (piGroup Qf P (famSpace hBN ρ ℓ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hcardℓ])

theorem famSpace_injective_of_isLine {ℓ ℓ' : Submodule K N} (hℓ : IsLine BN ℓ)
    (hℓ' : IsLine BN ℓ') (h : famSpace hBN ρ ℓ = famSpace hBN ρ ℓ') : ℓ = ℓ' := by
  have hA2 := finrank_famSpace_of_isLine hs hcopl hℓ
  obtain ⟨p, hpA, hp0⟩ : ∃ p ∈ famSpace hBN ρ ℓ, p ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : famSpace hBN ρ ℓ = ⊥ := (Submodule.eq_bot_iff _).mpr hcon
    rw [this, finrank_bot] at hA2
    omega
  have hP1 : finrank K (Submodule.span K {p}) = 1 := finrank_span_singleton hp0
  have hPA : Submodule.span K {p} ≤ famSpace hBN ρ ℓ :=
    (Submodule.span_singleton_le_iff_mem p _).mpr hpA
  have h1 := planeFamily_eq_piGroup_of_isLine hs hcopl hℓ hP1 hPA
  have h2 := planeFamily_eq_piGroup_of_isLine hs hcopl hℓ' hP1 (h ▸ hPA)
  rw [← h] at h2
  have h3 : planeGroup hBN ℓ = planeGroup hBN ℓ' := Subgroup.map_injective hs.inj (h1.trans h2.symm)
  exact eq_of_planeGroup_eq hBN hs.nondegN (Or.inl hℓ) (Or.inl hℓ') h3

end Axis

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
