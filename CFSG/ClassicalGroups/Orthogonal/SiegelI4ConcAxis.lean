module

public import CFSG.ClassicalGroups.Alternating.I4SpChain
public import CFSG.ClassicalGroups.Alternating.I4SpLeviHom
public import CFSG.ClassicalGroups.Orthogonal.SiegelI4CoplPoint

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.ClassicalGroups.Alternating CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {N : Type*} [AddCommGroup N] [Module K N] [FiniteDimensional K N]
  {BN : LinearMap.BilinForm K N}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {hBN : BN.IsAlt} {Qf : QuadraticForm K V} {ρ : Gsp BN →* (V ≃ₗ[K] V)}

@[expose] noncomputable def concPt (hBN : BN.IsAlt) (ρ : Gsp BN →* (V ≃ₗ[K] V))
    (π : Submodule K N) : Submodule K V :=
  axisInf (planeFamily hBN ρ π)

theorem concPt_map (g : Gsp BN) (π : Submodule K N) :
    concPt hBN ρ (π.map g.lin) = (concPt hBN ρ π).map (ρ g : V →ₗ[K] V) := by
  unfold concPt
  rw [planeFamily_map, axisInf_conjSubgroup]

omit [Finite K] [CharP K 2] in
theorem Gsp.map_lin_inv_map_lin (g : Gsp BN) (S : Submodule K N) :
    (S.map g.lin).map g⁻¹.lin = S := by
  have := Gsp.map_lin_map_lin_inv g⁻¹ S
  simpa using this

@[expose] def ConstLine (hBN : BN.IsAlt) (ρ : Gsp BN →* (V ≃ₗ[K] V)) (ℓ : Submodule K N) : Prop :=
  ∀ π π', IsPlane BN π → IsPlane BN π' → ℓ ≤ π → ℓ ≤ π' → concPt hBN ρ π = concPt hBN ρ π'

theorem constLine_map {ℓ : Submodule K N} (hc : ConstLine hBN ρ ℓ) (g : Gsp BN) :
    ConstLine hBN ρ (ℓ.map g.lin) := by
  have key : ∀ σ : Submodule K N, IsPlane BN σ → ℓ.map g.lin ≤ σ →
      IsPlane BN (σ.map g⁻¹.lin) ∧ ℓ ≤ σ.map g⁻¹.lin ∧
        concPt hBN ρ σ = (concPt hBN ρ (σ.map g⁻¹.lin)).map (ρ g : V →ₗ[K] V) := by
    intro σ hσ hℓσ
    refine ⟨hσ.map g⁻¹, ?_, ?_⟩
    · have h := Submodule.map_mono (f := g⁻¹.lin) hℓσ
      rwa [Gsp.map_lin_inv_map_lin] at h
    · rw [← concPt_map, Gsp.map_lin_map_lin_inv]
  intro π π' hπ hπ' hℓπ hℓπ'
  obtain ⟨hπ₀, hℓπ₀, e⟩ := key π hπ hℓπ
  obtain ⟨hπ₀', hℓπ₀', e'⟩ := key π' hπ' hℓπ'
  rw [e, e', hc _ _ hπ₀ hπ₀' hℓπ₀ hℓπ₀']

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem concPt_eq_of_forall_constLine (hall : ∀ ℓ, IsLine BN ℓ → ConstLine hBN ρ ℓ)
    {π π' : Submodule K N} (hπ : IsPlane BN π) (hπ' : IsPlane BN π') :
    concPt hBN ρ π = concPt hBN ρ π' := by
  have hchain := exists_planeAdj_chain hBN hπ hπ'
  suffices key : ∀ σ, Relation.ReflTransGen (PlaneAdj BN (π ⊓ π')) π σ →
      concPt hBN ρ π = concPt hBN ρ σ from key π' hchain
  intro σ hσ
  induction hσ with
  | refl => rfl
  | tail _ hstep ih =>
    obtain ⟨hσ₁, hσ₂, hfin, -, -⟩ := hstep
    have hℓ : IsLine BN (_ ⊓ _) := ⟨fun x hx y hy => hσ₁.1 x hx.1 y hy.1, hfin⟩
    exact ih.trans (hall _ hℓ _ _ hσ₁ hσ₂ inf_le_left inf_le_right)

section Conc

variable (hs : I4Setting hBN Qf ρ) (hconc : ∀ π, IsPlane BN π → Conc (planeFamily hBN ρ π))

include hs hconc

theorem finrank_concPt {π : Submodule K N} (hπ : IsPlane BN π) :
    finrank K (concPt hBN ρ π) = 1 :=
  (hs.isSiegelFamily_planeFamily hπ).finrank_axisInf_of_conc hs.nondeg (hconc π hπ)

theorem constLine_of_ne_movedSpace {ℓ : Submodule K N} {g g' : Gsp BN}
    (hg : g ∈ planeGroup hBN ℓ) (hg' : g' ∈ planeGroup hBN ℓ) (hg1 : g ≠ 1) (hg1' : g' ≠ 1)
    (hne : movedSpace (ρ g) ≠ movedSpace (ρ g')) : ConstLine hBN ρ ℓ := by
  have key : ∀ π, IsPlane BN π → ℓ ≤ π →
      concPt hBN ρ π = movedSpace (ρ g) ⊓ movedSpace (ρ g') := by
    intro π hπ hℓπ
    have hA : movedSpace (ρ g) ∈ axes (planeFamily hBN ρ π) :=
      ⟨ρ g, ⟨g, planeGroup_mono hBN hℓπ hg, rfl⟩,
        fun h => hg1 (hs.inj (by rw [h, map_one])), rfl⟩
    have hA' : movedSpace (ρ g') ∈ axes (planeFamily hBN ρ π) :=
      ⟨ρ g', ⟨g', planeGroup_mono hBN hℓπ hg', rfl⟩,
        fun h => hg1' (hs.inj (by rw [h, map_one])), rfl⟩
    have hE := hs.isSiegelFamily_planeFamily hπ
    have h1 := (hE.pair hs.nondeg hA hA' hne).1
    have h2 : concPt hBN ρ π ≤ movedSpace (ρ g) ⊓ movedSpace (ρ g') :=
      le_inf (axisInf_le hA) (axisInf_le hA')
    exact Submodule.eq_of_le_of_finrank_eq h2 (by rw [h1, finrank_concPt hs hconc hπ])
  intro π π' hπ hπ' hℓπ hℓπ'
  rw [key π hπ hℓπ, key π' hπ' hℓπ']

theorem not_constLine {ℓ : Submodule K N} (hℓ : IsLine BN ℓ) : ¬ ConstLine hBN ρ ℓ := by
  intro hc
  have hall : ∀ ℓ', IsLine BN ℓ' → ConstLine hBN ρ ℓ' := by
    intro ℓ' hℓ'
    obtain ⟨g, hg⟩ := exists_gsp_map_eq_of_isLine hBN hs.nondegN hℓ hℓ'
    rw [← hg]
    exact constLine_map hc g
  obtain ⟨π, -, hπ, -, -⟩ := exists_two_planes_through hBN hs.nondegN hs.dimN hℓ
  have hP1 := finrank_concPt hs hconc hπ
  obtain ⟨p, hp0, hpP⟩ := exists_ne_zero_span_eq_of_finrank_eq_one hP1
  have hstab : ∀ g : Gsp BN, ∃ s : K, ρ g p = s • p := by
    intro g
    have h1 : (concPt hBN ρ π).map (ρ g : V →ₗ[K] V) = concPt hBN ρ π := by
      rw [← concPt_map]
      exact concPt_eq_of_forall_constLine hall (hπ.map g) hπ
    have h2 : ρ g p ∈ concPt hBN ρ π := by
      rw [← h1]
      exact Submodule.mem_map_of_mem (hpP ▸ Submodule.mem_span_singleton_self p)
    rw [hpP] at h2
    obtain ⟨s, hs'⟩ := Submodule.mem_span_singleton.mp h2
    exact ⟨s, hs'.symm⟩
  choose c hc' using hstab
  have hcne : ∀ g, c g ≠ 0 := by
    intro g h0
    apply hp0
    have h1 : ρ g p = 0 := by rw [hc' g, h0, zero_smul]
    exact (ρ g).map_eq_zero_iff.mp h1
  have hcmul : ∀ g h, c (g * h) = c g * c h := by
    intro g h
    refine smul_left_injective K hp0 ?_
    show c (g * h) • p = (c g * c h) • p
    rw [← hc' (g * h), map_mul, LinearEquiv.mul_apply, hc' h, map_smul, hc' g, smul_smul,
      mul_comm]
  have : IsSimpleGroup (Gsp BN) :=
    isSimpleGroup_Gsp hs.card hBN hs.nondegN (by have := hs.dimN; omega)
  have hNpos : 0 < finrank K N := by have := hs.dimN; omega
  have : Nontrivial N := Module.nontrivial_of_finrank_pos hNpos
  obtain ⟨e, he⟩ := exists_ne (0 : N)
  obtain ⟨f, hef⟩ : ∃ f : N, BN e f ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact he (hs.nondegN.1 e hcon)
  have hxy := not_commute_Tsp_of_form_ne_zero hBN hs.nondegN hef
  have hc1 : ∀ g, c g = 1 := eq_one_of_mul_char hxy c hcmul hcne
  exact hp0 (hs.fix p fun g => by rw [hc' g, hc1 g, one_smul])

theorem conc_movedSpace_eq_famSpace {ℓ : Submodule K N} (hℓ : IsLine BN ℓ) {g : Gsp BN}
    (hg : g ∈ planeGroup hBN ℓ) (hg1 : g ≠ 1) : movedSpace (ρ g) = famSpace hBN ρ ℓ := by
  refine le_antisymm (movedSpace_le_famSpace hBN ρ hg) ?_
  refine commutatorSpace_le_of_forall_axes_le fun A hA => ?_
  obtain ⟨s, ⟨g', hg', rfl⟩, hs1, rfl⟩ := hA
  have hg1' : g' ≠ 1 := fun h => hs1 (by rw [h, map_one])
  by_contra hne
  exact not_constLine hs hconc hℓ
    (constLine_of_ne_movedSpace hs hconc hg' hg hg1' hg1 (fun h => hne h.le))

theorem concPt_le_famSpace {ℓ π : Submodule K N} (hℓ : IsLine BN ℓ) (hℓπ : ℓ ≤ π) :
    concPt hBN ρ π ≤ famSpace hBN ρ ℓ := by
  obtain ⟨g, hg, hg1⟩ := exists_ne_one_mem_planeGroup hBN hs.nondegN hℓ
  exact (conc_movedSpace_eq_famSpace hs hconc hℓ hg hg1) ▸
    axisInf_le ⟨ρ g, ⟨g, planeGroup_mono hBN hℓπ hg, rfl⟩,
      fun h => hg1 (hs.inj (by rw [h, map_one])), rfl⟩

theorem finrank_famSpace_isLine_conc {ℓ : Submodule K N} (hℓ : IsLine BN ℓ) :
    finrank K (famSpace hBN ρ ℓ) = 2 := by
  obtain ⟨g, hg, hg1⟩ := exists_ne_one_mem_planeGroup hBN hs.nondegN hℓ
  rw [← conc_movedSpace_eq_famSpace hs hconc hℓ hg hg1]
  exact (hs.isLongRootElement_map_of_isLine hℓ hg hg1).finrank_movedSpace hs.nondeg

theorem qf_eq_zero_of_mem_famSpace_isLine_conc {ℓ : Submodule K N} (hℓ : IsLine BN ℓ) :
    ∀ w ∈ famSpace hBN ρ ℓ, Qf w = 0 := by
  obtain ⟨g, hg, hg1⟩ := exists_ne_one_mem_planeGroup hBN hs.nondegN hℓ
  rw [← conc_movedSpace_eq_famSpace hs hconc hℓ hg hg1]
  exact fun w hw => (hs.isLongRootElement_map_of_isLine hℓ hg hg1).qf_eq_zero_of_mem_movedSpace hw

theorem conc_planeFamily_eq_piGroup {ℓ : Submodule K N} (hℓ : IsLine BN ℓ)
    {P : Submodule K V} (hP : finrank K P = 1) (hPA : P ≤ famSpace hBN ρ ℓ) :
    planeFamily hBN ρ ℓ = piGroup Qf P (famSpace hBN ρ ℓ) := by
  have hA2 := finrank_famSpace_isLine_conc hs hconc hℓ
  have hAs := qf_eq_zero_of_mem_famSpace_isLine_conc hs hconc hℓ
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
    · have hax := conc_movedSpace_eq_famSpace hs hconc hℓ hg hg1
      exact isLongRootElement_mem_piGroup (hs.isLongRootElement_map_of_isLine hℓ hg hg1)
        (hax ▸ hPA) hax.le
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hfin : Finite (piGroup Qf P (famSpace hBN ρ ℓ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hcardℓ])

end Conc

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
