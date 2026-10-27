module

public import CFSG.LargeExtraspecial.S9Mod

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Module CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial.OrthoF2
open CFSG.LargeExtraspecial.S2
open LinearMap (BilinForm)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {f : BilinForm (ZMod 2) V}
variable [FiniteDimensional (ZMod 2) V]
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

omit [FiniteDimensional (ZMod 2) V] in
theorem spTv_mem_spRadFix (hf : f.IsAlt) {F : Submodule (ZMod 2) V} {c : V}
    (hc : c ∈ spPerp f F) : ((spTv hf c : TauCeti.BilinForm.isometryGroup f) :
      V ≃ₗ[ZMod 2] V) ∈ spRadFix f F c := by
  refine ⟨spTransvection_mem_spPointRadical hf c, ?_⟩
  change _ ∈ fixGroup F
  rw [mem_fixGroup]
  intro v hv
  rw [coe_spTv, spTransvection_apply, (mem_spPerp.mp hc) v hv, zero_smul, add_zero]

variable [FiniteDimensional (ZMod 2) M] (ρ : TauCeti.BilinForm.isometryGroup f →* (M ≃ₗ[ZMod 2] M))

theorem exists_levi_pair (hf : f.IsAlt) (hnd : f.Nondegenerate)
    (hdim : finrank (ZMod 2) V = 4) {p p₁ : V} (hpp₁ : f p p₁ = 1)
    (hD : SpRadDecomp ρ ⊥ ⊤ p p₁) :
    ∃ x y : TauCeti.BilinForm.isometryGroup f, (x : V ≃ₗ[ZMod 2] V) p = p ∧
      (y : V ≃ₗ[ZMod 2] V) p = p ∧ x * x = 1 ∧ y * y = 1 ∧
      ∀ v ∈ fixOf ρ (spPointRadical f p : Set (V ≃ₗ[ZMod 2] V)), ρ x v = v → ρ y v = v →
        v = 0 := by
  have hbot : (⊥ : Submodule (ZMod 2) V) ⊓ spPerp f ⊥ = ⊥ := bot_inf_eq _
  have hpF : p ∈ spPerp f ⊥ := by rw [spPerp_bot]; exact Submodule.mem_top
  have hp₁F : p₁ ∈ spPerp f ⊥ := by rw [spPerp_bot]; exact Submodule.mem_top
  have hdim' : finrank (ZMod 2) (spPerp f (⊥ : Submodule (ZMod 2) V)) = 2 * 2 := by
    rw [spPerp_bot, finrank_top, hdim]
  set K := (⊥ : Submodule (ZMod 2) V) ⊔ Submodule.span (ZMod 2) {p, p₁} with hKdef
  have hK : K ⊓ spPerp f K = ⊥ := sup_span_pair_inf_spPerp_eq_bot hf hbot hpF hp₁F hpp₁
  have hKdim : finrank (ZMod 2) (spPerp f K) = 2 * 1 := by
    have := finrank_spPerp_sup_span_pair hf hnd hbot hpF hp₁F hpp₁
    rw [hdim', ← hKdef] at this
    omega
  have hne : spPerp f K ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hKdim
    exact absurd hKdim (by norm_num)
  obtain ⟨p', hp'K, hp'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨p₁', hp₁'K, hpp₁'⟩ := sp_exists_partner hf hnd hK hp'K hp'0
  obtain ⟨-, hp₁'0, -⟩ :=
    linearIndependent_pair_iff.mp (linearIndependent_of_apply_eq_one hf hpp₁')
  have hN : SpInvariant ρ ⊥ (⊤ : Submodule (ZMod 2) M) := fun _ _ _ _ => Submodule.mem_top
  obtain ⟨hW, hDW⟩ := sp_timmesfeld_2_1_b2 ρ hf hnd hbot hdim' hN hpF hp₁F hpp₁ hD hp'K hp₁'K
    hpp₁'
  have hpK : p ∈ K := Submodule.mem_sup_right (Submodule.subset_span (by simp))
  have hfix : ∀ {c : V}, c ∈ spPerp f K → ((spTv hf c : TauCeti.BilinForm.isometryGroup f) :
      V ≃ₗ[ZMod 2] V) p = p := fun hc => by
    rw [coe_spTv, spTransvection_apply, (mem_spPerp.mp hc) p hpK, zero_smul, add_zero]
  refine ⟨spTv hf p₁', spTv hf p', hfix hp₁'K, hfix hp'K, spTv_mul_self hf p₁',
    spTv_mul_self hf p', fun v hv hx hy => ?_⟩
  have hvW : v ∈ ⊤ ⊓ fixOf ρ (spRadFix f ⊥ p : Set (V ≃ₗ[ZMod 2] V)) := by
    rw [spRadFix_bot]
    exact ⟨Submodule.mem_top, hv⟩
  have hb0x := (sp_timmesfeld_2_1_b0 ρ hf hnd hK hKdim hW hp'K hp₁'K hpp₁' hDW (spTv hf p₁')
    (spTv_mem_spRadFix hf hp₁'K) (by rw [coe_spTv]; exact spTransvection_ne_one hf hnd hp₁'0)
    (not_isSpTypeA_spTransvection hf p₁')).1
  have hp₁'p : f p₁' p' = 1 := by rw [isAlt_symm hf, hpp₁']
  have hb0y := (sp_timmesfeld_2_1_b0 ρ hf hnd hK hKdim hW hp₁'K hp'K hp₁'p hDW.symm (spTv hf p')
    (spTv_mem_spRadFix hf hp'K) (by rw [coe_spTv]; exact spTransvection_ne_one hf hnd hp'0)
    (not_isSpTypeA_spTransvection hf p')).1
  have h1 : v ∈ (⊤ ⊓ fixOf ρ (spRadFix f ⊥ p : Set (V ≃ₗ[ZMod 2] V))) ⊓
      fixOf ρ (spRadFix f K p₁' : Set (V ≃ₗ[ZMod 2] V)) := by
    rw [← hb0x]
    exact ⟨hvW, mem_fixSpace.mpr hx⟩
  have h2 : v ∈ (⊤ ⊓ fixOf ρ (spRadFix f ⊥ p : Set (V ≃ₗ[ZMod 2] V))) ⊓
      fixOf ρ (spRadFix f K p' : Set (V ≃ₗ[ZMod 2] V)) := by
    rw [← hb0y]
    exact ⟨hvW, mem_fixSpace.mpr hy⟩
  have h3 := hDW.2
  have h4 : v ∈ ((⊤ ⊓ fixOf ρ (spRadFix f ⊥ p : Set (V ≃ₗ[ZMod 2] V))) ⊓
      fixOf ρ (spRadFix f K p' : Set (V ≃ₗ[ZMod 2] V))) ⊓
        ((⊤ ⊓ fixOf ρ (spRadFix f ⊥ p : Set (V ≃ₗ[ZMod 2] V))) ⊓
          fixOf ρ (spRadFix f K p₁' : Set (V ≃ₗ[ZMod 2] V))) := ⟨h2, h1⟩
  rw [h3, Submodule.mem_bot] at h4
  exact h4

omit [FiniteDimensional (ZMod 2) V] in
theorem eq_of_commute_levi {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] {U : Submodule (ZMod 2) E} (hU : finrank (ZMod 2) U = 2)
    (X Y : E → E) (φ : E →ₗ[ZMod 2] E) (hX0 : X 0 = 0) (hY0 : Y 0 = 0)
    (hXU : ∀ u ∈ U, X u ∈ U) (hYU : ∀ u ∈ U, Y u ∈ U) (hφU : ∀ u ∈ U, φ u ∈ U)
    (hXX : ∀ u ∈ U, X (X u) = u) (hYY : ∀ u ∈ U, Y (Y u) = u) (hφφ : ∀ u ∈ U, φ (φ u) = u)
    (hφX : ∀ u ∈ U, φ (X u) = X (φ u)) (hφY : ∀ u ∈ U, φ (Y u) = Y (φ u))
    (hXY : ∀ u ∈ U, X u = u → Y u = u → u = 0) : ∀ u ∈ U, φ u = u := by
  by_contra hne
  push Not at hne
  obtain ⟨u₀, hu₀U, hu₀⟩ := hne
  set k := φ u₀ + u₀ with hk
  have hkU : k ∈ U := add_mem (hφU u₀ hu₀U) hu₀U
  have hk0 : k ≠ 0 := by
    intro h0
    apply hu₀
    have : φ u₀ = -u₀ := eq_neg_of_add_eq_zero_left h0
    rw [this, ZModModule.neg_eq_self]
  have hφk : φ k = k := by rw [hk, map_add, hφφ u₀ hu₀U, add_comm]
  have hline : ∀ v ∈ U, φ v = v → v ≠ 0 → v = k := by
    intro v hvU hφv hv0
    by_contra hvk
    have hind : LinearIndependent (ZMod 2) ![k, v] :=
      linearIndependent_pair_iff.mpr ⟨hk0, hv0, Ne.symm hvk⟩
    have hspan : Submodule.span (ZMod 2) (Set.range ![k, v]) = U := by
      refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact hkU
        · exact hvU
      · rw [finrank_span_eq_card hind, hU, Fintype.card_fin]
    have hu₀span : u₀ ∈ Submodule.span (ZMod 2) (Set.range ![k, v]) := hspan ▸ hu₀U
    have hfix : ∀ w ∈ Submodule.span (ZMod 2) (Set.range ![k, v]), φ w = w := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨i, rfl⟩ := hw
        fin_cases i
        · exact hφk
        · exact hφv
      | zero => exact map_zero φ
      | add a b _ _ ha hb => rw [map_add, ha, hb]
      | smul c a _ ha => rw [map_smul, ha]
    exact hu₀ (hfix u₀ hu₀span)
  have hXk : X k = k := by
    refine hline (X k) (hXU k hkU) (by rw [hφX k hkU, hφk]) fun h0 => hk0 ?_
    rw [← hXX k hkU, h0, hX0]
  have hYk : Y k = k := by
    refine hline (Y k) (hYU k hkU) (by rw [hφY k hkU, hφk]) fun h0 => hk0 ?_
    rw [← hYY k hkU, h0, hY0]
  exact hk0 (hXY k hkU hXk hYk)

end CFSG.LargeExtraspecial.S9
