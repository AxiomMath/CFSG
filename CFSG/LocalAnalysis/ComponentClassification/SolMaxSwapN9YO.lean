module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9Defs

public section

namespace CFSG.ComponentClassification.SolMax.SwapP2

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

private theorem isSection_of_outer_solvable {S G A : Type} [Group S] [Group G] [Group A]
    [IsSimpleGroup A] (hA : ¬ Group.IsSolvable A)
    (hO : Group.IsSolvable (OuterAutomorphisms.Outer S))
    (ρ : G →* MulAut S) (φ : G →* A) (hφ : Function.Surjective φ) (hker : ρ.ker ≤ φ.ker) :
    ∃ (H : Subgroup S) (f : H →* A), Function.Surjective f := by
  haveI := hO
  set χ : G →* OuterAutomorphisms.Outer S :=
    (QuotientGroup.mk' (OuterAutomorphisms.inner S)).comp ρ with hχ
  have hK : χ.ker.map φ = ⊤ := by
    haveI : (χ.ker.map φ).Normal := Subgroup.Normal.map (MonoidHom.normal_ker χ) φ hφ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (χ.ker.map φ) with h | h
    · exfalso
      have hle : χ.ker ≤ φ.ker := fun g hg => by
        have hmem : φ g ∈ χ.ker.map φ := Subgroup.mem_map_of_mem φ hg
        rw [h, Subgroup.mem_bot] at hmem
        exact MonoidHom.mem_ker.mpr hmem
      have hsolv : Group.IsSolvable (G ⧸ χ.ker) :=
        Group.isSolvable_of_isSolvable_injective (QuotientGroup.kerLift_injective χ)
      let ℓ : G ⧸ χ.ker →* A := QuotientGroup.lift χ.ker φ hle
      have hℓ : Function.Surjective ℓ := by
        intro a
        obtain ⟨g, rfl⟩ := hφ a
        exact ⟨(g : G ⧸ χ.ker), rfl⟩
      exact hA (Group.isSolvable_of_surjective hℓ)
    · exact h
  let Θ : (MonoidHom.range ρ) →* A :=
    (QuotientGroup.lift ρ.ker φ hker).comp
      (QuotientGroup.quotientKerEquivRange ρ).symm.toMonoidHom
  have hΘ : ∀ g : G, Θ ⟨ρ g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ = φ g := by
    intro g
    have h1 : (QuotientGroup.quotientKerEquivRange ρ).symm ⟨ρ g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩
        = (g : G ⧸ ρ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift ρ.ker φ hker
      ((QuotientGroup.quotientKerEquivRange ρ).symm ⟨ρ g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩) = φ g
    rw [h1]
    rfl
  set H : Subgroup S := (MonoidHom.range ρ).comap (MulAut.conj : S →* MulAut S) with hH
  let c : H →* MonoidHom.range ρ :=
    MonoidHom.codRestrict ((MulAut.conj : S →* MulAut S).comp H.subtype) (MonoidHom.range ρ)
      (fun s => s.2)
  refine ⟨H, Θ.comp c, fun a => ?_⟩
  have ha : a ∈ χ.ker.map φ := by
    rw [hK]
    exact Subgroup.mem_top a
  obtain ⟨k, hkK, hka⟩ := Subgroup.mem_map.mp ha
  have hρk : ρ k ∈ (MulAut.conj : S →* MulAut S).range := by
    have h1 : QuotientGroup.mk' (OuterAutomorphisms.inner S) (ρ k) = 1 :=
      MonoidHom.mem_ker.mp hkK
    rw [QuotientGroup.mk'_apply] at h1
    exact (QuotientGroup.eq_one_iff (ρ k)).mp h1
  obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hρk
  have hsH : s ∈ H := by
    rw [hH, Subgroup.mem_comap, hs]
    exact MonoidHom.mem_range.mpr ⟨k, rfl⟩
  refine ⟨⟨s, hsH⟩, ?_⟩
  have hc : c ⟨s, hsH⟩ = ⟨ρ k, MonoidHom.mem_range.mpr ⟨k, rfl⟩⟩ := Subtype.ext hs
  show Θ (c ⟨s, hsH⟩) = a
  rw [hc]
  exact (hΘ k).trans hka

private theorem mem_coreActionKernel_of_perfect_quot {V : Subgroup X}
    (hVq : Group.IsPerfect (↥V ⧸ pPrimeCore 2 ↥V)) {g : X} (hg : g ∈ normalizer (V : Set X))
    (hz : ∀ v ∈ V, v⁻¹ * g⁻¹ * v * g ∈ (Open.fusionZStar ↥V).map V.subtype) :
    g ∈ UnbalancedLayer.coreActionKernel V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine UnbalancedLayer.mem_coreActionKernel.mpr ⟨hg, fun v hv => ?_⟩
  let φ' : MulAut ↥V := V.normalizerMonoidHom ⟨g⁻¹, inv_mem hg⟩
  have hφ' : ∀ u : V, ((φ' u : V) : X) = g⁻¹ * u * g := fun u => by
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
  have hOφ : (pPrimeCore 2 ↥V).map φ'.toMonoidHom = pPrimeCore 2 ↥V :=
    pPrimeCore_map_iso 2 φ'
  let σ : (↥V ⧸ pPrimeCore 2 ↥V) ≃* (↥V ⧸ pPrimeCore 2 ↥V) :=
    QuotientGroup.congr (pPrimeCore 2 ↥V) (pPrimeCore 2 ↥V) φ' hOφ
  have hσ : ∀ u : V, σ (u : ↥V ⧸ pPrimeCore 2 ↥V) = ((φ' u : V) : ↥V ⧸ pPrimeCore 2 ↥V) :=
    fun u => QuotientGroup.congr_mk _ _ _ _ u
  have hcen : ∀ q : ↥V ⧸ pPrimeCore 2 ↥V,
      q⁻¹ * σ.toMonoidHom q ∈ center (↥V ⧸ pPrimeCore 2 ↥V) := by
    intro q
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥V) q
    have h1 : (u : X)⁻¹ * g⁻¹ * u * g ∈ (Open.fusionZStar ↥V).map V.subtype := hz u u.2
    obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.mp h1
    have hw' : w = u⁻¹ * φ' u := Subtype.ext (by
      rw [show ((w : V) : X) = V.subtype w from rfl, hwu, Subgroup.coe_mul, Subgroup.coe_inv, hφ']
      group)
    rw [hw', CFSG.ComponentClassification.Sol78.fusionZStar_eq_comap ↥V, Subgroup.mem_comap] at hw
    have h2 : QuotientGroup.mk' (pPrimeCore 2 ↥V) (u⁻¹ * φ' u) ∈
        center (↥V ⧸ pPrimeCore 2 ↥V) := hw
    rw [map_mul, map_inv] at h2
    show (QuotientGroup.mk' (pPrimeCore 2 ↥V) u)⁻¹ *
      σ (QuotientGroup.mk' (pPrimeCore 2 ↥V) u) ∈ center (↥V ⧸ pPrimeCore 2 ↥V)
    rw [QuotientGroup.mk'_apply, hσ]
    exact h2
  have hid := PerfectAutomorphisms.hom_eq_id_of_central_displacement σ.toMonoidHom hcen
  have h3 : σ ((⟨v, hv⟩ : V) : ↥V ⧸ pPrimeCore 2 ↥V) =
      ((⟨v, hv⟩ : V) : ↥V ⧸ pPrimeCore 2 ↥V) := by
    have := DFunLike.congr_fun hid ((⟨v, hv⟩ : V) : ↥V ⧸ pPrimeCore 2 ↥V)
    exact this
  rw [hσ] at h3
  have h4 : (⟨v, hv⟩ : V)⁻¹ * φ' ⟨v, hv⟩ ∈ pPrimeCore 2 ↥V := QuotientGroup.eq.mp h3.symm
  refine ⟨_, h4, ?_⟩
  rw [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hφ']
  group

section Exotic

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {M : Subgroup X} {e₀ : X} {F : Subgroup X} {DF : Finset (Fin n)} {r : X} {N₁ : Subgroup X}

theorem a9_section_of_action (hS : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    {N₁ G : Subgroup X} (hq : IsQuasisimple (↥N₁ ⧸ pPrimeCore 2 ↥N₁))
    (hcat : Blueprint.Catalog (↥N₁ ⧸ Open.fusionZStar ↥N₁)) (hG : G ≤ normalizer (N₁ : Set X))
    (φ : ↥G →* alternatingGroup (Fin 9)) (hφ : Function.Surjective φ)
    (hker : ∀ g : ↥G, (g : X) ∈ UnbalancedLayer.coreActionKernel N₁ → φ g = 1) :
    FiveCat.IsSectionOf (alternatingGroup (Fin 9)) (↥N₁ ⧸ Open.fusionZStar ↥N₁) := by
  obtain ⟨hperf, hsimpQ, hnabQ⟩ := hq
  have hZ : Open.fusionZStar ↥N₁ =
      (center (↥N₁ ⧸ pPrimeCore 2 ↥N₁)).comap (QuotientGroup.mk' (pPrimeCore 2 ↥N₁)) :=
    CFSG.ComponentClassification.Sol78.fusionZStar_eq_comap ↥N₁
  have hOZ : pPrimeCore 2 ↥N₁ ≤ Open.fusionZStar ↥N₁ := by
    intro x hx
    rw [hZ, Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have hmap : (Open.fusionZStar ↥N₁).map (QuotientGroup.mk' (pPrimeCore 2 ↥N₁)) =
      center (↥N₁ ⧸ pPrimeCore 2 ↥N₁) := by
    rw [hZ]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  let eS : (↥N₁ ⧸ Open.fusionZStar ↥N₁) ≃*
      (↥N₁ ⧸ pPrimeCore 2 ↥N₁) ⧸ center (↥N₁ ⧸ pPrimeCore 2 ↥N₁) :=
    (QuotientGroup.quotientQuotientEquivQuotient (pPrimeCore 2 ↥N₁) (Open.fusionZStar ↥N₁)
      hOZ).symm.trans (QuotientGroup.quotientMulEquivOfEq hmap)
  haveI hSimpS : IsSimpleGroup (↥N₁ ⧸ Open.fusionZStar ↥N₁) := eS.isSimpleGroup
  have hnabS : ∃ a b : ↥N₁ ⧸ Open.fusionZStar ↥N₁, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnabQ
    refine ⟨eS.symm a, eS.symm b, fun h => hab ?_⟩
    have h' := congrArg eS h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h'
  have hO : Group.IsSolvable (OuterAutomorphisms.Outer (↥N₁ ⧸ Open.fusionZStar ↥N₁)) :=
    hS _ hnabS hcat
  let actG : ↥G →* MulAut ↥N₁ := N₁.normalizerMonoidHom.comp (Subgroup.inclusion hG)
  let zA : MulAut ↥N₁ →* MulAut (↥N₁ ⧸ Open.fusionZStar ↥N₁) :=
    { toFun := fun σ => QuotientGroup.congr (Open.fusionZStar ↥N₁) (Open.fusionZStar ↥N₁) σ
        (Subgroup.characteristic_iff_map_eq.mp
          (CFSG.ComponentClassification.SolMax.fusionZStar_characteristic ↥N₁) σ)
      map_one' := by
        refine MulEquiv.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | H y => rfl
      map_mul' := fun σ τ => by
        refine MulEquiv.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | H y => rfl }
  let ρ : ↥G →* MulAut (↥N₁ ⧸ Open.fusionZStar ↥N₁) := zA.comp actG
  have hker' : ρ.ker ≤ φ.ker := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    apply hker g
    have hρ : zA (actG g) = 1 := hg
    have hgN : (g : X) ∈ normalizer (N₁ : Set X) := hG g.2
    have hz : ∀ v ∈ N₁, v⁻¹ * (g : X)⁻¹⁻¹ * v * (g : X)⁻¹ ∈
        (Open.fusionZStar ↥N₁).map N₁.subtype := by
      intro v hv
      have h1 : zA (actG g) (QuotientGroup.mk (⟨v, hv⟩ : ↥N₁)) =
          QuotientGroup.mk (⟨v, hv⟩ : ↥N₁) := by
        rw [hρ, MulAut.one_apply]
      have h2 : QuotientGroup.mk (actG g ⟨v, hv⟩) =
          (QuotientGroup.mk (⟨v, hv⟩ : ↥N₁) : ↥N₁ ⧸ Open.fusionZStar ↥N₁) := h1
      have h3 : (⟨v, hv⟩ : ↥N₁)⁻¹ * actG g ⟨v, hv⟩ ∈ Open.fusionZStar ↥N₁ :=
        QuotientGroup.eq.mp h2.symm
      have h4 := Subgroup.mem_map_of_mem N₁.subtype h3
      have h5 : N₁.subtype ((⟨v, hv⟩ : ↥N₁)⁻¹ * actG g ⟨v, hv⟩) =
          v⁻¹ * ((g : X) * v * (g : X)⁻¹) := by
        simp [actG, Subgroup.normalizerMonoidHom_apply_apply_coe]
      rw [h5] at h4
      have h6 : v⁻¹ * (g : X)⁻¹⁻¹ * v * (g : X)⁻¹ = v⁻¹ * ((g : X) * v * (g : X)⁻¹) := by
        group
      rw [h6]
      exact h4
    have hmem := mem_coreActionKernel_of_perfect_quot hperf (inv_mem hgN) hz
    simpa using inv_mem hmem
  have hA : ¬ Group.IsSolvable (alternatingGroup (Fin 9)) := by
    haveI : IsSimpleGroup (alternatingGroup (Fin 9)) := alternatingGroup.isSimpleGroup (by simp)
    haveI : Group.IsPerfect (alternatingGroup (Fin 9)) :=
      Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 9))
  haveI : IsSimpleGroup (alternatingGroup (Fin 9)) := alternatingGroup.isSimpleGroup (by simp)
  exact isSection_of_outer_solvable hA hO ρ φ hφ hker'

end Exotic

end CFSG.ComponentClassification.SolMax.SwapP2
