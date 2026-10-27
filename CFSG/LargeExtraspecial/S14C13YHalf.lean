module

public import CFSG.LargeExtraspecial.S14C13YLin
public import CFSG.LargeExtraspecial.S2SixInd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V} {hq : q.polarBilin.Nondegenerate}
  {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]

namespace Half8

variable {ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M)} {p p₁ : V}

omit [FiniteDimensional (ZMod 2) M] in
theorem exists_ne_of_sym3 {A B : M →ₗ[ZMod 2] M} (hA2 : ∀ v, A (A v) = v)
    (hB2 : ∀ v, B (B v) = v) (hAB3 : ∀ v, A (B (A (B (A (B v))))) = v)
    (hAB1 : ∃ v, A (B v) ≠ v) : (∃ v, A v ≠ v) ∧ ∃ v, B v ≠ v := by
  obtain ⟨v, hv⟩ := hAB1
  constructor
  · by_contra hcon
    have hA : ∀ w, A w = w := fun w => by
      by_contra hw
      exact hcon ⟨w, hw⟩
    have h3 := hAB3 v
    simp only [hA] at h3
    rw [hB2] at h3
    exact hv (by rw [hA, h3])
  · by_contra hcon
    have hB : ∀ w, B w = w := fun w => by
      by_contra hw
      exact hcon ⟨w, hw⟩
    have h3 := hAB3 v
    simp only [hB] at h3
    rw [hA2] at h3
    exact hv (by rw [hB, h3])

theorem range_inf_range (h : Half8 ρ p p₁) {A B : M →ₗ[ZMod 2] M}
    (hA : ∀ g v, A (ρ g v) = ρ g (A v)) (hB : ∀ g v, B (ρ g v) = ρ g (B v))
    (hA2 : ∀ v, A (A v) = v) (hB2 : ∀ v, B (B v) = v)
    (hAB3 : ∀ v, A (B (A (B (A (B v))))) = v) (hAB1 : ∃ v, A (B v) ≠ v) :
    LinearMap.range (A - LinearMap.id) ⊓ LinearMap.range (B - LinearMap.id) = ⊥ := by
  obtain ⟨hA1, hB1⟩ := exists_ne_of_sym3 hA2 hB2 hAB3 hAB1
  have hU := h.finrank_range hA hA2 hA1
  have hU' := h.finrank_range hB hB2 hB1
  have h8 := h.dvd_finrank
    (omegaInvariant_inf (omegaInvariant_range (comm_sub hA)) (omegaInvariant_range (comm_sub hB)))
    (CompClosed.inf (h.compClosed_range (comm_sub hA)) (h.compClosed_range (comm_sub hB)))
  have hle := Submodule.finrank_mono (inf_le_left : LinearMap.range (A - LinearMap.id) ⊓
    LinearMap.range (B - LinearMap.id) ≤ LinearMap.range (A - LinearMap.id))
  rw [hU] at hle
  generalize hd : finrank (ZMod 2) ↥(LinearMap.range (A - LinearMap.id) ⊓
    LinearMap.range (B - LinearMap.id)) = d at h8 hle
  rcases (by omega : d = 0 ∨ d = 8) with rfl | rfl
  · exact Submodule.finrank_eq_zero.mp hd
  exfalso
  have e1 := Submodule.eq_of_le_of_finrank_eq inf_le_left (hd.trans hU.symm)
  have e2 := Submodule.eq_of_le_of_finrank_eq inf_le_right (hd.trans hU'.symm)
  have hBU : ∀ v, B v - v ∈ LinearMap.range (A - LinearMap.id) := fun v => by
    rw [← e1, e2]
    exact ⟨v, by simp⟩
  have hAU : ∀ v, A v - v ∈ LinearMap.range (B - LinearMap.id) := fun v => by
    rw [← e2, e1]
    exact ⟨v, by simp⟩
  have k1 : ∀ v, A (B v) = A v + B v - v := fun v => by
    have := apply_eq_of_mem_range hA2 (hBU v)
    rw [map_sub, sub_eq_iff_eq_add] at this
    rw [this]
    abel
  have k2 : ∀ v, B (A v) = A v + B v - v := fun v => by
    have := apply_eq_of_mem_range hB2 (hAU v)
    rw [map_sub, sub_eq_iff_eq_add] at this
    rw [this]
    abel
  have k3 : ∀ v, A (B (A (B v))) = v := fun v => by
    rw [k1 (A (B v)), hA2, k2 (B v), hB2]
    abel
  obtain ⟨v, hv⟩ := hAB1
  apply hv
  have := hAB3 v
  rwa [k3] at this

theorem range_sup_range (h : Half8 ρ p p₁) {A B : M →ₗ[ZMod 2] M}
    (hA : ∀ g v, A (ρ g v) = ρ g (A v)) (hB : ∀ g v, B (ρ g v) = ρ g (B v))
    (hA2 : ∀ v, A (A v) = v) (hB2 : ∀ v, B (B v) = v)
    (hAB3 : ∀ v, A (B (A (B (A (B v))))) = v) (hAB1 : ∃ v, A (B v) ≠ v) :
    LinearMap.range (A - LinearMap.id) ⊔ LinearMap.range (B - LinearMap.id) = ⊤ := by
  obtain ⟨hA1, hB1⟩ := exists_ne_of_sym3 hA2 hB2 hAB3 hAB1
  have hs := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (A - LinearMap.id))
    (LinearMap.range (B - LinearMap.id))
  rw [h.range_inf_range hA hB hA2 hB2 hAB3 hAB1, finrank_bot, add_zero,
    h.finrank_range hA hA2 hA1, h.finrank_range hB hB2 hB1] at hs
  exact Submodule.eq_top_of_finrank_eq (hs.trans h.dimM.symm)

theorem eq_on_range (h : Half8 ρ p p₁) {C φ : M →ₗ[ZMod 2] M}
    (hC : ∀ g v, C (ρ g v) = ρ g (C v)) (hC2 : ∀ v, C (C v) = v) (hC1 : ∃ v, C v ≠ v)
    (hφ : ∀ g v, φ (ρ g v) = ρ g (φ v)) (hφC : ∀ v, φ (C v) = C (φ v))
    (hinj : Function.Injective φ) : ∀ u ∈ LinearMap.range (C - LinearMap.id), φ u = u := by
  have hU := h.finrank_range hC hC2 hC1
  have hφU : ∀ v ∈ LinearMap.range (C - LinearMap.id),
      φ v ∈ LinearMap.range (C - LinearMap.id) := by
    rintro _ ⟨w, rfl⟩
    exact ⟨φ w, by simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, hφC]⟩
  obtain ⟨c, hc⟩ := S2.timmesfeld_2_6_1_omega ρ 4 (bot_inf_eq _) (by norm_num)
    (by rw [S2.perp_bot, finrank_top]; exact h.dimV) (omegaInvariant_range (comm_sub hC))
    (mem_perp_bot p) (mem_perp_bot p₁) h.ne_zero h.sing h.sing₁ h.polar_eq
    (h.radDecomp (h.compClosed_range (comm_sub hC))) (hU.trans (by norm_num)) φ hφU
    (fun g _ v _ => hφ g v)
  have hne : LinearMap.range (C - LinearMap.id) ≠ ⊥ := fun hb => by
    rw [hb, finrank_bot] at hU
    exact absurd hU (by norm_num)
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rcases OrthoF2.zmod2_eq_zero_or_eq_one c with rfl | rfl
  · exfalso
    have h0 := hc u hu
    rw [zero_smul] at h0
    exact hu0 (hinj (h0.trans (map_zero φ).symm))
  · intro v hv
    rw [hc v hv, one_smul]

theorem eq_id (h : Half8 ρ p p₁) {A B φ : M →ₗ[ZMod 2] M}
    (hA : ∀ g v, A (ρ g v) = ρ g (A v)) (hB : ∀ g v, B (ρ g v) = ρ g (B v))
    (hA2 : ∀ v, A (A v) = v) (hB2 : ∀ v, B (B v) = v)
    (hAB3 : ∀ v, A (B (A (B (A (B v))))) = v) (hAB1 : ∃ v, A (B v) ≠ v)
    (hφ : ∀ g v, φ (ρ g v) = ρ g (φ v)) (hφA : ∀ v, φ (A v) = A (φ v))
    (hφB : ∀ v, φ (B v) = B (φ v)) (hinj : Function.Injective φ) : ∀ v, φ v = v := by
  obtain ⟨hA1, hB1⟩ := exists_ne_of_sym3 hA2 hB2 hAB3 hAB1
  intro v
  have hv : v ∈ LinearMap.range (A - LinearMap.id) ⊔ LinearMap.range (B - LinearMap.id) := by
    rw [h.range_sup_range hA hB hA2 hB2 hAB3 hAB1]
    exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, h.eq_on_range hA hA2 hA1 hφ hφA hinj x hx,
    h.eq_on_range hB hB2 hB1 hφ hφB hinj y hy]

theorem inner (h : Half8 ρ p p₁) {A : M →ₗ[ZMod 2] M} (hA : ∀ g v, A (ρ g v) = ρ g (A v))
    (hA2 : ∀ v, A (A v) = v) (hA1 : ∃ v, A v ≠ v) (α : omegaGroup q hq ≃* omegaGroup q hq)
    (hαL : ∀ g : omegaGroup q hq, (g : V ≃ₗ[ZMod 2] V) ∈ pointRadical q p ↔
      (α g : V ≃ₗ[ZMod 2] V) ∈ pointRadical q p)
    (τ : M ≃ₗ[ZMod 2] M) (hτ : ∀ g v, τ (ρ g v) = ρ (α g) (τ v))
    (hτA : ∀ v, τ (A v) = A (τ v)) : ∃ x : omegaGroup q hq, ∀ g, α g = x * g * x⁻¹ := by
  have hα : S2.IsAutOn (⊥ : Submodule (ZMod 2) V) (α : omegaGroup q hq → omegaGroup q hq) :=
    { mem := fun g _ => mem_fixGroup_bot _
      map_mul := fun g k _ _ => map_mul α g k
      inj := fun g k _ _ e => α.injective e
      surj := fun k _ => ⟨α.symm k, mem_fixGroup_bot _, α.apply_symm_apply k⟩ }
  have hαp : S2.MapsRad (⊥ : Submodule (ZMod 2) V) (α : omegaGroup q hq → omegaGroup q hq)
      p p := by
    intro g _
    rw [S2.radFix_bot]
    exact hαL g
  have hτ' : S2.Realizes ρ ⊥ (LinearMap.range (A - LinearMap.id))
      (α : omegaGroup q hq → omegaGroup q hq) (τ : M →ₗ[ZMod 2] M) := by
    refine ⟨?_, fun v _ h0 => τ.map_eq_zero_iff.mp h0, fun g _ v _ => hτ g v⟩
    rintro _ ⟨w, rfl⟩
    exact ⟨τ w, by
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, map_sub, hτA]⟩
  obtain ⟨x, -, hx⟩ := S2.timmesfeld_2_6_2_rel ρ 4 (bot_inf_eq _) (by norm_num)
    (by rw [S2.perp_bot, finrank_top]; exact h.dimV) (omegaInvariant_range (comm_sub hA))
    (mem_perp_bot p) (mem_perp_bot p₁) h.ne_zero h.sing h.sing₁ h.polar_eq
    (h.radDecomp (h.compClosed_range (comm_sub hA)))
    ((h.finrank_range hA hA2 hA1).trans (by norm_num)) hα hαp hτ'
  exact ⟨x, fun g => hx g (mem_fixGroup_bot _)⟩

end Half8

end CFSG.LargeExtraspecial.S14
