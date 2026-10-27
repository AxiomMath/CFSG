module

public import CFSG.GroupTheory.CentralLiftCommutator
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.FixedSpace
public import Mathlib.RepresentationTheory.Invariants

public section

namespace CFSG.LinearAlgebra

open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
open scoped Pointwise

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def movedSpan (T : Subgroup (V ≃ₗ[K] V)) : Submodule K V :=
  Submodule.span K {w : V | ∃ t ∈ T, ∃ u : V, w = t u - u}

theorem apply_mem_movedSpan_of_commute {T : Subgroup (V ≃ₗ[K] V)} {g : V ≃ₗ[K] V}
    (hc : ∀ t ∈ T, g * t = t * g) :
    ∀ v ∈ movedSpan T, g v ∈ movedSpan T := by
  have hspan : movedSpan T ≤
      Submodule.comap (g : V →ₗ[K] V) (movedSpan T) := by
    rw [movedSpan, Submodule.span_le]
    rintro w ⟨t, ht, u, rfl⟩
    refine Submodule.subset_span ⟨t, ht, g u, ?_⟩
    calc g (t u - u) = g (t u) - g u := map_sub g (t u) u
      _ = t (g u) - g u := by
        rw [show g (t u) = t (g u) from by
          calc g (t u) = (g * t) u := (LinearEquiv.mul_apply g t u).symm
            _ = (t * g) u := by rw [hc t ht]
            _ = t (g u) := LinearEquiv.mul_apply t g u]
  exact hspan

section Averaging

variable (T : Subgroup (V ≃ₗ[K] V)) [Fintype T]

theorem isCompl_movedSpan_fixSub (hcard : (Fintype.card T : K) ≠ 0) :
    IsCompl (movedSpan T) (fixSub T) := by
  classical
  let ρ : Representation K T V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp T.subtype
  haveI : Invertible (Fintype.card T : K) := invertibleOfNonzero hcard
  have havg : ∀ v : V, Representation.averageMap ρ v =
      (Fintype.card T : K)⁻¹ • ∑ t : T, (t : V ≃ₗ[K] V) v := by
    intro v
    simp [Representation.averageMap, GroupAlgebra.average, ρ, Finset.smul_sum]
  have hinv : Representation.invariants ρ = fixSub T := by
    ext v
    rw [Representation.mem_invariants, mem_fixSub]
    exact ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g g.2⟩
  have hmoved_le_ker : movedSpan T ≤ LinearMap.ker (Representation.averageMap ρ) := by
    rw [movedSpan, Submodule.span_le]
    rintro w ⟨t, ht, u, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub]
    have hmul : Representation.averageMap ρ ((t : V ≃ₗ[K] V) u) =
        Representation.averageMap ρ u := by
      rw [havg, havg]
      congr 1
      exact Fintype.sum_equiv (Equiv.mulRight (⟨t, ht⟩ : T))
        (fun g : T => (g : V ≃ₗ[K] V) ((t : V ≃ₗ[K] V) u))
        (fun g : T => (g : V ≃ₗ[K] V) u) (fun g => rfl)
    rw [hmul, sub_self]
  have hker_le : LinearMap.ker (Representation.averageMap ρ) ≤ movedSpan T := by
    intro v hv
    have hv0 : Representation.averageMap ρ v = 0 := LinearMap.mem_ker.mp hv
    have hsum : (∑ t : T, ((t : V ≃ₗ[K] V) v - v)) ∈ movedSpan T := by
      refine Submodule.sum_mem _ (fun t _ => Submodule.subset_span ⟨t, t.2, v, rfl⟩)
    have hform : v - Representation.averageMap ρ v =
        -((Fintype.card T : K)⁻¹ • ∑ t : T, ((t : V ≃ₗ[K] V) v - v)) := by
      rw [havg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        ← Nat.cast_smul_eq_nsmul K]
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hcard, one_smul]
      abel
    have hveq : v = -((Fintype.card T : K)⁻¹ • ∑ t : T, ((t : V ≃ₗ[K] V) v - v)) := by
      rw [← hform, hv0, sub_zero]
    rw [hveq]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hsum)
  have hker : LinearMap.ker (Representation.averageMap ρ) = movedSpan T :=
    le_antisymm hker_le hmoved_le_ker
  have h := (Representation.isProj_averageMap ρ).isCompl
  rw [hinv, hker] at h
  exact h.symm

theorem movedSpan_eq_of_isCompl_fixSub (hcard : (Fintype.card T : K) ≠ 0)
    {W W' : Submodule K V} (hcompl : IsCompl W W')
    (hW : ∀ t ∈ T, ∀ w ∈ W, t w ∈ W)
    (hW' : ∀ t ∈ T, ∀ w ∈ W', t w = w)
    (hinf : W ⊓ fixSub T = ⊥) :
    movedSpan T = W ∧ fixSub T = W' := by
  have hU_le_W : movedSpan T ≤ W := by
    rw [movedSpan, Submodule.span_le]
    rintro w ⟨t, ht, u, rfl⟩
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ :=
      Submodule.mem_sup.mp (hcompl.sup_eq_top ▸ (Submodule.mem_top : u ∈ (⊤ : Submodule K V)))
    have h1 : t u₁ ∈ W := hW t ht u₁ hu₁
    have h2 : t u₂ = u₂ := hW' t ht u₂ hu₂
    have hsub : t (u₁ + u₂) - (u₁ + u₂) = t u₁ - u₁ := by
      rw [map_add, h2]
      abel
    rw [hsub]
    exact Submodule.sub_mem _ h1 hu₁
  have hcomplU : IsCompl (movedSpan T) (fixSub T) := isCompl_movedSpan_fixSub T hcard
  have hW_le_U : W ≤ movedSpan T := by
    intro w hw
    obtain ⟨u, hu, c, hc, huc⟩ := Submodule.mem_sup.mp
      (hcomplU.sup_eq_top ▸ (Submodule.mem_top : w ∈ (⊤ : Submodule K V)))
    have hcW : c ∈ W := by
      have : c = w - u := by rw [← huc]; abel
      rw [this]
      exact Submodule.sub_mem _ hw (hU_le_W hu)
    have hc0 : c = 0 := by
      have : c ∈ W ⊓ fixSub T := ⟨hcW, hc⟩
      rwa [hinf] at this
    rw [← huc, hc0, add_zero]
    exact hu
  have hW'le : W' ≤ fixSub T := by
    intro w hw
    exact mem_fixSub.mpr (fun t ht => hW' t ht w hw)
  have hfix_le_W' : fixSub T ≤ W' := by
    intro c hc
    obtain ⟨w, hw, w', hw', hww'⟩ := Submodule.mem_sup.mp
      (hcompl.sup_eq_top ▸ (Submodule.mem_top : c ∈ (⊤ : Submodule K V)))
    have hw'fix : w' ∈ fixSub T := hW'le hw'
    have hwfix : w ∈ fixSub T := by
      have : w = c - w' := by rw [← hww']; abel
      rw [this]
      exact Submodule.sub_mem _ hc hw'fix
    have hw0 : w = 0 := by
      have : w ∈ W ⊓ fixSub T := ⟨hw, hwfix⟩
      rwa [hinf] at this
    rw [← hww', hw0, zero_add]
    exact hw'
  exact ⟨le_antisymm hU_le_W hW_le_U, le_antisymm hfix_le_W' hW'le⟩

theorem commutator_commute_of_scalar_on_movedSpan (hcard : (Fintype.card T : K) ≠ 0)
    {S₁ : Subgroup (V ≃ₗ[K] V)} {x : V ≃ₗ[K] V} {c : K}
    (hcent : ∀ s ∈ S₁, ∀ t ∈ T, Commute s t)
    (hxT : ∀ t ∈ T, Commute x t)
    (hx : ∀ u ∈ movedSpan T, x u = c • u) :
    ∀ g ∈ ⁅S₁, Subgroup.zpowers x⁆, ∀ h : V ≃ₗ[K] V,
      (∀ w ∈ fixSub T, h w = w) → (∀ w ∈ movedSpan T, h w ∈ movedSpan T) →
      Commute g h := by
  have hS₁_pres : ∀ s ∈ S₁,
      Submodule.map (s : V →ₗ[K] V) (movedSpan T) = movedSpan T := by
    intro s hs
    refine le_antisymm ?_ ?_
    · rw [Submodule.map_le_iff_le_comap]
      exact apply_mem_movedSpan_of_commute (fun t ht => (hcent s hs t ht).eq)
    · intro u hu
      have hc : ∀ t ∈ T, s⁻¹ * t = t * s⁻¹ :=
        fun t ht => (hcent s hs t ht).inv_left.eq
      have h1 : s⁻¹ u ∈ movedSpan T := apply_mem_movedSpan_of_commute hc u hu
      exact ⟨s⁻¹ u, h1, by simp⟩
  have hgU : ∀ g ∈ ⁅S₁, Subgroup.zpowers x⁆, ∀ u ∈ movedSpan T, g u = u :=
    CFSG.GroupTheory.commutator_apply_eq_self_of_mapsTo_of_eq_smul hS₁_pres hx
  have hS₁_stab : S₁ ≤ MulAction.stabilizer (V ≃ₗ[K] V) (fixSub T) := by
    intro s hs
    rw [Submodule.mem_stabilizer_submodule_iff_map_eq]
    refine le_antisymm ?_ ?_
    · rintro w ⟨u, hu, rfl⟩
      exact apply_mem_fixSub_of_commute (E := T) (g := s)
        (fun t ht => (hcent s hs t ht).eq) hu
    · intro w hw
      have hc : ∀ t ∈ T, Commute s⁻¹ t := fun t ht => (hcent s hs t ht).inv_left
      have h1 : s⁻¹ w ∈ fixSub T := apply_mem_fixSub_of_commute (E := T) (g := s⁻¹) hc hw
      exact ⟨s⁻¹ w, h1, by simp⟩
  have hx_stab : Subgroup.zpowers x ≤ MulAction.stabilizer (V ≃ₗ[K] V) (fixSub T) := by
    rw [Subgroup.zpowers_le, Submodule.mem_stabilizer_submodule_iff_map_eq]
    refine le_antisymm ?_ ?_
    · rintro w ⟨u, hu, rfl⟩
      exact apply_mem_fixSub_of_commute (E := T) (g := x) (fun t ht => (hxT t ht).eq) hu
    · intro w hw
      have hc : ∀ t ∈ T, Commute x⁻¹ t := fun t ht => (hxT t ht).inv_left
      have h1 : x⁻¹ w ∈ fixSub T := apply_mem_fixSub_of_commute (E := T) (g := x⁻¹) hc hw
      exact ⟨x⁻¹ w, h1, by simp⟩
  have hS₂_stab : ⁅S₁, Subgroup.zpowers x⁆ ≤
      MulAction.stabilizer (V ≃ₗ[K] V) (fixSub T) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have ha' := hS₁_stab ha
    have hb' := hx_stab hb
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha' hb') (Subgroup.inv_mem _ ha'))
      (Subgroup.inv_mem _ hb')
  intro g hg h hhW hhU
  have hgW : ∀ w ∈ fixSub T, g w ∈ fixSub T := by
    intro w hw
    have h := hS₂_stab hg
    rw [Submodule.mem_stabilizer_submodule_iff_map_eq] at h
    rw [← h]
    exact ⟨w, hw, rfl⟩
  exact CFSG.GroupTheory.commute_of_fixes_of_mapsTo_of_sup_eq_top (U := movedSpan T) (W := fixSub T)
    (hgU g hg) hgW hhW hhU (isCompl_movedSpan_fixSub T hcard).sup_eq_top

end Averaging

theorem commute_of_mem_commutator_of_injective {K V U : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Group U] (ρ : U →* (V ≃ₗ[K] V)) (hρ : Function.Injective ρ)
    (TL : Subgroup (V ≃ₗ[K] V)) [Fintype TL] (hcard : (Fintype.card TL : K) ≠ 0)
    {S₁ B : Subgroup U} {A : U} {c : K}
    (hS₁ : ∀ s ∈ S₁, ∀ t ∈ TL, Commute (ρ s) t) (hA : ∀ t ∈ TL, Commute (ρ A) t)
    (hAmoved : ∀ u ∈ movedSpan TL, ρ A u = c • u)
    (hBfix : ∀ b ∈ B, ∀ w ∈ fixSub TL, ρ b w = w)
    (hBpres : ∀ b ∈ B, ∀ w ∈ movedSpan TL, ρ b w ∈ movedSpan TL) :
    ∀ g ∈ ⁅S₁, Subgroup.zpowers A⁆, ∀ b ∈ B, Commute g b := by
  intro g hg b hb
  have hmap : (⁅S₁, Subgroup.zpowers A⁆).map ρ =
      ⁅S₁.map ρ, Subgroup.zpowers (ρ A)⁆ := by
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
  have hg' : ρ g ∈ ⁅S₁.map ρ, Subgroup.zpowers (ρ A)⁆ := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem ρ hg
  have hcent : ∀ s ∈ S₁.map ρ, ∀ t ∈ TL, Commute s t := by
    rintro s ⟨s0, hs0, rfl⟩ t ht
    exact hS₁ s0 hs0 t ht
  have hcomm : Commute (ρ g) (ρ b) :=
    commutator_commute_of_scalar_on_movedSpan (T := TL) hcard
      hcent hA hAmoved (ρ g) hg' (ρ b) (hBfix b hb) (hBpres b hb)
  exact hρ (by rw [map_mul, map_mul]; exact hcomm.eq)

theorem eq_zero_of_fixed_by_subgroup_of_not_dvd_index
    {G : Type*} [Group G] [Finite G] (ρ : G →* (V ≃ₗ[K] V))
    {p : ℕ} (hp : p.Prime) {E T : Subgroup G} (hEp : IsPGroup p E)
    (hE : ∀ v : V, (∀ e ∈ E, ρ e v = v) → v = 0)
    (hTp : IsPGroup p T) (hT : ¬ p ∣ T.index)
    {v : V} (hv : ∀ t ∈ T, ρ t v = v) : v = 0 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p G := hTp.toSylow hT
  have hPT : (P : Subgroup G) = T := IsPGroup.toSylow_coe hTp hT
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hQ : (Q : Subgroup G) = MulAut.conj g • (P : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul]
  have hfix : ∀ e ∈ E, ρ e (ρ g v) = ρ g v := by
    intro e he
    have hmem : e ∈ (MulAut.conj g) • (P : Subgroup G) := by
      rw [← hQ]
      exact hEQ he
    have hmem' : (MulAut.conj g)⁻¹ • e ∈ (P : Subgroup G) :=
      (Subgroup.mem_pointwise_smul_iff_inv_smul_mem).mp hmem
    have hmemT : (MulAut.conj g)⁻¹ • e ∈ T := by
      rw [← hPT]
      exact hmem'
    have h1 : ρ ((MulAut.conj g)⁻¹ • e) v = v := hv _ hmemT
    have h2 : ρ g (ρ ((MulAut.conj g)⁻¹ • e) v) = ρ g v := by rw [h1]
    have h3 : (MulAut.conj g)⁻¹ • e = g⁻¹ * e * g := by
      rw [show (MulAut.conj g)⁻¹ = MulAut.conj g⁻¹ from
        (MonoidHom.map_inv (MulAut.conj : G →* MulAut G) g).symm]
      rw [MulAut.smul_def, MulAut.conj_apply]
      group
    calc ρ e (ρ g v) = ρ (e * g) v := by rw [map_mul]; rfl
      _ = ρ (g * ((MulAut.conj g)⁻¹ • e)) v := by rw [h3]; group
      _ = ρ g (ρ ((MulAut.conj g)⁻¹ • e) v) := by rw [map_mul]; rfl
      _ = ρ g v := h2
  have h0 : ρ g v = 0 := hE _ hfix
  exact (ρ g).injective (by rw [h0, map_zero])

end CFSG.LinearAlgebra

end
