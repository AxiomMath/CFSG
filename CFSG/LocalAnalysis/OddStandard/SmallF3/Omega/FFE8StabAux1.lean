module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSTypesAux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSSyl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8Def

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ffE8Stab_eq_of_ffSim_eq (hQ : Q.Nondegenerate) (hπ : piOrth Q ∉ omegaGroup hQ)
    {a b : OGroup Q} (ha : a ∈ omegaGroup hQ) (hb : b ∈ omegaGroup hQ)
    (h : ffSim Q a = ffSim Q b) : a = b := by
  have h1 : (QuotientGroup.mk (orthToSim Q a) : ProjSim Q) = QuotientGroup.mk (orthToSim Q b) := h
  rw [QuotientGroup.eq] at h1
  rcases mem_piSim_iff.mp h1 with h2 | h2
  · refine inv_mul_eq_one.mp (orthToSim_injective ?_)
    rw [map_mul, map_inv, map_one]
    exact h2
  · exfalso
    apply hπ
    have h3 : a⁻¹ * b = piOrth Q := orthToSim_injective (by rw [map_mul, map_inv]; exact h2)
    rw [← h3]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hb

theorem ffE8Stab_ffSim_simAct (γ : simGroup Q) (g : OGroup Q) :
    ffSim Q (simAct Q γ g) =
      QuotientGroup.mk γ * ffSim Q g * (QuotientGroup.mk γ : ProjSim Q)⁻¹ := by
  have h : orthToSim Q (simAct Q γ g) = γ * orthToSim Q g * γ⁻¹ := by
    apply Subtype.ext
    rw [coe_orthToSim, coe_simAct]
    rfl
  change (QuotientGroup.mk (orthToSim Q (simAct Q γ g)) : ProjSim Q) = _
  rw [h, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rfl

theorem ffE8Stab_isElemAb2_map {H K : Type} [Group H] [Group K] (f : H →* K)
    (hf : Function.Injective f) {U : Subgroup H} {k : ℕ} (h : IsElemAb2 U k) :
    IsElemAb2 (U.map f) k := by
  haveI : IsMulCommutative U := h.1.1
  refine ⟨⟨inferInstance, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, h.1.2 u hu, map_one]
  · rw [Nat.card_congr (U.equivMapOfInjective f hf).toEquiv.symm, h.2]

theorem ffE8Stab_act_ffZ0s (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : PFrame Q (Option (Fin 5)) ffC) {y : ProjSim Q}
    (hy : (ffP1p hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom = ffP1p hQ fr) :
    ffSimOmegaAct hQ h2 y (ffZ0s hQ fr) = ffZ0s hQ fr := by
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  have hz : ffZ0s hQ fr ∈ ffP1p hQ fr := ffB1p_le_ffP1p hQ fr (ffZ0s_mem_ffB1p hQ fr)
  have hg : ffSimOmegaAct hQ h2 y (ffZ0s hQ fr) ∈
      (ffP1p hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom := Subgroup.mem_map_of_mem _ hz
  rw [hy] at hg
  have hc : ∀ h ∈ ffP1p hQ fr, h * ffSimOmegaAct hQ h2 y (ffZ0s hQ fr) =
      ffSimOmegaAct hQ h2 y (ffZ0s hQ fr) * h := by
    intro h hh
    have hh' : h ∈ (ffP1p hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom := by rwa [hy]
    obtain ⟨h0, hh0, rfl⟩ := Subgroup.mem_map.mp hh'
    change ffSimOmegaAct hQ h2 y h0 * _ = _ * ffSimOmegaAct hQ h2 y h0
    rw [← map_mul, ← map_mul, ffZ0s_central hQ fr hh0]
  rcases ffP1p_center hQ hπ fr hg hc with h1 | h1
  · exfalso
    exact ffZ0s_ne_one hQ hπ fr ((ffSimOmegaAct hQ h2 y).injective (h1.trans (map_one _).symm))
  · exact h1

theorem ffE8Stab_simAct_z0 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : PFrame Q (Option (Fin 5)) ffC) {γ : simGroup Q}
    (hγ : (ffP1p hQ fr).map (ffSimOmegaAct hQ h2 (QuotientGroup.mk γ)).toMonoidHom =
      ffP1p hQ fr) : simAct Q γ (ffZ0p fr) = ffZ0p fr := by
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  have hz0 : ffZ0p fr ∈ omegaGroup hQ := ffB0p_le_omega hQ fr (ffZ0p_mem_ffB0p fr)
  have h3 := ff_omegaToSim_act hQ h2 (QuotientGroup.mk γ) (ffZ0s hQ fr)
  rw [ffE8Stab_act_ffZ0s hQ hdim hsgn h2 fr hγ, ffOutFF6PSTypes_ffOmegaToSim_ffZ0s] at h3
  refine ffE8Stab_eq_of_ffSim_eq hQ hπ (ff_simAct_mem_omegaGroup hQ h2 γ hz0) hz0 ?_
  rw [ffE8Stab_ffSim_simAct]
  exact h3.symm

theorem ffE8Stab_exists_lift (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : PFrame Q (Option (Fin 5)) ffC) {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1) :
    ∃ (γ : simGroup Q) (μ : (ZMod 3)ˣ), IsSimilitude Q (γ : V ≃ₗ[ZMod 3] V) μ ∧
      (μ : ZMod 3) = -ε ∧ (ffP1p hQ fr).map
        (ffSimOmegaAct hQ h2 (QuotientGroup.mk γ)).toMonoidHom = ffP1p hQ fr := by
  rcases hε with rfl | rfl
  · obtain ⟨y0, hy0G, hy0⟩ := ff6p_exists_y0 hQ hdim hsgn h2 fr
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective y0
    obtain ⟨c, hc⟩ := γ.2
    rcases aux_unit_eq_one_or_neg_one c with rfl | rfl
    · exact absurd ⟨toProj Q ⟨(γ : V ≃ₗ[ZMod 3] V), isSimilitude_one_iff.mp hc⟩, rfl⟩ hy0G
    · exact ⟨γ, -1, hc, by decide, hy0⟩
  · refine ⟨1, 1, aux_isSimilitude_one, by decide, ?_⟩
    have h : (ffSimOmegaAct hQ h2 (QuotientGroup.mk (1 : simGroup Q))).toMonoidHom =
        MonoidHom.id _ := by
      rw [QuotientGroup.mk_one, map_one]
      rfl
    rw [h, Subgroup.map_id]

end CFSG.OddStandard.SmallF3.Omega
