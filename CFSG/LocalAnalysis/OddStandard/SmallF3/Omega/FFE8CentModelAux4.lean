module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8Std
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8Def

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ffOutFFE8CentModel_elemAb2_map {H K : Type} [Group H] [Group K] (f : H →* K)
    (hf : Function.Injective f) {U : Subgroup H} {k : ℕ} (h : IsElemAb2 U k) :
    IsElemAb2 (U.map f) k := by
  haveI : IsMulCommutative U := h.1.1
  refine ⟨⟨inferInstance, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, h.1.2 u hu, map_one]
  · rw [Nat.card_congr (U.equivMapOfInjective f hf).toEquiv.symm, h.2]

theorem ffOutFFE8CentModel_sylow_map {H K : Type} [Group H] [Group K] (f : H →* K)
    (hf : Function.Injective f) {S T : Subgroup H} (h : IsSylow2Of S T) :
    IsSylow2Of (S.map f) (T.map f) := by
  refine ⟨Subgroup.map_mono h.1, h.2.1.map f, ?_⟩
  rw [Subgroup.relIndex_map_map_of_injective S T hf]
  exact h.2.2

theorem ffOutFFE8CentModel_normalE16_map {H K : Type} [Group H] [Group K] (f : H →* K)
    (hf : Function.Injective f) {P B : Subgroup H} (h : IsNormalE16In P B) :
    IsNormalE16In (P.map f) (B.map f) := by
  have hle : B.map f ≤ P.map f := Subgroup.map_mono h.1
  refine ⟨hle, ffOutFFE8CentModel_elemAb2_map f hf h.2.1, ?_⟩
  rw [Subgroup.normal_subgroupOf_iff hle]
  rintro _ _ ⟨b, hb, rfl⟩ ⟨p, hp, rfl⟩
  exact ⟨p * b * p⁻¹, (Subgroup.normal_subgroupOf_iff h.1).mp h.2.2 b p hb hp,
    by simp only [map_mul, map_inv]⟩

theorem ffOutFFE8CentModel_ffSim_eq_iff (t s : OGroup Q) :
    ffSim Q t = ffSim Q s ↔ s = t ∨ s = piOrth Q * t := by
  have h1 : ffSim Q t = ffSim Q s ↔ (orthToSim Q t)⁻¹ * orthToSim Q s ∈ piSim Q :=
    QuotientGroup.eq
  rw [h1, ← map_inv, ← map_mul, mem_piSim_iff, ← map_one (orthToSim Q),
    orthToSim_injective.eq_iff, orthToSim_injective.eq_iff, inv_mul_eq_one,
    inv_mul_eq_iff_eq_mul, mul_piOrth_comm, eq_comm (a := t)]

theorem ffOutFFE8CentModel_ffSim_mem (hQ : Q.Nondegenerate) {g : OGroup Q}
    (hg : g ∈ omegaGroup hQ) : ffSim Q g ∈ ffOmegaSim hQ :=
  ⟨omegaToProj hQ ⟨g, hg⟩, rfl⟩

theorem ffOutFFE8CentModel_exists_of_mem (hQ : Q.Nondegenerate) {x : ProjSim Q}
    (hx : x ∈ ffOmegaSim hQ) : ∃ g ∈ omegaGroup hQ, ffSim Q g = x := by
  obtain ⟨w, rfl⟩ := hx
  obtain ⟨g, rfl⟩ := omegaToProj_surjective hQ w
  exact ⟨g, g.2, rfl⟩

theorem ffOutFFE8CentModel_mem_ffB1Sim_iff (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) {y : ProjSim Q} :
    y ∈ ffB1Sim hQ fr ↔ ∃ g ∈ ffB0p fr, ffSim Q g = y := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨g, hg, rfl⟩ := (mem_ffStar_iff hQ).mp hw
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨omegaToProj hQ ⟨g, ffB0p_le_omega hQ fr hg⟩,
      (mem_ffStar_iff hQ).mpr ⟨⟨g, ffB0p_le_omega hQ fr hg⟩, hg, rfl⟩, rfl⟩

theorem ffOutFFE8CentModel_ffSim_simAct (γ : simGroup Q) (t : OGroup Q) :
    ffSim Q (simAct Q γ t) =
      (QuotientGroup.mk γ : ProjSim Q) * ffSim Q t * (QuotientGroup.mk γ : ProjSim Q)⁻¹ := by
  have h : orthToSim Q (simAct Q γ t) = γ * orthToSim Q t * γ⁻¹ := by
    apply Subtype.ext
    rw [coe_orthToSim, coe_simAct]
    rfl
  change (QuotientGroup.mk (orthToSim Q (simAct Q γ t)) : ProjSim Q) = _
  rw [h, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rfl

theorem ffOutFFE8CentModel_conj_ffOmegaSim (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (γ : simGroup Q) :
    (ffOmegaSim hQ).map (MulAut.conj (QuotientGroup.mk γ : ProjSim Q)).toMonoidHom =
      ffOmegaSim hQ := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨g, hg, rfl⟩ := ffOutFFE8CentModel_exists_of_mem hQ hx
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← ffOutFFE8CentModel_ffSim_simAct]
    exact ffOutFFE8CentModel_ffSim_mem hQ (ff_simAct_mem_omegaGroup hQ h2 γ hg)
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := ffOutFFE8CentModel_exists_of_mem hQ hx
    refine ⟨ffSim Q (simAct Q γ⁻¹ g),
      ffOutFFE8CentModel_ffSim_mem hQ (ff_simAct_mem_omegaGroup hQ h2 γ⁻¹ hg), ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← ffOutFFE8CentModel_ffSim_simAct,
      ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

end CFSG.OddStandard.SmallF3.Omega
