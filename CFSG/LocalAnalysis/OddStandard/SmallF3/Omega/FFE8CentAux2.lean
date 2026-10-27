module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8Def

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ffOutFFE8Cent_polar_sim {γ : V ≃ₗ[ZMod 3] V} {μ : (ZMod 3)ˣ}
    (hγ : IsSimilitude Q γ μ) (x y : V) :
    QuadraticMap.polar Q (γ x) (γ y) = (μ : ZMod 3) * QuadraticMap.polar Q x y := by
  rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add, hγ (x + y), hγ x, hγ y]
  ring

theorem ffOutFFE8Cent_mult (γ : simGroup Q) :
    IsSimilitude Q (γ : V ≃ₗ[ZMod 3] V) 1 ∨ IsSimilitude Q (γ : V ≃ₗ[ZMod 3] V) (-1) := by
  obtain ⟨c, hc⟩ := γ.2
  rcases aux_unit_eq_one_or_neg_one c with rfl | rfl
  · exact Or.inl hc
  · exact Or.inr hc

theorem ffOutFFE8Cent_simInGStar {γ : simGroup Q}
    (hγ : IsSimilitude Q (γ : V ≃ₗ[ZMod 3] V) 1) :
    SimInGStar (QuotientGroup.mk γ : ProjSim Q) := by
  let g : OGroup Q := ⟨(γ : V ≃ₗ[ZMod 3] V), isSimilitude_one_iff.mp hγ⟩
  refine ⟨toProj Q g, ?_⟩
  rw [projOrthToProjSim_toProj]
  exact congrArg QuotientGroup.mk (Subtype.ext rfl)

private lemma fk3_conj_apply_of_mul_eq {e e'' : OGroup Q} {δ : simGroup Q}
    (h : δ⁻¹ * orthToSim Q e * δ = orthToSim Q e'') (v : V) :
    (e : V ≃ₗ[ZMod 3] V) ((δ : V ≃ₗ[ZMod 3] V) v) =
      (δ : V ≃ₗ[ZMod 3] V) ((e'' : V ≃ₗ[ZMod 3] V) v) := by
  have h' : (δ : V ≃ₗ[ZMod 3] V)⁻¹ * (e : V ≃ₗ[ZMod 3] V) * (δ : V ≃ₗ[ZMod 3] V) =
      (e'' : V ≃ₗ[ZMod 3] V) := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_orthToSim] using
      congrArg (fun g : simGroup Q => (g : V ≃ₗ[ZMod 3] V)) h
  have hconj : (e : V ≃ₗ[ZMod 3] V) * (δ : V ≃ₗ[ZMod 3] V) =
      (δ : V ≃ₗ[ZMod 3] V) * (e'' : V ≃ₗ[ZMod 3] V) := by
    rw [← h']
    group
  simpa only [LinearEquiv.mul_apply] using
    congrArg (fun g : V ≃ₗ[ZMod 3] V => g v) hconj

private lemma fk3_conj_apply_of_mul_eq_neg {e e'' : OGroup Q} {δ : simGroup Q}
    (h : δ⁻¹ * orthToSim Q e * δ = orthToSim Q e'' * orthToSim Q (piOrth Q)) (v : V) :
    (e : V ≃ₗ[ZMod 3] V) ((δ : V ≃ₗ[ZMod 3] V) v) =
      -((δ : V ≃ₗ[ZMod 3] V) ((e'' : V ≃ₗ[ZMod 3] V) v)) := by
  have h' : (δ : V ≃ₗ[ZMod 3] V)⁻¹ * (e : V ≃ₗ[ZMod 3] V) * (δ : V ≃ₗ[ZMod 3] V) =
      (e'' : V ≃ₗ[ZMod 3] V) * (piOrth Q : V ≃ₗ[ZMod 3] V) := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_orthToSim] using
      congrArg (fun g : simGroup Q => (g : V ≃ₗ[ZMod 3] V)) h
  have hconj : (e : V ≃ₗ[ZMod 3] V) * (δ : V ≃ₗ[ZMod 3] V) =
      (δ : V ≃ₗ[ZMod 3] V) * ((e'' : V ≃ₗ[ZMod 3] V) * (piOrth Q : V ≃ₗ[ZMod 3] V)) := by
    rw [← h']
    group
  simpa only [LinearEquiv.mul_apply, coe_piOrth_apply, map_neg] using
    congrArg (fun g : V ≃ₗ[ZMod 3] V => g v) hconj

theorem ffOutFFE8Cent_conj {E : Subgroup (OGroup Q)} {Ē : Subgroup (ProjSim Q)}
    (hĒ : Ē = E.map (ffSim Q)) {δ : simGroup Q}
    (hδ : (QuotientGroup.mk δ : ProjSim Q) ∈ Subgroup.normalizer (Ē : Set (ProjSim Q))) :
    ∀ e ∈ E, ∃ e'' ∈ E, ∃ s : ZMod 3, (s = 1 ∨ s = -1) ∧
      ∀ v, (e : V ≃ₗ[ZMod 3] V) ((δ : V ≃ₗ[ZMod 3] V) v) =
        s • (δ : V ≃ₗ[ZMod 3] V) ((e'' : V ≃ₗ[ZMod 3] V) v) := by
  intro e he
  have hx : (QuotientGroup.mk δ)⁻¹ * ffSim Q e * QuotientGroup.mk δ ∈ Ē :=
    ((Subgroup.mem_normalizer_iff''.mp hδ) (ffSim Q e)).mp
      (by rw [hĒ]; exact Subgroup.mem_map_of_mem _ he)
  obtain ⟨e'', he'', he''eq⟩ := Subgroup.mem_map.mp (hĒ ▸ hx)
  have hkey : (orthToSim Q e'' : ProjSim Q) =
      (QuotientGroup.mk (δ⁻¹ * orthToSim Q e * δ) : ProjSim Q) := by
    calc (orthToSim Q e'' : ProjSim Q) = ffSim Q e'' := rfl
      _ = (QuotientGroup.mk δ)⁻¹ * ffSim Q e * QuotientGroup.mk δ := he''eq
      _ = QuotientGroup.mk (δ⁻¹ * orthToSim Q e * δ) := by
            simp only [ffSim, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
              QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hmem : (orthToSim Q e'')⁻¹ * (δ⁻¹ * orthToSim Q e * δ) ∈ piSim Q :=
    QuotientGroup.eq.mp hkey
  rcases mem_piSim_iff.mp hmem with hz | hz
  · refine ⟨e'', he'', 1, Or.inl rfl, fun v => ?_⟩
    have h : δ⁻¹ * orthToSim Q e * δ = orthToSim Q e'' := (inv_mul_eq_one.mp hz).symm
    rw [one_smul]
    exact fk3_conj_apply_of_mul_eq h v
  · refine ⟨e'', he'', -1, Or.inr rfl, fun v => ?_⟩
    have h : δ⁻¹ * orthToSim Q e * δ = orthToSim Q e'' * orthToSim Q (piOrth Q) :=
      eq_mul_of_inv_mul_eq hz
    rw [neg_one_smul]
    exact fk3_conj_apply_of_mul_eq_neg h v

end CFSG.OddStandard.SmallF3.Omega
