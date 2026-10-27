module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLevi
public import CFSG.Timmesfeld.LieEmbed.SLE6
public import CFSG.LieType.Steinberg.Isogeny.E6
public import CFSG.LieType.Chevalley.PinnedBridge

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.Timmesfeld.LieEmbed CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule

theorem charTwo_eq_one_of_mul_self_eq_one {R : Type*} [CommRing R] [IsDomain R] [CharP R 2]
    {x : R} (h : x * x = 1) : x = 1 := by
  have h2 : (x - 1) * (x - 1) = 0 := by
    have h2' : (2 : R) = 0 := CharP.cast_eq_zero R 2
    linear_combination h - (x - 1) * h2'
  exact sub_eq_zero.1 (mul_self_eq_zero.1 h2)


variable (K : Type) [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def slToAdjointE6 :
    Matrix.SpecialLinearGroup (Fin 6) K →* ↥(adjointGroup .E6 K) :=
  (e6Isogeny K).comp (exists_slToE6 (k := K)).choose

variable {K}

omit
  [Finite K] in
theorem coe_xPar_eq_pinnedX {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) (c : K) :
    ((xPar (rootOperatorFamily .E6) γ c : adjointGroup .E6 K) : ModGL .E6 K) =
      pinnedX .E6 K γ c := by
  have hs : ((rootOperatorFamily .E6).pinnedFamilySign γ : K) = 1 :=
    charTwo_eq_one_of_mul_self_eq_one ((rootOperatorFamily .E6).pinnedFamilySign_mul_self K γ)
  rw [(rootOperatorFamily .E6).pinnedX_eq_eltUnit K hγ, hs, one_mul, xPar_of_isRoot hγ]
  rfl

theorem coe_e6Isogeny_xm {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) (c : K) :
    ((e6Isogeny K (e6Data_valid.xm K γ c) : adjointGroup .E6 K) : ModGL .E6 K) =
      pinnedX .E6 K γ c := by
  have hδ : (relSignOr (rootOperatorFamily .E6) e6AdjData_valid γ : K) = 1 :=
    charTwo_eq_one_of_mul_self_eq_one (relSignOr_mul_self γ)
  rw [e6Isogeny_xm K hγ c, yPar, hδ, one_mul, coe_xPar_eq_pinnedX hγ]

theorem coe_slToAdjointE6_transvection {i j : Fin 6} (hij : i ≠ j) (c : K) :
    ((slToAdjointE6 K (Matrix.SpecialLinearGroup.transvection hij c) : adjointGroup .E6 K) :
        ModGL .E6 K) = pinnedX .E6 K (a5Root i j) c := by
  rw [slToAdjointE6, MonoidHom.comp_apply, (exists_slToE6 (k := K)).choose_spec i j hij c,
    coe_e6Isogeny_xm (isRoot_a5Root hij)]

theorem slToAdjointE6_transvection {i j : Fin 6} (hij : i ≠ j) (c : K) :
    slToAdjointE6 K (Matrix.SpecialLinearGroup.transvection hij c) =
      ⟨pinnedX .E6 K (a5Root i j) c, pinnedX_mem_adjointGroup _ c⟩ :=
  Subtype.ext (coe_slToAdjointE6_transvection hij c)

theorem slToAdjointE6_transvection_ne_one {i j : Fin 6} (hij : i ≠ j) {c : K} (hc : c ≠ 0) :
    slToAdjointE6 K (Matrix.SpecialLinearGroup.transvection hij c) ≠ 1 := by
  intro h
  have h' := congrArg (fun g : adjointGroup .E6 K => (g : ModGL .E6 K)) h
  simp only [coe_slToAdjointE6_transvection, OneMemClass.coe_one] at h'
  rw [← pinnedX_zero .E6 K (a5Root i j)] at h'
  exact hc (pinnedX_injective .E6 K _ h')

theorem range_slToAdjointE6 : (slToAdjointE6 K).range = a5Levi K := by
  rw [MonoidHom.range_eq_map,
    ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
    MonoidHom.map_closure, a5Levi_eq_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨⟨i, j, hij, c⟩, rfl⟩, rfl⟩
    exact ⟨i, j, hij, c, (coe_slToAdjointE6_transvection hij c).symm⟩
  · rintro ⟨i, j, hij, c, hc⟩
    refine ⟨_, ⟨⟨i, j, hij, c⟩, rfl⟩, Subtype.ext ?_⟩
    rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk, coe_slToAdjointE6_transvection, hc]

theorem slToAdjointE6_mem_a5Levi (A : Matrix.SpecialLinearGroup (Fin 6) K) :
    slToAdjointE6 K A ∈ a5Levi K := by
  rw [← range_slToAdjointE6]
  exact ⟨A, rfl⟩

end CFSG.SeitzReduction.E6Pilot
