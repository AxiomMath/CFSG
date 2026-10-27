module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Map

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem Gxy_inf_Qz_eq (p z : G) : Gxy p z ⊓ Qz z = Qz z ⊓ Gx p := by
  have hle : Qz z ≤ Gx z := Subgroup.map_subtype_le (CFSG.pCore 2 ↥(Gx z))
  rw [Gxy_eq_inf, inf_assoc, inf_of_le_right hle, inf_comm]

theorem self_mem_Qz {z : G} (hz : z ^ 2 = 1) : z ∈ Qz z := by
  let ζ : ↥(Gx z) := GxSelf z
  have hζ2 : ζ ^ (2 : ℕ) = 1 := by
    apply Subtype.ext
    show z ^ 2 = (1 : G)
    exact hz
  have hζ_center : ζ ∈ Subgroup.center ↥(Gx z) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (mem_Gx.mp g.2).symm
  have hnorm : (Subgroup.zpowers ζ).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hζ_center)
  have hpgrp : IsPGroup 2 (Subgroup.zpowers ζ) := by
    refine IsPGroup.of_card_dvd_pow (p := 2) (n := 1) ?_
    rw [Nat.card_zpowers]
    simpa using (orderOf_dvd_iff_pow_eq_one (x := ζ) (n := 2)).mpr hζ2
  have hmem : ζ ∈ CFSG.pCore 2 ↥(Gx z) :=
    le_sSup (show Subgroup.zpowers ζ ∈ {K : Subgroup ↥(Gx z) | K.Normal ∧ IsPGroup 2 K} from
      ⟨hnorm, hpgrp⟩) (Subgroup.mem_zpowers ζ)
  exact Subgroup.mem_map.mpr ⟨ζ, hmem, rfl⟩

theorem pCore_Gxy_of_conj {p z₀ z h : G} (hh : h ∈ Gx p) (hz : h * z₀ * h⁻¹ = z)
    (hpc : CFSG.Open.pCoreOf 2 (Gxy p z₀) = Qz z₀ ⊓ Gx p) :
    CFSG.Open.pCoreOf 2 (Gxy p z) = Qz z ⊓ Gx p := by
  let f : G →* G := (MulAut.conj h).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj h).injective
  have hfp : f p = p := by
    show h * p * h⁻¹ = p
    rw [← mem_Gx.mp hh, mul_assoc, mul_inv_cancel, mul_one]
  have hfz : f z₀ = z := by
    show h * z₀ * h⁻¹ = z
    exact hz
  have hrange : f.range = ⊤ := MonoidHom.range_eq_top.mpr (MulAut.conj h).surjective
  have hmapGx : ∀ c : G, (Gx c).map f = Gx (f c) := by
    intro c
    rw [map_Gx_of_injective hf c, hrange, inf_top_eq]
  have hmapGxy : (Gxy p z₀).map f = Gxy p z := by
    rw [Gxy_eq_inf, Subgroup.map_inf _ _ f hf, hmapGx p, hmapGx z₀, hfp, hfz, Gxy_eq_inf]
  have hmapQz : (Qz z₀).map f = Qz z := by
    have h1 : CFSG.Open.pCoreOf 2 ((Gx z₀).map f) = (Qz z₀).map f :=
      pCoreOf_map_of_injective hf (Gx z₀)
    rw [hmapGx z₀, hfz] at h1
    exact h1.symm
  calc
    CFSG.Open.pCoreOf 2 (Gxy p z)
        = CFSG.Open.pCoreOf 2 ((Gxy p z₀).map f) := by rw [hmapGxy]
    _ = (CFSG.Open.pCoreOf 2 (Gxy p z₀)).map f := pCoreOf_map_of_injective hf (Gxy p z₀)
    _ = (Qz z₀ ⊓ Gx p).map f := by rw [hpc]
    _ = (Qz z₀).map f ⊓ (Gx p).map f := Subgroup.map_inf _ _ f hf
    _ = Qz z ⊓ Gx p := by rw [hmapQz, hmapGx p, hfp]

end CFSG.EvenSporadicStandard.HNRecog.Section3
