module

public import CFSG.LargeExtraspecial.S4FiveL
public import CFSG.LargeExtraspecial.S4OmegaQ

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem mem_orbitOf_RmodN_iff (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (ht : t ∈ S.Lbar g)
    {v : Vt S g t} : v ∈ orbitOf (RmodN S g t) (aV ht) ↔ (v : S.Qt) ∈ orbit S g t := by
  constructor
  · rintro ⟨e, ⟨x, hx, hex⟩, rfl⟩
    exact ⟨x, hx, hex _⟩
  · intro hv
    obtain ⟨e, he, hev⟩ := exists_RmodN_of_mem_orbit ht haQ hv
    exact ⟨e, he, hev⟩

theorem span_orbitOf_RmodN (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) :
    Submodule.span (ZMod 2) (orbitOf (RmodN S g t) (aV ht)) = ⊤ := by
  apply Submodule.map_injective_of_injective (Vt S g t).injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  have himg : (Vt S g t).subtype '' orbitOf (RmodN S g t) (aV ht) = orbit S g t := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (mem_orbitOf_RmodN_iff H.conj_mem ht).mp hw
    · intro hv
      exact ⟨⟨v, orbit_subset_Vt ht H.conj_mem hv⟩,
        (mem_orbitOf_RmodN_iff H.conj_mem ht).mpr hv, rfl⟩
  rw [himg, ← Vt_eq_span_orbit H ht]

theorem conj_mem_LmodN (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    {e : Vt S g t ≃ₗ[ZMod 2] Vt S g t} (he : e ∈ RmodN S g t) (hea : e (aV ht) = aV ht)
    {f : Vt S g t ≃ₗ[ZMod 2] Vt S g t} (hf : f ∈ LmodN S g t) : e * f * e⁻¹ ∈ LmodN S g t := by
  obtain ⟨x, hx, hex⟩ := he
  have hxa : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) := by
    have := hex (aV ht)
    rw [hea] at this
    exact this.symm
  have hxN : x ∈ normalizer (S.Lbar g : Set S.O) := by
    have := mem_normalizer_of_fix (S := S) (g := g) (h := 1) H.conj_mem H.conj_ne
      (Rbar_le_Mbar hx) (by simpa using hxa)
    simpa using this
  obtain ⟨y, hy, hfy⟩ := hf
  refine ⟨x * y * x⁻¹, (mem_normalizer_iff.mp hxN y).mp hy, fun v => ?_⟩
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hex, hfy]
  have h1 : ((e⁻¹ v : Vt S g t) : S.Qt) = ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
    have := hex (e⁻¹ v)
    rw [show e (e⁻¹ v) = v from e.apply_symm_apply v] at this
    rw [this, inv_apply_apply_O]
  rw [h1, coe_mul_apply, coe_mul_apply]

theorem mem_normalizer_LmodN (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    {e : Vt S g t ≃ₗ[ZMod 2] Vt S g t} (he : e ∈ RmodN S g t) (hea : e (aV ht) = aV ht) :
    e ∈ normalizer (LmodN S g t : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) := by
  have hea' : e⁻¹ (aV ht) = aV ht := by
    have := e.symm_apply_apply (aV ht)
    rw [hea] at this
    exact this
  rw [mem_normalizer_iff]
  intro f
  refine ⟨fun hf => conj_mem_LmodN H ht he hea hf, fun hf => ?_⟩
  have := conj_mem_LmodN H ht (inv_mem he) hea' hf
  have e2 : e⁻¹ * (e * f * e⁻¹) * e⁻¹⁻¹ = f := by group
  rwa [e2] at this

end CFSG.LargeExtraspecial.S4
