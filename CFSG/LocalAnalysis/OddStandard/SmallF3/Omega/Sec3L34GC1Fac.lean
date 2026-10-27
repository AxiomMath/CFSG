module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Iso
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Def

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] {u x : G} {K : Subgroup G} {𝒪 : Set (Subgroup G)}

theorem L34GOrb.fac [Finite G] (hO : L34GOrb u x K 𝒪)
    (hxN : x ∈ normalizer ((sSup 𝒪 : Subgroup G) : Set G)) :
    L34GFac (l34gImg (sSup 𝒪) (sSup 𝒪)) (l34gImg (sSup 𝒪) '' 𝒪)
      ((sSup 𝒪).normalizerMonoidHom ⟨x, hxN⟩) := by
  have hEN : (sSup 𝒪 : Subgroup G) ≤ normalizer ((sSup 𝒪 : Subgroup G) : Set G) :=
    Subgroup.le_normalizer
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro S ⟨J, hJ, rfl⟩
    exact l34gImg_mono (le_sSup hJ)
  · rintro S ⟨J, hJ, rfl⟩ h hh s hs
    obtain ⟨e, heN, heE, rfl⟩ := mem_l34gImg.1 hh
    obtain ⟨j, hjN, hjJ, rfl⟩ := mem_l34gImg.1 hs
    have hejJ : e * j * e⁻¹ ∈ J := hO.normal hJ e heE j hjJ
    refine mem_l34gImg.2 ⟨e * j * e⁻¹, Subgroup.le_normalizer (le_sSup hJ hejJ), hejJ, ?_⟩
    have hsub : (⟨e * j * e⁻¹, Subgroup.le_normalizer (le_sSup hJ hejJ)⟩ :
        normalizer ((sSup 𝒪 : Subgroup G) : Set G)) = ⟨e, heN⟩ * ⟨j, hjN⟩ * ⟨e, heN⟩⁻¹ := rfl
    rw [hsub, map_mul, map_mul, map_inv]
  · rintro S ⟨J, hJ, rfl⟩
    exact hO.img_simple hJ
  · rintro S ⟨J, hJ, rfl⟩ T ⟨J', hJ', rfl⟩ hne a ha b hb
    have hJJ : J ≠ J' := fun h => hne (by rw [h])
    obtain ⟨j, hjN, hjJ, rfl⟩ := mem_l34gImg.1 ha
    obtain ⟨j', hj'N, hj'J', rfl⟩ := mem_l34gImg.1 hb
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (hO.commute hJ hJ' hJJ j hjJ j' hj'J'))
  · exact (l34gImg_sSup (E := sSup 𝒪) (𝒳 := 𝒪) fun J hJ => (le_sSup hJ).trans hEN).symm
  · rw [l34gImg_self]
    exact l34g_inn_centralizer_of_perfect (Subgroup.isPerfect_iff.2 hO.perfect)
  · rw [← map_mul]
    have hx2 : x * x = 1 := sec63P_mul_self hO.invol
    have : (⟨x, hxN⟩ * ⟨x, hxN⟩ : normalizer ((sSup 𝒪 : Subgroup G) : Set G)) = 1 :=
      Subtype.ext hx2
    rw [this, map_one]
  · rintro S ⟨J, hJ, rfl⟩
    exact ⟨CFSG.conjugate J x, hO.conj J hJ x (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)),
      (l34gImg_conjugate hxN).symm⟩

end CFSG.OddStandard.SmallF3.Omega
