module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldMirror
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldMirrorCentral
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldMirrorField
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldMirrorSpare

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

theorem l34FieldSignalizerVanishingMirror_of_inputs
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (h13 : Sol76T13.SolomonThm13Simple)
    (hcat : L3TwoPowProperFixedCatalog)
    (hmult : Quasithin.SchurMult2L3)
    (hGold : GoldschmidtStronglyClosedInput) :
    L34FieldSignalizerVanishingMirror := by
  intro G _ _ t P hset hmax E hEt hEab hE8
  obtain ⟨W, hWodd, hPW, hWE⟩ := l34FieldSignalizerGluing_of_inputs hmult G t P hset
  rw [hWE E hEt hEab hE8]
  by_contra hW1
  let M : Subgroup G := normalizer (W : Set G)
  have hM : normalizer (W : Set G) = M := rfl
  have hCM : centralizer ({t} : Set G) ≤ M := by
    intro c hc
    have hct : (MulAut.conj c).toMonoidHom t = t := by
      change c * t * c⁻¹ = t
      rw [Subgroup.mem_centralizer_singleton_iff.mp hc]
      group
    have hEc : E.map (MulAut.conj c).toMonoidHom ≤ centralizer ({t} : Set G) := by
      calc E.map (MulAut.conj c).toMonoidHom
          ≤ (centralizer ({t} : Set G)).map (MulAut.conj c).toMonoidHom :=
            Subgroup.map_mono hEt
        _ ≤ centralizer ((MulAut.conj c).toMonoidHom '' ({t} : Set G)) :=
            Subgroup.map_centralizer_le_centralizer_image _ _
        _ = centralizer ({t} : Set G) := by rw [Set.image_singleton, hct]
    have hcard : 8 ≤ Nat.card (E.map (MulAut.conj c).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
      exact hE8
    have hWc := hWE (E.map (MulAut.conj c).toMonoidHom) hEc
      (CFSG.SectionRank.isElemAbelian_map hEab (MulAut.conj c).toMonoidHom) hcard
    rw [wGroup_map_conj, hWE E hEt hEab hE8] at hWc
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hWc
  obtain ⟨m, hm, hme, hPm⟩ := hset.2.2.2.2.2
  obtain ⟨htM, L, n, hL, hZ, hnm, hLL, hshape⟩ :=
    exists_field_host_component hcat hmult hset hWodd hW1 hPW hM hm hme hPm
  have hmn : m ≤ n := by rcases hnm with rfl | rfl <;> omega
  rcases hshape with ⟨hLt, hPL, hn⟩ | ⟨hLt, hPL, hn⟩ | ⟨hmove, hPL⟩
  · have hn4 : 4 ≤ n := by omega
    by_cases hLn : L.Normal
    · exact false_of_field_host_central_normal hcat hmult hGold hset hWodd hW1 hPW hWE hM
        hL hLn hZ hPL hn4 hLL
    · exact false_of_field_host_central_moved h13 hset hmax hCM hL hPL hLn
  · by_cases hLn : L.Normal
    · refine false_of_field_host_field_normal hcat hmult hset hWodd hW1 hPW hWE hM hL hLn
        hZ hPL hm hme hPm ?_
      rwa [hn] at hLL
    · have hnotfix : ∃ g : ↥M ⧸ pPrimeCore 2 ↥M, L.map (MulAut.conj g).toMonoidHom ≠ L := by
        by_contra h
        push Not at h
        exact hLn (Subgroup.normal_iff_map_conj_eq.mpr (by simpa using h))
      obtain ⟨g, hg⟩ := hnotfix
      refine false_of_field_host_spare hS h13 hmult hset hmax hWodd hW1 hPW hWE hM htM hL
        hZ hm hPm hmn hLL (hPL.trans le_sup_left) (Or.inl ⟨hLt, hn⟩) ⟨g, hg, ?_⟩
      rwa [hLt]
  · by_cases hpair : ∀ g : ↥M ⧸ pPrimeCore 2 ↥M, L.map (MulAut.conj g).toMonoidHom = L ∨
        L.map (MulAut.conj g).toMonoidHom =
          L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom
    · exact false_of_field_host_swap_pair hcat hmult hset hWodd hW1 hPW hWE hM htM hmove hpair
    · push Not at hpair
      obtain ⟨g, hg1, hg2⟩ := hpair
      exact false_of_field_host_spare hS h13 hmult hset hmax hWodd hW1 hPW hWE hM htM hL
        hZ hm hPm hmn hLL hPL (Or.inr hmove) ⟨g, hg1, hg2⟩

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
