module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F7Syl

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem sec8t84_NK_conj {t : G} {S S' E T M0 : Subgroup G} {v : G}
    (hT : IsSylow2Of T (normalizer (E : Set G))) (hM0 : M0 = T ⊓ centralizer ({t} : Set G))
    (hS'C : S' ≤ centralizer ({t} : Set G)) (hS'2 : IsPGroup 2 S')
    (hS'T : S' ≤ normalizer (T : Set G)) (hM0S' : M0 ≤ S')
    (hvN : v ∈ normalizer (M0 : Set G)) (hS : S = S'.map (MulAut.conj v).toMonoidHom) :
    IsSylow2Of (T.map (MulAut.conj v).toMonoidHom)
        (normalizer ((E.map (MulAut.conj v).toMonoidHom : Subgroup G) : Set G)) ∧
      S ≤ normalizer ((T.map (MulAut.conj v).toMonoidHom : Subgroup G) : Set G) ∧
      S ⊓ normalizer ((E.map (MulAut.conj v).toMonoidHom : Subgroup G) : Set G) = M0 ∧
      S ⊓ normalizer ((E.map (MulAut.conj v).toMonoidHom : Subgroup G) : Set G) ≤
        T.map (MulAut.conj v).toMonoidHom := by
  have hinj : Function.Injective (MulAut.conj v).toMonoidHom := (MulAut.conj v).injective
  have hNormE : normalizer ((E.map (MulAut.conj v).toMonoidHom : Subgroup G) : Set G) =
      (normalizer (E : Set G)).map (MulAut.conj v).toMonoidHom := sec8t84_normalizer_map E v
  have hNormT : normalizer ((T.map (MulAut.conj v).toMonoidHom : Subgroup G) : Set G) =
      (normalizer (T : Set G)).map (MulAut.conj v).toMonoidHom := sec8t84_normalizer_map T v
  have hM0map : M0.map (MulAut.conj v).toMonoidHom = M0 := by
    simpa using (Subgroup.mem_normalizer_iff_map_conj_eq (H := M0) (g := v)).mp hvN
  have hM0T : M0 ≤ T := by rw [hM0]; exact inf_le_left
  have hM0E : M0 ≤ normalizer (E : Set G) := hM0T.trans hT.1
  have hS'E : S' ⊓ normalizer (E : Set G) = M0 := by
    refine le_antisymm ?_ (le_inf hM0S' hM0E)
    rw [hM0]
    exact le_inf (sec8t84_normalizing_le hT inf_le_right hS'2.to_inf_left
      (inf_le_left.trans hS'T)) (inf_le_left.trans hS'C)
  have hSinf : S ⊓ normalizer ((E.map (MulAut.conj v).toMonoidHom : Subgroup G) : Set G) = M0 := by
    rw [hS, hNormE, ← Subgroup.map_inf_eq S' (normalizer (E : Set G))
      (MulAut.conj v).toMonoidHom hinj, hS'E, hM0map]
  refine ⟨?_, ?_, hSinf, ?_⟩
  · rw [hNormE]
    exact sec8t84_isSylow2Of_map hT v
  · rw [hS, hNormT]
    exact Subgroup.map_mono hS'T
  · rw [hSinf]
    exact hM0map ▸ Subgroup.map_mono hM0T

end CFSG.OddStandard.SmallF3.Omega
