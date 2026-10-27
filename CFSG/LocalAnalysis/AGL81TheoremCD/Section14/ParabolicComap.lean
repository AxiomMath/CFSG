module

public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.A3ComponentsBasic

import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.RelIndexPrime

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

variable {X : Type} [Group X] [Finite X]

theorem minParabolic_comap_of_relIndex_eq_three {S : Type*} [Group S] (φ : X →* S)
    (hφ : Function.Surjective φ) (hker : IsPGroup 2 φ.ker) {E P : Subgroup S}
    (hE : IsPGroup 2 E) (hEP : E ≤ P) (hidx : E.relIndex P = 3)
    (hnorm : ¬ P ≤ Subgroup.normalizer (E : Set S)) :
    CFSG.Quasithin.MinParabolic (P.comap φ) (E.comap φ) (E.comap φ) := by
  classical
  have hE2 : IsPGroup 2 (E.comap φ) := IsPGroup.comap_of_ker_isPGroup hE φ hker
  have hEP' : E.comap φ ≤ P.comap φ := Subgroup.comap_mono hEP
  have hPmap : (P.comap φ).map φ = P := by
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr hφ, top_inf_eq]
  have hEmap : (E.comap φ).map φ = E := by
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr hφ, top_inf_eq]
  have hidx' : (E.comap φ).relIndex (P.comap φ) = 3 := by
    rw [Subgroup.relIndex_comap, hPmap, hidx]
  have hsyl : CFSG.QuasithinUnique.IsSylowTwoOf (E.comap φ) (P.comap φ) :=
    ⟨hEP', hE2, by
      change ¬ 2 ∣ (E.comap φ).relIndex (P.comap φ)
      rw [hidx']
      norm_num⟩
  have hnorm' : ¬ P.comap φ ≤ Subgroup.normalizer (E.comap φ : Set X) := by
    intro h
    have hm : (P.comap φ).map φ ≤ Subgroup.normalizer ((E.comap φ).map φ : Set S) :=
      (Subgroup.map_mono h).trans (Subgroup.le_normalizer_map (H := E.comap φ) φ)
    rw [hPmap, hEmap] at hm
    exact hnorm hm
  refine ⟨hsyl, hnorm', ?_⟩
  have hp3 : ((E.comap φ).relIndex (P.comap φ)).Prime := by
    rw [hidx']
    norm_num
  have key : ∀ K : Subgroup X, E.comap φ ≤ K → K ≤ P.comap φ →
      K = E.comap φ ∨ K = P.comap φ := fun _ hEK hKP =>
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.eq_or_eq_of_relIndex_prime hEK hKP hp3
  have hlt : E.comap φ < P.comap φ := by
    refine lt_of_le_of_ne hEP' ?_
    intro heq
    rw [heq, Subgroup.relIndex_self] at hidx'
    exact absurd hidx' (by norm_num)
  have hmax : CFSG.Quasithin.IsMaxSubgroupIn (P.comap φ) (E.comap φ) := by
    refine ⟨hlt, fun K hEK hKP => ?_⟩
    rcases key K hEK.le hKP with h | h
    · exact absurd h hEK.ne'
    · exact h
  exact CFSG.Quasithin.isUniqueMaxOver_iff.mpr
    ⟨hmax, le_rfl, fun N hN hEN => by
      rcases key N hEN hN.1.le with h | h
      · exact h
      · exact absurd h hN.1.ne⟩

theorem perfectCore_comap_eq_bot {S : Type*} [Group S] (φ : X →* S)
    (hker : IsSolvable φ.ker) {P : Subgroup S} (hP : IsSolvable P) :
    CFSG.Quasithin.perfectCore (P.comap φ) = ⊥ := by
  classical
  have hle : φ.ker ≤ P.comap φ := MonoidHom.ker_le_comap φ P
  let QP : Subgroup (P.comap φ) := φ.ker.subgroupOf (P.comap φ)
  let g : (P.comap φ) →* P := (φ.comp (P.comap φ).subtype).codRestrict P (fun p => p.2)
  let f : QP →* (P.comap φ) := QP.subtype
  have hker_g : g.ker = QP := by
    ext p
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact ⟨fun hp => congrArg Subtype.val hp, fun hp => Subtype.ext hp⟩
  have hfg : g.ker ≤ f.range := by
    rw [hker_g, Subgroup.range_subtype]
  haveI : Group.IsSolvable ↥φ.ker := hker
  haveI : Group.IsSolvable ↥QP :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hle).injective
  haveI : Group.IsSolvable ↥P := hP
  have hsolv : Group.IsSolvable ↥(P.comap φ) := Group.isSolvable_of_ker_le_range f g hfg
  exact (CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot (P.comap φ)).mp hsolv

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
