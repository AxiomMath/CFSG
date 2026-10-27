module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.M24KFact
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.McL

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census424Rest

open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24 CFSG.AGLEmbeddingD2.Wilson.ThreeCore
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Blueprint
  CFSG.RankThree.PartTwo.Sec21 Subgroup Equiv
open CFSG.AGLEmbeddingD2.Wilson.Census219


theorem m24_dichotomy {X : Type} [Group X] [Finite X] (e : X ≃* NativeSporadic.M24)
    (c : X) (hc3 : orderOf c = 3) :
    CFSG.IsQuasisimple (centralizer ({c} : Set X)) ∨ Nat.card (centralizer ({c} : Set X)) = 504 := by
  have hb3 : (e c) ^ 3 = 1 := by
    rw [← map_pow, show c ^ 3 = 1 by rw [← hc3]; exact pow_orderOf_eq_one c, map_one]
  have hord : orderOf ((e c : NativeSporadic.M24) : Perm (Fin 24)) = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hc3]
  obtain ⟨r, hr, g, hg, hgr⟩ := m24_cover (e c).2 hord
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · left
    let gP : NativeSporadic.M24 := ⟨g, hg⟩
    let φ : X ≃* NativeSporadic.M24 := e.trans (MulAut.conj gP⁻¹)
    have hφ : φ c = m24y := by
      apply Subtype.ext
      show g⁻¹ * ((e c : NativeSporadic.M24) : Perm (Fin 24)) * g = permOfArr 24 m24xA
      rw [hgr]
      show g⁻¹ * (g * permOfArr 24 m24xA * g⁻¹) * g = permOfArr 24 m24xA
      group
    obtain ⟨-, ⟨e'⟩, -⟩ := m24_layer
    have hq : CFSG.IsQuasisimple ↥(centralizer ({m24y} : Set NativeSporadic.M24)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e'.symm m24Tc_spec.2.1
    let ε : centralizer ({c} : Set X) ≃* centralizer ({m24y} : Set NativeSporadic.M24) :=
      (centralizerEquivOfMulEquiv φ c).trans (MulEquiv.subgroupCongr (by rw [hφ]))
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv ε.symm hq
  · right
    calc Nat.card ↥(centralizer ({c} : Set X))
        = Nat.card ↥((centralizer ({c} : Set X)).map e.toMonoidHom) :=
          (Subgroup.card_map_of_injective e.injective).symm
      _ = Nat.card ↥(centralizer ({e c} : Set NativeSporadic.M24)) := by
          rw [Proving.centralizer_map_mulEquiv_wilson e c]
      _ = Nat.card ↥((centralizer ({e c} : Set NativeSporadic.M24)).map
            NativeSporadic.M24.subtype) :=
          (Subgroup.card_map_of_injective NativeSporadic.M24.subtype_injective).symm
      _ = Nat.card ↥(NativeSporadic.M24 ⊓
            centralizer ({((e c : NativeSporadic.M24) : Perm (Fin 24))} : Set (Perm (Fin 24)))) := by
          rw [CFSG.Sporadic.SmallOddCore.map_subtype_centralizer]
      _ = Nat.card ↥(centralizer ({((e c : NativeSporadic.M24) : Perm (Fin 24))} :
            Set (Perm (Fin 24))) ⊓ NativeSporadic.M24) := by rw [inf_comm]
      _ = Nat.card ↥(centralizer ({tp 24 m24Row3B.rep} : Set (Perm (Fin 24))) ⊓
            NativeSporadic.M24) := (card_centralizer_inf_conj NativeSporadic.M24 hg hgr.symm).symm
      _ = 504 := by rw [inf_comm]; exact m24_threeSpec_rowB

end CFSG.AGLEmbeddingD2.Wilson.Census424Rest
