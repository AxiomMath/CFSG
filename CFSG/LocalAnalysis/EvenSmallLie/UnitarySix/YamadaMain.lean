module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaTransitiveMain
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaCentralizerA
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaCTwo

public section

namespace CFSG.EvenSmallLie.UnitarySix.Yamada

open Subgroup CFSG.Blueprint

namespace Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {D : ToddParabolic L} {t : G}

theorem yamada_4_3
    (h : Setting G L D t) :
    (∀ x ∈ normalizer (toddE D t : Set G), ∃ y ∈ normalizer (toddA D : Set G) ⊓
        centralizer ({t} : Set G), ∃ c ∈ yamadaC2 D t, x = y * c) ∧
      centralizer ({t} : Set G) ⊓ yamadaC2 D t = toddE D t ∧
      (center (yamadaC2 D t)).map (yamadaC2 D t).subtype = toddA D ∧
      (∀ c ∈ yamadaC2 D t, c * t * c⁻¹ * t ∈ toddA D) ∧
      (∀ c ∈ yamadaC2 D t, ∀ d ∈ yamadaC2 D t,
        c * d * t * (c * d)⁻¹ * t = (c * t * c⁻¹ * t) * (d * t * d⁻¹ * t)) ∧
      (∀ a ∈ toddA D, ∃ c ∈ yamadaC2 D t, c * t * c⁻¹ * t = a) ∧
      (∀ c ∈ yamadaC2 D t, c * t * c⁻¹ * t = 1 ↔ c ∈ toddE D t) :=
  h.yamada_4_3_of h.omegaSet_eq (h.exists_mem_centralizer_toddA_not_comm h.omegaSet_eq)

end Setting

end CFSG.EvenSmallLie.UnitarySix.Yamada
