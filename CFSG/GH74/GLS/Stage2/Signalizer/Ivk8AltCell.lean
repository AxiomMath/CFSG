module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgFin
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8AltY

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Common

variable {A : Type} [Group A] {J : Subgroup A}

theorem le_normalizer_of_unique {M : Subgroup A} (hJ : IsComponent J)
    (hu : ∀ K : Subgroup A, IsComponent K → K = J) : M ≤ normalizer (J : Set A) := by
  have hJn : J.Normal := Gen.normal_of_unique_comp hJ hu
  rw [Subgroup.normalizer_eq_top]
  exact le_top

end Common

section Frame

variable {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb J : Subgroup A}

theorem alt_mid_false (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J)
    (hnc : ¬ Vb ≤ centralizer (J : Set A)) {n : ℕ} (h8 : 8 ≤ n) (h10 : n ≤ 10)
    (e : (↥J ⧸ center ↥J) ≃* alternatingGroup (Fin n)) : False := by
  obtain ⟨-, hcfg⟩ := hfr.sylCfg hJ hnc
  exact altY_not_sylCfg n h8 h10 _ e hcfg

end Frame

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
