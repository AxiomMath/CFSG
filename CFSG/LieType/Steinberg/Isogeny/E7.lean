module

public import CFSG.LieType.Steinberg.Isogeny.Minuscule
public import CFSG.LieType.Steinberg.Isogeny.E7.RelSign
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121

public noncomputable section

namespace CFSG.LieType.Steinberg.Isogeny

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Adjoint

theorem e7_checkSigns : checkSigns e7Data e7AdjData = true := by decide +kernel

open _root_.Classical in
@[expose] def e7Eps (γ : Fin (Tag.rank .E7) → ℤ) : ℤ :=
  if h : IsRoot .E7 γ then e7RelSign (rootPos ⟨γ, h⟩) else 1

theorem e7Eps_of_isRoot {γ : Fin (Tag.rank .E7) → ℤ} (h : IsRoot .E7 γ) :
    e7Eps γ = e7RelSign (rootPos ⟨γ, h⟩) := by
  classical
  exact dite_eq_left h

theorem e7Eps_eq_one_or (γ : Fin (Tag.rank .E7) → ℤ) : e7Eps γ = 1 ∨ e7Eps γ = -1 := by
  classical
  unfold e7Eps e7RelSign
  split_ifs <;> simp

variable (k : Type) [Field k] [Finite k]

@[expose] def e7Isogeny : ↥(e7Data_valid.minGroup k) →* ↥(adjointGroup .E7 k) :=
  isogeny e7Data_valid posDef_cartan_E7 (rootOperatorFamily .E7) e7AdjData_valid noG2_E7
    e7_checkSigns k (roots_eq isFiniteType_cartan_E7) (e7_presentationB k)

theorem e7Isogeny_xm (γ : Fin (Tag.rank .E7) → ℤ) (c : k) :
    e7Isogeny k (e7Data_valid.xm k γ c) =
      xPar (rootOperatorFamily .E7) γ ((e7Eps γ : k) * c) := by
  by_cases hγ : IsRoot .E7 γ
  · have h : e7Isogeny k (e7Data_valid.xm k γ c) =
        yPar (rootOperatorFamily .E7) e7AdjData_valid γ c :=
      isogeny_xm _ _ _ _ _ _ _ _ _ hγ c
    rw [h, yPar, relSignOr_of_isRoot hγ, relSign_e7, e7Eps_of_isRoot hγ]
  · rw [e7Data_valid.xm_of_not_isRoot k hγ, map_one, xPar_of_not_isRoot hγ]

theorem e7Isogeny_xm_single (j : Fin (Tag.rank .E7)) (c : k) :
    e7Isogeny k (e7Data_valid.xm k (Pi.single j 1) c) =
      (rootOperatorFamily .E7).eltElement (simpleRoot .E7 j) c :=
  isogeny_xm_single _ _ _ _ _ _ _ _ _ j c

theorem e7Isogeny_xm_neg_single (j : Fin (Tag.rank .E7)) (c : k) :
    e7Isogeny k (e7Data_valid.xm k (-Pi.single j 1) c) =
      (rootOperatorFamily .E7).eltElement (-simpleRoot .E7 j) c :=
  isogeny_xm_neg_single _ _ _ _ _ _ _ _ _ j c

theorem e7Isogeny_surjective : Function.Surjective (e7Isogeny k) :=
  isogeny_surjective _ _ _ _ _ _ _ _ _

theorem exists_e7Isogeny_ne_one : ∃ g, e7Isogeny k g ≠ 1 :=
  isogeny_ne_one _ _ _ _ _ _ _ _ _

end CFSG.LieType.Steinberg.Isogeny
