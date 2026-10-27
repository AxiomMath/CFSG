module

public import CFSG.LieType.Chevalley.C2E6UnitaryFourCompound
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaMinusPiecesModel

public section

namespace CFSG.SeitzReduction.F4Pilot

open Matrix CFSG.LieType.Chevalley.C2E6Overlap TauCeti.GLSymplecticFin
open CFSG.LieType.Universal.Symplectic.SpExtras (E)
open CFSG.SeitzReduction.SymplecticPilot (kOmMEmb kOmMVec)

abbrev EdgeV := Fin (3 + 1 - 1) ⊕ Fin (3 + 1 - 1) ⊕ Fin 2

abbrev EdgeW := Fin 6 ⊕ Fin 2

abbrev EdgeH := Fin 3 ⊕ Fin 3

@[expose] def edgeMat {α β : Type} [DecidableEq α] [DecidableEq β] (l : List (α × β)) :
    Matrix α β (ZMod 2) :=
  Matrix.of fun a b => if (a, b) ∈ l then 1 else 0

@[expose] def edgeP : Matrix EdgeV EdgeW (ZMod 2) :=
  edgeMat [(.inl 0, .inl 1), (.inl 0, .inl 4), (.inl 0, .inr 0), (.inl 0, .inr 1),
    (.inl 1, .inl 0), (.inl 2, .inl 2), (.inr (.inl 0), .inl 1), (.inr (.inl 0), .inl 4),
    (.inr (.inl 0), .inr 0), (.inr (.inl 1), .inl 5), (.inr (.inl 2), .inl 3),
    (.inr (.inr 0), .inl 1), (.inr (.inr 0), .inr 1), (.inr (.inr 1), .inl 1),
    (.inr (.inr 1), .inl 4)]

@[expose] def edgePinv : Matrix EdgeW EdgeV (ZMod 2) :=
  edgeMat [(.inl 0, .inl 1), (.inl 1, .inl 0), (.inl 1, .inr (.inl 0)), (.inl 1, .inr (.inr 0)),
    (.inl 2, .inl 2), (.inl 3, .inr (.inl 2)), (.inl 4, .inl 0), (.inl 4, .inr (.inl 0)),
    (.inl 4, .inr (.inr 0)), (.inl 4, .inr (.inr 1)), (.inl 5, .inr (.inl 1)),
    (.inr 0, .inr (.inl 0)), (.inr 0, .inr (.inr 1)), (.inr 1, .inl 0), (.inr 1, .inr (.inl 0))]

@[expose] def edgeC : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  edgeMat [(0, 1), (1, 0), (1, 1)]

@[expose] def edgeD (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Matrix EdgeW EdgeW (ZMod 2) :=
  fromBlocks (ext2 A) 0 0 1

@[expose] def edgeMu (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Matrix EdgeV EdgeV (ZMod 2) :=
  edgeP * edgeD A * edgePinv

@[expose] def edgeT (i j : Fin 4) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  1 + single i j 1

@[expose] def edgeSg (C D : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix EdgeV EdgeV (ZMod 2) :=
  Matrix.of fun a b => match a, b with
    | .inl i, .inl j => C i j
    | .inr (.inl i), .inr (.inl j) => D i j
    | .inr (.inr i), .inr (.inr j) => if i = j then 1 else 0
    | _, _ => 0

@[expose] def edgeLev (C D : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix EdgeH EdgeH (ZMod 2) :=
  fromBlocks C 0 0 D

@[expose] noncomputable def edgeSp (r : RootSubgroupIndex 3) : Matrix EdgeH EdgeH (ZMod 2) :=
  1 + E (ZMod 2) r

@[expose] def edgeS01 : Matrix (Fin 3) (Fin 3) (ZMod 2) := edgeMat [(0, 1), (1, 0), (2, 2)]

@[expose] def edgeS02 : Matrix (Fin 3) (Fin 3) (ZMod 2) := edgeMat [(0, 2), (1, 1), (2, 0)]

@[expose] def edgeC01 : Matrix (Fin 3) (Fin 3) (ZMod 2) := edgeMat [(0, 0), (0, 1), (1, 1), (2, 2)]

@[expose] def edgeC10 : Matrix (Fin 3) (Fin 3) (ZMod 2) := edgeMat [(0, 0), (1, 0), (1, 1), (2, 2)]

@[expose] def edgeVec : EdgeV → ZMod 2 := Pi.single (Sum.inr (Sum.inr 0)) 1

theorem edgeP_mul_edgePinv : edgeP * edgePinv = 1 := by decide +kernel

theorem edgePinv_mul_edgeP : edgePinv * edgeP = 1 := by decide +kernel

theorem edgeMu_t02_vec : edgeMu (edgeT 0 2) *ᵥ edgeVec = edgeVec := by decide +kernel

theorem edgeMu_t20_vec : edgeMu (edgeT 2 0) *ᵥ edgeVec = edgeVec := by decide +kernel

theorem edgeMu_t13_vec : edgeMu (edgeT 1 3) *ᵥ edgeVec = edgeVec := by decide +kernel

theorem edgeMu_t31_vec : edgeMu (edgeT 3 1) *ᵥ edgeVec = edgeVec := by decide +kernel

theorem edgeMu_plus_vec : edgeMu (edgeT 0 3 * edgeT 1 2) *ᵥ edgeVec = edgeVec := by
  decide +kernel

theorem edgeMu_minus_vec : edgeMu (edgeT 2 1 * edgeT 3 0) *ᵥ edgeVec = edgeVec := by
  decide +kernel

theorem edgeMu_t02_hyp : (edgeMu (edgeT 0 2)).submatrix (kOmMEmb 3) (kOmMEmb 3) =
    edgeSp (.positiveSum 1 2 (by decide)) := by decide +kernel

theorem edgeMu_t20_hyp : (edgeMu (edgeT 2 0)).submatrix (kOmMEmb 3) (kOmMEmb 3) =
    edgeSp (.negativeSum 1 2 (by decide)) := by decide +kernel

theorem edgeMu_t13_hyp : (edgeMu (edgeT 1 3)).submatrix (kOmMEmb 3) (kOmMEmb 3) =
    edgeSp (.difference 1 2 (by decide)) := by decide +kernel

theorem edgeMu_t31_hyp : (edgeMu (edgeT 3 1)).submatrix (kOmMEmb 3) (kOmMEmb 3) =
    edgeSp (.difference 2 1 (by decide)) := by decide +kernel

theorem edgeMu_plus_hyp : (edgeMu (edgeT 0 3 * edgeT 1 2)).submatrix (kOmMEmb 3) (kOmMEmb 3) =
    edgeSp (.positiveLong 1) := by decide +kernel

theorem edgeMu_minus_hyp : (edgeMu (edgeT 2 1 * edgeT 3 0)).submatrix (kOmMEmb 3) (kOmMEmb 3) =
    edgeSp (.negativeLong 1) := by decide +kernel

theorem edgeMc_eq : edgeSg edgeS01 edgeS01 * edgeMu (edgeT 0 3 * edgeT 1 2) *
      edgeMu (edgeT 2 1 * edgeT 3 0) * edgeSg edgeS01 edgeS01 =
    edgeP * (fromBlocks (1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) 0 0 edgeC :
      Matrix EdgeW EdgeW (ZMod 2)) * edgePinv := by decide +kernel

@[expose] def edgeRu : Matrix EdgeV EdgeV (ZMod 2) :=
  edgeSg edgeC01 edgeC10 * edgeSg edgeS02 edgeS02 * edgeMu (edgeT 2 0) * edgeSg edgeS02 edgeS02

@[expose] def edgeRu' : Matrix EdgeV EdgeV (ZMod 2) :=
  edgeSg edgeC10 edgeC01 * edgeSg edgeS02 edgeS02 * edgeMu (edgeT 0 2) * edgeSg edgeS02 edgeS02

theorem edgeRu_commute_t01 : edgeRu * edgeMu (edgeT 0 1) = edgeMu (edgeT 0 1) * edgeRu := by
  decide +kernel

theorem edgeRu_commute_t10 : edgeRu * edgeMu (edgeT 1 0) = edgeMu (edgeT 1 0) * edgeRu := by
  decide +kernel

theorem edgeRu'_commute_t01 : edgeRu' * edgeMu (edgeT 0 1) = edgeMu (edgeT 0 1) * edgeRu' := by
  decide +kernel

theorem edgeRu'_commute_t10 : edgeRu' * edgeMu (edgeT 1 0) = edgeMu (edgeT 1 0) * edgeRu' := by
  decide +kernel

theorem edgeC01_mul_transpose : edgeC01 * edgeC10ᵀ = 1 := by decide +kernel

theorem edgeC10_mul_transpose : edgeC10 * edgeC01ᵀ = 1 := by decide +kernel

theorem edgeS01_mul_transpose : edgeS01 * edgeS01ᵀ = 1 := by decide +kernel

theorem edgeS02_mul_transpose : edgeS02 * edgeS02ᵀ = 1 := by decide +kernel

theorem det_edgeC01 : edgeC01.det = 1 := by decide +kernel

theorem det_edgeC10 : edgeC10.det = 1 := by decide +kernel

theorem det_edgeS01 : edgeS01.det = 1 := by decide +kernel

theorem det_edgeS02 : edgeS02.det = 1 := by decide +kernel

theorem edgeSp_c_eq : edgeSp (.positiveLong 0) * edgeSp (.negativeLong 0) =
    edgeLev edgeS01 edgeS01 * edgeSp (.positiveLong 1) * edgeSp (.negativeLong 1) *
      edgeLev edgeS01 edgeS01 := by decide +kernel

theorem edgeSp_M01_eq : edgeSp (.negativeSum 0 1 (by decide)) =
    edgeLev edgeS02 edgeS02 * edgeSp (.negativeSum 1 2 (by decide)) *
      edgeLev edgeS02 edgeS02 := by decide +kernel

theorem edgeSp_P01_eq : edgeSp (.positiveSum 0 1 (by decide)) =
    edgeLev edgeS02 edgeS02 * edgeSp (.positiveSum 1 2 (by decide)) *
      edgeLev edgeS02 edgeS02 := by decide +kernel

theorem edgeSp_D01_eq : edgeSp (.difference 0 1 (by decide)) = edgeLev edgeC01 edgeC10 := by
  decide +kernel

theorem edgeSp_D10_eq : edgeSp (.difference 1 0 (by decide)) = edgeLev edgeC10 edgeC01 := by
  decide +kernel

@[expose] noncomputable def edgeSpH : Matrix EdgeH EdgeH (ZMod 2) :=
  edgeSp (.negativeLong 0) * edgeSp (.difference 0 1 (by decide)) *
    edgeSp (.positiveSum 0 1 (by decide))

@[expose] noncomputable def edgeSpZr : Matrix EdgeH EdgeH (ZMod 2) :=
  edgeSp (.positiveSum 0 1 (by decide)) * edgeSp (.negativeSum 0 1 (by decide))

@[expose] noncomputable def edgeSpZb : Matrix EdgeH EdgeH (ZMod 2) :=
  edgeSp (.difference 0 1 (by decide)) * edgeSp (.difference 1 0 (by decide))

theorem edgeSp_hz : edgeSpH * (edgeSp (.positiveLong 0) * edgeSp (.negativeLong 0)) =
    edgeSpZr * edgeSpZb * edgeSpH := by decide +kernel

theorem edgeSp_hz' : edgeSpH * (edgeSp (.positiveLong 1) * edgeSp (.negativeLong 1)) =
    edgeSpZr * (edgeSp (.difference 1 0 (by decide)) * edgeSp (.difference 0 1 (by decide))) *
      edgeSpH := by decide +kernel

theorem edgeSp_hu : edgeSpH * (edgeSp (.difference 1 2 (by decide)) *
      edgeSp (.negativeSum 1 2 (by decide))) =
    (edgeSp (.difference 1 2 (by decide)) * edgeSp (.negativeSum 1 2 (by decide))) * edgeSpH := by
  decide +kernel

theorem edgeSp_hu' : edgeSpH * (edgeSp (.difference 2 1 (by decide)) *
      edgeSp (.positiveSum 1 2 (by decide))) =
    (edgeSp (.difference 2 1 (by decide)) * edgeSp (.positiveSum 1 2 (by decide))) * edgeSpH := by
  decide +kernel

theorem edgeSp_zr_cube : edgeSpZr * edgeSpZr * edgeSpZr = 1 := by decide +kernel

theorem edgeSp_zr_ne_one : edgeSpZr ≠ 1 := by decide +kernel

theorem edgeSp_zr_comm : edgeSpZr * edgeSpZb = edgeSpZb * edgeSpZr := by decide +kernel

end CFSG.SeitzReduction.F4Pilot
