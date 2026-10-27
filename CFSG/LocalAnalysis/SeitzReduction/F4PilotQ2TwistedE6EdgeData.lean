module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2TwistedE6EdgeKlein
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6EdgeMat

public section

namespace CFSG.SeitzReduction.F4Pilot

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.SeitzReduction.SymplecticPilot (kOmegaVec kOmegaEmb zThreeMat)
open CFSG.LieType.Steinberg.Sp (blockMat)

abbrev twCast : ZMod 2 →+* TwF4 := algebraMap (ZMod 2) TwF4

@[expose] def twMu0 (A : Matrix (Fin 4) (Fin 4) TwF4) : Matrix omPI omPI (ZMod 2) :=
  omPT * fromBlocks (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 (omMMat6 (twKappa A)) * omPTi

@[expose] def twA03 : Matrix (Fin 4) (Fin 4) (ZMod 2) := 1 + single 0 3 1

@[expose] def twA30 : Matrix (Fin 4) (Fin 4) (ZMod 2) := 1 + single 3 0 1

@[expose] def twA12 : Matrix (Fin 4) (Fin 4) (ZMod 2) := 1 + single 1 2 1

@[expose] def twA21 : Matrix (Fin 4) (Fin 4) (ZMod 2) := 1 + single 2 1 1

@[expose] def twA0123 : Matrix (Fin 4) (Fin 4) (ZMod 2) := 1 + single 0 1 1 + single 2 3 1

@[expose] def twX (a : TwF4) : Matrix (Fin 4) (Fin 4) TwF4 :=
  1 + single 0 1 a + single 2 3 (CFSG.LieType.Chevalley.C2E6Overlap.bar a)

@[expose] def twX' (a : TwF4) : Matrix (Fin 4) (Fin 4) TwF4 :=
  1 + single 1 0 a + single 3 2 (CFSG.LieType.Chevalley.C2E6Overlap.bar a)

@[expose] def twMuA03Tab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 0, 1, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def twMuA30Tab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 1, 0, 0;
    0, 1, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def twMuA12Tab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def twMuA21Tab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 1, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def twMuA0123Tab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 1, 0, 0, 1, 1;
    0, 0, 0, 1, 0, 0, 1, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1, 1]

theorem twMu0_A03 : twMu0 (twA03.map twCast) = omPMat twMuA03Tab := by decide +kernel

theorem twMu0_A30 : twMu0 (twA30.map twCast) = omPMat twMuA30Tab := by decide +kernel

theorem twMu0_A12 : twMu0 (twA12.map twCast) = omPMat twMuA12Tab := by decide +kernel

theorem twMu0_A21 : twMu0 (twA21.map twCast) = omPMat twMuA21Tab := by decide +kernel

theorem twMu0_A0123 : twMu0 (twA0123.map twCast) = omPMat twMuA0123Tab := by decide +kernel

theorem twMuA03Tab_ne_one : omPMat twMuA03Tab ≠ 1 := by decide +kernel

theorem twMuA03_vec : omPMat twMuA03Tab *ᵥ kOmegaVec (ZMod 2) 3 = kOmegaVec (ZMod 2) 3 := by
  decide +kernel

theorem twMuA30_vec : omPMat twMuA30Tab *ᵥ kOmegaVec (ZMod 2) 3 = kOmegaVec (ZMod 2) 3 := by
  decide +kernel

theorem twMuA12_vec : omPMat twMuA12Tab *ᵥ kOmegaVec (ZMod 2) 3 = kOmegaVec (ZMod 2) 3 := by
  decide +kernel

theorem twMuA21_vec : omPMat twMuA21Tab *ᵥ kOmegaVec (ZMod 2) 3 = kOmegaVec (ZMod 2) 3 := by
  decide +kernel

theorem twMuA0123_vec : omPMat twMuA0123Tab *ᵥ kOmegaVec (ZMod 2) 3 = kOmegaVec (ZMod 2) 3 := by
  decide +kernel

theorem twMuA03_hyp : (omPMat twMuA03Tab).submatrix (kOmegaEmb 3) (kOmegaEmb 3) =
    edgeSp (.positiveSum 1 2 (by decide)) := by decide +kernel

theorem twMuA30_hyp : (omPMat twMuA30Tab).submatrix (kOmegaEmb 3) (kOmegaEmb 3) =
    edgeSp (.negativeSum 1 2 (by decide)) := by decide +kernel

theorem twMuA12_hyp : (omPMat twMuA12Tab).submatrix (kOmegaEmb 3) (kOmegaEmb 3) =
    edgeSp (.difference 1 2 (by decide)) := by decide +kernel

theorem twMuA21_hyp : (omPMat twMuA21Tab).submatrix (kOmegaEmb 3) (kOmegaEmb 3) =
    edgeSp (.difference 2 1 (by decide)) := by decide +kernel

theorem twMuA0123_hyp : (omPMat twMuA0123Tab).submatrix (kOmegaEmb 3) (kOmegaEmb 3) =
    edgeSp (.positiveLong 2) := by decide +kernel

@[expose] def twS02 : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2) :=
  edgeMat [(0, 2), (1, 1), (2, 0), (3, 3)]

@[expose] def twPiMat : Matrix omPI omPI (ZMod 2) := fromBlocks twS02 0 0 twS02

theorem twS02_det : twS02.det = 1 := by decide +kernel

theorem twS02_mul_transpose : twS02 * twS02ᵀ = 1 := by decide +kernel

theorem twS02_three : ∀ j : Fin (3 + 1),
    twS02 3 j = (1 : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) 3 j ∧
      twS02 j 3 = (1 : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) j 3 := by
  decide +kernel

theorem twPiMat_vec : twPiMat *ᵥ kOmegaVec (ZMod 2) 3 = kOmegaVec (ZMod 2) 3 := by
  decide +kernel

theorem twPiMat_hyp :
    twPiMat.submatrix (kOmegaEmb 3) (kOmegaEmb 3) = edgeLev edgeS02 edgeS02 := by
  decide +kernel

theorem edgeSp_cPrime_eq_blockMat :
    edgeSp (.positiveLong 0) * edgeSp (.negativeLong 0) =
      blockMat (Sum.inl 0) (Sum.inr 0) (zThreeMat (K := ZMod 2)) := by
  decide +kernel

theorem edgeSp_relay_eq_conj :
    edgeSp (.difference 0 1 (by decide)) * edgeSp (.negativeSum 0 1 (by decide)) =
      edgeLev edgeS02 edgeS02 * (edgeSp (.difference 2 1 (by decide)) *
        edgeSp (.negativeSum 1 2 (by decide))) * edgeLev edgeS02 edgeS02 := by
  decide +kernel

theorem edgeSp_relay'_eq_conj :
    edgeSp (.difference 1 0 (by decide)) * edgeSp (.positiveSum 0 1 (by decide)) =
      edgeLev edgeS02 edgeS02 * (edgeSp (.difference 1 2 (by decide)) *
        edgeSp (.positiveSum 1 2 (by decide))) * edgeLev edgeS02 edgeS02 := by
  decide +kernel

@[expose] def twRuTab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 1, 0, 0, 1, 0, 0, 0;
    1, 1, 0, 0, 1, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def twRu'Tab : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 1, 0, 0;
    1, 1, 0, 0, 1, 1, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

theorem twRu_eq : twPiMat * omPMat twMuA21Tab * omPMat twMuA30Tab * twPiMat = omPMat twRuTab := by
  decide +kernel

theorem twRu'_eq :
    twPiMat * omPMat twMuA12Tab * omPMat twMuA03Tab * twPiMat = omPMat twRu'Tab := by
  decide +kernel

theorem twRu_commute_twX : ∀ a : TwF4,
    omPMat twRuTab * twMu0 (twX a) = twMu0 (twX a) * omPMat twRuTab := by
  decide +kernel

theorem twRu_commute_twX' : ∀ a : TwF4,
    omPMat twRuTab * twMu0 (twX' a) = twMu0 (twX' a) * omPMat twRuTab := by
  decide +kernel

theorem twRu'_commute_twX : ∀ a : TwF4,
    omPMat twRu'Tab * twMu0 (twX a) = twMu0 (twX a) * omPMat twRu'Tab := by
  decide +kernel

theorem twRu'_commute_twX' : ∀ a : TwF4,
    omPMat twRu'Tab * twMu0 (twX' a) = twMu0 (twX' a) * omPMat twRu'Tab := by
  decide +kernel

end CFSG.SeitzReduction.F4Pilot
