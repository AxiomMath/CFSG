module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactFour
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMismatchTables
public import CFSG.RankThree.PartOne.K159.Klein
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactLevel

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.SeitzReduction.OmegaPilot (diagOmega)
open CFSG.Quasithin (perfectCore)

section Torus

theorem isHypFrame_quadPlus_inl_inr (K : Type) [Field K] (m : ℕ) :
    OmegaPilot.IsHypFrame (CFSG.LieType.Universal.Spin.quadPlus m K)
      (Sum.inl : Fin m → Fin m ⊕ Fin m) Sum.inr where
  hyp i := OmegaPilot.isHypCoord_quadPlus i
  left_injective := Sum.inl_injective
  right_injective := Sum.inr_injective
  left_ne_right _ _ := Sum.inl_ne_inr

theorem toLinEquiv_diagOmega {K : Type} [Field K] {m : ℕ} (t : Fin m → Kˣ) :
    CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m) K (diagOmega K m t) =
      OmegaPilot.frameLin Sum.inl Sum.inr t := by
  ext v a
  rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, OmegaPilot.frameLin_apply,
    OmegaPilot.diagOmega_coe, mulVec_diagonal]
  congr 1
  rcases a with i | i
  · rw [SymplecticPilot.diagSpEntry_inl, (isHypFrame_quadPlus_inl_inr K m).frameEntry_left]
  · rw [SymplecticPilot.diagSpEntry_inr, (isHypFrame_quadPlus_inl_inr K m).frameEntry_right]

theorem diagOmega_mem_statedOmega {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (t : Fin m → Kˣ) : diagOmega K m t ∈ StatedOmega (StatedQuadPlus m K) := by
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap
      (CFSG.LieType.Universal.Spin.coe_quadPlus m K), Subgroup.mem_comap,
    MulEquiv.coe_toMonoidHom, toLinEquiv_diagOmega]
  exact (isHypFrame_quadPlus_inl_inr K m).frameLin_mem_orthDerived t

theorem diagOmega_mem_omegaPlus8 (k : Type) [Field k] [Finite k] [CharP k 2] (t : Fin 4 → kˣ) :
    diagOmega k 4 t ∈ StatedOmega (StatedQuadPlus 4 k) :=
  diagOmega_mem_statedOmega t

end Torus

section Orders

variable {K : Type} [Field K] [Finite K]

theorem natCard_specialLinearGroup_eq_ordSL {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (SpecialLinearGroup (Fin n) K) = ordSL n (Nat.card K) :=
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq hn

theorem natCard_statedOmega_quadPlus_three [CharP K 2] (hK : 4 ≤ Nat.card K) :
    Nat.card (StatedOmega (StatedQuadPlus 3 K)) = ordSL 4 (Nat.card K) := by
  obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) (n := 3) le_rfl
  obtain ⟨κ⟩ := CFSG.RankThree.PartOne.K159.Klein.klein_commutator_orthogonal_six
    (CFSG.LieType.Universal.Spin.quadPlus 3 K) hQ (by simp) hT hK
  set O := TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadPlus 3 K)
    with hO
  have h1 : (commutator ↥O).map O.subtype = ⁅O, O⁆ := Subgroup.map_subtype_commutator _
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap
      (CFSG.LieType.Universal.Spin.coe_quadPlus 3 K), ← hO, Subgroup.comap_equiv_eq_map_symm',
    Subgroup.card_map_of_injective (MulEquiv.injective _), ← h1,
    Subgroup.card_map_of_injective O.subtype_injective, Nat.card_congr κ.toEquiv,
    ← Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 K).toEquiv]
  exact natCard_specialLinearGroup_eq_ordSL (by norm_num)

theorem natCard_perfectCore_omegaBlock_of_card_two [CharP K 2] (hK : 4 ≤ Nat.card K) {m : ℕ}
    {I : Finset (Fin m)} (hI : I.card = 2) :
    Nat.card (perfectCore (OmegaPilot.omegaBlock K I)) = ordSL 2 (Nat.card K) ^ 2 := by
  obtain ⟨e⟩ := OmegaPilot.nonempty_perfectCore_omegaBlock_mulEquiv_SL2 hK hI
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, natCard_specialLinearGroup_eq_ordSL (by norm_num),
    sq]

theorem natCard_omegaLeviSL {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (OmegaPilot.omegaLeviSL K n) = ordSL n (Nat.card K) := by
  rw [← Nat.card_congr (OmegaPilot.omegaLeviSLEquiv (F := K) (k := n)).toEquiv]
  exact natCard_specialLinearGroup_eq_ordSL hn

end Orders

end CFSG.SeitzReduction.F4Pilot
