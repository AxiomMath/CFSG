module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesOrders
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusTorus
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesEmbed
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoresForms
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFact
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSetup
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactPiece
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Open.QuasithinDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Walter.JRFacts

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadMinus)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.SymplecticPilot (suppGL)

local notation "ι₈" => Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2

section Torus

variable {k : Type} [Field k]

theorem diagOmegaMinus_apply_ne (t : Fin 3 → kˣ) {a b : ι₈} (hab : a ≠ b) :
    (diagOmegaMinus k t : Matrix ι₈ ι₈ k) a b = 0 := by
  rw [diagOmegaMinus_coe, diagonal_apply_ne _ hab]

theorem diagOmegaMinus_apply_self (t : Fin 3 → kˣ) (a : ι₈) :
    (diagOmegaMinus k t : Matrix ι₈ ι₈ k) a a = minusWeight k t a := by
  rw [diagOmegaMinus_coe, diagonal_apply_eq]

theorem perfectCore_inf_centralizer_diagOmegaMinus [Finite k] (H : Subgroup (GL ι₈ k))
    {S : Set ι₈} (Ts : Set (Fin 3 → kˣ))
    (hconst : ∀ t ∈ Ts, ∀ a ∈ S, ∀ b ∈ S, minusWeight k t a = minusWeight k t b)
    (hsep : ∀ a b : ι₈, a ≠ b → (a ∉ S ∨ b ∉ S) →
      ∃ t ∈ Ts, minusWeight k t a ≠ minusWeight k t b) :
    perfectCore (H ⊓ centralizer (diagOmegaMinus k '' Ts)) = perfectCore (H ⊓ suppGL k S) := by
  have hSC : suppGL k S ≤ centralizer (diagOmegaMinus k '' Ts) := by
    intro x hx
    rw [mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    refine ((SymplecticPilot.commute_of_diag_iff
      (fun a b hab => diagOmegaMinus_apply_ne t hab) x).2 fun a b hab => ?_).eq.symm
    rw [diagOmegaMinus_apply_self, diagOmegaMinus_apply_self] at hab
    by_cases h : a ∈ S ∧ b ∈ S
    · exact absurd (hconst t ht a h.1 b h.2) hab
    · have hne : a ≠ b := fun e => hab (e ▸ rfl)
      rw [hx a b h, Matrix.one_apply_ne hne]
  rw [SymplecticPilot.perfectCore_inf_centralizer_eq_perfectCore_inf_suppGL (T := Set.univ)
      (fun x _ a b hab => absurd ⟨Set.mem_univ a, Set.mem_univ b⟩ hab) (diagOmegaMinus k '' Ts)
      (by rintro _ ⟨t, -, rfl⟩ a b hab; exact diagOmegaMinus_apply_ne t hab)
      (fun a _ b _ hab hS => by
        obtain ⟨t, ht, hne⟩ := hsep a b hab hS
        exact ⟨diagOmegaMinus k t, ⟨t, ht, rfl⟩, by
          rw [diagOmegaMinus_apply_self, diagOmegaMinus_apply_self]; exact hne⟩),
    inf_of_le_left (inf_le_right.trans hSC)]

theorem minusWeight_eq_coe (t : Fin 3 → kˣ) (a : ι₈) :
    minusWeight k t a = ((minusDiagUnits k t a : kˣ) : k) := by
  rcases a with i | i | j <;> rfl

theorem minusWeight_mulSingle_ne {κ : kˣ} (hκ : κ * κ ≠ 1) (i : Fin 3) {a b : ι₈} (hab : a ≠ b)
    (ha : a = Sum.inl i ∨ a = Sum.inr (Sum.inl i)) :
    minusWeight k (Pi.mulSingle i κ) a ≠ minusWeight k (Pi.mulSingle i κ) b := by
  have hκ1 : κ ≠ 1 := SymplecticPilot.units_ne_one_of_mul_self_ne_one hκ
  have hκi : κ ≠ κ⁻¹ := fun h => hκ (mul_eq_one_iff_eq_inv.2 h)
  rw [minusWeight_eq_coe, minusWeight_eq_coe]
  intro h
  have h' := Units.ext h
  rcases ha with rfl | rfl <;> rcases b with j | j | j <;>
    [have hj : j ≠ i := fun e => hab (by rw [e]); by_cases hj : j = i; skip;
      by_cases hj : j = i; have hj : j ≠ i := fun e => hab (by rw [e]); skip] <;>
    (try subst hj) <;>
    simp [minusDiagUnits, Pi.mulSingle_eq_of_ne, hκi.symm, *] at h'

end Torus

section Coords

@[expose] def minusEmbA : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → ι₈ :=
  Sum.map (Fin.succ : Fin (3 - 1) → Fin (4 - 1))
    (Sum.map (Fin.succ : Fin (3 - 1) → Fin (4 - 1)) id)

theorem minusEmbA_injective : Function.Injective minusEmbA :=
  Sum.map_injective.2 ⟨Fin.succ_injective _, Sum.map_injective.2 ⟨Fin.succ_injective _,
    Function.injective_id⟩⟩

theorem eq_of_not_mem_range_minusEmbA {a : ι₈} (ha : a ∉ Set.range minusEmbA) :
    a = Sum.inl 0 ∨ a = Sum.inr (Sum.inl 0) := by
  rcases a with i | i | j
  · left
    refine congrArg Sum.inl ?_
    by_contra hi
    obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 hi
    exact ha ⟨Sum.inl i', rfl⟩
  · right
    refine congrArg (fun x => Sum.inr (Sum.inl x)) ?_
    by_contra hi
    obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 hi
    exact ha ⟨Sum.inr (Sum.inl i'), rfl⟩
  · exact absurd ⟨Sum.inr (Sum.inr j), rfl⟩ ha

@[expose] def minusEmbTwo : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → ι₈ :=
  Sum.map (fun _ => (2 : Fin (4 - 1))) (Sum.map (fun _ => (2 : Fin (4 - 1))) id)

theorem minusEmbTwo_injective : Function.Injective minusEmbTwo :=
  Sum.map_injective.2 ⟨fun x y _ => Subsingleton.elim (α := Fin 1) x y, Sum.map_injective.2
    ⟨fun x y _ => Subsingleton.elim (α := Fin 1) x y, Function.injective_id⟩⟩

theorem exists_of_not_mem_range_minusEmbTwo {a : ι₈} (ha : a ∉ Set.range minusEmbTwo) :
    ∃ i : Fin 3, i ≠ 2 ∧ (a = Sum.inl i ∨ a = Sum.inr (Sum.inl i)) := by
  rcases a with i | i | j
  · refine ⟨i, fun hi => ha ⟨Sum.inl 0, ?_⟩, Or.inl rfl⟩
    rw [hi]
    rfl
  · refine ⟨i, fun hi => ha ⟨Sum.inr (Sum.inl 0), ?_⟩, Or.inr rfl⟩
    rw [hi]
    rfl
  · exact absurd ⟨Sum.inr (Sum.inr j), rfl⟩ ha

variable {k : Type} [Field k]

theorem isCoordSplit_minusEmbA (b c : k) :
    IsCoordSplit (StatedQuadMinus 4 k b c) (StatedQuadMinus 3 k b c) minusEmbA := by
  refine ⟨fun v => v (Sum.inl 0) * v (Sum.inr (Sum.inl 0)), fun v => ?_, fun v w h => ?_⟩
  · simp only [StatedQuadMinus, Function.comp_apply, minusEmbA, Sum.map_inl, Sum.map_inr, id]
    rw [Fin.sum_univ_succ (n := 2)]
    ring
  · have h0 : (Sum.inl 0 : ι₈) ∉ Set.range minusEmbA := by
      rintro ⟨x | x | x, hx⟩ <;> simp [minusEmbA] at hx
    have h1 : (Sum.inr (Sum.inl 0) : ι₈) ∉ Set.range minusEmbA := by
      rintro ⟨x | x | x, hx⟩ <;> simp [minusEmbA] at hx
    simp only [h _ h0, h _ h1]

theorem isCoordSplit_minusEmbTwo (b c : k) :
    IsCoordSplit (StatedQuadMinus 4 k b c) (StatedQuadMinus 2 k b c) minusEmbTwo := by
  refine ⟨fun v => v (Sum.inl 0) * v (Sum.inr (Sum.inl 0)) +
    v (Sum.inl 1) * v (Sum.inr (Sum.inl 1)), fun v => ?_, fun v w h => ?_⟩
  · simp only [StatedQuadMinus, Function.comp_apply, minusEmbTwo, Sum.map_inl, Sum.map_inr, id]
    rw [Fin.sum_univ_three, Fin.sum_univ_one]
    ring
  · have hn : ∀ i : Fin 3, i ≠ 2 → (Sum.inl i : ι₈) ∉ Set.range minusEmbTwo ∧
        (Sum.inr (Sum.inl i) : ι₈) ∉ Set.range minusEmbTwo := fun i hi => by
      refine ⟨?_, ?_⟩ <;> rintro ⟨x | x | x, hx⟩ <;> simp [minusEmbTwo] at hx <;>
        exact hi hx.symm
    simp only [h _ (hn 0 (by decide)).1, h _ (hn 0 (by decide)).2, h _ (hn 1 (by decide)).1,
      h _ (hn 1 (by decide)).2]

end Coords

section Pieces

theorem minusWeight_minusEmbA {k : Type} [Field k] {t : Fin 3 → kˣ} (ht1 : t 1 = 1)
    (ht2 : t 2 = 1) (x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) :
    minusWeight k t (minusEmbA x) = 1 := by
  rcases x with i | i | j
  · fin_cases i <;> simp [minusWeight, minusEmbA, ht1, ht2]
  · fin_cases i <;> simp [minusWeight, minusEmbA, ht1, ht2]
  · simp [minusWeight, minusEmbA]

theorem minusWeight_minusEmbTwo {k : Type} [Field k] {t : Fin 3 → kˣ} (ht2 : t 2 = 1)
    (x : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) : minusWeight k t (minusEmbTwo x) = 1 := by
  rcases x with i | i | j
  · simp [minusWeight, minusEmbTwo, ht2]
  · simp [minusWeight, minusEmbTwo, ht2]
  · simp [minusWeight, minusEmbTwo]

theorem perfectCore_omegaMinus8_A_eq (k : Type) [Field k] [Finite k] [CharP k 2] {b c : k}
    (hk : 4 ≤ Nat.card k) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    perfectCore (StatedOmega (StatedQuadMinus 4 k b c) ⊓
      Subgroup.centralizer (diagOmegaMinus k '' {t | t 1 = 1 ∧ t 2 = 1})) =
      (StatedOmega (StatedQuadMinus 3 k b c)).map (coordEmbedGL minusEmbA minusEmbA_injective) := by
  obtain ⟨κ, hκ⟩ := SymplecticPilot.exists_units_mul_self_ne_one_of_four_le hk
  rw [perfectCore_inf_centralizer_diagOmegaMinus _ (S := Set.range minusEmbA) _
      (fun t ht a ha b hb => by
        obtain ⟨x, rfl⟩ := ha
        obtain ⟨y, rfl⟩ := hb
        rw [minusWeight_minusEmbA ht.1 ht.2, minusWeight_minusEmbA ht.1 ht.2])
      (fun a b hab hS => ⟨Pi.mulSingle 0 κ, by simp, by
        rcases hS with ha | hb
        · exact minusWeight_mulSingle_ne hκ 0 hab (eq_of_not_mem_range_minusEmbA ha)
        · exact (minusWeight_mulSingle_ne hκ 0 hab.symm (eq_of_not_mem_range_minusEmbA hb)).symm⟩),
    (isCoordSplit_minusEmbA b c).perfectCore_statedOmega_inf_suppGL minusEmbA_injective
      (commutator_statedOmega_quadMinus_three hirr)]

theorem card_perfectCore_omegaMinus8_A (k : Type) [Field k] [Finite k] [CharP k 2] {b c : k}
    (hk : 4 ≤ Nat.card k) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (perfectCore (StatedOmega (StatedQuadMinus 4 k b c) ⊓
      Subgroup.centralizer (diagOmegaMinus k '' {t | t 1 = 1 ∧ t 2 = 1}))) =
      ordSU 4 (Nat.card k) := by
  rw [perfectCore_omegaMinus8_A_eq k hk hirr,
    Subgroup.card_map_of_injective (coordEmbedGL_injective minusEmbA_injective),
    natCard_statedOmega_quadMinus_three hirr]

theorem perfectCore_omegaMinus8_M2_eq (k : Type) [Field k] [Finite k] [CharP k 2] {b c : k}
    (hk : 4 ≤ Nat.card k) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    perfectCore (StatedOmega (StatedQuadMinus 4 k b c) ⊓
      Subgroup.centralizer (diagOmegaMinus k '' {t | t 2 = 1})) =
      (StatedOmega (StatedQuadMinus 2 k b c)).map
        (coordEmbedGL minusEmbTwo minusEmbTwo_injective) := by
  obtain ⟨κ, hκ⟩ := SymplecticPilot.exists_units_mul_self_ne_one_of_four_le hk
  rw [perfectCore_inf_centralizer_diagOmegaMinus _ (S := Set.range minusEmbTwo) _
      (fun t ht a ha b hb => by
        obtain ⟨x, rfl⟩ := ha
        obtain ⟨y, rfl⟩ := hb
        rw [minusWeight_minusEmbTwo ht, minusWeight_minusEmbTwo ht])
      (fun a b hab hS => by
        rcases hS with ha | hb
        · obtain ⟨i, hi, hai⟩ := exists_of_not_mem_range_minusEmbTwo ha
          exact ⟨Pi.mulSingle i κ, by simp [hi.symm],
            minusWeight_mulSingle_ne hκ i hab hai⟩
        · obtain ⟨i, hi, hbi⟩ := exists_of_not_mem_range_minusEmbTwo hb
          exact ⟨Pi.mulSingle i κ, by simp [hi.symm],
            (minusWeight_mulSingle_ne hκ i hab.symm hbi).symm⟩),
    (isCoordSplit_minusEmbTwo b c).perfectCore_statedOmega_inf_suppGL minusEmbTwo_injective
      (commutator_statedOmega_quadMinus_two hirr)]

theorem card_perfectCore_omegaMinus8_M2 (k : Type) [Field k] [Finite k] [CharP k 2] {b c : k}
    (hk : 4 ≤ Nat.card k) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (perfectCore (StatedOmega (StatedQuadMinus 4 k b c) ⊓
      Subgroup.centralizer (diagOmegaMinus k '' {t | t 2 = 1}))) =
      ordSL 2 (Nat.card k ^ 2) := by
  rw [perfectCore_omegaMinus8_M2_eq k hk hirr,
    Subgroup.card_map_of_injective (coordEmbedGL_injective minusEmbTwo_injective),
    natCard_statedOmega_quadMinus_two hirr]

end Pieces

end CFSG.SeitzReduction.F4Pilot
