module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.CatalogInputs
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma137b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1311
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidMinusFacts
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidPlusFacts
public import CFSG.RankThree.Literature.FSmithOrthogonal
public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeAlt
public import CFSG.HardMathSupport.RichardWeiss.Proving.PLType.SpSmall
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield
public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeOrthCent
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GH74.M12.HypGroup
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

namespace OmegaFacts

theorem inputOmegaDvd1311_holds : Lemma1311.InputOmegaDvd1311 := by
  intro p _ ε n X _ _ hn hX hfp
  exact Prop1116.InputOmegaDvd_holds X p ε n hn hX hfp

theorem commutator_eq_top_of_simple_of_center_bot {G : Type*} [Group G] [IsSimpleGroup G]
    (hZ : Subgroup.center G = ⊥) : commutator G = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exfalso
    have hc : ∀ a b : G, a * b = b * a := by
      intro a b
      have : ⁅a, b⁆ ∈ commutator G :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    have hz : (⊤ : Subgroup G) ≤ Subgroup.center G := fun a _ => by
      rw [Subgroup.mem_center_iff]
      intro g
      exact hc g a
    rw [hZ] at hz
    obtain ⟨a, b, hab⟩ := exists_pair_ne G
    exact hab ((Subgroup.mem_bot.1 (hz (Subgroup.mem_top a))).trans
      (Subgroup.mem_bot.1 (hz (Subgroup.mem_top b))).symm)
  · exact h

theorem commutator_eq_top_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : commutator H = ⊤) : commutator G = ⊤ := by
  haveI : Group.IsPerfect H := ⟨h⟩
  haveI : Group.IsPerfect G := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
    e.symm.surjective
  exact Group.IsPerfect.commutator_eq_top

theorem commutator_statedOmega_plus_eq_top {n : ℕ} (hn : 2 ≤ n) :
    commutator ↥(StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))) = ⊤ := by
  haveI : IsSimpleGroup ↥(StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))) :=
    CFSG.ComponentClassification.RankTwoClassical.ORigid.isSimpleGroup_statedOmega_quadPlus_of_three_le
      (K := ZMod 2) (k := n + 1) (by omega)
  exact commutator_eq_top_of_simple_of_center_bot (Prop95Iv.omegaCentreTrivial_holds n hn).1

theorem commutator_statedOmega_minus_eq_top {n : ℕ} (hn : 2 ≤ n) :
    commutator ↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)) = ⊤ := by
  haveI : IsSimpleGroup ↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)) :=
    CFSG.ComponentClassification.RankTwoClassical.ORigid.isSimpleGroup_statedOmega_quadMinus_of_two_le
      (K := ZMod 2) (b := 1) (c := 1) (m := n + 1) (by omega) (by decide)
  exact commutator_eq_top_of_simple_of_center_bot (Prop95Iv.omegaCentreTrivial_holds n hn).2

theorem inputOmegaTwoPerfect_holds : InputOmegaTwoPerfect := by
  intro p hp hp2 ε n hn hfp Y _ _ hY
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    cases ε
    · obtain ⟨e⟩ := hY
      refine commutator_eq_top_of_mulEquiv (e.trans
        CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedOmega_quadMinus_two_mulEquiv_alt5) ?_
      exact commutator_alternatingGroup_eq_top (by simp)
    · exact absurd hfp
        (CFSG.HardMathSupport.Timmesfeld.Proving.not_hasFixedPointFreeOrder_plus_one hp hp2)
  · cases ε
    · obtain ⟨e⟩ := hY
      exact commutator_eq_top_of_mulEquiv e (commutator_statedOmega_minus_eq_top h2)
    · obtain ⟨e⟩ := hY
      exact commutator_eq_top_of_mulEquiv e (commutator_statedOmega_plus_eq_top h2)

section Rank

variable {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def reflMat (Q : (ι → ZMod 2) → ZMod 2) (a : ι → ZMod 2) : Matrix ι ι (ZMod 2) :=
  Matrix.of fun i j => (if i = j then 1 else 0) +
    a i * (Q (Pi.single j 1 + a) + Q (Pi.single j 1) + Q a)

@[expose] def reflGL (Q : (ι → ZMod 2) → ZMod 2) (a : ι → ZMod 2)
    (h : reflMat Q a * reflMat Q a = 1) : GL ι (ZMod 2) :=
  ⟨reflMat Q a, reflMat Q a, h, h⟩

theorem reflGL_inv (Q : (ι → ZMod 2) → ZMod 2) (a : ι → ZMod 2)
    (h : reflMat Q a * reflMat Q a = 1) : (reflGL Q a h)⁻¹ = reflGL Q a h := by
  apply inv_eq_of_mul_eq_one_right
  exact Units.ext h

theorem reflGL_mem_isometryCore (Q : (ι → ZMod 2) → ZMod 2) (a : ι → ZMod 2)
    (h : reflMat Q a * reflMat Q a = 1)
    (hQ : ∀ v : ι → ZMod 2, Q (Matrix.mulVec (reflMat Q a) v) = Q v) :
    reflGL Q a h ∈ CFSG.MatrixModel.isometryCore Q :=
  Subgroup.subset_closure hQ

theorem comm_refl_mem (Q : (ι → ZMod 2) → ZMod 2) (a b : ι → ZMod 2)
    (ha : reflMat Q a * reflMat Q a = 1) (hb : reflMat Q b * reflMat Q b = 1)
    (hQa : ∀ v : ι → ZMod 2, Q (Matrix.mulVec (reflMat Q a) v) = Q v)
    (hQb : ∀ v : ι → ZMod 2, Q (Matrix.mulVec (reflMat Q b) v) = Q v) :
    reflGL Q a ha * reflGL Q b hb * reflGL Q a ha * reflGL Q b hb ∈ StatedOmega Q := by
  have h1 := Subgroup.commutator_mem_commutator (reflGL_mem_isometryCore Q a ha hQa)
    (reflGL_mem_isometryCore Q b hb hQb)
  rw [commutatorElement_def, reflGL_inv, reflGL_inv] at h1
  exact h1

end Rank

@[expose] def Rank2 {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∃ g₁ ∈ H, ∃ g₂ ∈ H, g₁ ^ 3 = 1 ∧ g₂ ^ 3 = 1 ∧ g₁ * g₂ = g₂ * g₁ ∧ g₁ ≠ 1 ∧
    g₂ ∉ Subgroup.zpowers g₁

theorem Rank2.map {G G' : Type*} [Group G] [Group G'] (φ : G →* G') (hφ : Function.Injective φ)
    {H : Subgroup G} {H' : Subgroup G'} (hH : H.map φ ≤ H') (h : Rank2 H) : Rank2 H' := by
  obtain ⟨g₁, hg₁, g₂, hg₂, h1, h2, h12, h1ne, hnot⟩ := h
  refine ⟨φ g₁, hH (Subgroup.mem_map_of_mem φ hg₁), φ g₂, hH (Subgroup.mem_map_of_mem φ hg₂),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, h1, map_one]
  · rw [← map_pow, h2, map_one]
  · rw [← map_mul, ← map_mul, h12]
  · intro h
    exact h1ne (hφ (h.trans (map_one φ).symm))
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    apply hnot
    refine Subgroup.mem_zpowers_iff.2 ⟨k, hφ ?_⟩
    rw [map_zpow, hk]

theorem not_mem_zpowers_of_pow_three {G : Type*} [Group G] {g h : G} (hg : g ^ 3 = 1)
    (h1 : h ≠ 1) (h2 : h ≠ g) (h3 : h ≠ g ^ 2) : h ∉ Subgroup.zpowers g := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  rw [zpow_eq_zpow_emod' k hg] at hk
  have hk3 : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hk3 with h | h | h
  · rw [h, zpow_zero] at hk
    exact h1 hk.symm
  · rw [h, zpow_one] at hk
    exact h2 hk.symm
  · rw [h] at hk
    exact h3 (by rw [← hk]; norm_cast)

theorem gl_val_eq {ι : Type} [Fintype ι] [DecidableEq ι] {g h : GL ι (ZMod 2)} (e : g = h) :
    (g : Matrix ι ι (ZMod 2)) = (h : Matrix ι ι (ZMod 2)) :=
  congrArg Units.val e

abbrev Qplus4 : (Fin 2 ⊕ Fin 2 → ZMod 2) → ZMod 2 := StatedQuadPlus 2 (ZMod 2)

@[expose] def va1 : Fin 2 ⊕ Fin 2 → ZMod 2 := Sum.elim ![1, 0] ![1, 0]
@[expose] def vb1 : Fin 2 ⊕ Fin 2 → ZMod 2 := Sum.elim ![1, 1] ![0, 1]
@[expose] def va2 : Fin 2 ⊕ Fin 2 → ZMod 2 := Sum.elim ![1, 1] ![1, 0]
@[expose] def vb2 : Fin 2 ⊕ Fin 2 → ZMod 2 := Sum.elim ![1, 0] ![1, 1]

theorem refl_va1 : reflMat Qplus4 va1 * reflMat Qplus4 va1 = 1 := by decide +kernel
theorem refl_vb1 : reflMat Qplus4 vb1 * reflMat Qplus4 vb1 = 1 := by decide +kernel
theorem refl_va2 : reflMat Qplus4 va2 * reflMat Qplus4 va2 = 1 := by decide +kernel
theorem refl_vb2 : reflMat Qplus4 vb2 * reflMat Qplus4 vb2 = 1 := by decide +kernel
theorem iso_va1 : ∀ v : Fin 2 ⊕ Fin 2 → ZMod 2, Qplus4 (Matrix.mulVec (reflMat Qplus4 va1) v) = Qplus4 v := by
  decide +kernel
theorem iso_vb1 : ∀ v : Fin 2 ⊕ Fin 2 → ZMod 2, Qplus4 (Matrix.mulVec (reflMat Qplus4 vb1) v) = Qplus4 v := by
  decide +kernel
theorem iso_va2 : ∀ v : Fin 2 ⊕ Fin 2 → ZMod 2, Qplus4 (Matrix.mulVec (reflMat Qplus4 va2) v) = Qplus4 v := by
  decide +kernel
theorem iso_vb2 : ∀ v : Fin 2 ⊕ Fin 2 → ZMod 2, Qplus4 (Matrix.mulVec (reflMat Qplus4 vb2) v) = Qplus4 v := by
  decide +kernel

@[expose] def G41 : GL (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  reflGL Qplus4 va1 refl_va1 * reflGL Qplus4 vb1 refl_vb1 * reflGL Qplus4 va1 refl_va1 * reflGL Qplus4 vb1 refl_vb1
@[expose] def G42 : GL (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  reflGL Qplus4 va2 refl_va2 * reflGL Qplus4 vb2 refl_vb2 * reflGL Qplus4 va2 refl_va2 * reflGL Qplus4 vb2 refl_vb2

theorem G41_val : (G41 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) =
    reflMat Qplus4 va1 * reflMat Qplus4 vb1 * reflMat Qplus4 va1 * reflMat Qplus4 vb1 := rfl
theorem G42_val : (G42 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) =
    reflMat Qplus4 va2 * reflMat Qplus4 vb2 * reflMat Qplus4 va2 * reflMat Qplus4 vb2 := rfl

theorem G41_cube : G41 ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, G41_val]
  decide +kernel

theorem G42_cube : G42 ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, G42_val]
  decide +kernel

theorem G41_ne_one : G41 ≠ 1 := by
  intro h
  have := gl_val_eq h
  rw [G41_val] at this
  revert this
  decide +kernel

theorem G4_comm : G41 * G42 = G42 * G41 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, G41_val, G42_val]
  decide +kernel

theorem G42_not_mem : G42 ∉ Subgroup.zpowers G41 := by
  refine not_mem_zpowers_of_pow_three G41_cube ?_ ?_ ?_
  · intro h
    have := gl_val_eq h
    rw [G42_val] at this
    revert this
    decide +kernel
  · intro h
    have := gl_val_eq h
    rw [G42_val, G41_val] at this
    revert this
    decide +kernel
  · intro h
    have := gl_val_eq h
    rw [G42_val, pow_two, Units.val_mul, G41_val] at this
    revert this
    decide +kernel

theorem rank2_plus_two : Rank2 (StatedOmega Qplus4) :=
  ⟨G41, comm_refl_mem Qplus4 va1 vb1 refl_va1 refl_vb1 iso_va1 iso_vb1, G42,
    comm_refl_mem Qplus4 va2 vb2 refl_va2 refl_vb2 iso_va2 iso_vb2, G41_cube, G42_cube, G4_comm,
    G41_ne_one, G42_not_mem⟩

theorem rank2_plus_succ {n : ℕ} (h : Rank2 (StatedOmega (StatedQuadPlus n (ZMod 2)))) :
    Rank2 (StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))) :=
  Rank2.map (Units.map (CatalogInputs.extMat (CatalogInputs.plus_hyp n)))
    (CatalogInputs.units_map_injective (CatalogInputs.plus_hyp n))
    (CatalogInputs.map_commutator_le (CatalogInputs.plus_hyp n) (CatalogInputs.plus_hQ n)) h

theorem rank2_minus_succ {m : ℕ}
    (h : Rank2 (StatedOmega (StatedQuadMinus (m + 1) (ZMod 2) 1 1))) :
    Rank2 (StatedOmega (StatedQuadMinus (m + 1 + 1) (ZMod 2) 1 1)) :=
  Rank2.map (Units.map (CatalogInputs.extMat (CatalogInputs.minus_hyp m)))
    (CatalogInputs.units_map_injective (CatalogInputs.minus_hyp m))
    (CatalogInputs.map_commutator_le (CatalogInputs.minus_hyp m) (CatalogInputs.minus_hQ m)) h

theorem rank2_plus : ∀ n : ℕ, 1 ≤ n → Rank2 (StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact rank2_plus_two
  | succ n hn ih => exact rank2_plus_succ ih

abbrev Qminus6 : (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2) → ZMod 2 := StatedQuadMinus 3 (ZMod 2) 1 1

@[expose] def wa1 : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2 := Sum.elim ![0, 0] (Sum.elim ![0, 0] ![1, 0])
@[expose] def wb1 : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2 := Sum.elim ![0, 0] (Sum.elim ![0, 0] ![0, 1])
@[expose] def wa2 : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2 := Sum.elim ![1, 1] (Sum.elim ![1, 0] ![0, 0])
@[expose] def wb2 : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2 := Sum.elim ![1, 0] (Sum.elim ![1, 1] ![0, 0])

theorem refl_wa1 : reflMat Qminus6 wa1 * reflMat Qminus6 wa1 = 1 := by decide +kernel
theorem refl_wb1 : reflMat Qminus6 wb1 * reflMat Qminus6 wb1 = 1 := by decide +kernel
theorem refl_wa2 : reflMat Qminus6 wa2 * reflMat Qminus6 wa2 = 1 := by decide +kernel
theorem refl_wb2 : reflMat Qminus6 wb2 * reflMat Qminus6 wb2 = 1 := by decide +kernel
theorem iso_wa1 : ∀ v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2,
    Qminus6 (Matrix.mulVec (reflMat Qminus6 wa1) v) = Qminus6 v := by decide +kernel
theorem iso_wb1 : ∀ v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2,
    Qminus6 (Matrix.mulVec (reflMat Qminus6 wb1) v) = Qminus6 v := by decide +kernel
theorem iso_wa2 : ∀ v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2,
    Qminus6 (Matrix.mulVec (reflMat Qminus6 wa2) v) = Qminus6 v := by decide +kernel
theorem iso_wb2 : ∀ v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2,
    Qminus6 (Matrix.mulVec (reflMat Qminus6 wb2) v) = Qminus6 v := by decide +kernel

@[expose] def G61 : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  reflGL Qminus6 wa1 refl_wa1 * reflGL Qminus6 wb1 refl_wb1 * reflGL Qminus6 wa1 refl_wa1 * reflGL Qminus6 wb1 refl_wb1
@[expose] def G62 : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  reflGL Qminus6 wa2 refl_wa2 * reflGL Qminus6 wb2 refl_wb2 * reflGL Qminus6 wa2 refl_wa2 * reflGL Qminus6 wb2 refl_wb2

theorem G61_val : (G61 : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) =
    reflMat Qminus6 wa1 * reflMat Qminus6 wb1 * reflMat Qminus6 wa1 * reflMat Qminus6 wb1 := rfl
theorem G62_val : (G62 : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) =
    reflMat Qminus6 wa2 * reflMat Qminus6 wb2 * reflMat Qminus6 wa2 * reflMat Qminus6 wb2 := rfl

theorem G61_cube : G61 ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, G61_val]
  decide +kernel

theorem G62_cube : G62 ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, G62_val]
  decide +kernel

theorem G61_ne_one : G61 ≠ 1 := by
  intro h
  have := gl_val_eq h
  rw [G61_val] at this
  revert this
  decide +kernel

theorem G6_comm : G61 * G62 = G62 * G61 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, G61_val, G62_val]
  decide +kernel

theorem G62_not_mem : G62 ∉ Subgroup.zpowers G61 := by
  refine not_mem_zpowers_of_pow_three G61_cube ?_ ?_ ?_
  · intro h
    have := gl_val_eq h
    rw [G62_val] at this
    revert this
    decide +kernel
  · intro h
    have := gl_val_eq h
    rw [G62_val, G61_val] at this
    revert this
    decide +kernel
  · intro h
    have := gl_val_eq h
    rw [G62_val, pow_two, Units.val_mul, G61_val] at this
    revert this
    decide +kernel

theorem rank2_minus_three : Rank2 (StatedOmega Qminus6) :=
  ⟨G61, comm_refl_mem Qminus6 wa1 wb1 refl_wa1 refl_wb1 iso_wa1 iso_wb1, G62,
    comm_refl_mem Qminus6 wa2 wb2 refl_wa2 refl_wb2 iso_wa2 iso_wb2, G61_cube, G62_cube, G6_comm,
    G61_ne_one, G62_not_mem⟩

theorem rank2_minus : ∀ n : ℕ, 2 ≤ n →
    Rank2 (StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact rank2_minus_three
  | succ n hn ih => exact rank2_minus_succ ih

theorem rank2_top_of_subgroup {G : Type*} [Group G] {H : Subgroup G} (h : Rank2 H) :
    Rank2 (⊤ : Subgroup ↥H) := by
  obtain ⟨g₁, hg₁, g₂, hg₂, h1, h2, h12, h1ne, hnot⟩ := h
  refine ⟨⟨g₁, hg₁⟩, Subgroup.mem_top _, ⟨g₂, hg₂⟩, Subgroup.mem_top _, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subtype.ext h1
  · exact Subtype.ext h2
  · exact Subtype.ext h12
  · intro h'
    exact h1ne (congrArg Subtype.val h')
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    apply hnot
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this

theorem exists_elemAbelian_three_pow_of_rank2 {X : Type} [Group X] [Finite X]
    (h : Rank2 (⊤ : Subgroup X)) :
    ∃ (E : Subgroup X) (k : ℕ), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k ∧ 2 ≤ k := by
  obtain ⟨g₁, -, g₂, -, h1, h2, h12, h1ne, hnot⟩ := h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : (3 : ℕ).Prime := Nat.prime_three
  set A : Subgroup X := Subgroup.zpowers g₁ with hA
  set B : Subgroup X := Subgroup.zpowers g₂ with hB
  have hpowA : ∀ a ∈ A, a ^ 3 = 1 := by
    intro a ha
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h1, one_zpow]
  have hpowB : ∀ b ∈ B, b ^ 3 = 1 := by
    intro b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h2, one_zpow]
  have hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow (show Commute g₁ g₂ from h12) i j).eq
  have hAA : ∀ a ∈ A, ∀ c ∈ A, a * c = c * a := by
    intro a ha c hc
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    exact (Commute.zpow_zpow_self g₁ i j).eq
  have hBB : ∀ b ∈ B, ∀ d ∈ B, b * d = d * b := by
    intro b hb d hd
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
    exact (Commute.zpow_zpow_self g₂ i j).eq
  set E : Subgroup X := A ⊔ B with hE
  have hprod : ∀ x ∈ E, ∃ a ∈ A, ∃ b ∈ B, x = a * b := Lemma137.mem_sup_of_comm hAB
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hprod x hx
    obtain ⟨c, hc, d, hd, rfl⟩ := hprod y hy
    calc a * b * (c * d) = a * (b * c) * d := by group
      _ = a * (c * b) * d := by rw [(hAB c hc b hb).symm]
      _ = (a * c) * (b * d) := by group
      _ = (c * a) * (d * b) := by rw [hAA a ha c hc, hBB b hb d hd]
      _ = c * (a * d) * b := by group
      _ = c * (d * a) * b := by rw [hAB a ha d hd]
      _ = c * d * (a * b) := by group
  have hEpow : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hprod x hx
    rw [(show Commute a b from hAB a ha b hb).mul_pow, hpowA a ha, hpowB b hb, one_mul]
  have hEel : IsElemAbelian 3 E :=
    ⟨⟨⟨fun a b => Subtype.ext (hEcomm a a.2 b b.2)⟩⟩, hEpow⟩
  have hEp : IsPGroup 3 E := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hEpow x x.2⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hord : orderOf g₁ = 3 := orderOf_eq_prime h1 h1ne
  have hAcard : Nat.card A = 3 := by rw [hA, Nat.card_zpowers, hord]
  have hAE : A ≤ E := le_sup_left
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hk1 : k ≤ 1 := by omega
    have hle : Nat.card E ≤ Nat.card A := by
      rw [hk, hAcard]
      calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
        _ = 3 := pow_one 3
    have heq : A = E := Subgroup.eq_of_le_of_card_ge hAE hle
    apply hnot
    have : g₂ ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers g₂)
    rwa [← heq] at this
  exact ⟨E, k, hEel, hk, hk2⟩

theorem two_le_pRank_three_of_rank2 {X : Type} [Group X] [Finite X] (h : Rank2 (⊤ : Subgroup X)) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨E, k, hEel, hk, hk2⟩ := exists_elemAbelian_three_pow_of_rank2 h
  exact hk2.trans (CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_top hEel hk)

theorem nine_dvd_card_of_rank2 {X : Type} [Group X] [Finite X] (h : Rank2 (⊤ : Subgroup X)) :
    9 ∣ Nat.card X := by
  obtain ⟨E, k, -, hk, hk2⟩ := exists_elemAbelian_three_pow_of_rank2 h
  have h1 : 3 ^ 2 ∣ Nat.card E := hk ▸ pow_dvd_pow 3 hk2
  exact h1.trans (Subgroup.card_subgroup_dvd_card E)

theorem two_le_pRank_three_of_isOmegaTwo {ε : Bool} {n : ℕ} (hn : 2 ≤ n) {X : Type} [Group X]
    [Finite X] (hX : IsOmegaTwo ε (n + 1) X) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  cases ε
  · obtain ⟨e⟩ := hX
    exact two_le_pRank_three_of_rank2 (Rank2.map e.symm.toMonoidHom e.symm.injective
      (fun _ _ => Subgroup.mem_top _) (rank2_top_of_subgroup (rank2_minus n hn)))
  · obtain ⟨e⟩ := hX
    exact two_le_pRank_three_of_rank2 (Rank2.map e.symm.toMonoidHom e.symm.injective
      (fun _ _ => Subgroup.mem_top _) (rank2_top_of_subgroup (rank2_plus n (by omega))))

theorem inputRankOneOmega3_holds : Prop139.InputRankOneOmega3 := by
  intro ε n X _ _ hn hX hfp hrk
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    exact (Lemma137b.omegaFour Nat.prime_three (by norm_num) hfp hX).2
  · exfalso
    have := two_le_pRank_three_of_isOmegaTwo h2 hX
    omega

open CFSG.HardMathSupport.Curtis.Coordinator.PLType (fourProd)

@[expose] def omegaOrd (ε : Bool) (m : ℕ) : ℕ :=
  2 ^ (m * (m - 1)) * (if ε then 2 ^ m - 1 else 2 ^ m + 1) * fourProd (m - 1)

theorem card_comap_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (S : Subgroup H) :
    Nat.card (S.comap e.toMonoidHom) = Nat.card S := by
  have key : S.comap e.toMonoidHom = S.map e.symm.toMonoidHom :=
    Subgroup.comap_equiv_eq_map_symm e S
  rw [key, Subgroup.card_map_of_injective e.symm.injective]

theorem prod_int_eq_fourProd (k : ℕ) :
    (∏ i ∈ Finset.Icc 1 k, ((2 : ℤ) ^ (2 * i) - 1)) = (fourProd k : ℤ) := by
  unfold fourProd
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num)), pow_mul]
  norm_num

theorem card_eq_two_mul_of_relIndex {G : Type*} [Group G] {Ω O : Subgroup G} (hΩO : Ω ≤ O)
    (h : Ω.relIndex O = 2) : Nat.card O = 2 * Nat.card Ω := by
  have hcard := (Ω.subgroupOf O).card_mul_index
  rw [Subgroup.relIndex] at h
  rw [h, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΩO).toEquiv] at hcard
  omega

theorem card_statedOmega_quadMinus_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    Nat.card ↥(StatedOmega (StatedQuadMinus (k + 1) (ZMod 2) 1 1)) = omegaOrd false (k + 1) := by
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  have hQ := CFSG.LieType.Universal.Spin.coe_quadMinus (k + 1) (ZMod 2) 1 1
  have hnd : (QuadraticMap.polarBilin (CFSG.LieType.Universal.Spin.quadMinus (k + 1) (ZMod 2) 1
      1)).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (k + 1) (ZMod 2) hirr
  have h6 : 6 ≤ Module.finrank (ZMod 2) (Fin (k + 1 - 1) ⊕ Fin (k + 1 - 1) ⊕ Fin 2 → ZMod 2) := by
    simp [Module.finrank_fintype_fun_eq_card]
    omega
  haveI : Nonempty (Fin (k + 1 - 1) ⊕ Fin (k + 1 - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hQ, card_comap_mulEquiv,
    CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup hnd h6]
  have hidx := CFSG.RankThree.OrthogonalInvolutions.relIndex_omegaGroup
    (CFSG.LieType.Universal.Spin.quadMinus (k + 1) (ZMod 2) 1 1) hnd
  have hO := (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus k hirr).2
  have hOz : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadMinus (k + 1) (ZMod 2) 1 1)) : ℤ) =
        2 * ((2 ^ (k * (k + 1)) * (2 ^ (k + 1) + 1) * fourProd k : ℕ) : ℤ) := by
    rw [hO, Nat.card_zmod]
    simp only [Nat.cast_ofNat]
    rw [prod_int_eq_fourProd]
    push_cast
    ring
  have hOn : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadMinus (k + 1) (ZMod 2) 1 1)) =
        2 * (2 ^ (k * (k + 1)) * (2 ^ (k + 1) + 1) * fourProd k) := by exact_mod_cast hOz
  have hc := card_eq_two_mul_of_relIndex
    (CFSG.RankThree.OrthogonalInvolutions.omegaGroup_le
      (CFSG.LieType.Universal.Spin.quadMinus (k + 1) (ZMod 2) 1 1) hnd) hidx
  rw [hOn] at hc
  unfold omegaOrd
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel]
  rw [show (k + 1) * k = k * (k + 1) by ring]
  omega

theorem card_statedOmega_quadPlus_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    Nat.card ↥(StatedOmega (StatedQuadPlus (k + 1) (ZMod 2))) = omegaOrd true (k + 1) := by
  have hQ := CFSG.LieType.Universal.Spin.coe_quadPlus (k + 1) (ZMod 2)
  have hnd : (QuadraticMap.polarBilin (CFSG.LieType.Universal.Spin.quadPlus (k + 1)
      (ZMod 2))).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus (k + 1) (ZMod 2)
  have h6 : 6 ≤ Module.finrank (ZMod 2) (Fin (k + 1) ⊕ Fin (k + 1) → ZMod 2) := by
    simp [Module.finrank_fintype_fun_eq_card]
    omega
  haveI : Nonempty (Fin (k + 1) ⊕ Fin (k + 1)) := ⟨Sum.inl 0⟩
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hQ, card_comap_mulEquiv,
    CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup hnd h6]
  have hidx := CFSG.RankThree.OrthogonalInvolutions.relIndex_omegaGroup
    (CFSG.LieType.Universal.Spin.quadPlus (k + 1) (ZMod 2)) hnd
  have hO := (CFSG.Timmesfeld.ClassicalOrders.card_quadPlus (K := ZMod 2) k).2
  have hpos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have hOz : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadPlus (k + 1) (ZMod 2))) : ℤ) =
        2 * ((2 ^ (k * (k + 1)) * (2 ^ (k + 1) - 1) * fourProd k : ℕ) : ℤ) := by
    rw [hO, Nat.card_zmod]
    simp only [Nat.cast_ofNat]
    rw [prod_int_eq_fourProd]
    push_cast [Nat.cast_sub hpos]
    ring
  have hOn : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadPlus (k + 1) (ZMod 2))) =
        2 * (2 ^ (k * (k + 1)) * (2 ^ (k + 1) - 1) * fourProd k) := by exact_mod_cast hOz
  have hc := card_eq_two_mul_of_relIndex
    (CFSG.RankThree.OrthogonalInvolutions.omegaGroup_le
      (CFSG.LieType.Universal.Spin.quadPlus (k + 1) (ZMod 2)) hnd) hidx
  rw [hOn] at hc
  unfold omegaOrd
  simp only [↓reduceIte, Nat.add_sub_cancel]
  rw [show (k + 1) * k = k * (k + 1) by ring]
  omega

abbrev Q2p : (Fin 1 ⊕ Fin 1 → ZMod 2) → ZMod 2 := StatedQuadPlus 1 (ZMod 2)

theorem iso2p : ∀ M : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) (ZMod 2),
    (∀ v : Fin 1 ⊕ Fin 1 → ZMod 2, Q2p (Matrix.mulVec M v) = Q2p v) →
      M = 1 ∨ M = Matrix.fromBlocks 0 1 1 0 := by
  decide +kernel

@[expose] def swapGL : GL (Fin 1 ⊕ Fin 1) (ZMod 2) :=
  ⟨Matrix.fromBlocks 0 1 1 0, Matrix.fromBlocks 0 1 1 0, by decide, by decide⟩

theorem statedOmega_plus_one : StatedOmega (StatedQuadPlus 1 (ZMod 2)) = ⊥ := by
  have hS : CFSG.MatrixModel.isometryCore Q2p ≤ Subgroup.zpowers swapGL := by
    refine (Subgroup.closure_le _).2 ?_
    intro A hA
    rcases iso2p A.val hA with h | h
    · have : A = 1 := Units.ext h
      rw [SetLike.mem_coe, this]
      exact Subgroup.one_mem _
    · have : A = swapGL := Units.ext h
      rw [SetLike.mem_coe, this]
      exact Subgroup.mem_zpowers _
  show ⁅CFSG.MatrixModel.isometryCore Q2p, CFSG.MatrixModel.isometryCore Q2p⁆ = ⊥
  refine eq_bot_iff.2 ((Subgroup.commutator_mono hS hS).trans ?_)
  rw [Subgroup.commutator_le]
  intro g hg h hh
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact (Commute.zpow_zpow_self swapGL i j).eq

theorem card_statedOmega_plus_one : Nat.card ↥(StatedOmega (StatedQuadPlus 1 (ZMod 2))) = 1 := by
  rw [statedOmega_plus_one]
  exact Subgroup.card_bot

abbrev Q2m : (Fin (1 - 1) ⊕ Fin (1 - 1) ⊕ Fin 2 → ZMod 2) → ZMod 2 := StatedQuadMinus 1 (ZMod 2) 1 1

@[expose] def ua : Fin (1 - 1) ⊕ Fin (1 - 1) ⊕ Fin 2 → ZMod 2 :=
  Sum.elim ![] (Sum.elim ![] ![1, 0])
@[expose] def ub : Fin (1 - 1) ⊕ Fin (1 - 1) ⊕ Fin 2 → ZMod 2 :=
  Sum.elim ![] (Sum.elim ![] ![0, 1])

theorem refl_ua : reflMat Q2m ua * reflMat Q2m ua = 1 := by decide +kernel
theorem refl_ub : reflMat Q2m ub * reflMat Q2m ub = 1 := by decide +kernel
theorem iso_ua : ∀ v : Fin (1 - 1) ⊕ Fin (1 - 1) ⊕ Fin 2 → ZMod 2,
    Q2m (Matrix.mulVec (reflMat Q2m ua) v) = Q2m v := by decide +kernel
theorem iso_ub : ∀ v : Fin (1 - 1) ⊕ Fin (1 - 1) ⊕ Fin 2 → ZMod 2,
    Q2m (Matrix.mulVec (reflMat Q2m ub) v) = Q2m v := by decide +kernel

theorem Gm_ne_one : reflGL Q2m ua refl_ua * reflGL Q2m ub refl_ub * reflGL Q2m ua refl_ua *
    reflGL Q2m ub refl_ub ≠ 1 := by
  intro h
  have := gl_val_eq h
  revert this
  decide +kernel

theorem statedOmega_minus_one_ne_bot : StatedOmega (StatedQuadMinus 1 (ZMod 2) 1 1) ≠ ⊥ := by
  intro h
  have hmem := comm_refl_mem Q2m ua ub refl_ua refl_ub iso_ua iso_ub
  rw [h, Subgroup.mem_bot] at hmem
  exact Gm_ne_one hmem

theorem one_lt_card_statedOmega_minus_one :
    1 < Nat.card ↥(StatedOmega (StatedQuadMinus 1 (ZMod 2) 1 1)) := by
  have : Nontrivial ↥(StatedOmega (StatedQuadMinus 1 (ZMod 2) 1 1)) :=
    (Subgroup.nontrivial_iff_ne_bot _).2 statedOmega_minus_one_ne_bot
  exact Finite.one_lt_card

theorem card_statedOmega_minus_one_le :
    Nat.card ↥(StatedOmega (StatedQuadMinus 1 (ZMod 2) 1 1)) ≤ 6 := by
  have h1 := Subgroup.card_le_card_group (StatedOmega (StatedQuadMinus 1 (ZMod 2) 1 1))
  have h2 : Nat.card (GL (Fin (1 - 1) ⊕ Fin (1 - 1) ⊕ Fin 2) (ZMod 2)) = 6 := by
    rw [CatalogInputs.card_GL_zmod_two_eq _ 2 (by simp)]
    decide
  omega

theorem omegaOrd_pos {ε : Bool} {m : ℕ} (hm : 1 ≤ m) : 0 < omegaOrd ε m := by
  unfold omegaOrd
  refine Nat.mul_pos (Nat.mul_pos (by positivity) ?_)
    (CFSG.HardMathSupport.Curtis.Coordinator.PLType.fourProd_pos _)
  cases ε
  · simp
  · have : 1 < 2 ^ m := Nat.one_lt_two_pow (by omega)
    simp only [↓reduceIte]
    omega

theorem sixtyFour_dvd_omegaOrd {ε : Bool} {m : ℕ} (hm : 3 ≤ m) : 64 ∣ omegaOrd ε m := by
  unfold omegaOrd
  refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
  have h6 : 6 ≤ m * (m - 1) := by
    have := Nat.mul_le_mul hm (show 2 ≤ m - 1 by omega)
    omega
  exact (show (64 : ℕ) = 2 ^ 6 by norm_num) ▸ pow_dvd_pow 2 h6

theorem not_isSolvable_of_perfect {X : Type*} [Group X] [Nontrivial X] (h : commutator X = ⊤) :
    ¬ Group.IsSolvable X := by
  haveI : Group.IsPerfect X := ⟨h⟩
  exact Group.IsPerfect.not_isSolvable X

theorem card_alternatingGroup_five : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
  have h := CFSG.HardMathSupport.Curtis.Coordinator.PLType.two_mul_card_alt_fin 5 le_rfl
  have h5 : Nat.factorial 5 = 120 := by decide
  omega

theorem omega_data {ε : Bool} {n : ℕ} {X : Type} [Group X] [Finite X]
    (hX : IsOmegaTwo ε (n + 1) X) :
    (n = 0 ∧ ε = true ∧ Nat.card X = 1) ∨
    (n = 0 ∧ ε = false ∧ 1 < Nat.card X ∧ Nat.card X ≤ 6) ∨
    (n = 1 ∧ ε = true ∧ Group.IsSolvable X ∧ 9 ∣ Nat.card X) ∨
    (n = 1 ∧ ε = false ∧ Nat.card X = 60 ∧ ¬ Group.IsSolvable X) ∨
    (2 ≤ n ∧ Nat.card X = omegaOrd ε (n + 1) ∧ 64 ∣ Nat.card X ∧ ¬ Group.IsSolvable X) := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
    · cases ε
      · obtain ⟨e⟩ := hX
        refine Or.inr (Or.inl ⟨rfl, rfl, ?_, ?_⟩)
        · rw [Nat.card_congr e.toEquiv]
          exact one_lt_card_statedOmega_minus_one
        · rw [Nat.card_congr e.toEquiv]
          exact card_statedOmega_minus_one_le
      · obtain ⟨e⟩ := hX
        refine Or.inl ⟨rfl, rfl, ?_⟩
        rw [Nat.card_congr e.toEquiv]
        exact card_statedOmega_plus_one
    · cases ε
      · obtain ⟨e⟩ := hX
        let e' := e.trans
          CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedOmega_quadMinus_two_mulEquiv_alt5
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, ?_, ?_⟩)))
        · rw [Nat.card_congr e'.toEquiv]
          exact card_alternatingGroup_five
        · haveI : Nontrivial ↥(alternatingGroup (Fin 5)) := by
            rw [← Finite.one_lt_card_iff_nontrivial, card_alternatingGroup_five]
            norm_num
          have hperf : commutator ↥(alternatingGroup (Fin 5)) = ⊤ :=
            commutator_alternatingGroup_eq_top (by simp)
          intro hs
          haveI : Group.IsSolvable ↥(alternatingGroup (Fin 5)) :=
            Group.isSolvable_of_isSolvable_injective (f := e'.symm.toMonoidHom) e'.symm.injective
          exact not_isSolvable_of_perfect hperf this
      · obtain ⟨e⟩ := hX
        refine Or.inr (Or.inr (Or.inl ⟨rfl, rfl, ?_, ?_⟩))
        · haveI : Group.IsSolvable ↥(StatedOmega (StatedQuadPlus 2 (ZMod 2))) :=
            Prop95I1920.isSolvable_statedOmega_plus_two
          exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
        · exact nine_dvd_card_of_rank2 (Rank2.map e.symm.toMonoidHom e.symm.injective
            (fun _ _ => Subgroup.mem_top _) (rank2_top_of_subgroup rank2_plus_two))
  · have hcardeq : Nat.card X = omegaOrd ε (n + 1) := by
      cases ε
      · obtain ⟨e⟩ := hX
        rw [Nat.card_congr e.toEquiv]
        exact card_statedOmega_quadMinus_of_two_le h2
      · obtain ⟨e⟩ := hX
        rw [Nat.card_congr e.toEquiv]
        exact card_statedOmega_quadPlus_of_two_le h2
    have h64 : 64 ∣ omegaOrd ε (n + 1) := sixtyFour_dvd_omegaOrd (by omega)
    have hpos : 0 < omegaOrd ε (n + 1) := omegaOrd_pos (by omega)
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨h2, hcardeq, hcardeq ▸ h64, ?_⟩)))
    have hcard : 1 < Nat.card X := by
      have := Nat.le_of_dvd hpos h64
      omega
    haveI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.1 hcard
    have hperf : commutator X = ⊤ := by
      cases ε
      · obtain ⟨e⟩ := hX
        exact commutator_eq_top_of_mulEquiv e (commutator_statedOmega_minus_eq_top h2)
      · obtain ⟨e⟩ := hX
        exact commutator_eq_top_of_mulEquiv e (commutator_statedOmega_plus_eq_top h2)
    exact not_isSolvable_of_perfect hperf

theorem odd_omegaOrd_cofactor {ε : Bool} {m : ℕ} (hm : 1 ≤ m) :
    Odd ((if ε then 2 ^ m - 1 else 2 ^ m + 1) *
      CFSG.HardMathSupport.Curtis.Coordinator.PLType.fourProd (m - 1)) := by
  refine Odd.mul ?_ (CFSG.HardMathSupport.Curtis.Coordinator.PLType.fourProd_odd _)
  have h1 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨k, hk⟩ : Even (2 ^ m) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  cases ε
  · exact ⟨k, by simp only [Bool.false_eq_true, ↓reduceIte]; omega⟩
  · exact ⟨k - 1, by simp only [↓reduceIte]; omega⟩

theorem padicValNat_two_omegaOrd {ε : Bool} {m : ℕ} (hm : 1 ≤ m) :
    padicValNat 2 (omegaOrd ε m) = m * (m - 1) := by
  have hodd := odd_omegaOrd_cofactor (ε := ε) hm
  have hpos : (if ε then 2 ^ m - 1 else 2 ^ m + 1) *
      CFSG.HardMathSupport.Curtis.Coordinator.PLType.fourProd (m - 1) ≠ 0 := hodd.pos.ne'
  have : omegaOrd ε m = 2 ^ (m * (m - 1)) *
      ((if ε then 2 ^ m - 1 else 2 ^ m + 1) *
        CFSG.HardMathSupport.Curtis.Coordinator.PLType.fourProd (m - 1)) := by
    unfold omegaOrd
    ring
  rw [this, padicValNat.mul (by positivity) hpos, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hodd.not_two_dvd_nat, add_zero]

theorem omegaOrd_inj {ε ε' : Bool} {m m' : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (h : omegaOrd ε m = omegaOrd ε' m') : ε = ε' ∧ m = m' := by
  have hv := congrArg (padicValNat 2) h
  rw [padicValNat_two_omegaOrd hm, padicValNat_two_omegaOrd hm'] at hv
  have hmm : m = m' := by
    obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, m' = b + 1 := ⟨m' - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hv
    have hab : a = b := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · nlinarith
      · nlinarith
    rw [hab]
  subst hmm
  refine ⟨?_, rfl⟩
  have hP := CFSG.HardMathSupport.Curtis.Coordinator.PLType.fourProd_pos (m - 1)
  unfold omegaOrd at h
  have h2 : 0 < 2 ^ (m * (m - 1)) := by positivity
  have h3 := Nat.eq_of_mul_eq_mul_right hP h
  have h4 := Nat.eq_of_mul_eq_mul_left h2 h3
  have h5 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  cases ε <;> cases ε' <;> simp only [Bool.false_eq_true, ↓reduceIte] at h4 ⊢ <;> omega

theorem input3_3OmegaUnique_holds : Lemma137b.Input3_3OmegaUnique := by
  intro ε ε' n n' X _ _ hX hX'
  rcases omega_data hX with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ |
      ⟨h1, h2, h3, h4⟩ | ⟨h1, h3, h5, h4⟩ <;>
  rcases omega_data hX' with ⟨g1, g2, g3⟩ | ⟨g1, g2, g3, g4⟩ | ⟨g1, g2, g3, g4⟩ |
      ⟨g1, g2, g3, g4⟩ | ⟨g1, g3, g5, g4⟩
  all_goals first
    | (exfalso; first | omega | exact absurd ‹Group.IsSolvable X› ‹¬ Group.IsSolvable X›)
    | (exact ⟨by simp_all, by omega⟩)
    | skip
  obtain ⟨hε, hm⟩ := omegaOrd_inj (ε := ε) (ε' := ε') (m := n + 1) (m' := n' + 1) (by omega)
    (by omega) (h3.symm.trans g3)
  exact ⟨hε, by omega⟩

theorem nonempty_statedSp_two_mulEquiv_perm_six :
    Nonempty (↥(StatedSp 2 (ZMod 2)) ≃* Equiv.Perm (Fin 6)) :=
  CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm (k := ZMod 2)
    (by simp)

theorem nonempty_mulEquiv_of_subsingleton {A B : Type*} [Group A] [Group B] [Subsingleton A]
    [Subsingleton B] : Nonempty (A ≃* B) :=
  ⟨{ toFun := fun _ => 1
     invFun := fun _ => 1
     left_inv := fun _ => Subsingleton.elim _ _
     right_inv := fun _ => Subsingleton.elim _ _
     map_mul' := fun _ _ => Subsingleton.elim _ _ }⟩

theorem subsingleton_statedSp_zero : Subsingleton ↥(StatedSp 0 (ZMod 2)) := by
  refine ⟨fun a b => Subtype.ext (Units.ext ?_)⟩
  exact Subsingleton.elim _ _

theorem omegaOrd_three_plus : omegaOrd true 3 = 20160 := by decide +kernel

theorem omegaOrd_three_minus : omegaOrd false 3 = 25920 := by decide +kernel

theorem input3_3OmegaAlt_holds : Lemma137b.Input3_3OmegaAlt := by
  intro p k hp hp2 ε n X _ _ hAlt hΩ
  obtain ⟨eA⟩ := hAlt
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    have hX1 : Nat.card X = 1 := by
      have h2 : Nat.card ↥(alternatingGroup (Fin (0 * p + 2))) = 1 := by
        rw [zero_mul, zero_add]
        rw [Nat.card_eq_one_iff_unique]
        refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨1⟩⟩
        have key : ∀ σ : Equiv.Perm (Fin 2), Equiv.Perm.sign σ = 1 → σ = 1 := by decide
        exact (key _ (Equiv.Perm.mem_alternatingGroup.1 a.2)).trans
          (key _ (Equiv.Perm.mem_alternatingGroup.1 b.2)).symm
      rw [Nat.card_congr eA.toEquiv, h2]
    rcases omega_data hΩ with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ |
        ⟨h1, h2, h3, h4⟩ | ⟨h1, h3, h5, h4⟩
    · subst h1
      haveI := subsingleton_statedSp_zero
      haveI : Subsingleton (Equiv.Perm (Fin (0 * p))) := by
        rw [zero_mul]
        infer_instance
      exact nonempty_mulEquiv_of_subsingleton
    all_goals exfalso; omega
  · have hN5 : 5 ≤ k * p + 2 := by nlinarith
    have hfac : 2 * Nat.card X = Nat.factorial (k * p + 2) := by
      rw [Nat.card_congr eA.toEquiv]
      exact CFSG.HardMathSupport.Curtis.Coordinator.PLType.two_mul_card_alt_fin _ hN5
    have h120 : 120 ≤ Nat.factorial (k * p + 2) := by
      have := Nat.factorial_le hN5
      have h5 : Nat.factorial 5 = 120 := by decide
      omega
    have hns : ¬ Group.IsSolvable X := by
      haveI : Nontrivial ↥(alternatingGroup (Fin (k * p + 2))) := by
        rw [← Finite.one_lt_card_iff_nontrivial,
          ← CFSG.HardMathSupport.Curtis.Coordinator.PLType.two_mul_card_alt_fin _ hN5] at *
        omega
      have hperf : commutator ↥(alternatingGroup (Fin (k * p + 2))) = ⊤ :=
        commutator_alternatingGroup_eq_top (by simpa using hN5)
      intro hs
      haveI : Group.IsSolvable ↥(alternatingGroup (Fin (k * p + 2))) :=
        Group.isSolvable_of_isSolvable_injective (f := eA.symm.toMonoidHom) eA.symm.injective
      exact not_isSolvable_of_perfect hperf this
    rcases omega_data hΩ with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ |
        ⟨h1, h2, h3, h4⟩ | ⟨h1, h3, h5, h4⟩
    · exfalso; omega
    · exfalso; omega
    · exact absurd h3 hns
    ·
      subst h1
      have hfac5 : Nat.factorial (k * p + 2) = Nat.factorial 5 := by
        have h5 : Nat.factorial 5 = 120 := by decide
        omega
      have hkp : k * p + 2 = 5 :=
        (Nat.factorial_inj (by omega : 1 < k * p + 2)).1 hfac5
      have hkp' : k * p = 3 := by omega
      rw [hkp']
      exact CFSG.HardMathSupport.RichardWeiss.Proving.PLType.nonempty_statedSp_one_mulEquiv_perm_three
    ·
      by_cases hn2 : n = 2
      · subst hn2
        cases ε
        · exfalso
          rw [omegaOrd_three_minus] at h3
          have := CFSG.HardMathSupport.Curtis.Coordinator.PLType.factorial_ne_51840 hN5
          omega
        · have hord : Nat.card X = 20160 := by rw [h3]; exact omegaOrd_three_plus
          have hfac8 : Nat.factorial (k * p + 2) = Nat.factorial 8 := by
            have h8 : Nat.factorial 8 = 40320 := by decide
            omega
          have hkp : k * p + 2 = 8 :=
            (Nat.factorial_inj (by omega : 1 < k * p + 2)).1 hfac8
          have hkp' : k * p = 6 := by omega
          rw [hkp']
          exact nonempty_statedSp_two_mulEquiv_perm_six
      · exfalso
        have hm4 : 4 ≤ n + 1 := by omega
        refine CFSG.HardMathSupport.Curtis.Coordinator.PLType.factorial_ne_two_mul_orth hm4 hN5
          (A := if ε then 2 ^ (n + 1) - 1 else 2 ^ (n + 1) + 1) (by cases ε <;> simp) ?_
        rw [← hfac, h3]
        unfold omegaOrd
        simp only [Nat.add_sub_cancel]

@[expose] noncomputable def projEquivZMod2 {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Subgroup (GL ι (ZMod 2))) : StatedProj H ≃* H :=
  (QuotientGroup.quotientMulEquivOfEq (by
    rw [CFSG.Open.StatedAPI.statedScalars_zmod_two_eq_bot ι, Subgroup.bot_subgroupOf])).trans
    QuotientGroup.quotientBot

theorem isSimpleGroup_statedSp_zmod_two {n : ℕ} (hn : 3 ≤ n) :
    IsSimpleGroup ↥(StatedSp n (ZMod 2)) := by
  have : IsSimpleGroup (StatedProj (StatedSp n (ZMod 2))) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (ZMod 2) n (by omega)
      (Or.inr (Or.inr ⟨Nat.card_zmod 2, hn⟩))
  exact (projEquivZMod2 (StatedSp n (ZMod 2))).symm.isSimpleGroup

theorem card_statedSp_zmod_two (n : ℕ) :
    Nat.card ↥(StatedSp n (ZMod 2)) = 2 ^ (n ^ 2) * ∏ j ∈ Finset.Icc 1 n, (2 ^ (2 * j) - 1) := by
  have := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := ZMod 2) n
  rwa [Nat.card_zmod] at this

theorem typeSign_dvd_card_statedSp {n : ℕ} (hn : 1 ≤ n) (ε : Bool) :
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.typeSign ε n ∣
      Nat.card ↥(StatedSp n (ZMod 2)) := by
  have h1 := card_statedSp_zmod_two n
  have h2 : 2 ^ (2 * n) - 1 ∣ ∏ j ∈ Finset.Icc 1 n, (2 ^ (2 * j) - 1) :=
    Finset.dvd_prod_of_mem (fun j => 2 ^ (2 * j) - 1) (Finset.mem_Icc.2 ⟨hn, le_rfl⟩)
  have h3 : CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.typeSign ε n ∣ 2 ^ (2 * n) - 1 := by
    have hsq : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      have := Nat.sq_sub_sq (2 ^ n) 1
      rw [one_pow] at this
      rw [pow_mul' 2 2 n]
      exact this
    unfold CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.typeSign
    rw [hsq]
    cases ε
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact dvd_mul_right _ _
    · simp only [↓reduceIte]
      exact dvd_mul_left _ _
  rw [h1]
  exact (h3.trans h2).trans (dvd_mul_left _ _)

theorem pPrimeCore_eq_bot_of_simple {p : ℕ} (hp : p.Prime) {C : Type} [Group C] [Finite C]
    [IsSimpleGroup C] (hpC : p ∣ Nat.card C) : GLAPPrimeCore p C = ⊥ := by
  show CFSG.pPrimeCore p C = ⊥
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro R hR hcop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R with h | h
  · exact h
  · exfalso
    rw [h, Subgroup.card_top] at hcop
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop hpC

theorem input3_3SpFacts_holds : Lemma137b.Input3_3SpFacts := by
  intro p hp hp2 ε n hn hfp C _ _ hC
  obtain ⟨e⟩ := hC
  have hdvdSign :=
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.dvd_typeSign_of_hasFixedPointFreeOrder hp
      hp2 (by omega) hfp
  have hpC : p ∣ Nat.card C := by
    rw [Nat.card_congr e.toEquiv]
    exact hdvdSign.trans (typeSign_dvd_card_statedSp (by omega) ε)
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · obtain rfl : n = 2 := by omega
    obtain ⟨f⟩ := nonempty_statedSp_two_mulEquiv_perm_six
    let g : C ≃* Equiv.Perm (Fin 6) := e.trans f
    have hp6 : p ≤ 6 := by
      have hle := Nat.le_of_dvd (by
        cases ε <;>
        simp [CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.typeSign]) hdvdSign
      have hle5 : CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.typeSign ε 2 ≤ 5 := by
        cases ε <;> simp [CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.typeSign]
      omega
    refine ⟨Lemma137b.pPrimeCore_eq_bot_of_equiv g
      (Lemma137b.pPrimeCore_perm_eq_bot (by norm_num) hp hp2 hp6), ?_⟩
    have hgd := Lemma137b.GoodDer.of_mulEquiv g.symm
      (Lemma137b.goodDer_perm (n := 6) (by norm_num))
    exact ⟨hgd.simple, hgd.nonab⟩
  · haveI : IsSimpleGroup ↥(StatedSp n (ZMod 2)) := isSimpleGroup_statedSp_zmod_two h3
    haveI : IsSimpleGroup C := e.isSimpleGroup
    have h4 : 4 ∣ Nat.card C := by
      rw [Nat.card_congr e.toEquiv, card_statedSp_zmod_two]
      refine Dvd.dvd.mul_right ?_ _
      exact (show (4 : ℕ) = 2 ^ 2 by norm_num) ▸ pow_dvd_pow 2 (by nlinarith)
    have hnp : ¬ (Nat.card C).Prime := fun hprime =>
      absurd ((Nat.dvd_prime hprime).1 h4) (by
        rintro (h | h)
        · omega
        · rw [← h] at hprime
          exact absurd hprime (by norm_num))
    have hZ : Subgroup.center C = ⊥ := CatalogInputs.center_eq_bot_of_simple_not_prime hnp
    have hgd := Lemma137b.goodDer_of_simple (Lemma137b.not_comm_of_simple_center_bot hZ)
    exact ⟨pPrimeCore_eq_bot_of_simple hp hpC, hgd.simple, hgd.nonab⟩

section Transvections

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal

section Transv

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem zmod2_aux1 : ∀ a b p : ZMod 2, a + b + p = a → p = b := by decide
theorem zmod2_aux2 : ∀ a b : ZMod 2, a + b = b → a = 0 := by decide
theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem transv_eq_reflect (Q : QuadraticForm (ZMod 2) (ι → ZMod 2))
    (hnd : (polarBilin Q).Nondegenerate) {t : GL ι (ZMod 2)}
    (hQt : ∀ x, Q (t.val *ᵥ x) = Q x) (hT : IsTransvection t) :
    ∃ w : ι → ZMod 2, Q w = 1 ∧ ∀ x, t.val *ᵥ x = x + polar Q x w • w := by
  obtain ⟨v, f, hv, hf, hfv, htx⟩ := hT
  have key : ∀ x, f x = 1 → polar Q x v = Q v := by
    intro x hx
    have h := hQt x
    rw [htx x, hx, one_smul, QuadraticMap.map_add Q] at h
    exact zmod2_aux1 _ _ _ h
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, f x₀ = 1 := by
    by_contra hcon
    push Not at hcon
    apply hf
    refine LinearMap.ext fun x => ?_
    rcases zmod2_cases (f x) with h | h
    · simpa using h
    · exact absurd h (hcon x)
  have hform : ∀ x, polar Q x v = f x * Q v := by
    intro x
    rcases zmod2_cases (f x) with h | h
    · rw [h, zero_mul]
      have h1 : f (x + x₀) = 1 := by rw [map_add, h, hx₀, zero_add]
      have h2 := key _ h1
      rw [polar_add_left, key x₀ hx₀] at h2
      exact zmod2_aux2 _ _ h2
    · rw [h, one_mul]
      exact key x h
  have hne : ∃ y, polar Q v y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (hnd.1 v fun y => by simpa [polarBilin_apply_apply] using hcon y)
  obtain ⟨y, hy⟩ := hne
  have hQv : Q v = 1 := by
    rw [polar_comm, hform] at hy
    rcases zmod2_cases (Q v) with h | h
    · rw [h, mul_zero] at hy; exact absurd rfl hy
    · exact h
  refine ⟨v, hQv, fun x => ?_⟩
  rw [htx x, hform, hQv, mul_one]

end Transv

section Core

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isometryCore_eq_comap (Q : QuadraticForm (ZMod 2) (ι → ZMod 2)) :
    CFSG.MatrixModel.isometryCore ⇑Q =
      (TauCeti.QuadraticMap.orthogonalGroup Q).comap (toLinEquiv ι (ZMod 2)).toMonoidHom :=
  closure_isometries_eq_comap rfl

theorem statedOmega_eq_comap' (Q : QuadraticForm (ZMod 2) (ι → ZMod 2)) :
    StatedOmega ⇑Q = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆.comap (toLinEquiv ι (ZMod 2)).toMonoidHom :=
  statedOmega_eq_comap rfl

@[expose] noncomputable def reflM (Q : QuadraticForm (ZMod 2) (ι → ZMod 2)) (w : ι → ZMod 2) :
    GL ι (ZMod 2) :=
  (toLinEquiv ι (ZMod 2)).symm (reflect Q w)

theorem reflM_mulVec {Q : QuadraticForm (ZMod 2) (ι → ZMod 2)} {w : ι → ZMod 2} (hw : Q w = 1)
    (x : ι → ZMod 2) : (reflM Q w).val *ᵥ x = x + polar Q x w • w := by
  have := reflect_apply_of_map_eq_one (Q := Q) hw x
  rw [← this]
  change (toLinEquiv ι (ZMod 2)) ((toLinEquiv ι (ZMod 2)).symm (reflect Q w)) x = _
  rw [MulEquiv.apply_symm_apply]

theorem eq_reflM_of_transv {Q : QuadraticForm (ZMod 2) (ι → ZMod 2)} {w : ι → ZMod 2}
    (hw : Q w = 1) {t : GL ι (ZMod 2)} (ht : ∀ x, t.val *ᵥ x = x + polar Q x w • w) :
    t = reflM Q w := by
  apply (toLinEquiv ι (ZMod 2)).injective
  refine LinearEquiv.ext fun x => ?_
  rw [toLinEquiv_apply, ht, toLinEquiv_apply, reflM_mulVec hw]

theorem reflM_not_mem {Q : QuadraticForm (ZMod 2) (ι → ZMod 2)}
    (hnd : (polarBilin Q).Nondegenerate) {w : ι → ZMod 2} (hw : Q w = 1) :
    reflM Q w ∉ StatedOmega ⇑Q := by
  rw [statedOmega_eq_comap', Subgroup.mem_comap]
  have hψt : toLinEquiv ι (ZMod 2) (reflM Q w) = reflect Q w := MulEquiv.apply_symm_apply _ _
  rw [MulEquiv.coe_toMonoidHom, hψt]
  have hle : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hnd :=
    CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hnd
  intro hmem
  have h2 : reflect Q w ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      Even (Module.finrank (ZMod 2)
        (CFSG.RankThree.OrthogonalInvolutions.commSpace (reflect Q w))) := hle hmem
  have h3 := CFSG.RankThree.Literature.FSmith.finrank_commSpace_reflect hnd hw
  rw [h3] at h2
  exact (by decide : ¬ Even 1) h2.2

theorem omegaTransv_a {Q : QuadraticForm (ZMod 2) (ι → ZMod 2)}
    (hnd : (polarBilin Q).Nondegenerate)
    (hC1 : ∀ g : GL ι (ZMod 2), g ∈ CFSG.MatrixModel.isometryCore ⇑Q →
      (∀ x ∈ StatedOmega ⇑Q, g * x = x * g) → g = 1)
    {t : GL ι (ZMod 2)} (ht : t ∈ Subgroup.normalizer (StatedOmega ⇑Q : Set (GL ι (ZMod 2))))
    (hQt : ∀ x, ⇑Q (t.val *ᵥ x) = ⇑Q x) (hT : IsTransvection t) :
    ∀ a : ↥(StatedOmega ⇑Q), MulAut.conj a ≠ (StatedOmega ⇑Q).normalizerMonoidHom ⟨t, ht⟩ := by
  obtain ⟨w, hw, hact⟩ := transv_eq_reflect Q hnd hQt hT
  have htw : t = reflM Q w := eq_reflM_of_transv hw hact
  have hz : t ∉ StatedOmega ⇑Q := htw ▸ reflM_not_mem hnd hw
  intro a ha
  have h1 : ∀ x : ↥(StatedOmega ⇑Q), (a : GL ι (ZMod 2)) * x * (a : GL ι (ZMod 2))⁻¹ =
      t * x * t⁻¹ := by
    intro x
    have := congrArg (fun f : MulAut ↥(StatedOmega ⇑Q) =>
      ((f x : ↥(StatedOmega ⇑Q)) : GL ι (ZMod 2))) ha
    simpa [MulAut.conj_apply, Subgroup.normalizerMonoidHom_apply_apply_coe] using this
  have htI : t ∈ CFSG.MatrixModel.isometryCore ⇑Q := Subgroup.subset_closure hQt
  have haI : (a : GL ι (ZMod 2)) ∈ CFSG.MatrixModel.isometryCore ⇑Q :=
    Subgroup.commutator_le_self _ a.2
  have hg := hC1 (t⁻¹ * a) (Subgroup.mul_mem _ (Subgroup.inv_mem _ htI) haI) (by
    intro x hx
    have h2 := h1 ⟨x, hx⟩
    calc t⁻¹ * (a : GL ι (ZMod 2)) * x
        = t⁻¹ * ((a : GL ι (ZMod 2)) * x * (a : GL ι (ZMod 2))⁻¹) * a := by group
      _ = t⁻¹ * (t * x * t⁻¹) * a := by rw [h2]
      _ = x * (t⁻¹ * a) := by group)
  have hta : t = a := inv_mul_eq_one.mp hg
  exact hz (hta ▸ a.2)

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.UnbalancedCatalog in
theorem centralizer_equiv_coord {k : ℕ} (e : ι ≃ Fin (2 * k))
    {Q : QuadraticForm (ZMod 2) (ι → ZMod 2)} (hnd : (polarBilin Q).Nondegenerate)
    {w : ι → ZMod 2} (hw : Q w = 1) :
    (polarBilin (reindexQuadraticForm e Q)).Nondegenerate ∧
    reindexQuadraticForm e Q (reindexVectorEquiv (K := ZMod 2) e w) = 1 ∧
    symmetryGL (reindexQuadraticForm e Q) (reindexVectorEquiv (K := ZMod 2) e w) ∉
      matrixDerived (reindexQuadraticForm e Q) ∧
    Nonempty (↥(StatedOmega ⇑Q ⊓ Subgroup.centralizer ({reflM Q w} : Set (GL ι (ZMod 2)))) ≃*
      ↥(matrixDerived (reindexQuadraticForm e Q) ⊓
        symmetryCentralizer (reindexQuadraticForm e Q)
          (reindexVectorEquiv (K := ZMod 2) e w))) := by
  set ρ := reindexMatrixEquiv (K := ZMod 2) e with hρ
  set Q' := reindexQuadraticForm e Q with hQ'
  have hnd' : (polarBilin Q').Nondegenerate :=
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.nondegenerate_polarBilin_of_isometry
      (reindexVectorEquiv e).symm (fun v => rfl) hnd
  set v' := reindexVectorEquiv (K := ZMod 2) e w with hv'def
  have hv' : Q' v' = 1 := by
    rw [hv'def, hQ', reindexQuadraticForm_map]
    exact hw
  have hρt : ρ (reflM Q w) = symmetryGL Q' v' := by
    refine CFSG.HardMathSupport.Curtis.Coordinator.PLType.OrthCent.gl_ext' fun x => ?_
    obtain ⟨y, rfl⟩ := (reindexVectorEquiv e).surjective x
    rw [symmetryGL_mulVec_of_charTwo hv']
    have h1 := reindexMatrixEquiv_mulVec (K := ZMod 2) e (reflM Q w) y
    rw [matrixLinearEquiv_apply] at h1
    rw [h1, reflM_mulVec hw y, map_add, map_smul]
    have h2 := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.polar_isometry
      (reindexVectorEquiv (K := ZMod 2) e) (reindexQuadraticForm_map e Q) w y
    rw [hv'def, h2, polar_comm]
  have hΩρ : (StatedOmega ⇑Q).map ρ.toMonoidHom = matrixDerived Q' := stated_derived_reindex e Q
  have hz' : symmetryGL Q' v' ∉ matrixDerived Q' := by
    rw [← hρt, ← hΩρ, Subgroup.mem_map_equiv]
    simpa using reflM_not_mem hnd hw
  have hcent : (Subgroup.centralizer ({reflM Q w} : Set (GL ι (ZMod 2)))).map ρ.toMonoidHom =
      Subgroup.centralizer {symmetryGL Q' v'} := by
    rw [← hρt]
    ext A
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have := congrArg ρ h
      simpa using this
    · intro h
      apply ρ.injective
      simpa using h
  have hmap : (StatedOmega ⇑Q ⊓ Subgroup.centralizer {reflM Q w}).map ρ.toMonoidHom =
      matrixDerived Q' ⊓ symmetryCentralizer Q' v' := by
    have hinj : Function.Injective ρ.toMonoidHom := ρ.injective
    rw [Subgroup.map_inf (StatedOmega ⇑Q) (Subgroup.centralizer {reflM Q w}) ρ.toMonoidHom hinj,
      hΩρ, hcent]
    ext A
    simp only [Subgroup.mem_inf, symmetryCentralizer]
    exact ⟨fun h => ⟨h.1, matrixDerived_le_isometries _ h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  exact ⟨hnd', hv', hz', ⟨(Subgroup.equivMapOfInjective _ ρ.toMonoidHom ρ.injective).trans
    (MulEquiv.subgroupCongr hmap)⟩⟩

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.UnbalancedCatalog in
theorem card_centralizer_le {k : ℕ} (e : ι ≃ Fin (2 * k))
    {Q : QuadraticForm (ZMod 2) (ι → ZMod 2)} (hnd : (polarBilin Q).Nondegenerate)
    {w : ι → ZMod 2} (hw : Q w = 1) :
    Nat.card ↥(StatedOmega ⇑Q ⊓ Subgroup.centralizer ({reflM Q w} : Set (GL ι (ZMod 2)))) ≤
      Nat.card ↥(StatedSp (k - 1) (ZMod 2)) := by
  obtain ⟨hnd', hv', hz', ⟨E⟩⟩ := centralizer_equiv_coord e hnd hw
  rw [Nat.card_congr E.toEquiv]
  set Q' := reindexQuadraticForm e Q with hQ'
  set v' := reindexVectorEquiv (K := ZMod 2) e w with hv'def
  let ρ' : symmetryCentralizer Q' v' →* ↥(CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup
      (vQuotForm Q' v')) :=
    (symmetryRestrict hnd' hv').codRestrict _ (symmetryRestrict_mem hnd' hv')
  let φ : ↥(matrixDerived Q' ⊓ symmetryCentralizer Q' v') →*
      ↥(CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup (vQuotForm Q' v')) :=
    ρ'.comp (Subgroup.inclusion inf_le_right)
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_bot]
    have h1 : symmetryRestrict hnd' hv' (Subgroup.inclusion inf_le_right x) = 1 :=
      congrArg Subtype.val hx
    rcases eq_one_or_eq_symmetryGL_of_restrict_eq_one hnd' hv' h1 with h | h
    · exact Subtype.ext h
    · exfalso
      apply hz'
      have hmem := x.2.1
      have h2 : ((x : GL (Fin (2 * k)) (ZMod 2))) = symmetryGL Q' v' := h
      rwa [h2] at hmem
  obtain ⟨g⟩ := CFSG.HardMathSupport.Curtis.Coordinator.PLType.OrthCoord.nonempty_bilinIsometryGroup_vQuotForm_equiv
    hnd' hv' (rfl : 2 * k = 2 * k)
  calc Nat.card ↥(matrixDerived Q' ⊓ symmetryCentralizer Q' v')
      ≤ Nat.card ↥(CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup (vQuotForm Q' v')) :=
        Nat.card_le_card_of_injective _ hinj
    _ = Nat.card ↥(StatedSp (k - 1) (ZMod 2)) := Nat.card_congr g.toEquiv

theorem fixSub_equiv_centralizer {Ω : Subgroup (GL ι (ZMod 2))} {t : GL ι (ZMod 2)}
    (ht : t ∈ Subgroup.normalizer (Ω : Set (GL ι (ZMod 2)))) :
    Nonempty (↥(fixSub (Ω.normalizerMonoidHom ⟨t, ht⟩)) ≃*
      ↥(Ω ⊓ Subgroup.centralizer ({t} : Set (GL ι (ZMod 2))))) := by
  have hfix : fixSub (Ω.normalizerMonoidHom ⟨t, ht⟩) =
      (Ω ⊓ Subgroup.centralizer {t}).subgroupOf Ω := by
    ext x
    rw [mem_fixSub, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h'
      refine ⟨x.2, ?_⟩
      calc (x : GL ι (ZMod 2)) * t = (t * x * t⁻¹) * t := by rw [h']
        _ = t * x := by group
    · rintro ⟨-, h⟩
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      calc t * (x : GL ι (ZMod 2)) * t⁻¹ = (x * t) * t⁻¹ := by rw [h]
        _ = x := by group
  exact ⟨(MulEquiv.subgroupCongr hfix).trans (Subgroup.subgroupOfEquivOfLe inf_le_left)⟩

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.UnbalancedCatalog in
theorem omegaTransv_core {k : ℕ} (e : ι ≃ Fin (2 * k))
    (Q : QuadraticForm (ZMod 2) (ι → ZMod 2)) (hnd : (polarBilin Q).Nondegenerate)
    (hrel : (⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆).relIndex (TauCeti.QuadraticMap.orthogonalGroup Q) = 2)
    (hC1 : ∀ g : GL ι (ZMod 2), g ∈ CFSG.MatrixModel.isometryCore ⇑Q →
      (∀ x ∈ StatedOmega ⇑Q, g * x = x * g) → g = 1)
    {t : GL ι (ZMod 2)} (ht : t ∈ Subgroup.normalizer (StatedOmega ⇑Q : Set (GL ι (ZMod 2))))
    (hQt : ∀ x, ⇑Q (t.val *ᵥ x) = ⇑Q x) (hT : IsTransvection t) :
    (∀ a : ↥(StatedOmega ⇑Q), MulAut.conj a ≠ (StatedOmega ⇑Q).normalizerMonoidHom ⟨t, ht⟩) ∧
      Nonempty (↥(fixSub ((StatedOmega ⇑Q).normalizerMonoidHom ⟨t, ht⟩)) ≃*
        ↥(StatedSp (k - 1) (ZMod 2))) := by
  refine ⟨omegaTransv_a hnd hC1 ht hQt hT, ?_⟩
  obtain ⟨w, hw, hact⟩ := transv_eq_reflect Q hnd hQt hT
  have htw : t = reflM Q w := eq_reflM_of_transv hw hact
  subst htw
  obtain ⟨hnd', hv', hz', ⟨E⟩⟩ := centralizer_equiv_coord e hnd hw
  set ρ := reindexMatrixEquiv (K := ZMod 2) e with hρ
  set Q' := reindexQuadraticForm e Q with hQ'
  set ψ := (toLinEquiv ι (ZMod 2)) with hψ
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  have hΩ : StatedOmega ⇑Q = ⁅O, O⁆.comap ψ.toMonoidHom := statedOmega_eq_comap' Q
  have hI : CFSG.MatrixModel.isometryCore ⇑Q = O.comap ψ.toMonoidHom := isometryCore_eq_comap Q
  have hΩρ : (StatedOmega ⇑Q).map ρ.toMonoidHom = matrixDerived Q' := stated_derived_reindex e Q
  have hIρ : (CFSG.MatrixModel.isometryCore ⇑Q).map ρ.toMonoidHom = matrixIsometries Q' :=
    stated_isometries_reindex e Q
  have hidx' : ∀ x y, x ∈ matrixIsometries Q' → y ∈ matrixIsometries Q' →
      x ∉ matrixDerived Q' → y ∉ matrixDerived Q' → x * y ∈ matrixDerived Q' := by
    intro x y hx hy hxn hyn
    rw [← hIρ, Subgroup.mem_map_equiv] at hx hy
    have hxn' : ρ.symm x ∉ StatedOmega ⇑Q := fun h =>
      hxn (by rw [← hΩρ, Subgroup.mem_map_equiv]; exact h)
    have hyn' : ρ.symm y ∉ StatedOmega ⇑Q := fun h =>
      hyn (by rw [← hΩρ, Subgroup.mem_map_equiv]; exact h)
    have hmul : ρ.symm x * ρ.symm y ∈ StatedOmega ⇑Q := by
      rw [hΩ] at hxn' hyn' ⊢
      rw [hI] at hx hy
      rw [Subgroup.mem_comap] at hxn' hyn' hx hy ⊢
      rw [map_mul]
      exact CFSG.HardMathSupport.Curtis.Coordinator.PLType.OrthCent.mul_mem_of_relIndex_two hrel
        hx hy hxn' hyn'
    rw [← hΩρ, Subgroup.mem_map_equiv, map_mul]
    exact hmul
  obtain ⟨f⟩ := CFSG.HardMathSupport.Curtis.Coordinator.PLType.OrthCoord.coord_centralizer_equiv
    Q' hnd' _ hv' hidx' hz'
  obtain ⟨F⟩ := fixSub_equiv_centralizer (Ω := StatedOmega ⇑Q) (t := reflM Q w) ht
  exact ⟨F.trans (E.trans f)⟩

end Core

end Transvections

section Instances

open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal

theorem relIndex_commutator_quadPlus {k : ℕ} (hk : 2 ≤ k) :
    (⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus (k + 1) (ZMod 2)),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus (k + 1) (ZMod 2))⁆).relIndex
        (TauCeti.QuadraticMap.orthogonalGroup (quadPlus (k + 1) (ZMod 2))) = 2 := by
  have hnd : (QuadraticMap.polarBilin (quadPlus (k + 1) (ZMod 2))).Nondegenerate :=
    nondegenerate_polarBilin_quadPlus (k + 1) (ZMod 2)
  have h6 : 6 ≤ Module.finrank (ZMod 2) (Fin (k + 1) ⊕ Fin (k + 1) → ZMod 2) := by
    simp [Module.finrank_fintype_fun_eq_card]
    omega
  haveI : Nonempty (Fin (k + 1) ⊕ Fin (k + 1)) := ⟨Sum.inl 0⟩
  rw [CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup hnd h6]
  exact CFSG.RankThree.OrthogonalInvolutions.relIndex_omegaGroup _ hnd

theorem relIndex_commutator_quadMinus {k : ℕ} (hk : 2 ≤ k) :
    (⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus (k + 1) (ZMod 2) 1 1),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus (k + 1) (ZMod 2) 1 1)⁆).relIndex
        (TauCeti.QuadraticMap.orthogonalGroup (quadMinus (k + 1) (ZMod 2) 1 1)) = 2 := by
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  have hnd : (QuadraticMap.polarBilin (quadMinus (k + 1) (ZMod 2) 1 1)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite (k + 1) (ZMod 2) hirr
  have h6 : 6 ≤ Module.finrank (ZMod 2) (Fin (k + 1 - 1) ⊕ Fin (k + 1 - 1) ⊕ Fin 2 → ZMod 2) := by
    simp [Module.finrank_fintype_fun_eq_card]
    omega
  haveI : Nonempty (Fin (k + 1 - 1) ⊕ Fin (k + 1 - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  rw [CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup hnd h6]
  exact CFSG.RankThree.OrthogonalInvolutions.relIndex_omegaGroup _ hnd

theorem relIndex_commutator_quadMinus_two :
    (⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 (ZMod 2) 1 1),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 (ZMod 2) 1 1)⁆).relIndex
        (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 (ZMod 2) 1 1)) = 2 := by
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  have hQ := coe_quadMinus 2 (ZMod 2) 1 1
  have hO := (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus 1 hirr).2
  have hOcard : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 (ZMod 2) 1 1)) =
      120 := by
    have h2 : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
        (quadMinus (1 + 1) (ZMod 2) 1 1)) : ℤ) = 120 := by
      rw [hO, Nat.card_zmod]
      norm_num [Finset.prod_Icc_succ_top]
    exact_mod_cast h2
  have hΩcard : Nat.card ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 (ZMod 2) 1 1),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 (ZMod 2) 1 1)⁆ = 60 := by
    have := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.card_statedOmega_quadMinus_two
    rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hQ, card_comap_mulEquiv] at this
    exact this
  have hle := Subgroup.commutator_le_self (TauCeti.QuadraticMap.orthogonalGroup
    (quadMinus 2 (ZMod 2) 1 1))
  have hcard := (Subgroup.subgroupOf ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 (ZMod 2) 1 1),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 (ZMod 2) 1 1)⁆
      (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 (ZMod 2) 1 1))).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hΩcard, hOcard] at hcard
  rw [Subgroup.relIndex]
  omega

theorem eq_one_of_commute_of_rigid {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm (ZMod 2) (ι → ZMod 2)}
    {E : Subgroup ((ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2))}
    (hE : (StatedOmega ⇑Q).map (toLinEquiv ι (ZMod 2)).toMonoidHom = E)
    (hrig : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, (∀ x ∈ E, g * x = x * g) → g = 1) :
    ∀ g : GL ι (ZMod 2), g ∈ CFSG.MatrixModel.isometryCore ⇑Q →
      (∀ x ∈ StatedOmega ⇑Q, g * x = x * g) → g = 1 := by
  intro g hg hc
  have hg' : toLinEquiv ι (ZMod 2) g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    have := hg
    rw [isometryCore_eq_comap, Subgroup.mem_comap] at this
    exact this
  have h1 : toLinEquiv ι (ZMod 2) g = 1 := by
    refine hrig _ hg' fun x' hx' => ?_
    rw [← hE, Subgroup.mem_map] at hx'
    obtain ⟨x, hx, rfl⟩ := hx'
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, hc x hx]
  exact (toLinEquiv ι (ZMod 2)).injective (h1.trans (map_one _).symm)

theorem hC1_plus {m : ℕ} (hm : 3 ≤ m) :
    ∀ g : GL (Fin m ⊕ Fin m) (ZMod 2), g ∈ CFSG.MatrixModel.isometryCore ⇑(quadPlus m (ZMod 2)) →
      (∀ x ∈ StatedOmega ⇑(quadPlus m (ZMod 2)), g * x = x * g) → g = 1 := by
  refine eq_one_of_commute_of_rigid (E := elementaryGroup (quadPlus m (ZMod 2))) ?_ ?_
  · rw [coe_quadPlus]
    exact CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedOmega_quadPlus_eq_map_elementaryGroup
      (K := ZMod 2) hm
  · intro g hg hc
    exact CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.eq_one_of_commute_elementaryGroup_of_isometry_plus
      (K := ZMod 2) hm (LinearEquiv.refl (ZMod 2) _) (fun v => rfl) hg hc

theorem hC1_minus {m : ℕ} (hm : 3 ≤ m) :
    ∀ g : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (ZMod 2),
      g ∈ CFSG.MatrixModel.isometryCore ⇑(quadMinus m (ZMod 2) 1 1) →
      (∀ x ∈ StatedOmega ⇑(quadMinus m (ZMod 2) 1 1), g * x = x * g) → g = 1 := by
  refine eq_one_of_commute_of_rigid (E := elementaryGroup (quadMinus m (ZMod 2) 1 1)) ?_ ?_
  · rw [coe_quadMinus]
    exact CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedOmega_quadMinus_eq_map_elementaryGroup
      (K := ZMod 2) (m := m) (by omega)
  · intro g hg hc
    exact CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.eq_one_of_commute_elementaryGroup_of_isometry_minus
      (K := ZMod 2) hm (LinearEquiv.refl (ZMod 2) _) (fun v => rfl) hg hc

open Matrix CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaFour in
theorem hC1_minus_two :
    ∀ g : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (ZMod 2),
      g ∈ CFSG.MatrixModel.isometryCore ⇑(quadMinus 2 (ZMod 2) 1 1) →
      (∀ x ∈ StatedOmega ⇑(quadMinus 2 (ZMod 2) 1 1), g * x = x * g) → g = 1 := by
  intro g hg hc
  rw [coe_quadMinus] at hg hc
  have hgO : g ∈ O4 := by
    have h : Subgroup.closure
        {A : GL ι4 (ZMod 2) | ∀ v, Q4 ((A : Matrix ι4 ι4 (ZMod 2)) *ᵥ v) = Q4 v} = O4 :=
      Subgroup.closure_eq O4
    rw [← h]
    exact hg
  have h1 : Subgroup.map O4.subtype ⁅(⊤ : Subgroup O4), (⊤ : Subgroup O4)⁆ = StatedOmega Q4 := by
    rw [statedOmega_eq, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have h2 : Subgroup.map o4MulEquivPerm.toMonoidHom ⁅(⊤ : Subgroup O4), (⊤ : Subgroup O4)⁆ =
      alternatingGroup (Fin 5) := by
    have htop : o4MulEquivPerm.toMonoidHom.range = ⊤ :=
      MonoidHom.range_eq_top.2 o4MulEquivPerm.surjective
    rw [Subgroup.map_commutator, Subgroup.map_top, htop]
    exact alternatingGroup.commutator_perm_eq (by simp)
  have hσ : ∀ τ ∈ alternatingGroup (Fin 5),
      o4MulEquivPerm ⟨g, hgO⟩ * τ = τ * o4MulEquivPerm ⟨g, hgO⟩ := by
    intro τ hτ
    rw [← h2] at hτ
    obtain ⟨x, hx, rfl⟩ := hτ
    have hxΩ : (x : GL ι4 (ZMod 2)) ∈ StatedOmega Q4 := by
      rw [← h1]
      exact Subgroup.mem_map_of_mem _ hx
    have hgx : (⟨g, hgO⟩ : O4) * x = x * ⟨g, hgO⟩ := Subtype.ext (hc x hxΩ)
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, hgx]
  have h3 : o4MulEquivPerm ⟨g, hgO⟩ = 1 :=
    Lemma137b.eq_one_of_commute_alternatingGroup (n := 5) le_rfl hσ
  have h4 : (⟨g, hgO⟩ : O4) = 1 := o4MulEquivPerm.injective (h3.trans (map_one _).symm)
  exact congrArg Subtype.val h4

theorem omegaTransv_core' {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ} (e : ι ≃ Fin (2 * k))
    (Q : QuadraticForm (ZMod 2) (ι → ZMod 2)) (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hrel : (⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆).relIndex
          (TauCeti.QuadraticMap.orthogonalGroup Q) = 2)
    (hC1 : ∀ g : GL ι (ZMod 2), g ∈ CFSG.MatrixModel.isometryCore ⇑Q →
      (∀ x ∈ StatedOmega ⇑Q, g * x = x * g) → g = 1)
    {Q₀ : (ι → ZMod 2) → ZMod 2} (hQ : ⇑Q = Q₀) {t : GL ι (ZMod 2)}
    (ht : t ∈ Subgroup.normalizer (StatedOmega Q₀ : Set (GL ι (ZMod 2))))
    (hQt : ∀ x, Q₀ (Matrix.mulVec (t.val) x) = Q₀ x) (hT : IsTransvection t) :
    (∀ a : ↥(StatedOmega Q₀), MulAut.conj a ≠ (StatedOmega Q₀).normalizerMonoidHom ⟨t, ht⟩) ∧
      Nonempty (↥(fixSub ((StatedOmega Q₀).normalizerMonoidHom ⟨t, ht⟩)) ≃*
        ↥(StatedSp (k - 1) (ZMod 2))) := by
  subst hQ
  exact omegaTransv_core e Q hnd hrel hC1 ht hQt hT

theorem transv_plus_of_two_le {n : ℕ} (hn : 2 ≤ n)
    {t : GL (Fin (n + 1) ⊕ Fin (n + 1)) (ZMod 2)}
    (ht : t ∈ Subgroup.normalizer
      (StatedOmega (StatedQuadPlus (n + 1) (ZMod 2)) : Set (GL (Fin (n + 1) ⊕ Fin (n + 1)) (ZMod 2))))
    (hQt : ∀ x, StatedQuadPlus (n + 1) (ZMod 2) (Matrix.mulVec (t : Matrix _ _ (ZMod 2)) x) =
      StatedQuadPlus (n + 1) (ZMod 2) x)
    (hT : IsTransvection t) :
    (∀ a : ↥(StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))),
      MulAut.conj a ≠ (StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))).normalizerMonoidHom ⟨t, ht⟩) ∧
    Nonempty (↥(fixSub ((StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))).normalizerMonoidHom
      ⟨t, ht⟩)) ≃* ↥(StatedSp n (ZMod 2))) := by
  have e : (Fin (n + 1) ⊕ Fin (n + 1)) ≃ Fin (2 * (n + 1)) :=
    Fintype.equivFinOfCardEq (by simp [Fintype.card_sum]; ring)
  exact omegaTransv_core' e (quadPlus (n + 1) (ZMod 2))
    (nondegenerate_polarBilin_quadPlus (n + 1) (ZMod 2))
    (relIndex_commutator_quadPlus hn) (hC1_plus (by omega)) (coe_quadPlus (n + 1) (ZMod 2)) ht
    hQt hT

theorem transv_minus {n : ℕ} (hn : 1 ≤ n)
    {t : GL (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2) (ZMod 2)}
    (ht : t ∈ Subgroup.normalizer
      (StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1) :
        Set (GL (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2) (ZMod 2))))
    (hQt : ∀ x, StatedQuadMinus (n + 1) (ZMod 2) 1 1 (Matrix.mulVec (t : Matrix _ _ (ZMod 2)) x) =
      StatedQuadMinus (n + 1) (ZMod 2) 1 1 x)
    (hT : IsTransvection t) :
    (∀ a : ↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)),
      MulAut.conj a ≠ (StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)).normalizerMonoidHom
        ⟨t, ht⟩) ∧
    Nonempty (↥(fixSub ((StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)).normalizerMonoidHom
      ⟨t, ht⟩)) ≃* ↥(StatedSp n (ZMod 2))) := by
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  have e : (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2) ≃ Fin (2 * (n + 1)) :=
    Fintype.equivFinOfCardEq (by simp [Fintype.card_sum]; omega)
  have hnd := nondegenerate_polarBilin_quadMinus_of_finite (n + 1) (ZMod 2) (b := 1) (c := 1) hirr
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · obtain rfl : n = 1 := by omega
    exact omegaTransv_core' e (quadMinus 2 (ZMod 2) 1 1) hnd relIndex_commutator_quadMinus_two
      (hC1_minus_two) (coe_quadMinus 2 (ZMod 2) 1 1) ht hQt hT
  · exact omegaTransv_core' e (quadMinus (n + 1) (ZMod 2) 1 1) hnd
      (relIndex_commutator_quadMinus h2) (hC1_minus (by omega)) (coe_quadMinus (n + 1) (ZMod 2) 1 1)
      ht hQt hT

@[expose] def PlusTwoTransv : Prop :=
  ∀ (t : GL (Fin (1 + 1) ⊕ Fin (1 + 1)) (ZMod 2))
    (ht : t ∈ Subgroup.normalizer
      (StatedOmega (StatedQuadPlus (1 + 1) (ZMod 2)) :
        Set (GL (Fin (1 + 1) ⊕ Fin (1 + 1)) (ZMod 2)))),
    (∀ x, StatedQuadPlus (1 + 1) (ZMod 2) (Matrix.mulVec (t : Matrix _ _ (ZMod 2)) x) =
      StatedQuadPlus (1 + 1) (ZMod 2) x) →
    IsTransvection t →
    (∀ a : ↥(StatedOmega (StatedQuadPlus (1 + 1) (ZMod 2))),
      MulAut.conj a ≠ (StatedOmega (StatedQuadPlus (1 + 1) (ZMod 2))).normalizerMonoidHom ⟨t, ht⟩) ∧
    Nonempty (↥(fixSub ((StatedOmega (StatedQuadPlus (1 + 1) (ZMod 2))).normalizerMonoidHom
      ⟨t, ht⟩)) ≃* ↥(StatedSp 1 (ZMod 2)))

theorem input9_6OmegaTransv_of_plusTwo (h : PlusTwoTransv) : Lemma137b.Input9_6OmegaTransv := by
  refine ⟨fun n hn t ht hQt hT => ?_, fun n hn t ht hQt hT => transv_minus hn ht hQt hT⟩
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · obtain rfl : n = 1 := by omega
    exact h t ht hQt hT
  · exact transv_plus_of_two_le h2 ht hQt hT

section PlusTwo

open Matrix

@[expose] def colsMat4 (c0 c1 c2 c3 : Fin 2 ⊕ Fin 2 → ZMod 2) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  Matrix.of fun i j => (Sum.elim ![c0, c1] ![c2, c3] j) i

theorem eq_colsMat4 (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) :
    M = colsMat4 (M *ᵥ Pi.single (Sum.inl 0) 1) (M *ᵥ Pi.single (Sum.inl 1) 1)
      (M *ᵥ Pi.single (Sum.inr 0) 1) (M *ᵥ Pi.single (Sum.inr 1) 1) := by
  ext i j
  rcases j with j | j <;> fin_cases j <;> simp [colsMat4, Matrix.mulVec_single_one]

@[expose] def ColsOK (c0 c1 c2 c3 : Fin 2 ⊕ Fin 2 → ZMod 2) : Prop :=
  Qplus4 c0 = 0 ∧ Qplus4 c1 = 0 ∧ Qplus4 c2 = 0 ∧ Qplus4 c3 = 0 ∧
    Qplus4 (c0 + c1) = 0 ∧ Qplus4 (c0 + c2) = 1 ∧ Qplus4 (c0 + c3) = 0 ∧
    Qplus4 (c1 + c2) = 0 ∧ Qplus4 (c1 + c3) = 1 ∧ Qplus4 (c2 + c3) = 0

instance (c0 c1 c2 c3 : Fin 2 ⊕ Fin 2 → ZMod 2) : Decidable (ColsOK c0 c1 c2 c3) := by
  unfold ColsOK; infer_instance

theorem colsOK_of_iso (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2))
    (h : ∀ v : Fin 2 ⊕ Fin 2 → ZMod 2, Qplus4 (M *ᵥ v) = Qplus4 v) :
    ColsOK (M *ᵥ Pi.single (Sum.inl 0) 1) (M *ᵥ Pi.single (Sum.inl 1) 1)
      (M *ᵥ Pi.single (Sum.inr 0) 1) (M *ᵥ Pi.single (Sum.inr 1) 1) := by
  have hq : ∀ u v : Fin 2 ⊕ Fin 2 → ZMod 2, Qplus4 (M *ᵥ u + M *ᵥ v) = Qplus4 (u + v) := by
    intro u v
    rw [← Matrix.mulVec_add, h]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [hq]; decide
  · rw [hq]; decide
  · rw [hq]; decide
  · rw [hq]; decide
  · rw [hq]; decide
  · rw [hq]; decide

@[expose] def gCmat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  colsMat4 (Pi.single (Sum.inr 1) 1) (Pi.single (Sum.inr 0) 1) (Pi.single (Sum.inl 1) 1)
    (Pi.single (Sum.inl 0) 1)

theorem gCmat_sq : gCmat * gCmat = 1 := by decide +kernel
theorem gCmat_iso : ∀ v : Fin 2 ⊕ Fin 2 → ZMod 2, Qplus4 (gCmat *ᵥ v) = Qplus4 v := by
  decide +kernel

@[expose] def gC : GL (Fin 2 ⊕ Fin 2) (ZMod 2) := ⟨gCmat, gCmat, gCmat_sq, gCmat_sq⟩

theorem gC_inv : gC⁻¹ = gC := inv_eq_of_mul_eq_one_right (Units.ext gCmat_sq)

@[expose] def iotaGL : GL (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  gC * reflGL Qplus4 va1 refl_va1 * gC * reflGL Qplus4 va1 refl_va1

theorem iotaGL_val : (iotaGL : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) =
    gCmat * reflMat Qplus4 va1 * gCmat * reflMat Qplus4 va1 := rfl

@[expose] def CommCond (c0 c1 c2 c3 : Fin 2 ⊕ Fin 2 → ZMod 2) : Prop :=
  colsMat4 c0 c1 c2 c3 * (G41 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) =
      (G41 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) * colsMat4 c0 c1 c2 c3 →
    colsMat4 c0 c1 c2 c3 * (G42 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) =
      (G42 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) * colsMat4 c0 c1 c2 c3 →
    colsMat4 c0 c1 c2 c3 * (iotaGL : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) =
      (iotaGL : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) * colsMat4 c0 c1 c2 c3 →
    colsMat4 c0 c1 c2 c3 = 1

instance (c0 c1 c2 c3 : Fin 2 ⊕ Fin 2 → ZMod 2) : Decidable (CommCond c0 c1 c2 c3) := by
  unfold CommCond
  infer_instance

theorem plusTwo_cols : ∀ c0 : Fin 2 ⊕ Fin 2 → ZMod 2, Qplus4 c0 = 0 →
    ∀ c1 : Fin 2 ⊕ Fin 2 → ZMod 2, Qplus4 c1 = 0 → Qplus4 (c0 + c1) = 0 →
    ∀ c2 : Fin 2 ⊕ Fin 2 → ZMod 2, Qplus4 c2 = 0 → Qplus4 (c0 + c2) = 1 → Qplus4 (c1 + c2) = 0 →
    ∀ c3 : Fin 2 ⊕ Fin 2 → ZMod 2, Qplus4 c3 = 0 → Qplus4 (c0 + c3) = 0 → Qplus4 (c1 + c3) = 1 →
      Qplus4 (c2 + c3) = 0 → CommCond c0 c1 c2 c3 := by
  have hcheck : ∀ c0 c1 c2 c3 : Fin 2 ⊕ Fin 2 → ZMod 2,
      ColsOK c0 c1 c2 c3 → CommCond c0 c1 c2 c3 := by
    decide +kernel +revert
  intro c0 h0 c1 h1 h01 c2 h2 h02 h12 c3 h3 h03 h13 h23
  exact hcheck c0 c1 c2 c3 ⟨h0, h1, h2, h3, h01, h02, h03, h12, h13, h23⟩

theorem iso_of_mem_isometryCore {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm (ZMod 2) (ι → ZMod 2)} {Q₀ : (ι → ZMod 2) → ZMod 2} (hQ : ⇑Q = Q₀)
    {g : GL ι (ZMod 2)} (hg : g ∈ CFSG.MatrixModel.isometryCore Q₀) :
    ∀ v, Q₀ (Matrix.mulVec (g : Matrix ι ι (ZMod 2)) v) = Q₀ v := by
  subst hQ
  rw [isometryCore_eq_comap, Subgroup.mem_comap] at hg
  intro v
  have := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hg v
  rwa [MulEquiv.coe_toMonoidHom, toLinEquiv_apply] at this

theorem gC_mem : gC ∈ CFSG.MatrixModel.isometryCore Qplus4 :=
  Subgroup.subset_closure gCmat_iso

theorem iotaGL_mem : iotaGL ∈ StatedOmega Qplus4 := by
  have h1 := Subgroup.commutator_mem_commutator gC_mem
    (reflGL_mem_isometryCore Qplus4 va1 refl_va1 iso_va1)
  rw [commutatorElement_def, gC_inv, reflGL_inv] at h1
  exact h1

theorem G41_mem : G41 ∈ StatedOmega Qplus4 :=
  comm_refl_mem Qplus4 va1 vb1 refl_va1 refl_vb1 iso_va1 iso_vb1

theorem G42_mem : G42 ∈ StatedOmega Qplus4 :=
  comm_refl_mem Qplus4 va2 vb2 refl_va2 refl_vb2 iso_va2 iso_vb2

theorem hC1_plus_two :
    ∀ g : GL (Fin 2 ⊕ Fin 2) (ZMod 2),
      g ∈ CFSG.MatrixModel.isometryCore ⇑(quadPlus 2 (ZMod 2)) →
      (∀ x ∈ StatedOmega ⇑(quadPlus 2 (ZMod 2)), g * x = x * g) → g = 1 := by
  intro g hg hc
  rw [coe_quadPlus] at hg hc
  have hiso := iso_of_mem_isometryCore (coe_quadPlus 2 (ZMod 2)) hg
  obtain ⟨c0, c1, c2, c3, hgc, hok⟩ : ∃ c0 c1 c2 c3 : Fin 2 ⊕ Fin 2 → ZMod 2,
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) = colsMat4 c0 c1 c2 c3 ∧
        ColsOK c0 c1 c2 c3 :=
    ⟨_, _, _, _, eq_colsMat4 _, colsOK_of_iso _ hiso⟩
  obtain ⟨q0, q1, q2, q3, q01, q02, q03, q12, q13, q23⟩ := hok
  have h1 := congrArg Units.val (hc G41 G41_mem)
  have h2 := congrArg Units.val (hc G42 G42_mem)
  have h3 := congrArg Units.val (hc iotaGL iotaGL_mem)
  rw [Units.val_mul, Units.val_mul, hgc] at h1 h2 h3
  apply Units.ext
  rw [hgc, Units.val_one]
  exact plusTwo_cols c0 q0 c1 q1 q01 c2 q2 q02 q12 c3 q3 q03 q13 q23 h1 h2 h3

section PlusTwoGeneral

open QuadraticMap

theorem conj_mem_statedOmega {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm (ZMod 2) (ι → ZMod 2)} {g x : GL ι (ZMod 2)}
    (hg : g ∈ CFSG.MatrixModel.isometryCore ⇑Q) (hx : x ∈ StatedOmega ⇑Q) :
    g * x * g⁻¹ ∈ StatedOmega ⇑Q := by
  rw [statedOmega_eq_comap', Subgroup.mem_comap] at hx ⊢
  rw [isometryCore_eq_comap, Subgroup.mem_comap] at hg
  rw [map_mul, map_mul, map_inv]
  exact CFSG.RankThree.Literature.FSmith.conj_mem_commutator_orthogonalGroup hg hx

theorem conj_reflM {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm (ZMod 2) (ι → ZMod 2)} {g : GL ι (ZMod 2)}
    (hg : g ∈ CFSG.MatrixModel.isometryCore ⇑Q) {a : ι → ZMod 2} (ha : Q a = 1) :
    g * reflM Q a * g⁻¹ = reflM Q (Matrix.mulVec (g : Matrix ι ι (ZMod 2)) a) := by
  have hg' : toLinEquiv ι (ZMod 2) g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [isometryCore_eq_comap, Subgroup.mem_comap] at hg
    exact hg
  have hQga : Q (Matrix.mulVec (g : Matrix ι ι (ZMod 2)) a) = 1 := by
    have := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hg' a
    rw [toLinEquiv_apply] at this
    rw [this, ha]
  refine eq_reflM_of_transv hQga (fun x => ?_)
  have hgx : Matrix.mulVec (g : Matrix ι ι (ZMod 2))
      (Matrix.mulVec ((g⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) x) = x := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hpol : polar Q (Matrix.mulVec ((g⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) x) a =
      polar Q x (Matrix.mulVec (g : Matrix ι ι (ZMod 2)) a) := by
    have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg'
      (Matrix.mulVec ((g⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) x) a
    rw [toLinEquiv_apply, toLinEquiv_apply, hgx] at this
    exact this.symm
  calc Matrix.mulVec ((g * reflM Q a * g⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) x
      = Matrix.mulVec (g : Matrix ι ι (ZMod 2))
          (Matrix.mulVec ((reflM Q a : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2))
            (Matrix.mulVec ((g⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) x)) := by
        rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    _ = x + polar Q x (Matrix.mulVec (g : Matrix ι ι (ZMod 2)) a) •
          Matrix.mulVec (g : Matrix ι ι (ZMod 2)) a := by
        rw [reflM_mulVec ha, Matrix.mulVec_add, Matrix.mulVec_smul, hgx, hpol]

theorem refl_sq_of_nonsing : ∀ u : Fin 2 ⊕ Fin 2 → ZMod 2, Qplus4 u = 1 →
    reflMat Qplus4 u * reflMat Qplus4 u = 1 := by decide +kernel

theorem iso_refl_of_nonsing : ∀ u : Fin 2 ⊕ Fin 2 → ZMod 2, Qplus4 u = 1 →
    ∀ v, Qplus4 (Matrix.mulVec (reflMat Qplus4 u) v) = Qplus4 v := by decide +kernel

theorem exists_refl_prod : ∀ w : Fin 2 ⊕ Fin 2 → ZMod 2, Qplus4 w = 1 →
    w = va1 ∨ (∃ u, Qplus4 u = 1 ∧ Matrix.mulVec (reflMat Qplus4 u) va1 = w) ∨
      w = Matrix.mulVec gCmat va1 ∨
      ∃ u, Qplus4 u = 1 ∧ Matrix.mulVec (reflMat Qplus4 u) (Matrix.mulVec gCmat va1) = w := by
  decide +kernel

theorem exists_isometry_va1_to {w : Fin 2 ⊕ Fin 2 → ZMod 2} (hw : Qplus4 w = 1) :
    ∃ g : GL (Fin 2 ⊕ Fin 2) (ZMod 2), g ∈ CFSG.MatrixModel.isometryCore Qplus4 ∧
      Matrix.mulVec (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) va1 = w := by
  rcases exists_refl_prod w hw with h | ⟨u, hu, h⟩ | h | ⟨u, hu, h⟩
  · exact ⟨1, Subgroup.one_mem _, by simp [h]⟩
  · exact ⟨reflGL Qplus4 u (refl_sq_of_nonsing u hu),
      reflGL_mem_isometryCore _ _ _ (iso_refl_of_nonsing u hu), h⟩
  · exact ⟨gC, gC_mem, h.symm⟩
  · refine ⟨reflGL Qplus4 u (refl_sq_of_nonsing u hu) * gC,
      Subgroup.mul_mem _ (reflGL_mem_isometryCore _ _ _ (iso_refl_of_nonsing u hu)) gC_mem, ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact h

theorem reflMat_va1_apply : ∀ x : Fin 2 ⊕ Fin 2 → ZMod 2,
    Matrix.mulVec (reflMat Qplus4 va1) x =
      x + (Qplus4 (x + va1) - Qplus4 x - Qplus4 va1) • va1 := by decide +kernel

theorem reflGL_va1_eq : reflGL Qplus4 va1 refl_va1 = reflM (quadPlus 2 (ZMod 2)) va1 := by
  have hw : (quadPlus 2 (ZMod 2)) va1 = 1 := by
    change ⇑(quadPlus 2 (ZMod 2)) va1 = 1
    rw [coe_quadPlus]
    decide
  refine eq_reflM_of_transv hw (fun x => ?_)
  have hpol : polar (quadPlus 2 (ZMod 2)) x va1 = Qplus4 (x + va1) - Qplus4 x - Qplus4 va1 := by
    show ⇑(quadPlus 2 (ZMod 2)) (x + va1) - ⇑(quadPlus 2 (ZMod 2)) x - ⇑(quadPlus 2 (ZMod 2)) va1 = _
    rw [coe_quadPlus]
  rw [hpol]
  exact reflMat_va1_apply x

theorem G42_comm_refl : (G42 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) * reflMat Qplus4 va1 =
    reflMat Qplus4 va1 * (G42 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) := by
  rw [G42_val]
  decide +kernel

theorem iota_comm_refl :
    (iotaGL : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) * reflMat Qplus4 va1 =
      reflMat Qplus4 va1 * (iotaGL : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) := by
  rw [iotaGL_val]
  decide +kernel

theorem iota_sq : (iotaGL : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) * iotaGL = 1 := by
  rw [iotaGL_val]
  decide +kernel

theorem G42_iota_ne : (G42 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) * iotaGL ≠
    iotaGL * (G42 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) := by
  rw [G42_val, iotaGL_val]
  decide +kernel

theorem G42_ne_one : G42 ≠ 1 := by
  intro h
  apply G42_not_mem
  rw [h]
  exact Subgroup.one_mem _

theorem plusTwo_base : ∃ x ∈ StatedOmega ⇑(quadPlus 2 (ZMod 2)) ⊓ Subgroup.centralizer
      ({reflM (quadPlus 2 (ZMod 2)) va1} : Set (GL (Fin 2 ⊕ Fin 2) (ZMod 2))),
    ∃ y ∈ StatedOmega ⇑(quadPlus 2 (ZMod 2)) ⊓ Subgroup.centralizer
      ({reflM (quadPlus 2 (ZMod 2)) va1} : Set (GL (Fin 2 ⊕ Fin 2) (ZMod 2))),
    x ^ 3 = 1 ∧ x ≠ 1 ∧ y ^ 2 = 1 ∧ x * y ≠ y * x := by
  rw [← reflGL_va1_eq, coe_quadPlus]
  refine ⟨G42, ⟨G42_mem, ?_⟩, iotaGL, ⟨iotaGL_mem, ?_⟩, G42_cube, G42_ne_one, ?_, ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.2
      (Units.ext (by rw [Units.val_mul, Units.val_mul]; exact G42_comm_refl))
  · exact Subgroup.mem_centralizer_singleton_iff.2
      (Units.ext (by rw [Units.val_mul, Units.val_mul]; exact iota_comm_refl))
  · rw [pow_two]
    exact Units.ext (by rw [Units.val_mul, Units.val_one]; exact iota_sq)
  · intro h
    exact G42_iota_ne (by simpa only [Units.val_mul] using congrArg Units.val h)

theorem plusTwo_data {w : Fin 2 ⊕ Fin 2 → ZMod 2} (hw : Qplus4 w = 1) :
    ∃ x ∈ StatedOmega ⇑(quadPlus 2 (ZMod 2)) ⊓ Subgroup.centralizer
      ({reflM (quadPlus 2 (ZMod 2)) w} : Set (GL (Fin 2 ⊕ Fin 2) (ZMod 2))),
    ∃ y ∈ StatedOmega ⇑(quadPlus 2 (ZMod 2)) ⊓ Subgroup.centralizer
      ({reflM (quadPlus 2 (ZMod 2)) w} : Set (GL (Fin 2 ⊕ Fin 2) (ZMod 2))),
    x ^ 3 = 1 ∧ x ≠ 1 ∧ y ^ 2 = 1 ∧ x * y ≠ y * x := by
  obtain ⟨g, hg, hgw⟩ := exists_isometry_va1_to hw
  have hQ : ⇑(quadPlus 2 (ZMod 2)) = Qplus4 := coe_quadPlus 2 (ZMod 2)
  have hgQ : g ∈ CFSG.MatrixModel.isometryCore ⇑(quadPlus 2 (ZMod 2)) := by rw [hQ]; exact hg
  have hva : (quadPlus 2 (ZMod 2)) va1 = 1 := by
    change ⇑(quadPlus 2 (ZMod 2)) va1 = 1
    rw [hQ]
    decide
  have hconj := conj_reflM hgQ hva
  rw [hgw] at hconj
  rw [← hconj]
  obtain ⟨x, hx, y, hy, h3, h1, h2, hxy⟩ := plusTwo_base
  have hcomm : ∀ z ∈ StatedOmega ⇑(quadPlus 2 (ZMod 2)) ⊓ Subgroup.centralizer
      ({reflM (quadPlus 2 (ZMod 2)) va1} : Set (GL (Fin 2 ⊕ Fin 2) (ZMod 2))),
      g * z * g⁻¹ ∈ StatedOmega ⇑(quadPlus 2 (ZMod 2)) ⊓ Subgroup.centralizer
        ({g * reflM (quadPlus 2 (ZMod 2)) va1 * g⁻¹} : Set (GL (Fin 2 ⊕ Fin 2) (ZMod 2))) := by
    intro z hz
    refine ⟨conj_mem_statedOmega hgQ hz.1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have := Subgroup.mem_centralizer_singleton_iff.1 hz.2
    calc g * z * g⁻¹ * (g * reflM (quadPlus 2 (ZMod 2)) va1 * g⁻¹)
        = g * (z * reflM (quadPlus 2 (ZMod 2)) va1) * g⁻¹ := by group
      _ = g * (reflM (quadPlus 2 (ZMod 2)) va1 * z) * g⁻¹ := by rw [this]
      _ = g * reflM (quadPlus 2 (ZMod 2)) va1 * g⁻¹ * (g * z * g⁻¹) := by group
  refine ⟨g * x * g⁻¹, hcomm x hx, g * y * g⁻¹, hcomm y hy, ?_, ?_, ?_, ?_⟩
  · rw [conj_pow, h3]
    group
  · intro h
    apply h1
    have := congrArg (fun z => g⁻¹ * z * g) h
    simpa [mul_assoc] using this
  · rw [conj_pow, h2]
    group
  · intro h
    apply hxy
    have e1 : g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
    have e2 : g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
    rw [e1, e2] at h
    exact mul_left_cancel (mul_right_cancel h)

theorem card_eq_six_of_data {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hle : Nat.card H ≤ 6) {x y : G} (hx : x ∈ H) (hy : y ∈ H) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hy2 : y ^ 2 = 1) (hxy : x * y ≠ y * x) : Nat.card H = 6 := by
  have hy1 : y ≠ 1 := fun h => hxy (by rw [h, one_mul, mul_one])
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have h2 : orderOf y = 2 := orderOf_eq_prime hy2 hy1
  have d3 : 3 ∣ Nat.card H := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : H)
    rwa [Subgroup.orderOf_mk, h3] at this
  have d2 : 2 ∣ Nat.card H := by
    have := orderOf_dvd_natCard (⟨y, hy⟩ : H)
    rwa [Subgroup.orderOf_mk, h2] at this
  have d6 : 3 * 2 ∣ Nat.card H := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d3 d2
  have hpos : 0 < Nat.card H := Nat.card_pos
  have := Nat.le_of_dvd hpos d6
  omega

theorem plusTwo_core {Q₀ : (Fin 2 ⊕ Fin 2 → ZMod 2) → ZMod 2} (hQ : ⇑(quadPlus 2 (ZMod 2)) = Q₀)
    {t : GL (Fin 2 ⊕ Fin 2) (ZMod 2)}
    (ht : t ∈ Subgroup.normalizer (StatedOmega Q₀ : Set (GL (Fin 2 ⊕ Fin 2) (ZMod 2))))
    (hQt : ∀ x, Q₀ (Matrix.mulVec (t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) x) = Q₀ x)
    (hT : IsTransvection t) :
    (∀ a : ↥(StatedOmega Q₀), MulAut.conj a ≠ (StatedOmega Q₀).normalizerMonoidHom ⟨t, ht⟩) ∧
      Nonempty (↥(fixSub ((StatedOmega Q₀).normalizerMonoidHom ⟨t, ht⟩)) ≃*
        ↥(StatedSp 1 (ZMod 2))) := by
  subst hQ
  have hnd := nondegenerate_polarBilin_quadPlus 2 (ZMod 2)
  refine ⟨omegaTransv_a hnd hC1_plus_two ht hQt hT, ?_⟩
  obtain ⟨w, hw, hact⟩ := transv_eq_reflect (quadPlus 2 (ZMod 2)) hnd hQt hT
  have htw : t = reflM (quadPlus 2 (ZMod 2)) w := eq_reflM_of_transv hw hact
  subst htw
  obtain ⟨F⟩ := fixSub_equiv_centralizer (Ω := StatedOmega ⇑(quadPlus 2 (ZMod 2))) ht
  have e : (Fin 2 ⊕ Fin 2) ≃ Fin (2 * 2) :=
    Fintype.equivFinOfCardEq (by simp [Fintype.card_sum])
  have hle : Nat.card ↥(StatedOmega ⇑(quadPlus 2 (ZMod 2)) ⊓ Subgroup.centralizer
      ({reflM (quadPlus 2 (ZMod 2)) w} : Set (GL (Fin 2 ⊕ Fin 2) (ZMod 2)))) ≤ 6 := by
    have h := card_centralizer_le e hnd hw
    exact h.trans
      (le_of_eq CFSG.HardMathSupport.RichardWeiss.Proving.PLType.card_statedSp_one_two)
  have hw' : Qplus4 w = 1 := (congrFun (coe_quadPlus 2 (ZMod 2)) w).symm.trans hw
  obtain ⟨x, hx, y, hy, hx3, hx1, hy2, hxy⟩ := plusTwo_data hw'
  have hc6 := card_eq_six_of_data hle hx hy hx3 hx1 hy2 hxy
  obtain ⟨e1⟩ := CFSG.GH74.M12.Hyp.nonempty_mulEquiv_perm_three_of_card_six hc6 ⟨x, hx⟩ ⟨y, hy⟩
    (fun h => hxy (congrArg Subtype.val h))
  obtain ⟨e2⟩ :=
    CFSG.HardMathSupport.RichardWeiss.Proving.PLType.nonempty_statedSp_one_mulEquiv_perm_three
  exact ⟨F.trans (e1.trans e2.symm)⟩

theorem plusTwoTransv_holds : PlusTwoTransv := fun _ ht hQt hT =>
  plusTwo_core (coe_quadPlus 2 (ZMod 2)) ht hQt hT

end PlusTwoGeneral

end PlusTwo

theorem input9_6OmegaTransv_holds : Lemma137b.Input9_6OmegaTransv :=
  input9_6OmegaTransv_of_plusTwo plusTwoTransv_holds

end Instances

open Sec13d

end OmegaFacts

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
