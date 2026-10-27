module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphBlock
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LULinear
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearEnd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamField
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

section Param

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {N : ℕ}

structure NsLinParam (hK : Nat.card K = 2) (ε : ℕ) (e : L ≃* StatedSp N K) (k : Fin N) where
  Φ : q2Block ε K {k} →* G
  injective : Function.Injective Φ
  range_eq : Φ.range = centralizerPerfectCore (modelToG e (nsTorusSp K k))
  N1 : ∀ (y : StatedSp N K) (hy : y ∈ spBlock K ({k} : Finset (Fin N))ᶜ),
    Φ ⟨q2Embed ε hK y, (q2Embed_mem_q2Block_iff hK).2 hy⟩ = ((e.symm y : L) : G)

end Param

section Fixed

variable {N ε : ℕ} {K : Type} [Field K]

theorem fixedSubgroup_q2GraphBlock [CharP K 2] (hK : Nat.card K = 2) (hε : ε ≤ 1)
    (R : Finset (Fin N)) : fixedSubgroup (q2GraphBlock ε hK R) = q2SpBlock ε K hK R := by
  ext x
  constructor
  · intro hx
    have hx' : q2Graph ε hK (x : SpecialLinearGroup (Fin (2 * N + ε)) K) = x :=
      congrArg Subtype.val (show q2GraphBlock ε hK R x = x from hx)
    obtain ⟨y, hy⟩ := exists_eq_q2Embed_of_q2Graph_eq hK hε hx'
    refine (mem_q2SpBlock hK).2 ⟨y, (q2Embed_mem_q2Block_iff (ε := ε) hK).1 ?_, hy⟩
    rw [hy]
    exact x.2
  · intro hx
    exact q2GraphBlock_fix hK hx

@[expose] noncomputable def q2SpBlockEquiv (hK : Nat.card K = 2) (R : Finset (Fin N)) :
    spBlock K Rᶜ ≃* q2SpBlock ε K hK R :=
  MulEquiv.ofBijective
    ({ toFun := fun y => ⟨⟨q2Embed (N := N) ε hK (y : StatedSp N K),
          (q2Embed_mem_q2Block_iff hK).2 y.2⟩, (mem_q2SpBlock hK).2 ⟨y, y.2, rfl⟩⟩
       map_one' := Subtype.ext (Subtype.ext (map_one (q2Embed (N := N) ε hK)))
       map_mul' := fun y z => Subtype.ext (Subtype.ext (map_mul (q2Embed (N := N) ε hK)
         (y : StatedSp N K) z)) } :
      spBlock K Rᶜ →* q2SpBlock ε K hK R)
    ⟨fun y z h => Subtype.ext (q2Embed_injective hK
      (congrArg (fun w : q2SpBlock ε K hK R => ((w : q2Block ε K R) :
        SpecialLinearGroup (Fin (2 * N + ε)) K)) h)), fun w => by
      obtain ⟨y, hy, hyw⟩ := (mem_q2SpBlock hK).1 w.2
      exact ⟨⟨y, hy⟩, Subtype.ext (Subtype.ext hyw)⟩⟩

theorem coe_q2SpBlockEquiv (hK : Nat.card K = 2) {R : Finset (Fin N)} (y : spBlock K Rᶜ) :
    (((q2SpBlockEquiv (ε := ε) hK R y : q2SpBlock ε K hK R) : q2Block ε K R) :
      SpecialLinearGroup (Fin (2 * N + ε)) K) = q2Embed ε hK y := rfl

theorem lieModel_fixedSubgroup_q2GraphBlock [CharP K 2] (hK : Nat.card K = 2) (hε : ε ≤ 1)
    {m : ℕ} (hm : 3 ≤ m) (k : Fin (m + 1)) :
    LieModel (fixedSubgroup (q2GraphBlock ε hK ({k} : Finset (Fin (m + 1))))) .PSp m 2 1 := by
  have e1 : fixedSubgroup (q2GraphBlock ε hK ({k} : Finset (Fin (m + 1)))) ≃*
      StatedSp m K :=
    ((MulEquiv.subgroupCongr (fixedSubgroup_q2GraphBlock hK hε _)).trans
      (q2SpBlockEquiv hK _).symm).trans (blockComplEquiv K k)
  exact lieModel_of_mulEquiv_statedSp e1 (by rw [hK, pow_one]) (by omega)
    (fun h => by have := congrArg Prod.fst h; simp only at this; omega)

end Fixed

section Conj

variable {N ε : ℕ} {K : Type} [Field K]

theorem exists_normalForm_of_lieModel_PSp (hε : ε ≤ 1) {m : ℕ}
    (hm : 3 ≤ m) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    {μ : MulAut (LinearFlag.projectiveSL (2 * m + ε) F)} (hμμ : μ * μ = 1)
    (hμo : μ ∉ (MulAut.conj : LinearFlag.projectiveSL (2 * m + ε) F →* MulAut _).range)
    (hμfix : LieModel (fixedSubgroup μ) .PSp m 2 1) :
    ∃ H C : GL (Fin (2 * m + ε)) F,
      ((ε = 0 ∧ (C : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) F) =
          UnitaryHigher.blockSwapJ (2 * m + ε) m) ∨
        (ε = 1 ∧ (C : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) F) = 1)) ∧
      μ = LinearFlag.conjAut (2 * m + ε) F H *
        (LinearFlag.conjAut (2 * m + ε) F C * LinearFlag.dualAut (2 * m + ε) F) *
          (LinearFlag.conjAut (2 * m + ε) F H)⁻¹ := by
  have hF' : Nat.card F = 2 ^ 1 := by rw [hF, pow_one]
  have hμ2 : μ ^ 2 = 1 := by rw [sq]; exact hμμ
  have hμE := not_mem_semilinearAutGroup_of_lieModel_PSp (by omega) le_rfl hF' hμ2 hμo hμfix
  obtain ⟨H, C, hC, hμHC⟩ := exists_conjAut_dualAut_normalForm (by omega) le_rfl hF' hμ2 hμE hμfix
  refine ⟨H, C, ?_, hμHC⟩
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    rcases hC with h1 | ⟨r', hr', hJ⟩
    · exfalso
      have hfix' : LieModel (fixedSubgroup (LinearFlag.conjAut (2 * m + 0) F C *
          LinearFlag.dualAut (2 * m + 0) F)) .PSp m 2 1 := by
        have hcon : MulAut.congr (LinearFlag.conjAut (2 * m + 0) F H)⁻¹ μ =
            LinearFlag.conjAut (2 * m + 0) F C * LinearFlag.dualAut (2 * m + 0) F := by
          rw [hμHC, LinearPilot.mulAut_congr_eq_mul]
          group
        rw [← hcon]
        exact LieType.CurtisTits.lieModel_of_mulEquiv
          (CFSG.ComponentClassification.CatLeafProof.fixedSubgroupCongrEquiv _ μ) hμfix
      exact not_lieModel_PSp_fixedSubgroup_dualAut_one le_rfl hF' (by omega)
        ⟨m, by omega⟩ h1 hfix'
    · obtain rfl : r' = m := by omega
      exact hJ
  · right
    refine ⟨rfl, ?_⟩
    rcases hC with h1 | ⟨r', hr', -⟩
    · exact h1
    · omega

theorem exists_eq_mul_q2GraphBlock_mul_inv [CharP K 2]
    (hK : Nat.card K = 2) (hε : ε ≤ 1) {m : ℕ} (hm : 3 ≤ m) (k : Fin (m + 1)) {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = 2)
    (χ : q2Block ε K ({k} : Finset (Fin (m + 1))) ≃* LinearFlag.projectiveSL (2 * m + ε) F)
    {α : MulAut (q2Block ε K ({k} : Finset (Fin (m + 1))))} (hαα : α * α = 1)
    (hαo : α ∉ (MulAut.conj : q2Block ε K ({k} : Finset (Fin (m + 1))) →* MulAut _).range)
    (hαfix : LieModel (fixedSubgroup α) .PSp m 2 1) :
    ∃ β : MulAut (q2Block ε K ({k} : Finset (Fin (m + 1)))),
      α = β * q2GraphBlock ε hK {k} * β⁻¹ := by
  obtain ⟨p, hp⟩ : ∃ p : Fin (m + 1), p ≠ k := ⟨if k = 0 then 1 else 0, by
    split_ifs with h
    · rw [h]; exact Fin.ne_of_val_ne (by simp; omega)
    · exact Ne.symm h⟩
  obtain ⟨p', hp'k, hp'p⟩ : ∃ p' : Fin (m + 1), p' ≠ k ∧ p' ≠ p := by
    obtain ⟨p', hp'⟩ := exists_ne_ne_of_three_le (by omega : 3 ≤ m + 1) k p
    exact ⟨p', hp'.1, hp'.2⟩
  have hγγ : q2GraphBlock ε hK ({k} : Finset (Fin (m + 1))) * q2GraphBlock ε hK {k} = 1 := by
    ext1 x
    apply Subtype.ext
    rw [MulAut.mul_apply, MulAut.one_apply, coe_q2GraphBlock, coe_q2GraphBlock,
      ← MulAut.mul_apply, q2Graph_mul_self, MulAut.one_apply]
  have hγo := q2GraphBlock_not_mem_inner (R := ({k} : Finset (Fin (m + 1)))) hK hε
    (Ne.symm hp'p) (by simpa using hp) (by simpa using hp'k)
  have hγfix := lieModel_fixedSubgroup_q2GraphBlock hK hε hm k (ε := ε)
  have htr : ∀ μ : MulAut (q2Block ε K ({k} : Finset (Fin (m + 1)))), μ * μ = 1 →
      μ ∉ (MulAut.conj : q2Block ε K ({k} : Finset (Fin (m + 1))) →* MulAut _).range →
      LieModel (fixedSubgroup μ) .PSp m 2 1 →
      ∃ H C : GL (Fin (2 * m + ε)) F,
        ((ε = 0 ∧ (C : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) F) =
            CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ (2 * m + ε) m) ∨
          (ε = 1 ∧ (C : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) F) = 1)) ∧
        MulAut.congr χ μ = LinearFlag.conjAut (2 * m + ε) F H *
          (LinearFlag.conjAut (2 * m + ε) F C * LinearFlag.dualAut (2 * m + ε) F) *
            (LinearFlag.conjAut (2 * m + ε) F H)⁻¹ := by
    intro μ hμμ hμo hμfix
    refine exists_normalForm_of_lieModel_PSp hε hm hF (by rw [← map_mul, hμμ, map_one])
      (fun h => hμo ((FixedFourGroup.congr_mem_inner_iff χ μ).1 h)) ?_
    exact LieType.CurtisTits.lieModel_of_mulEquiv
      (CFSG.ComponentClassification.CatLeafProof.fixedSubgroupCongrEquiv χ μ) hμfix
  obtain ⟨H₁, C₁, hC₁, h₁⟩ := htr α hαα hαo hαfix
  obtain ⟨H₂, C₂, hC₂, h₂⟩ := htr _ hγγ hγo hγfix
  have hC : C₁ = C₂ := by
    apply Units.ext
    rcases hC₁ with ⟨e1, h1⟩ | ⟨e1, h1⟩ <;> rcases hC₂ with ⟨e2, h2⟩ | ⟨e2, h2⟩
    · rw [h1, h2]
    · omega
    · omega
    · rw [h1, h2]
  subst hC
  set β' : MulAut (LinearFlag.projectiveSL (2 * m + ε) F) :=
    LinearFlag.conjAut (2 * m + ε) F H₁ * (LinearFlag.conjAut (2 * m + ε) F H₂)⁻¹ with hβ'
  refine ⟨(MulAut.congr χ).symm β', (MulAut.congr χ).injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h₁, h₂, hβ']
  group

end Conj

end CFSG.SeitzReduction.SymplecticPilot
