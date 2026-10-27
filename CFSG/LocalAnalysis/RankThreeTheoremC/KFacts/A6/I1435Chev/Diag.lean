module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435Chev.Setup
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossDefs
public import CFSG.Open.StatedDefs
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.SteinbergCBFTCores
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltThreeRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairMaximal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ScalarTorus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Survivor
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ThreeStrong
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3P34Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.Holds
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435Chev

open Subgroup CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis (diagGL coe_diagGL)

theorem Shape.not_elemAbelian81 {K : Type} [Group K] [Finite K] (h : Shape K)
    {E : Subgroup K} (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 4) : False := by
  obtain ⟨e⟩ := h.sylow81 E (IsPGroup.of_card hc) (by rw [hc]; norm_num)
  obtain ⟨a, b, hab⟩ := not_comm_of_mulEquiv_W3 e
  exact hab (hE.1.is_comm.comm a b)

theorem Shape.not_abelian_nine {K : Type} [Group K] [Finite K] (h : Shape K)
    {A : Subgroup K} (hA : IsPGroup 3 A) (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (h27 : 27 ≤ Nat.card A) {a : K} (ha : a ∈ A) (ha3 : a ^ 3 ≠ 1) : False :=
  ha3 (h.abelian_exp A hA hc h27 a ha)

section Torus

variable {L : Type} [Field L] [Finite L]

theorem exists_abelian_nine {ζ : Lˣ} (hζ : orderOf ζ = 9) (H : Subgroup (GL (Fin 3) L))
    (hdiag : ∀ u : Fin 3 → Lˣ, (∀ i, u i ∈ Subgroup.zpowers ζ) → ∏ i, u i = 1 →
      diagGL 3 u ∈ H) :
    ∃ A : Subgroup (StatedProj H), IsPGroup 3 A ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      27 ≤ Nat.card A ∧ ∃ a ∈ A, a ^ 3 ≠ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let E : Multiplicative (ℤ × ℤ) →* (Fin 3 → Lˣ) :=
    MonoidHom.mk' (fun v => ![ζ ^ v.toAdd.1, ζ ^ v.toAdd.2, ζ ^ (-v.toAdd.1 - v.toAdd.2)])
      (fun v w => by
        funext i
        fin_cases i
        · show ζ ^ (v.toAdd.1 + w.toAdd.1) = ζ ^ v.toAdd.1 * ζ ^ w.toAdd.1
          exact zpow_add ζ _ _
        · show ζ ^ (v.toAdd.2 + w.toAdd.2) = ζ ^ v.toAdd.2 * ζ ^ w.toAdd.2
          exact zpow_add ζ _ _
        · show ζ ^ (-(v.toAdd.1 + w.toAdd.1) - (v.toAdd.2 + w.toAdd.2)) =
            ζ ^ (-v.toAdd.1 - v.toAdd.2) * ζ ^ (-w.toAdd.1 - w.toAdd.2)
          rw [← zpow_add]
          congr 1
          ring)
  have hE : ∀ v, diagGL 3 (E v) ∈ H := by
    intro v
    apply hdiag
    · intro i
      fin_cases i
      · exact Subgroup.zpow_mem_zpowers ζ _
      · exact Subgroup.zpow_mem_zpowers ζ _
      · exact Subgroup.zpow_mem_zpowers ζ _
    · rw [Fin.prod_univ_three]
      show ζ ^ v.toAdd.1 * ζ ^ v.toAdd.2 * ζ ^ (-v.toAdd.1 - v.toAdd.2) = 1
      rw [← zpow_add, ← zpow_add, show v.toAdd.1 + v.toAdd.2 + (-v.toAdd.1 - v.toAdd.2) = 0 by
        ring, zpow_zero]
  let θ : Multiplicative (ℤ × ℤ) →* StatedProj H :=
    (QuotientGroup.mk' _).comp (((diagGL 3).comp E).codRestrict H hE)
  have hθ : ∀ v, θ v = QuotientGroup.mk (⟨diagGL 3 (E v), hE v⟩ : H) := fun v => rfl
  have hζz : ∀ m n : ℤ, ζ ^ m = ζ ^ n ↔ m ≡ n [ZMOD 9] := fun m n => by
    rw [zpow_eq_zpow_iff_modEq, hζ]
    rfl
  have hθ1 : ∀ a b : ℤ, θ (Multiplicative.ofAdd (a, b)) = 1 →
      a ≡ b [ZMOD 9] ∧ b ≡ -a - b [ZMOD 9] := by
    intro a b h
    rw [hθ] at h
    obtain ⟨s, hs⟩ := Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h)
    have hs' : (Matrix.GeneralLinearGroup.scalar (Fin 3) s : GL (Fin 3) L) = diagGL 3 (E _) := hs
    have hent : ∀ i : Fin 3, (s : L) = (E (Multiplicative.ofAdd (a, b)) i : L) := by
      intro i
      have := congrArg (fun g : GL (Fin 3) L => (g : Matrix (Fin 3) (Fin 3) L) i i) hs'
      simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_diagGL] using this
    have h01 : ζ ^ a = ζ ^ b := Units.ext ((hent 0).symm.trans (hent 1))
    have h12 : ζ ^ b = ζ ^ (-a - b) := Units.ext ((hent 1).symm.trans (hent 2))
    exact ⟨(hζz a b).1 h01, (hζz b _).1 h12⟩
  refine ⟨θ.range, ?_, ?_, ?_, θ (Multiplicative.ofAdd (1, -1)), ⟨_, rfl⟩, ?_⟩
  · rintro ⟨_, v, rfl⟩
    refine ⟨2, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow]
    obtain ⟨⟨a, b⟩, rfl⟩ : ∃ p : ℤ × ℤ, v = Multiplicative.ofAdd p := ⟨v.toAdd, rfl⟩
    show θ (Multiplicative.ofAdd (9 • (a, b))) = 1
    rw [Prod.smul_mk, nsmul_eq_mul, nsmul_eq_mul, hθ]
    refine (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 ⟨ζ ^ (9 * a), ?_⟩)
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    show Matrix.scalar (Fin 3) ((ζ ^ (9 * a) : Lˣ) : L) = Matrix.diagonal fun i => _
    rw [Matrix.scalar_apply]
    congr 1
    funext i
    have hζ9 : ζ ^ (9 : ℤ) = 1 := by
      rw [show (9 : ℤ) = ((9 : ℕ) : ℤ) from rfl, zpow_natCast, ← hζ, pow_orderOf_eq_one]
    have h9 : ∀ m : ℤ, ζ ^ (9 * m) = 1 := fun m => by
      rw [zpow_mul, hζ9, one_zpow]
    fin_cases i
    · rfl
    · show ((ζ ^ (9 * a) : Lˣ) : L) = ((ζ ^ (9 * b) : Lˣ) : L)
      rw [h9, h9]
    · show ((ζ ^ (9 * a) : Lˣ) : L) = ((ζ ^ (-(9 * a) - 9 * b) : Lˣ) : L)
      rw [h9, show -(9 * a) - 9 * b = 9 * (-a - b) by ring, h9]
  · rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  ·
    let ψ : Fin 9 × Fin 3 → θ.range := fun ij =>
      ⟨θ (Multiplicative.ofAdd ((ij.1 : ℤ), (ij.2 : ℤ))), _, rfl⟩
    have hψ : Function.Injective ψ := by
      rintro ⟨i, j⟩ ⟨i', j'⟩ h
      have h' : θ (Multiplicative.ofAdd ((i : ℤ), (j : ℤ))) =
          θ (Multiplicative.ofAdd ((i' : ℤ), (j' : ℤ))) := congrArg Subtype.val h
      have h1 : θ (Multiplicative.ofAdd ((i : ℤ) - i', (j : ℤ) - j')) = 1 := by
        have : Multiplicative.ofAdd ((i : ℤ) - i', (j : ℤ) - j') =
            Multiplicative.ofAdd ((i : ℤ), (j : ℤ)) *
              (Multiplicative.ofAdd ((i' : ℤ), (j' : ℤ)))⁻¹ := by
          rfl
        rw [this, map_mul, map_inv, h', mul_inv_cancel]
      obtain ⟨hab, hbc⟩ := hθ1 _ _ h1
      have hi := i.2
      have hj := j.2
      have hi' := i'.2
      have hj' := j'.2
      simp only [Int.ModEq] at hab hbc
      have e1 : (i : ℕ) = i' ∧ (j : ℕ) = j' := by omega
      exact Prod.ext (Fin.ext e1.1) (Fin.ext e1.2)
    have := Nat.card_le_card_of_injective ψ hψ
    simpa using this
  ·
    intro h
    rw [← map_pow] at h
    have h' : θ (Multiplicative.ofAdd ((3 : ℤ), (-3 : ℤ))) = 1 := by
      have : (Multiplicative.ofAdd ((1 : ℤ), (-1 : ℤ))) ^ 3 =
          Multiplicative.ofAdd ((3 : ℤ), (-3 : ℤ)) := by rfl
      rwa [this] at h
    obtain ⟨hab, -⟩ := hθ1 _ _ h'
    exact absurd hab (by decide)

end Torus

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435Chev
