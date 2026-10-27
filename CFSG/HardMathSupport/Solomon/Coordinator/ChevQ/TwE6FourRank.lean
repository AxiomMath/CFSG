module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6Four
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutRank
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.SL2Pair
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
public import CFSG.RankThree.PartTwo.Census.Exceptional.TwistedE6

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open
open scoped MatrixGroups Matrix
open TauCeti CFSG.TauCetiBridge CFSG.RankThree.PartTwo.Census.Exceptional
  CFSG.RankThree.PartTwo.Census CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth (c3 u1 c3_pow_three c3_ne_one c3_pow_commute_u1)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
  (orderThreeHom pow_three_eq_one_of_multiplicative_zmod)

namespace TwE6FourRankAux

section Char2

variable {F : Type} [Field F] [Finite F]

theorem two_eq_zero_of_natCard (h4 : Nat.card F = 4) : (2 : F) = 0 := by
  have h1 : addOrderOf (1 : F) ∣ 4 := by
    have := addOrderOf_dvd_natCard (1 : F)
    rwa [h4] at this
  have h2 : (4 : ℕ) • (1 : F) = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.1 h1
  have h3 : (4 : F) = 0 := by simpa using h2
  have h5 : (2 : F) * 2 = 0 := by rw [← h3]; norm_num
  exact mul_self_eq_zero.1 h5

theorem exists_sq_add_add_one (h4 : Nat.card F = 4) : ∃ w : F, w ≠ 0 ∧ w ^ 2 + w + 1 = 0 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card]; exact h4
  have hs : ({0, 1} : Finset F).card < (Finset.univ : Finset F).card := by
    rw [Finset.card_univ, hcard]
    exact lt_of_le_of_lt Finset.card_le_two (by norm_num)
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hs
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  obtain ⟨hx0, hx1⟩ := hx
  have h4x : x ^ 4 = x := by
    have := FiniteField.pow_card x
    rwa [hcard] at this
  have h3 : x ^ 3 = 1 := by
    have h : x * (x ^ 3 - 1) = 0 := by linear_combination h4x
    rcases mul_eq_zero.1 h with h' | h'
    · exact absurd h' hx0
    · exact sub_eq_zero.1 h'
  have hq : (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.1 hq with h' | h'
  · exact absurd (sub_eq_zero.1 h') hx1
  · exact ⟨x, hx0, h'⟩

end Char2

section SL2

variable {F : Type} [Field F]

@[expose] def vecV (w : F) : Fin 2 → F := ![1, w]

@[expose] def stabV (w : F) : Subgroup SL(2, F) where
  carrier := {x | (x : Matrix (Fin 2) (Fin 2) F) *ᵥ vecV w = vecV w}
  mul_mem' := fun {a b} ha hb => by
    change (a : Matrix (Fin 2) (Fin 2) F) *ᵥ vecV w = vecV w at ha
    change (b : Matrix (Fin 2) (Fin 2) F) *ᵥ vecV w = vecV w at hb
    change ((a * b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ vecV w = vecV w
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hb, ha]
  one_mem' := by
    change ((1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ vecV w = vecV w
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  inv_mem' := fun {a} ha => by
    change (a : Matrix (Fin 2) (Fin 2) F) *ᵥ vecV w = vecV w at ha
    change ((a⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ vecV w = vecV w
    have key : ((a⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ
        ((a : Matrix (Fin 2) (Fin 2) F) *ᵥ vecV w) = vecV w := by
      rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    rwa [ha] at key

theorem mem_stabV {w : F} {x : SL(2, F)} :
    x ∈ stabV w ↔ (x : Matrix (Fin 2) (Fin 2) F) *ᵥ vecV w = vecV w := Iff.rfl

theorem mul_self_of_mulVec_eq {M : Matrix (Fin 2) (Fin 2) F} (h2 : (2 : F) = 0) {w : F}
    (hdet : M.det = 1) (hv : M *ᵥ vecV w = vecV w) : M * M = 1 := by
  rw [Matrix.det_fin_two] at hdet
  have E1 := congrFun hv 0
  have E2 := congrFun hv 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, vecV] at E1 E2
  have hT : M 0 0 + M 1 1 = 2 := by
    linear_combination (1 - M 1 1) * E1 + M 0 1 * E2 + hdet
  have hd : M 1 1 = M 0 0 := by linear_combination hT + (1 - M 0 0) * h2
  have e00 : M 0 0 * M 0 0 + M 0 1 * M 1 0 = 1 := by
    linear_combination (-1 : F) * hdet + M 0 0 * hT + (M 0 0 - 1) * h2
  have e01 : M 0 0 * M 0 1 + M 0 1 * M 1 1 = 0 := by
    linear_combination M 0 1 * hT + M 0 1 * h2
  have e10 : M 1 0 * M 0 0 + M 1 1 * M 1 0 = 0 := by
    linear_combination M 1 0 * hT + M 1 0 * h2
  have e11 : M 1 0 * M 0 1 + M 1 1 * M 1 1 = 1 := by
    linear_combination (M 1 1 + M 0 0) * hd + (-1 : F) * hdet + M 0 0 * hT + (M 0 0 - 1) * h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · exact e00
  · exact e01
  · exact e10
  · exact e11

theorem sq_eq_one_of_mem_stabV (h2 : (2 : F) = 0) {w : F} {x : SL(2, F)} (hx : x ∈ stabV w) :
    x * x = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  exact mul_self_of_mulVec_eq h2 (Matrix.SpecialLinearGroup.det_coe x) (mem_stabV.1 hx)

theorem mulVec_inv_eq {w μ : F} (hμ : μ ≠ 0) {g : SL(2, F)}
    (hg : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ vecV w = μ • vecV w) :
    ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ vecV w = μ⁻¹ • vecV w := by
  have hinv : ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h1 : ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ (μ • vecV w) = vecV w := by
    rw [← hg, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  rw [Matrix.mulVec_smul] at h1
  calc ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ vecV w
      = μ⁻¹ • (μ • ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ vecV w) := by
        rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
    _ = μ⁻¹ • vecV w := by rw [h1]

theorem conj_mem_stabV {w μ : F} (hμ : μ ≠ 0) {g : SL(2, F)}
    (hg : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ vecV w = μ • vecV w) {x : SL(2, F)}
    (hx : x ∈ stabV w) : g * x * g⁻¹ ∈ stabV w := by
  have hx' := mem_stabV.1 hx
  have hgi := mulVec_inv_eq hμ hg
  refine mem_stabV.2 ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgi, Matrix.mulVec_smul, hx',
    Matrix.mulVec_smul, hg, smul_smul, inv_mul_cancel₀ hμ, one_smul]

theorem c3_mulVec {w : F} (h2 : (2 : F) = 0) (hw : w ^ 2 + w + 1 = 0) :
    ((c3 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ vecV w = w • vecV w := by
  have hc : ((c3 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, -1] := rfl
  have hv : ((c3 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ vecV w = ![-w, 1 - w] := by
    rw [hc]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, vecV] <;> ring
  rw [hv]
  ext i
  fin_cases i
  · show -w = w * 1
    linear_combination (-w) * h2
  · show 1 - w = w * w
    linear_combination (-1 : F) * hw + h2

@[expose] def transv (h2 : (2 : F) = 0) (w : F) : SL(2, F) :=
  ⟨!![1 + w, 1; w ^ 2, 1 + w], by rw [Matrix.det_fin_two_of]; linear_combination w * h2⟩

theorem transv_mem (h2 : (2 : F) = 0) (w : F) : transv h2 w ∈ stabV w := by
  refine mem_stabV.2 ?_
  have hc : ((transv h2 w : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      !![1 + w, 1; w ^ 2, 1 + w] := rfl
  have hv : ((transv h2 w : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ vecV w =
      ![1 + 2 * w, w ^ 2 + (1 + w) * w] := by
    rw [hc]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, vecV] <;> ring
  rw [hv]
  ext i
  fin_cases i
  · show 1 + 2 * w = 1
    linear_combination w * h2
  · show w ^ 2 + (1 + w) * w = w
    linear_combination w ^ 2 * h2

theorem transv_ne_one (h2 : (2 : F) = 0) (w : F) : transv h2 w ≠ 1 := by
  intro h
  have h01 := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [transv] at h01

theorem mem_normalizer_map {S : Type} [Group S] {ψ : SL(2, F) →* S}
    (hψ : Function.Injective ψ) {w μ : F} (hμ : μ ≠ 0) {g : SL(2, F)}
    (hg : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ vecV w = μ • vecV w) :
    ψ g ∈ Subgroup.normalizer (((stabV w).map ψ : Subgroup S) : Set S) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hh
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map.2 ⟨g * y * g⁻¹, conj_mem_stabV hμ hg hy, rfl⟩
  · intro hh
    obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.1 hh
    refine Subgroup.mem_map.2 ⟨g⁻¹ * z * g, ?_, ?_⟩
    · have := conj_mem_stabV (inv_ne_zero hμ) (mulVec_inv_eq hμ hg) hz
      rwa [inv_inv] at this
    · rw [map_mul, map_mul, map_inv, hzeq]
      group

end SL2

theorem mem_normalizer_of_commute {S : Type} [Group S] (U : Subgroup S) {g : S}
    (hg : ∀ u ∈ U, Commute g u) : g ∈ Subgroup.normalizer (U : Set S) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have e : g * h * g⁻¹ = h := by rw [(hg h hh).eq, mul_inv_cancel_right]
    rw [e]
    exact hh
  · intro hh
    have hc := (hg _ hh).eq
    have e1 : h = g⁻¹ * (g * h * g⁻¹) * g := by group
    have e2 : g⁻¹ * (g * h * g⁻¹) * g = g * h * g⁻¹ := by
      calc g⁻¹ * (g * h * g⁻¹) * g = g⁻¹ * ((g * h * g⁻¹) * g) := by group
        _ = g⁻¹ * (g * (g * h * g⁻¹)) := by rw [hc]
        _ = g * h * g⁻¹ := by group
    have e : h = g * h * g⁻¹ := e1.trans e2
    rw [e]
    exact hh

section Four

variable {G : Type} [Group G]

theorem card_multiplicative_zmod_three : Nat.card (Multiplicative (ZMod 3)) = 3 := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 3) ≃ ZMod 3), Nat.card_zmod]

noncomputable def fourHom (x₁ x₂ x₃ x₄ : G) (h₁ : x₁ ^ 3 = 1) (h₂ : x₂ ^ 3 = 1)
    (h₃ : x₃ ^ 3 = 1) (h₄ : x₄ ^ 3 = 1) (c₁₂ : Commute x₁ x₂) (c₁₃ : Commute x₁ x₃)
    (c₁₄ : Commute x₁ x₄) (c₂₃ : Commute x₂ x₃) (c₂₄ : Commute x₂ x₄) (c₃₄ : Commute x₃ x₄) :
    (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) ×
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) →* G :=
  let φ₁ := orderThreeHom x₁ h₁
  let φ₂ := orderThreeHom x₂ h₂
  let φ₃ := orderThreeHom x₃ h₃
  let φ₄ := orderThreeHom x₄ h₄
  let k₁₂ : ∀ s t : Multiplicative (ZMod 3), Commute (φ₁ s) (φ₂ t) := fun s t => c₁₂.pow_pow _ _
  let k₃₄ : ∀ s t : Multiplicative (ZMod 3), Commute (φ₃ s) (φ₄ t) := fun s t => c₃₄.pow_pow _ _
  let ψ₁ := φ₁.noncommCoprod φ₂ k₁₂
  let ψ₂ := φ₃.noncommCoprod φ₄ k₃₄
  have kk : ∀ s t : Multiplicative (ZMod 3) × Multiplicative (ZMod 3),
      Commute (ψ₁ s) (ψ₂ t) := by
    intro s t
    rw [MonoidHom.noncommCoprod_apply, MonoidHom.noncommCoprod_apply]
    exact ((c₁₃.pow_pow _ _).mul_right (c₁₄.pow_pow _ _)).mul_left
      ((c₂₃.pow_pow _ _).mul_right (c₂₄.pow_pow _ _))
  ψ₁.noncommCoprod ψ₂ kk

theorem fourHom_apply (x₁ x₂ x₃ x₄ : G) (h₁ : x₁ ^ 3 = 1) (h₂ : x₂ ^ 3 = 1)
    (h₃ : x₃ ^ 3 = 1) (h₄ : x₄ ^ 3 = 1) (c₁₂ : Commute x₁ x₂) (c₁₃ : Commute x₁ x₃)
    (c₁₄ : Commute x₁ x₄) (c₂₃ : Commute x₂ x₃) (c₂₄ : Commute x₂ x₄) (c₃₄ : Commute x₃ x₄)
    (s : (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) ×
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) :
    fourHom x₁ x₂ x₃ x₄ h₁ h₂ h₃ h₄ c₁₂ c₁₃ c₁₄ c₂₃ c₂₄ c₃₄ s =
      x₁ ^ (Multiplicative.toAdd s.1.1).val * x₂ ^ (Multiplicative.toAdd s.1.2).val *
        x₃ ^ (Multiplicative.toAdd s.2.1).val * x₄ ^ (Multiplicative.toAdd s.2.2).val := by
  obtain ⟨⟨s₁, s₂⟩, ⟨s₃, s₄⟩⟩ := s
  show (x₁ ^ (Multiplicative.toAdd s₁).val * x₂ ^ (Multiplicative.toAdd s₂).val) *
      (x₃ ^ (Multiplicative.toAdd s₃).val * x₄ ^ (Multiplicative.toAdd s₄).val) = _
  simp only [mul_assoc]

theorem fourHom_injective (x₁ x₂ x₃ x₄ : G) (h₁ : x₁ ^ 3 = 1) (h₂ : x₂ ^ 3 = 1)
    (h₃ : x₃ ^ 3 = 1) (h₄ : x₄ ^ 3 = 1) (c₁₂ : Commute x₁ x₂) (c₁₃ : Commute x₁ x₃)
    (c₁₄ : Commute x₁ x₄) (c₂₃ : Commute x₂ x₃) (c₂₄ : Commute x₂ x₄) (c₃₄ : Commute x₃ x₄)
    (hind : ∀ a b c d : ℕ, x₁ ^ a * x₂ ^ b * x₃ ^ c * x₄ ^ d = 1 →
      3 ∣ a ∧ 3 ∣ b ∧ 3 ∣ c ∧ 3 ∣ d) :
    Function.Injective (fourHom x₁ x₂ x₃ x₄ h₁ h₂ h₃ h₄ c₁₂ c₁₃ c₁₄ c₂₃ c₂₄ c₃₄) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨⟨s₁, s₂⟩, ⟨s₃, s₄⟩⟩ hs
  rw [fourHom_apply] at hs
  obtain ⟨ha, hb, hc, hd⟩ := hind _ _ _ _ hs
  have hz : ∀ s : Multiplicative (ZMod 3), 3 ∣ (Multiplicative.toAdd s).val → s = 1 := by
    intro s hs'
    have h3 := ZMod.val_lt (Multiplicative.toAdd s)
    have h0 : (Multiplicative.toAdd s).val = 0 := by omega
    exact Multiplicative.toAdd.injective ((ZMod.val_eq_zero _).1 h0)
  exact Prod.ext (Prod.ext (hz _ ha) (hz _ hb)) (Prod.ext (hz _ hc) (hz _ hd))

theorem four_range_facts (x₁ x₂ x₃ x₄ : G) (h₁ : x₁ ^ 3 = 1) (h₂ : x₂ ^ 3 = 1)
    (h₃ : x₃ ^ 3 = 1) (h₄ : x₄ ^ 3 = 1) (c₁₂ : Commute x₁ x₂) (c₁₃ : Commute x₁ x₃)
    (c₁₄ : Commute x₁ x₄) (c₂₃ : Commute x₂ x₃) (c₂₄ : Commute x₂ x₄) (c₃₄ : Commute x₃ x₄)
    (hind : ∀ a b c d : ℕ, x₁ ^ a * x₂ ^ b * x₃ ^ c * x₄ ^ d = 1 →
      3 ∣ a ∧ 3 ∣ b ∧ 3 ∣ c ∧ 3 ∣ d) :
    ∃ A : Subgroup G, IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 4 ∧
      ∀ a ∈ A, ∃ n₁ n₂ n₃ n₄ : ℕ, a = x₁ ^ n₁ * x₂ ^ n₂ * x₃ ^ n₃ * x₄ ^ n₄ := by
  have hinj := fourHom_injective x₁ x₂ x₃ x₄ h₁ h₂ h₃ h₄ c₁₂ c₁₃ c₁₄ c₂₃ c₂₄ c₃₄ hind
  refine ⟨(fourHom x₁ x₂ x₃ x₄ h₁ h₂ h₃ h₄ c₁₂ c₁₃ c₁₄ c₂₃ c₂₄ c₃₄).range, ?_, ?_, ?_⟩
  · refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨s, hs⟩ := MonoidHom.mem_range.1 a.2
      obtain ⟨t, ht⟩ := MonoidHom.mem_range.1 b.2
      change (a : G) * (b : G) = (b : G) * (a : G)
      rw [← hs, ← ht, ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨s, rfl⟩ := MonoidHom.mem_range.1 hx
      have hs3 : s ^ 3 = 1 :=
        Prod.ext (Prod.ext (pow_three_eq_one_of_multiplicative_zmod _)
          (pow_three_eq_one_of_multiplicative_zmod _))
          (Prod.ext (pow_three_eq_one_of_multiplicative_zmod _)
          (pow_three_eq_one_of_multiplicative_zmod _))
      rw [← map_pow, hs3, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    simp only [Nat.card_prod, card_multiplicative_zmod_three]
    norm_num
  · intro a ha
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.1 ha
    exact ⟨_, _, _, _, fourHom_apply x₁ x₂ x₃ x₄ h₁ h₂ h₃ h₄ c₁₂ c₁₃ c₁₄ c₂₃ c₂₄ c₃₄ s⟩

end Four

section Indep

variable {X : Type} [Group X]

theorem exponent_eq_of_commute_u1 {K : Type} [Field K] {φ : SL(2, K) →* X}
    (hφ : Function.Injective φ) {n : ℕ} {y : X} (hy : ∀ B : SL(2, K), Commute y (φ B))
    (hn : φ c3 ^ n = y) : 3 ∣ n := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : Commute (φ (c3 ^ n)) (φ u1) := by
    rw [map_pow, hn]
    exact hy u1
  have h2 : Commute ((c3 : SL(2, K)) ^ n) u1 := by
    refine (?_ : (c3 : SL(2, K)) ^ n * u1 = u1 * (c3 : SL(2, K)) ^ n)
    apply hφ
    rw [map_mul, map_mul]
    exact h1.eq
  have h3 := c3_pow_commute_u1 h2
  rw [← orderOf_eq_prime (c3_pow_three (K := K)) (c3_ne_one (K := K))]
  exact orderOf_dvd_of_pow_eq_one h3

theorem indep_four {K : Type} [Field K] {φ : Fin 4 → SL(2, K) →* X}
    (hφ : ∀ i, Function.Injective (φ i))
    (hc : ∀ i j, i ≠ j → ∀ A B, Commute (φ i A) (φ j B)) :
    ∀ a b c d : ℕ, φ 0 c3 ^ a * φ 1 c3 ^ b * φ 2 c3 ^ c * φ 3 c3 ^ d = 1 →
      3 ∣ a ∧ 3 ∣ b ∧ 3 ∣ c ∧ 3 ∣ d := by
  have hp : ∀ i j, i ≠ j → ∀ (n : ℕ) (B : SL(2, K)), Commute (φ i c3 ^ n) (φ j B) :=
    fun i j hij n B => (hc i j hij c3 B).pow_left n
  have hone : ∀ (i : Fin 4) (n : ℕ), 3 ∣ n → φ i c3 ^ n = 1 := by
    intro i n hn
    obtain ⟨k, rfl⟩ := hn
    rw [pow_mul, ← map_pow, c3_pow_three, map_one, one_pow]
  intro a b c d h
  have ha : 3 ∣ a := exponent_eq_of_commute_u1 (hφ 0)
    (y := (φ 1 c3 ^ b * φ 2 c3 ^ c * φ 3 c3 ^ d)⁻¹)
    (fun B => Commute.inv_left (((hp 1 0 (by decide) b B).mul_left
      (hp 2 0 (by decide) c B)).mul_left (hp 3 0 (by decide) d B)))
    (by
      refine eq_inv_of_mul_eq_one_left ?_
      simpa [mul_assoc] using h)
  rw [hone 0 a ha, one_mul] at h
  have hb : 3 ∣ b := exponent_eq_of_commute_u1 (hφ 1)
    (y := (φ 2 c3 ^ c * φ 3 c3 ^ d)⁻¹)
    (fun B => Commute.inv_left ((hp 2 1 (by decide) c B).mul_left (hp 3 1 (by decide) d B)))
    (by
      refine eq_inv_of_mul_eq_one_left ?_
      simpa [mul_assoc] using h)
  rw [hone 1 b hb, one_mul] at h
  have hc' : 3 ∣ c := exponent_eq_of_commute_u1 (hφ 2)
    (y := (φ 3 c3 ^ d)⁻¹)
    (fun B => Commute.inv_left (hp 3 2 (by decide) d B))
    (by
      refine eq_inv_of_mul_eq_one_left ?_
      simpa [mul_assoc] using h)
  rw [hone 2 c hc', one_mul] at h
  have hd : 3 ∣ d := exponent_eq_of_commute_u1 (hφ 3) (y := 1)
    (fun B => Commute.one_left _) (by simpa using h)
  exact ⟨ha, hb, hc', hd⟩

theorem central_step {K : Type} [Field K] {φ : SL(2, K) →* X}
    (hφ : Function.Injective φ) {a R : X} {n : ℕ} (hcen : ∀ x : X, a * x = x * a)
    (hR : ∀ B : SL(2, K), Commute R (φ B)) (ha : a = φ c3 ^ n * R) : a = R := by
  have hac : ∀ B : SL(2, K), Commute a (φ B) := fun B => hcen (φ B)
  have h3 : 3 ∣ n := exponent_eq_of_commute_u1 hφ (y := a * R⁻¹)
    (fun B => Commute.mul_left (hac B) (hR B).inv_left)
    (by rw [ha, mul_inv_cancel_right])
  obtain ⟨k, rfl⟩ := h3
  have h1 : φ c3 ^ (3 * k) = 1 := by
    rw [pow_mul, ← map_pow, c3_pow_three, map_one, one_pow]
  rw [h1, one_mul] at ha
  exact ha

end Indep

theorem partI_of_four {F : Type} [Field F] {S : Type} [Group S]
    (h2 : (2 : F) = 0) {w : F} (hw0 : w ≠ 0) (hw : w ^ 2 + w + 1 = 0)
    (ψ : Fin 4 → SL(2, F) →* S) (hψ : ∀ i, Function.Injective (ψ i))
    (hc : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) :
    ∃ A U : Subgroup S, IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 4 ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      A ≤ Subgroup.normalizer (U : Set S) ∧ (∀ a ∈ A, (∀ x : S, a * x = x * a) → a = 1) := by
  have hx3 : ∀ i, ψ i c3 ^ 3 = 1 := fun i => by rw [← map_pow, c3_pow_three, map_one]
  have hcc : ∀ i j, i ≠ j → Commute (ψ i c3) (ψ j c3) := fun i j hij => hc i j hij c3 c3
  have hp : ∀ i j, i ≠ j → ∀ (n : ℕ) (B : SL(2, F)), Commute (ψ i c3 ^ n) (ψ j B) :=
    fun i j hij n B => (hc i j hij c3 B).pow_left n
  have hind := indep_four hψ hc
  obtain ⟨A, hAel, hAcard, hAform⟩ := four_range_facts (ψ 0 c3) (ψ 1 c3) (ψ 2 c3) (ψ 3 c3)
    (hx3 0) (hx3 1) (hx3 2) (hx3 3) (hcc 0 1 (by decide)) (hcc 0 2 (by decide))
    (hcc 0 3 (by decide)) (hcc 1 2 (by decide)) (hcc 1 3 (by decide)) (hcc 2 3 (by decide)) hind
  have hN0 : ψ 0 c3 ∈ Subgroup.normalizer (((stabV w).map (ψ 0) : Subgroup S) : Set S) :=
    mem_normalizer_map (hψ 0) hw0 (c3_mulVec h2 hw)
  have hN1 : ψ 1 c3 ∈ Subgroup.normalizer (((stabV w).map (ψ 0) : Subgroup S) : Set S) :=
    mem_normalizer_of_commute _ fun u hu => by
      obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hu
      exact hc 1 0 (by decide) c3 y
  have hN2 : ψ 2 c3 ∈ Subgroup.normalizer (((stabV w).map (ψ 0) : Subgroup S) : Set S) :=
    mem_normalizer_of_commute _ fun u hu => by
      obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hu
      exact hc 2 0 (by decide) c3 y
  have hN3 : ψ 3 c3 ∈ Subgroup.normalizer (((stabV w).map (ψ 0) : Subgroup S) : Set S) :=
    mem_normalizer_of_commute _ fun u hu => by
      obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hu
      exact hc 3 0 (by decide) c3 y
  refine ⟨A, (stabV w).map (ψ 0), hAel, hAcard, ?_, ?_, ?_, ?_⟩
  · intro hbot
    have hmem : ψ 0 (transv h2 w) ∈ (stabV w).map (ψ 0) :=
      Subgroup.mem_map.2 ⟨transv h2 w, transv_mem h2 w, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact transv_ne_one h2 w (hψ 0 (hmem.trans (map_one (ψ 0)).symm))
  · intro g
    obtain ⟨u, hu, hug⟩ := Subgroup.mem_map.1 g.2
    refine ⟨1, Subtype.ext ?_⟩
    have hu2 : u ^ 2 = 1 := by rw [sq]; exact sq_eq_one_of_mem_stabV h2 hu
    have hg2 : (g : S) ^ 2 = 1 := by rw [← hug, ← map_pow, hu2, map_one]
    simpa using hg2
  · intro a ha
    obtain ⟨n0, n1, n2, n3, rfl⟩ := hAform a ha
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.pow_mem _ hN0 n0) (Subgroup.pow_mem _ hN1 n1)) (Subgroup.pow_mem _ hN2 n2))
      (Subgroup.pow_mem _ hN3 n3)
  · intro a ha hcen
    obtain ⟨n0, n1, n2, n3, rfl⟩ := hAform a ha
    have hR0 : ∀ B : SL(2, F), Commute (ψ 1 c3 ^ n1 * ψ 2 c3 ^ n2 * ψ 3 c3 ^ n3) (ψ 0 B) :=
      fun B => ((hp 1 0 (by decide) n1 B).mul_left (hp 2 0 (by decide) n2 B)).mul_left
        (hp 3 0 (by decide) n3 B)
    have hR1 : ∀ B : SL(2, F), Commute (ψ 2 c3 ^ n2 * ψ 3 c3 ^ n3) (ψ 1 B) :=
      fun B => (hp 2 1 (by decide) n2 B).mul_left (hp 3 1 (by decide) n3 B)
    have hR2 : ∀ B : SL(2, F), Commute (ψ 3 c3 ^ n3) (ψ 2 B) :=
      fun B => hp 3 2 (by decide) n3 B
    have hR3 : ∀ B : SL(2, F), Commute (1 : S) (ψ 3 B) := fun B => Commute.one_left _
    have e0 := central_step (n := n0) (hψ 0) hcen hR0 (by simp only [mul_assoc])
    have e1 := central_step (n := n1) (hψ 1) hcen hR1 (by rw [e0]; simp only [mul_assoc])
    have e2 := central_step (n := n2) (hψ 2) hcen hR2 e1
    have e3 := central_step (n := n3) (hψ 3) hcen hR3 (by rw [e2, mul_one])
    exact e3

section Model

theorem exists_four_sl2_twistedE6_card (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q.card ∧
      ∃ φ : Fin 4 → SL(2, F) →* ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩,
        (∀ i, Function.Injective (φ i)) ∧
          ∀ i j, i ≠ j → ∀ A B, Commute (φ i A) (φ j B) := by
  let d : TypeTwistedE6LieIndex :=
    ⟨⟨.twistedE6 q, hv⟩, (LieTypeIndex.isTypeTwistedE6_iff _).2 trivial⟩
  have hfin : Finite d.1.fixedField := Nat.finite_of_card_ne_zero (by
    rw [ValidLieTypeIndex.card_fixedField]
    have h : (d.1 : ValidLieTypeIndex).fieldOrder = q.card := LieTypeIndex.fieldOrder_twistedE6 q
    rw [h, TauCeti.PrimePower.card_def]
    exact (pow_pos q.prime_p.pos _).ne')
  have : Fintype d.1.fixedField := Fintype.ofFinite _
  have hC := commutator_fixedGroup_quadField d
  have hj : ∀ x, quadFrob d (quadIncl d x) = quadIncl d x := quadFrob_quadIncl d
  have hinj : ∀ i : Fin 4, Function.Injective
      ((toQuot (te6Embed d) hC).comp (te6SL2 (quadFrob d) (quadIncl d) hj i)) := fun i =>
    toQuot_comp_injective (te6Embed_injective d) hC _ fun A hA =>
      te6SL2_central (quadFrob d) (quadIncl d) hj i hA
  refine ⟨d.1.fixedField, inferInstance, hfin, ?_, fun i => (toQuot (te6Embed d) hC).comp
    (te6SL2 (quadFrob d) (quadIncl d) hj i), hinj, fun i i' hii' A B => ?_⟩
  · rw [ValidLieTypeIndex.card_fixedField]
    exact LieTypeIndex.fieldOrder_twistedE6 q
  · have h01 : Commute (te6SL2 (quadFrob d) (quadIncl d) hj i A)
        (te6SL2 (quadFrob d) (quadIncl d) hj i' B) :=
      te6SL2_commute (quadFrob d) (quadIncl d) hj hii' A B
    exact h01.map (toQuot (te6Embed d) hC)

theorem partI_data (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid) (hq : q.card = 4)
    {S : Type} [Group S] [Finite S] (e : S ≃* ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) :
    ∃ A U : Subgroup S, IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 4 ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      A ≤ Subgroup.normalizer (U : Set S) ∧ (∀ a ∈ A, (∀ x : S, a * x = x * a) → a = 1) := by
  obtain ⟨F, hF, hFfin, hFcard, φ, hφinj, hφc⟩ := exists_four_sl2_twistedE6_card q hv
  have h4 : Nat.card F = 4 := hFcard.trans hq
  obtain ⟨w, hw0, hw⟩ := exists_sq_add_add_one h4
  exact partI_of_four (two_eq_zero_of_natCard h4) hw0 hw
    (fun i => e.symm.toMonoidHom.comp (φ i))
    (fun i => e.symm.injective.comp (hφinj i))
    (fun i j hij A B => (hφc i j hij A B).map e.symm.toMonoidHom)

theorem partI_index (d : TauCeti.ValidLieTypeIndex) (hd : IsTwistedE6FourIndex d.1) {S : Type}
    [Group S] [Finite S] (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ∃ A U : Subgroup S, IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 4 ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      A ≤ Subgroup.normalizer (U : Set S) ∧ (∀ a ∈ A, (∀ x : S, a * x = x * a) → a = 1) := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | twistedE6 q =>
    obtain ⟨hq2, hqe⟩ : q.p = 2 ∧ q.exponent = 2 := hd
    have hq : q.card = 4 := by
      rw [TauCeti.PrimePower.card_def, hq2, hqe]
      norm_num
    exact partI_data q hv hq e
  | _ => exact absurd hd (by simp [IsTwistedE6FourIndex])

end Model

end TwE6FourRankAux

@[expose] def TwE6FourRankInnerConj : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex), IsTwistedE6FourIndex d.1 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ E F : Subgroup (MulAut S), IsElemAbelian 3 E → IsElemAbelian 3 F →
      Nat.card E = 3 ^ 4 → Nat.card F = 3 ^ 4 →
      E ≤ (MulAut.conj : S →* MulAut S).range → F ≤ (MulAut.conj : S →* MulAut S).range →
      ∃ β : MulAut S, F = E.map (MulAut.conj β).toMonoidHom

section Final

theorem twE6FourRank_of_inner_conj (hConj : TwE6FourRankInnerConj) : TwE6FourRank := by
  intro S _ _ d hd hiso
  obtain ⟨e⟩ := hiso
  obtain ⟨A, U, hA, hAcard, hU0, hU2, hAN, hcen⟩ := TwE6FourRankAux.partI_index d hd e
  refine ⟨⟨A, hA, hAcard, U, hU0, hU2, hAN⟩, ?_⟩
  intro E hE hEcard hEinn
  haveI : IsMulCommutative A := hA.1
  let κ : A →* MulAut S := (MulAut.conj : S →* MulAut S).comp A.subtype
  have hκinj : Function.Injective κ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    apply Subtype.ext
    apply hcen (a : S) a.2
    intro x
    have hx := congrArg (fun φ : MulAut S => φ x) ha
    simp only [κ, MonoidHom.comp_apply, MulAut.conj_apply, MulAut.one_apply] at hx
    exact (mul_inv_eq_iff_eq_mul).1 hx
  have hκcard : Nat.card κ.range = 3 ^ 4 := by
    rw [← hAcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hκinj).toEquiv).symm
  have hκel : IsElemAbelian 3 κ.range := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 x.2
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 y.2
      apply Subtype.ext
      show (x : MulAut S) * (y : MulAut S) = (y : MulAut S) * (x : MulAut S)
      rw [← ha, ← hb]
      change κ a * κ b = κ b * κ a
      rw [← map_mul, ← map_mul, IsMulCommutative.is_comm.comm a b]
    · obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 hx
      have h3 : a ^ 3 = 1 := Subtype.ext (by simpa using hA.2 (a : S) a.2)
      rw [← ha, ← map_pow, h3, map_one]
  have hκinn : κ.range ≤ (MulAut.conj : S →* MulAut S).range := by
    rintro x ⟨a, rfl⟩
    exact ⟨(a : S), rfl⟩
  obtain ⟨β, hβ⟩ := hConj S d hd ⟨e⟩ κ.range E hκel hE hκcard hEcard hκinn hEinn
  refine ⟨U.map β.toMonoidHom, ?_, ?_, ?_⟩
  · intro hbot
    apply hU0
    rw [eq_bot_iff]
    intro u hu
    have hmem : β u ∈ U.map β.toMonoidHom := Subgroup.mem_map.2 ⟨u, hu, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact β.injective (hmem.trans (map_one β).symm)
  · intro g
    obtain ⟨u, hu, hug⟩ := Subgroup.mem_map.1 g.2
    obtain ⟨k, hk⟩ := hU2 ⟨u, hu⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hk' : u ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hug, ← map_pow, hk', map_one]
  · intro φ hφ u' hu'
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hu'
    rw [hβ] at hφ
    obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.1 hφ
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 hψ
    have hψx : ∀ x : S, ψ x = (a : S) * x * (a : S)⁻¹ := fun x => by
      rw [← ha]
      exact MulAut.conj_apply (a : S) x
    refine Subgroup.mem_map.2 ⟨(a : S) * u * (a : S)⁻¹,
      (Subgroup.mem_normalizer_iff.1 (hAN a.2) u).1 hu, ?_⟩
    show β ((a : S) * u * (a : S)⁻¹) = (β * ψ * β⁻¹) (β u)
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, hψx]

end Final

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
