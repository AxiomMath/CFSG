module

public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitCentEquiv
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Polynomial.SpecificDegree

public noncomputable section

namespace CFSG.AGLEmbedding.LinearThreeKit

open Matrix Polynomial CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {K : Type*} [Field K]

namespace IsFixedLine

variable {p : ℕ} {u : SpecialLinearGroup (Fin 3) K} {x : Fin 3 → K}

theorem root_ne_one (h : IsFixedLine p u x) : AdjoinRoot.root (centPoly u) ≠ 1 := by
  intro h1
  have h2 := root_sq (Matrix.trace (u : Matrix (Fin 3) (Fin 3) K) - 1)
  rw [h1, one_pow, mul_one] at h2
  have h3 : AdjoinRoot.of (centPoly u) (Matrix.trace (u : Matrix (Fin 3) (Fin 3) K) - 1) =
      AdjoinRoot.of (centPoly u) 2 := by
    rw [map_ofNat]
    linear_combination -h2
  have := quadElem_injective (t := Matrix.trace (u : Matrix (Fin 3) (Fin 3) K) - 1)
    (a := Matrix.trace (u : Matrix (Fin 3) (Fin 3) K) - 1) (b := 0) (a' := 2) (b' := 0)
    (by rw [quadElem, quadElem, h3])
  exact h.trace_sub_one_ne_two this.1

theorem orderOf_centralizerEquiv_self (h : IsFixedLine p u x) (hp : p.Prime) :
    orderOf (h.centralizerEquiv ⟨u, self_mem_centralizer u⟩) = p := by
  have : Fact p.Prime := ⟨hp⟩
  refine orderOf_eq_prime ?_ fun h1 => h.root_ne_one ?_
  · rw [← map_pow, show (⟨u, self_mem_centralizer u⟩ : Subgroup.centralizer {u}) ^ p = 1 from
      Subtype.ext h.pow_eq_one, map_one]
  · rw [← h.centralizerEquiv_self, h1, Units.val_one]

theorem irreducible_centPoly (hns : ∀ r : K, ¬ (centPoly u).IsRoot r) :
    Irreducible (centPoly u) :=
  Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (by rw [quadPoly_natDegree]; decide) hns

theorem isCyclic_of_le_centralizer (h : IsFixedLine p u x)
    (hns : ∀ r : K, ¬ (centPoly u).IsRoot r) {Q : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hQ : Q ≤ Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin 3) K))) [Finite Q] :
    IsCyclic Q := by
  have : Fact (Irreducible (centPoly u)) := ⟨irreducible_centPoly hns⟩
  refine isCyclic_of_injective_ringHom ((Units.coeHom _).comp
    (h.centralizerEquiv.toMonoidHom.comp (Subgroup.inclusion hQ))) ?_
  intro a b hab
  exact Subgroup.inclusion_injective hQ (h.centralizerEquiv.injective (Units.ext hab))

theorem mem_zpowers_of_pow_eq_one (h : IsFixedLine p u x)
    (hns : ∀ r : K, ¬ (centPoly u).IsRoot r) (hp : p.Prime) {g : SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin 3) K)))
    (hgp : g ^ p = 1) : g ∈ Subgroup.zpowers u := by
  have : Fact (Irreducible (centPoly u)) := ⟨irreducible_centPoly hns⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  set e := h.centralizerEquiv with he
  have hprim : IsPrimitiveRoot (e ⟨u, self_mem_centralizer u⟩ : AdjoinRoot (centPoly u)) p :=
    IsPrimitiveRoot.coe_units_iff.mpr
      (IsPrimitiveRoot.iff_orderOf.mpr (h.orderOf_centralizerEquiv_self hp))
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one (ξ := (e ⟨g, hg⟩ : AdjoinRoot (centPoly u)))
    (by rw [← Units.val_pow_eq_pow_val, ← map_pow, show (⟨g, hg⟩ : Subgroup.centralizer {u}) ^ p
      = 1 from Subtype.ext hgp, map_one, Units.val_one])
  have hgi : (⟨u, self_mem_centralizer u⟩ : Subgroup.centralizer {u}) ^ i = ⟨g, hg⟩ :=
    e.injective (Units.ext (by rw [map_pow, Units.val_pow_eq_pow_val, hi]))
  exact ⟨i, by simpa using congrArg Subtype.val hgi⟩

theorem finite_card_le_of_nonsplit (h : IsFixedLine p u x)
    (hns : ∀ r : K, ¬ (centPoly u).IsRoot r) {E : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hE : E ≤ Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin 3) K)))
    (hEp : ∀ g ∈ E, g ^ p = 1) : Finite E ∧ Nat.card E ≤ p := by
  have : Fact (Irreducible (centPoly u)) := ⟨irreducible_centPoly hns⟩
  have : NeZero p := ⟨h.odd.pos.ne'⟩
  let f : E → rootsOfUnity p (AdjoinRoot (centPoly u)) := fun g =>
    ⟨h.centralizerEquiv ⟨g, hE g.2⟩, by
      rw [mem_rootsOfUnity, ← map_pow, show (⟨g, hE g.2⟩ : Subgroup.centralizer {u}) ^ p = 1
        from Subtype.ext (hEp g g.2), map_one]⟩
  have hf : Function.Injective f := fun a b hab => by
    have := h.centralizerEquiv.injective (congrArg Subtype.val hab)
    exact Subtype.ext (congrArg (Subtype.val : Subgroup.centralizer ({u} : Set
      (SpecialLinearGroup (Fin 3) K)) → SpecialLinearGroup (Fin 3) K) this)
  exact ⟨Finite.of_injective f hf,
    (Nat.card_le_card_of_injective f hf).trans (card_rootsOfUnity _ p)⟩

theorem trace_eq_of_isRoot {r : K} (hr : (centPoly u).IsRoot r) :
    r ≠ 0 ∧ Matrix.trace (u : Matrix (Fin 3) (Fin 3) K) - 1 = r + r⁻¹ := by
  have e : r ^ 2 - (Matrix.trace (u : Matrix (Fin 3) (Fin 3) K) - 1) * r + 1 = 0 := by
    simpa [centPoly, quadPoly] using hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at e
  refine ⟨hr0, ?_⟩
  field_simp
  linear_combination -e

theorem exists_splitTorus (h : IsFixedLine p u x) {r : K} (hr : (centPoly u).IsRoot r) :
    ∃ b₁ b₂ : Fin 3 → K, LinearIndependent K ![x, b₁, b₂] ∧
      (u : Matrix (Fin 3) (Fin 3) K) *ᵥ b₁ = r • b₁ ∧
      (u : Matrix (Fin 3) (Fin 3) K) *ᵥ b₂ = r⁻¹ • b₂ ∧ r ≠ 1 ∧ r ≠ r⁻¹ ∧ r ^ p = 1 ∧
      ∀ g : SpecialLinearGroup (Fin 3) K,
        g ∈ Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin 3) K)) ↔
          ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ x ∈ K ∙ x ∧
            (g : Matrix (Fin 3) (Fin 3) K) *ᵥ b₁ ∈ K ∙ b₁ ∧
            (g : Matrix (Fin 3) (Fin 3) K) *ᵥ b₂ ∈ K ∙ b₂) := by
  set U : Matrix (Fin 3) (Fin 3) K := (u : Matrix (Fin 3) (Fin 3) K) with hUdef
  obtain ⟨hr0, ht⟩ := trace_eq_of_isRoot hr
  set w := h.nbVec with hwdef
  have hli := h.nbVec_li
  have hsq : U *ᵥ (U *ᵥ w) = (r + r⁻¹) • (U *ᵥ w) - w := by rw [← ht]; exact h.nbVec_sq
  have hfx : U *ᵥ x = x := h.fixed
  have hrr : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0
  set b₁ := U *ᵥ w - r⁻¹ • w with hb₁
  set b₂ := U *ᵥ w - r • w with hb₂
  have hU₁ : U *ᵥ b₁ = r • b₁ := by
    rw [hb₁, Matrix.mulVec_sub, Matrix.mulVec_smul, hsq, smul_sub, smul_smul, hrr]
    module
  have hU₂ : U *ᵥ b₂ = r⁻¹ • b₂ := by
    rw [hb₂, Matrix.mulVec_sub, Matrix.mulVec_smul, hsq, smul_sub, smul_smul, inv_mul_cancel₀ hr0]
    module
  have hb₁0 : b₁ ≠ 0 := fun h0 => by
    have := LinearIndependent.pair_iff.mp (linearIndependent_tail_pair hli) (-r⁻¹) 1
      (by rw [← h0, hb₁]; module)
    simp at this
  have hrp : r ^ p = 1 := by
    have e := pow_mulVec_of_mulVec_eq_smul hU₁ p
    rw [coe_pow_eq_one h.pow_eq_one, Matrix.one_mulVec] at e
    exact smul_left_injective K hb₁0 (by simpa using e.symm)
  have hr1 : r ≠ 1 := fun h1 => h.trace_sub_one_ne_two (by rw [ht, h1, inv_one]; norm_num)
  have hrr' : r ≠ r⁻¹ := by
    intro h1
    have h2 : (r - 1) * (r + 1) = 0 := by
      have : r * r = 1 := by rw [← hrr, ← h1]
      linear_combination this
    have hm : r = -1 := eq_neg_of_add_eq_zero_left
      ((mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hr1))
    rw [hm, h.odd.neg_one_pow] at hrp
    exact hr1 (hm.trans hrp)
  have hli' : LinearIndependent K ![x, b₁, b₂] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hc
    have := Fintype.linearIndependent_iff.mp hli ![c 0, -(c 1 * r⁻¹) - c 2 * r, c 1 + c 2]
      (by simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ← hc, hb₁, hb₂]; module)
    have h0 : c 0 = 0 := by simpa using this 0
    have h1 : -(c 1 * r⁻¹) - c 2 * r = 0 := by simpa using this 1
    have h2 : c 1 + c 2 = 0 := by simpa using this 2
    have hc1 : c 1 = 0 := by
      have : c 1 * (r - r⁻¹) = 0 := by linear_combination h1 + r * h2
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hrr')
    intro i
    fin_cases i
    · exact h0
    · exact hc1
    · simpa [hc1] using h2
  have heig : ∀ (l : K) (v : Fin 3 → K), U *ᵥ v = l • v →
      ∃ c : Fin 3 → K, v = c 0 • x + c 1 • b₁ + c 2 • b₂ ∧
        c 0 * (l - 1) = 0 ∧ c 1 * (l - r) = 0 ∧ c 2 * (l - r⁻¹) = 0 := by
    intro l v hv
    obtain ⟨c, hc⟩ := exists_sum_smul_eq hli' v
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hc
    have := Fintype.linearIndependent_iff.mp hli' ![c 0 * (l - 1), c 1 * (l - r), c 2 * (l - r⁻¹)]
      (by
        simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        have e := hv
        rw [← hc, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
          Matrix.mulVec_smul, hfx, hU₁, hU₂] at e
        linear_combination (norm := module) -e)
    exact ⟨c, hc.symm, by simpa using this 0, by simpa using this 1, by simpa using this 2⟩
  have hr1' : r⁻¹ ≠ 1 := fun h1 => hr1 (by rw [← inv_inv r, h1, inv_one])
  refine ⟨b₁, b₂, hli', hU₁, hU₂, hr1, hrr', hrp, fun g => ⟨fun hg => ?_, fun ⟨h0, h1, h2⟩ => ?_⟩⟩
  · have hc := coe_mul_comm_of_mem_centralizer hg
    refine ⟨h.le _ (mulVec_fixed_of_commute hc hfx), ?_, ?_⟩
    · obtain ⟨c, hcv, h0, -, h2⟩ := heig r _ (by
        rw [← mulVec_mulVec_comm hc, hU₁, Matrix.mulVec_smul])
      have hc0 := (mul_eq_zero.mp h0).resolve_right (sub_ne_zero.mpr hr1)
      have hc2 := (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr hrr')
      exact Submodule.mem_span_singleton.mpr ⟨c 1, by rw [hcv, hc0, hc2]; simp⟩
    · obtain ⟨c, hcv, h0, h1, -⟩ := heig r⁻¹ _ (by
        rw [← mulVec_mulVec_comm hc, hU₂, Matrix.mulVec_smul])
      have hc0 := (mul_eq_zero.mp h0).resolve_right (sub_ne_zero.mpr hr1')
      have hc1 := (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr hrr'.symm)
      exact Submodule.mem_span_singleton.mpr ⟨c 2, by rw [hcv, hc0, hc1]; simp⟩
  · obtain ⟨l₀, hl₀⟩ := Submodule.mem_span_singleton.mp h0
    obtain ⟨l₁, hl₁⟩ := Submodule.mem_span_singleton.mp h1
    obtain ⟨l₂, hl₂⟩ := Submodule.mem_span_singleton.mp h2
    refine mem_centralizer_of_coe_mul_comm (eq_of_mulVec_eq hli' (forall_fin_three ?_ ?_ ?_))
    · change (U * (g : Matrix (Fin 3) (Fin 3) K)) *ᵥ x = ((g : Matrix (Fin 3) (Fin 3) K) * U) *ᵥ x
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfx, ← hl₀, Matrix.mulVec_smul, hfx]
    · change (U * (g : Matrix (Fin 3) (Fin 3) K)) *ᵥ b₁ = ((g : Matrix (Fin 3) (Fin 3) K) * U) *ᵥ b₁
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hU₁, Matrix.mulVec_smul, ← hl₁,
        Matrix.mulVec_smul, hU₁, smul_comm]
    · change (U * (g : Matrix (Fin 3) (Fin 3) K)) *ᵥ b₂ = ((g : Matrix (Fin 3) (Fin 3) K) * U) *ᵥ b₂
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hU₂, Matrix.mulVec_smul, ← hl₂,
        Matrix.mulVec_smul, hU₂, smul_comm]

end IsFixedLine

end CFSG.AGLEmbedding.LinearThreeKit
