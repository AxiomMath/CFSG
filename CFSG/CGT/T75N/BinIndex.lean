module

public import CFSG.CGT.T75N.BinOvergroup
public import CFSG.CGT.T75N.PpdCyclic
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.CGT.T75N

open Matrix MatrixGroups CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F]

private noncomputable def slAct (n : ℕ) (F : Type) [Field F] :
    SpecialLinearGroup (Fin n) F →* ((Fin n → F) ≃ₗ[F] (Fin n → F)) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin n → F)).toMonoidHom.comp
    (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := F)).toMonoidHom).comp
    SpecialLinearGroup.toGL

private theorem slAct_apply {n : ℕ} (g : SpecialLinearGroup (Fin n) F) (v : Fin n → F) :
    slAct n F g v = (g : Matrix (Fin n) (Fin n) F) *ᵥ v := by
  simp [slAct]

private theorem slAct_injective (n : ℕ) : Function.Injective (slAct n F) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin n → F)).injective.comp
    (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := F)).injective).comp
    SpecialLinearGroup.toGL_injective

theorem exists_conj_unitriangular_le [Finite F] (hF : Nat.card F = 2) {n : ℕ}
    (S : Subgroup (SpecialLinearGroup (Fin n) F)) (hS : ¬ 2 ∣ S.index) :
    ∃ g : SpecialLinearGroup (Fin n) F, ∀ u ∈ unitriangular n F, g⁻¹ * u * g ∈ S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 (unitriangular n F) :=
    IsPGroup.of_card (n := n * (n - 1) / 2) (by rw [card_unitriangular, hF])
  obtain ⟨x, hx⟩ := hU2.nonempty_fixed_point_of_prime_not_dvd_card
    (α := SpecialLinearGroup (Fin n) F ⧸ S) (by rwa [← Subgroup.index])
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨g, fun u hu => ?_⟩
  have h := hx ⟨u⁻¹, (unitriangular n F).inv_mem hu⟩
  have h2 : ((u⁻¹ * g : SpecialLinearGroup (Fin n) F) : SpecialLinearGroup (Fin n) F ⧸ S) =
      (g : SpecialLinearGroup (Fin n) F ⧸ S) := h
  rw [QuotientGroup.eq] at h2
  simpa [mul_assoc] using h2

theorem eq_top_of_odd_index [Finite F] (hF : Nat.card F = 2) {m p : ℕ} [Fact p.Prime]
    (hm : 1 ≤ m) (hpn : p ∣ 2 ^ (m + 1) - 1) (hnp : ∀ k, 0 < k → k < m + 1 → ¬ p ∣ 2 ^ k - 1)
    (hpcard : p ∣ Nat.card (SpecialLinearGroup (Fin (m + 1)) F))
    (S : Subgroup (SpecialLinearGroup (Fin (m + 1)) F)) (hS2 : ¬ 2 ∣ S.index)
    (hSp : ¬ p ∣ S.index) : S = ⊤ := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hF]
  obtain ⟨g, hg⟩ := exists_conj_unitriangular_le hF S hS2
  let c : MulAut (SpecialLinearGroup (Fin (m + 1)) F) := MulAut.conj g⁻¹
  let S' : Subgroup (SpecialLinearGroup (Fin (m + 1)) F) := S.comap c.toMonoidHom
  have hidx : S'.index = S.index := Subgroup.index_comap_of_surjective S c.surjective
  have hUS' : unitriangular (m + 1) F ≤ S' := fun u hu => by
    have := hg u hu
    simpa [S', c, MulAut.conj_apply] using this
  have hpS' : p ∣ Nat.card S' := by
    rw [← S'.card_mul_index] at hpcard
    exact ((Nat.Prime.dvd_mul Fact.out).1 hpcard).resolve_right (hidx ▸ hSp)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpS'
  have hirr : ∀ X : Submodule F (Fin (m + 1) → F),
      (∀ s ∈ S', ∀ v ∈ X, (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ v ∈ X) →
        X = ⊥ ∨ X = ⊤ := by
    intro X hX
    let φ := slAct (m + 1) F
    have hφ : Function.Injective φ := slAct_injective (m + 1)
    have hxp : ((x : SpecialLinearGroup (Fin (m + 1)) F)) ^ p = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx] at this
      exact congrArg Subtype.val this
    have hy : φ x ^ p = 1 := by rw [← map_pow, hxp, map_one]
    have hy1 : φ x ≠ 1 := by
      intro h
      have h1 : (x : SpecialLinearGroup (Fin (m + 1)) F) = 1 := hφ (h.trans (map_one φ).symm)
      have : x = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hx
      exact (Fact.out : p.Prime).one_lt.ne hx
    refine (simple_of_ppd (F := F) (V := Fin (m + 1) → F) (Module.finrank_fin_fun F)
      (by rwa [hFc]) (fun k hk hkn => by rw [hFc]; exact hnp k hk hkn) (φ x) hy hy1).2 X ?_
    intro v hv
    rw [slAct_apply]
    exact hX x x.2 v hv
  have htop : S' = ⊤ := eq_top_of_unitriangular_le hF hm S' hUS' hirr
  have h1 : S.index = 1 := by rw [← hidx, htop, Subgroup.index_top]
  exact Subgroup.index_eq_one.1 h1

theorem eq_top_of_index_dvd_sixtythree [Finite F] (hF : Nat.card F = 2) {a : ℕ}
    (ha : a = 4 ∨ a = 5) (S : Subgroup (SpecialLinearGroup (Fin a) F)) (hS : S.index ∣ 63) :
    S = ⊤ := by
  have h2 : ¬ 2 ∣ S.index := fun h => by have := h.trans hS; omega
  rcases ha with rfl | rfl
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    refine eq_top_of_odd_index (m := 3) (p := 5) hF (by norm_num) (by norm_num) ?_ ?_ S h2 ?_
    · intro k hk hk4
      interval_cases k <;> norm_num
    · rw [card_SL_eq (by norm_num), hF]
      decide
    · intro h
      have := h.trans hS
      omega
  · have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
    refine eq_top_of_odd_index (m := 4) (p := 31) hF (by norm_num) (by norm_num) ?_ ?_ S h2 ?_
    · intro k hk hk5
      interval_cases k <;> norm_num
    · rw [card_SL_eq (by norm_num), hF]
      decide
    · intro h
      have := h.trans hS
      omega

end CFSG.CGT.T75N
