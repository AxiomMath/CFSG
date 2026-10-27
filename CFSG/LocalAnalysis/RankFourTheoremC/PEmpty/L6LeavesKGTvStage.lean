module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGTvSmall
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGTvSym
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGTvOrth
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGTvY

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGTv

open Module CFSG.ComponentClassification.OutcomeLocal CFSG.Open CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Cooperstein.StructureLie
open scoped commutatorElement

theorem commutator_eq_top_of_simple_nonab {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ∃ x y : G, x * y ≠ y * x) : commutator G = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h0 | h0
  · exfalso
    obtain ⟨x, y, hxy⟩ := h
    apply hxy
    have : ⁅x, y⁆ ∈ commutator G :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  · exact h0

theorem stageL {X : Type} [Group X] [Finite X] {N : Subgroup X} [N.Normal]
    (hNs : IsSimpleGroup ↥N) (hNn : ∃ x y : ↥N, x * y ≠ y * x)
    (hnotAlt : ∀ n : ℕ, 7 ≤ n → ¬ Nonempty (↥N ≃* alternatingGroup (Fin n)))
    {a z : X} {q : ℕ} (haN : a ∉ N) (hX : ∀ x : X, x ∈ N ∨ x * a ∈ N) (hz : z ∈ N)
    (hzq : orderOf z = q) (hq : q.Prime) (hq5 : 5 ≤ q) (hcomm : a * z = z * a)
    {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (ψ : X →* LinearMap.GeneralLinearGroup (ZMod 2) U) (hinj : Function.Injective ψ)
    (hirr : ∀ T : Submodule (ZMod 2) U,
      (∀ g ∈ ψ.range, ∀ w ∈ T, (g : U →ₗ[ZMod 2] U) w ∈ T) → T = ⊥ ∨ T = ⊤)
    (hgen : ∃ T : Set (LinearMap.GeneralLinearGroup (ZMod 2) U),
      (∀ t ∈ T, IsF2Transvection t) ∧ ψ.range = Subgroup.closure T)
    (hτ : IsF2Transvection (ψ a)) :
    ∃ (ε : Bool) (n : ℕ), 3 ≤ n ∧ IsOmegaTwo ε n ↥N ∧
      ∃ Y : Subgroup X, Y ≤ N ⊓ Subgroup.centralizer ({a} : Set X) ∧ z ∈ Y ∧
        IsSimpleGroup ↥Y ∧ (∃ x y : ↥Y, x * y ≠ y * x) ∧ 3 ∣ Nat.card ↥Y := by
  classical
  haveI : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  haveI := hNs
  have hidx : N.index = 2 :=
    Subgroup.index_eq_two_iff_exists_notMem_and.2 ⟨a, haN, fun b => (hX b).symm⟩
  have hrel : (N.map ψ).relIndex ψ.range = 2 := by
    rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective N ⊤ hinj,
      Subgroup.relIndex_top_right, hidx]
  haveI : Group.IsPerfect ↥N := ⟨commutator_eq_top_of_simple_nonab hNn⟩
  have hperf : ⁅N.map ψ, N.map ψ⁆ = N.map ψ := by
    rw [← Subgroup.map_commutator, Subgroup.commutator_eq_self]
  have hL1 : N.map ψ ≠ ⊥ := by
    intro h
    have hN0 : N = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ hinj).1 h
    obtain ⟨x, y, hxy⟩ := hNn
    apply hxy
    have hx : (x : X) ∈ (⊥ : Subgroup X) := hN0 ▸ x.2
    have hy : (y : X) ∈ (⊥ : Subgroup X) := hN0 ▸ y.2
    rw [Subgroup.mem_bot] at hx hy
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hx, hy])
  obtain ⟨φ, a₀, hφa, hφ, ha₀, hτeq⟩ := (isF2Transvection_iff _).1 hτ
  have hn1 : 1 ≤ finrank (ZMod 2) U :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 2)).mpr ⟨a₀, ha₀⟩
  by_cases hd : Nat.card U ≤ 16
  · exfalso
    have hz' : ψ z * tv φ a₀ hφa = tv φ a₀ hφa * ψ z := by
      rw [← hτeq, ← map_mul, ← map_mul, hcomm.symm]
    exact false_of_commute_tv hd φ a₀ hφa hφ ha₀ hz' hq hq5
      ((orderOf_injective ψ hinj z).trans hzq)
  · have hd5 : 5 ≤ finrank (ZMod 2) U := by
      by_contra hlt
      apply hd
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U), Nat.card_zmod]
      calc 2 ^ finrank (ZMod 2) U ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 16 := by norm_num
    obtain ⟨hLeq, hcases⟩ := shape_of_perfect_index_two hn1 ψ.range (N.map ψ) hgen hirr
      (Subgroup.map_le_range ψ N) hrel hperf hL1
    have hNc : N = ⁅(⊤ : Subgroup X), ⊤⁆ := by
      apply Subgroup.map_injective hinj
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map]
      exact hLeq
    rcases hcases with ⟨h4, -⟩ | ⟨Q, hQ, hH⟩ | hsym
    · omega
    · obtain ⟨ε, n, hn2, hΩ, ⟨S⟩⟩ := orth_case hNc ψ hinj hτ Q hQ hH hd5
      have hzC : z ∈ N ⊓ Subgroup.centralizer ({a} : Set X) :=
        ⟨hz, Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm⟩
      obtain ⟨Y, hYle, hzY, hYs, hYn, hY3⟩ := exists_Y (N ⊓ Subgroup.centralizer ({a} : Set X))
        hn2 S hzC (hzq ▸ hq.odd_of_ne_two (by omega))
      exact ⟨ε, n + 1, by omega, hΩ, Y, hYle, hzY, hYs, hYn, hY3⟩
    · exact (false_of_sym hNc ψ hinj hd5 hsym hnotAlt).elim

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGTv
