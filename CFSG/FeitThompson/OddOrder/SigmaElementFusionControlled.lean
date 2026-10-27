module

public import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity
import CFSG.FeitThompson.OddOrder.MaximalSubgroupsSelfNormalizing
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.CoprimeNormalComplementPrimeCore

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {M : Subgroup G}

theorem exists_mem_conj_eq_of_mem_sigmaPrimes [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    (hM : IsCoatom M) (hpM : p ∈ sigmaPrimes M) {x : G} (hxM : x ∈ M)
    (hxp : ∃ k, orderOf x = p ^ k) {g : G} (hxg : g⁻¹ * x * g ∈ M) :
    ∃ m ∈ M, g⁻¹ * x * g = m⁻¹ * x * m := by
  have hX : IsPGroup p (zpowers x) :=
    (isPGroup_zpowers_iff_exists_orderOf_eq_pow (prime_of_mem_sigmaPrimes hpM)).2 hxp
  have ha : zpowers x ≤ MulAut.conj g • M := by
    rw [zpowers_le, conj_smul_eq_map_conj]
    refine ⟨g⁻¹ * x * g, hxg, ?_⟩
    change g * (g⁻¹ * x * g) * g⁻¹ = x
    group
  have hb : zpowers x ≤ MulAut.conj (1 : G) • M := by
    rw [map_one, one_smul, zpowers_le]; exact hxM
  obtain ⟨c, hc, hcg⟩ :=
    exists_mem_centralizer_conj_smul_of_mem_sigmaPrimes hna hodd hsolv hM hpM hX ha hb
  rw [map_one, one_smul, conj_smul_conj_smul] at hcg
  have hcx : x * c = c * x := (Subgroup.mem_centralizer_iff.1 hc) x (mem_zpowers x)
  have hmem : c * g ∈ M := by
    rw [← normalizer_coe_eq_of_isCoatom hna hM]
    exact mem_normalizer_iff_conj_smul_eq.2 hcg
  refine ⟨c * g, hmem, ?_⟩
  have hc' : c⁻¹ * x * c = x := by rw [mul_assoc, hcx]; group
  rw [show (c * g)⁻¹ * x * (c * g) = g⁻¹ * (c⁻¹ * x * c) * g by group, hc']

theorem exists_mem_conj_eq_of_mem_sigmaPrimes_of_ne_one [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    (hM : IsCoatom M) (hpM : p ∈ sigmaPrimes M) {x : G} (hxM : x ∈ M) (_hx1 : x ≠ 1)
    {k : ℕ} (hxp : orderOf x = p ^ k) {g : G} (hxg : g⁻¹ * x * g ∈ M) :
    ∃ m ∈ M, g⁻¹ * x * g = m⁻¹ * x * m :=
  exists_mem_conj_eq_of_mem_sigmaPrimes hna hodd hsolv hM hpM hxM ⟨k, hxp⟩ hxg

theorem exists_mem_conj_eq_of_isConj [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    (hM : IsCoatom M) (hpM : p ∈ sigmaPrimes M) {x y : G} (hxM : x ∈ M) (hyM : y ∈ M)
    (hxp : ∃ k, orderOf x = p ^ k) (hxy : IsConj x y) :
    ∃ m ∈ M, m⁻¹ * x * m = y := by
  obtain ⟨u, hu⟩ := hxy
  rw [SemiconjBy] at hu
  have hy : ((u : G))⁻¹⁻¹ * x * ((u : G))⁻¹ = y := by
    rw [inv_inv, hu]; group
  obtain ⟨m, hm, hmeq⟩ :=
    exists_mem_conj_eq_of_mem_sigmaPrimes hna hodd hsolv hM hpM hxM hxp (hy ▸ hyM)
  exact ⟨m, hm, by rw [← hmeq, hy]⟩

end

end CFSG.FeitThompson
