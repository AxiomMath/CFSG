module

public import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Definitions.KappaPrimes
import CFSG.FeitThompson.Representations.ConjugationTransportsDadeSignalizers
import CFSG.FeitThompson.Local.ConjugationUniqueMaximalOvergroup
import CFSG.FeitThompson.Foundations.NonabelianPGroupInvariantCentralDerived
import CFSG.FeitThompson.Foundations.PGroupNontrivialCenter
import CFSG.FeitThompson.OddOrder.MaximalSubgroupsSelfNormalizing

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G H : Type*} [Group G] [Group H]

theorem smul_centralizer (u : G) (s : Set G) :
    MulAut.conj u • centralizer s = centralizer (MulAut.conj u • s) := by
  rw [Subgroup.pointwise_smul_def]
  exact map_centralizer_eq_centralizer_image s (MulAut.conj u)

theorem smul_centralizer_coe (u : G) (S : Subgroup G) :
    MulAut.conj u • centralizer (S : Set G)
      = centralizer ((MulAut.conj u • S : Subgroup G) : Set G) := by
  rw [smul_centralizer, Subgroup.coe_pointwise_smul]

theorem smul_inf_centralizer_of_mem_normalizer {u : G} {S : Subgroup G}
    (hu : u ∈ normalizer (S : Set G)) :
    MulAut.conj u • (S ⊓ centralizer (S : Set G)) = S ⊓ centralizer (S : Set G) := by
  have hS : MulAut.conj u • S = S := by
    rw [Subgroup.pointwise_smul_def]; exact Subgroup.mem_normalizer_iff_map_conj_eq.1 hu
  rw [Subgroup.smul_inf, smul_centralizer_coe, hS]

theorem mem_normalizer_of_smul_eq {u : G} {S : Subgroup G} (h : MulAut.conj u • S = S) :
    u ∈ normalizer (S : Set G) := by
  rw [Subgroup.pointwise_smul_def] at h
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2 h

theorem orderOf_conj (u x : G) : orderOf (u * x * u⁻¹) = orderOf x :=
  orderOf_injective (MulAut.conj u : G →* G) (MulAut.conj u).injective x

theorem center_eq_bot_of_isSimpleGroup [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) :
    center G = ⊥ :=
  (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G)).resolve_right
    fun h => hna (Subgroup.center_eq_top_iff.1 h)

theorem centralizer_singleton_lt_top [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    {y : G} (hy : y ≠ 1) : centralizer ({y} : Set G) < ⊤ := by
  refine lt_top_iff_ne_top.2 fun h => hy ?_
  have hmem := Subgroup.centralizer_eq_top_iff_subset.1 h (Set.mem_singleton y)
  rw [center_eq_bot_of_isSimpleGroup hna] at hmem
  simpa using hmem

theorem exists_mem_inf_centralizer_orderOf_eq_of_notMem_sigmaPrimes
    [Finite G] [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (_hodd : Odd (Nat.card G)) (_hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K)
    {M : Subgroup G} (hM : IsCoatom M) {q : ℕ} (hq : q.Prime) (hqs : q ∉ sigmaPrimes M)
    {Q : Subgroup G} (hQM : Q ≤ M) (hQcard : Nat.card Q = q ^ (Nat.card M).factorization q)
    (hQ : Q ≠ ⊥) :
    ∃ x ∈ Q ⊓ centralizer (Q : Set G), orderOf x = q ∧ centralizer ({x} : Set G) < ⊤ ∧
      ¬ IsUniqueMaximalOvergroup (centralizer ({x} : Set G)) M := by
  set e := (Nat.card M).factorization q with hedef
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h, pow_zero, Subgroup.card_eq_one] at hQcard
      exact absurd hQcard hQ
    · exact h
  set Z : Subgroup G := Q ⊓ centralizer (Q : Set G) with hZdef
  obtain ⟨z, hzc, hzo⟩ := exists_mem_center_orderOf_eq hq hQcard he
  have hzZ : ((z : G)) ∈ Z := by
    rw [hZdef, ← map_subtype_center_eq_inf_centralizer]
    exact ⟨z, hzc, rfl⟩
  have hzo' : orderOf ((z : G)) = q := by rw [Subgroup.orderOf_coe]; exact hzo
  have hkey : ∃ x ∈ Z, orderOf x = q ∧
      ¬ IsUniqueMaximalOvergroup (centralizer ({x} : Set G)) M := by
    by_contra hgood
    have hgood' : ∀ x ∈ Z, orderOf x = q →
        IsUniqueMaximalOvergroup (centralizer ({x} : Set G)) M := fun x hx hxo =>
      not_not.1 fun h => hgood ⟨x, hx, hxo, h⟩
    have hdvd : q ∣ Nat.card M := Nat.dvd_of_factorization_pos (by omega)
    refine hqs ((mem_sigmaPrimes_iff_exists_subgroup hq).2 ⟨hdvd, Q, hQM, hQcard, fun u hu => ?_⟩)
    have hZu : MulAut.conj u • Z = Z := smul_inf_centralizer_of_mem_normalizer hu
    have hconjZ : u * (z : G) * u⁻¹ ∈ Z := by
      have h := Subgroup.smul_mem_pointwise_smul ((z : G)) (MulAut.conj u) Z hzZ
      rwa [hZu, MulAut.smul_def, MulAut.conj_apply] at h
    have h1 := hgood' _ hzZ hzo'
    have h2 := hgood' _ hconjZ (by rw [orderOf_conj]; exact hzo')
    have h3 : IsUniqueMaximalOvergroup (centralizer ({u * (z : G) * u⁻¹} : Set G))
        (MulAut.conj u • M) := by
      have h := h1.smul u
      rwa [smul_centralizer_singleton] at h
    have h5 := mem_normalizer_of_smul_eq (h3.unique h2)
    rwa [normalizer_coe_eq_of_isCoatom hna hM] at h5
  obtain ⟨x, hxZ, hxo, hxu⟩ := hkey
  have hx1 : x ≠ 1 := fun h => hq.ne_one (by rw [← hxo, h, orderOf_one])
  exact ⟨x, hxZ, hxo, centralizer_singleton_lt_top hna hx1, hxu⟩

theorem exists_mem_center_sylow_orderOf_eq_of_notMem_sigmaPrimes
    [Finite G] [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K)
    {M : Subgroup G} (hM : IsCoatom M) {q : ℕ} (hq : q.Prime) (hqs : q ∉ sigmaPrimes M)
    (Q : Sylow q ↥M) (hQ : (Q : Subgroup ↥M) ≠ ⊥) :
    ∃ x ∈ ((Q : Subgroup ↥M).map M.subtype) ⊓
        centralizer ((((Q : Subgroup ↥M).map M.subtype) : Subgroup G) : Set G),
      orderOf x = q ∧ centralizer ({x} : Set G) < ⊤ ∧
        ¬ IsUniqueMaximalOvergroup (centralizer ({x} : Set G)) M := by
  obtain ⟨hle, hcard⟩ :=
    (exists_sylow_map_subtype_eq_iff hq (P := (Q : Subgroup ↥M).map M.subtype)).1 ⟨Q, rfl⟩
  refine exists_mem_inf_centralizer_orderOf_eq_of_notMem_sigmaPrimes hna hodd hsolv hM hq hqs
    hle hcard ?_
  simpa [Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective] using hQ

theorem exists_mem_inf_centralizer_setOf_isCoatom_ne_singleton_of_notMem_sigmaPrimes
    [Finite G] [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K)
    {M : Subgroup G} (hM : IsCoatom M) {q : ℕ} (hq : q.Prime) (hqs : q ∉ sigmaPrimes M)
    {Q : Subgroup G} (hQM : Q ≤ M) (hQcard : Nat.card Q = q ^ (Nat.card M).factorization q)
    (hQ : Q ≠ ⊥) :
    ∃ x ∈ Q ⊓ centralizer (Q : Set G), orderOf x = q ∧ centralizer ({x} : Set G) < ⊤ ∧
      {N : Subgroup G | IsCoatom N ∧ centralizer ({x} : Set G) ≤ N} ≠ {M} := by
  obtain ⟨x, hxZ, hxo, hxlt, hxu⟩ := exists_mem_inf_centralizer_orderOf_eq_of_notMem_sigmaPrimes
    hna hodd hsolv hM hq hqs hQM hQcard hQ
  exact ⟨x, hxZ, hxo, hxlt, fun h => hxu ((isUniqueMaximalOvergroup_iff _ _).2 h)⟩

end

end CFSG.FeitThompson
