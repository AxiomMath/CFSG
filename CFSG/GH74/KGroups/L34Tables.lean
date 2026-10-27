
module

public import CFSG.GH74.KGroups.L34TablesBase

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.Generic6
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.Checks2
public import CFSG.GH74.KGroups.Checks3
public import CFSG.GH74.KGroups.L34
public import CFSG.GH74.KGroups.L34Aut
public import CFSG.GH74.KGroups.CoverL34
public meta import CFSG.GH74.KGroups.Checks
public meta import CFSG.GH74.KGroups.Checks2
public meta import CFSG.GH74.KGroups.Checks3
public meta import CFSG.GH74.KGroups.L34
public meta import CFSG.GH74.KGroups.L34Aut
public import CFSG.GH74.KGroups.L34TablesInputs
public meta import CFSG.GH74.KGroups.L34TablesInputs
public import CFSG.GH74.KGroups.PSLN
public import CFSG.GH74.KGroups.FieldGF
public import CFSG.GH74.KGroups.L34Inputs
public import CFSG.GH74.KGroups.L34AutInputs
public import Certificates.Certificate5124

public section

namespace CFSG.GH74.KGroups.L34

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint

theorem P_le_A :
    QP.originalSubgroup ≤ QA.originalSubgroup :=
  Certificates.certificate5124.2.2.1

theorem x0_mem :
    x0 ∈ QP.originalSubgroup :=
  Certificates.certificate5124.1.2.2

theorem one_class_P :
    ∀ y ∈ QP.originalSubgroup, y ^ 2 = 1 → y ≠ 1 →
    ∃ g ∈ QP.originalSubgroup, g * x0 * g⁻¹ = y :=
  Certificates.certificate5124.2.1

theorem card_CP :
    Nat.card ↥(QP.originalSubgroup ⊓
    Subgroup.centralizer ({x0} : Set (Equiv.Perm (Fin 42)))) = 64 :=
  Certificates.certificate5124.2.2.2.1

theorem card_CA : Nat.card ↥(QA.originalSubgroup ⊓
    Subgroup.centralizer ({x0} : Set (Equiv.Perm (Fin 42)))) = 768 :=
  Certificates.certificate5124.2.2.2.2.1

theorem solv_CA :
    Group.IsSolvable ↥(QA.originalSubgroup ⊓
    Subgroup.centralizer ({x0} : Set (Equiv.Perm (Fin 42)))) := by
  apply isSolvable_of_two_primes
  have h : (768 : ℕ) = 2 ^ 8 * 3 := by norm_num
  rw [card_CA, h, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
  exact (Finset.card_union_le _ _).trans (by simp)

theorem cent_sq :
    ∀ σ ∈ QA.originalSubgroup, (∀ q ∈ QP.originalSubgroup ⊓
    Subgroup.centralizer ({x0} : Set (Equiv.Perm (Fin 42))), σ * q = q * σ) → σ ^ 2 = 1 :=
  Certificates.certificate5124.2.2.2.2.2

theorem center_trivial
    {K : Type} [Group K] (e : K ≃* QP.originalSubgroup) (g : K)
    (hg : ∀ n : K, n * g = g * n) : g = 1 := by
  obtain ⟨M, hP, hA⟩ := autModel e
  have hgP : (M.e g : Equiv.Perm (Fin 42)) ∈ QP.originalSubgroup := by
    rw [← hP]; exact (M.e g).2
  have h1 : (M.e g : Equiv.Perm (Fin 42)) = 1 := by
    apply M.centralizer_trivial (by rw [hA]; exact P_le_A hgP)
    intro y hy
    obtain ⟨n, hn⟩ := M.e.surjective ⟨y, hy⟩
    have hyn : (M.e n : Equiv.Perm (Fin 42)) = y := congrArg Subtype.val hn
    rw [← hyn]
    have := (congrArg (fun z : K => (M.e z : Equiv.Perm (Fin 42))) (hg n)).symm
    simpa using this
  exact M.e.injective (Subtype.ext (by simpa using h1))

theorem ki3_model
    {H : Type} [Group H] (N : Subgroup H) [N.Normal]
    (hFit : Subgroup.centralizer (N : Set H) ≤ N) (e : ↥N ≃* QP.originalSubgroup)
    (x : H) (hx : x ∈ N) (hx2 : orderOf x = 2) :
    Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set H)) ∧
      CFSG.pPrimeCore 2 ↥(Subgroup.centralizer ({x} : Set H)) = ⊥ ∧
      Nat.card ↥(Subgroup.centralizer ({x} : Set H) ⊓ N) = 64 := by
  have hN : Subgroup.centralizer (N : Set H) = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [Subgroup.mem_bot]
    have hcN : c ∈ N := hFit hc
    have h1 := center_trivial e ⟨c, hcN⟩ (fun n => Subtype.ext (by
      have := Subgroup.mem_centralizer_iff.1 hc n n.2
      simpa using this))
    simpa using congrArg Subtype.val h1
  obtain ⟨M, hP, hA⟩ := autModel e
  set xN : N := ⟨x, hx⟩ with hxN
  have hxx : (xN : H) = x := rfl
  have hord : orderOf ((M.e xN : M.P) : Equiv.Perm (Fin 42)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hxN, Subgroup.orderOf_mk]
    exact hx2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsq, hne⟩ := orderOf_eq_prime_iff.1 hord
  have hbarP : ((M.e xN : M.P) : Equiv.Perm (Fin 42)) ∈ QP.originalSubgroup := by
    rw [← hP]; exact (M.e xN).2
  obtain ⟨g, hgP, hg⟩ := one_class_P _ hbarP hsq hne
  have hgPM : g ∈ M.P := by rw [hP]; exact hgP
  have hcard : Nat.card ↥(Subgroup.centralizer ({x} : Set H) ⊓ N) = 64 := by
    have h1 := card_centralizer_inf_normal N M.P M.e xN
    rw [hxx] at h1
    rw [h1, ← hg, card_conj M.P g x0 hgPM, hP, card_CP]
  refine ⟨?_, ?_, hcard⟩
  · exact centralizer_solvable_of_model N hN M xN (by
      rw [← hg, hA]
      exact solvable_conj QA.originalSubgroup g x0 (P_le_A hgP) solv_CA)
  · exact pPrimeCore_centralizer_eq_bot N hN M xN 6 (by
      intro q hq
      have h2 : (⟨q, hq⟩ : ↥(Subgroup.centralizer ({x} : Set H) ⊓ N)) ^
          Nat.card ↥(Subgroup.centralizer ({x} : Set H) ⊓ N) = 1 := pow_card_eq_one'
      rw [hcard] at h2
      simpa using congrArg Subtype.val h2) (by
      rw [← hg, hA, hP]
      exact commute_all_conj QA.originalSubgroup QP.originalSubgroup P_le_A g x0 hgP cent_sq)

end CFSG.GH74.KGroups.L34
