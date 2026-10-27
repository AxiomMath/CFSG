module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Local.ConstrainedCentralizerCoreCoverage
public import
  CFSG.FeitThompson.Definitions.MaximalANormalizedQSubgroups
import Mathlib.GroupTheory.Nilpotent
import CFSG.FeitThompson.Foundations.MinimalNormalInFittingCenter
import CFSG.FeitThompson.Local.CoprimePlaneGeneratesSolvableGroup
import CFSG.FeitThompson.Local.SubgroupIndicatorElementaryPlane
import CFSG.FeitThompson.Local.OutsideSigmaSylowCentralPrimeElement
import CFSG.FeitThompson.Local.ConjugationUniqueMaximalOvergroup
import CFSG.FeitThompson.Local.InvariantMaximalPrimeSubgroupsConjugate

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G] {p q : ℕ}

theorem exists_ne_one_inf_centralizer_singleton_ne_bot [Finite G] (hp : p.Prime)
    {E Q : Subgroup G} (hEcard : Nat.card E = p ^ 2) (hEexp : ∀ x ∈ E, x ^ p = 1)
    (hEN : E ≤ normalizer (Q : Set G)) (hQsolv : Group.IsSolvable Q)
    (hpQ : ¬ p ∣ Nat.card Q) (hQbot : Q ≠ ⊥) :
    ∃ e ∈ E, e ≠ 1 ∧ (Q ⊓ centralizer ({e} : Set G) : Subgroup G) ≠ ⊥ := by
  have := hQsolv
  have hexp : ∀ a : E, a ^ p = 1 := fun a => Subtype.ext (by simpa using hEexp (a : G) a.2)
  set ρ : E →* MulAut Q := Q.normalizerMonoidHom.comp (Subgroup.inclusion hEN) with hρ
  have hkey := iSup_autFixedSubgroup_eq_top hp hEcard hexp ρ hpQ
  by_contra hc
  simp only [not_exists, not_and, not_not] at hc
  have hbot : ∀ a : E, a ≠ 1 → autFixedSubgroup (ρ a) = ⊥ := by
    intro a ha
    refine eq_bot_iff.2 fun y hy => ?_
    have ha' : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
    have h1 := congrArg Subtype.val (mem_autFixedSubgroup.1 hy)
    rw [hρ] at h1
    simp only [MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion] at h1
    have h2 : (y : G) ∈ (Q ⊓ centralizer ({(a : G)} : Set G) : Subgroup G) :=
      ⟨y.2, mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h1).symm⟩
    rw [hc (a : G) a.2 ha'] at h2
    exact Subgroup.mem_bot.2 (Subtype.ext (by simpa using h2))
  have htop : (⊤ : Subgroup Q) = ⊥ :=
    le_bot_iff.1 (hkey ▸ iSup₂_le fun a ha => (hbot a ha).le)
  refine hQbot (eq_bot_iff.2 fun z hz => ?_)
  have hmem : (⟨z, hz⟩ : Q) ∈ (⊥ : Subgroup Q) := htop ▸ Subgroup.mem_top _
  exact Subgroup.mem_bot.2 (by simpa using congrArg Subtype.val (Subgroup.mem_bot.1 hmem))

theorem exists_mem_constrainedCentralizerCore_conj_inv_smul_eq_of_natCard_eq_sq [Finite G]
    [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) {A E : Subgroup G}
    (hAbot : ⊥ < A) (hAtop : A < ⊤) (hcon : IsConstrained A) (hq : q.Prime)
    (hqπ : q ∉ subgroupPrimeSupport A) (hqC : q ∣ Nat.card (centralizer (A : Set G)))
    (hp : p.Prime) (hEA : E ≤ A) (hEC : E ≤ centralizer (A : Set G))
    (hEcard : Nat.card E = p ^ 2) (hEexp : ∀ x ∈ E, x ^ p = 1) :
    ∀ Q₁ ∈ maximalNormalizedPSubgroups A q, ∀ Q₂ ∈ maximalNormalizedPSubgroups A q,
      ∃ k ∈ constrainedCentralizerCore A, MulAut.conj k⁻¹ • Q₁ = Q₂ := by
  have hqf : Fact q.Prime := ⟨hq⟩
  obtain ⟨u₀, hu₀⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (A : Set G)) q hqC
  set u : G := (u₀ : G) with hudef
  have huC : u ∈ centralizer (A : Set G) := u₀.2
  have huord : orderOf u = q := by rw [hudef, Subgroup.orderOf_coe]; exact hu₀
  set U : Subgroup G := zpowers u with hUdef
  have hUp : IsPGroup q U := IsPGroup.of_card (n := 1) (by rw [hUdef, Nat.card_zpowers, huord,
    pow_one])
  have hUN : A ≤ normalizer (U : Set G) :=
    (Subgroup.le_centralizer_iff.2 (Subgroup.zpowers_le.2 huC)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hu1 : u ≠ 1 := fun h => hq.one_lt.ne' (by rw [← huord, h, orderOf_one])
  have hUbot : U ≠ ⊥ := by rw [hUdef]; simpa using hu1
  obtain ⟨R, hR, hUR⟩ := exists_mem_maximalNormalizedPSubgroups_ge hUp hUN
  have hne : ∀ Q ∈ maximalNormalizedPSubgroups A q, Q ≠ ⊥ := fun Q hQ hQbot =>
    hUbot ((eq_of_mem_of_le hQ hUp hUN (hQbot.le.trans bot_le)).trans hQbot)
  have hpA : p ∈ subgroupPrimeSupport A :=
    mem_subgroupPrimeSupport_iff.2 (Nat.mem_primeFactors.2
      ⟨hp, dvd_trans (hEcard ▸ dvd_pow_self p two_ne_zero) (Subgroup.card_dvd_of_le hEA),
        Nat.card_pos.ne'⟩)
  have hpq : p ≠ q := fun h => hqπ (h ▸ hpA)
  have main : ∀ Q ∈ maximalNormalizedPSubgroups A q,
      ∃ k ∈ constrainedCentralizerCore A, MulAut.conj k⁻¹ • Q = R := by
    intro Q hQ
    have hQp : IsPGroup q Q := isPGroup_of_mem hQ
    have hQsolv : Group.IsSolvable Q := by
      have := hQp.isNilpotent
      infer_instance
    have hpQ : ¬ p ∣ Nat.card Q := by
      obtain ⟨n, hn⟩ := hQp.exists_card_eq
      rw [hn]
      exact fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow h))
    obtain ⟨e, heE, he1, hQe⟩ := exists_ne_one_inf_centralizer_singleton_ne_bot hp hEcard hEexp
      (hEA.trans (le_normalizer_of_mem hQ)) hQsolv hpQ (hne Q hQ)
    set H : Subgroup G := centralizer ({e} : Set G) with hHdef
    have hHtop : H < ⊤ := centralizer_singleton_lt_top hna he1
    have hAH : A ≤ H := fun a ha =>
      mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hEC heE) a ha)
    have hUH : U ≤ H := by
      rw [hUdef, hHdef, Subgroup.zpowers_le]
      exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 huC e (hEA heE)).symm
    have hRH : (R ⊓ H : Subgroup G) ≠ ⊥ := fun h =>
      hUbot (le_bot_iff.1 (h ▸ le_inf hUR hUH))
    exact exists_mem_constrainedCentralizerCore_conj_inv_smul_eq hsolv hAbot hAtop hcon hq hqπ
      hQ hR hHtop hAH hQe hRH
  intro Q₁ hQ₁ Q₂ hQ₂
  obtain ⟨k₁, hk₁, he₁⟩ := main Q₁ hQ₁
  obtain ⟨k₂, hk₂, he₂⟩ := main Q₂ hQ₂
  refine ⟨k₁ * k₂⁻¹, mul_mem hk₁ (inv_mem hk₂), ?_⟩
  have h2 : (MulAut.conj k₂ • R : Subgroup G) = Q₂ := by
    rw [← he₂, smul_smul, ← map_mul]
    simp
  calc MulAut.conj (k₁ * k₂⁻¹)⁻¹ • Q₁
      = MulAut.conj k₂ • (MulAut.conj k₁⁻¹ • Q₁ : Subgroup G) := by
        rw [mul_inv_rev, inv_inv, map_mul, mul_smul]
    _ = Q₂ := by rw [he₁, h2]

theorem exists_mem_constrainedCentralizerCore_conj_inv_smul_eq_of_mulEquiv [Finite G]
    (_hodd : Odd (Nat.card G)) (hsimple : IsSimpleGroup G) (hna : ¬ IsMulCommutative G)
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) {A E : Subgroup G}
    (hAbot : ⊥ < A) (hAtop : A < ⊤) (hcon : IsConstrained A) (hq : q.Prime)
    (hqπ : q ∉ subgroupPrimeSupport A) (hqC : q ∣ Nat.card (centralizer (A : Set G)))
    (hp : p.Prime) (hEZ : E ≤ (Subgroup.center A).map A.subtype)
    (hE : E ≃* Multiplicative (ZMod p × ZMod p)) :
    ∀ Q₁ ∈ maximalNormalizedPSubgroups A q, ∀ Q₂ ∈ maximalNormalizedPSubgroups A q,
      ∃ k ∈ constrainedCentralizerCore A, MulAut.conj k⁻¹ • Q₁ = Q₂ := by
  have := hsimple
  obtain ⟨hEA, hEC⟩ := le_map_center_subtype_iff.1 hEZ
  exact exists_mem_constrainedCentralizerCore_conj_inv_smul_eq_of_natCard_eq_sq hna hsolv hAbot
    hAtop hcon hq hqπ hqC hp hEA hEC (card_eq_sq_of_mulEquiv hE hp)
    fun x hx => by simpa using congrArg Subtype.val (pow_eq_one_of_mulEquiv hE hp ⟨x, hx⟩)

theorem exists_mem_constrainedCentralizerCore_forall_mem_iff_of_mulEquiv [Finite G]
    (hodd : Odd (Nat.card G)) (hsimple : IsSimpleGroup G) (hna : ¬ IsMulCommutative G)
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) {A E : Subgroup G}
    (hAbot : ⊥ < A) (hAtop : A < ⊤) (hcon : IsConstrained A) (hq : q.Prime)
    (hqπ : q ∉ subgroupPrimeSupport A) (hqC : q ∣ Nat.card (centralizer (A : Set G)))
    (hp : p.Prime) (hEZ : E ≤ (Subgroup.center A).map A.subtype)
    (hE : E ≃* Multiplicative (ZMod p × ZMod p)) :
    ∀ Q₁ ∈ maximalNormalizedPSubgroups A q, ∀ Q₂ ∈ maximalNormalizedPSubgroups A q,
      ∃ k ∈ constrainedCentralizerCore A, ∀ x : G, x ∈ Q₂ ↔ k * x * k⁻¹ ∈ Q₁ := by
  intro Q₁ hQ₁ Q₂ hQ₂
  obtain ⟨k, hk, hkeq⟩ := exists_mem_constrainedCentralizerCore_conj_inv_smul_eq_of_mulEquiv hodd
    hsimple hna hsolv hAbot hAtop hcon hq hqπ hqC hp hEZ hE Q₁ hQ₁ Q₂ hQ₂
  exact ⟨k, hk, fun x => by rw [← hkeq, mem_conj_inv_smul_iff]⟩

end

end CFSG.FeitThompson

