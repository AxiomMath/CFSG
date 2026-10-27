module

public import CFSG.FeitThompson.Local.ReducedKernelExponentPrimeSpecial
public import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
import CFSG.FeitThompson.Local.PrimeCentralizerAbelianCommutatorConjugates
import CFSG.FeitThompson.Local.TwoPrimeComplementFaithfulAction
import CFSG.FeitThompson.Local.FixedOrderElementaryAbelianCover
import CFSG.FeitThompson.Local.OddRankTwoAutomorphismDerivedPrimePower
import CFSG.FeitThompson.Foundations.MinimalNormalInFittingCenter

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Matrix Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

theorem isMulCommutative_GL_of_le_one {q e : ℕ} (he : e ≤ 1) :
    IsMulCommutative (GL (Fin e) (ZMod q)) := by
  interval_cases e
  · exact ⟨⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩⟩
  · exact isMulCommutative_generalLinearGroup_one (ZMod q)

theorem isMulCommutative_subgroup_GL_of_le_two {q e : ℕ} (hq : q.Prime) (he : e ≤ 2)
    {S : Subgroup (GL (Fin e) (ZMod q))} (hodd : Odd (Nat.card S)) (hnd : ¬ q ∣ Nat.card S) :
    IsMulCommutative S := by
  rcases Nat.lt_or_ge e 2 with h | h
  · have := isMulCommutative_GL_of_le_one (q := q) (Nat.lt_succ_iff.1 h)
    infer_instance
  · have : e = 2 := le_antisymm he h
    subst this
    exact isMulCommutative_of_odd_of_not_dvd_prime_field hq hodd hnd

variable {G : Type u} [Group G] [Finite G]

namespace IsReducedPrimeCentralizerKernel

variable {p q : ℕ} {H R R0 V K U N P : Subgroup G}
  (hc : IsReducedPrimeCentralizerKernel p q H R R0 V K U N P)

include hc

theorem false_of_injective_of_mulEquiv_pi {W : Type*} [Group W]
    (σ : ↥(P ⊔ R) →* MulAut W) (hσ : Function.Injective σ)
    {e : ℕ} (he : e ≤ 2) (φ : W ≃* (Fin e → Multiplicative (ZMod q))) : False := by
  classical
  let ψ : W ≃* Multiplicative (Fin e → ZMod q) :=
    φ.trans (MulEquiv.piMultiplicative (fun _ : Fin e => ZMod q)).symm
  let ρ : ↥(P ⊔ R) →* GL (Fin e) (ZMod q) := (mulAutMulEquivGL W ψ).toMonoidHom.comp σ
  have hρ : Function.Injective ρ := (mulAutMulEquivGL W ψ).injective.comp hσ
  have hcard : Nat.card ρ.range = Nat.card ↥(P ⊔ R) :=
    (Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv).symm
  have hcomm : IsMulCommutative ρ.range :=
    isMulCommutative_subgroup_GL_of_le_two hc.prime_q he
      (hcard ▸ hc.admissible.odd_card_subgroup (P ⊔ R))
      (hcard ▸ hc.not_dvd_natCard_sup)
  have hab : ∀ a b : ↥(P ⊔ R), (a : G) * b = (b : G) * a := by
    intro a b
    have h := hcomm.is_comm.comm (MonoidHom.ofInjective hρ a) (MonoidHom.ofInjective hρ b)
    have h2 : a * b = b * a := (MonoidHom.ofInjective hρ).injective (by rw [map_mul, map_mul, h])
    exact congrArg Subtype.val h2
  refine hc.P_ne_bot ?_
  rw [hc.P_eq_commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  exact Subgroup.mem_centralizer_iff.2 fun y hy =>
    hab ⟨y, (le_sup_right : R ≤ P ⊔ R) hy⟩ ⟨x, (le_sup_left : P ≤ P ⊔ R) hx⟩

theorem index_center_dvd_sq : (Subgroup.center ↥K).index ∣ q ^ 2 := by
  obtain ⟨x, hxP, hne⟩ := hc.exists_conj_ne
  have hle : ((⁅K, R⁆ : Subgroup G) ⊓ (MulAut.conj x⁻¹ • (⁅K, R⁆ : Subgroup G) : Subgroup G)
      : Subgroup G).subgroupOf K ≤ Subgroup.center ↥K := by
    have h := hc.inf_conj_le_center hxP hne
    intro y hy
    have hy' : (y : G) ∈ K ⊓ centralizer (K : Set G) := h (Subgroup.mem_subgroupOf.1 hy)
    rw [← map_center_subtype_eq_inf_centralizer K] at hy'
    obtain ⟨z, hz, hzy⟩ := hy'
    exact (Subtype.ext hzy : z = y) ▸ hz
  exact (Subgroup.index_dvd_of_le hle).trans (dvd_of_eq (hc.index_inf_conj hxP hne))

theorem isMulCommutative_K : IsMulCommutative ↥K := by
  by_contra hnc
  rcases hc.elementaryAbelian_or_special with ⟨d, -, ⟨f⟩⟩ | ⟨hZ, hC⟩
  · exact hnc (IsMulCommutative.of_comm fun a b =>
      f.injective (by simpa using mul_comm (f a) (f b)))
  · have hZΦ : (frattini ↥K).index ∣ q ^ 2 := by
      rw [← hZ.trans hC]; exact hc.index_center_dvd_sq
    obtain ⟨e, hecard, ⟨φ⟩⟩ := hc.exists_mulEquiv_quotient_frattini
    have hdvd : q ^ e ∣ q ^ 2 := by
      rw [← hecard, ← Subgroup.index_eq_card]; exact hZΦ
    exact hc.false_of_injective_of_mulEquiv_pi (frattiniQuotientAction hc.action)
      hc.injective_frattiniQuotientAction
      ((Nat.pow_dvd_pow_iff_le_right hc.prime_q.one_lt).1 hdvd) φ

theorem isElementaryAbelian_K : IsElementaryAbelian q K :=
  isElementaryAbelian_iff.2 ⟨hc.isMulCommutative_K, fun _ hx => hc.pow_eq_one hx⟩

theorem exists_natCard_eq_pow_mulEquiv_pi : ∃ d, Nat.card ↥K = q ^ d ∧
    Nonempty (↥K ≃* (Fin d → Multiplicative (ZMod q))) := by
  have := Fact.mk hc.prime_q
  obtain ⟨d, hd⟩ := hc.isPGroup_K.exists_card_eq
  have := hc.isMulCommutative_K
  let _ : CommGroup ↥K := IsMulCommutative.instCommGroup
  exact ⟨d, hd, nonempty_mulEquiv_pi_of_exponent hc.prime_q
    (fun x => Subtype.ext (by simpa using hc.pow_eq_one x.2)) hd⟩

theorem three_le_of_natCard_eq_pow {d : ℕ} (hd : Nat.card ↥K = q ^ d) : 3 ≤ d := by
  by_contra hlt
  obtain ⟨d', hd', ⟨φ⟩⟩ := hc.exists_natCard_eq_pow_mulEquiv_pi
  have : d' = d := Nat.pow_right_injective hc.prime_q.two_le (hd'.symm.trans hd)
  subst this
  exact hc.false_of_injective_of_mulEquiv_pi hc.action hc.injective_action (by omega) φ

theorem three_le_elementaryAbelianPRank_K : 3 ≤ elementaryAbelianPRank q ↥K := by
  obtain ⟨d, hd, -⟩ := hc.exists_natCard_eq_pow_mulEquiv_pi
  exact le_trans (hc.three_le_of_natCard_eq_pow hd)
    (hc.isElementaryAbelian_K.le_elementaryAbelianPRank hc.prime_q hd le_rfl)

theorem primeCentralizerElementaryKernel :
    IsElementaryAbelian q K ∧ ∃ d, 3 ≤ d ∧ Nat.card ↥K = q ^ d ∧
      Nonempty (↥K ≃* (Fin d → Multiplicative (ZMod q))) := by
  obtain ⟨d, hd, hφ⟩ := hc.exists_natCard_eq_pow_mulEquiv_pi
  exact ⟨hc.isElementaryAbelian_K, d, hc.three_le_of_natCard_eq_pow hd, hd, hφ⟩

end IsReducedPrimeCentralizerKernel

end CFSG.FeitThompson

end
