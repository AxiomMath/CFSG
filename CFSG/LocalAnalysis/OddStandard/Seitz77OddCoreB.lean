module

public import CFSG.LocalAnalysis.OddStandard.Seitz77OddCoreBFin
public import CFSG.LocalAnalysis.OddStandard.Seitz77OddCoreRep
public import CFSG.LocalAnalysis.OddStandard.Seitz77OddCoreGroup

import CFSG.FeitThompson.OddOrderTheorem
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup Polynomial

theorem oddCore_exists_idempotent {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (m : Module.End (ZMod 2) V) (p : ℕ) (hm : m ^ p = 1) (hp2 : (p : ZMod 2) = 1) :
    ∃ e₀ : Module.End (ZMod 2) V, IsIdempotentElem e₀ ∧ m * e₀ = e₀ ∧ (∀ i : ℕ, m ^ i * e₀ = e₀) ∧
      (∀ t : Module.End (ZMod 2) V, t * m = m * t → t * e₀ = e₀ * t) ∧
      (∀ v, m v = v → e₀ v = v) := by
  refine ⟨∑ i ∈ Finset.range p, m ^ i, ?_⟩
  set e₀ : Module.End (ZMod 2) V := ∑ i ∈ Finset.range p, m ^ i with he₀
  have hme : m * e₀ = e₀ := by
    have h1 : m * e₀ = ∑ i ∈ Finset.range p, m ^ (i + 1) := by
      rw [he₀, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => (pow_succ' m i).symm)
    have h2 : ∑ i ∈ Finset.range (p + 1), m ^ i = ∑ i ∈ Finset.range p, m ^ (i + 1) + 1 := by
      rw [Finset.sum_range_succ']
      simp
    have h3 : ∑ i ∈ Finset.range (p + 1), m ^ i = e₀ + 1 := by
      rw [Finset.sum_range_succ, hm]
    rw [h1]
    exact add_right_cancel (h2.symm.trans h3)
  have hmie : ∀ i : ℕ, m ^ i * e₀ = e₀ := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, mul_assoc, hme, ih]
  have hnsmul : p • e₀ = e₀ := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), hp2, one_smul]
  have hidem : IsIdempotentElem e₀ := by
    show e₀ * e₀ = e₀
    have : e₀ * e₀ = ∑ i ∈ Finset.range p, m ^ i * e₀ := by
      conv_lhs => rw [he₀]
      rw [Finset.sum_mul]
    rw [this]
    simp only [hmie, Finset.sum_const, Finset.card_range]
    exact hnsmul
  refine ⟨hidem, hme, hmie, ?_, ?_⟩
  · intro t ht
    have hti : ∀ i : ℕ, t * m ^ i = m ^ i * t := fun i => (Commute.pow_right ht i)
    rw [he₀, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => hti i)
  · intro v hv
    have hvi : ∀ i : ℕ, (m ^ i) v = v := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => rw [pow_succ, Module.End.mul_apply, hv, ih]
    show (∑ i ∈ Finset.range p, m ^ i) v = v
    rw [LinearMap.sum_apply]
    simp only [hvi, Finset.sum_const, Finset.card_range]
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), hp2, one_smul]

theorem oddCore_false_of_central_prime_order {H : Type*} [Group H] [Finite H]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hV : Module.finrank (ZMod 2) V = 8) (θ : H →* Module.End (ZMod 2) V)
    (hθ : Function.Injective θ) (hperf : commutator H = ⊤) (h25 : 25 ∣ Nat.card H)
    (μ : H) (hμ : ∀ g, g * μ = μ * g) (p : ℕ) (hp : p.Prime) (hμp : orderOf μ = p)
    (hpR : p ∣ 3 ^ 3 * 7 ^ 2 * 17 * 31 * 127) : False := by
  classical
  have hm : θ μ ^ p = 1 := by rw [← map_pow, ← hμp, pow_orderOf_eq_one, map_one]
  have hp' := oddCore_prime_dvd_R_B hp hpR
  have hpodd : Odd p := hp.odd_of_ne_two (by rcases hp' with h | h | h | h | h <;> omega)
  have hp2 : (p : ZMod 2) = 1 := hpodd.natCast_zmod_two
  have hm1 : θ μ ≠ 1 := by
    intro h
    have h1 : μ = 1 := hθ (by rw [h, map_one])
    have h2 : orderOf μ = 1 := orderOf_eq_one_iff.mpr h1
    have := hp.one_lt
    omega
  obtain ⟨e₀, hidem, hme, hmie, hcomm, hfixe⟩ := oddCore_exists_idempotent (θ μ) p hm hp2
  have hcompl : IsCompl (LinearMap.range e₀) (LinearMap.ker e₀) :=
    LinearMap.IsIdempotentElem.isCompl hidem
  have hcomm' : ∀ g : H, θ g * e₀ = e₀ * θ g := fun g =>
    hcomm (θ g) (by rw [← map_mul, ← map_mul, hμ])
  have hC : ∀ g : H, ∀ y ∈ LinearMap.range e₀, θ g y ∈ LinearMap.range e₀ := by
    rintro g y ⟨z, rfl⟩
    refine ⟨θ g z, ?_⟩
    have := congrArg (fun f : Module.End (ZMod 2) V => f z) (hcomm' g)
    simp only [Module.End.mul_apply] at this
    exact this.symm
  have hU : ∀ g : H, ∀ y ∈ LinearMap.ker e₀, θ g y ∈ LinearMap.ker e₀ := by
    intro g y hy
    rw [LinearMap.mem_ker] at hy ⊢
    have := congrArg (fun f : Module.End (ZMod 2) V => f y) (hcomm' g)
    simp only [Module.End.mul_apply] at this
    rw [← this, hy, map_zero]
  let θC : H →* Module.End (ZMod 2) (LinearMap.range e₀) :=
    { toFun := fun g => (θ g).restrict (hC g)
      map_one' := by ext y; simp
      map_mul' := fun g h => by ext y; simp }
  let θU : H →* Module.End (ZMod 2) (LinearMap.ker e₀) :=
    { toFun := fun g => (θ g).restrict (hU g)
      map_one' := by ext y; simp
      map_mul' := fun g h => by ext y; simp }
  have hfixU : ∀ u : LinearMap.ker e₀, θU μ u = u → u = 0 := by
    intro u hu
    have h1 : θ μ u = u := congrArg Subtype.val hu
    have h2 : e₀ u = u := hfixe _ h1
    have h3 : e₀ u = 0 := u.2
    exact Subtype.ext (by rw [← h2, h3]; rfl)
  have hUne : LinearMap.ker e₀ ≠ ⊥ := by
    intro hU0
    apply hm1
    have hinj : ∀ v, e₀ v = v := by
      intro v
      have hmem : e₀ v - v ∈ LinearMap.ker e₀ := by
        rw [LinearMap.mem_ker, map_sub]
        have : e₀ (e₀ v) = e₀ v := by
          simpa using congrArg (fun f : Module.End (ZMod 2) V => f v) hidem
        rw [this, sub_self]
      rw [hU0, Submodule.mem_bot, sub_eq_zero] at hmem
      exact hmem
    have he1 : e₀ = 1 := LinearMap.ext hinj
    rw [he1, mul_one] at hme
    exact hme
  have hab : Module.finrank (ZMod 2) (LinearMap.range e₀) +
      Module.finrank (ZMod 2) (LinearMap.ker e₀) = 8 := by
    rw [Submodule.finrank_add_eq_of_isCompl hcompl, hV]
  have hker : ∀ g : H, θC g = 1 → θU g = 1 → g = 1 := by
    intro g hgC hgU
    apply hθ
    rw [map_one]
    ext v
    have hv : v ∈ LinearMap.range e₀ ⊔ LinearMap.ker e₀ := by
      rw [hcompl.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨c, hc, u, hu, rfl⟩ := Submodule.mem_sup.mp hv
    have h1 : θ g c = c := congrArg (fun f : Module.End (ZMod 2) (LinearMap.range e₀) =>
      ((f ⟨c, hc⟩ : LinearMap.range e₀) : V)) hgC
    have h2 : θ g u = u := congrArg (fun f : Module.End (ZMod 2) (LinearMap.ker e₀) =>
      ((f ⟨u, hu⟩ : LinearMap.ker e₀) : V)) hgU
    simp [map_add, h1, h2]
  let Φ : H →* (Module.End (ZMod 2) (LinearMap.range e₀))ˣ ×
      (Module.End (ZMod 2) (LinearMap.ker e₀))ˣ :=
    (θC.toHomUnits).prod (θU.toHomUnits)
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 := congrArg (fun x => (x.1 : Module.End (ZMod 2) (LinearMap.range e₀))) hg
    have h2 := congrArg (fun x => (x.2 : Module.End (ZMod 2) (LinearMap.ker e₀))) hg
    exact hker g (by simpa [Φ] using h1) (by simpa [Φ] using h2)
  have hdvd := Subgroup.card_dvd_of_injective Φ hΦ
  rw [Nat.card_prod, oddCore_card_units_end _ rfl, oddCore_card_units_end _ rfl] at hdvd
  have h5 := oddCore_eq_of_dvd_gl _ _ hab (h25.trans hdvd)
  have hb : Module.finrank (ZMod 2) (LinearMap.ker e₀) = 4 ∨
      Module.finrank (ZMod 2) (LinearMap.ker e₀) = 8 := by
    have hb0 : Module.finrank (ZMod 2) (LinearMap.ker e₀) ≠ 0 := fun h =>
      hUne (Submodule.finrank_eq_zero.mp h)
    omega
  have : Nontrivial (LinearMap.ker e₀) := Submodule.nontrivial_iff_ne_bot.mpr hUne
  exact oddCore_false_of_central_on_fixedPointFree θU hperf μ hμ p hp hμp hpR _ hb rfl hfixU

theorem odd_core_trivial_B {H : Type*} [Group H] [Finite H]
    (ρ : H →* GL (Fin 8) (ZMod 2)) (hρ : Function.Injective ρ) (hperf : commutator H = ⊤)
    (K₀ : Subgroup H) [K₀.Normal] (hodd : Odd (Nat.card K₀))
    (hcard : Nat.card (H ⧸ K₀) = 3600)
    (hgen : Subgroup.closure {x : H ⧸ K₀ | orderOf x = 5} = ⊤) : K₀ = ⊥ := by
  classical
  by_contra hK₀
  have hHcard : Nat.card H = 3600 * Nat.card K₀ := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup K₀, hcard]
  have hdvd := oddCore_card_dvd_gl_eight ρ hρ
  rw [hHcard] at hdvd
  have hR : Nat.card K₀ ∣ 3 ^ 3 * 7 ^ 2 * 17 * 31 * 127 := oddCore_dvd_R_of_mul_dvd_gl_B hodd hdvd
  have h25 : 25 ∣ Nat.card H := hHcard ▸ Dvd.dvd.mul_right (by norm_num : 25 ∣ 3600) _
  have hcop5 : Nat.Coprime 5 (Nat.card K₀) := by
    refine (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr (fun h5 => ?_)
    have := h5.trans hR
    norm_num at this
  have hsolv : Group.IsSolvable K₀ := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  obtain ⟨M, p, r, hMn, hMK, hp, hr, hMcard⟩ := oddCore_exists_normal_pgroup_le K₀ hK₀
  have hMdvd : Nat.card M ∣ Nat.card K₀ := Subgroup.card_dvd_of_le hMK
  have hMR : p ^ r ∣ 3 ^ 3 * 7 ^ 2 * 17 * 31 * 127 := hMcard ▸ hMdvd.trans hR
  have hpR : p ∣ 3 ^ 3 * 7 ^ 2 * 17 * 31 * 127 := (dvd_pow_self p hr.ne').trans hMR
  have hp5 : p ≠ 5 := by
    intro h
    subst h
    norm_num at hpR
  have hMz : M ≤ Subgroup.center H := by
    by_cases hp31 : p = 31
    · have h1 := oddCore_prime_pow_dvd_R_B hp hr hMR
      have hr1 : r = 1 := by
        rcases h1 with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact absurd hp31 h
      subst hr1
      subst hp31
      exact oddCore_le_center_of_card_prime hperf M (by rw [hMcard]; norm_num)
    · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      have htab : ∀ j, 1 ≤ j → j ≤ r → p ^ j % 5 ≠ 1 := fun j hj hjr => by
        rcases oddCore_prime_pow_dvd_R_B hp hj ((pow_dvd_pow p hjr).trans hMR) with ⟨h, _⟩ | ⟨_, h⟩
        · exact absurd h hp31
        · exact h
      have hcent : ∀ x : H, orderOf x = 5 → x ∈ Subgroup.centralizer (M : Set H) := fun x hx =>
        oddCore_mem_centralizer_of_pow_eq_one M x 5 (hx ▸ pow_orderOf_eq_one x) p r hp hp5 hMcard
          htab
      have hsup := oddCore_sup_eq_top_of_order_five K₀ hcop5 hgen
        (Subgroup.centralizer (M : Set H)) hcent
      exact oddCore_le_center_of_sup_eq_top hperf K₀ M hsup
  have hpM : p ∣ Nat.card M := hMcard ▸ dvd_pow_self p hr.ne'
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨μ', hμ'⟩ := exists_prime_orderOf_dvd_card' p hpM
  have hμp : orderOf (μ' : H) = p := by rw [Subgroup.orderOf_coe]; exact hμ'
  have hμc : ∀ g, g * (μ' : H) = (μ' : H) * g := fun g =>
    Subgroup.mem_center_iff.mp (hMz μ'.2) g
  exact oddCore_false_of_central_prime_order oddCore_finrank_fin_eight_fun (oddCoreRep ρ)
    (oddCoreRep_injective ρ hρ)
    hperf h25 (μ' : H) hμc p hp hμp hpR

end CFSG.OddStandard.Seitz77
