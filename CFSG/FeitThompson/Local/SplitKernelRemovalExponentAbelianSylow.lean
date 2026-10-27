module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Complement
import CFSG.FeitThompson.Foundations.SylowExponentPrimePart
import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise

variable {U : Type*} [Group U] {p q : ℕ}

theorem natCard_sup_eq_mul_of_normal_of_inf_eq_bot {A T : Subgroup U} [A.Normal]
    (h : A ⊓ T = ⊥) : Nat.card (A ⊔ T : Subgroup U) = Nat.card A * Nat.card T := by
  have h2 := natCard_mul_mul_natCard_inf A T
  rw [← Subgroup.normal_mul A T, h] at h2
  simpa using h2

theorem exponent_dvd_exponent_of_le {H K : Subgroup U} (h : H ≤ K) :
    Monoid.exponent H ∣ Monoid.exponent K :=
  Monoid.exponent_dvd_of_monoidHom (Subgroup.inclusion h) (Subgroup.inclusion_injective h)

theorem exists_subgroup_le_natCard_eq_pow_factorization [Finite U] (hq : q.Prime)
    (V : Subgroup U) :
    ∃ T : Subgroup U, T ≤ V ∧ Nat.card T = q ^ (Nat.card V).factorization q := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow q V))
  refine ⟨(P : Subgroup V).map V.subtype, Subgroup.map_subtype_le _, ?_⟩
  rw [Subgroup.card_map_of_injective V.subtype_injective, P.card_eq_multiplicity]

theorem isMulCommutative_conj_smul (g : U) (P : Subgroup U) [IsMulCommutative P] :
    IsMulCommutative ((MulAut.conj g • P : Subgroup U)) := by
  refine IsMulCommutative.of_setLike_mul_comm fun x hx y hy => ?_
  obtain ⟨a, ha, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists x _ P).mp hx
  obtain ⟨b, hb, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists y _ P).mp hy
  have hab : a * b = b * a := setLike_mul_comm ha hb
  simp only [MulAut.smul_def, MulAut.conj_apply]
  calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
    _ = g * (b * a) * g⁻¹ := by rw [hab]
    _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group

theorem isMulCommutative_of_natCard_eq_pow_factorization [Finite U] [Fact p.Prime]
    {S : Subgroup U} (hSab : IsMulCommutative S)
    (hS : Nat.card S = p ^ (Nat.card U).factorization p)
    {Q : Subgroup U} (hQ : Nat.card Q = p ^ (Nat.card U).factorization p) :
    IsMulCommutative Q := by
  obtain ⟨g, hg⟩ := exists_conj_smul_eq hS hQ
  rw [← hg]
  exact isMulCommutative_conj_smul g S

theorem exponent_sup_dvd_lcm {A T : Subgroup U} [A.Normal]
    (hab : IsMulCommutative (A ⊔ T : Subgroup U)) :
    Monoid.exponent (A ⊔ T : Subgroup U) ∣ Nat.lcm (Monoid.exponent A) (Monoid.exponent T) := by
  rw [Monoid.exponent_dvd]
  intro g
  have hg : (g : U) ∈ ((A ⊔ T : Subgroup U) : Set U) := g.2
  rw [Subgroup.normal_mul A T] at hg
  obtain ⟨a, ha, t, ht, hat⟩ := Set.mem_mul.mp hg
  have hcomm : Commute a t :=
    setLike_mul_comm (S := Subgroup U) (s := A ⊔ T)
      (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right ht)
  have h1 : orderOf g = orderOf (a * t) := by rw [← Subgroup.orderOf_coe g, hat]
  rw [h1]
  refine dvd_trans hcomm.orderOf_mul_dvd_lcm (Nat.lcm_dvd ?_ ?_)
  · exact dvd_trans (orderOf_dvd_exponent_of_mem ha) (Nat.dvd_lcm_left _ _)
  · exact dvd_trans (orderOf_dvd_exponent_of_mem ht) (Nat.dvd_lcm_right _ _)

theorem pow_dvd_of_sylow_exponent_dvd [Finite U] (hq : q.Prime) {T : Subgroup U} {n k : ℕ}
    (hT : Nat.card T = q ^ (Nat.card U).factorization q) (hn : Monoid.exponent T ∣ n)
    (hk : q ^ k ∣ Monoid.exponent U) : q ^ k ∣ n := by
  have hexp : Monoid.exponent U ≠ 0 := Monoid.ExponentExists.exponent_ne_zero .of_finite
  have hkle : k ≤ (Monoid.exponent U).factorization q :=
    (hq.pow_dvd_iff_le_factorization hexp).mp hk
  refine dvd_trans (dvd_trans (pow_dvd_pow q hkle) ?_) hn
  rw [exponent_eq_pow_factorization_exponent hq hT]

theorem dvd_exponent_of_dvd_natCard [Finite U] (hq : q.Prime) {T : Subgroup U}
    (h : q ∣ Nat.card T) : q ∣ Monoid.exponent T := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := T) q h
  exact hx ▸ Monoid.order_dvd_exponent x

theorem exponent_eq_of_natCard_eq_prime [Finite U] [Fact p.Prime] {A V S : Subgroup U} [A.Normal]
    (hA : Nat.card A = p) (hsup : A ⊔ V = ⊤) (hinf : A ⊓ V = ⊥) (hpV : p ∣ Nat.card V)
    (hS : Nat.card S = p ^ (Nat.card U).factorization p) (hSab : IsMulCommutative S) :
    Monoid.exponent V = Monoid.exponent U := by
  have hp : p.Prime := Fact.out
  have hV0 : Nat.card V ≠ 0 := Nat.card_pos.ne'
  have hUcard : Nat.card U = p * Nat.card V := by
    have h := natCard_sup_eq_mul_of_normal_of_inf_eq_bot (A := A) (T := V) hinf
    rwa [hsup, Subgroup.card_top, hA] at h
  refine Nat.dvd_antisymm (exponent_subgroup_dvd V) ?_
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro r k hr hrk
  obtain ⟨T, hTV, hT⟩ := exists_subgroup_le_natCard_eq_pow_factorization hr V
  by_cases hrp : r = p
  ·
    subst hrp
    have hvpos : 1 ≤ (Nat.card V).factorization r :=
      (hr.pow_dvd_iff_le_factorization hV0).mp (by simpa using hpV)
    have hAT : A ⊓ T = ⊥ := le_bot_iff.mp (hinf ▸ inf_le_inf_left A hTV)
    have hcard : Nat.card (A ⊔ T : Subgroup U) = r ^ (Nat.card U).factorization r := by
      rw [natCard_sup_eq_mul_of_normal_of_inf_eq_bot hAT, hA, hT, hUcard,
        Nat.factorization_mul hr.pos.ne' hV0]
      simp only [Finsupp.add_apply, hr.factorization_self]
      rw [pow_add, pow_one]
    have hATab : IsMulCommutative (A ⊔ T : Subgroup U) :=
      isMulCommutative_of_natCard_eq_pow_factorization hSab hS hcard
    have hrT : r ∣ Monoid.exponent T := by
      refine dvd_exponent_of_dvd_natCard hr ?_
      rw [hT]
      exact dvd_pow_self r (by omega)
    have hsupT : Monoid.exponent (A ⊔ T : Subgroup U) ∣ Monoid.exponent T := by
      refine dvd_trans (exponent_sup_dvd_lcm hATab) (Nat.lcm_dvd ?_ dvd_rfl)
      exact dvd_trans (hA ▸ Group.exponent_dvd_nat_card) hrT
    exact pow_dvd_of_sylow_exponent_dvd hr hcard
      (hsupT.trans (exponent_dvd_exponent_of_le hTV)) hrk
  ·
    have hTU : Nat.card T = r ^ (Nat.card U).factorization r := by
      rw [hT, hUcard, Nat.factorization_mul hp.pos.ne' hV0]
      simp [Nat.factorization_eq_zero_of_not_dvd
        (fun hd => hrp ((Nat.prime_dvd_prime_iff_eq hr hp).mp hd))]
    exact pow_dvd_of_sylow_exponent_dvd hr hTU (exponent_dvd_exponent_of_le hTV) hrk

theorem exponent_eq_of_sylow_isMulCommutative [Finite U] [Fact p.Prime] {A V : Subgroup U}
    [A.Normal] (S : Sylow p U) (hA : Nat.card A = p) (hsup : A ⊔ V = ⊤) (hinf : A ⊓ V = ⊥)
    (hpV : p ∣ Nat.card V) (hSab : IsMulCommutative (S : Subgroup U)) :
    Monoid.exponent V = Monoid.exponent U :=
  exponent_eq_of_natCard_eq_prime hA hsup hinf hpV S.card_eq_multiplicity hSab

theorem exponent_eq_of_isComplement' [Finite U] [Fact p.Prime] {A V : Subgroup U} [A.Normal]
    (S : Sylow p U) (hA : Nat.card A = p) (hAV : Subgroup.IsComplement' A V)
    (hpV : p ∣ Nat.card V) (hSab : IsMulCommutative (S : Subgroup U)) :
    Monoid.exponent V = Monoid.exponent U :=
  exponent_eq_of_sylow_isMulCommutative S hA hAV.sup_eq_top
    (disjoint_iff.mp hAV.disjoint) hpV hSab

theorem coe_mul_eq_univ_iff_sup_eq_top {A V : Subgroup U} [A.Normal] :
    (A : Set U) * (V : Set U) = Set.univ ↔ A ⊔ V = ⊤ := by
  rw [← Subgroup.normal_mul A V, Subgroup.coe_eq_univ]

end

end CFSG.FeitThompson
