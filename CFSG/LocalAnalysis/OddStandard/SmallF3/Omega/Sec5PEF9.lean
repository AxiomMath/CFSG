module

public import CFSG.GH74.GLS.IVK.Defs
import CFSG.GH74.GLS.IVK.L2.Lemma14j
import CFSG.Walter.PSL2Facts.FieldAut
import CFSG.Walter.Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.GH74.GLS.IVK
open CFSG.GorensteinWalter CFSG.Walter

theorem sec5pef_outer_prime_order
    {F : Type} [Field F] [Finite F] (hF : L2Field F) {K : Type} [Group K] (e : K ≃* L2 F)
    {x : MulAut K} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hx : orderOf x = r)
    (hout : x ∉ innDiagSub e) :
    ∃ q₁ : ℕ, Odd q₁ ∧ 3 ≤ q₁ ∧ Nat.card F = q₁ ^ r ∧
      Nat.card ↥(x.toMonoidHom.eqLocus (MonoidHom.id K)) ∣ q₁ * (q₁ ^ 2 - 1) := by
  classical
  set ψ : F ≃+* F := fieldProj e x with hψ
  have hψne : ψ ≠ 1 := by
    intro h
    exact hout ((mem_innDiagSub_iff e x).mpr (by rw [← hψ, h]))
  have hψdvd : orderOf ψ ∣ r := by
    have h := orderOf_map_dvd (fieldProj e) x
    rwa [hx, ← hψ] at h
  have hψord : orderOf ψ = r := by
    rcases (Nat.dvd_prime hr).mp hψdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hψne
    · exact h
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  have hψodd : Odd (orderOf ψ) := hψord ▸ hrodd
  have hxpow : x ^ orderOf (fieldProj e x) = 1 := by
    rw [← hψ, hψord, ← hx]
    exact pow_orderOf_eq_one x
  obtain ⟨c, -, hconj⟩ := exists_conj_fieldAutHom e x hxpow
  rw [← hψ] at hconj
  have hconj' : ∀ y : K, fieldAutHom e ψ y = (c⁻¹ : MulAut K) (x (c y)) := by
    intro y
    have h := congrArg (fun f : MulAut K => f y) hconj
    simpa using h.symm
  have hcard_fix :
      Nat.card ↥(x.toMonoidHom.eqLocus (MonoidHom.id K)) =
        Nat.card ↥((fieldAutHom e ψ).toMonoidHom.eqLocus (MonoidHom.id K)) := by
    refine Nat.card_congr (Equiv.subtypeEquiv (c⁻¹).toEquiv ?_)
    intro k
    change x k = k ↔ fieldAutHom e ψ (c⁻¹ k) = c⁻¹ k
    constructor
    · intro hk
      rw [hconj', MulAut.apply_inv_self, hk]
    · intro hk
      have h := hconj' (c⁻¹ k)
      rw [MulAut.apply_inv_self] at h
      exact (c⁻¹).injective (h.symm.trans hk)
  have hcard_psl :
      Nat.card ↥((fieldAutHom e ψ).toMonoidHom.eqLocus (MonoidHom.id K)) =
        Nat.card {y : PSL2 F // psl2FieldAut F ψ y = y} := by
    refine Nat.card_congr (Equiv.subtypeEquiv (toPSL e).toEquiv ?_)
    intro k
    change fieldAutHom e ψ k = k ↔ psl2FieldAut F ψ (toPSL e k) = toPSL e k
    constructor
    · intro hk
      rw [← toPSL_fieldAutHom e ψ k, hk]
    · intro hk
      exact (toPSL e).injective (by rw [toPSL_fieldAutHom e ψ k, hk])
  let F0 : Subfield F := FixedPoints.subfield (Subgroup.zpowers ψ) F
  have hcard_range :
      Nat.card {y : PSL2 F // psl2FieldAut F ψ y = y} =
        Nat.card ↥(psl2Map F0.subtype).range := by
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl (PSL2 F)) ?_)
    intro y
    rw [psl2FieldAut_eq_psl2Map]
    exact psl2Map_eq_self_iff ψ hψodd y
  have hcard_PSL : Nat.card ↥(psl2Map F0.subtype).range = Nat.card (PSL2 F0) :=
    (Nat.card_congr (MonoidHom.ofInjective (f := psl2Map F0.subtype)
      (psl2Map_injective F0.subtype)).toEquiv).symm
  have hdvd_PSL : Nat.card (PSL2 F0) ∣ Nat.card F0 * (Nat.card F0 ^ 2 - 1) := by
    have h1 := Subgroup.card_quotient_dvd_card
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F0))
    rw [sl2_card_formula F0] at h1
    exact h1
  haveI : Finite (F ≃+* F) :=
    Finite.of_injective (fun τ : F ≃+* F => (τ : F → F))
      (fun a b h => RingEquiv.ext (congrFun h))
  haveI : Fintype (Subgroup.zpowers ψ) := Fintype.ofFinite _
  have hfinrank : Module.finrank F0 F = orderOf ψ := by
    show Module.finrank (FixedPoints.subfield (Subgroup.zpowers ψ) F) F = orderOf ψ
    rw [FixedPoints.finrank_eq_card, Fintype.card_eq_nat_card, Nat.card_zpowers]
  have hcard_pow : Nat.card F = Nat.card F0 ^ orderOf ψ := by
    rw [← hfinrank]
    exact Module.natCard_eq_pow_finrank
  have hcardF : Nat.card F = Nat.card F0 ^ r := by
    rw [hcard_pow, hψord]
  have hq1odd : Odd (Nat.card F0) := by
    have h1 : Odd (Nat.card F0 ^ r) := hcardF ▸ hF.1
    exact (Nat.odd_pow_iff hr.pos.ne').mp h1
  have hq1ge3 : 3 ≤ Nat.card F0 := by
    have hgt : 3 < Nat.card F0 ^ r := hcardF ▸ hF.2
    have hpos : 0 < Nat.card F0 := by
      rcases Nat.eq_zero_or_pos (Nat.card F0) with h | h
      · exfalso
        rw [h, zero_pow hr.pos.ne'] at hgt
        exact absurd hgt (by norm_num)
      · exact h
    have hne1 : Nat.card F0 ≠ 1 := by
      intro h
      have h1 : 3 < Nat.card F0 ^ r := hcardF ▸ hF.2
      rw [h, one_pow] at h1
      exact absurd h1 (by norm_num)
    obtain ⟨k, hk⟩ := hq1odd
    have hk0 : k ≠ 0 := by
      intro hk0
      apply hne1
      rw [hk, hk0]
      norm_num
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    calc 3 = 2 * 1 + 1 := by norm_num
      _ ≤ 2 * k + 1 := Nat.add_le_add_right (Nat.mul_le_mul_left 2 hk1) 1
      _ = Nat.card F0 := hk.symm
  refine ⟨Nat.card F0, hq1odd, hq1ge3, hcardF, ?_⟩
  rw [hcard_fix, hcard_psl, hcard_range, hcard_PSL]
  exact hdvd_PSL

end CFSG.OddStandard.SmallF3.Omega
