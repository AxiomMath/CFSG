module

public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
import CFSG.LinearAlgebra.SL2MinimalFaithful

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem JStarHyp.false_of_constrained {Y : Type} [Group Y] [Finite Y] {p n : ℕ} [Fact p.Prime]
    {Rb : Sylow p Y} {Y₀ Jt Xt : Subgroup Y} {φ : Jt →* PSL2GF p n}
    (h : JStarHyp p n Rb Y₀ Jt Xt φ)
    (hcon : ∃ O : Subgroup Y, O.Normal ∧ IsPGroup p O ∧ Subgroup.centralizer (O : Set Y) ≤ O) :
    False := by
  obtain ⟨O, hOn, hOp, hOC⟩ := hcon
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; have := h.ne_two; omega
  have hn := h.three_le
  obtain ⟨ℓ, hℓ, hℓdvd, hprim⟩ :=
    CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one (a := p) (n := 2 * n) hp3
      (by omega)
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓp : ℓ ≠ p := by
    rintro rfl
    have h1 : ℓ ∣ ℓ ^ (2 * n) := dvd_pow_self ℓ (by omega)
    have h2 := Nat.dvd_sub h1 hℓdvd
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hℓ.pos)] at h2
    exact hℓ.one_lt.ne' (Nat.dvd_one.mp h2)
  have hℓJ : ℓ ∣ Nat.card Jt :=
    (prime_dvd_card_psl2GF h.ne_two (by omega) hℓ hℓdvd hprim).trans
      (Subgroup.card_dvd_of_surjective (f := φ) h.surj)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' ℓ hℓJ
  let ρ : Jt →* MulAut O := (MulAut.conjNormal : Y →* MulAut O).comp Jt.subtype
  have hρg : ρ g ≠ 1 := by
    intro h1
    have hgC : (g : Y) ∈ Subgroup.centralizer (O : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro o ho
      have := congrArg (fun f : MulAut O => ((f ⟨o, ho⟩ : O) : Y)) h1
      simp only [ρ, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc o * (g : Y) = (g : Y) * o * (g : Y)⁻¹ * g := by rw [this]
        _ = (g : Y) * o := by group
    obtain ⟨k, hk⟩ := hOp ⟨g, hOC hgC⟩
    have hord : orderOf (g : Y) ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by
      simpa using congrArg Subtype.val hk)
    rw [Subgroup.orderOf_coe, hg] at hord
    exact hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow hord))
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp hOp
  have hd2 : d < 2 * n := by
    have h1 := Nat.le_of_dvd (Nat.mul_pos (pow_pos hp.pos n) (by omega)) (hd ▸ h.card_dvd O hOp)
    have h2 : p ^ n * n < p ^ n * p ^ n :=
      Nat.mul_lt_mul_of_pos_left (Nat.lt_pow_self hp.one_lt) (pow_pos hp.pos n)
    rw [← pow_add, show n + n = 2 * n by ring] at h2
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp (lt_of_le_of_lt h1 h2)
  obtain ⟨e, hed, hdvd⟩ := CFSG.SL2MinimalFaithful.exists_dvd_pow_sub_pow hp hℓ ρ hg hρg hd
  have hfac : p ^ d - p ^ e = p ^ e * (p ^ (d - e) - 1) := by
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hed.le]
  rw [hfac] at hdvd
  have hℓpe : ¬ ℓ ∣ p ^ e := fun h' =>
    hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow h'))
  exact hprim (d - e) (by omega) (by omega)
    (Nat.Coprime.dvd_of_dvd_mul_left ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓpe) hdvd)

theorem jStarO1 : StmtJStarO1 := fun h hcon => h.false_of_constrained hcon

end CFSG.AGLEmbedding
