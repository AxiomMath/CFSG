module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Torsion

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.SectionRank.Ccomm

open Subgroup CFSG.Open CFSG.SectionRank

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
theorem not_sq_dvd_card_GL_two (hp' : p.Prime) : ¬ p ^ 2 ∣ (p ^ 2 - 1) * (p ^ 2 - p) := by
  intro h
  have hp2 := hp'.two_le
  have e : p ^ 2 - p = p * (p - 1) := by rw [Nat.mul_sub_one, sq]
  rw [e, mul_left_comm] at h
  have h1 : p ∣ (p ^ 2 - 1) * (p - 1) :=
    Nat.dvd_of_mul_dvd_mul_left hp'.pos (by simpa [sq] using h)
  rcases (Nat.Prime.dvd_mul hp').1 h1 with h2 | h2
  · rw [show p ^ 2 - 1 = (p + 1) * (p - 1) by rw [← Nat.sq_sub_sq, one_pow]] at h2
    rcases (Nat.Prime.dvd_mul hp').1 h2 with h3 | h3
    · have := (Nat.dvd_add_right (dvd_refl p)).1 h3
      exact hp'.one_lt.ne' (Nat.dvd_one.1 this)
    · have := Nat.le_of_dvd (by omega) h3
      omega
  · have := Nat.le_of_dvd (by omega) h2
    omega

theorem pow_le_of_dvd_card_mulAut {W : Type*} [Group W] [Finite W]
    (hcomm : ∀ a b : W, a * b = b * a) (hpow : ∀ a : W, a ^ p = 1) {d : ℕ}
    (hcard : Nat.card W = p ^ d) (hd : d ≤ 2) {k : ℕ} (hk : p ^ k ∣ Nat.card (MulAut W)) :
    k ≤ 1 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hcomm hpow hcard
  rw [card_mulAut_eq_card_GL e, card_GL_zmod] at hk
  have hp2 := hp.out.two_le
  by_contra hk1
  have hsq : p ^ 2 ∣ p ^ k := pow_dvd_pow p (by omega)
  interval_cases d
  · simp at hk
    omega
  · simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.val_zero, pow_zero, pow_one,
      Finset.prod_singleton] at hk
    have := Nat.le_of_dvd (by omega) (hsq.trans hk)
    have : p ≤ p ^ 2 := Nat.le_self_pow (by norm_num) p
    omega
  · rw [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one] at hk
    exact not_sq_dvd_card_GL_two hp.out (hsq.trans hk)

theorem rank_two_exponent_prime_order_bound {R : Type*} [Group R] [Finite R] (hR : IsPGroup p R)
    (hexp : ∀ x : R, x ^ p = 1) (hrank : pRank p (⊤ : Subgroup R) ≤ 2) :
    Nat.card R ≤ p ^ 3 ∧ Nat.card (R ⧸ frattini R) ≤ p ^ 2 := by
  have hp1 := hp.out.one_lt
  let S : Set (Subgroup R) := {B | B.Normal ∧ ∀ x ∈ B, ∀ y ∈ B, x * y = y * x}
  obtain ⟨D, hDmax⟩ := S.toFinite.exists_maximal ⟨⊥, inferInstance, fun x hx y hy => by
    rw [mem_bot.1 hx, mem_bot.1 hy]⟩
  obtain ⟨hDn, hDab⟩ := hDmax.prop
  have hcen : centralizer (D : Set R) = D :=
    maximal_abelian_normal_self_centralizing hR hDab fun B hBn hBab hDB =>
      le_antisymm (hDmax.2 ⟨hBn, hBab⟩ hDB) hDB
  obtain ⟨d, hd⟩ := (hR.to_subgroup D).exists_card_eq
  have hDel : IsElemAbelian p D := ⟨⟨⟨fun a b => Subtype.ext (hDab _ a.2 _ b.2)⟩⟩,
    fun x _ => hexp x⟩
  have hd2 : d ≤ 2 := (le_pRank hp1 le_top hDel hd).trans hrank
  set c : R →* MulAut D := MulAut.conjNormal with hc
  have hker : c.ker = D := by
    refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
    · rw [MonoidHom.mem_ker] at hg
      rw [← hcen, mem_centralizer_iff]
      intro a ha
      have := congrArg (fun φ : MulAut D => ((φ ⟨a, ha⟩ : D) : R)) hg
      simp only [hc, MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc a * g = g * a * g⁻¹ * g := by rw [this]
        _ = g * a := by group
    · rw [MonoidHom.mem_ker]
      ext a
      rw [MulAut.one_apply, hc, MulAut.conjNormal_apply, hDab g hg a a.2, mul_inv_cancel_right]
  have hcardR : Nat.card R = Nat.card c.range * p ^ d := by
    rw [card_eq_card_quotient_mul_card_subgroup c.ker, hker, hd,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange c).toEquiv.symm, hker]
  obtain ⟨k, hk⟩ := (hR.to_quotient c.ker).exists_card_eq
  have hrange : Nat.card c.range = p ^ k := by
    rw [← hk]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange c).toEquiv.symm
  have hk1 : k ≤ 1 := by
    have hdvd : p ^ k ∣ Nat.card (MulAut D) := hrange ▸ card_subgroup_dvd_card c.range
    exact pow_le_of_dvd_card_mulAut (fun a b => Subtype.ext (hDab _ a.2 _ b.2))
      (fun a => Subtype.ext (by rw [coe_pow, hexp, coe_one])) hd hd2 hdvd
  have hRle : Nat.card R ≤ p ^ 3 := by
    rw [hcardR, hrange, ← pow_add]
    exact Nat.pow_le_pow_right hp.out.pos (by omega)
  refine ⟨hRle, ?_⟩
  by_cases hab : ∀ a b : R, a * b = b * a
  ·
    have hel : IsElemAbelian p (⊤ : Subgroup R) :=
      ⟨⟨⟨fun a b => Subtype.ext (hab _ _)⟩⟩, fun x _ => hexp x⟩
    obtain ⟨r, hr⟩ := hR.exists_card_eq
    have hr' : Nat.card (⊤ : Subgroup R) = p ^ r := by rw [card_top, hr]
    have hr2 : r ≤ 2 := (le_pRank hp1 le_rfl hel hr').trans hrank
    calc Nat.card (R ⧸ frattini R) ≤ Nat.card R :=
          Nat.le_of_dvd Nat.card_pos (card_quotient_dvd_card _)
      _ = p ^ r := hr
      _ ≤ p ^ 2 := Nat.pow_le_pow_right hp.out.pos hr2
  ·
    have hΦ : frattini R ≠ ⊥ := fun h => hab ((frattini_eq_bot_iff hR).1 h).1
    obtain ⟨j, hj⟩ := (hR.to_subgroup (frattini R)).exists_card_eq
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, card_eq_one] at hj
      exact hΦ hj
    obtain ⟨a, ha⟩ := (hR.to_quotient (frattini R)).exists_card_eq
    have htot := card_eq_card_quotient_mul_card_subgroup (frattini R)
    rw [ha, hj, ← pow_add] at htot
    have : a + j ≤ 3 := by
      have h3 := htot ▸ hRle
      exact (Nat.pow_le_pow_iff_right hp1).1 h3
    rw [ha]
    exact Nat.pow_le_pow_right hp.out.pos (by omega)

end CFSG.SectionRank.Ccomm
