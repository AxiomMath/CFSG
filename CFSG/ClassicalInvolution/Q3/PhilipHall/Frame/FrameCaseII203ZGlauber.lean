module

public import CFSG.Adapters.Involutions
public import CFSG.ClassicalInvolution.Asc77.WP1Defs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Asc77 (IsSylow2In)

theorem card_oddCore_odd (Q : Type) [Group Q] [Finite Q] : Odd (Nat.card (CFSG.oddCore Q)) := by
  have hle : CFSG.oddCore Q ≤ CFSG.pPrimeCore 2 Q :=
    sSup_le fun N hN => le_sSup ⟨hN.1, Nat.coprime_two_left.mpr hN.2⟩
  have hdvd : Nat.card (CFSG.oddCore Q) ∣ Nat.card (CFSG.pPrimeCore 2 Q) :=
    Subgroup.card_dvd_of_le hle
  have hcop : Nat.Coprime 2 (Nat.card (CFSG.oddCore Q)) :=
    Nat.Coprime.coprime_dvd_right hdvd CFSG.pPrimeCore_coprime_card
  exact Nat.coprime_two_left.mp hcop

theorem padicValNat_card_le_one_of_zStar {Q : Type} [Group Q] [Finite Q]
    {P : Subgroup Q} (hP : IsSylow2In P ⊤) {z : Q} (hzP : z ∈ P) (hz1 : z ≠ 1)
    (hz2 : z * z = 1) (hcent : ∀ p ∈ P, p * z = z * p)
    (hweak : ∀ g : Q, g⁻¹ * z * g ∈ P → g⁻¹ * z * g = z)
    (hgen : ∀ q : Q, q ∈ Subgroup.closure {x : Q | ∃ g : Q, x = g * z * g⁻¹}) :
    padicValNat 2 (Nat.card Q) ≤ 1 := by
  let S' : Sylow 2 Q :=
    { toSubgroup := P
      isPGroup' := hP.2.1
      is_maximal' := fun {T} hT hle => hP.2.2 T le_top hT hle }
  have hzS : z ∈ (S' : Subgroup Q) := hzP
  have hzZ : (⟨z, hzS⟩ : (S' : Subgroup Q)) ∈ Subgroup.center (S' : Subgroup Q) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcent g.1 g.2)
  have hz : orderOf (⟨z, hzS⟩ : (S' : Subgroup Q)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hwc : ∀ g : Q, g⁻¹ * z * g ∈ (S' : Subgroup Q) → g⁻¹ * z * g = z := hweak
  have hcen : (QuotientGroup.mk z : Q ⧸ CFSG.oddCore Q) ∈
      Subgroup.center (Q ⧸ CFSG.oddCore Q) :=
    (CFSG.Adapters.glauberman_zStar S' ⟨z, hzS⟩ hzZ hz hwc).2
  have hconj : ∀ g : Q, g * z * g⁻¹ ∈ Subgroup.zpowers z ⊔ CFSG.oddCore Q := by
    intro g
    have h := Subgroup.mem_center_iff.mp hcen (QuotientGroup.mk g)
    have h1 : (QuotientGroup.mk (g * z) : Q ⧸ CFSG.oddCore Q) = QuotientGroup.mk (z * g) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact h
    have h2 := QuotientGroup.eq.mp h1
    have e1 : (g * z)⁻¹ * (z * g) = z⁻¹ * g⁻¹ * z * g := by group
    rw [e1] at h2
    have hOn : (CFSG.oddCore Q).Normal := inferInstance
    have h3 := (CFSG.oddCore Q).inv_mem (hOn.conj_mem _ h2 g)
    have e2 : (g * (z⁻¹ * g⁻¹ * z * g) * g⁻¹)⁻¹ = z⁻¹ * g * z * g⁻¹ := by group
    rw [e2] at h3
    have e3 : g * z * g⁻¹ = z * (z⁻¹ * g * z * g⁻¹) := by group
    rw [e3]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers z) h3
  have hall : ∀ q : Q, q ∈ Subgroup.zpowers z ⊔ CFSG.oddCore Q := by
    intro q
    have hle : Subgroup.closure {x : Q | ∃ g : Q, x = g * z * g⁻¹} ≤
        Subgroup.zpowers z ⊔ CFSG.oddCore Q := by
      rw [Subgroup.closure_le]
      rintro _ ⟨g, rfl⟩
      exact hconj g
    exact hle (hgen q)
  have hg2 : (QuotientGroup.mk z : Q ⧸ CFSG.oddCore Q) ^ 2 = 1 := by
    rw [sq, ← QuotientGroup.mk_mul, hz2, QuotientGroup.mk_one]
  have hcov : ∀ x : Q ⧸ CFSG.oddCore Q,
      x ∈ Subgroup.zpowers (QuotientGroup.mk z : Q ⧸ CFSG.oddCore Q) := by
    intro x
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, hy, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hall q)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff o).mpr ho, mul_one,
      QuotientGroup.mk_zpow]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) n
  have hcardQ : Nat.card (Q ⧸ CFSG.oddCore Q) ≤ 2 := by
    have hfin : Nat.card (Q ⧸ CFSG.oddCore Q) ≤
        Nat.card (Subgroup.zpowers (QuotientGroup.mk z : Q ⧸ CFSG.oddCore Q)) :=
      Nat.card_le_card_of_surjective (fun x => (x : Q ⧸ CFSG.oddCore Q))
        (fun x => ⟨⟨x, hcov x⟩, rfl⟩)
    have horder : orderOf (QuotientGroup.mk z : Q ⧸ CFSG.oddCore Q) ≤ 2 :=
      Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one hg2)
    rw [Nat.card_zpowers] at hfin
    exact hfin.trans horder
  have hcard_eq : Nat.card Q = Nat.card (CFSG.oddCore Q) * Nat.card (Q ⧸ CFSG.oddCore Q) := by
    rw [← Subgroup.index_eq_card, Subgroup.card_mul_index]
  have hOodd : Odd (Nat.card (CFSG.oddCore Q)) := card_oddCore_odd Q
  have hOpos : Nat.card (CFSG.oddCore Q) ≠ 0 := hOodd.pos.ne'
  have hm : 0 < Nat.card (Q ⧸ CFSG.oddCore Q) := Nat.card_pos
  rw [hcard_eq]
  rcases (by omega : Nat.card (Q ⧸ CFSG.oddCore Q) = 1 ∨
      Nat.card (Q ⧸ CFSG.oddCore Q) = 2) with h | h
  · rw [h, mul_one, padicValNat.eq_zero_of_not_dvd hOodd.not_two_dvd_nat]
    exact Nat.zero_le _
  · rw [h, padicValNat.mul hOpos two_ne_zero,
      padicValNat.eq_zero_of_not_dvd hOodd.not_two_dvd_nat, padicValNat.self (by norm_num)]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

end
