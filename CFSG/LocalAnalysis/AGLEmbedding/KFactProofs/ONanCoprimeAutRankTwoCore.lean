module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
public import CFSG.LocalAnalysis.SectionRank.Ccomm.RankTwo
public import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy

public section

namespace CFSG.AGLEmbedding.KFactProofs.CoprimeAutRankTwo

open CFSG.SectionRank.Ccomm CFSG.Open

theorem exists_dvd_pow_sub_one_of_orderOf {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {N : Type}
    [Group N] [Finite N] (hN : IsPGroup p N) (hrk : Open.pRank p (⊤ : Subgroup N) ≤ 2) {r : ℕ}
    (hr : r.Prime) (hrp : r ≠ p) (α : MulAut N) (hα : orderOf α = r) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ 3 ∧ r ∣ p ^ k - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have hNnt : Nontrivial N := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have h1 : α = 1 := MulEquiv.ext fun x => Subsingleton.elim _ _
    rw [h1, orderOf_one] at hα
    exact hr.one_lt.ne hα
  obtain ⟨D, hDchar, -, -, hDexp, hDfix⟩ := odd_critical_exponent_subgroup hp2 hN
  have hDp : IsPGroup p D := hN.to_subgroup D
  have hDrk : Open.pRank p (⊤ : Subgroup D) ≤ 2 :=
    (CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt D.subtype D.subtype_injective).trans hrk
  have hDcard : Nat.card D ≤ p ^ 3 :=
    (rank_two_exponent_prime_order_bound hDp (fun x => Subtype.ext (by
      rw [Subgroup.coe_pow, hDexp x x.2, Subgroup.coe_one])) hDrk).1
  set β : MulAut D := MulAut.characteristic D α with hβ
  have hβ1 : β ≠ 1 := by
    intro h1
    have hfix : α ∈ fixingSubgroup (MulAut N) (D : Set N) := by
      rw [mem_fixingSubgroup_iff]
      intro x hx
      exact congrArg (fun γ : MulAut D => ((γ ⟨x, hx⟩ : D) : N)) h1
    obtain ⟨k, hk⟩ := hDfix ⟨α, hfix⟩
    have hpow : α ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hrd : r ∣ p ^ k := hα ▸ orderOf_dvd_of_pow_eq_one hpow
    exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow hrd))
  have hβr : β ^ r = 1 := by
    rw [hβ, ← map_pow, ← hα, pow_orderOf_eq_one, map_one]
  have hG : IsPGroup r (Subgroup.zpowers β) := by
    intro g
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, ← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hβr, one_zpow, Subgroup.coe_one]
  have hmod := hG.card_modEq_card_fixedPoints D
  let F : Subgroup D := MonoidHom.eqLocus (β : D →* D) (MonoidHom.id D)
  have hFmem : ∀ x : D, x ∈ F ↔ β x = x := fun x => Iff.rfl
  have hfixF : Nat.card (MulAction.fixedPoints (Subgroup.zpowers β) D) = Nat.card F := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [hFmem, MulAction.mem_fixedPoints]
    constructor
    · intro h
      exact h ⟨β, Subgroup.mem_zpowers β⟩
    · intro h g
      have hle : Subgroup.zpowers β ≤ MulAction.stabilizer (MulAut D) x :=
        Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 h)
      exact MulAction.mem_stabilizer_iff.1 (hle g.2)
  have hFtop : F ≠ ⊤ := by
    intro htop
    apply hβ1
    exact MulEquiv.ext fun x => (Subgroup.eq_top_iff' F).1 htop x
  obtain ⟨a, ha⟩ := hDp.exists_card_eq
  obtain ⟨b, hb⟩ := (hDp.to_subgroup F).exists_card_eq
  have hlt : Nat.card F < Nat.card D :=
    lt_of_le_of_ne (Subgroup.card_le_card_group F) fun h =>
      hFtop ((Subgroup.card_eq_iff_eq_top F).1 h)
  rw [ha, hfixF, hb] at hmod
  rw [ha] at hDcard hlt
  rw [hb] at hlt
  have hab : b < a := (Nat.pow_lt_pow_iff_right hp.one_lt).1 hlt
  have ha3 : a ≤ 3 := (Nat.pow_le_pow_iff_right hp.one_lt).1 hDcard
  have hdvd : r ∣ p ^ a - p ^ b := (Nat.modEq_iff_dvd' hlt.le).1 hmod.symm
  have hsub : p ^ a - p ^ b = p ^ b * (p ^ (a - b) - 1) := by
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hab.le]
  rw [hsub] at hdvd
  rcases (Nat.Prime.dvd_mul hr).1 hdvd with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow h)) hrp
  · exact ⟨a - b, by omega, by omega, h⟩

theorem exists_primitive_prime_dvd_add_one {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 2 ≤ m) :
    ∃ r : ℕ, r.Prime ∧ r ≠ p ∧ r ∣ p ^ m + 1 ∧ ∀ k : ℕ, 0 < k → k < 2 * m → ¬ r ∣ p ^ k - 1 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨r, hr, hdvd, hprim⟩ :=
    CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one hp3 (n := 2 * m) (by omega)
  refine ⟨r, hr, ?_, ?_, hprim⟩
  · rintro rfl
    have h1 : r ∣ r ^ (2 * m) := dvd_pow_self r (by omega)
    have h2 := Nat.dvd_sub h1 hdvd
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hr.pos)] at h2
    exact hr.one_lt.ne' (Nat.dvd_one.1 h2)
  · have hx : p ^ (2 * m) - 1 = (p ^ m + 1) * (p ^ m - 1) := by
      rw [pow_mul', ← Nat.sq_sub_sq, one_pow]
    rw [hx] at hdvd
    rcases (Nat.Prime.dvd_mul hr).1 hdvd with h | h
    · exact h
    · exact absurd h (hprim m (by omega) (by omega))

theorem false_of_dvd_card {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y N : Type} [Group Y] [Finite Y]
    [Group N] [Finite N] (hN : IsPGroup p N) (hrk : Open.pRank p (⊤ : Subgroup N) ≤ 2)
    (ρ : Y →* MulAut N) (hρ : Function.Injective ρ) {m : ℕ} (hm : 2 ≤ m)
    (hdvd : p ^ m + 1 ∣ Nat.card Y) : False := by
  obtain ⟨r, hr, hrp, hrm, hprim⟩ := exists_primitive_prime_dvd_add_one hp hp2 hm
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' r (hrm.trans hdvd)
  have hα : orderOf (ρ y) = r := by rw [orderOf_injective ρ hρ y, hy]
  obtain ⟨k, hk1, hk3, hk⟩ := exists_dvd_pow_sub_one_of_orderOf hp hp2 hN hrk hr hrp (ρ y) hα
  exact hprim k (by omega) (by omega) hk

end CFSG.AGLEmbedding.KFactProofs.CoprimeAutRankTwo
