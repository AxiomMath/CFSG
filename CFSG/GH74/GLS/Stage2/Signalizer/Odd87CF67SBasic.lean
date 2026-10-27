module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67N2
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.CF67S

open Subgroup CFSG CFSG.ComponentClassification.OuterAutomorphisms

section Basic

theorem conj_injective_of_center_bot {Y : Type*} [Group Y] (hcenter : Subgroup.center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmem : g ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro x
    have := congrArg (fun φ : MulAut Y => φ x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.mp this).symm
  rw [hcenter] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem card_mulAut_eq_outer_mul {Y : Type} [Group Y] [Finite Y] (hcenter : Subgroup.center Y = ⊥) :
    Nat.card (MulAut Y) = Nat.card (Outer Y) * Nat.card Y := by
  have hinj := conj_injective_of_center_bot hcenter
  have h1 : Nat.card (inner Y) = Nat.card Y := by
    have : inner Y = (MulAut.conj : Y →* MulAut Y).range := rfl
    rw [this]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (inner Y)
  rw [h1] at h2
  exact h2

theorem mem_inner_of_pow_eq_one {Y : Type} [Group Y] [Finite Y] {φ : MulAut Y} {n : ℕ}
    (hφ : φ ^ n = 1) (hcop : Nat.Coprime n (Nat.card (Outer Y))) : φ ∈ inner Y := by
  have h1 : (QuotientGroup.mk φ : Outer Y) ^ n = 1 := by
    rw [← QuotientGroup.mk_pow, hφ, QuotientGroup.mk_one]
  have h2 : orderOf (QuotientGroup.mk φ : Outer Y) ∣ n := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (QuotientGroup.mk φ : Outer Y) ∣ Nat.card (Outer Y) := orderOf_dvd_natCard _
  have h4 : orderOf (QuotientGroup.mk φ : Outer Y) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hcop) h3
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h4
  exact h4

theorem exists_inner_ne_one {Y : Type} [Group Y] [Finite Y] {r : ℕ}
    (V : Subgroup (MulAut Y)) (hV : Nat.card V = r ^ 2) (hOut : ¬ r ^ 2 ∣ Nat.card (Outer Y)) :
    ∃ v ∈ V, v ≠ 1 ∧ v ∈ inner Y := by
  classical
  let f : ↥V →* Outer Y := (QuotientGroup.mk' (inner Y)).comp V.subtype
  have h1 := Subgroup.card_ker_mul_card_range f
  have h2 : Nat.card f.range ∣ Nat.card (Outer Y) := Subgroup.card_subgroup_dvd_card f.range
  have hker : f.ker ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot, one_mul, hV] at h1
    exact hOut (h1 ▸ h2)
  obtain ⟨⟨x, hxker⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hker
  refine ⟨(x : MulAut Y), x.2, fun h => hx1 (Subtype.ext (Subtype.ext (by simpa using h))), ?_⟩
  have := (MonoidHom.mem_ker).mp hxker
  simpa [f, QuotientGroup.eq_one_iff] using this

theorem n2_sq_dvd {Y : Type} [Group Y] [Finite Y] {r : ℕ} {V Z : Subgroup (MulAut Y)}
    (h : N2Cfg Y r V Z) : r ^ 2 ∣ Nat.card (MulAut Y) := by
  obtain ⟨-, -, -, hVc, -⟩ := h
  exact hVc ▸ Subgroup.card_subgroup_dvd_card V

theorem n2_exists_prime_elt {Y : Type} [Group Y] [Finite Y] {r : ℕ} {V Z : Subgroup (MulAut Y)}
    (h : N2Cfg Y r V Z) :
    ∃ (s : ℕ) (y : MulAut Y), s.Prime ∧ Odd s ∧ s ≠ r ∧ y ^ s = 1 ∧ y ≠ 1 ∧ y ∈ Z ∧
      ∀ v ∈ V, v * y = y * v := by
  obtain ⟨hr, hr2, hVe, hVc, hZab, hZodd, hZcop, hZbot, hcomm⟩ := h
  have hZcard1 : Nat.card ↥Z ≠ 1 := fun h => hZbot (Subgroup.card_eq_one.mp h)
  have hs : (Nat.card ↥Z).minFac.Prime := Nat.minFac_prime hZcard1
  have hsdvd : (Nat.card ↥Z).minFac ∣ Nat.card ↥Z := Nat.minFac_dvd _
  have : Fact (Nat.card ↥Z).minFac.Prime := ⟨hs⟩
  have hZfin : Finite ↥Z := Nat.finite_of_card_ne_zero (Odd.pos hZodd).ne'
  obtain ⟨⟨y, hyZ⟩, hyord⟩ := exists_prime_orderOf_dvd_card' (Nat.card ↥Z).minFac hsdvd
  have hyord' : orderOf y = (Nat.card ↥Z).minFac := by
    rw [← hyord]; exact (Subgroup.orderOf_mk y hyZ).symm
  refine ⟨(Nat.card ↥Z).minFac, y, hs, Odd.of_dvd_nat hZodd hsdvd, ?_, ?_, ?_, hyZ,
    fun v hv => hcomm v hv y hyZ⟩
  · intro hrs
    have hcop : Nat.Coprime r (Nat.card ↥Z) := hZcop.symm
    have := hcop.eq_one_of_dvd (hrs ▸ hsdvd)
    exact hr.one_lt.ne' this
  · rw [← hyord']; exact pow_orderOf_eq_one y
  · intro hy1
    rw [hy1, orderOf_one] at hyord'
    exact hs.one_lt.ne hyord'

end Basic

end CFSG.GH74.GLS.Stage2.Bender.Thm1.CF67S
