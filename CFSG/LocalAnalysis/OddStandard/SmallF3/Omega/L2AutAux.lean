module

public import Mathlib.FieldTheory.Finite.GaloisField
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearRingEquiv
import CFSG.Walter.PSL2Facts.FieldAut
import CFSG.Walter.Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.GorensteinWalter CFSG.Walter
open scoped MatrixGroups

universe u

theorem l2aut_reduce {M : Type*} [Group M] {F : Type u} [Field F] [Finite F] (e : M ≃* PSL2 F)
    (h5 : 5 ≤ Nat.card F) (h8 : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5) {P : Prop}
    (H : ∀ (p f : ℕ) [Fact p.Prime], Odd p → 0 < f → 5 ≤ p ^ f →
      (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) → M ≃* PSL(2, GaloisField p f) → P) : P := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hpr, hq⟩ := FiniteField.card F (ringChar F)
  haveI : Fact (ringChar F).Prime := ⟨hpr⟩
  have hcard : Nat.card F = ringChar F ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hq]
  have hodd : Odd (ringChar F) := by
    rcases hpr.eq_two_or_odd' with h2 | h2
    · exfalso
      have hev : Even (Nat.card F) := by
        rw [hcard, h2]
        exact (Nat.even_pow' n.ne_zero).mpr even_two
      rw [Nat.even_iff] at hev
      omega
    · exact h2
  have : Fintype (GaloisField (ringChar F) n) := Fintype.ofFinite _
  let φ : F ≃+* GaloisField (ringChar F) n := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      GaloisField.card _ _ n.ne_zero, hcard])
  rw [hcard] at h5 h8
  exact H (ringChar F) n hodd n.pos h5 h8 (e.trans (psl2RingEquiv φ))

theorem l2aut_pow_apply_eq {H : Type*} [Group H] (α : MulAut H) {x : H} (hx : α x = x) (k : ℕ) :
    (α ^ k) x = x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, MulAut.mul_apply, hx, ih]

theorem l2aut_gf_odd_eq_one
    {p f : ℕ} [Fact p.Prime] (hp : Odd p) (hf : 0 < f) (h5 : 5 ≤ p ^ f)
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) {α : MulAut PSL(2, GaloisField p f)}
    (hα : Odd (orderOf α)) {u : PSL(2, GaloisField p f)} (hu : orderOf u = 2)
    (hfix : ∀ x ∈ Subgroup.centralizer ({u} : Set PSL(2, GaloisField p f)), α x = x) :
    α = 1 := by
  classical
  by_contra hne
  have hm0 : orderOf α ≠ 0 := by
    intro h
    rw [h, Nat.odd_iff] at hα
    omega
  have hm1 : orderOf α ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hm1
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hα) (even_iff_two_dvd.mpr hrdvd)
  have hβ : orderOf (α ^ (orderOf α / r)) = r := orderOf_pow_orderOf_div hm0 hrdvd
  have hpg : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hu, pow_one])
  obtain ⟨S, hS⟩ := hpg.exists_le_sylow
  have huS : u ∈ (S : Subgroup PSL(2, GaloisField p f)) := hS (Subgroup.mem_zpowers u)
  have hK := psl2_odd_sylow_two_isKleinFour hp hf h8 S
  haveI : IsMulCommutative (S : Subgroup PSL(2, GaloisField p f)) := hK.isMulCommutative
  have hSc : ∀ x ∈ (S : Subgroup PSL(2, GaloisField p f)),
      x ∈ Subgroup.centralizer ({u} : Set PSL(2, GaloisField p f)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact congrArg Subtype.val (mul_comm' (⟨y, huS⟩ : S) ⟨x, hx⟩)
  obtain ⟨-, hrf, ⟨eqv⟩⟩ := psl2_mulAut_of_centralizes_sylow_two hp hf h5 h8 hr hr2
    (α ^ (orderOf α / r)) hβ S fun x hx => l2aut_pow_apply_eq α (hfix x (hSc x hx)) _
  have hle : Subgroup.centralizer ({u} : Set PSL(2, GaloisField p f)) ≤
      (α ^ (orderOf α / r)).toMonoidHom.eqLocus (MonoidHom.id _) :=
    fun x hx => l2aut_pow_apply_eq α (hfix x hx) _
  have hcard1 := Subgroup.card_le_of_le hle
  rw [Nat.card_congr eqv.toEquiv] at hcard1
  have hfr : 0 < f / r := Nat.div_pos (Nat.le_of_dvd hf hrf) hr.pos
  have hp3 : 3 ≤ p := by
    have h2 := (Fact.out : p.Prime).two_le
    rcases hp with ⟨k, hk⟩
    omega
  have hq'3 : 3 ≤ p ^ (f / r) := le_trans hp3 (Nat.le_self_pow hfr.ne' p)
  have hqf : p ^ f = (p ^ (f / r)) ^ r := by rw [← pow_mul, Nat.div_mul_cancel hrf]
  have hr3 : 3 ≤ r := by have := hr.two_le; omega
  have hq3 : (p ^ (f / r)) ^ 3 ≤ p ^ f := by
    rw [hqf]
    exact Nat.pow_le_pow_right (by omega) hr3
  have hC : p ^ f - 1 ≤ Nat.card (Subgroup.centralizer ({u} : Set PSL(2, GaloisField p f))) := by
    obtain ⟨h1, h3⟩ := psl2_odd_centralizer_involution hp hf hu
    have h4 : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by omega
    rcases h4 with h | h
    · rw [(h1 h).1]
    · rw [(h3 h).1]
      omega
  have hP := psl2_card_formula (GaloisField p (f / r))
    (isOddPrimePower_of_card (GaloisField.card p (f / r) hfr.ne') hp hfr)
  rw [GaloisField.card p (f / r) hfr.ne'] at hP
  have h2 : (p ^ f - 1) * 2 ≤ p ^ (f / r) * ((p ^ (f / r)) ^ 2 - 1) := by
    have h := le_trans hC hcard1
    rw [hP] at h
    exact (Nat.le_div_iff_mul_le two_pos).mp h
  generalize p ^ (f / r) = a at hq'3 hq3 h2
  generalize p ^ f = Q at h5 hq3 h2
  have ha2 : a ^ 2 = (a ^ 2 - 1) + 1 := by
    have : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have h3 : a * (a ^ 2 - 1) + a = a ^ 3 := by
    calc a * (a ^ 2 - 1) + a = a * ((a ^ 2 - 1) + 1) := by ring
      _ = a * a ^ 2 := by rw [← ha2]
      _ = a ^ 3 := by ring
  omega

theorem l2aut_gf_odd_eq_one_of_equiv
    {p f : ℕ} [Fact p.Prime] (hp : Odd p) (hf : 0 < f) (h5 : 5 ≤ p ^ f)
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) {H : Type*} [Group H]
    (e : H ≃* PSL(2, GaloisField p f)) {α : MulAut H} (hα : Odd (orderOf α)) {u : H}
    (hu : orderOf u = 2) (hfix : ∀ x ∈ Subgroup.centralizer ({u} : Set H), α x = x) :
    α = 1 := by
  have h1 : MulAut.congr e α = 1 := by
    refine l2aut_gf_odd_eq_one hp hf h5 h8
      (by rwa [MulEquiv.orderOf_eq (MulAut.congr e) α]) (u := e u)
      (by rwa [MulEquiv.orderOf_eq e u]) fun y hy => ?_
    have hy' : e.symm y ∈ Subgroup.centralizer ({u} : Set H) := by
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hy (e v) (Set.mem_singleton _)
    change e (α (e.symm y)) = y
    rw [hfix _ hy', MulEquiv.apply_symm_apply]
  exact (MulAut.congr e).injective (h1.trans (map_one _).symm)

end CFSG.OddStandard.SmallF3.Omega
