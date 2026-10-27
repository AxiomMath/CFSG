module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Diag.S2

open Subgroup

open IsMulCommutative in
theorem central_eq_one_of_abelian_index {E : Type*} [Group E] [Finite E]
    (hE : commutator E = ⊤) {P : Subgroup E} [IsMulCommutative P] {z : E}
    (hzc : z ∈ center E) (hcop : Nat.Coprime (orderOf z) P.index) : z = 1 := by
  set T : E →* P := (MonoidHom.id P).transfer with hT
  have hT1 : ∀ g, T g = 1 := fun g => by
    have h1 : g ∈ commutator E := hE ▸ mem_top g
    exact Abelianization.commutator_subset_ker T h1
  have hkey : ∀ (k : ℕ) (g₀ : E), g₀⁻¹ * z ^ k * g₀ ∈ P → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hzk : z ^ k ∈ center E := pow_mem hzc k
    rw [mul_assoc, ← (mem_center_iff.mp hzk g₀), inv_mul_cancel_left]
  have h1 := MonoidHom.transfer_eq_pow (MonoidHom.id P) z hkey
  rw [hT1] at h1
  have h2 : z ^ P.index = 1 := by
    have := congrArg Subtype.val h1
    simpa using this.symm
  have h3 := Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one h2)
  exact orderOf_eq_one_iff.mp h3

theorem ker_eq_bot_of_odd_central {E S : Type*} [Group E] [Finite E] [Group S] [Finite S]
    (hE : commutator E = ⊤) (ρ : E →* S) (hc : ρ.ker ≤ center E)
    (hodd : Odd (Nat.card ρ.ker))
    (hS : ∀ p : ℕ, p.Prime → Odd p → ¬ p ^ 2 ∣ Nat.card S) : ρ.ker = ⊥ := by
  by_contra hne
  have hne1 : Nat.card ρ.ker ≠ 1 := fun h => hne (Subgroup.eq_bot_of_card_eq _ h)
  have hp : (Nat.card ρ.ker).minFac.Prime := Nat.minFac_prime hne1
  generalize hpdef : (Nat.card ρ.ker).minFac = p at hp
  have : Fact p.Prime := ⟨hp⟩
  have hpdvd : p ∣ Nat.card ρ.ker := hpdef ▸ Nat.minFac_dvd _
  have hpodd : Odd p := Odd.of_dvd_nat hodd hpdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  have hzo : orderOf (x : E) = p := by rw [Subgroup.orderOf_coe]; exact hx
  have hzc : (x : E) ∈ center E := hc x.2
  obtain ⟨P⟩ : Nonempty (Sylow p E) := inferInstance
  let f₀ : (P : Subgroup E) →* S := ρ.comp (P : Subgroup E).subtype
  have hker0 : f₀.rangeRestrict.ker ≤ center (P : Subgroup E) := by
    intro y hy
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hy
    refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
    exact Subgroup.mem_center_iff.mp (hc hy) (g : E)
  have hQp : IsPGroup p f₀.range := P.2.of_surjective f₀.rangeRestrict f₀.rangeRestrict_surjective
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hQp
  have hk1 : k ≤ 1 := by
    by_contra hk2
    refine hS p hp hpodd ?_
    have h1 : p ^ 2 ∣ p ^ k := pow_dvd_pow p (by omega)
    exact h1.trans (hk ▸ Subgroup.card_subgroup_dvd_card _)
  have hcyc : IsCyclic f₀.range := by
    have : Nat.card f₀.range ∣ p := by
      rw [hk]
      simpa using pow_dvd_pow p hk1
    exact isCyclic_of_card_dvd_prime this
  have hcomm : IsMulCommutative (P : Subgroup E) :=
    MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center f₀.rangeRestrict hker0
  have hcop : Nat.Coprime (orderOf (x : E)) (P : Subgroup E).index := by
    rw [hzo]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 P.not_dvd_index
  have h1 := central_eq_one_of_abelian_index hE hzc hcop
  rw [h1, orderOf_one] at hzo
  exact hp.one_lt.ne hzo

theorem card_sl2_four : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) = 60 := by
  have : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hK : Fintype.card (GaloisField 2 2) = 4 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
    norm_num
  classical
  rw [Matrix.card_SL_field, hK]
  decide

theorem not_odd_prime_sq_dvd_sl2_four : ∀ p : ℕ, p.Prime → Odd p →
    ¬ p ^ 2 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) := by
  intro p hp hpo hdvd
  rw [card_sl2_four] at hdvd
  have hp2 : p ^ 2 ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd
  have hp7 : p ≤ 7 := by nlinarith
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    have := Nat.odd_iff.mp hpo
    omega
  interval_cases p <;> revert hdvd <;> decide

end CFSG.CGT.PushingUpLit.CGT6.Diag.S2
