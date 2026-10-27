module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L53

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem centralizes_of_coprime {p : ℕ} [hp : Fact p.Prime] {X Y : Subgroup G} (hX : IsPGroup p ↥X)
    (hYX : Y ≤ X) {c : G} (hc : ¬ p ∣ orderOf c)
    (hcY : ∀ y ∈ Y, c * y * c⁻¹ = y) (hcXY : ∀ x ∈ X, x⁻¹ * (c * x * c⁻¹) ∈ Y) :
    ∀ x ∈ X, c * x * c⁻¹ = x := by
  intro x hx
  set y : G := x⁻¹ * (c * x * c⁻¹) with hy
  have hyY : y ∈ Y := hcXY x hx
  have hyX : y ∈ X := hYX hyY
  have hcx : c * x * c⁻¹ = x * y := by rw [hy]; group
  have hk : ∀ k : ℕ, c ^ k * x * (c ^ k)⁻¹ = x * y ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : c ^ (k + 1) * x * (c ^ (k + 1))⁻¹ = c * (c ^ k * x * (c ^ k)⁻¹) * c⁻¹ := by
        rw [pow_succ', mul_inv_rev]; group
      rw [h1, ih]
      have h2 : c * (x * y ^ k) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) ^ k := by
        rw [conj_pow]; group
      rw [h2, hcx, hcY y hyY, pow_succ']
      group
  have hn := hk (orderOf c)
  rw [pow_orderOf_eq_one] at hn
  simp only [inv_one, mul_one, one_mul] at hn
  have hyn : y ^ orderOf c = 1 := by
    have : x * y ^ orderOf c = x := by rw [← hn]
    simpa using this
  obtain ⟨k, hk'⟩ := (IsPGroup.iff_orderOf.mp hX) ⟨y, hyX⟩
  have hok : orderOf y = p ^ k := by
    have : orderOf (⟨y, hyX⟩ : ↥X) = orderOf y := Subgroup.orderOf_mk y hyX
    rw [← this]; exact hk'
  have hdvd : orderOf y ∣ orderOf c := orderOf_dvd_of_pow_eq_one hyn
  rw [hok] at hdvd
  have hk0 : k = 0 := by
    by_contra hne
    exact hc (dvd_trans (dvd_pow_self p hne) hdvd)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hok
  rw [hcx, hok, mul_one]

theorem comm_sup_le {U D K : Subgroup G} (hD : D ≤ normalizer (U : Set G))
    (hK : K ≤ normalizer (U : Set G)) : ⁅U ⊔ D, K⁆ ≤ U ⊔ ⁅D, K⁆ := by
  rw [Subgroup.commutator_le]
  intro x hx k hk
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right D U hD
  rw [sup_comm, ← SetLike.mem_coe, hset] at hx
  obtain ⟨d, hd, u, hu, rfl⟩ := Set.mem_mul.1 hx
  have h1 : ⁅d * u, k⁆ = (d * ⁅u, k⁆ * d⁻¹) * ⁅d, k⁆ := by
    simp only [commutatorElement_def]; group
  rw [h1]
  refine Subgroup.mul_mem _ ?_ ?_
  · refine Subgroup.mem_sup_left ?_
    have hk' : ⁅u, k⁆ ∈ U := by
      have h2 := (Subgroup.mem_normalizer_iff.mp (hK hk)) u⁻¹
      have h3 : k * u⁻¹ * k⁻¹ ∈ U := (h2.mp (U.inv_mem hu))
      have : ⁅u, k⁆ = u * (k * u⁻¹ * k⁻¹) := by simp only [commutatorElement_def]; group
      rw [this]; exact U.mul_mem hu h3
    have hdn := Subgroup.mem_normalizer_iff.mp (hD hd) ⁅u, k⁆
    have h4 : d * ⁅u, k⁆ * d⁻¹ ∈ U := hdn.mp hk'
    exact h4
  · exact Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hd hk)

theorem le_of_le_comm_sup {T X Y : Subgroup G} (hT : Group.IsNilpotent ↥T) (hXT : X ≤ T)
    (hTY : T ≤ normalizer (Y : Set G)) (h : X ≤ ⁅X, T⁆ ⊔ Y) : X ≤ Y := by
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries T).mp hT
  have key : ∀ k, X ≤ T.lowerCentralSeries k ⊔ Y := by
    intro k
    induction k with
    | zero => exact hXT.trans le_sup_left
    | succ k ih =>
      have hD : T.lowerCentralSeries k ≤ normalizer (Y : Set G) :=
        ((Subgroup.lowerCentralSeries_antitone T (Nat.zero_le k)).trans le_rfl).trans hTY
      have h1 : ⁅X, T⁆ ≤ ⁅Y ⊔ T.lowerCentralSeries k, T⁆ :=
        Subgroup.commutator_mono_left (by rw [sup_comm]; exact ih)
      have h2 := comm_sup_le hD hTY (K := T) |>.trans' h1
      have h3 : ⁅X, T⁆ ⊔ Y ≤ T.lowerCentralSeries (k + 1) ⊔ Y := by
        refine sup_le ?_ le_sup_right
        refine h2.trans ?_
        rw [Subgroup.lowerCentralSeries_succ, sup_comm]
      exact h.trans h3
  have := key n
  rwa [hn, bot_sup_eq] at this

end CFSG.GH74.GLS.Stage2.Signalizer.L53
