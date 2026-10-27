module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

theorem normal_closure_odd (X : Type*) [Group X] :
    (Subgroup.closure {x : X | Odd (orderOf x)}).Normal := by
  refine ⟨fun n hn g => ?_⟩
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    refine Subgroup.subset_closure ?_
    have : orderOf (g * x * g⁻¹) = orderOf x := (MulAut.conj g).orderOf_eq x
    show Odd (orderOf (g * x * g⁻¹))
    rw [this]
    exact hx
  | one => simp
  | mul x y _ _ ihx ihy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ih =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ih

theorem odd_orderOf_pow_two_part {X : Type*} [Group X] [Finite X] (x : X) :
    Odd (orderOf (x ^ 2 ^ (orderOf x).factorization 2)) := by
  set a := (orderOf x).factorization 2 with ha
  have hdvd : 2 ^ a ∣ orderOf x := Nat.ordProj_dvd _ _
  rw [orderOf_pow_of_dvd (by positivity) hdvd]
  have hpos : 0 < orderOf x := orderOf_pos x
  have : ¬ 2 ∣ orderOf x / 2 ^ a := Nat.not_dvd_ordCompl Nat.prime_two hpos.ne'
  exact Nat.odd_iff.mpr (by omega)

theorem pResidual_two_eq_closure_odd (X : Type*) [Group X] [Finite X] :
    pResidual 2 X = Subgroup.closure {x : X | Odd (orderOf x)} := by
  apply le_antisymm
  · have := normal_closure_odd X
    refine pResidual_le fun x => ?_
    exact ⟨(orderOf x).factorization 2, Subgroup.subset_closure (odd_orderOf_pow_two_part x)⟩
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [pResidual, SetLike.mem_coe, Subgroup.mem_iInf]
    intro N hN hk
    obtain ⟨k, hk⟩ := hk x
    have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hx)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact N.pow_mem hk m

theorem pResidualOf_two_eq_closure_odd {G : Type*} [Group G] [Finite G] (X : Subgroup G) :
    pResidualOf 2 X = Subgroup.closure {x : G | x ∈ X ∧ Odd (orderOf x)} := by
  unfold pResidualOf
  rw [pResidual_two_eq_closure_odd, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    simpa [Subgroup.orderOf_coe] using hy
  · rintro ⟨hx, hodd⟩
    exact ⟨⟨x, hx⟩, by simpa [Subgroup.orderOf_mk] using hodd, rfl⟩

end CFSG.QuasithinUnique
