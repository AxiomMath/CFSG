module

public import CFSG.ClassicalInvolution.Phan.Phan3ASound
public import CFSG.ClassicalInvolution.Phan.Phan3ACover
public import CFSG.ClassicalInvolution.Phan.Phan3ACentral
public import CFSG.ClassicalInvolution.Phan.Phan3AOrder

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.CosetTable (mk_flatten_replicate)
open CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank

noncomputable def kerA : PhanA3Group := PresentedGroup.mk _ (FreeGroup.mk phanA3U1)

noncomputable def kerB : PhanA3Group := PresentedGroup.mk _ (FreeGroup.mk phanA3U2)

theorem mk_powWord (u : List (Fin 6 × Bool)) (k : Int) :
    (PresentedGroup.mk _ (FreeGroup.mk (powWord u k)) : PhanA3Group) =
      (PresentedGroup.mk _ (FreeGroup.mk u)) ^ k := by
  cases k with
  | ofNat n =>
    show (PresentedGroup.mk _ (FreeGroup.mk (List.replicate n u).flatten) : PhanA3Group) =
      _ ^ ((n : ℕ) : ℤ)
    rw [mk_flatten_replicate, map_pow, zpow_natCast]
  | negSucc n =>
    show (PresentedGroup.mk _ (FreeGroup.mk (List.replicate (n + 1) (invWord u)).flatten) :
      PhanA3Group) = _ ^ Int.negSucc n
    rw [mk_flatten_replicate, map_pow, zpow_negSucc, ← inv_pow]
    congr 2

theorem mk_append (u v : List (Fin 6 × Bool)) :
    (PresentedGroup.mk _ (FreeGroup.mk (u ++ v)) : PhanA3Group) =
      PresentedGroup.mk _ (FreeGroup.mk u) * PresentedGroup.mk _ (FreeGroup.mk v) := by
  rw [← FreeGroup.mul_mk, map_mul]

theorem mem_phanA3Exps {s t : Int} (hs : -2 ≤ s ∧ s ≤ 2) (ht : -2 ≤ t ∧ t ≤ 2)
    (h : (s, t) ≠ (0, 0)) : (s, t) ∈ phanA3Exps := by
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨ht1, ht2⟩ := ht
  interval_cases s <;> interval_cases t <;> first | exact absurd rfl h | decide

theorem kerA_zpow_mul_kerB_zpow_ne_one {s t : Int}
    (hs : -2 ≤ s ∧ s ≤ 2) (ht : -2 ≤ t ∧ t ≤ 2) (h : (s, t) ≠ (0, 0)) :
    kerA ^ s * kerB ^ t ≠ 1 := by
  intro h1
  have hw : (powWord phanA3U1 s ++ powWord phanA3U2 t, 3) ∈ phanA3KernelWords :=
    List.mem_map.mpr ⟨(s, t), mem_phanA3Exps hs ht h, rfl⟩
  have h3 := three_dvd_orderOf_phanA3 hw
  rw [mk_append, mk_powWord, mk_powWord] at h3
  change 3 ∣ orderOf (kerA ^ s * kerB ^ t) at h3
  rw [h1, orderOf_one] at h3
  omega

theorem phanP_kerA : phanP kerA = 1 := phanP_mk_u1

theorem phanP_kerB : phanP kerB = 1 := phanP_mk_u2

theorem nine_le_card_ker : 9 ≤ Nat.card phanP.ker := by
  have : Finite PhanA3Group := card_phanA3Group_le.1
  let f : Fin 3 × Fin 3 → phanP.ker := fun ij =>
    ⟨kerA ^ (ij.1.val : ℤ) * kerB ^ (ij.2.val : ℤ), by
      rw [MonoidHom.mem_ker, map_mul, map_zpow, map_zpow, phanP_kerA, phanP_kerB, one_zpow,
        one_zpow, mul_one]⟩
  have hinj : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hij
    have h : kerA ^ (i.val : ℤ) * kerB ^ (j.val : ℤ) =
        kerA ^ (i'.val : ℤ) * kerB ^ (j'.val : ℤ) := congrArg Subtype.val hij
    have h1 : kerA ^ ((i.val : ℤ) - i'.val) * kerB ^ ((j.val : ℤ) - j'.val) = 1 := by
      calc kerA ^ ((i.val : ℤ) - i'.val) * kerB ^ ((j.val : ℤ) - j'.val)
          = kerA ^ (-(i'.val : ℤ)) * (kerA ^ (i.val : ℤ) * kerB ^ (j.val : ℤ)) *
              kerB ^ (-(j'.val : ℤ)) := by group
        _ = kerA ^ (-(i'.val : ℤ)) * (kerA ^ (i'.val : ℤ) * kerB ^ (j'.val : ℤ)) *
              kerB ^ (-(j'.val : ℤ)) := by rw [h]
        _ = 1 := by group
    by_contra hne
    have hi := i.isLt
    have hi' := i'.isLt
    have hj := j.isLt
    have hj' := j'.isLt
    refine kerA_zpow_mul_kerB_zpow_ne_one (s := (i.val : ℤ) - i'.val) (t := (j.val : ℤ) - j'.val)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ?_ h1
    intro hst
    simp only [Prod.mk.injEq] at hst
    obtain ⟨hs0, ht0⟩ := hst
    have e1 : i = i' := Fin.ext (by omega)
    have e2 : j = j' := Fin.ext (by omega)
    exact hne (by rw [e1, e2])
  simpa using Nat.card_le_card_of_injective f hinj

theorem card_su4 : Nat.card (Su K9 3 1 4) = 13063680 := by
  rw [Nat.card_congr (MulEquiv.subgroupCongr (SUid_eq_statedSU card_K9 4)).toEquiv]
  exact card_statedSU_four_three (card_K9.trans (by norm_num))

theorem card_eq_mul_ker : Nat.card PhanA3Group = Nat.card (Su K9 3 1 4) * Nat.card phanP.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup phanP.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective phanP phanP_surjective).toEquiv]

theorem card_ker_le : Nat.card phanP.ker ≤ 9 := by
  have h1 := card_phanA3Group_le.2
  rw [card_eq_mul_ker, card_su4] at h1
  omega

theorem card_ker_eq : Nat.card phanP.ker = 9 :=
  le_antisymm card_ker_le nine_le_card_ker

theorem ker_comm :
    ∀ x ∈ phanP.ker, ∀ y ∈ phanP.ker, x * y = y * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : IsMulCommutative phanP.ker :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [card_ker_eq]; norm_num)
  intro x hx y hy
  exact congrArg Subtype.val (hc.is_comm.comm (⟨x, hx⟩ : phanP.ker) ⟨y, hy⟩)

theorem phanP_ker :
    ∀ e ∈ phanP.ker, e ∈ Subgroup.center PhanA3Group ∧ ∃ k : ℕ, e ^ 3 ^ k = 1 := by
  have : Finite PhanA3Group := card_phanA3Group_le.1
  let eS : Su K9 3 1 4 ≃* StatedSU 4 (3 ^ 1) K9 :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU card_K9 4)
  have hK9 : Nat.card K9 = 9 := card_K9.trans (by norm_num)
  have hker : (eS.toMonoidHom.comp phanP).ker = phanP.ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff eS eS.injective]
  have hcent : phanP.ker ≤ Subgroup.center PhanA3Group := by
    have : Finite K9 := inferInstance
    rw [← hker]
    refine ker_le_center_of_card_lt (isQuasisimple_statedSU_four_three hK9)
      (eS.toMonoidHom.comp phanP) (eS.surjective.comp phanP_surjective)
      (by rw [hker]; exact ker_comm) ?_
    rw [hker, card_ker_eq, card_center_statedSU_four_three hK9, card_statedSU_four_three hK9]
    decide
  intro e he
  refine ⟨hcent he, 2, ?_⟩
  have h9 : (⟨e, he⟩ : phanP.ker) ^ Nat.card phanP.ker = 1 := pow_card_eq_one'
  rw [card_ker_eq] at h9
  have := congrArg Subtype.val h9
  simpa using this

end CFSG.ClassicalInvolution.Phan.Q3G
