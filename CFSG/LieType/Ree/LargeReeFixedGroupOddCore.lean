module

public import CFSG.LieType.Ree.LargeReeCenterTrivial
public import CFSG.LieType.Simplicity.TitsModel

public noncomputable section

namespace CFSG.LieType.Ree.ReeTag

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Simplicity

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime]

variable (K) in
@[expose] def reeFixedEquivReeGamma
    (m : ℕ) : reeFixed F4 K m ≃* F4.reeGamma K m :=
  ((reeFixed F4 K m).equivMapOfInjective (adjointGroup F4.tag K).subtype
    Subtype.val_injective).trans
    (MulEquiv.subgroupCongr (by rw [reeGamma_eq_reeFixedGroup, reeFixedGroup_eq_map_reeFixed]))

theorem coe_reeFixedEquivReeGamma
    (m : ℕ) (x : reeFixed F4 K m) :
    (reeFixedEquivReeGamma K m x : ModGL F4.tag K) = ((x : adjointGroup F4.tag K) :
      ModGL F4.tag K) :=
  rfl

theorem involution_mem_reeGamma
    {m : ℕ} (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    ∃ y ∈ F4.reeGamma K m, orderOf y = 2 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have hmem : xUnit F4.tag K largeReeI1 1 * xUnit F4.tag K largeReeI4 1 ∈
      (F4.reeFixedOrbitUnipotent K m ⟨0, by decide⟩ : Set (ModGL F4.tag K)) := by
    rw [coe_reeFixedOrbitUnipotent_zero hK]
    exact ⟨1, by simp⟩
  refine ⟨_, (Subgroup.mem_inf.1 hmem).2, orderOf_eq_prime ?_ ?_⟩
  · have hc := (largeRee_commute_xx (K := K) 1 1).eq
    calc (xUnit F4.tag K largeReeI1 1 * xUnit F4.tag K largeReeI4 1) ^ 2 =
        xUnit F4.tag K largeReeI1 1 *
          (xUnit F4.tag K largeReeI4 1 * xUnit F4.tag K largeReeI1 1) *
            xUnit F4.tag K largeReeI4 1 := by rw [sq]; group
      _ = xUnit F4.tag K largeReeI1 1 *
          (xUnit F4.tag K largeReeI1 1 * xUnit F4.tag K largeReeI4 1) *
            xUnit F4.tag K largeReeI4 1 := by rw [hc]
      _ = xUnit F4.tag K largeReeI1 (1 + 1) * xUnit F4.tag K largeReeI4 (1 + 1) := by
          rw [xUnit_add, xUnit_add]; group
      _ = 1 := by rw [CharTwo.add_self_eq_zero, xUnit_zero, xUnit_zero, mul_one]
  · intro h
    have h' : xUnit F4.tag K largeReeI1 1 * xUnit F4.tag K largeReeI4 1 =
        xUnit F4.tag K largeReeI1 0 * xUnit F4.tag K largeReeI4 0 := by
      rw [h, xUnit_zero, xUnit_zero, mul_one]
    exact one_ne_zero (largeRee_x_inj h').1

theorem not_two_dvd_of_odd {G : Type*} [Group G] {M : Subgroup G} (hodd : Odd (Nat.card M))
    {y : G} (hy : y ∈ M) (hy2 : orderOf y = 2) : False := by
  have h := orderOf_dvd_natCard (⟨y, hy⟩ : M)
  rw [Subgroup.orderOf_mk, hy2] at h
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)

theorem eq_bot_of_normal_of_odd
    {m : ℕ} (hK : Nat.card K = 2 ^ (2 * m + 1))
    (M : Subgroup (F4.reeGamma K m)) (hM : M.Normal) (hodd : Odd (Nat.card M)) : M = ⊥ := by
  set e := reeFixedEquivReeGamma K m with he
  set M' := M.comap e.toMonoidHom with hM'
  have hMn : M'.Normal := hM.comap _
  have hmap : M'.map e.toMonoidHom = M := Subgroup.map_comap_eq_self_of_surjective e.surjective M
  have hodd' : Odd (Nat.card M') := by
    rwa [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hmap]
  have hinv : ∀ x ∈ M', orderOf x = 2 → False := fun x hx hx2 =>
    not_two_dvd_of_odd hodd' hx hx2
  rcases Nat.eq_zero_or_pos m with rfl | hm
  ·
    have hK2 : Nat.card K = 2 := by simpa using hK
    set T := titsData K hK2
    rcases T.le_of_normal hK2 M' with h | h
    · rw [← hmap, h, Subgroup.map_bot]
    · exfalso
      exact hinv T.g₀ (h T.g₀_mem) (orderOf_eq_prime (by rw [sq, T.g₀_mul_self]) T.g₀_ne_one)
  ·
    have hperf : Group.IsPerfect (reeFixed F4 K m) := ⟨commutator_reeFixed_F4 m hm hK⟩
    have hB := isSolvable_reeBorelPart (t := F4) (K := K) m
    have hgen : Subgroup.normalClosure (reeUnipPart F4 K m : Set (reeFixed F4 K m)) = ⊤ :=
      CFSG.LieType.TitsSimplicity.eq_top_of_sup_eq_top hperf hB
        (sup_reeBorelPart_eq_top_F4 _ (not_normalClosure_le_reeBorelPart m))
    by_cases hMB : M' ≤ reeBorelPart F4 K m
    ·
      have hcen := le_center_of_le_reeBorelPart hgen M' hMB
      rw [eq_bot_iff, ← large_Ree_fixed_group_center_trivial m K hK, ← hmap]
      rintro _ ⟨x, hx, rfl⟩
      refine Subgroup.mem_center_iff.2 fun z => ?_
      obtain ⟨w, rfl⟩ := e.surjective z
      change e w * e x = e x * e w
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 (hcen hx)) w]
    ·
      exfalso
      have htop := CFSG.LieType.TitsSimplicity.eq_top_of_sup_eq_top hperf hB
        (sup_reeBorelPart_eq_top_F4 M' hMB)
      obtain ⟨y, hy, hy2⟩ := involution_mem_reeGamma (m := m) hK
      refine hinv (e.symm ⟨y, hy⟩) (htop ▸ Subgroup.mem_top _) ?_
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy2]

theorem F4_Ree_fixed_group_odd_core_including_field_two
    (m : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    CFSG.oddCore (F4.reeGamma K m) = ⊥ ∧
      CFSG.piCore {p : Nat.Primes | p.val ≠ 2} (F4.reeGamma K m) = ⊥ := by
  have h : CFSG.oddCore (F4.reeGamma K m) = ⊥ :=
    sSup_eq_bot.2 fun M hM => eq_bot_of_normal_of_odd hK M hM.1 hM.2
  exact ⟨h, by rw [← CFSG.oddCore_eq_piCore, h]⟩

end CFSG.LieType.Ree.ReeTag
