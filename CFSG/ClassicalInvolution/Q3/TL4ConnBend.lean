module

public import CFSG.ClassicalInvolution.Q3.TL4ConnDefs
public import CFSG.ClassicalInvolution.Q3.TL4ConnBendOut
public import CFSG.ClassicalInvolution.Q3.TL4ConnBendSyl

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open Subgroup CFSG CFSG.Open CFSG.ClassicalInvolution QuaternionGroup
  CFSG.ComponentClassification.OuterAutomorphisms Bend

theorem tightBenderEndR : TightBenderEndR := by
  intro Y _ _ R S t hT hB hC
  classical
  set F := genFittingFStar Y with hF
  have hFn : F.Normal := genFittingFStar_normal Y
  let ψ : Y →* Outer ↥F := (QuotientGroup.mk' (inner ↥F)).comp MulAut.conjNormal
  have hker : ∀ y : Y, ψ y = 1 → y ∈ F := by
    intro y hy
    have h1 : (MulAut.conjNormal y : MulAut ↥F) ∈ inner ↥F :=
      (QuotientGroup.eq_one_iff (N := inner ↥F) _).mp hy
    obtain ⟨f, hf⟩ := MonoidHom.mem_range.mp h1
    set f₀ : Y := (f : Y) with hf₀
    have hc : y⁻¹ * f₀ ∈ centralizer (F : Set Y) := by
      rw [mem_centralizer_iff]
      intro w hw
      have h2 := congrArg (fun α : MulAut ↥F => ((α ⟨w, hw⟩ : ↥F) : Y)) hf
      simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h2
      calc w * (y⁻¹ * f₀) = y⁻¹ * (y * w * y⁻¹) * f₀ := by group
        _ = y⁻¹ * (f₀ * w * f₀⁻¹) * f₀ := by rw [← h2]
        _ = y⁻¹ * f₀ * w := by group
    rw [hC, mem_bot, inv_mul_eq_one] at hc
    rw [hc]
    exact f.2
  obtain ⟨r, hr, ⟨e⟩⟩ := hT.quat
  set n := 2 ^ (r - 2) with hn_def
  have hn : 2 ≤ n :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : NeZero n := ⟨by omega⟩
  let ι : QuaternionGroup n →* Y :=
    R.subtype.comp ((S : Subgroup R).subtype.comp e.symm.toMonoidHom)
  have hι : Function.Injective ι :=
    Subtype.val_injective.comp (Subtype.val_injective.comp e.symm.injective)
  have hιR : ∀ g, ι g ∈ R := fun g => ((e.symm g : (S : Subgroup R)) : R).2
  have han : orderOf (a n : QuaternionGroup n) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [sq, a_mul_a, ← Nat.cast_add, ← two_mul, ZMod.natCast_self, a_zero]
    · rw [one_def, Ne, a.injEq]
      intro h0
      rw [show (0 : ZMod (2 * n)) = ((0 : ℕ) : ZMod (2 * n)) by simp,
        ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega : n < 2 * n), Nat.zero_mod] at h0
      omega
  have hιt : ι (a n) = t :=
    hT.eq_of_orderOf_eq_two (hιR _) (by rw [orderOf_injective ι hι, han])
  have hQ2 : IsPGroup 2 (QuaternionGroup n) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.of_card (n := r) ?_
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card, hn_def,
      show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  obtain ⟨g, hgF, hg1, hgt⟩ : ∃ g : QuaternionGroup n, ι g ∈ F ∧ g ≠ 1 ∧ g ≠ a n := by
    have hTot := twoTot_outer (F := ↥F) hB
    have hP : IsPGroup 2 ↥(ψ.comp ι).range :=
      hQ2.of_surjective (ψ.comp ι).rangeRestrict (MonoidHom.rangeRestrict_surjective _)
    rcases hTot _ hP _ ⟨a 1, rfl⟩ _ ⟨xa 0, rfl⟩ with h | h
    · obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
      refine ⟨a 1 * (xa 0) ^ (-k), hker _ ?_,
        a_one_mul_ne hn (zpow_mem (mem_zpowers _) _)⟩
      have hk' : ψ (ι (xa 0)) ^ k = ψ (ι (a 1)) := hk
      rw [map_mul, map_mul, map_zpow, map_zpow, zpow_neg, hk', mul_inv_cancel]
    · obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
      refine ⟨xa 0 * (a 1) ^ (-k), hker _ ?_, xa_zero_mul_ne (zpow_mem (mem_zpowers _) _)⟩
      have hk' : ψ (ι (a 1)) ^ k = ψ (ι (xa 0)) := hk
      rw [map_mul, map_mul, map_zpow, map_zpow, zpow_neg, hk', mul_inv_cancel]
  set x := ι g with hx
  have hxR := hιR g
  have hx1 : x ≠ 1 := fun h => hg1 (hι (by rw [← hx, h, map_one]))
  have hx2 : x * x ≠ 1 := by
    intro h
    have hord : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact h) hx1
    exact hgt (hι ((hT.eq_of_orderOf_eq_two hxR hord).trans hιt.symm))
  obtain ⟨j, hj⟩ : ∃ j : ℕ, orderOf x = 2 ^ j := by
    obtain ⟨j₀, hj₀⟩ := hQ2 g
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (orderOf_dvd_of_pow_eq_one hj₀)
    exact ⟨j, by rw [hx, orderOf_injective ι hι, hj]⟩
  have hj2 : 2 ≤ j := by
    by_contra h
    interval_cases j
    · exact hx1 (orderOf_eq_one_iff.mp (by rw [hj, pow_zero]))
    · apply hx2
      have h2 : x ^ (orderOf x) = 1 := pow_orderOf_eq_one x
      rw [hj, pow_one, sq] at h2
      exact h2
  have htx : x ^ (2 ^ (j - 1)) = t := by
    refine hT.eq_of_orderOf_eq_two (pow_mem hxR _) ?_
    rw [orderOf_pow_of_dvd (by positivity) (hj ▸ pow_dvd_pow 2 (by omega)), hj,
      Nat.pow_div (by omega) (by norm_num)]
    rw [show j - (j - 1) = 1 by omega, pow_one]
  have htF : t ∈ F := htx ▸ pow_mem hgF _
  set x' : ↥F := ⟨x, hgF⟩ with hx'
  set t' : ↥F := ⟨t, htF⟩ with ht'
  have hzp : IsPGroup 2 ↥(zpowers x') := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.of_card (n := j) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hj]
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  have hx'Q : x' ∈ (Q : Subgroup ↥F) := hQ (mem_zpowers x')
  have ht'Q : t' ∈ (Q : Subgroup ↥F) := by
    have : t' = x' ^ (2 ^ (j - 1)) := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact htx.symm)
    rw [this]
    exact pow_mem hx'Q _
  have ht'2 : t' * t' = 1 := Subtype.ext (by
    simpa [← sq] using pow_orderOf_eq_one t |>.symm.trans (by rw [hT.order]) |>.symm)
  have htc := Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one hB Q ht'Q ht'2
  have hBF := Timmesfeld.Bridge.Asc72.IsBenderGroup.benderBorelFacts hB Q
  have hcomm : ∀ y : ↥(Q : Subgroup ↥F),
      (⟨x', hx'Q⟩ : ↥(Q : Subgroup ↥F)) * y * (⟨x', hx'Q⟩ : ↥(Q : Subgroup ↥F))⁻¹ * y⁻¹ = 1 ∨
        (⟨x', hx'Q⟩ : ↥(Q : Subgroup ↥F)) * y * (⟨x', hx'Q⟩ : ↥(Q : Subgroup ↥F))⁻¹ * y⁻¹ =
          ⟨t', ht'Q⟩ := by
    rintro ⟨y, hy⟩
    obtain ⟨hcQ, hccen⟩ := hBF.commutator_central x' hx'Q y hy
    have hcc : (x' * y * x'⁻¹ * y⁻¹) * (x' * y * x'⁻¹ * y⁻¹) = 1 :=
      Timmesfeld.Bridge.Asc72.IsBenderGroup.mul_self_eq_one_of_commute hB Q hcQ
        fun q hq => (hccen q hq).symm
    have hyN : (y : Y) ∈ normalizer (R : Set Y) := by
      refine hT.le_normalizer ?_
      rw [mem_centralizer_singleton_iff]
      have := congrArg Subtype.val (htc y hy).eq
      simpa using this.symm
    have hcR : ((x' * y * x'⁻¹ * y⁻¹ : ↥F) : Y) ∈ R := by
      have h1 : (y : Y) * x⁻¹ * (y : Y)⁻¹ ∈ R := (mem_normalizer_iff.mp hyN x⁻¹).mp (inv_mem hxR)
      have e1 : ((x' * y * x'⁻¹ * y⁻¹ : ↥F) : Y) = x * ((y : Y) * x⁻¹ * (y : Y)⁻¹) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hx']
        group
      rw [e1]
      exact mul_mem hxR h1
    by_cases h1 : x' * y * x'⁻¹ * y⁻¹ = 1
    · exact Or.inl (Subtype.ext h1)
    · right
      apply Subtype.ext
      apply Subtype.ext
      have hord : orderOf ((x' * y * x'⁻¹ * y⁻¹ : ↥F) : Y) = 2 := by
        refine orderOf_eq_prime ?_ ?_
        · rw [sq, ← Subgroup.coe_mul, hcc, Subgroup.coe_one]
        · exact fun h => h1 (Subtype.ext h)
      exact hT.eq_of_orderOf_eq_two hcR hord
  have hcen := bigCommT_sylow_of_isBenderGroup hB Q ⟨x', hx'Q⟩ ⟨t', ht'Q⟩ hcomm
  have hx'2 : x' * x' = 1 :=
    Timmesfeld.Bridge.Asc72.IsBenderGroup.mul_self_eq_one_of_commute hB Q hx'Q
      fun q hq => congrArg Subtype.val (hcen ⟨q, hq⟩).eq
  exact hx2 (congrArg Subtype.val hx'2)

end CFSG.ClassicalInvolution.Q3.TL4
