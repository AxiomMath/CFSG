module

import CFSG.Mathlib.GroupTheory.PermCommute
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

theorem zpowers_eq_and_card_of_central {Y : Type*} [Group Y] (Z : Subgroup Y) [Z.Normal]
    (hZ : Nat.card Z = 2) (e : Y ⧸ Z ≃* Equiv.Perm (Fin 5)) {t : Y} (ht : ∀ y, t * y = y * t)
    (ht1 : t ≠ 1) : Z = Subgroup.zpowers t ∧ Nat.card Y = 240 := by
  have hmk : ((t : Y ⧸ Z)) = 1 := by
    apply e.injective
    rw [map_one]
    refine CFSG.perm_eq_one_of_forall_commute (by simp) fun g => ?_
    have hc : g * e ↑t * g⁻¹ = e ↑t := by
      obtain ⟨y, rfl⟩ := e.surjective g
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
      rw [← map_mul, ← map_inv, ← map_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul, ← ht y, mul_inv_cancel_right]
    exact (mul_inv_eq_iff_eq_mul.1 hc).symm
  have htZ : t ∈ Z := (QuotientGroup.eq_one_iff t).1 hmk
  have hle : Subgroup.zpowers t ≤ Z := (Subgroup.zpowers_le).2 htZ
  have hd : Nat.card (Subgroup.zpowers t) ∣ 2 := hZ ▸ Subgroup.card_dvd_of_le hle
  have hne : Nat.card (Subgroup.zpowers t) ≠ 1 := fun h =>
    ht1 (Subgroup.zpowers_eq_bot.1 (Subgroup.eq_bot_of_card_eq _ h))
  have hcard : Nat.card (Subgroup.zpowers t) = 2 :=
    ((Nat.dvd_prime Nat.prime_two).1 hd).resolve_left hne
  haveI : Finite Z := Nat.finite_of_card_ne_zero (by omega)
  refine ⟨(Subgroup.eq_of_le_of_card_ge hle (by omega)).symm, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Z, Nat.card_congr e.toEquiv, hZ,
    Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem perm_five_normal_two_group_eq_bot (N : Subgroup (Equiv.Perm (Fin 5))) [N.Normal]
    (hN : IsPGroup 2 N) : N = ⊥ := by
  have hA : ∀ x ∈ N, x ∈ alternatingGroup (Fin 5) → x = 1 := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (alternatingGroup (Fin 5)))
      with h | h
    · intro x hx hxA
      have : (⟨x, hxA⟩ : alternatingGroup (Fin 5)) ∈ N.subgroupOf (alternatingGroup (Fin 5)) :=
        hx
      rw [h] at this
      simpa using this
    · exfalso
      have hle : alternatingGroup (Fin 5) ≤ N := by
        intro x hxA
        have : (⟨x, hxA⟩ : alternatingGroup (Fin 5)) ∈ N.subgroupOf (alternatingGroup (Fin 5)) :=
          h ▸ Subgroup.mem_top _
        exact this
      haveI := Fact.mk Nat.prime_two
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (hN.to_le hle)
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at hn
      have h3 : 3 ∣ 2 ^ n := hn ▸ (by decide : 3 ∣ Nat.factorial 5 / 2)
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  have hc : ∀ g : Equiv.Perm (Fin 5), g * x * g⁻¹ = x := by
    intro g
    have hy : g * x * g⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance x hx g
    have := hA (x * (g * x * g⁻¹)⁻¹) (N.mul_mem hx (N.inv_mem hy)) (by
      rw [Equiv.Perm.mem_alternatingGroup]
      simp only [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, map_mul, map_inv]
      generalize Equiv.Perm.sign x = a
      generalize Equiv.Perm.sign g = b
      revert a b
      decide)
    exact (mul_inv_eq_one.1 this).symm
  exact CFSG.perm_eq_one_of_forall_commute (by simp) fun g =>
    (mul_inv_eq_iff_eq_mul.1 (hc g)).symm

theorem step2 {G : Type*} [Group G] {Y : Subgroup G}
    (hY : IsNonsplitDoubleCoverOfS5 ↥Y) {t : G} (htY : t ∈ Y) (ht : ∀ y ∈ Y, t * y = y * t)
    (ht1 : t ≠ 1) :
    Nat.card ↥Y = 240 ∧
      ∀ N : Subgroup G, N ≤ Y → (∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N) → IsPGroup 2 ↥N →
        N ≤ Subgroup.zpowers t := by
  obtain ⟨Z, hZn, hZcard, ⟨e⟩, _⟩ := hY
  haveI : Z.Normal := hZn
  let t' : ↥Y := ⟨t, htY⟩
  have ht'central : ∀ y : ↥Y, t' * y = y * t' := by
    intro y
    apply Subtype.ext
    change (t' : G) * (y : G) = (y : G) * (t' : G)
    exact ht y.1 y.2
  have ht'1 : t' ≠ 1 := by
    intro h
    exact ht1 (congrArg Subtype.val h)
  obtain ⟨hZeq, hcard⟩ := zpowers_eq_and_card_of_central Z hZcard e ht'central ht'1
  refine ⟨hcard, ?_⟩
  intro N hNY hNnorm hN2
  let N' : Subgroup ↥Y := N.subgroupOf Y
  have hN'normal : N'.Normal :=
    (Subgroup.normal_subgroupOf_iff hNY).2 fun h k hh hk => hNnorm k hk h hh
  let π : ↥Y →* Equiv.Perm (Fin 5) := e.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hπsurj : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hN'2 : IsPGroup 2 ↥N' := hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNY).symm
  haveI : (N'.map π).Normal := hN'normal.map π hπsurj
  have hmapbot : N'.map π = ⊥ := perm_five_normal_two_group_eq_bot _ (hN'2.map π)
  intro n hn
  have hn' : (⟨n, hNY hn⟩ : ↥Y) ∈ N' := hn
  have hπn : π ⟨n, hNY hn⟩ = 1 := by
    have hmem : π ⟨n, hNY hn⟩ ∈ N'.map π := ⟨⟨n, hNY hn⟩, hn', rfl⟩
    rw [hmapbot] at hmem
    simpa using hmem
  have hmk1 : (QuotientGroup.mk' Z ⟨n, hNY hn⟩ : ↥Y ⧸ Z) = 1 := by
    apply e.injective
    rw [map_one]
    simpa [π] using hπn
  have hmemZ : (⟨n, hNY hn⟩ : ↥Y) ∈ Z := (QuotientGroup.eq_one_iff _).1 hmk1
  rw [hZeq] at hmemZ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmemZ
  refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
  have hcoe : ((t' ^ k : ↥Y) : G) = n := by
    simpa using congrArg (Subtype.val) hk
  simpa [Subgroup.coe_zpow] using hcoe

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
