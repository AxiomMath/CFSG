module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.BMGeom
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Reduce
public import CFSG.Monster.Existence.Defs

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Subgroup CFSG.Blueprint CFSG.Monster.Existence

section Abstract

theorem orderOf_mk_eq_of_isPGroup {H : Type*} [Group H] {N : Subgroup H} [N.Normal]
    (hN : IsPGroup 2 N) {g : H} (hodd : Odd (orderOf g)) :
    orderOf (QuotientGroup.mk g : H ⧸ N) = orderOf g := by
  apply Nat.dvd_antisymm
  · exact orderOf_map_dvd (QuotientGroup.mk' N) g
  · set m := orderOf (QuotientGroup.mk g : H ⧸ N) with hm
    have hgm : g ^ m ∈ N := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact pow_orderOf_eq_one _
    obtain ⟨k, hk⟩ := hN ⟨g ^ m, hgm⟩
    have hk' : (g ^ m) ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    obtain ⟨j, -, h1⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk')
    have h2 : orderOf (g ^ m) ∣ orderOf g := orderOf_pow_dvd m
    have hk0 : j = 0 := by
      by_contra hne
      have h2k : 2 ∣ 2 ^ j := dvd_pow_self 2 hne
      rw [← h1] at h2k
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h2k.trans h2))
    rw [hk0, pow_zero] at h1
    have h3 : g ^ m = 1 := orderOf_eq_one_iff.1 h1
    exact orderOf_dvd_of_pow_eq_one h3

theorem false_of_noOrder_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {x : X}
    {n : ℕ} (hx : orderOf x = n) (h : NoOrder n Y) : False :=
  h (e x) (by rw [MulEquiv.orderOf_eq]; exact hx)

variable {G : Type} [Group G]

theorem noOrder65_of_involution (hE : MonsterExistenceStatement G)
    (hB65 : NoOrder 65 NativeSporadic.B) (hCo65 : NoOrder 65 NativeSporadic.Co1)
    (hinv : ∀ g : G, orderOf g = 65 → ∃ t : G, orderOf t = 2 ∧ t * g = g * t) :
    NoOrder 65 G := by
  obtain ⟨-, a, z, ha, hz, -, hcls, hA, hBz, -⟩ := hE
  intro g hg
  obtain ⟨t, ht, htg⟩ := hinv g hg
  have hgmem : g ∈ cent t := mem_centralizer_singleton_iff.2 htg.symm
  have hg'o : orderOf (⟨g, hgmem⟩ : ↥(cent t)) = 65 := by rw [Subgroup.orderOf_mk]; exact hg
  have hodd : Odd (orderOf (⟨g, hgmem⟩ : ↥(cent t))) := by rw [hg'o]; decide
  rcases hcls t ht with h | h
  · obtain ⟨-, hzc, ⟨e⟩⟩ := hA t h
    have hc : Nat.card ↥(center ↥(cent t)) = 2 := by
      rw [← Subgroup.card_map_of_injective (cent t).subtype_injective, hzc, Nat.card_zpowers, ht]
    have hN : IsPGroup 2 (center ↥(cent t)) :=
      IsPGroup.of_card (n := 1) (by rw [hc, pow_one])
    have hmk := orderOf_mk_eq_of_isPGroup hN hodd
    exact @false_of_noOrder_of_mulEquiv _ NativeSporadic.B _ Units.instGroup e
      (QuotientGroup.mk (⟨g, hgmem⟩ : ↥(cent t))) 65 (hmk.trans hg'o) hB65
  · obtain ⟨-, -, -, ⟨e⟩, -, -⟩ := hBz t h
    have hN : IsPGroup 2 (CFSG.pCore 2 ↥(cent t)) := CFSG.pCore_isPGroup
    haveI : (CFSG.pCore 2 ↥(cent t)).Normal := CFSG.pCore_normal
    have hmk := orderOf_mk_eq_of_isPGroup hN hodd
    exact @false_of_noOrder_of_mulEquiv _ NativeSporadic.Co1 _ Units.instGroup e
      (QuotientGroup.mk (⟨g, hgmem⟩ : ↥(cent t))) 65 (hmk.trans hg'o) hCo65

theorem ncard_invComm_map {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (x : X) :
    (invComm (e x)).ncard = (invComm x).ncard := by
  have h : invComm (e x) = e '' invComm x := by
    ext f
    constructor
    · rintro ⟨hf2, hf1, hfx⟩
      refine ⟨e.symm f, ⟨?_, ?_, ?_⟩, by simp⟩
      · apply e.injective
        rw [map_mul, map_one, MulEquiv.apply_symm_apply]
        exact hf2
      · intro h
        apply hf1
        have := congrArg e h
        simpa using this
      · apply e.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact hfx
    · rintro ⟨f', ⟨hf2, hf1, hfx⟩, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [← map_mul, hf2, map_one]
      · intro h
        exact hf1 (e.injective (by rw [h, map_one]))
      · rw [← map_mul, ← map_mul, hfx]
  rw [h, Set.ncard_image_of_injective _ e.injective]

end Abstract

end CFSG.HardMathSupport.Dickson.Sec6.I1431
