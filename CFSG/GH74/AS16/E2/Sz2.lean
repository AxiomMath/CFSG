module

public import CFSG.GH74.AS16.E2.Sz2G
public import CFSG.GH74.AS16.E2.Sz2Table

public section

namespace CFSG.GH74.AS16.E2

open Subgroup CFSG CFSG.Blueprint
open CFSG.GH74.E2 hiding Hyp

theorem noPair2Sz8 :
    NoPairOf Shape2Sz8 := by
  intro G _ _ T z L hcfg _ hsh
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsh' := hsh
  obtain ⟨hq, hZc, hS⟩ := hsh'
  have hsyl := hcfg.isSylowOf_inf
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hsyl
  set Q : Subgroup ↥L := ((T : Subgroup G) ⊓ L).subgroupOf L with hQdef
  have hQ2 : IsPGroup 2 Q := hsyl.2.1.comap_subtype
  have hQi : ¬ 2 ∣ Q.index := hsyl.2.2
  have hmemQ : ∀ k : ↥L, k ∈ Q ↔ (k : G) ∈ (T : Subgroup G) ⊓ L := fun k =>
    Subgroup.mem_subgroupOf
  obtain ⟨AK, hAKQ, hAKcomm, hAK2, hAKcard, hZAK, hAKQcomm, hAKsq, hAKmov⟩ :=
    (twoSzTable_of_shape hsh Q hQ2 hQi).exists_A
  have hZp : IsPGroup 2 ↥(center ↥L) := IsPGroup.of_card (n := 1) (by rw [hZc]; norm_num)
  have hZQ : center ↥L ≤ Q := hZp.le_sylow_of_normal (hQ2.toSylow hQi)
  have hZsq : ∀ k ∈ center ↥L, k ^ 2 = 1 := by
    intro k hk
    have := pow_card_eq_one' (G := ↥(center ↥L)) (x := ⟨k, hk⟩)
    rw [hZc] at this
    exact congrArg Subtype.val this
  have hZg : L ⊓ centralizer (L : Set G) = (center ↥L).map L.subtype := by
    ext x
    constructor
    · rintro ⟨hxL, hxc⟩
      refine ⟨⟨x, hxL⟩, ?_, rfl⟩
      show (⟨x, hxL⟩ : ↥L) ∈ center ↥L
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxc g g.2)
    · rintro ⟨k, hk, rfl⟩
      refine ⟨k.2, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hk ⟨h, hh⟩)
  have hdec := hcfg.decomp2 (fun l hl hc => by
    have hlc : (⟨l, hl⟩ : ↥L) ∈ center ↥L := Subgroup.mem_center_iff.2 fun g =>
      Subtype.ext (hc g g.2).symm
    exact congrArg Subtype.val (hZsq _ hlc))
    (out_inner_of_shape2Sz8 hsh)
  set A : Subgroup G := AK.map L.subtype with hA
  have hmemA : ∀ x : G, x ∈ A ↔ ∃ k ∈ AK, (k : G) = x := fun x => Subgroup.mem_map
  have hAT : A ≤ (T : Subgroup G) ⊓ L := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := (hmemA x).1 hx
    exact (hmemQ k).1 (hAKQ hk)
  refine false_of_sz2 hcfg hdec hAT ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a ha b hb
    obtain ⟨k, hk, rfl⟩ := (hmemA a).1 ha
    obtain ⟨k', hk', rfl⟩ := (hmemA b).1 hb
    exact congrArg Subtype.val (hAKcomm k hk k' hk')
  · intro a ha
    obtain ⟨k, hk, rfl⟩ := (hmemA a).1 ha
    exact congrArg Subtype.val (hAK2 k hk)
  · rw [hA, Subgroup.card_map_of_injective L.subtype_injective, hAKcard]
  · rw [hZg, Subgroup.card_map_of_injective L.subtype_injective, hZc]
  · intro x hx
    rw [hZg] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact (hmemQ k).1 (hZQ hk) |>.1
  · intro x hx
    rw [hZg] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact (hmemA _).2 ⟨k, hZAK hk, rfl⟩
  · intro x hx a ha
    obtain ⟨k, hk, rfl⟩ := (hmemA a).1 ha
    rw [hZg]
    exact ⟨⟨x, hx.2⟩ * k * ⟨x, hx.2⟩⁻¹ * k⁻¹,
      hAKQcomm ⟨x, hx.2⟩ ((hmemQ _).2 hx) k hk, rfl⟩
  · intro s hs hs2
    rw [hZg] at hs2
    obtain ⟨k, hk, hks⟩ := hs2
    have hsk : (⟨s, hs.2⟩ : ↥L) * ⟨s, hs.2⟩ ∈ center ↥L := by
      have : k = ⟨s, hs.2⟩ * ⟨s, hs.2⟩ := Subtype.ext hks
      rw [← this]; exact hk
    exact (hmemA s).2 ⟨⟨s, hs.2⟩, hAKsq ⟨s, hs.2⟩ ((hmemQ _).2 hs) hsk, rfl⟩
  · intro b hb hbZ
    obtain ⟨k, hk, rfl⟩ := (hmemA b).1 hb
    have hkZ : k ∉ center ↥L := fun h => hbZ (by rw [hZg]; exact ⟨k, h, rfl⟩)
    obtain ⟨x, hx, hxk⟩ := hAKmov k hk hkZ
    refine ⟨(x : G), (hmemQ x).1 hx, fun h => hxk ?_⟩
    exact Subtype.ext h

end CFSG.GH74.AS16.E2
