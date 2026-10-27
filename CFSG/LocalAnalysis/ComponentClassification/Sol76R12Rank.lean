module

public import CFSG.Walter.W67.Section5.MaxClass
public import CFSG.GH74.Uniqueness.SU.SU1CyclicIdx
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.ComponentClassification.Sol76T13.R12

open Subgroup

theorem card_le_four_of_card_centralizer {T : Type} [Group T] [Finite T] (hT : IsPGroup 2 T)
    {x : T} (hx : orderOf x = 2) (hc : Nat.card (centralizer ({x} : Set T)) = 4)
    {E : Subgroup T} (hE : ∀ y ∈ E, y * y = 1) : Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm2, hm, hγ⟩ := CFSG.Walter.W67.isMaximalClass_of_card_centralizer (p := 2) hT x hx
    (by rw [hc]; norm_num)
  have hnil : Group.IsNilpotent T := hT.isNilpotent
  have hcl : m - 1 ≤ Group.nilpotencyClass T := by
    by_contra hcon
    apply hγ
    rw [Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
    omega
  by_cases hm3 : 3 ≤ m
  · obtain ⟨M, hMidx, hMcyc⟩ :=
      CFSG.GH74.Uniqueness.SU.SU1.exists_cyclic_index_two m hm3 T hm hcl
    have : IsCyclic ↥M := hMcyc
    exact CFSG.GH74.Uniqueness.SU.SU1.card_le_four_of_cyclic_index_two hMidx hE
  · have hm' : m = 2 := by omega
    calc Nat.card E ≤ Nat.card T := Subgroup.card_le_card_group E
      _ = 4 := by rw [hm, hm']; norm_num

theorem pRank_le_two_of_card_inf_centralizer {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (hT : IsPGroup 2 T) {x : X} (hxT : x ∈ T) (hx : orderOf x = 2)
    (hc : Nat.card ↥(T ⊓ centralizer ({x} : Set X)) = 4) : CFSG.Open.pRank 2 T ≤ 2 := by
  set x' : ↥T := ⟨x, hxT⟩ with hx'def
  have hx' : orderOf x' = 2 := by rw [hx'def, Subgroup.orderOf_mk]; exact hx
  have hmap : (centralizer ({x'} : Set ↥T)).map T.subtype = T ⊓ centralizer ({x} : Set X) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine mem_inf.mpr ⟨z.2, mem_centralizer_singleton_iff.mpr ?_⟩
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hz)
    · intro hy
      obtain ⟨hyT, hyC⟩ := mem_inf.mp hy
      refine ⟨⟨y, hyT⟩, mem_centralizer_singleton_iff.mpr (Subtype.ext ?_), rfl⟩
      exact mem_centralizer_singleton_iff.mp hyC
  have hc' : Nat.card (centralizer ({x'} : Set ↥T)) = 4 := by
    rw [← hc, ← hmap, card_map_of_injective T.subtype_injective]
  refine SectionRank.pRank_le (by norm_num) fun E hET hE => ?_
  have hE' : ∀ y ∈ E.subgroupOf T, y * y = 1 := fun y hy =>
    Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two]; exact hE.2 _ (mem_subgroupOf.mp hy))
  have h4 := card_le_four_of_card_centralizer hT hx' hc' hE'
  rw [Nat.card_congr (subgroupOfEquivOfLe hET).toEquiv] at h4
  calc Nat.card E ≤ 4 := h4
    _ = 2 ^ 2 := by norm_num

theorem pRank_le_two_of_card_sylow {G : Type} [Group G] [Finite G] {K S : Subgroup G} {b : G}
    (hb2 : orderOf b = 2) (hSKC : S ≤ K ⊓ centralizer ({b} : Set G)) (hbS : b ∈ S)
    (hS2 : IsPGroup 2 S)
    (hScard : Nat.card S = 2 ^ (Nat.card ↥(K ⊓ centralizer ({b} : Set G))).factorization 2)
    (h4 : Nat.card S = 4) : CFSG.pRank 2 ↥K ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSK : S ≤ K := hSKC.trans inf_le_left
  obtain ⟨T, hST⟩ := (hS2.comap_subtype (K := K)).exists_le_sylow
  set T₀ : Subgroup G := (T : Subgroup ↥K).map K.subtype with hT₀
  have hT₀2 : IsPGroup 2 T₀ := T.isPGroup'.map _
  have hST₀ : S ≤ T₀ := fun s hs => ⟨⟨s, hSK hs⟩, hST (mem_comap.mpr hs), rfl⟩
  have hcard : Nat.card ↥(T₀ ⊓ centralizer ({b} : Set G)) = 4 := by
    apply le_antisymm
    · have hle : T₀ ⊓ centralizer ({b} : Set G) ≤ K ⊓ centralizer ({b} : Set G) :=
        inf_le_inf_right _ (map_subtype_le _)
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hT₀2.to_le
        (inf_le_left : T₀ ⊓ centralizer ({b} : Set G) ≤ T₀))
      have hkle : k ≤ (Nat.card ↥(K ⊓ centralizer ({b} : Set G))).factorization 2 :=
        (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp
          (hk ▸ card_dvd_of_le hle)
      rw [hk, ← h4, hScard]
      exact Nat.pow_le_pow_right (by norm_num) hkle
    · rw [← h4]
      exact card_le_of_le (le_inf hST₀ (hSKC.trans inf_le_right))
  have hT₀r := pRank_le_two_of_card_inf_centralizer hT₀2 (hST₀ hbS) hb2 hcard
  rw [← (SectionRank.pRank_sylow T).2, SectionRank.pRank_eq_open_pRank_top,
    ← SectionRank.pRank_eq_pRank_top_subgroup]
  exact (SectionRank.pRank_le_map (by norm_num) K.subtype K.subtype_injective _).trans hT₀r

end CFSG.ComponentClassification.Sol76T13.R12
