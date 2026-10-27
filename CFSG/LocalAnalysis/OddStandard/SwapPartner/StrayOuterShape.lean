module

public import CFSG.Holt.TwoGroups
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.StrayOuterSylow

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

theorem exists_sylow_shape_of_small_centralizer {G : Type*} [Group G] [Finite G] {L : Subgroup G}
    {a : G} (ha : a ^ 2 = 1) (haN : a ∈ normalizer (L : Set G)) (haL : a ∉ L)
    (hL2 : 2 ∣ Nat.card L) (hC : Nat.card ↥(L ⊓ centralizer ({a} : Set G)) ≤ 3) :
    ∃ T : Sylow 2 ↥L, IsCyclic ↥(T : Subgroup ↥L) ∨
      (∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥(T : Subgroup ↥L) ≃* DihedralGroup (2 ^ m))) ∨
      ∃ n : ℕ, 3 ≤ n ∧ Nonempty (↥(T : Subgroup ↥L) ≃* QuaternionGroup (2 ^ (n - 2))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Ts, hTs, haTs, -, hrel, hcardS⟩ := exists_sylow_index_two ha haN haL
  set S : Subgroup G := Ts ⊓ L with hS
  set C : Subgroup G := centralizer ({a} : Set G) with hCdef
  have hSL : S ≤ L := by rw [hS]; exact inf_le_right
  have hST : S ≤ Ts := by rw [hS]; exact inf_le_left
  have hrel' : S.relIndex Ts = 2 := by rw [hS]; exact hrel
  have hcardS' : Nat.card ↥S = 2 ^ (Nat.card ↥L).factorization 2 := by
    rw [hS]; exact hcardS
  have hC' : Nat.card ↥(L ⊓ C) ≤ 3 := by rw [hCdef]; exact hC
  have hfac : 1 ≤ (Nat.card ↥L).factorization 2 :=
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two
      (Nat.card_pos (α := ↥L)).ne').mp hL2
  have hcardS2 : 2 ≤ Nat.card ↥S := by
    rw [hcardS']
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (Nat.card ↥L).factorization 2 :=
        Nat.pow_le_pow_right (by norm_num) hfac
  have hSne : S ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcardS2
    omega
  have hS'idx : (S.subgroupOf Ts).index = 2 := hrel'
  haveI : (S.subgroupOf Ts).Normal := Subgroup.normal_of_index_eq_two hS'idx
  haveI : Group.IsNilpotent Ts := hTs.isNilpotent
  have hS'ne : S.subgroupOf Ts ≠ ⊥ := by
    intro hbot
    have hcard1 : Nat.card ↥(S.subgroupOf Ts) = 1 := by rw [hbot, Subgroup.card_bot]
    have hcardeq : Nat.card ↥(S.subgroupOf Ts) = Nat.card ↥S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hST).toEquiv
    omega
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hS'ne)
  have hzS : ((z.1 : Ts) : G) ∈ S := Subgroup.mem_subgroupOf.mp z.2.1
  have hzC : ((z.1 : Ts) : G) ∈ C := by
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
    exact (congrArg Subtype.val
      (Subgroup.mem_center_iff.mp z.2.2 (⟨a, haTs⟩ : Ts))).symm
  have hw1 : ((z.1 : Ts) : G) ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
  have hCne : S ⊓ C ≠ ⊥ := by
    intro hbot
    have : ((z.1 : Ts) : G) ∈ (⊥ : Subgroup G) := hbot ▸ ⟨hzS, hzC⟩
    exact hw1 (Subgroup.mem_bot.mp this)
  have hge2 : 2 ≤ Nat.card ↥(S ⊓ C) := by
    have := (S ⊓ C).one_lt_card_iff_ne_bot.mpr hCne
    omega
  obtain ⟨k, hk⟩ := (hTs.to_le (inf_le_left.trans hST)).exists_card_eq
  have hle_inf : S ⊓ C ≤ L ⊓ C := fun x hx => ⟨hSL hx.1, hx.2⟩
  have hCle : Nat.card ↥(S ⊓ C) ≤ 3 :=
    (Subgroup.card_le_of_le hle_inf).trans hC'
  have hk_le : k ≤ 1 := by
    have hk3 : 2 ^ k ≤ 3 := by rw [← hk]; exact hCle
    by_contra h
    have h2 : 2 ≤ k := by omega
    have h4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h2
    omega
  have hcardC : Nat.card ↥(S ⊓ C) = 2 := by
    apply le_antisymm _ hge2
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk_le
      _ = 2 := by norm_num
  have hSC : Nat.card ↥(S ⊓ centralizer ({a} : Set G)) = 2 := by
    rw [← hCdef]; exact hcardC
  have ha1 : a ≠ 1 := fun h => haL (h ▸ L.one_mem)
  have hta : orderOf a = 2 := orderOf_eq_prime (p := 2) ha ha1
  have haS : a ∉ S := fun h => haL (hSL h)
  have hshape := CFSG.Holt.suzuki_index_two hTs hST hrel' haTs haS hta hSC
  have hcard_sub : Nat.card ↥(S.subgroupOf L) = 2 ^ (Nat.card ↥L).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv]
    exact hcardS'
  refine ⟨Sylow.ofCard (S.subgroupOf L) hcard_sub, ?_⟩
  simp only [Sylow.coe_ofCard]
  obtain ⟨e⟩ : Nonempty (↥(S.subgroupOf L) ≃* ↥S) :=
    ⟨Subgroup.subgroupOfEquivOfLe hSL⟩
  rcases hshape.1 with hcyc | ⟨m, hm, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩
  · exact Or.inl (e.isCyclic.mpr hcyc)
  · exact Or.inr (Or.inl ⟨m, hm, ⟨e.trans f⟩⟩)
  · exact Or.inr (Or.inr ⟨n, hn, ⟨e.trans f⟩⟩)

end CFSG.OddStandard.AltStdSec.SwapPartner
