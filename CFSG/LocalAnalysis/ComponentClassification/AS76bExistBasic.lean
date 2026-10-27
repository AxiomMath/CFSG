module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.PCore.Defs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

section Group

variable {G : Type*} [Group G]

theorem tightlyEmbedded_centralizer {A : Subgroup G} (hA : standardComponentIsStandard A) :
    TightlyEmbedded (centralizer (A : Set G)) :=
  hA.tightlyEmbedded_centralizer

theorem normalizer_centralizer_eq {A : Subgroup G} (hA : standardComponentIsStandard A) :
    normalizer (centralizer (A : Set G) : Set G) = normalizer (A : Set G) :=
  hA.2.2.2.1

theorem IsElemAbelian.mono {p : ℕ} {E F : Subgroup G} (hE : IsElemAbelian p E) (hFE : F ≤ E) :
    IsElemAbelian p F := CFSG.Open.IsElemAbelian.mono hE hFE

end Group

section Quaternion

theorem QuaternionGroup.eq_a_of_orderOf_eq_two {n : ℕ} [NeZero n] {x : QuaternionGroup n}
    (hx : orderOf x = 2) : x = QuaternionGroup.a n := by
  rcases x with i | i
  · have h1 : QuaternionGroup.a i ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one _
    have h2 : QuaternionGroup.a i ≠ 1 := fun h => by rw [h, orderOf_one] at hx; norm_num at hx
    rw [sq, QuaternionGroup.a_mul_a, QuaternionGroup.one_def, QuaternionGroup.a.injEq] at h1
    rw [QuaternionGroup.one_def, ne_eq, QuaternionGroup.a.injEq] at h2
    congr 1
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have hval := congrArg ZMod.val h1
    rw [ZMod.val_add, ZMod.val_zero] at hval
    have hlt := ZMod.val_lt i
    have hi0 : i.val ≠ 0 := fun h => h2 ((ZMod.val_eq_zero i).mp h)
    have hin : i.val = n := by
      have h2n : (i.val + i.val) % (2 * n) = 0 := hval
      rcases Nat.lt_or_ge (i.val + i.val) (2 * n) with h | h
      · rw [Nat.mod_eq_of_lt h] at h2n
        omega
      · have : (i.val + i.val) % (2 * n) = i.val + i.val - 2 * n := by
          rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
        omega
    apply ZMod.val_injective
    rw [hin, ZMod.val_natCast_of_lt (by omega)]
  · rw [QuaternionGroup.orderOf_xa] at hx
    norm_num at hx

end Quaternion

section Finite

variable {G : Type*} [Group G] [Finite G]

theorem isSylowOf_ne_bot_of_even {P K : Subgroup G} (hP : IsSylowOf 2 P K)
    (hK : Even (Nat.card K)) : P ≠ ⊥ := by
  intro hbot
  have hcard := hP.card_eq
  rw [hbot, Subgroup.card_bot] at hcard
  have hf : 0 < (Nat.card K).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' (even_iff_two_dvd.mp hK)
  have h3 : 2 ∣ (2 : ℕ) ^ (Nat.card K).factorization 2 := dvd_pow_self 2 hf.ne'
  rw [← hcard] at h3
  omega

theorem exists_elemAbelian_four {H : Subgroup G} (h : 1 < Open.pRank 2 H) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 2 E ∧ Nat.card E = 4 := by
  obtain ⟨E, hEH, hE, hcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two H
  have hdiv : 2 ^ 2 ∣ Nat.card E := by
    rw [hcard]
    exact Nat.pow_dvd_pow 2 h
  obtain ⟨F, hFcard, -, hFE⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (H := (⊥ : Subgroup G)) (L := E) (by simp) hdiv bot_le
  exact ⟨F, hFE.trans hEH, IsElemAbelian.mono hE hFE, by simpa using hFcard⟩

omit [Finite G] in
theorem exists_two_involutions {E : Subgroup G} (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4) :
    ∃ x ∈ E, ∃ y ∈ E, orderOf x = 2 ∧ orderOf y = 2 ∧ x ≠ y := by
  have hne : E ≠ ⊥ := fun h => by rw [h, card_bot] at h4; norm_num at h4
  obtain ⟨⟨x, hxE⟩, hx1'⟩ := ne_bot_iff_exists_ne_one.mp hne
  have hx1 : x ≠ 1 := fun h => hx1' (Subtype.ext h)
  have hxo : orderOf x = 2 := orderOf_eq_prime (hE.2 x hxE) hx1
  have hzx : Nat.card (zpowers x) = 2 := by rw [Nat.card_zpowers, hxo]
  have hlt : zpowers x ≠ E := fun h => by rw [h, h4] at hzx; norm_num at hzx
  have hle : zpowers x ≤ E := (zpowers_le).mpr hxE
  obtain ⟨y, hyE, hyx⟩ : ∃ y ∈ E, y ∉ zpowers x := by
    by_contra hcon
    push Not at hcon
    exact hlt (le_antisymm hle fun y hy => hcon y hy)
  have hy1 : y ≠ 1 := fun h => hyx (h ▸ one_mem _)
  exact ⟨x, hxE, y, hyE, hxo, orderOf_eq_prime (hE.2 y hyE) hy1,
    fun h => hyx (h ▸ mem_zpowers x)⟩

theorem false_of_le_cyclic_or_quaternion {S E : Subgroup G} (hES : E ≤ S)
    (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4)
    (hS : IsCyclic S ∨ ∃ r : ℕ, 3 ≤ r ∧ Nonempty (S ≃* QuaternionGroup (2 ^ (r - 2)))) :
    False := by
  obtain ⟨x, hxE, y, hyE, hxo, hyo, hxy⟩ := exists_two_involutions hE h4
  rcases hS with hcyc | ⟨r, -, ⟨e⟩⟩
  ·
    have hx' : orderOf (⟨x, hES hxE⟩ : S) = 2 := by rw [Subgroup.orderOf_mk]; exact hxo
    have hy' : orderOf (⟨y, hES hyE⟩ : S) = 2 := by rw [Subgroup.orderOf_mk]; exact hyo
    have hz : zpowers (⟨x, hES hxE⟩ : S) = zpowers (⟨y, hES hyE⟩ : S) := by
      rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hx', hy']
    have hmem : (⟨y, hES hyE⟩ : S) ∈ zpowers (⟨x, hES hxE⟩ : S) := hz ▸ mem_zpowers _
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
    rw [← zpow_mod_orderOf, hx'] at hk
    rcases Int.emod_two_eq_zero_or_one k with h0 | h0
    · rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h0, zpow_zero] at hk
      have : y = 1 := congrArg Subtype.val hk.symm
      rw [this, orderOf_one] at hyo
      norm_num at hyo
    · rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h0, zpow_one] at hk
      exact hxy (congrArg Subtype.val hk)
  · have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
    have hx' : orderOf (e ⟨x, hES hxE⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hxo
    have hy' : orderOf (e ⟨y, hES hyE⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hyo
    have h := (QuaternionGroup.eq_a_of_orderOf_eq_two hx').trans
      (QuaternionGroup.eq_a_of_orderOf_eq_two hy').symm
    exact hxy (congrArg Subtype.val (e.injective h))

theorem eq_bot_of_odd_normal {L : Subgroup G} [L.Normal] (hO : standardComponentOddCore G = ⊥)
    {M : Subgroup L} (hM : M.Normal) (hodd : Odd (Nat.card M)) : M = ⊥ := by
  open CFSG.DisconnectedInvolutionGraph.Helpers in
  have : (oddCore L).Characteristic := oddCore_characteristic
  have hMle : M ≤ oddCore L := normal_odd_le_oddCore M hM hodd
  have hnorm : ((oddCore L).map L.subtype).Normal := inferInstance
  have hodd' : Odd (Nat.card ((oddCore L).map L.subtype)) := by
    rw [card_map_of_injective L.subtype_injective]
    exact oddCore_odd
  have hle : (oddCore L).map L.subtype ≤ standardComponentOddCore G := le_sSup ⟨hnorm, hodd'⟩
  rw [hO, le_bot_iff, map_eq_bot_iff_of_injective _ L.subtype_injective] at hle
  exact le_bot_iff.mp (hle ▸ hMle)

omit [Finite G] in
theorem mem_of_two_element_of_odd_index {N : Subgroup G} [N.Normal] (hN : Odd N.index) {x : G}
    {k : ℕ} (hx : x ^ (2 ^ k) = 1) : x ∈ N := by
  have hdvd1 : orderOf (QuotientGroup.mk' N x) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx, map_one])
  have hdvd2 : orderOf (QuotientGroup.mk' N x) ∣ N.index := by
    rw [Subgroup.index]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) N.index := Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hN)
  have h1 : orderOf (QuotientGroup.mk' N x) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

omit [Finite G] in
theorem closure_twoElements_normal {L : Subgroup G} [hL : L.Normal] :
    (closure {x | x ∈ L ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1}).Normal := by
  refine ⟨fun n hn g => ?_⟩
  induction hn using closure_induction with
  | mem x hx =>
    refine subset_closure ⟨hL.conj_mem x hx.1 g, ?_⟩
    obtain ⟨k, hk⟩ := hx.2
    exact ⟨k, by rw [conj_pow, hk, mul_one, mul_inv_cancel]⟩
  | one => simp
  | mul x y _ _ hx hy =>
    have := mul_mem hx hy
    rwa [show g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ by group] at this
  | inv x _ hx =>
    have := inv_mem hx
    rwa [show (g * x * g⁻¹)⁻¹ = g * x⁻¹ * g⁻¹ by group] at this

end Finite

end CFSG.ComponentClassification.AS76b
