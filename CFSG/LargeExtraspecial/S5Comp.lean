module

public import CFSG.ClassicalInvolution.Basic
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SubnormalCore
public import CFSG.Open.TimmesfeldLargeExtraspecialMilestoneDefs
public import CFSG.LargeExtraspecial.S3Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S5

open Subgroup CFSG.Open CFSG.ClassicalInvolution CFSG.Quasithin.A3
  CFSG.ComponentClassification

section Generic

variable {X : Type*} [Group X]

theorem isSubnormal_subgroupOf_top_iff {A K : Subgroup X} (hAK : A ≤ K) :
    IsSubnormal (A.subgroupOf K) ⊤ ↔ IsSubnormal A K := by
  constructor
  · intro h
    have := subnormal_map K.subtype h
    rwa [map_subgroupOf_eq_of_le hAK, ← MonoidHom.range_eq_map, range_subtype] at this
  · intro h
    have := subnormal_comap K.subtype h
    change IsSubnormal (A.subgroupOf K) (K.subgroupOf K) at this
    rwa [subgroupOf_self] at this

theorem isComponentOf_iff_subgroupOf {A K : Subgroup X} (hAK : A ≤ K) :
    IsComponentOf A K ↔ IsComponentOf (A.subgroupOf K) ⊤ := by
  constructor
  · rintro ⟨-, hsub, hq⟩
    exact ⟨le_top, (isSubnormal_subgroupOf_top_iff hAK).mpr hsub,
      Components.quasisimple_of_equiv (subgroupOfEquivOfLe hAK) hq⟩
  · rintro ⟨-, hsub, hq⟩
    exact ⟨hAK, (isSubnormal_subgroupOf_top_iff hAK).mp hsub,
      Components.quasisimple_of_equiv (subgroupOfEquivOfLe hAK).symm hq⟩

theorem IsComponentOf.le {A K : Subgroup X} (h : IsComponentOf A K) : A ≤ K := h.1

theorem commute_of_isComponentOf_ne [Finite X] {A B K : Subgroup X} (hA : IsComponentOf A K)
    (hB : IsComponentOf B K) (hne : A ≠ B) : ⁅A, B⁆ = ⊥ := by
  have hA' := (isComponentOf_iff_subgroupOf hA.1).mp hA
  have hB' := (isComponentOf_iff_subgroupOf hB.1).mp hB
  have hne' : A.subgroupOf K ≠ B.subgroupOf K := by
    intro h
    have h' := subgroupOf_inj.mp h
    rw [inf_eq_left.mpr hA.1, inf_eq_left.mpr hB.1] at h'
    exact hne h'
  have h := LocalComponents.commute_of_ne _ _ hA' hB' hne'
  have hmap := congrArg (Subgroup.map K.subtype) h
  rwa [map_commutator, map_subgroupOf_eq_of_le hA.1, map_subgroupOf_eq_of_le hB.1,
    Subgroup.map_bot] at hmap

theorem mul_comm_of_isComponentOf_ne [Finite X] {A B K : Subgroup X} (hA : IsComponentOf A K)
    (hB : IsComponentOf B K) (hne : A ≠ B) {a b : X} (ha : a ∈ A) (hb : b ∈ B) :
    a * b = b * a := by
  have h := commute_of_isComponentOf_ne hA hB hne
  have hmem : a * b * a⁻¹ * b⁻¹ ∈ ⁅A, B⁆ := commutator_mem_commutator ha hb
  rw [h, mem_bot] at hmem
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [hmem, one_mul]

theorem isComponentOf_map_conj {A K : Subgroup X} (hA : IsComponentOf A K) {k : X}
    (hk : k ∈ K) : IsComponentOf (A.map (MulAut.conj k).toMonoidHom) K := by
  have hK : K.map (MulAut.conj k).toMonoidHom = K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact K.mul_mem (K.mul_mem hk hy) (K.inv_mem hk)
    · intro hx
      refine ⟨k⁻¹ * x * k, K.mul_mem (K.mul_mem (K.inv_mem hk) hx) hk, ?_⟩
      simp [mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hK]
    exact map_mono hA.1
  · have := isSubnormal_map_conj hA.2.1 k
    rwa [hK] at this
  · exact Components.quasisimple_of_equiv
      (A.equivMapOfInjective _ (MulAut.conj k).injective).symm hA.2.2

theorem commute_or_eq_of_normalized {A N : Subgroup X} (hA : CFSG.Open.IsQuasisimple A)
    (hNA : N ≤ A)
    (hnorm : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) :
    (∀ n ∈ N, ∀ a ∈ A, n * a = a * n) ∨ N = A := by
  have hN : (N.subgroupOf A).Normal := ⟨fun n hn a => by
    rw [mem_subgroupOf] at hn ⊢
    exact hnorm a a.2 n hn⟩
  rcases Quasisimple.normal_le_center_or_eq_top hA (N.subgroupOf A) with h | h
  · left
    intro n hn a ha
    have hc := h (show (⟨n, hNA hn⟩ : A) ∈ N.subgroupOf A from hn)
    have := (mem_center_iff.mp hc) ⟨a, ha⟩
    exact (congrArg Subtype.val this).symm
  · right
    exact le_antisymm hNA (subgroupOf_eq_top.mp h)

theorem map_timmesfeldLayer (K : Subgroup X) :
    (timmesfeldLayer K).map K.subtype = sSup {A : Subgroup X | IsComponentOf A K} := by
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    refine sSup_le fun L hL => ?_
    rw [← map_le_iff_le_comap]
    refine le_sSup ((isComponentOf_iff_subgroupOf (map_subtype_le L)).mpr ?_)
    have e : (L.map K.subtype).subgroupOf K = L :=
      comap_map_eq_self_of_injective K.subtype_injective L
    rw [e]
    exact hL
  · refine sSup_le fun A hA => ?_
    rw [← map_subgroupOf_eq_of_le hA.1]
    exact map_mono (le_sSup ((isComponentOf_iff_subgroupOf hA.1).mp hA))

theorem timmesfeldLayer_eq_bot_or_isQuasisimple {H : Type*} [Group H]
    (h : ∀ A B : Subgroup H, IsComponentOf A ⊤ → IsComponentOf B ⊤ → A = B) :
    timmesfeldLayer H = ⊥ ∨ CFSG.Open.IsQuasisimple (timmesfeldLayer H) := by
  by_cases hex : ∃ A : Subgroup H, IsComponentOf A ⊤
  · obtain ⟨A, hA⟩ := hex
    have hset : {L : Subgroup H | IsComponentOf L ⊤} = {A} := by
      ext L
      exact ⟨fun hL => h L A hL hA, fun hL => hL ▸ hA⟩
    right
    rw [timmesfeldLayer, hset, sSup_singleton]
    exact hA.2.2
  · left
    push Not at hex
    rw [timmesfeldLayer, eq_bot_iff]
    exact sSup_le fun L hL => absurd hL (hex L)

end Generic

variable {G : Type*} [Group G] [Finite G]

theorem eq_bot_of_isSubnormal_Mbar (S : Setting G) {P : Subgroup S.O}
    (hP : IsSubnormal P S.Mbar) (h2 : IsPGroup 2 P) : P = ⊥ := by
  have h := CFSG.RankThreeEvenClassification.Helpers.subnormal_pSubgroup_le_pCoreOf 2 hP h2
  have hle := S.pCore_Mbar_eq_bot
  rw [pCoreOf, hle, Subgroup.map_bot] at h
  exact le_bot_iff.mp h

theorem eq_one_of_mem_center_of_pow (S : Setting G) {A : Subgroup S.O}
    (hA : IsSubnormal A S.Mbar) {x : S.O} (hxA : x ∈ A) (hcomm : ∀ y ∈ A, x * y = y * x)
    {k : ℕ} (hk : x ^ (2 ^ k) = 1) : x = 1 := by
  have hle : zpowers x ≤ A := zpowers_le.mpr hxA
  have hnorm : ((zpowers x).subgroupOf A).Normal := ⟨fun n hn a => by
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hn
    have hc : (a : S.O) * x = x * a := (hcomm a a.2).symm
    have : (a : S.O) * x ^ i * (a : S.O)⁻¹ = x ^ i := by
      rw [((Commute.zpow_right hc i)).eq, mul_inv_cancel_right]
    simp only [coe_mul, coe_inv]
    rw [← hi, this]
    exact zpow_mem (mem_zpowers x) i⟩
  have hsub : IsSubnormal (zpowers x) S.Mbar :=
    isSubnormal_trans (isSubnormal_of_normal_subgroupOf hle hnorm) hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (zpowers x) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    refine IsPGroup.of_card (n := j) ?_
    rw [Nat.card_zpowers, hj]
  have h := eq_bot_of_isSubnormal_Mbar S hsub h2
  exact zpowers_eq_bot.mp h

end CFSG.LargeExtraspecial.S5
