module

public import CFSG.GH74.GLS.Bg.Local.Transfer1515
public import CFSG.LargeExtraspecial.GLRSplitLevi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup CFSG.GH74.GLS.Bg.Thompson

variable {G : Type*} [Group G] [Finite G]

theorem exists_isSylowIn_le {H P : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 2 P) :
    ∃ T, P ≤ T ∧ IsSylowIn 2 T H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf H) := hP.of_equiv (subgroupOfEquivOfLe hPH).symm
  obtain ⟨R, hR⟩ := hP'.exists_le_sylow
  refine ⟨(R : Subgroup H).map H.subtype, fun p hp => ⟨⟨p, hPH hp⟩, hR hp, rfl⟩,
    ⟨fun _ ⟨r, _, hr⟩ => hr ▸ r.2, R.isPGroup'.map _, ?_⟩⟩
  rw [relIndex]
  change ¬ 2 ∣ (comap H.subtype (map H.subtype (R : Subgroup H))).index
  rw [comap_map_eq_self_of_injective H.subtype_injective]
  exact R.not_dvd_index

namespace SylowIn

omit [Finite G] in
theorem le {T H : Subgroup G} (h : IsSylowIn 2 T H) : T ≤ H := h.1

omit [Finite G] in
theorem isPGroup {T H : Subgroup G} (h : IsSylowIn 2 T H) : IsPGroup 2 T := h.2.1

theorem eq_of_le {T T' H : Subgroup G} (h : IsSylowIn 2 T H) (hTT' : T ≤ T') (hT'H : T' ≤ H)
    (hT' : IsPGroup 2 T') : T' = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmul := relIndex_mul_relIndex T T' H hTT' hT'H
  obtain ⟨j, hj⟩ := hT'.exists_card_eq
  have hdvd : T.relIndex T' ∣ 2 ^ j := hj ▸ relIndex_dvd_card T T'
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rcases i with _ | i
  · rw [pow_zero, relIndex_eq_one] at hi
    exact le_antisymm hi hTT'
  · exfalso
    apply h.2.2
    rw [← hmul, hi, pow_succ]
    exact Dvd.dvd.mul_right (dvd_mul_left 2 _) _

theorem le_of_normal {T H N : Subgroup G} (h : IsSylowIn 2 T H) (hNH : N ≤ H)
    (hN : IsPGroup 2 N) (hnorm : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N) : N ≤ T := by
  have hTN : T ≤ normalizer (N : Set G) := fun t ht =>
    mem_normalizer_of_forall_conj_mem fun n hn => hnorm t (le h ht) n hn
  have hsup : IsPGroup 2 (T ⊔ N : Subgroup G) := (isPGroup h).to_sup_of_normal_right' hN hTN
  have := eq_of_le h le_sup_left (sup_le (le h) hNH) hsup
  rw [← this]
  exact le_sup_right

theorem of_normalizer {T Y H : Subgroup G} (h : IsSylowIn 2 T Y) (hYH : Y ≤ H)
    (hN : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P → ∀ s ∈ P, s ∈ normalizer (T : Set G) →
      s ∈ Y) : IsSylowIn 2 T H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hTP, hP⟩ := exists_isSylowIn_le ((le h).trans hYH) (isPGroup h)
  suffices hPT : P = T by rw [← hPT]; exact hP
  by_contra hne
  have hlt : T.subgroupOf P < ⊤ := by
    refine lt_of_le_of_ne le_top fun he => hne (le_antisymm ?_ hTP)
    intro y hy
    have : (⟨y, hy⟩ : P) ∈ T.subgroupOf P := he ▸ mem_top _
    exact this
  have hnil : Group.IsNilpotent P := (isPGroup hP).isNilpotent
  obtain ⟨⟨w, hwP⟩, hwN, hwT⟩ := Set.exists_of_ssubset
    (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hwN' : w ∈ normalizer (T : Set G) := by
    refine mem_normalizer_of_forall_conj_mem fun y hy => ?_
    exact (mem_normalizer_iff.mp hwN ⟨y, hTP hy⟩).mp hy
  have hwY : w ∈ Y := hN P (le hP) (isPGroup hP) w hwP hwN'
  have h2 : IsPGroup 2 (T ⊔ zpowers w : Subgroup G) :=
    (isPGroup hP).to_le (sup_le hTP (zpowers_le.mpr hwP))
  have heq := eq_of_le h le_sup_left (sup_le (le h) (zpowers_le.mpr hwY)) h2
  exact hwT (heq ▸ mem_sup_right (mem_zpowers w))

theorem factorization_eq {T H : Subgroup G} (h : IsSylowIn 2 T H) :
    (Nat.card H).factorization 2 = (Nat.card T).factorization 2 := by
  have hmul := relIndex_mul_card T H
  rw [inf_eq_left.mpr (le h)] at hmul
  have h1 : T.relIndex H ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hmul
    exact Nat.card_pos.ne' hmul.symm
  rw [← hmul, Nat.factorization_mul h1 Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd h.2.2, zero_add]

end SylowIn

namespace Config

variable {S : Setting G}

omit [Finite G] in
theorem isPGroup_QG (S : Setting G) : IsPGroup 2 S.QG := S.extraspecial.1.map _

theorem QG_le_of_sylowIn {T : Subgroup G} (hT : IsSylowIn 2 T S.M) : S.QG ≤ T :=
  SylowIn.le_of_normal hT S.QG_le_M (isPGroup_QG S) fun _ hg _ hn => S.conj_mem_QG hg hn

theorem sylowIn_top {T : Subgroup G} (hT : IsSylowIn 2 T S.M) : IsSylowIn 2 T ⊤ := by
  have hQT := QG_le_of_sylowIn hT
  obtain ⟨P, hTP, hP⟩ := exists_isSylowIn_le (le_top : T ≤ ⊤) (SylowIn.isPGroup hT)
  have hzP : S.z ∈ P := hTP (hQT S.z_mem_QG)
  have hPM : P ≤ S.M := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Nontrivial P := ⟨⟨⟨S.z, hzP⟩, 1, fun h => S.z_ne_one (congrArg Subtype.val h)⟩⟩
    have hcen := (SylowIn.isPGroup hP).center_nontrivial
    obtain ⟨w, hw⟩ := exists_ne (1 : center P)
    have hwc : ∀ p ∈ P, ((w : P) : G) * p = p * (w : P) := fun p hp => by
      have := mem_center_iff.mp w.2 ⟨p, hp⟩
      exact (congrArg Subtype.val this).symm
    have hwM : ((w : P) : G) ∈ S.M := S.mem_M_iff.mpr (hwc S.z hzP)
    have hwQ : ((w : P) : G) ∈ S.QG :=
      S.mem_QG_of_commute hwM fun x hx => hwc x (hTP (hQT hx))
    rcases S.eq_one_or_z_of_commute hwQ (fun y hy => hwc y (hTP (hQT hy))) with h1 | h1
    · exact absurd (Subtype.ext (Subtype.ext h1)) hw
    · intro p hp
      have := hwc p hp
      rw [h1] at this
      exact S.mem_M_iff.mpr this.symm
  have := SylowIn.eq_of_le hT hTP hPM (SylowIn.isPGroup hP)
  rw [← this]
  exact hP

variable (C : Config S)

theorem relIndex_inf_X {T : Subgroup G} (hTM : T ≤ S.M) {g : G} (hgT : g ∈ T) (hgX : g ∉ C.X) :
    (T ⊓ C.X).relIndex T = 2 := by
  rw [relIndex, index_eq_two_iff]
  refine ⟨⟨g, hgT⟩, fun b => ?_⟩
  simp only [mem_subgroupOf, coe_mul, mem_inf]
  have hb := C.mul_mem_X_iff (hTM b.2) (hTM hgT)
  by_cases hbX : (b : G) ∈ C.X
  · have : (b : G) * g ∉ C.X := fun h => hgX ((hb.mp h).mp hbX)
    simp [hbX, this, b.2]
  · have : (b : G) * g ∈ C.X := hb.mpr (iff_of_false hbX hgX)
    simp [hbX, this, b.2, T.mul_mem b.2 hgT]

end Config

end CFSG.LargeExtraspecial.GLR
