module

public import CFSG.GH74.Uniqueness.SU.SU4Iso
public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.GH74.Uniqueness.SU.SU4

open Subgroup

theorem thompson_involution_index_two {Y : Type*} [Group Y] [Finite Y] {P T : Subgroup Y} {u : Y}
    (hP : IsPGroup 2 P) (hPidx : ¬ 2 ∣ P.index) (hTn : ∀ t ∈ P, ∀ q ∈ T, t * q * t⁻¹ ∈ T)
    (hcos : ∀ t ∈ P, t ∈ T ∨ u⁻¹ * t ∈ T) (huP : u ∈ P) (huT : u ∉ T) (hu2 : u * u = 1) :
    (∃ (N : Subgroup Y) (_ : N.Normal), IsCyclic (Y ⧸ N) ∧ IsPGroup 2 (Y ⧸ N) ∧ u ∉ N) ∨
    ∃ g : Y, g⁻¹ * u * g ∈ T ∧
      ∀ c ∈ P ⊓ centralizer ({u} : Set Y), g⁻¹ * c * g ∈ P ⊓ centralizer ({g⁻¹ * u * g} : Set Y) := by
  have hcyc : ∃ b ∈ P, ∀ t ∈ P, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ T := by
    refine ⟨u, huP, fun t ht => ?_⟩
    rcases hcos t ht with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  have hb : ∀ (g : Y) (k : ℕ), g⁻¹ * u ^ (2 * k) * g ∈ P → g⁻¹ * u ^ (2 * k) * g ∈ T := by
    intro g k _
    have : u ^ (2 * k) = 1 := by
      rw [pow_mul, pow_two, hu2, one_pow]
    rw [this]
    simp
  have hc : ∀ g : Y, g⁻¹ * u * g ∈ P →
      CFSG.GH74.GLS.Bg.Thompson.IsExtremalIn 2 P (g⁻¹ * u * g) →
        g⁻¹ * u * g ∈ T ∨ u⁻¹ * (g⁻¹ * u * g) ∈ T := fun g hg _ => hcos _ hg
  have := CFSG.GH74.GLS.Bg.Thompson.thompson_transfer_1515 (p := 2) hP hPidx hTn hcyc huP huT hb hc
  rcases this with h | ⟨g, hg, -, hc'⟩
  · left; exact h
  · right; exact ⟨g, hg, hc'⟩

theorem oResidual_le_of_isPGroup_quotient {Y : Type*} [Group Y] {N : Subgroup Y} [N.Normal]
    (h : IsPGroup 2 (Y ⧸ N)) : GLS.oResidual 2 Y ≤ N := by
  refine (Subgroup.closure_le N).mpr ?_
  intro y hy
  have hy' : Nat.Coprime (orderOf y) 2 := hy
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).mp h (QuotientGroup.mk y)
  have hd : orderOf (QuotientGroup.mk y : Y ⧸ N) ∣ orderOf y :=
    orderOf_map_dvd (QuotientGroup.mk' N) y
  rw [hk] at hd
  have hcop : Nat.Coprime (2 ^ k) (orderOf y) := (Nat.Coprime.pow_left k (hy'.symm))
  have h1 : 2 ^ k = 1 := Nat.Coprime.eq_one_of_dvd hcop hd
  have hone : orderOf (QuotientGroup.mk y : Y ⧸ N) = 1 := by rw [hk, h1]
  exact (QuotientGroup.eq_one_iff y).mp (orderOf_eq_one_iff.mp hone)

variable {G : Type} [Group G]

omit [Group G] in
theorem zpowers_commute_of {G : Type} [Group G] {x z : G} (h : x * z = z * x) :
    ∀ a ∈ zpowers x, ∀ b ∈ zpowers z, a * b = b * a := by
  rintro a ⟨m, rfl⟩ b ⟨n, rfl⟩
  exact (Commute.zpow_zpow (show Commute x z from h) m n).eq

theorem inv_mul_mem_of_relIndex_eq_two {T U : Subgroup G} (hUidx : U.relIndex T = 2) {a b : G}
    (haT : a ∈ T) (hbT : b ∈ T) (haU : a ∉ U) (hbU : b ∉ U) : a⁻¹ * b ∈ U := by
  have key := (Subgroup.mul_mem_iff_of_index_two (H := U.subgroupOf T) hUidx
    (a := (⟨a, haT⟩ : T)⁻¹) (b := ⟨b, hbT⟩)).2 (by
      rw [inv_mem_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact iff_of_false haU hbU)
  exact Subgroup.mem_subgroupOf.1 key

theorem mem_centralizer_of_normalizes {S U : Subgroup G}
    (hn : ∀ g ∈ S, ∀ u ∈ U, g * u * g⁻¹ ∈ U) {t q : G} (ht : t ∈ S)
    (hq : q ∈ centralizer (U : Set G)) : t * q * t⁻¹ ∈ centralizer (U : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hu0 : t⁻¹ * u * t ∈ U := by simpa using hn t⁻¹ (S.inv_mem ht) u hu
  have h := Subgroup.mem_centralizer_iff.mp hq _ hu0
  calc (u * (t * q * t⁻¹)) = t * ((t⁻¹ * u * t) * q) * t⁻¹ := by group
    _ = t * (q * (t⁻¹ * u * t)) * t⁻¹ := by rw [h]
    _ = (t * q * t⁻¹) * u := by group

variable {G : Type} [Group G] [Finite G]

theorem x_not_mem_oResidual {X V S K : Subgroup G} {x z w : G}
    (hV : IsIsolatedVertex X V) (hgen : V = zpowers x ⊔ zpowers z)
    (hS : IsSylowIn X S) (hSrk : 3 ≤ Open.pRank 2 S) (hVS : V ≤ S) (hxV : x ∈ V)
    (hx2 : x * x = 1) (hKS : K ≤ S) (hKx : ∀ k ∈ K, k * x = x * k) (hwK : w ∈ K)
    (hww : w * w = z) : x ∉ (GLS.oResidual 2 ↥X).map X.subtype := by
  intro hxO
  have hSX : S ≤ X := hS.1
  have hxS : x ∈ S := hVS hxV
  have hxX : x ∈ X := hSX hxS
  have hxO' : (⟨x, hxX⟩ : ↥X) ∈ GLS.oResidual 2 ↥X := by
    obtain ⟨x', hx', hx'eq⟩ := Subgroup.mem_map.mp hxO
    have : x' = ⟨x, hxX⟩ := Subtype.ext hx'eq
    rwa [← this]
  obtain ⟨U₁, hU₁⟩ := exists_isNormalEp2 hS.2.1 hSrk
  have hU₁4 : IsFour X U₁ := ⟨hU₁.1.trans hSX, hU₁.2.2.1, hU₁.2.2.2⟩
  have hrel : (centralizer (U₁ : Set G)).relIndex S ≤ 2 :=
    (SU1.ig10_20_ii Nat.prime_two hS.2.1 hU₁).2.1
  have hnorm : ∀ g ∈ S, ∀ u ∈ U₁, g * u * g⁻¹ ∈ U₁ := SU1.conj_mem_of_le_normalizer hU₁.2.1
  have hconj : ∃ g ∈ X, g⁻¹ * x * g ∈ centralizer (U₁ : Set G) ∧ ∀ k ∈ K, g⁻¹ * k * g ∈ S := by
    by_cases hxT : x ∈ centralizer (U₁ : Set G)
    · exact ⟨1, X.one_mem, by simpa using hxT, fun k hk => by simpa using hKS hk⟩
    · have hrel2 : (centralizer (U₁ : Set G)).relIndex S = 2 := by
        have h0 : (centralizer (U₁ : Set G)).relIndex S ≠ 1 := by
          rw [Ne, Subgroup.relIndex_eq_one]
          intro h
          exact hxT (h hxS)
        have h1 : (centralizer (U₁ : Set G)).relIndex S ≠ 0 := SU1.relIndex_ne_zero_of_finite _ _
        omega
      have hPp : IsPGroup 2 ↥(S.subgroupOf X) :=
        IsPGroup.of_equiv hS.2.1 (Subgroup.subgroupOfEquivOfLe hSX).symm
      have hPidx : ¬ 2 ∣ (S.subgroupOf X).index := by
        have := hS.2.2
        have h : (S.subgroupOf X).index = S.relIndex X := rfl
        rw [h]
        rw [Nat.odd_iff] at this
        omega
      have hTn : ∀ t ∈ S.subgroupOf X, ∀ q ∈ (centralizer (U₁ : Set G) ⊓ S).subgroupOf X,
          t * q * t⁻¹ ∈ (centralizer (U₁ : Set G) ⊓ S).subgroupOf X := by
        intro t ht q hq
        rw [Subgroup.mem_subgroupOf] at ht hq ⊢
        refine ⟨?_, ?_⟩
        · have := mem_centralizer_of_normalizes hnorm ht hq.1
          simpa using this
        · simpa using S.mul_mem (S.mul_mem ht hq.2) (S.inv_mem ht)
      have hcos : ∀ t ∈ S.subgroupOf X, t ∈ (centralizer (U₁ : Set G) ⊓ S).subgroupOf X ∨
          (⟨x, hxX⟩ : ↥X)⁻¹ * t ∈ (centralizer (U₁ : Set G) ⊓ S).subgroupOf X := by
        intro t ht
        rw [Subgroup.mem_subgroupOf] at ht
        by_cases htc : (t : G) ∈ centralizer (U₁ : Set G)
        · left
          rw [Subgroup.mem_subgroupOf]
          exact ⟨htc, ht⟩
        · right
          rw [Subgroup.mem_subgroupOf]
          have h1 := inv_mul_mem_of_relIndex_eq_two hrel2 hxS ht hxT htc
          refine ⟨by simpa using h1, ?_⟩
          simpa using S.mul_mem (S.inv_mem hxS) ht
      have huP : (⟨x, hxX⟩ : ↥X) ∈ S.subgroupOf X := by
        rw [Subgroup.mem_subgroupOf]; exact hxS
      have huT : (⟨x, hxX⟩ : ↥X) ∉ (centralizer (U₁ : Set G) ⊓ S).subgroupOf X := by
        rw [Subgroup.mem_subgroupOf]
        intro h
        exact hxT h.1
      have hu2 : (⟨x, hxX⟩ : ↥X) * ⟨x, hxX⟩ = 1 := Subtype.ext hx2
      rcases thompson_involution_index_two hPp hPidx hTn hcos huP huT hu2 with
        ⟨N, hN, -, hNp, huN⟩ | ⟨g, hg, hgc⟩
      · have := hN
        exact absurd (oResidual_le_of_isPGroup_quotient hNp hxO') huN
      · refine ⟨(g : G), g.2, ?_, fun k hk => ?_⟩
        · have := (Subgroup.mem_subgroupOf.mp hg).1
          simpa using this
        · have hkS : k ∈ S := hKS hk
          have hkX : k ∈ X := hSX hkS
          have hc : (⟨k, hkX⟩ : ↥X) ∈
              S.subgroupOf X ⊓ centralizer ({(⟨x, hxX⟩ : ↥X)} : Set ↥X) :=
            Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hkS,
              Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext (hKx k hk))⟩
          have h1 := Subgroup.mem_subgroupOf.mp (hgc _ hc).1
          simpa using h1
  obtain ⟨g, hgX, hgx, hgK⟩ := hconj
  have hw' : g⁻¹ * w * g ∈ S := hgK w hwK
  have hz' : g⁻¹ * z * g ∈ centralizer (U₁ : Set G) := by
    have : g⁻¹ * z * g = (g⁻¹ * w * g) * (g⁻¹ * w * g) := by rw [← hww]; group
    rw [this]
    exact sq_mem_of_relIndex_le_two hrel hw'
  have hxU : x ∈ centralizer ((conjSub g U₁ : Subgroup G) : Set G) := by
    rw [← conjSub_centralizer]; exact mem_conjSub.mpr hgx
  have hzU : z ∈ centralizer ((conjSub g U₁ : Subgroup G) : Set G) := by
    rw [← conjSub_centralizer]; exact mem_conjSub.mpr hz'
  have hVU : V ≤ centralizer ((conjSub g U₁ : Subgroup G) : Set G) := by
    rw [hgen]; exact sup_le (Subgroup.zpowers_le.mpr hxU) (Subgroup.zpowers_le.mpr hzU)
  have hconjX : conjSub g X = X := conjSub_self_of_mem hgX
  have hU₁'4 : IsFour X (conjSub g U₁) := isFour_conjSub hconjX.le hU₁4
  have hcomm : ∀ a ∈ V, ∀ b ∈ conjSub g U₁, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hVU ha) b hb).symm
  have heq : conjSub g U₁ = V := hV.eq_of_commute hU₁'4 hcomm
  have hiso' : IsIsolatedVertex X U₁ := by
    have h1 := isIsolatedVertex_conjSub (g := g⁻¹) (X := X) (Y := X) (V := V)
      (conjSub_self_of_mem (X.inv_mem hgX)) hV
    rwa [← heq, conjSub_inv_conjSub] at h1
  have hiso'' : IsIsolatedVertex S U₁ := hiso'.mono hSX hU₁.1
  obtain ⟨h4, hiso⟩ := hiso''
  exact SU1.not_isIsolated_of_isNormalEp2 Nat.prime_two hS.2.1 hSrk hU₁ ⟨U₁, h4⟩ rfl hiso

variable {G : Type} [Group G]

structure Conf181 (X V : Subgroup G) (x z : G) (S K : Subgroup G) : Prop where
  x_mem : x ∈ V
  z_mem : z ∈ V
  hx : orderOf x = 2
  hz : orderOf z = 2
  gen : V = zpowers x ⊔ zpowers z
  syl : IsSylowIn X S
  syl_c : IsSylowIn (centralizer ({x} : Set G) ⊓ X) (centralizer ({x} : Set G) ⊓ S)
  K_le : K ≤ centralizer ({x} : Set G) ⊓ S
  K_inf : zpowers x ⊓ K = ⊥
  K_sup : zpowers x ⊔ K = centralizer ({x} : Set G) ⊓ S
  z_K : z ∈ K
  K_inv : ∀ k ∈ K, k * k = 1 → k = 1 ∨ k = z
  z_cent : ∀ s ∈ S, s * z = z * s
  z_uniq : ∀ c ∈ S, (∀ s ∈ S, s * c = c * s) → c * c = 1 → c = 1 ∨ c = z
  x_not : x ∉ (GLS.oResidual 2 ↥X).map X.subtype

section Finite

variable [Finite G]

theorem lemma181_core {X V : Subgroup G} (hX : 3 ≤ Open.pRank 2 X)
    (hV : IsIsolatedVertex X V) : ∃ x z S K, Conf181 X V x z S K := by
  have hV4 := hV.isFour
  have hVel := SU1.isElemAbelian_iff.mp hV4.2.1
  obtain ⟨S₁, hS₁⟩ := exists_isSylowIn (centralizer (V : Set G) ⊓ X)
  obtain ⟨x, hxV, hx1, hrk2⟩ := exists_x_rank_two hX hV hS₁
  have hx2 : x * x = 1 := by rw [← pow_two]; exact hVel.2 x hxV
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  have hS₁C : S₁ ≤ centralizer ({x} : Set G) ⊓ X :=
    hS₁.1.trans (inf_le_inf_right X (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxV)))
  obtain ⟨R, hR, hS₁R⟩ := exists_isSylowIn_ge hS₁C hS₁.2.1
  obtain ⟨S, hS, hRS⟩ := exists_isSylowIn_ge (hR.1.trans inf_le_right) hR.2.1
  have hSX : S ≤ X := hS.1
  have hSrk : 3 ≤ Open.pRank 2 S := by rw [hS.pRank_eq]; exact hX
  have hVS₁ : V ≤ S₁ := le_of_isSylowIn_centralizer hV4 hS₁
  have hVS : V ≤ S := hVS₁.trans (hS₁R.trans hRS)
  have hCSx : centralizer ({x} : Set G) ⊓ S = R :=
    hR.eq_of_le (inf_le_inf_left _ hSX) (hS.2.1.to_le inf_le_right)
      (le_inf (hR.1.trans inf_le_left) hRS)
  have hsylc : IsSylowIn (centralizer ({x} : Set G) ⊓ X) (centralizer ({x} : Set G) ⊓ S) := by
    rw [hCSx]; exact hR
  have hxS : x ∈ S := hVS hxV
  have hxnc : ∃ s ∈ S, s * x ≠ x * s := by
    by_contra h
    push Not at h
    have hle : S ≤ centralizer ({x} : Set G) ⊓ X :=
      le_inf (fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr (h s hs)) hSX
    have := SU1.pRank_mono (p := 2) (by norm_num) hle
    omega
  obtain ⟨z, hzS, hz2, hz1, hzc⟩ := exists_central_involution hS.2.1 (ne_bot_of_rank_three hSrk)
  have hzV : z ∈ V := hV.mem_of_commute (hSX hzS) hz2 (fun v hv => (hzc v (hVS hv)).symm)
  have hzx : z ≠ x := by
    intro h
    obtain ⟨s, hs, hsx⟩ := hxnc
    exact hsx (by rw [← h]; exact hzc s hs)
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hzn : z ∉ zpowers x := by
    intro hm
    rcases eq_one_or_eq_of_mem_zpowers hx2 hm with h | h
    · exact hz1 h
    · exact hzx h
  obtain ⟨-, hcard⟩ := SU1.isElemAbelian_card_sup_zpowers Nat.prime_two
    (by rw [pow_two]; exact hx2) (by rw [pow_two]; exact hz2) hx1 hzn (hVel.1 x hxV z hzV)
  have hgen : zpowers x ⊔ zpowers z = V :=
    Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hxV)
      (Subgroup.zpowers_le.mpr hzV)) (by rw [hcard, hV4.2.2])
  have hzuniq : ∀ c ∈ S, (∀ s ∈ S, s * c = c * s) → c * c = 1 → c = 1 ∨ c = z := by
    intro c hcS hcc hc2
    have hcV : c ∈ V := hV.mem_of_commute (hSX hcS) hc2 (fun v hv => (hcc v (hVS hv)).symm)
    rw [← hgen] at hcV
    obtain ⟨a, ha, b, hb, hab⟩ := SU1.mem_sup_of_commute
      (zpowers_commute_of (show x * z = z * x from hVel.1 x hxV z hzV)) hcV
    obtain ⟨s, hs, hsx⟩ := hxnc
    have hac := eq_one_or_eq_of_mem_zpowers hx2 ha
    have hbc := eq_one_or_eq_of_mem_zpowers hz2 hb
    rcases hac with h1 | h1 <;> rcases hbc with h2 | h2
    · left; rw [← hab, h1, h2]; simp
    · right; rw [← hab, h1, h2]; simp
    · exfalso
      apply hsx
      have hcx : c = x := by rw [← hab, h1, h2]; simp
      rw [← hcx]; exact hcc s hs
    · exfalso
      apply hsx
      have hcxz : c = x * z := by rw [← hab, h1, h2]
      have hxc : x = c * z := by rw [hcxz, mul_assoc, hz2, mul_one]
      rw [hxc]
      calc s * (c * z) = (s * c) * z := by group
        _ = (c * s) * z := by rw [hcc s hs]
        _ = c * (s * z) := by group
        _ = c * (z * s) := by rw [hzc s hs]
        _ = (c * z) * s := by group
  have hVS' : IsIsolatedVertex S V := hV.mono hSX hVS
  obtain ⟨h4S, hisoS⟩ := hVS'
  have hz2' : z ^ 2 = 1 := by rw [pow_two]; exact hz2
  obtain ⟨-, hall⟩ := SU1.ig10_21_iii Nat.prime_two hS.2.1 hSrk
    (exists_isNormalEp2 hS.2.1 hSrk) ⟨V, h4S⟩ hisoS (E := zpowers z)
    (Subgroup.zpowers_le.mpr hzS) (le_normalizer_zpowers_of_central hzc)
    (SU1.isElemAbelian_zpowers hz2') (by rwa [Ne, Subgroup.zpowers_eq_bot])
  have hxE : x ∉ zpowers z := by
    intro hm
    rcases eq_one_or_eq_of_mem_zpowers hz2 hm with h | h
    · exact hx1 h
    · exact hzx h.symm
  obtain ⟨-, K, hKS, hKC, hKinf, hKsup, hVEK, hKrk⟩ := (hall x hxV hxE).2
  have hzK : z ∈ K := hVEK (Subgroup.mem_inf.mpr ⟨hzV, Subgroup.mem_zpowers z⟩)
  have hKinv : ∀ k ∈ K, k * k = 1 → k = 1 ∨ k = z := by
    intro k hkK hk2
    by_contra hcon
    push Not at hcon
    have hkn : k ∉ zpowers z := by
      intro hm
      rcases eq_one_or_eq_of_mem_zpowers hz2 hm with h | h
      · exact hcon.1 h
      · exact hcon.2 h
    have hcomm : z * k = k * z := (hzc k (hKS hkK)).symm
    obtain ⟨hel2, hcard2⟩ := SU1.isElemAbelian_card_sup_zpowers Nat.prime_two hz2'
      (by rw [pow_two]; exact hk2) hz1 hkn hcomm
    have hle : zpowers z ⊔ zpowers k ≤ K :=
      sup_le (Subgroup.zpowers_le.mpr hzK) (Subgroup.zpowers_le.mpr hkK)
    have := SU1.le_pRank (by norm_num) hle hel2 hcard2
    omega
  have hw : ∃ w ∈ K, w * w = z := by
    by_contra hcon
    push Not at hcon
    have hKz : K ≤ zpowers z := by
      intro k hk
      by_contra hkn
      obtain ⟨y, hyK, -, -, hyyV, hyy1⟩ := exists_orderOf_four (P := K) (V := zpowers z)
        (hS.2.1.to_le hKS)
        (fun v hv => by
          rcases eq_one_or_eq_of_mem_zpowers hz2 hv with h | h <;> rw [h] <;> simp [hz2])
        (fun t ht h => by
          rcases hKinv t ht h with h' | h' <;> rw [h'] <;> simp)
        hk hkn
      rcases eq_one_or_eq_of_mem_zpowers hz2 hyyV with h | h
      · exact hyy1 h
      · exact hcon y hyK h
    have hCle : centralizer ({x} : Set G) ⊓ S ≤ V := by
      rw [← hKsup, ← hgen]
      exact sup_le_sup_left hKz _
    have hc4 : Nat.card ↥(S ⊓ centralizer ({x} : Set G)) ≤ 4 := by
      rw [inf_comm]
      have := Subgroup.card_le_of_le hCle
      rw [hV4.2.2] at this
      simpa using this
    have h8 := eight_lt_card_of_rank_three hSrk hxS hc4
    have := SU1.ig10_24_25 hS.2.1 h8 hxS hc4
    omega
  obtain ⟨w, hwK, hww⟩ := hw
  have hnotO := x_not_mem_oResidual hV hgen.symm hS hSrk hVS hxV hx2 hKS
    (fun k hk => Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)) hwK hww
  exact ⟨x, z, S, K, ⟨hxV, hzV, hxo, hzo, hgen.symm, hS, hsylc, le_inf hKC hKS, hKinf, hKsup, hzK,
    hKinv, hzc, hzuniq, hnotO⟩⟩

end Finite

end CFSG.GH74.Uniqueness.SU.SU4
