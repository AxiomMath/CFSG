module

public import CFSG.Goldschmidt.OddCore
public import CFSG.GroupTheory.QuasiDihedralFusion.OddKernel
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Defs

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.Open CFSG.Goldschmidt

section Gold

variable {G : Type} [Group G] [Finite G]

theorem pCore_open_eq_bot_of_simple [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    CFSG.Open.pCore 2 G = ⊥ := by
  have hn : (CFSG.Open.pCore 2 G).Normal := CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal 2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.Open.pCore 2 G) with h | h
  · exact h
  · exfalso
    have hp : IsPGroup 2 G := by
      have := CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup (G := G) 2
      rw [h] at this
      exact this.of_equiv Subgroup.topEquiv
    have hs : Group.IsSolvable G := by
      have := hp.isNilpotent
      infer_instance
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (IsSimpleGroup.comm_iff_isSolvable.2 hs a b)

theorem mem_of_involution_of_fusionStronglyClosed (hGold : CoreStatement) [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G) {A : Subgroup G}
    (hAS : A ≤ (S : Subgroup G)) (hAab : IsMulCommutative A) (hAne : A ≠ ⊥)
    (hclosed : fusionStronglyClosed (A : Set G) (S : Subgroup G)) {s : G}
    (hsS : s ∈ (S : Subgroup G)) (hs : s * s = 1) : s ∈ A := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnc : Subgroup.normalClosure (A : Set G) = ⊤ := by
    have hn : (Subgroup.normalClosure (A : Set G)).Normal := Subgroup.normalClosure_normal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure (A : Set G)) with h | h
    · exfalso
      exact hAne (le_bot_iff.mp (h ▸ Subgroup.subset_normalClosure))
    · exact h
  have hO : goldschmidtOddCore G = ⊥ := by
    rw [goldschmidtOddCore_eq_pPrimeCore]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 G) with h | h
    · exact h
    · exfalso
      have h2 : Nat.Coprime 2 (Nat.card (pPrimeCore 2 G)) := pPrimeCore_coprime_card
      rw [h, Subgroup.card_top] at h2
      have hAp : IsPGroup 2 A := (S.isPGroup').to_le hAS
      obtain ⟨k, hk⟩ := hAp.exists_card_eq
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hAne (Subgroup.card_eq_one.1 (by simpa using hk))
      have h3 : 2 ∣ Nat.card G := by
        have : 2 ∣ Nat.card A := by
          rw [hk]
          exact dvd_pow_self 2 hk0
        exact this.trans (Subgroup.card_subgroup_dvd_card A)
      exact absurd (Nat.Coprime.eq_one_of_dvd h2 h3) (by norm_num)
  obtain ⟨h1, h2, -⟩ := hGold G S A hAS hAab hclosed hnc hO
  have hp : CFSG.Open.pCore 2 G = ⊥ := pCore_open_eq_bot_of_simple hnonab
  rw [hp, bot_sup_eq] at h1 h2
  have hmem : s ∈ Subgroup.closure
      {t | t ∈ (S : Subgroup G) ⊓ goldschmidtLayer G ∧ t ^ 2 = 1} :=
    Subgroup.subset_closure ⟨⟨hsS, by rw [h1]; exact Subgroup.mem_top _⟩, by rw [sq]; exact hs⟩
  rw [← h2] at hmem
  exact hmem


@[expose] def AhatNoncommutingInvolutions : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (n : ℕ), 8 ≤ n → IsDoubleCoverOfAlt Q n →
    ∃ u v : Q, u * u = 1 ∧ v * v = 1 ∧ u * v ≠ v * u ∧ (u * v) ^ 4 = 1

theorem isPGroup_closure_pair {Q : Type} [Group Q] {u v : Q} (hu : u * u = 1) (hv : v * v = 1)
    (huv : (u * v) ^ 4 = 1) : IsPGroup 2 ↥(Subgroup.closure ({u, v} : Set Q)) := by
  set r : Q := u * v with hr
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have hur1 : u * r * u⁻¹ = r⁻¹ := by
    rw [hr, mul_inv_rev, hui, hvi]
    calc u * (u * v) * u = (u * u) * v * u := by group
      _ = v * u := by rw [hu, one_mul]
  have hur : ∀ k : ℤ, u * r ^ k * u = r ^ (-k) := by
    intro k
    have h2 : u * r ^ k * u⁻¹ = (u * r * u⁻¹) ^ k := by
      simp
    rw [hui] at h2 hur1
    rw [h2, hur1, inv_zpow, zpow_neg]
  have hur' : ∀ k : ℤ, u * r ^ k = r ^ (-k) * u := by
    intro k
    calc u * r ^ k = (u * r ^ k * u) * u := by rw [mul_assoc, mul_assoc, hu, mul_one]
      _ = r ^ (-k) * u := by rw [hur]
  let W : Subgroup Q :=
    { carrier := {g | ∃ k : ℤ, g = r ^ k ∨ g = r ^ k * u}
      one_mem' := ⟨0, Or.inl (by simp)⟩
      mul_mem' := by
        rintro a b ⟨ka, ha | ha⟩ ⟨kb, hb | hb⟩
        · exact ⟨ka + kb, Or.inl (by rw [ha, hb, zpow_add])⟩
        · exact ⟨ka + kb, Or.inr (by rw [ha, hb, zpow_add, mul_assoc])⟩
        · refine ⟨ka - kb, Or.inr ?_⟩
          rw [ha, hb, mul_assoc, hur', ← mul_assoc, ← zpow_add, sub_eq_add_neg]
        · refine ⟨ka - kb, Or.inl ?_⟩
          rw [ha, hb, mul_assoc, ← mul_assoc u, hur, ← zpow_add, sub_eq_add_neg]
      inv_mem' := by
        rintro a ⟨k, ha | ha⟩
        · exact ⟨-k, Or.inl (by rw [ha, zpow_neg])⟩
        · refine ⟨k, Or.inr ?_⟩
          rw [ha, mul_inv_rev, hui, ← zpow_neg, hur', neg_neg] }
  have hv' : v = r ^ (-1 : ℤ) * u := by
    have h1 : u * r = r ^ (-1 : ℤ) * u := by simpa using hur' 1
    calc v = u * r := by rw [hr, ← mul_assoc, hu, one_mul]
      _ = r ^ (-1 : ℤ) * u := h1
  have hD : Subgroup.closure ({u, v} : Set Q) ≤ W := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨0, Or.inr (by simp)⟩
    · exact ⟨-1, Or.inr hv'⟩
  intro x
  obtain ⟨k, hk | hk⟩ := hD x.2
  · refine ⟨2, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, hk]
    norm_num
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, huv, one_zpow]
  · refine ⟨2, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, hk]
    have h2 : (r ^ k * u) ^ 2 = 1 := by
      rw [sq, mul_assoc, ← mul_assoc u, hur, ← zpow_add, add_neg_cancel, zpow_zero]
    norm_num
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, one_pow]


theorem eq_one_of_mem_pPrimeCore_of_isPGroup {Y : Type} [Group Y] [Finite Y] {x : Y}
    (hx : x ∈ pPrimeCore 2 Y) {P : Subgroup Y} (hP : IsPGroup 2 ↥P) (hxP : x ∈ P) : x = 1 := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hP) ⟨x, hxP⟩
  have h1 : orderOf x = 2 ^ k := by rwa [Subgroup.orderOf_mk] at hk
  have hOdd : Odd (Nat.card (pPrimeCore 2 Y)) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have h2 : Odd (orderOf x) := Odd.of_dvd_nat hOdd (Subgroup.orderOf_dvd_natCard _ hx)
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.2 h2) (h1 ▸ Nat.even_pow.2 ⟨even_two, hk0⟩)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at h1
  exact h1

theorem false_of_isAhatIntr_of_fusionStronglyClosed (hGold : CoreStatement)
    (hInv : AhatNoncommutingInvolutions) [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {t : G} {L : Subgroup G} (hL : IsAhatIntr G t L)
    (S : Sylow 2 G) {A : Subgroup G} (hAS : A ≤ (S : Subgroup G)) (hAab : IsMulCommutative A)
    (hAne : A ≠ ⊥) (hclosed : fusionStronglyClosed (A : Set G) (S : Subgroup G)) : False := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, n, hn, hcov⟩ := hL
  obtain ⟨u, v, hu, hv, huv, h4⟩ := hInv _ n hn hcov
  have hD := isPGroup_closure_pair hu hv h4
  obtain ⟨PQ, hPQ⟩ := hD.exists_le_sylow
  let π : ↥L →* ↥L ⧸ pPrimeCore 2 ↥L := QuotientGroup.mk' _
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  obtain ⟨P, hP⟩ := QuasiDihedralFusion.exists_sylow_map_eq π hπs PQ
  have huP : u ∈ (P : Subgroup ↥L).map π := by
    rw [hP]
    exact hPQ (Subgroup.subset_closure (by simp))
  have hvP : v ∈ (P : Subgroup ↥L).map π := by
    rw [hP]
    exact hPQ (Subgroup.subset_closure (by simp))
  obtain ⟨u', hu'P, hu'⟩ := huP
  obtain ⟨v', hv'P, hv'⟩ := hvP
  have hker : ∀ x ∈ (P : Subgroup ↥L), π x = 1 → x = 1 := fun x hx h1 =>
    eq_one_of_mem_pPrimeCore_of_isPGroup ((QuotientGroup.eq_one_iff x).1 h1) P.isPGroup' hx
  have hu'2 : u' * u' = 1 :=
    hker _ (mul_mem hu'P hu'P) (by rw [map_mul, show π u' = u from hu', hu])
  have hv'2 : v' * v' = 1 :=
    hker _ (mul_mem hv'P hv'P) (by rw [map_mul, show π v' = v from hv', hv])
  have hnc : u' * v' ≠ v' * u' := fun h => huv (by
    have := congrArg π h
    rwa [map_mul, map_mul, show π u' = u from hu', show π v' = v from hv'] at this)
  set PG : Subgroup G := (P : Subgroup ↥L).map L.subtype with hPG
  have hPGp : IsPGroup 2 ↥PG := P.isPGroup'.map L.subtype
  obtain ⟨S', hS'⟩ := hPGp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S' S
  have hconj : ∀ x ∈ (S' : Subgroup G), g * x * g⁻¹ ∈ (S : Subgroup G) := by
    intro x hx
    rw [← hg, Sylow.coe_subgroup_smul]
    exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨x, hx, by simp [MulAut.smul_def]⟩
  have hu'S : (u' : G) ∈ (S' : Subgroup G) := hS' ⟨u', hu'P, rfl⟩
  have hv'S : (v' : G) ∈ (S' : Subgroup G) := hS' ⟨v', hv'P, rfl⟩
  have hu'G : (u' : G) * (u' : G) = 1 := by
    have := congrArg (fun y : ↥L => (y : G)) hu'2
    simpa using this
  have hv'G : (v' : G) * (v' : G) = 1 := by
    have := congrArg (fun y : ↥L => (y : G)) hv'2
    simpa using this
  have hs1 : g * (u' : G) * g⁻¹ ∈ A :=
    mem_of_involution_of_fusionStronglyClosed hGold hnonab S hAS hAab hAne hclosed
      (hconj _ hu'S) (by
        calc g * (u' : G) * g⁻¹ * (g * (u' : G) * g⁻¹) = g * ((u' : G) * (u' : G)) * g⁻¹ := by
              group
          _ = 1 := by rw [hu'G]; group)
  have hs2 : g * (v' : G) * g⁻¹ ∈ A :=
    mem_of_involution_of_fusionStronglyClosed hGold hnonab S hAS hAab hAne hclosed
      (hconj _ hv'S) (by
        calc g * (v' : G) * g⁻¹ * (g * (v' : G) * g⁻¹) = g * ((v' : G) * (v' : G)) * g⁻¹ := by
              group
          _ = 1 := by rw [hv'G]; group)
  have hcomm := congrArg Subtype.val (hAab.is_comm.comm ⟨_, hs1⟩ ⟨_, hs2⟩)
  apply hnc
  apply Subtype.ext
  have : g * (u' : G) * g⁻¹ * (g * (v' : G) * g⁻¹) = g * (v' : G) * g⁻¹ * (g * (u' : G) * g⁻¹) :=
    hcomm
  show (u' : G) * (v' : G) = (v' : G) * (u' : G)
  calc (u' : G) * (v' : G) = g⁻¹ * (g * (u' : G) * g⁻¹ * (g * (v' : G) * g⁻¹)) * g := by group
    _ = g⁻¹ * (g * (v' : G) * g⁻¹ * (g * (u' : G) * g⁻¹)) * g := by rw [this]
    _ = (v' : G) * (u' : G) := by group

end Gold

end CFSG.OddStandard.Solomon75
