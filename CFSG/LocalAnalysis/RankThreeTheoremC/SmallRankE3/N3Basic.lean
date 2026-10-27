module

public import CFSG.Open.RankThreeDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

variable {Γ : Type} [Group Γ] [Finite Γ] (X : Subgroup Γ)

theorem subgroupOf_normal_of_conj {N : Subgroup Γ} (hN : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) :
    (N.subgroupOf X).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  exact hN g.1 g.2 n.1 hn

theorem conj_mem_zpowers_of_central {Zc : Subgroup Γ} (hZc : ∀ k ∈ Zc, ∀ g : Γ, g * k = k * g)
    {g : Γ} (hg : g ∈ Zc) {x n : Γ} (hn : n ∈ Subgroup.zpowers g) :
    x * n * x⁻¹ ∈ Subgroup.zpowers g := by
  have hnZ : n ∈ Zc := Subgroup.zpowers_le.mpr hg hn
  have hc : x * n * x⁻¹ = n := by rw [hZc n hnZ x, mul_inv_cancel_right]
  rw [hc]
  exact hn

theorem exists_split_two_odd {G : Type*} [Group G] (k : G) {a m : ℕ} (hm : Odd m)
    (hn : orderOf k = 2 ^ a * m) :
    ∃ k2 ∈ Subgroup.zpowers k, ∃ ko ∈ Subgroup.zpowers k,
      k = k2 * ko ∧ k2 ^ 2 ^ a = 1 ∧ ko ^ m = 1 := by
  have hcop : Nat.Coprime m (2 ^ a) := Nat.Coprime.pow_right a hm.coprime_two_right
  have hbez : (1 : ℤ) = (m : ℤ) * Nat.gcdA m (2 ^ a) + ((2 ^ a : ℕ) : ℤ) * Nat.gcdB m (2 ^ a) := by
    have h := Nat.gcd_eq_gcd_ab m (2 ^ a)
    rw [hcop.gcd_eq_one] at h
    exact_mod_cast h
  refine ⟨k ^ ((m : ℤ) * Nat.gcdA m (2 ^ a)), Subgroup.zpow_mem_zpowers k _,
    k ^ (((2 ^ a : ℕ) : ℤ) * Nat.gcdB m (2 ^ a)), Subgroup.zpow_mem_zpowers k _, ?_, ?_, ?_⟩
  · rw [← zpow_add, ← hbez, zpow_one]
  · rw [← zpow_natCast, ← zpow_mul]
    apply orderOf_dvd_iff_zpow_eq_one.mp
    rw [hn]
    exact ⟨Nat.gcdA m (2 ^ a), by push_cast; ring⟩
  · rw [← zpow_natCast, ← zpow_mul]
    apply orderOf_dvd_iff_zpow_eq_one.mp
    rw [hn]
    exact ⟨Nat.gcdB m (2 ^ a), by push_cast; ring⟩

theorem pCoreOf_two_le : pCoreOf 2 X ≤ X := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
  exact y.2

theorem pCoreOf_two_conj {x : Γ} (hx : x ∈ X) {t : Γ} (ht : t ∈ pCoreOf 2 X) :
    x * t * x⁻¹ ∈ pCoreOf 2 X := by
  obtain ⟨t₀, ht₀, rfl⟩ := Subgroup.mem_map.mp ht
  have hN : (CFSG.pCore 2 ↥X).Normal := CFSG.pCore_normal
  exact Subgroup.mem_map.mpr
    ⟨(⟨x, hx⟩ : X) * t₀ * (⟨x, hx⟩ : X)⁻¹, hN.conj_mem t₀ ht₀ _, rfl⟩

theorem pCoreOf_two_isPGroup : IsPGroup 2 (pCoreOf 2 X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (CFSG.pCore_isPGroup (p := 2) (G := ↥X))
  refine IsPGroup.of_card (n := n) ?_
  unfold pCoreOf
  rw [Subgroup.card_map_of_injective X.subtype_injective, hn]

theorem le_pCoreOf_two {N : Subgroup Γ} (hNX : N ≤ X) (hN : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hN2 : IsPGroup 2 N) : N ≤ pCoreOf 2 X := by
  have hM : (N.subgroupOf X).Normal := subgroupOf_normal_of_conj X hN
  have hM2 : IsPGroup 2 (N.subgroupOf X) := by
    intro g
    obtain ⟨k, hk⟩ := hN2 ⟨g.1.1, Subgroup.mem_subgroupOf.mp g.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have h := congrArg Subtype.val hk
    simpa using h
  have hle : N.subgroupOf X ≤ CFSG.pCore 2 ↥X := le_sSup ⟨hM, hM2⟩
  calc N = (N.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hNX).symm
    _ ≤ (CFSG.pCore 2 ↥X).map X.subtype := Subgroup.map_mono hle
    _ = pCoreOf 2 X := rfl

theorem primeCore_two_le : rankThreePrimeCore 2 X ≤ X :=
  relPPrimeCore_le X

theorem primeCore_two_conj {x : Γ} (hx : x ∈ X) {y : Γ} (hy : y ∈ rankThreePrimeCore 2 X) :
    x * y * x⁻¹ ∈ rankThreePrimeCore 2 X := by
  have hyX : y ∈ X := primeCore_two_le X hy
  have hmem : (⟨y, hyX⟩ : ↥X) ∈ (rankThreePrimeCore 2 X).subgroupOf X :=
    Subgroup.mem_subgroupOf.mpr hy
  have h := (relPPrimeCore_normal (p := 2) Nat.prime_two X).conj_mem _ hmem ⟨x, hx⟩
  exact Subgroup.mem_subgroupOf.mp h

theorem primeCore_two_coprime : Nat.Coprime 2 (Nat.card (rankThreePrimeCore 2 X)) :=
  coprime_card_relPPrimeCore Nat.prime_two X

theorem le_primeCore_two {N : Subgroup Γ} (hNX : N ≤ X) (hN : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hN2 : Nat.Coprime 2 (Nat.card N)) : N ≤ rankThreePrimeCore 2 X := by
  have hM : (N.subgroupOf X).Normal := subgroupOf_normal_of_conj X hN
  unfold rankThreePrimeCore relPPrimeCore
  exact le_sSup ⟨hNX, hM, hN2⟩

theorem primeCore_two_commute_pCore {y t : Γ} (hy : y ∈ rankThreePrimeCore 2 X)
    (ht : t ∈ pCoreOf 2 X) : y * t = t * y := by
  have hyX : y ∈ X := primeCore_two_le X hy
  have htX : t ∈ X := pCoreOf_two_le X ht
  have hc_Y : y * t * y⁻¹ * t⁻¹ ∈ rankThreePrimeCore 2 X := by
    have h1 : t * y⁻¹ * t⁻¹ ∈ rankThreePrimeCore 2 X :=
      primeCore_two_conj X htX ((rankThreePrimeCore 2 X).inv_mem hy)
    have h2 := (rankThreePrimeCore 2 X).mul_mem hy h1
    rwa [show y * t * y⁻¹ * t⁻¹ = y * (t * y⁻¹ * t⁻¹) by group]
  have hc_T : y * t * y⁻¹ * t⁻¹ ∈ pCoreOf 2 X := by
    have h1 : y * t * y⁻¹ ∈ pCoreOf 2 X := pCoreOf_two_conj X hyX ht
    exact (pCoreOf 2 X).mul_mem h1 ((pCoreOf 2 X).inv_mem ht)
  have hmem : y * t * y⁻¹ * t⁻¹ ∈ rankThreePrimeCore 2 X ⊓ pCoreOf 2 X :=
    Subgroup.mem_inf.mpr ⟨hc_Y, hc_T⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (pCoreOf_two_isPGroup X)
  have hd1 : Nat.card ↥(rankThreePrimeCore 2 X ⊓ pCoreOf 2 X) ∣ Nat.card ↥(rankThreePrimeCore 2 X) :=
    Subgroup.card_dvd_of_le inf_le_left
  have hd2 : Nat.card ↥(rankThreePrimeCore 2 X ⊓ pCoreOf 2 X) ∣ Nat.card ↥(pCoreOf 2 X) :=
    Subgroup.card_dvd_of_le inf_le_right
  have hcop : Nat.Coprime 2 (Nat.card ↥(rankThreePrimeCore 2 X ⊓ pCoreOf 2 X)) :=
    Nat.Coprime.coprime_dvd_right hd1 (primeCore_two_coprime X)
  have hK : Nat.card ↥(rankThreePrimeCore 2 X ⊓ pCoreOf 2 X) ∣ 2 ^ n := by
    rw [← hn]
    exact hd2
  have hK1 : Nat.card ↥(rankThreePrimeCore 2 X ⊓ pCoreOf 2 X) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right n hcop.symm) hK
  have hsub := (Nat.card_eq_one_iff_unique.mp hK1).1
  have hc1 : (⟨y * t * y⁻¹ * t⁻¹, hmem⟩ : ↥(rankThreePrimeCore 2 X ⊓ pCoreOf 2 X)) = 1 :=
    Subsingleton.elim _ _
  have hc : y * t * y⁻¹ * t⁻¹ = 1 := congrArg Subtype.val hc1
  calc y * t = y * t * y⁻¹ * t⁻¹ * (t * y) := by group
    _ = t * y := by rw [hc, one_mul]

theorem mem_sup_primeCore_pCore {x : Γ} :
    x ∈ rankThreePrimeCore 2 X ⊔ pCoreOf 2 X ↔
      ∃ y ∈ rankThreePrimeCore 2 X, ∃ t ∈ pCoreOf 2 X, x = y * t := by
  constructor
  · intro hx
    let S : Subgroup Γ :=
      { carrier := {r | ∃ a ∈ rankThreePrimeCore 2 X, ∃ b ∈ pCoreOf 2 X, r = a * b}
        mul_mem' := by
          rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
          refine ⟨a₁ * a₂, (rankThreePrimeCore 2 X).mul_mem ha₁ ha₂, b₁ * b₂,
            (pCoreOf 2 X).mul_mem hb₁ hb₂, ?_⟩
          calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by simp only [mul_assoc]
            _ = a₁ * (a₂ * b₁) * b₂ := by rw [primeCore_two_commute_pCore X ha₂ hb₁]
            _ = a₁ * a₂ * (b₁ * b₂) := by simp only [mul_assoc]
        one_mem' := ⟨1, (rankThreePrimeCore 2 X).one_mem, 1, (pCoreOf 2 X).one_mem,
          (mul_one 1).symm⟩
        inv_mem' := by
          rintro _ ⟨a, ha, b, hb, rfl⟩
          refine ⟨a⁻¹, (rankThreePrimeCore 2 X).inv_mem ha, b⁻¹, (pCoreOf 2 X).inv_mem hb, ?_⟩
          rw [mul_inv_rev]
          exact (primeCore_two_commute_pCore X ((rankThreePrimeCore 2 X).inv_mem ha)
            ((pCoreOf 2 X).inv_mem hb)).symm }
    have hS : rankThreePrimeCore 2 X ⊔ pCoreOf 2 X ≤ S := by
      refine sup_le ?_ ?_
      · intro a ha
        exact ⟨a, ha, 1, (pCoreOf 2 X).one_mem, (mul_one a).symm⟩
      · intro b hb
        exact ⟨1, (rankThreePrimeCore 2 X).one_mem, b, hb, (one_mul b).symm⟩
    obtain ⟨a, ha, b, hb, h⟩ := hS hx
    exact ⟨a, ha, b, hb, h⟩
  · rintro ⟨y, hy, t, ht, rfl⟩
    exact (rankThreePrimeCore 2 X ⊔ pCoreOf 2 X).mul_mem (Subgroup.mem_sup_left hy)
      (Subgroup.mem_sup_right ht)

theorem inf_central_le_sup {Zc : Subgroup Γ} (hZc : ∀ k ∈ Zc, ∀ g : Γ, g * k = k * g) {k : Γ}
    (hkX : k ∈ X) (hk : k ∈ Zc) : k ∈ rankThreePrimeCore 2 X ⊔ pCoreOf 2 X := by
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
  obtain ⟨k2, hk2, ko, hko, hsplit, hk2p, hkop⟩ := exists_split_two_odd k hm hn
  have hkZ : Subgroup.zpowers k ≤ Zc := Subgroup.zpowers_le.mpr hk
  have hkX' : Subgroup.zpowers k ≤ X := Subgroup.zpowers_le.mpr hkX
  have hk2Zc : k2 ∈ Zc := hkZ hk2
  have hkoZc : ko ∈ Zc := hkZ hko
  have hT : k2 ∈ pCoreOf 2 X := by
    have h1 : Subgroup.zpowers k2 ≤ pCoreOf 2 X := by
      refine le_pCoreOf_two X (Subgroup.zpowers_le.mpr (hkX' hk2)) ?_ ?_
      · intro x _ n hn'
        exact conj_mem_zpowers_of_central hZc hk2Zc hn'
      · refine IsPGroup.of_card_dvd_pow (n := a) ?_
        rw [Nat.card_zpowers]
        exact orderOf_dvd_of_pow_eq_one hk2p
    exact h1 (Subgroup.mem_zpowers k2)
  have hY : ko ∈ rankThreePrimeCore 2 X := by
    have h1 : Subgroup.zpowers ko ≤ rankThreePrimeCore 2 X := by
      refine le_primeCore_two X (Subgroup.zpowers_le.mpr (hkX' hko)) ?_ ?_
      · intro x _ n hn'
        exact conj_mem_zpowers_of_central hZc hkoZc hn'
      · rw [Nat.card_zpowers]
        exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hkop) hm.coprime_two_left
    exact h1 (Subgroup.mem_zpowers ko)
  rw [hsplit, hZc ko hkoZc k2]
  exact (rankThreePrimeCore 2 X ⊔ pCoreOf 2 X).mul_mem (Subgroup.mem_sup_left hY)
    (Subgroup.mem_sup_right hT)

theorem exists_mem_normalizer_not_mem {T R : Subgroup Γ} (hT : IsPGroup 2 T) (hRT : R ≤ T)
    (hne : R ≠ T) :
    ∃ t ∈ T, t ∉ R ∧ ∀ r : Γ, r ∈ R ↔ t * r * t⁻¹ ∈ R := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥T := hT.isNilpotent
  have hlt : R.subgroupOf T < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne ?_
    exact le_antisymm hRT (Subgroup.subgroupOf_eq_top.mp h)
  obtain ⟨g, hgN, hgR⟩ :=
    SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := ↥T) (R.subgroupOf T) hlt)
  have hgN' := Subgroup.mem_normalizer_iff.mp hgN
  refine ⟨(g : Γ), g.2, fun hmem => hgR (Subgroup.mem_subgroupOf.mpr hmem), fun r => ?_⟩
  by_cases hr : r ∈ T
  · have h := hgN' ⟨r, hr⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h
    exact h
  · constructor
    · intro hrR
      exact absurd (hRT hrR) hr
    · intro hcon
      exfalso
      apply hr
      have h1 : (g : Γ) * r * (g : Γ)⁻¹ ∈ T := hRT hcon
      have h2 := T.mul_mem (T.mul_mem (T.inv_mem g.2) h1) g.2
      rwa [show (g : Γ)⁻¹ * ((g : Γ) * r * (g : Γ)⁻¹) * (g : Γ) = r by group] at h2

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
