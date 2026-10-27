module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.GH74.GLS.Stage2.OddAut

theorem odd_of_coprime_two {n : ℕ} (h : Nat.Coprime n 2) : Odd n := by
  have h2 : ¬ 2 ∣ n := fun hd => by
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm h) hd
    omega
  exact Nat.odd_iff.2 (by omega)

theorem radRigidInner_of_sylow_core {K : Type} [Group K] [Finite K] (hBT : HoldsTits K 2)
    (T : Sylow 2 K)
    (hcore : ∀ R : Subgroup K, IsRadical 2 R → R ≤ (T : Subgroup K) →
      (T : Subgroup K) ≤ Subgroup.normalizer (R : Set K) →
        ∀ g : K, (∀ r ∈ R, g * r = r * g) → Odd (orderOf g) → g = 1) :
    RadRigidInner 2 K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro R hR x hx hxo
  have hR' := hR
  obtain ⟨h0, hp, hc, hnt⟩ := hR
  obtain ⟨-, -, -, -, -, U, hUN⟩ := canonical_parabolic_tits hBT h0 hp
  rw [radInf_eq_of_pCoreOf hc] at hUN
  have hRU : R ≤ (U : Subgroup K) := by
    have hsup : IsPGroup 2 ↥(R ⊔ (U : Subgroup K)) := hp.to_sup_of_normal_left' U.isPGroup' hUN
    have h1 : R ⊔ (U : Subgroup K) = (U : Subgroup K) := U.is_maximal' hsup le_sup_right
    exact h1 ▸ le_sup_left
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K U T
  have hTU : (T : Subgroup K) = (U : Subgroup K).map (MulAut.conj k).toMonoidHom := by
    rw [← hk, Sylow.coe_subgroup_smul]
    rfl
  have hrad : IsRadical 2 (R.map (MulAut.conj k : K ≃* K).toMonoidHom) :=
    IsRadical.map_mulEquiv (MulAut.conj k : K ≃* K) hR'
  have h1 : R.map (MulAut.conj k : K ≃* K).toMonoidHom ≤ (T : Subgroup K) := by
    rw [hTU]
    exact Subgroup.map_mono hRU
  have h2 : (T : Subgroup K) ≤ Subgroup.normalizer
      ((R.map (MulAut.conj k : K ≃* K).toMonoidHom : Subgroup K) : Set K) := by
    rw [← Subgroup.map_equiv_normalizer_eq, hTU]
    exact Subgroup.map_mono hUN
  have hcomm : ∀ r ∈ R.map (MulAut.conj k : K ≃* K).toMonoidHom,
      (k * x * k⁻¹) * r = r * (k * x * k⁻¹) := by
    rintro _ ⟨r, hr, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc k * x * k⁻¹ * (k * r * k⁻¹) = k * (x * r) * k⁻¹ := by group
      _ = k * (r * x) * k⁻¹ := by rw [hx r hr]
      _ = k * r * k⁻¹ * (k * x * k⁻¹) := by group
  have hodd : Odd (orderOf (k * x * k⁻¹)) := by
    have : orderOf (k * x * k⁻¹) = orderOf x :=
      orderOf_injective (MulAut.conj k : K ≃* K).toMonoidHom (MulAut.conj k : K ≃* K).injective x
    rw [this]
    exact odd_of_coprime_two hxo
  have := hcore _ hrad h1 h2 _ hcomm hodd
  have h3 : k * x * k⁻¹ = 1 := this
  rw [mul_inv_eq_one] at h3
  have : x = 1 := by
    have h4 : k⁻¹ * (k * x) = k⁻¹ * k := by rw [h3]
    simpa using h4
  exact this

theorem zpowers_four_cases {K : Type} [Group K] (z : K) (hz4 : orderOf z = 4) {w : K}
    (hw : w ∈ Subgroup.zpowers z) (hw1 : w ≠ 1) : w = z ^ 2 ∨ w ^ 2 = z ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have hz : z ^ 4 = 1 := by rw [← hz4]; exact pow_orderOf_eq_one z
  have hmod : z ^ k = z ^ (k % 4) := by
    have := zpow_mod_orderOf z k
    rw [hz4] at this
    simpa using this.symm
  have h4 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases h4 with h | h | h | h
  · exact absurd (by rw [hmod, h]; simp) hw1
  · right
    rw [hmod, h]
    simp
  · left
    rw [hmod, h]
    simp
  · right
    rw [hmod, h, ← zpow_natCast, ← zpow_mul]
    have : (3 : ℤ) * (((2 : ℕ) : ℤ)) = 4 + 2 := by norm_num
    rw [show ((3 : ℤ) * ((2 : ℕ) : ℤ)) = 4 + 2 by norm_num, zpow_add, show (4 : ℤ) = ((4 : ℕ) : ℤ) by rfl,
      zpow_natCast, hz, one_mul]
    simp

theorem u33_core {K : Type} [Group K] [Finite K] (T : Subgroup K) (z : K) (hT2 : IsPGroup 2 T)
    (hT : Nat.card T = 32) (hzT : z ∈ T) (hz4 : orderOf z = 4)
    (hzc : ∀ x ∈ T, x * z = z * x)
    (hZ : ∀ x ∈ T, (∀ y ∈ T, x * y = y * x) → x ∈ Subgroup.zpowers z)
    (hC : Nat.card (Subgroup.centralizer ({z ^ 2} : Set K)) = 96)
    (hE : ∀ g : K, g ^ 3 = 1 → g ≠ 1 → g * z ^ 2 = z ^ 2 * g → ∀ x ∈ T, x * g = g * x →
      x ∈ Subgroup.zpowers z)
    (R : Subgroup K) (hR : IsRadical 2 R) (hRT : R ≤ T)
    (hTN : T ≤ Subgroup.normalizer (R : Set K)) (g : K) (hg : ∀ r ∈ R, g * r = r * g)
    (hgo : Odd (orderOf g)) : g = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hg1
  obtain ⟨h0, hp, hc, hnt⟩ := hR
  have ht : z ^ 2 ∈ R := by
    haveI : Group.IsNilpotent T := hT2.isNilpotent
    haveI hnorm : (R.subgroupOf T).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hRT).2 hTN
    have hne : R.subgroupOf T ≠ ⊥ := by
      intro hbot
      apply h0
      rw [eq_bot_iff]
      intro r hr
      have h1 : (⟨r, hRT hr⟩ : T) ∈ R.subgroupOf T := hr
      rw [hbot, Subgroup.mem_bot] at h1
      have := congrArg Subtype.val h1
      simpa using this
    obtain ⟨y, hy⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
    obtain ⟨hyR, hyZ⟩ := Subgroup.mem_inf.1 y.2
    have hyR' : ((y : T) : K) ∈ R := hyR
    have hyc : ∀ x ∈ T, ((y : T) : K) * x = x * ((y : T) : K) := by
      intro x hx
      have := Subgroup.mem_center_iff.1 hyZ ⟨x, hx⟩
      exact (congrArg Subtype.val this).symm
    have hyz : ((y : T) : K) ∈ Subgroup.zpowers z := hZ _ (y : T).2 hyc
    have hy1 : ((y : T) : K) ≠ 1 := by
      intro h1
      apply hy
      apply Subtype.ext
      apply Subtype.ext
      exact h1
    rcases zpowers_four_cases z hz4 hyz hy1 with h | h
    · rw [← h]; exact hyR'
    · rw [← h]; exact pow_mem hyR' 2
  have hgM : g ∈ Subgroup.centralizer ({z ^ 2} : Set K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact (hg _ ht).symm
  have hord96 : orderOf g ∣ 96 := hC ▸ Subgroup.orderOf_dvd_natCard _ hgM
  have hord3 : orderOf g ∣ 3 := by
    have h2 : ¬ 2 ∣ orderOf g := fun hd => by
      obtain ⟨m, hm⟩ := hgo
      omega
    have hcop : Nat.Coprime (2 ^ 5) (orderOf g) :=
      Nat.Coprime.pow_left 5 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2)
    have : orderOf g ∣ 3 * 2 ^ 5 := by simpa using hord96
    exact Nat.Coprime.dvd_of_dvd_mul_right hcop.symm this
  have hg3 : g ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.1 hord3
  have hgt : g * z ^ 2 = z ^ 2 * g := hg _ ht
  have hRz : R ≤ Subgroup.zpowers z := fun r hr =>
    hE g hg3 hg1 hgt r (hRT hr) (hg r hr).symm
  have hRcard : Nat.card R ≤ 4 := by
    have h1 := Subgroup.card_le_of_le hRz
    rwa [Nat.card_zpowers, hz4] at h1
  set M : Subgroup K := Subgroup.centralizer ({z ^ 2} : Set K) with hMdef
  have hTM : T ≤ M := by
    intro x hx
    rw [hMdef, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    have h1 : z * x = x * z := (hzc x hx).symm
    calc z ^ 2 * x = z * (z * x) := by rw [pow_two, mul_assoc]
      _ = z * (x * z) := by rw [h1]
      _ = (z * x) * z := by rw [mul_assoc]
      _ = (x * z) * z := by rw [h1]
      _ = x * z ^ 2 := by rw [pow_two, mul_assoc]
  set T' : Subgroup M := T.subgroupOf M with hT'def
  have hT'card : Nat.card T' = 32 := by
    rw [← hT]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv
  have hT'index : T'.index = 3 := by
    have h1 := Subgroup.card_mul_index T'
    rw [hT'card, hC] at h1
    omega
  set N : Subgroup M := T'.normalCore with hNdef
  have hNle : N ≤ T' := Subgroup.normalCore_le T'
  have hNindex : N.index ≤ 6 := by
    have := Subgroup.index_normalCore_le_factorial_index (H := T')
    rw [hT'index] at this
    simpa [Nat.factorial] using this
  have hNcard : 16 ≤ Nat.card N := by
    have h1 := Subgroup.card_mul_index N
    rw [hC] at h1
    have hpos : 0 < N.index := Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := N))
    nlinarith
  set Q : Subgroup K := N.map M.subtype with hQdef
  have hQT : Q ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact hNle hx
  have hQcard : 16 ≤ Nat.card Q := by
    rw [hQdef, Subgroup.card_map_of_injective M.subtype_injective]
    exact hNcard
  have hQnorm : ∀ m ∈ M, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q := by
    rintro m hm _ ⟨a, ha, rfl⟩
    refine ⟨⟨m, hm⟩ * a * ⟨m, hm⟩⁻¹, ?_, rfl⟩
    exact (inferInstance : N.Normal).conj_mem a ha ⟨m, hm⟩
  have hQM : ∀ m ∈ M, m ∈ Subgroup.normalizer (Q : Set K) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨fun hq => hQnorm m hm q hq, fun hq => ?_⟩
    have := hQnorm m⁻¹ (inv_mem hm) _ hq
    simpa [mul_assoc] using this
  set C : Subgroup K := Subgroup.centralizer (R : Set K) with hCdef
  have hCM : C ≤ M := Subgroup.centralizer_le (by
    rintro _ rfl
    exact ht)
  have hQC : Q ≤ C := by
    intro q hq
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro r hr
    have hrz := hRz hr
    have hqz : Commute q z := hzc q (hQT hq)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hrz
    exact ((hqz.zpow_right k).eq).symm
  have hQp : IsPGroup 2 Q := hT2.to_le hQT
  have hQcore : Q ≤ pCoreOf 2 C :=
    le_pCoreOf_of_le_normalizer 2 hQC (fun c hc' => hQM c (hCM hc')) hQp
  have hCN : C ≤ Subgroup.normalizer (R : Set K) := Subgroup.centralizer_le_normalizer _
  have hNC : Subgroup.normalizer (R : Set K) ≤ Subgroup.normalizer (C : Set K) := by
    intro n hn
    have key : ∀ n ∈ Subgroup.normalizer (R : Set K), ∀ c ∈ C, n * c * n⁻¹ ∈ C := by
      intro n hn c hc'
      rw [hCdef, Subgroup.mem_centralizer_iff] at hc' ⊢
      intro r hr
      have hr' : n⁻¹ * r * n ∈ R := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) r).1 hr
        simpa using this
      have h1 := hc' _ hr'
      calc r * (n * c * n⁻¹) = n * ((n⁻¹ * r * n) * c) * n⁻¹ := by group
        _ = n * (c * (n⁻¹ * r * n)) * n⁻¹ := by rw [h1]
        _ = n * c * n⁻¹ * r := by group
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc' => key n hn c hc', fun hc' => ?_⟩
    have := key n⁻¹ (inv_mem hn) _ hc'
    simpa [mul_assoc] using this
  have hCcoreR : pCoreOf 2 C ≤ R := by
    have h1 : pCoreOf 2 C ≤ pCoreOf 2 (Subgroup.normalizer (R : Set K)) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 C).trans hCN)
        (hNC.trans (normalizer_le_normalizer_pCoreOf 2 C)) (pCoreOf_isPGroup 2 C)
    rwa [hc] at h1
  have hQR : Q ≤ R := hQcore.trans hCcoreR
  have := Subgroup.card_le_of_le hQR
  omega

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
