module

public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDMuA

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6.SD

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem mem_sup_of_conj_mem_of_mem_centralizer (ht : Setup194Three K z)
    (hA : AllTypeTwo K z) {R : Subgroup G} (hR : R ∈ RSet (CoreAssembly.conjClass K))
    (hRK : R ≤ K) {S : Sylow 2 G} (hRS : R ≤ (S : Subgroup G))
    (hSKR : (S : Subgroup G) ⊓ K ≤ R) (hSN : (S : Subgroup G) ≤ Subgroup.normalizer (R : Set G))
    (hSz : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G)) {g : G}
    (htS : g * z * g⁻¹ ∈ (S : Subgroup G)) (htz : g * z * g⁻¹ ≠ z) {x : G}
    (hxP : x ∈ R ⊔ Subgroup.zpowers (g * z * g⁻¹)) {c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) (hcx : c * x * c⁻¹ ∈ (S : Subgroup G)) :
    c * x * c⁻¹ ∈ R ⊔ Subgroup.zpowers (g * z * g⁻¹) := by
  have hI := ht.isUniqueInvolution
  have hU := ht.uniqueInvolutionNormal
  have hNC := ht.normEq
  have hcl : ∀ h : G, h * z * h⁻¹ ∈ (S : Subgroup G) →
      h * z * h⁻¹ ∈ R ⊔ Subgroup.zpowers (g * z * g⁻¹) := fun h hh =>
    mem_sup_of_allTypeTwo ht hA hR hRK S.isPGroup' hRS hSN hSz htS htz hh
  set t := g * z * g⁻¹ with htdef
  have ht2 : t * t = 1 := by
    calc t * t = g * (z * z) * g⁻¹ := by rw [htdef]; group
      _ = 1 := by rw [hI.sq]; group
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hN : ∀ n ∈ Subgroup.centralizer ({z} : Set G), ∀ k ∈ K, n * k * n⁻¹ ∈ K :=
    fun n hn k hk => (Subgroup.mem_normalizer_iff.mp (hNC ▸ hn) k).mp hk
  have hNi : ∀ n ∈ Subgroup.centralizer ({z} : Set G), ∀ k ∈ K, n⁻¹ * k * n ∈ K :=
    fun n hn k hk => by
      have := hN n⁻¹ (Subgroup.inv_mem _ hn) k hk
      rwa [inv_inv] at this
  have htC : t ∈ Subgroup.centralizer ({z} : Set G) := hSz htS
  have htK : t ∉ K := by
    intro htK
    have h2 : orderOf t = 2 := orderOf_eq_prime (by rw [_root_.sq]; exact ht2) (fun h1 => by
      have : z = g⁻¹ * t * g := by rw [htdef]; group
      rw [h1] at this
      exact hI.ne_one (by rw [this]; group))
    exact htz (hU.2.2.1 t htK h2)
  have hPK : ∀ y ∈ R ⊔ Subgroup.zpowers t, y ∉ K → y * t ∈ R := fun y hy hyK =>
    (mem_or_mul_mem_of_mem_sup_zpowers ht2 (hSN htS) hy).resolve_left fun h => hyK (hRK h)
  have hPK' : ∀ y ∈ R ⊔ Subgroup.zpowers t, y ∉ K → y * t⁻¹ ∈ K := fun y hy hyK => by
    rw [hti]; exact hRK (hPK y hy hyK)
  rcases mem_or_mul_mem_of_mem_sup_zpowers ht2 (hSN htS) hxP with hxR | hxR
  · exact Subgroup.mem_sup_left (hSKR ⟨hcx, hN c hc x (hRK hxR)⟩)
  · obtain ⟨r, hr⟩ : ∃ r : G, x * t = r := ⟨_, rfl⟩
    rw [hr] at hxR
    have hxr : x = r * t := by rw [← hr, mul_assoc, ht2, mul_one]
    obtain ⟨t₁, ht₁⟩ : ∃ t₁ : G, c * t * c⁻¹ = t₁ := ⟨_, rfl⟩
    have hk : c * r * c⁻¹ ∈ K := hN c hc r (hRK hxR)
    have hy : c * x * c⁻¹ = (c * r * c⁻¹) * t₁ := by rw [hxr, ← ht₁]; group
    have hSKN : (S : Subgroup G) ≤ Subgroup.normalizer (K : Set G) := hNC ▸ hSz
    have ht₁H : t₁ ∈ (S : Subgroup G) ⊔ K := by
      have e : t₁ = (c * r * c⁻¹)⁻¹ * (c * x * c⁻¹) := by rw [hy]; group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (K.inv_mem hk))
        (Subgroup.mem_sup_left hcx)
    have ht₁2 : IsPGroup 2 (Subgroup.zpowers t₁) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one]
      have hne : t₁ ≠ 1 := fun h1 => htK (by
        have : t = c⁻¹ * t₁ * c := by rw [← ht₁]; group
        rw [this, h1]
        simp)
      refine orderOf_eq_prime ?_ hne
      rw [_root_.sq, ← ht₁]
      calc c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
        _ = 1 := by rw [ht2]; group
    obtain ⟨m, hmH, hmS⟩ := exists_conj_mem_of_sylow_le S le_sup_left ht₁H ht₁2
    have hm : m ∈ (((S : Subgroup G) ⊔ K : Subgroup G) : Set G) := hmH
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hSKN] at hm
    obtain ⟨s, hs, k, hk', rfl⟩ := Set.mem_mul.mp hm
    have hsC : s ∈ Subgroup.centralizer ({z} : Set G) := hSz hs
    have hkC : k ∈ Subgroup.centralizer ({z} : Set G) := ht.le_centralizer hk'
    have hu : s * k * t₁ * (s * k)⁻¹ ∈ R ⊔ Subgroup.zpowers t := by
      have e : s * k * t₁ * (s * k)⁻¹ = (s * k * c * g) * z * (s * k * c * g)⁻¹ := by
        rw [← ht₁, htdef]; group
      rw [e]
      exact hcl _ (by rw [← e]; exact hmS)
    have huK : s * k * t₁ * (s * k)⁻¹ ∉ K := by
      intro h1
      apply htK
      have e : t = (s * k * c)⁻¹ * (s * k * t₁ * (s * k)⁻¹) * (s * k * c) := by
        rw [← ht₁]; group
      rw [e]
      exact hNi _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hsC hkC) hc) _ h1
    have hvS : s⁻¹ * t * s ∈ (S : Subgroup G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hs) htS) hs
    have hv : s⁻¹ * t * s ∈ R ⊔ Subgroup.zpowers t := by
      have e : s⁻¹ * t * s = (s⁻¹ * g) * z * (s⁻¹ * g)⁻¹ := by rw [htdef]; group
      rw [e]
      exact hcl _ (by rw [← e]; exact hvS)
    have hvK : s⁻¹ * t * s ∉ K := fun h1 => htK (by
      have := hN s hsC _ h1
      rwa [show s * (s⁻¹ * t * s) * s⁻¹ = t by group] at this)
    have h1 := hPK' _ hu huK
    have h2 := hPK' _ hv hvK
    have h3 : t₁ * t⁻¹ ∈ K := by
      have e : t₁ * t⁻¹ = k⁻¹ * (s⁻¹ * (s * k * t₁ * (s * k)⁻¹ * t⁻¹) * s) *
          (s⁻¹ * t * s * t⁻¹) * (t * k * t⁻¹) := by group
      rw [e]
      refine K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem hk') (hNi s hsC _ h1)) h2) ?_
      exact hN t htC k hk'
    have h4 : c * x * c⁻¹ * t⁻¹ ∈ K := by
      rw [hy, mul_assoc]
      exact K.mul_mem hk h3
    have h5 : c * x * c⁻¹ * t⁻¹ ∈ R :=
      hSKR ⟨Subgroup.mul_mem _ hcx (Subgroup.inv_mem _ htS), h4⟩
    have e : c * x * c⁻¹ = (c * x * c⁻¹ * t⁻¹) * t := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h5)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))

theorem false_of_mul_self_eq (ht : Setup194Three K z) (hA : AllTypeTwo K z) {w : G}
    (hwz : w * z = z * w) {g : G} (hw : w * w = g * z * g⁻¹) (htz : g * z * g⁻¹ ≠ z) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hI := ht.isUniqueInvolution
  set t := g * z * g⁻¹ with htdef
  have ht2 : t * t = 1 := by
    calc t * t = g * (z * z) * g⁻¹ := by rw [htdef]; group
      _ = 1 := by rw [hI.sq]; group
  have ht1 : t ≠ 1 := fun h1 => hI.ne_one (by
    have : z = g⁻¹ * t * g := by rw [htdef]; group
    rw [this, h1]; group)
  have htzc : t * z = z * t := by
    rw [← hw]
    calc w * w * z = w * (w * z) := by group
      _ = w * (z * w) := by rw [hwz]
      _ = z * w * w := by rw [← mul_assoc, hwz]
      _ = z * (w * w) := by group
  have hw4 : orderOf w = 4 := by
    refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
    · rw [pow_one, _root_.sq, hw]; exact ht1
    · rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, _root_.sq w, hw, _root_.sq, ht2]
  have hV4 : Nat.card (Subgroup.zpowers w) = 4 := by rw [Nat.card_zpowers, hw4]
  have hVN : Subgroup.zpowers w ≤ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.zpowers_le, ht.normEq,
      Subgroup.mem_centralizer_singleton_iff]
    exact hwz
  have hV2 : IsPGroup 2 (Subgroup.zpowers w) :=
    IsPGroup.of_card (n := 2) (by rw [hV4]; norm_num)
  obtain ⟨R', hR', hR'N⟩ := AscL62.exists_sylow_normalized hV2 hVN
  have hVNR : Subgroup.zpowers w ≤ Subgroup.normalizer (R' : Set G) := fun v hv =>
    mem_normalizer_iff_conjSub_eq.mpr (hR'N v hv)
  have hR'R : R' ∈ RSet (CoreAssembly.conjClass K) :=
    mem_RSet_of_isSylow2In (CoreAssembly.mem_conjClass_self K) hR'
  have h8 := (ht.exists_ne_comm_of_mem_rSet hR'R).2
  have hzR' : IsUniqueInvolution R' z := ht.isUniqueInvolution_of_mem_rSet_of_le hR'R hR'.1
  obtain ⟨k, hk⟩ := hR'.2.1.exists_card_eq
  have hk3 : 3 ≤ k := by
    by_contra hk3
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h4 : 4 ∣ Nat.card R' := by
    rw [hk, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact pow_dvd_pow 2 (by omega)
  have hCt := hA K (CoreAssembly.mem_conjClass_self K) z t hI ⟨g, rfl⟩ htz htzc
    (R' ⊓ Subgroup.centralizer ({t} : Set G)) (hR'.2.1.to_le inf_le_left)
    (inf_le_left.trans hR'.1) inf_le_right
  refine false_of_card_centralizer_eq_two hV4 hVNR h4 fun v hv hv1 => ?_
  have htv : t ∈ Subgroup.zpowers v := by
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    rw [← zpow_mod_orderOf, hw4] at hv1 ⊢
    obtain ⟨m, hm⟩ : ∃ m : ℕ, j % ((4 : ℕ) : ℤ) = m :=
      ⟨(j % 4).toNat, by
        have := Int.emod_nonneg j (by norm_num : ((4 : ℕ) : ℤ) ≠ 0)
        push_cast at this ⊢
        omega⟩
    have hm4 : m < 4 := by
      have := Int.emod_lt_of_pos j (by norm_num : (0 : ℤ) < ((4 : ℕ) : ℤ))
      omega
    rw [hm, zpow_natCast] at hv1 ⊢
    have hw4' : w ^ 4 = 1 := by rw [← hw4]; exact pow_orderOf_eq_one w
    interval_cases m
    · exact absurd (pow_zero w) hv1
    · rw [pow_one, ← hw]
      exact Subgroup.mul_mem _ (Subgroup.mem_zpowers w) (Subgroup.mem_zpowers w)
    · rw [_root_.sq, hw]
      exact Subgroup.mem_zpowers t
    · have e : (w ^ 3) ^ 2 = t := by
        rw [← pow_mul, show 3 * 2 = 4 + 2 by norm_num, pow_add, hw4', one_mul, _root_.sq, hw]
      rw [← e]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
  have hle : R' ⊓ Subgroup.centralizer ({v} : Set G) ≤
      R' ⊓ Subgroup.centralizer ({t} : Set G) := by
    refine inf_le_inf_left _ fun y hy => ?_
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp htv
    rw [← hi]
    exact ((Commute.zpow_left (show Commute v y from hy.symm) i).eq).symm
  have hne : R' ⊓ Subgroup.centralizer ({v} : Set G) ≠ ⊥ := by
    intro hbot
    have hmem : z ∈ R' ⊓ Subgroup.centralizer ({v} : Set G) := by
      refine ⟨hzR'.mem, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have := Subgroup.mem_centralizer_singleton_iff.mp
        ((Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hwz)) hv)
      exact this.symm
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hI.ne_one hmem
  have h1 := Subgroup.card_le_of_le hle
  have h2 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  omega

end CFSG.ClassicalInvolution.Q3.Q3T6.SD
