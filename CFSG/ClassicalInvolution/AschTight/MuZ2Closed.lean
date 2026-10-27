module

public import CFSG.ClassicalInvolution.AschTight.MuZ2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

theorem exists_conj_mem_of_sylow_le [Finite G] (S : Sylow 2 G) {H : Subgroup G}
    (hSH : (S : Subgroup G) ≤ H) {x : G} (hxH : x ∈ H) (hx2 : IsPGroup 2 (Subgroup.zpowers x)) :
    ∃ m ∈ H, m * x * m⁻¹ ∈ (S : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S' : Sylow 2 H := S.subtype hSH
  have hW : IsPGroup 2 ((Subgroup.zpowers x).subgroupOf H) :=
    hx2.of_equiv (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxH)).symm
  obtain ⟨P, hP⟩ := hW.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq H P S'
  refine ⟨(m : G), m.2, ?_⟩
  have hxP : (⟨x, hxH⟩ : H) ∈ (P : Subgroup H) :=
    hP (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers x))
  have hmem : MulAut.conj m (⟨x, hxH⟩ : H) ∈ ((m • P : Sylow 2 H) : Subgroup H) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hxP
  rw [hm] at hmem
  have hmem' : MulAut.conj m (⟨x, hxH⟩ : H) ∈ (S : Subgroup G).subgroupOf H := by
    rw [← Sylow.coe_subtype S hSH]
    exact hmem
  exact hmem'

namespace SDData

variable {P : Subgroup G} {a b : G} {M : ℕ}

theorem mul_self_eq (h : SDData P a b M) {y : G} (hy : y ∈ P) (hy2 : y * y * (y * y) = 1)
    (hy1 : y * y ≠ 1) : y * y = a ^ (4 * (M : ℤ)) := by
  have hM := h.M_pos
  have h4 : a ^ (4 * (M : ℤ)) * a ^ (4 * (M : ℤ)) = 1 := by
    rw [← zpow_add, h.zpow_eq_one_iff]
    exact ⟨1, by ring⟩
  have h41 : a ^ (4 * (M : ℤ)) ≠ 1 := by
    rw [Ne, h.zpow_eq_one_iff]
    rintro ⟨c, hc⟩
    have : (M : ℤ) * (4 - 8 * c) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0 <;> omega
  obtain ⟨i, hi⟩ : ∃ i : ℤ, a ^ i = y * y := by
    rcases h.mem_or hy with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨i + i, by rw [zpow_add]⟩
    · exact ⟨4 * M * i, (h.sq i).symm⟩
  rw [← hi] at hy2 hy1 ⊢
  exact zpow_eq_zpow_of_mul_self_eq_one hy2 h4 hy1 h41

end SDData

variable {p f : ℕ} [Fact p.Prime] [Finite G] {K : Subgroup G} {z : G}

theorem mem_sup_of_conj_mem_of_mem_centralizer (ht : S19R.TightStd p f K z)
    (hA : AllTypeTwo K z) {R : Subgroup G} (hR : R ∈ RSet (CoreAssembly.conjClass K))
    (hRK : R ≤ K) {S : Sylow 2 G} (hRS : R ≤ (S : Subgroup G))
    (hSKR : (S : Subgroup G) ⊓ K ≤ R) (hSN : (S : Subgroup G) ≤ Subgroup.normalizer (R : Set G))
    (hSz : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G)) {g : G}
    (htS : g * z * g⁻¹ ∈ (S : Subgroup G)) (htz : g * z * g⁻¹ ≠ z) {x : G}
    (hxP : x ∈ R ⊔ Subgroup.zpowers (g * z * g⁻¹)) {c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) (hcx : c * x * c⁻¹ ∈ (S : Subgroup G)) :
    c * x * c⁻¹ ∈ R ⊔ Subgroup.zpowers (g * z * g⁻¹) := by
  have htb := ht.toTightBranch
  have hI := isUniqueInvolution_of_tight htb
  have hU := uniqueInvolutionNormal_of_tight htb
  have hNC := normalizer_eq_centralizer_of_tight htb
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
    have hkC : k ∈ Subgroup.centralizer ({z} : Set G) := (le_centralizer_of_tight htb) hk'
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

theorem false_of_mul_self_eq (ht : S19R.TightStd p f K z) (hA : AllTypeTwo K z) {w : G}
    (hwz : w * z = z * w) {g : G} (hw : w * w = g * z * g⁻¹) (htz : g * z * g⁻¹ ≠ z) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htb := ht.toTightBranch
  have hI := isUniqueInvolution_of_tight htb
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
    rw [Subgroup.zpowers_le, normalizer_eq_centralizer_of_tight htb,
      Subgroup.mem_centralizer_singleton_iff]
    exact hwz
  have hV2 : IsPGroup 2 (Subgroup.zpowers w) :=
    IsPGroup.of_card (n := 2) (by rw [hV4]; norm_num)
  obtain ⟨R', hR', hR'N⟩ := AscL62.exists_sylow_normalized hV2 hVN
  have hVNR : Subgroup.zpowers w ≤ Subgroup.normalizer (R' : Set G) := fun v hv =>
    mem_normalizer_iff_conjSub_eq.mpr (hR'N v hv)
  have hR'R : R' ∈ RSet (CoreAssembly.conjClass K) :=
    mem_RSet_of_isSylow2In (CoreAssembly.mem_conjClass_self K) hR'
  have h8 := (exists_ne_comm_of_mem_rSet ht.branch.odd ht.branch.five ht.branch.member hR'R).2
  have hzR' : IsUniqueInvolution R' z := isUniqueInvolution_of_mem_rSet_of_le htb hR'R hR'.1
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

theorem isSemidihedral_sup_of_allTypeTwo (ht : S19R.TightStd p f K z) (hA : AllTypeTwo K z)
    {R : Subgroup G} (hR : R ∈ RSet (CoreAssembly.conjClass K)) (hRK : R ≤ K) {g : G}
    (htN : g * z * g⁻¹ ∈ Subgroup.normalizer (R : Set G))
    (htzc : g * z * g⁻¹ * z = z * (g * z * g⁻¹)) (htz : g * z * g⁻¹ ≠ z) :
    IsSemidihedral (R ⊔ Subgroup.zpowers (g * z * g⁻¹)) := by
  have htb := ht.toTightBranch
  have hI := isUniqueInvolution_of_tight htb
  have hU := uniqueInvolutionNormal_of_tight htb
  set t := g * z * g⁻¹ with htdef
  have ht2 : t * t = 1 := by
    calc t * t = g * (z * z) * g⁻¹ := by rw [htdef]; group
      _ = 1 := by rw [hI.sq]; group
  have ht1 : t ≠ 1 := fun h1 => hI.ne_one (by
    have : z = g⁻¹ * t * g := by rw [htdef]; group
    rw [this, h1]; group)
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [_root_.sq]; exact ht2) ht1
  have htR : t ∉ R := fun h1 => htz (hU.2.2.1 t (hRK h1) hord)
  have hR2 : IsPGroup 2 R := isPGroup_of_mem_rSet hR
  have hzt : ∀ y ∈ Subgroup.zpowers t, y = 1 ∨ y = t := fun y hy =>
    eq_one_or_eq_of_mem_zpowers_of_mul_self ht2 hy
  have hCRt : ¬ 4 ≤ Nat.card ↥(R ⊓ Subgroup.centralizer ({t} : Set G)) := by
    have := hA K (CoreAssembly.mem_conjClass_self K) z t hI ⟨g, rfl⟩ htz htzc
      (R ⊓ Subgroup.centralizer ({t} : Set G)) (hR2.to_le inf_le_left) (inf_le_left.trans hRK)
      inf_le_right
    omega
  have hcfg : AscL62.CoreCfg R (Subgroup.zpowers t) z t :=
    { quat := isQuatSub_of_mem_rSet ht.branch.odd ht.branch.five ht.branch.member hR
      hz := isUniqueInvolution_of_mem_rSet_of_le htb hR hRK
      V2 := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, pow_one]; exact hord)
      norm := fun y hy => conjSub_eq_of_mem_normalizer (Subgroup.zpowers_le.mpr htN hy)
      inter := fun y hy hyR => (hzt y hy).resolve_right fun h1 => htR (h1 ▸ hyR)
      ht := ⟨Subgroup.mem_zpowers t, ht1, ht2, fun y hy _ => hzt y hy⟩ }
  exact (hcfg.eq_zpowers_and_isSemidihedral hCRt).2

theorem mem_sup_of_conj_mem (ht : S19R.TightStd p f K z) (hA : AllTypeTwo K z)
    {R : Subgroup G} (hR : R ∈ RSet (CoreAssembly.conjClass K)) (hRK : R ≤ K) {S : Sylow 2 G}
    (hRS : R ≤ (S : Subgroup G)) (hSKR : (S : Subgroup G) ⊓ K ≤ R)
    (hSN : (S : Subgroup G) ≤ Subgroup.normalizer (R : Set G))
    (hSz : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G)) {g : G}
    (htS : g * z * g⁻¹ ∈ (S : Subgroup G)) (htz : g * z * g⁻¹ ≠ z) {x : G}
    (hxP : x ∈ R ⊔ Subgroup.zpowers (g * z * g⁻¹)) {y : G}
    (hyx : y * x * y⁻¹ ∈ (S : Subgroup G)) :
    y * x * y⁻¹ ∈ R ⊔ Subgroup.zpowers (g * z * g⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htb := ht.toTightBranch
  have hI := isUniqueInvolution_of_tight htb
  have hcl : ∀ h : G, h * z * h⁻¹ ∈ (S : Subgroup G) →
      h * z * h⁻¹ ∈ R ⊔ Subgroup.zpowers (g * z * g⁻¹) := fun h hh =>
    mem_sup_of_allTypeTwo ht hA hR hRK S.isPGroup' hRS hSN hSz htS htz hh
  have hzR : IsUniqueInvolution R z := isUniqueInvolution_of_mem_rSet_of_le htb hR hRK
  have hR2 : IsPGroup 2 R := isPGroup_of_mem_rSet hR
  have hRnc := (exists_ne_comm_of_mem_rSet ht.branch.odd ht.branch.five ht.branch.member hR).1
  set t := g * z * g⁻¹ with htdef
  have ht2 : t * t = 1 := by
    calc t * t = g * (z * z) * g⁻¹ := by rw [htdef]; group
      _ = 1 := by rw [hI.sq]; group
  have htzc : t * z = z * t := Subgroup.mem_centralizer_singleton_iff.mp (hSz htS)
  have hU := uniqueInvolutionNormal_of_tight htb
  have htR : t ∉ R := fun h1 => htz (hU.2.2.1 t (hRK h1)
    (orderOf_eq_prime (by rw [_root_.sq]; exact ht2) fun h2 => hI.ne_one (by
      have : z = g⁻¹ * t * g := by rw [htdef]; group
      rw [this, h2]; group)))
  have hsd := isSemidihedral_sup_of_allTypeTwo ht hA hR hRK (hSN htS) htzc htz
  have hPS : R ⊔ Subgroup.zpowers t ≤ (S : Subgroup G) :=
    sup_le hRS (Subgroup.zpowers_le.mpr htS)
  obtain ⟨a, b, M, hsdd⟩ := exists_sdData (S.isPGroup'.to_le hPS) hsd
  have hM := hsdd.M_pos
  have ha2 : a * a ∈ R := mul_self_mem_of_mem_sup_zpowers ht2 (hSN htS) hsdd.a_mem
  have hza : z = a ^ (4 * (M : ℤ)) := by
    have h4 : a ^ (4 * (M : ℤ)) ∈ R := by
      rw [show 4 * (M : ℤ) = 2 * (2 * M) by ring, zpow_mul, zpow_two]
      exact R.zpow_mem ha2 _
    refine ((hzR.unique _ h4 ?_).resolve_left ?_).symm
    · rw [← zpow_add, hsdd.zpow_eq_one_iff]; exact ⟨1, by ring⟩
    · rw [hsdd.zpow_eq_one_iff]
      rintro ⟨c, hc⟩
      have : (M : ℤ) * (4 - 8 * c) = 0 := by linarith
      rcases mul_eq_zero.mp this with h0 | h0 <;> omega
  by_cases hx1 : x = 1
  · rw [hx1, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  by_cases hx2 : x * x = 1
  ·
    by_cases hxR : x ∈ R
    · have hxz : x = z := (hzR.unique x hxR hx2).resolve_left hx1
      rw [hxz]
      exact hcl y (by rw [← hxz]; exact hyx)
    · obtain ⟨-, q, -, hq⟩ := conj_of_not_mem_of_isSemidihedral hR2 hzR hRnc ht2 htR (hSN htS)
        hsd hxP hxR (Or.inl hx2)
      have e : y * x * y⁻¹ = (y * q * g) * z * (y * q * g)⁻¹ := by
        rw [← hq, htdef]; group
      rw [e]
      exact hcl _ (by rw [← e]; exact hyx)
  ·
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp (S.isPGroup'.to_le hPS)) ⟨x, hxP⟩
    rw [Subgroup.orderOf_mk] at hj
    have hj2 : 2 ≤ j := by
      by_contra hj2
      apply hx2
      rw [← _root_.sq]
      have : orderOf x ∣ 2 := by
        rw [hj]
        exact (pow_dvd_pow 2 (by omega : j ≤ 1)).trans (by rw [pow_one])
      exact orderOf_dvd_iff_pow_eq_one.mp this
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : G, x ^ (2 ^ (j - 2)) = x₀ := ⟨_, rfl⟩
    have hx₀P : x₀ ∈ R ⊔ Subgroup.zpowers t := hx₀ ▸ Subgroup.pow_mem _ hxP _
    have hx₀2 : x₀ * x₀ = x ^ (2 ^ (j - 1)) := by
      rw [← hx₀, ← pow_add, ← two_mul, ← pow_succ', show j - 2 + 1 = j - 1 by omega]
    have hx₀4 : x₀ * x₀ * (x₀ * x₀) = 1 := by
      rw [hx₀2, ← pow_add, ← two_mul, ← pow_succ', show j - 1 + 1 = j by omega, ← hj,
        pow_orderOf_eq_one]
    have hx₀1 : x₀ * x₀ ≠ 1 := by
      rw [hx₀2]
      exact pow_ne_one_of_lt_orderOf (pow_ne_zero _ two_ne_zero)
        (by rw [hj]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
    have hx₀z : x₀ * x₀ = z := (hsdd.mul_self_eq hx₀P hx₀4 hx₀1).trans hza.symm
    by_cases hyz : y * z * y⁻¹ = z
    ·
      have hyC : y ∈ Subgroup.centralizer ({z} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc y * z = y * z * y⁻¹ * y := by group
          _ = z * y := by rw [hyz]
      exact mem_sup_of_conj_mem_of_mem_centralizer ht hA hR hRK hRS hSKR hSN hSz htS htz hxP hyC
        hyx
    ·
      exfalso
      have hwS : y * x₀ * y⁻¹ ∈ (S : Subgroup G) := by
        rw [← hx₀, ← conj_pow]
        exact Subgroup.pow_mem _ hyx _
      have hw : y * x₀ * y⁻¹ * (y * x₀ * y⁻¹) = y * z * y⁻¹ := by
        rw [← hx₀z]; group
      exact false_of_mul_self_eq ht hA
        (Subgroup.mem_centralizer_singleton_iff.mp (hSz hwS)) hw hyz

end CFSG.ClassicalInvolution.Disconnected.AschTight
