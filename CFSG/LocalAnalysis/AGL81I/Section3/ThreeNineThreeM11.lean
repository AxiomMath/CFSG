module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineOrders

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem pow_eq_pow_factorization_of_eq {p a k N : ℕ} (hp : p.Prime) (hN : N = p ^ a * k)
    (hk : ¬ p ∣ k) : p ^ a = p ^ N.factorization p := by
  have hk0 : k ≠ 0 := fun h => hk (h ▸ dvd_zero p)
  have hp0 : p ^ a ≠ 0 := pow_ne_zero a hp.ne_zero
  rw [hN, Nat.factorization_mul hp0 hk0, Finsupp.add_apply, hp.factorization_pow,
    Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hk, add_zero]

section SylowNormalizer

variable {G : Type*} [Group G] [Finite G]

theorem card_normalizer_sylow_eq {q : ℕ} [Fact q.Prime] (P P' : Sylow q G) :
    Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) =
      Nat.card (Subgroup.normalizer ((P' : Subgroup G) : Set G)) := by
  have h1 := (Subgroup.normalizer ((P : Subgroup G) : Set G)).card_mul_index
  have h2 := (Subgroup.normalizer ((P' : Subgroup G) : Set G)).card_mul_index
  have e1 : Nat.card (Sylow q G) = (Subgroup.normalizer ((P : Subgroup G) : Set G)).index :=
    Sylow.card_eq_index_normalizer P
  have e2 : Nat.card (Sylow q G) = (Subgroup.normalizer ((P' : Subgroup G) : Set G)).index :=
    Sylow.card_eq_index_normalizer P'
  rw [← e1] at h1
  rw [← e2] at h2
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)

theorem mem_normalizer_zpowers {g t : G} (h1 : t * g * t⁻¹ ∈ Subgroup.zpowers g)
    (h2 : t⁻¹ * g * t ∈ Subgroup.zpowers g) :
    t ∈ Subgroup.normalizer ((Subgroup.zpowers g : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ h1 n
  · intro hh
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hc : (t⁻¹ * g * t) ^ n = t⁻¹ * g ^ n * t := by
      have := conj_zpow (a := t⁻¹) (b := g) (i := n)
      rwa [inv_inv] at this
    have : h = (t⁻¹ * g * t) ^ n := by
      rw [hc, hn]
      group
    rw [this]
    exact Subgroup.zpow_mem _ h2 n

theorem orderOf_dvd_card_normalizer_sylow {q : ℕ} [Fact q.Prime] (P : Sylow q G) {g t : G}
    (hg : Nat.card (Subgroup.zpowers g) = q ^ (Nat.card G).factorization q)
    (h1 : t * g * t⁻¹ ∈ Subgroup.zpowers g) (h2 : t⁻¹ * g * t ∈ Subgroup.zpowers g) :
    orderOf t ∣ Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) := by
  rw [card_normalizer_sylow_eq P (Sylow.ofCard _ hg), Sylow.coe_ofCard]
  have ht := mem_normalizer_zpowers h1 h2
  have := orderOf_dvd_natCard
    (⟨t, ht⟩ : Subgroup.normalizer ((Subgroup.zpowers g : Subgroup G) : Set G))
  rwa [Subgroup.orderOf_mk] at this

theorem eight_dvd_card_normalizer_sylow {q : ℕ} [Fact q.Prime] (P : Sylow q G) {g t s : G}
    (hg : Nat.card (Subgroup.zpowers g) = q ^ (Nat.card G).factorization q)
    (h1 : t * g * t⁻¹ ∈ Subgroup.zpowers g) (h2 : t⁻¹ * g * t ∈ Subgroup.zpowers g)
    (ht4 : t ^ 4 = 1) (ht2 : t ^ 2 * g ≠ g * t ^ 2) (hs : orderOf s = 2) (hsg : s * g = g * s) :
    8 ∣ Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) := by
  rw [card_normalizer_sylow_eq P (Sylow.ofCard _ hg), Sylow.coe_ofCard]
  set H : Subgroup G := Subgroup.zpowers g with hH
  set N : Subgroup G := Subgroup.normalizer ((H : Subgroup G) : Set G) with hN
  let f := H.normalizerMonoidHom
  have hker : ∀ x : N, x ∈ f.ker ↔ (x : G) ∈ Subgroup.centralizer (H : Set G) := by
    intro x
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
  have ht : t ∈ N := mem_normalizer_zpowers h1 h2
  have hsC : s ∈ Subgroup.centralizer (H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((Commute.zpow_left (show Commute g s from hsg.symm) n)).eq
  have hsN : s ∈ N := Subgroup.centralizer_le_normalizer (H : Set G) hsC
  have hcard : Nat.card N = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have h2ker : 2 ∣ Nat.card f.ker := by
    have hmem : (⟨s, hsN⟩ : N) ∈ f.ker := (hker _).mpr hsC
    have := orderOf_dvd_natCard (⟨⟨s, hsN⟩, hmem⟩ : f.ker)
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hs] at this
  have h4range : 4 ∣ Nat.card f.range := by
    have hfx : orderOf (f ⟨t, ht⟩) = 2 ^ (1 + 1) := by
      refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
      · intro h
        rw [pow_one, ← map_pow] at h
        have hmem : ((⟨t, ht⟩ : N) ^ 2) ∈ f.ker := h
        rw [hker] at hmem
        apply ht2
        have := (Subgroup.mem_centralizer_iff.mp hmem) g (Subgroup.mem_zpowers g)
        simpa using this.symm
      · rw [← map_pow]
        have : (⟨t, ht⟩ : N) ^ 2 ^ (1 + 1) = 1 := by
          apply Subtype.ext
          simpa using ht4
        rw [this, map_one]
    have := orderOf_dvd_natCard (⟨f ⟨t, ht⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩ : f.range)
    rwa [Subgroup.orderOf_mk, hfx] at this
  rw [hcard]
  exact (Nat.mul_dvd_mul h4range h2ker : 4 * 2 ∣ _)

end SylowNormalizer

namespace ThreeNineHyp

variable {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {p d : ℕ}

theorem exists_sylow_normalizer_le (h : ThreeNineHyp K E D X₁ p d)
    (hZ : Subgroup.center ↥K = ⊥) (hd : ¬ d ∣ Nat.card (Outer ↥K)) :
    ∃ SD : Sylow d ↥K,
      Subgroup.normalizer ((SD : Subgroup ↥K) : Set ↥K) ≤ X₁.subgroupOf K := by
  have : Fact d.Prime := ⟨h.d_prime⟩
  have : K.Normal := h.normal
  have hDK : D ≤ K := h.D_le_K_of_not_dvd hZ hd
  have hDsylK : CFSG.ABGLocalTools.IsSylowOf d (D ⊓ K) K :=
    h.sylow.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top_iff.mpr h.normal])
  rw [inf_eq_left.mpr hDK] at hDsylK
  have hDcard := hDsylK.card_eq
  refine ⟨Sylow.ofCard (D.subgroupOf K) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv, hDcard]), ?_⟩
  intro n hn
  have hn' : n ∈ Subgroup.normalizer ((D.subgroupOf K : Subgroup ↥K) : Set ↥K) := hn
  rw [← Subgroup.subgroupOf_normalizer_eq hDK] at hn'
  exact h.normalizer_inf_le_of_le_D le_rfl h.D_ne_bot ⟨hn', le_sup_left (a := K) n.2⟩

end ThreeNineHyp

abbrev m11PermA : Equiv.Perm (Fin 11) :=
  List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] * List.formPerm [7, 8]

abbrev m11PermB : Equiv.Perm (Fin 11) :=
  List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8]

abbrev m11PermG : Equiv.Perm (Fin 11) :=
  m11PermB⁻¹ * m11PermA * m11PermB * m11PermB * m11PermA * m11PermB * m11PermA

theorem m11PermA_mem : m11PermA ∈ NativeSporadic.M11 :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem m11PermB_mem : m11PermB ∈ NativeSporadic.M11 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem m11PermG_mem : m11PermG ∈ NativeSporadic.M11 := by
  have ha := m11PermA_mem
  have hb := m11PermB_mem
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (inv_mem hb) ha) hb) hb) ha) hb) ha

theorem orderOf_m11PermG : orderOf m11PermG = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · ext i
    revert i
    decide +kernel
  · intro h
    have := congrArg (fun f : Equiv.Perm (Fin 11) => f 1) h
    revert this
    decide +kernel

theorem orderOf_m11PermA : orderOf m11PermA = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · ext i
    revert i
    decide +kernel
  · intro h
    have := congrArg (fun f : Equiv.Perm (Fin 11) => f 1) h
    revert this
    decide +kernel

theorem m11PermA_conj_G : m11PermA * m11PermG * m11PermA⁻¹ = m11PermG ^ 4 := by
  ext i
  revert i
  decide +kernel

theorem m11PermA_inv_conj_G : m11PermA⁻¹ * m11PermG * m11PermA = m11PermG ^ 4 := by
  ext i
  revert i
  decide +kernel

variable {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {d : ℕ}

theorem false_of_threeNineHyp_M11
    (h : ThreeNineHyp K E D X₁ 3 d)
    (hK : CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .M11) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact d.Prime := ⟨h.d_prime⟩
  obtain ⟨e⟩ := hK
  dsimp only [CFSG.Blueprint.NativeSporadic.Carrier] at e
  have hcard : Nat.card ↥K = 7920 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Schreier.m11_card
  have hZ : Subgroup.center ↥K = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e z ∈ Subgroup.center NativeSporadic.M11 := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro y
      have := hz (e.symm y)
      rw [← e.apply_symm_apply y, ← map_mul, ← map_mul, this]
    rw [CFSG.Sporadic.Schreier.m11_center_eq_bot, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    exact e.injective (by rw [hz', map_one])
  have hOut : Nat.card (Outer ↥K) ≤ 2 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact CFSG.Sporadic.Schreier.at_m11_schreier.1
  haveI : Finite (MulAut ↥K) :=
    Finite.of_injective (fun f : MulAut ↥K => (f : ↥K → ↥K)) fun f g hfg => MulEquiv.ext (congrFun hfg)
  have hOut0 : 0 < Nat.card (Outer ↥K) := Nat.card_pos
  have hd3 : 3 ≤ d := by
    have := h.d_prime.two_le
    have := h.d_ne_two
    omega
  have hdOut : ¬ d ∣ Nat.card (Outer ↥K) := fun hdv => by
    have := Nat.le_of_dvd hOut0 hdv
    omega
  have h3Out : ¬ 3 ∣ Nat.card (Outer ↥K) := fun hdv => by
    have := Nat.le_of_dvd hOut0 hdv
    omega
  obtain ⟨hY, hm3, hmd, h3Y, hdY, hdK⟩ := h.index_facts hZ h3Out hdOut
  obtain ⟨SD, hSD⟩ := h.exists_sylow_normalizer_le hZ hdOut
  rw [hcard] at h3Y hdY hdK
  have hY1 : (X₁.subgroupOf K).index ≠ 1 := fun h1 => hY (Subgroup.index_eq_one.mp h1)
  have h9 : (3 : ℕ) ^ (7920 : ℕ).factorization 3 = 9 :=
    (pow_eq_pow_factorization_of_eq (a := 2) (k := 880) Nat.prime_three (by norm_num)
      (by norm_num)).symm
  rw [h9] at h3Y
  have hd511 : d = 5 ∨ d = 11 := by
    have hfac : (7920 : ℕ) = 2 ^ 4 * 3 ^ 2 * 5 * 11 := by norm_num
    rw [hfac] at hdK
    rcases (Nat.Prime.dvd_mul h.d_prime).mp hdK with h1 | h1
    · rcases (Nat.Prime.dvd_mul h.d_prime).mp h1 with h1 | h1
      · rcases (Nat.Prime.dvd_mul h.d_prime).mp h1 with h1 | h1
        · exact absurd ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_two).mp
            (h.d_prime.dvd_of_dvd_pow h1)) h.d_ne_two
        · exact absurd ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_three).mp
            (h.d_prime.dvd_of_dvd_pow h1)) h.d_ne
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq h.d_prime (by norm_num)).mp h1)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq h.d_prime (by norm_num)).mp h1)
  rcases hd511 with rfl | rfl
  ·
    have h5 : (5 : ℕ) ^ (7920 : ℕ).factorization 5 = 5 :=
      (pow_eq_pow_factorization_of_eq (a := 1) (k := 1584) (by norm_num) (by norm_num)
        (by norm_num)).symm
    rw [h5] at hdY
    have h45 : 45 ∣ Nat.card (X₁.subgroupOf K) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 9 5) h3Y hdY
    have hidx := index_dvd_div_of_dvd_card h45
    rw [hcard] at hidx
    have key : ∀ m ∈ Nat.divisors 176, m ≡ 1 [MOD 3] → m ≡ 1 [MOD 5] → m ≠ 1 → m = 16 := by
      decide +kernel
    have h16 := key _ (Nat.mem_divisors.mpr ⟨hidx, by norm_num⟩) hm3 hmd hY1
    have hYcard : Nat.card (X₁.subgroupOf K) = 495 := by
      have hmul := (X₁.subgroupOf K).card_mul_index
      rw [hcard, h16] at hmul
      omega
    let gM : ↥NativeSporadic.M11 := ⟨m11PermG, m11PermG_mem⟩
    let tM : ↥NativeSporadic.M11 := ⟨m11PermA, m11PermA_mem⟩
    have hgM : orderOf gM = 5 := by rw [Subgroup.orderOf_mk, orderOf_m11PermG]
    have htM : orderOf tM = 2 := by rw [Subgroup.orderOf_mk, orderOf_m11PermA]
    have hc1 : tM * gM * tM⁻¹ = gM ^ 4 := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
      exact m11PermA_conj_G)
    have hc2 : tM⁻¹ * gM * tM = gM ^ 4 := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
      exact m11PermA_inv_conj_G)
    set g' : ↥K := e.symm gM
    set t' : ↥K := e.symm tM
    have hg' : orderOf g' = 5 := by rw [MulEquiv.orderOf_eq, hgM]
    have ht' : orderOf t' = 2 := by rw [MulEquiv.orderOf_eq, htM]
    have hc1' : t' * g' * t'⁻¹ ∈ Subgroup.zpowers g' := by
      have : t' * g' * t'⁻¹ = g' ^ 4 := by
        simp only [t', g', ← map_inv, ← map_mul, ← map_pow, hc1]
      rw [this]
      exact Subgroup.npow_mem_zpowers g' 4
    have hc2' : t'⁻¹ * g' * t' ∈ Subgroup.zpowers g' := by
      have : t'⁻¹ * g' * t' = g' ^ 4 := by
        simp only [t', g', ← map_inv, ← map_mul, ← map_pow, hc2]
      rw [this]
      exact Subgroup.npow_mem_zpowers g' 4
    have hgc : Nat.card (Subgroup.zpowers g') = 5 ^ (Nat.card ↥K).factorization 5 := by
      rw [Nat.card_zpowers, hg', hcard, h5]
    have h2N := orderOf_dvd_card_normalizer_sylow SD hgc hc1' hc2'
    rw [ht'] at h2N
    have h2Y : 2 ∣ Nat.card (X₁.subgroupOf K) := h2N.trans (Subgroup.card_dvd_of_le hSD)
    rw [hYcard] at h2Y
    norm_num at h2Y
  ·
    have h11 : (11 : ℕ) ^ (7920 : ℕ).factorization 11 = 11 :=
      (pow_eq_pow_factorization_of_eq (a := 1) (k := 720) (by norm_num) (by norm_num)
        (by norm_num)).symm
    rw [h11] at hdY
    have h99 : 99 ∣ Nat.card (X₁.subgroupOf K) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 9 11) h3Y hdY
    have hidx := index_dvd_div_of_dvd_card h99
    rw [hcard] at hidx
    have key : ∀ m ∈ Nat.divisors 80, m ≡ 1 [MOD 3] → m ≡ 1 [MOD 11] → m = 1 := by
      decide +kernel
    exact hY1 (key _ (Nat.mem_divisors.mpr ⟨hidx, by norm_num⟩) hm3 hmd)

end CFSG.LocalAnalysis.AGL81I.Section3
