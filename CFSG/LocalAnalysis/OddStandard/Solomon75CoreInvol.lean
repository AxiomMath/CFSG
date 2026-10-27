module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Basic
public import CFSG.LocalAnalysis.OddStandard.Solomon75CoreHyp
public import CFSG.LocalAnalysis.OddStandard.Solomon75GH71Sylow
public import CFSG.LocalAnalysis.OddStandard.Solomon75Consistency

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

namespace CoreAux

section Abstract

variable {M : Type} [Group M] [Finite M]

theorem odd_card_pPrimeCore (M : Type) [Group M] [Finite M] :
    Odd (Nat.card (pPrimeCore 2 M)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

omit [Finite M] in
theorem exists_conj_of_mul_inv_mem_odd {N : Subgroup M} [N.Normal] (hN : Odd (Nat.card N))
    {u v : M} (hu : orderOf u = 2) (hv : orderOf v = 2) (h : v * u⁻¹ ∈ N) :
    ∃ d ∈ N, v = d⁻¹ * u * d := by
  have htN : u ∈ Subgroup.normalizer (N : Set M) :=
    (Subgroup.normalizer_eq_top_iff.mpr inferInstance :
      Subgroup.normalizer (N : Set M) = ⊤) ▸ Subgroup.mem_top u
  have h1 := (CFSG.OddInversion.odd_inversion_coset_count hN htN
    (CFSG.OddInversion.notMem_of_odd_card hN hu) hu).1
  have h2 : v ∈ {v : M | v * u⁻¹ ∈ N ∧ orderOf v = 2} := ⟨h, hv⟩
  rw [h1] at h2
  exact h2

theorem quotient_involution_not_central {n : ℕ} {t u : M} (ht : orderOf t = 2)
    (htc : t ∈ center M) (hcov : IsDoubleCoverOfAlt (M ⧸ pPrimeCore 2 M) n) (hu : orderOf u = 2)
    (hut : u ≠ t) :
    orderOf (QuotientGroup.mk u : M ⧸ pPrimeCore 2 M) = 2 ∧
      (QuotientGroup.mk u : M ⧸ pPrimeCore 2 M) ∉ center (M ⧸ pPrimeCore 2 M) := by
  have hN := odd_card_pPrimeCore M
  have hsq : ∀ x : M, orderOf x = 2 → x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.1 (dvd_of_eq hx)
  have hu1 : (QuotientGroup.mk u : M ⧸ pPrimeCore 2 M) ≠ 1 := by
    intro h
    have := eq_one_of_mul_self_eq_one_of_mem_odd hN ((QuotientGroup.eq_one_iff u).1 h) (hsq u hu)
    rw [this, orderOf_one] at hu
    omega
  have ht1 : (QuotientGroup.mk t : M ⧸ pPrimeCore 2 M) ≠ 1 := by
    intro h
    have := eq_one_of_mul_self_eq_one_of_mem_odd hN ((QuotientGroup.eq_one_iff t).1 h) (hsq t ht)
    rw [this, orderOf_one] at ht
    omega
  refine ⟨orderOf_eq_prime ?_ hu1, ?_⟩
  · rw [pow_two, ← QuotientGroup.mk_mul, hsq u hu]
    rfl
  · intro hcen
    have htcen : (QuotientGroup.mk t : M ⧸ pPrimeCore 2 M) ∈ center (M ⧸ pPrimeCore 2 M) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp htc g₀]
    have heq : (QuotientGroup.mk u : M ⧸ pPrimeCore 2 M) = QuotientGroup.mk t := by
      have hcard := hcov.2.1
      rw [Nat.card_eq_two_iff' (1 : ↥(center (M ⧸ pPrimeCore 2 M)))] at hcard
      obtain ⟨y, -, hy⟩ := hcard
      have e1 := hy ⟨_, hcen⟩ (fun h => hu1 (congrArg Subtype.val h))
      have e2 := hy ⟨_, htcen⟩ (fun h => ht1 (congrArg Subtype.val h))
      exact congrArg Subtype.val (e1.trans e2.symm)
    have hmem : u⁻¹ * t ∈ pPrimeCore 2 M := QuotientGroup.eq.mp heq
    have hmem' : t * u⁻¹ ∈ pPrimeCore 2 M := by
      have := (inferInstance : (pPrimeCore 2 M).Normal).conj_mem _ hmem u
      simpa [mul_assoc] using this
    obtain ⟨d, -, hd⟩ := exists_conj_of_mul_inv_mem_odd hN hu ht hmem'
    apply hut
    calc u = d * (d⁻¹ * u * d) * d⁻¹ := by group
      _ = d * t * d⁻¹ := by rw [← hd]
      _ = t := by
        rw [Subgroup.mem_center_iff.mp htc d]
        group

theorem isConj_of_ne_central {n : ℕ} {t u v : M} (ht : orderOf t = 2) (htc : t ∈ center M)
    (hcov : IsDoubleCoverOfAlt (M ⧸ pPrimeCore 2 M) n)
    (hone : ∀ a b : M ⧸ pPrimeCore 2 M, orderOf a = 2 → orderOf b = 2 →
      a ∉ center (M ⧸ pPrimeCore 2 M) → b ∉ center (M ⧸ pPrimeCore 2 M) → IsConj a b)
    (hu : orderOf u = 2) (hut : u ≠ t) (hv : orderOf v = 2) (hvt : v ≠ t) :
    ∃ m : M, m * u * m⁻¹ = v := by
  obtain ⟨hu2, huc⟩ := quotient_involution_not_central ht htc hcov hu hut
  obtain ⟨hv2, hvc⟩ := quotient_involution_not_central ht htc hcov hv hvt
  obtain ⟨c, hc⟩ := isConj_iff.mp (hone _ _ hu2 hv2 huc hvc)
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective c
  have hmem : (m * u * m⁻¹)⁻¹ * v ∈ pPrimeCore 2 M := by
    apply QuotientGroup.eq.mp
    rw [← hc]
    simp
  have hord : orderOf (m * u * m⁻¹) = 2 := by
    rw [← hu]
    exact (orderOf_injective (MulAut.conj m).toMonoidHom (MulAut.conj m).injective u)
  have hmem' : v * (m * u * m⁻¹)⁻¹ ∈ pPrimeCore 2 M := by
    have := (inferInstance : (pPrimeCore 2 M).Normal).conj_mem _ hmem (m * u * m⁻¹)
    simpa [mul_assoc] using this
  obtain ⟨d, -, hd⟩ := exists_conj_of_mul_inv_mem_odd (odd_card_pPrimeCore M) hord hv hmem'
  refine ⟨d⁻¹ * m, ?_⟩
  rw [hd]
  group

end Abstract

section Sylow

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_center_cen_self (t : G) :
    (⟨t, self_mem_centralizer t⟩ : ↥(centralizer ({t} : Set G))) ∈
      center ↥(centralizer ({t} : Set G)) := by
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (mem_centralizer_singleton_iff.1 y.2)

theorem exists_sylow_central {t : G} (ht : orderOf t = 2) {n : ℕ} (hn : 8 ≤ n)
    (hcov : IsDoubleCoverOfAlt (CentQuot t) n) :
    ∃ P : Sylow 2 G, t ∈ (P : Subgroup G) ∧ (P : Subgroup G) ≤ cen t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥(centralizer ({t} : Set G))) := Sylow.nonempty
  obtain ⟨P, hP⟩ := exists_sylow_eq_map_of_centralizer_cover ht hn hcov T
  have ht₀p : IsPGroup 2 (zpowers (⟨t, self_mem_centralizer t⟩ :
      ↥(centralizer ({t} : Set G)))) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht, pow_one])
  have : (zpowers (⟨t, self_mem_centralizer t⟩ : ↥(centralizer ({t} : Set G)))).Normal :=
    normal_of_le_center (zpowers_le.2 (mem_center_cen_self t))
  have ht₀T := ht₀p.le_sylow_of_normal T (mem_zpowers _)
  refine ⟨P, ?_, ?_⟩
  · rw [hP]
    exact ⟨_, ht₀T, rfl⟩
  · rw [hP]
    rintro _ ⟨x, -, rfl⟩
    exact x.2

omit [Finite G] in
theorem orderOf_conj_eq' (g u : G) : orderOf (g * u * g⁻¹) = orderOf u := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective u
  simpa [MulAut.conj_apply] using this

theorem exists_conj_mem_sylow' {z : G} (hz : orderOf z = 2) (S : Sylow 2 G) :
    ∃ g : G, g⁻¹ * z * g ∈ (S : Subgroup G) := by
  have hz2 : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  obtain ⟨P, hP⟩ := hz2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  refine ⟨g, ?_⟩
  have hzP : z ∈ (P : Subgroup G) := hP (Subgroup.mem_zpowers z)
  rw [← hg] at hzP
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hzP
  simpa [MulAut.conj_apply, mul_assoc] using hzP

end Sylow

section ZStar

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

omit [Finite G] in
theorem center_eq_bot_of_nonabelian (hnonab : ∃ a b : G, a * b ≠ b * a) : center G = ⊥ := by
  rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    apply hab
    have : a ∈ center G := h ▸ mem_top a
    exact (mem_center_iff.1 this b).symm

theorem exists_noncentral_sylow_conj (hnonab : ∃ a b : G, a * b ≠ b * a) {t : G}
    (ht : orderOf t = 2) (P : Sylow 2 G) (htP : t ∈ (P : Subgroup G))
    (hPC : (P : Subgroup G) ≤ cen t) :
    ∃ g : G, g⁻¹ * t * g ∈ (P : Subgroup G) ∧ g⁻¹ * t * g ≠ t := by
  by_contra hcon
  push Not at hcon
  have hzZ : (⟨t, htP⟩ : ↥(P : Subgroup G)) ∈ center ↥(P : Subgroup G) := by
    rw [Subgroup.mem_center_iff]
    intro s
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hPC s.2))
  obtain ⟨hfac, -⟩ := CFSG.Milestones.glauberman_zStar_central_sylow_involution P ⟨t, htP⟩ hzZ
    (by rw [Subgroup.orderOf_mk]; exact ht) hcon
  have hodd : oddCore G = ⊥ := by
    rcases (inferInstance : (oddCore G).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact absurd (h ▸ mem_top t) (CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two ht)
  have htcen : t ∈ center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨c, hc, k, hk, rfl⟩ := hfac g
    rw [hodd, Subgroup.mem_bot] at hk
    subst hk
    rw [mul_one]
    exact mem_centralizer_singleton_iff.1 hc
  rw [center_eq_bot_of_nonabelian hnonab, Subgroup.mem_bot] at htcen
  rw [htcen, orderOf_one] at ht
  omega

end ZStar

section Conj

variable {G : Type} [Group G]

theorem cen_conj (g t : G) :
    cen (g * t * g⁻¹) = (cen t).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply]; group⟩
    rw [mem_centralizer_singleton_iff] at hx ⊢
    have h := hx
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [h]
      _ = t * (g⁻¹ * x * g) := by group
  · rintro ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff] at hy ⊢
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * y * g⁻¹ * (g * t * g⁻¹) = g * (y * t) * g⁻¹ := by group
      _ = g * (t * y) * g⁻¹ := by rw [hy]
      _ = g * t * g⁻¹ * (g * y * g⁻¹) := by group

end Conj

section ConjCover

variable {G : Type} [Group G]

theorem isDoubleCoverOfAlt_centQuot_conj {t : G} {n : ℕ} (g : G)
    (hcov : IsDoubleCoverOfAlt (CentQuot t) n) :
    IsDoubleCoverOfAlt (CentQuot (g * t * g⁻¹)) n := by
  have h : (cen t).map (MulAut.conj g).toMonoidHom = cen (g * t * g⁻¹) := (cen_conj g t).symm
  let e₁ : ↥(cen t) ≃* ↥(cen (g * t * g⁻¹)) :=
    (MulEquiv.subgroupMap (MulAut.conj g) (cen t)).trans (MulEquiv.subgroupCongr h)
  have h2 : (pPrimeCore 2 ↥(cen t)).map e₁.toMonoidHom = pPrimeCore 2 ↥(cen (g * t * g⁻¹)) :=
    pPrimeCore_map_iso 2 e₁
  exact CFSG.GH74.GLS.Stage12.McLRec.isDoubleCoverOfAlt_congr
    (QuotientGroup.congr (pPrimeCore 2 ↥(cen t)) (pPrimeCore 2 ↥(cen (g * t * g⁻¹))) e₁ h2) hcov

end ConjCover

section OneClass

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_in_cen {t : G} (ht : orderOf t = 2) {n : ℕ}
    (hcov : IsDoubleCoverOfAlt (CentQuot t) n)
    (hone : ∀ a b : CentQuot t, orderOf a = 2 → orderOf b = 2 → a ∉ center (CentQuot t) →
      b ∉ center (CentQuot t) → IsConj a b)
    {u v : G} (hu : u ∈ cen t) (hv : v ∈ cen t) (hu2 : orderOf u = 2) (hv2 : orderOf v = 2)
    (hut : u ≠ t) (hvt : v ≠ t) : ∃ m : G, m ∈ cen t ∧ m * u * m⁻¹ = v := by
  obtain ⟨m, hm⟩ := isConj_of_ne_central (M := ↥(cen t)) (t := ⟨t, self_mem_centralizer t⟩)
    (u := ⟨u, hu⟩) (v := ⟨v, hv⟩) (by rw [Subgroup.orderOf_mk]; exact ht)
    (mem_center_cen_self t) hcov hone (by rw [Subgroup.orderOf_mk]; exact hu2)
    (fun h => hut (congrArg Subtype.val h)) (by rw [Subgroup.orderOf_mk]; exact hv2)
    (fun h => hvt (congrArg Subtype.val h))
  exact ⟨m, m.2, congrArg Subtype.val hm⟩

end OneClass

end CoreAux

open CoreAux

section OneClass

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem exists_conj_of_involution (hnonab : ∃ a b : G, a * b ≠ b * a) {t : G}
    (ht : orderOf t = 2) {n : ℕ} (hn : 8 ≤ n) (hcov : IsDoubleCoverOfAlt (CentQuot t) n)
    (hB : AlternatingBalanceData n) :
    ∀ u : G, orderOf u = 2 → ∃ g : G, u = g * t * g⁻¹ := by
  intro u hu
  obtain ⟨P, htP, hPC⟩ := exists_sylow_central ht hn hcov
  obtain ⟨g₁, hg₁⟩ := exists_conj_mem_sylow' hu P
  set u' := g₁⁻¹ * u * g₁ with hu'
  have hu'2 : orderOf u' = 2 := by
    rw [hu', ← hu]
    simpa using orderOf_conj_eq' g₁⁻¹ u
  by_cases hut : u' = t
  · exact ⟨g₁, by rw [← hut, hu']; group⟩
  · obtain ⟨g, hg, hgt⟩ := exists_noncentral_sylow_conj hnonab ht P htP hPC
    set s := g⁻¹ * t * g with hs
    have hs2 : orderOf s = 2 := by
      rw [hs, ← ht]
      simpa using orderOf_conj_eq' g⁻¹ t
    obtain ⟨m, hm, hmu⟩ := exists_conj_in_cen ht hcov (hB.one_class (CentQuot t) hcov)
      (hPC hg₁) (hPC hg) hu'2 hs2 hut hgt
    refine ⟨g₁ * m⁻¹ * g⁻¹, ?_⟩
    have h1 : u' = m⁻¹ * s * m := by
      rw [← hmu]
      group
    calc u = g₁ * u' * g₁⁻¹ := by rw [hu']; group
      _ = g₁ * (m⁻¹ * (g⁻¹ * t * g) * m) * g₁⁻¹ := by rw [h1, hs]
      _ = g₁ * m⁻¹ * g⁻¹ * t * (g₁ * m⁻¹ * g⁻¹)⁻¹ := by group

theorem one_class (hnonab : ∃ a b : G, a * b ≠ b * a) {t : G} (ht : orderOf t = 2) {n : ℕ}
    (hn : 8 ≤ n) (hcov : IsDoubleCoverOfAlt (CentQuot t) n) (hB : AlternatingBalanceData n) :
    ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v := by
  intro u v hu hv
  obtain ⟨a, rfl⟩ := exists_conj_of_involution hnonab ht hn hcov hB u hu
  obtain ⟨b, rfl⟩ := exists_conj_of_involution hnonab ht hn hcov hB v hv
  rw [isConj_iff]
  exact ⟨b * a⁻¹, by group⟩

end OneClass

end CFSG.OddStandard.Solomon75
