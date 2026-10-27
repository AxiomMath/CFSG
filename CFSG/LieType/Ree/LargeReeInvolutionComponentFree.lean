module

public import CFSG.LieType.Ree.LargeReeInvolutionFusion
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIBasic
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ReeTag

theorem not_isComponent_of_conj {G : Type*} [Group G] [Finite G] {Γ : Subgroup G} {t r x : G}
    (ht : t ∈ Γ) (hx : x ∈ Γ) (hr : x * t * x⁻¹ = r) {N : Subgroup G}
    (hNC : N ≤ Γ ⊓ Subgroup.centralizer {r}) (hN2 : IsPGroup 2 N)
    (hnorm : ∀ g ∈ Γ ⊓ Subgroup.centralizer {r}, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hcen : ∀ g ∈ Γ ⊓ Subgroup.centralizer {r}, (∀ n ∈ N, g * n = n * g) → g ∈ N)
    (B : Subgroup (Subgroup.centralizer ({⟨t, ht⟩} : Set Γ))) : ¬ CFSG.IsComponent B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set xΓ : Γ := ⟨x, hx⟩
  set Q : Subgroup Γ := (N.comap Γ.subtype).comap (MulAut.conj xΓ).toMonoidHom with hQ
  have hmemQ : ∀ q : Γ, q ∈ Q ↔ x * q * x⁻¹ ∈ N := fun q => Iff.rfl
  have hconjC : ∀ c : Γ, c ∈ Subgroup.centralizer ({⟨t, ht⟩} : Set Γ) →
      x * c * x⁻¹ ∈ Γ ⊓ Subgroup.centralizer {r} := fun c hc => by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    have hc' : (c : G) * t = t * c := congrArg Subtype.val hc
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hx c.2) (inv_mem hx),
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← hr]
    calc x * c * x⁻¹ * (x * t * x⁻¹) = x * (c * t) * x⁻¹ := by group
      _ = x * (t * c) * x⁻¹ := by rw [hc']
      _ = x * t * x⁻¹ * (x * c * x⁻¹) := by group
  refine CFSG.ComponentClassification.OutcomeLocal.not_isComponent_of_le (p := 2) (Q := Q)
    ?_ ?_ ?_ ?_ B
  ·
    intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hn : x * q * x⁻¹ * r = r * (x * q * x⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hNC ((hmemQ q).1 hq))).2
    rw [← hr] at hn
    refine Subtype.ext ?_
    change (q : G) * t = t * q
    calc (q : G) * t = x⁻¹ * (x * q * x⁻¹ * (x * t * x⁻¹)) * x := by group
      _ = x⁻¹ * (x * t * x⁻¹ * (x * q * x⁻¹)) * x := by rw [hn]
      _ = t * q := by group
  ·
    exact (hN2.comap_of_injective Γ.subtype Γ.subtype_injective).comap_of_injective _
      (MulAut.conj xΓ).injective
  ·
    intro c hc q hq
    rw [hmemQ] at hq ⊢
    have h := hnorm _ (hconjC c hc) _ hq
    have e : x * ↑(c * q * c⁻¹) * x⁻¹ = x * c * x⁻¹ * (x * q * x⁻¹) * (x * c * x⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact h
  ·
    intro c hc hcq
    rw [hmemQ]
    refine hcen _ (hconjC c hc) fun n hn => ?_
    have hnΓ : n ∈ Γ := (Subgroup.mem_inf.1 (hNC hn)).1
    set q : Γ := ⟨x⁻¹ * n * x, mul_mem (mul_mem (inv_mem hx) hnΓ) hx⟩
    have hq : q ∈ Q := by
      rw [hmemQ]
      change x * (x⁻¹ * n * x) * x⁻¹ ∈ N
      rwa [show x * (x⁻¹ * n * x) * x⁻¹ = n by group]
    have h := congrArg Subtype.val (hcq q hq)
    change (c : G) * (x⁻¹ * n * x) = x⁻¹ * n * x * c at h
    calc x * c * x⁻¹ * n = x * (c * (x⁻¹ * n * x)) * x⁻¹ := by group
      _ = x * (x⁻¹ * n * x * c) * x⁻¹ := by rw [h]
      _ = n * (x * c * x⁻¹) := by group

theorem not_isComponentOf_conj {G : Type*} [Group G] [Finite G] {Γ : Subgroup G} {t r x : G}
    (hx : x ∈ Γ) (hr : x * t * x⁻¹ = r) {N : Subgroup G}
    (hNC : N ≤ Γ ⊓ Subgroup.centralizer {r}) (hN2 : IsPGroup 2 N)
    (hnorm : ∀ g ∈ Γ ⊓ Subgroup.centralizer {r}, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hcen : ∀ g ∈ Γ ⊓ Subgroup.centralizer {r}, (∀ n ∈ N, g * n = n * g) → g ∈ N)
    (B : Subgroup G) : ¬ CFSG.Assembly.IsComponentOf B (Γ ⊓ Subgroup.centralizer {t}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hB
  have hB' := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    hB.1).1 hB
  set Q : Subgroup G := N.comap (MulAut.conj x).toMonoidHom with hQ
  have hmemQ : ∀ q : G, q ∈ Q ↔ x * q * x⁻¹ ∈ N := fun q => Iff.rfl
  have hconjC : ∀ c ∈ Γ ⊓ Subgroup.centralizer {t}, x * c * x⁻¹ ∈
      Γ ⊓ Subgroup.centralizer {r} := fun c hc => by
    obtain ⟨hcΓ, hct⟩ := Subgroup.mem_inf.1 hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hct
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hx hcΓ) (inv_mem hx),
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← hr]
    calc x * c * x⁻¹ * (x * t * x⁻¹) = x * (c * t) * x⁻¹ := by group
      _ = x * (t * c) * x⁻¹ := by rw [hct]
      _ = x * t * x⁻¹ * (x * c * x⁻¹) := by group
  refine CFSG.ComponentClassification.OutcomeLocal.not_isComponent_of_le (p := 2)
    (C := Γ ⊓ Subgroup.centralizer {t}) (Q := Q) ?_ ?_ ?_ ?_ _ hB'
  ·
    intro q hq
    have hn := Subgroup.mem_inf.1 (hNC ((hmemQ q).1 hq))
    have hqΓ : q ∈ Γ := by
      have := mul_mem (mul_mem (inv_mem hx) hn.1) hx
      rwa [show x⁻¹ * (x * q * x⁻¹) * x = q by group] at this
    have hc := Subgroup.mem_centralizer_singleton_iff.1 hn.2
    rw [← hr] at hc
    refine Subgroup.mem_inf.2 ⟨hqΓ, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc q * t = x⁻¹ * (x * q * x⁻¹ * (x * t * x⁻¹)) * x := by group
      _ = x⁻¹ * (x * t * x⁻¹ * (x * q * x⁻¹)) * x := by rw [hc]
      _ = t * q := by group
  · exact hN2.comap_of_injective _ (MulAut.conj x).injective
  · intro c hc q hq
    rw [hmemQ] at hq ⊢
    have h := hnorm _ (hconjC c hc) _ hq
    rwa [show x * (c * q * c⁻¹) * x⁻¹ = x * c * x⁻¹ * (x * q * x⁻¹) * (x * c * x⁻¹)⁻¹ by group]
  · intro c hc hcq
    rw [hmemQ]
    refine hcen _ (hconjC c hc) fun n hn => ?_
    have hq : x⁻¹ * n * x ∈ Q := by
      rw [hmemQ, show x * (x⁻¹ * n * x) * x⁻¹ = n by group]
      exact hn
    have h := hcq _ hq
    calc x * c * x⁻¹ * n = x * (c * (x⁻¹ * n * x)) * x⁻¹ := by group
      _ = x * (x⁻¹ * n * x * c) * x⁻¹ := by rw [h]
      _ = n * (x * c * x⁻¹) := by group

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem kernel_data_of_subgroupOf {G : Type*} [Group G] {C N : Subgroup G} (hNC : N ≤ C)
    (hN : (N.subgroupOf C).Normal)
    (hcen : Subgroup.centralizer ((N.subgroupOf C : Subgroup C) : Set C) ≤ N.subgroupOf C) :
    (∀ g ∈ C, ∀ n ∈ N, g * n * g⁻¹ ∈ N) ∧ (∀ g ∈ C, (∀ n ∈ N, g * n = n * g) → g ∈ N) := by
  refine ⟨fun g hg n hn => ?_, fun g hg hgn => ?_⟩
  · have h := hN.conj_mem ⟨n, hNC hn⟩ (by rw [Subgroup.mem_subgroupOf]; exact hn) ⟨g, hg⟩
    rw [Subgroup.mem_subgroupOf] at h
    exact h
  · have h : (⟨g, hg⟩ : C) ∈ N.subgroupOf C := hcen (Subgroup.mem_centralizer_iff.2 fun n hn =>
      Subtype.ext (by
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hn
        exact (hgn n hn).symm))
    rwa [Subgroup.mem_subgroupOf] at h

theorem exists_kernel
    (ha : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) {t : ModGL F4.tag K}
    (ht : t ∈ F4.reeGamma K m) (htt : t ^ 2 = 1) (ht1 : t ≠ 1) :
    ∃ r x : ModGL F4.tag K, x ∈ F4.reeGamma K m ∧ x * t * x⁻¹ = r ∧
      ∃ N : Subgroup (ModGL F4.tag K), N ≤ F4.reeGamma K m ⊓ Subgroup.centralizer {r} ∧
        IsPGroup 2 N ∧
        (∀ g ∈ F4.reeGamma K m ⊓ Subgroup.centralizer {r}, ∀ n ∈ N, g * n * g⁻¹ ∈ N) ∧
        ∀ g ∈ F4.reeGamma K m ⊓ Subgroup.centralizer {r}, (∀ n ∈ N, g * n = n * g) → g ∈ N := by
  obtain ⟨hz, -, -, hzN, -, hzC, -, -, -, -, -, -⟩ := large_Ree_centralZ_centralizer ha hK
  obtain ⟨ht', -, -, -, -, htN, -, htC, -, -, -, -, -, -, -⟩ := large_Ree_tOne_centralizer ha hK
  rcases involution_conj_zOne_or_tOne ha hK ht htt ht1 with ⟨x, hx, hxt⟩ | ⟨x, hx, hxt⟩
  · rw [sylowH_zero_eq_centralZ] at hxt
    obtain ⟨hn, hc⟩ := kernel_data_of_subgroupOf (le_sup_left : _ ≤ centralizerZ K m) hzN hzC
    refine ⟨_, x, hx, hxt, F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩, ?_,
      (isPGroup_reeFixedPosUnipotent ha hK).to_le (reeFixedOrbitComplementUnipotent_le _),
      fun g hg => hn g (hz ▸ hg), fun g hg => hc g (hz ▸ hg)⟩
    rw [hz]
    exact le_sup_left
  · obtain ⟨hn, hc⟩ := kernel_data_of_subgroupOf (le_sup_left : _ ≤ centralizerT K m) htN htC
    refine ⟨_, x, hx, hxt, tKernel K m, ?_, tKernel_isPGroup ha hK,
      fun g hg => hn g (ht' ▸ hg), fun g hg => hc g (ht' ▸ hg)⟩
    rw [ht']
    exact le_sup_left

theorem large_Ree_involution_centralizers_component_free
    (a : ℕ) (ha : 1 ≤ a) (k : Type)
    [Field k] [Finite k] [CharP k F4.prime] (hk : Nat.card k = 2 ^ (2 * a + 1)) :
    (∀ t : F4.reeGamma k a, orderOf t = 2 →
      ∀ B : Subgroup (Subgroup.centralizer ({t} : Set (F4.reeGamma k a))),
        ¬ CFSG.IsComponent B) ∧
    ∀ t ∈ F4.reeGamma k a, orderOf t = 2 → ∀ B : Subgroup (ModGL F4.tag k),
      ¬ CFSG.Assembly.IsComponentOf B (F4.reeGamma k a ⊓ Subgroup.centralizer {t}) := by
  have := finite_modGL (τ := F4.tag) (K := k)
  have hinv : ∀ t : ModGL F4.tag k, orderOf t = 2 → t ^ 2 = 1 ∧ t ≠ 1 := by
    intro t ht
    refine ⟨by rw [← ht, pow_orderOf_eq_one], ?_⟩
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  refine ⟨fun t ht B => ?_, fun t ht ht2 B => ?_⟩
  · have ht2 : orderOf (t : ModGL F4.tag k) = 2 := by rw [Subgroup.orderOf_coe, ht]
    obtain ⟨htt, ht1⟩ := hinv _ ht2
    obtain ⟨r, x, hx, hxt, N, hNC, hN2, hn, hc⟩ := exists_kernel ha hk t.2 htt ht1
    exact not_isComponent_of_conj t.2 hx hxt hNC hN2 hn hc B
  · obtain ⟨htt, ht1⟩ := hinv _ ht2
    obtain ⟨r, x, hx, hxt, N, hNC, hN2, hn, hc⟩ := exists_kernel ha hk ht htt ht1
    exact not_isComponentOf_conj hx hxt hNC hN2 hn hc B

end CFSG.LieType.Ree.LargeReeInvolution
