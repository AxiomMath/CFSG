module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmcFusion

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools CFSG.GH74.Uniqueness.Bender

namespace U3C1OuterSwapHigh

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G} {w s : G} {P : Subgroup G}
  (hW : U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P)
include hW

theorem gmc_K_facts :
    IsSimpleGroup ↥(L ⊓ centralizer ({w} : Set G)) ∧
      (∃ a b : ↥(L ⊓ centralizer ({w} : Set G)), a * b ≠ b * a) ∧
      BenderType ↥(L ⊓ centralizer ({w} : Set G)) f 1 1 ∧
      szA₁ (szT₁ L T) ≤ L ⊓ centralizer ({w} : Set G) ∧
      ∀ c ∈ centralizer ({w} : Set G) ⊓ centralizer ({t} : Set G),
        ∀ y ∈ L ⊓ centralizer ({w} : Set G), c * y * c⁻¹ ∈ L ⊓ centralizer ({w} : Set G) := by
  have h := hW.step.start
  have hS2 := hW.step.card_sylow
  have hw1 : w ≠ 1 := fun h1 => hW.w_not_mem (by rw [h1]; exact one_mem _)
  have hwo : orderOf w = 2 := orderOf_eq_prime hW.w_sq hw1
  obtain ⟨hwout, hwA₁, -, -⟩ := h.outer_facts_of_card_sylow hS2 hW.w_mem hW.w_sq hW.w_not_mem
  obtain ⟨⟨eL⟩, hs, hnab, -, -, hKN, -, -⟩ :=
    u3Star_local h.setting h.two_le h.model hS2 h.inv h.mem hwo (h.le_normalizer hW.w_mem) hwout
  refine ⟨hs, hnab, BenderType.linear f h.two_le eL, fun a ha => ?_, hKN⟩
  exact mem_inf.mpr ⟨szT₁_le_right L T (szA₁_le _ ha),
    mem_centralizer_singleton_iff.mpr (hwA₁ a ha).symm⟩

theorem gmc_conj_K {x : G} (hxS₂ : x ∈ swapS₂ P U T) (hx2 : x ^ 2 = 1)
    (hxt : x * t * x⁻¹ = w) {y : G} (hy : y ∈ L ⊓ centralizer ({w} : Set G)) :
    x * y * x⁻¹ ∈ L ⊓ centralizer ({w} : Set G) := by
  obtain ⟨hs, -, -, hA₁K, hKN⟩ := hW.gmc_K_facts
  obtain ⟨-, hA₁card, -, -, -, -, -⟩ := hW.step.start.facts_of_card_sylow hW.step.card_sylow
  set K := L ⊓ centralizer ({w} : Set G) with hKdef
  have hxx : x * x = 1 := by rw [← sq]; exact hx2
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hxw : x * w * x⁻¹ = t := by
    rw [← hxt, show x * (x * t * x⁻¹) * x⁻¹ = (x * x) * t * (x * x)⁻¹ by group, hxx]
    group
  have hx't : x⁻¹ * t * x = w := by
    have e := hxt
    rw [hxinv] at e ⊢
    exact e
  have hx'w : x⁻¹ * w * x = t := by
    have e := hxw
    rw [hxinv] at e ⊢
    exact e
  have hKt : ∀ k ∈ K, k * t = t * k := fun k hk =>
    mem_centralizer_iff.mp hW.step.start.mem k (mem_inf.mp hk).1
  have hKw : ∀ k ∈ K, k * w = w * k := fun k hk =>
    mem_centralizer_singleton_iff.mp (mem_inf.mp hk).2
  set M : Subgroup G := K.map (MulAut.conj x).toMonoidHom with hMdef
  have hMmem : ∀ z ∈ K, x * z * x⁻¹ ∈ M := fun z hz => ⟨z, hz, by simp⟩
  have hMK : ∀ k ∈ K, ∀ m ∈ M, k * m * k⁻¹ ∈ M := by
    rintro k hk _ ⟨y', hy', rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hcw : x⁻¹ * k * x ∈ centralizer ({w} : Set G) ⊓ centralizer ({t} : Set G) := by
      refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_,
        mem_centralizer_singleton_iff.mpr ?_⟩
      · calc x⁻¹ * k * x * w = x⁻¹ * k * (x * w * x⁻¹) * x := by group
          _ = x⁻¹ * (k * t) * x := by rw [hxw]; group
          _ = x⁻¹ * (t * k) * x := by rw [hKt k hk]
          _ = (x⁻¹ * t * x) * (x⁻¹ * k * x) := by group
          _ = w * (x⁻¹ * k * x) := by rw [hx't]
      · calc x⁻¹ * k * x * t = x⁻¹ * k * (x * t * x⁻¹) * x := by group
          _ = x⁻¹ * (k * w) * x := by rw [hxt]; group
          _ = x⁻¹ * (w * k) * x := by rw [hKw k hk]
          _ = (x⁻¹ * w * x) * (x⁻¹ * k * x) := by group
          _ = t * (x⁻¹ * k * x) := by rw [hx'w]
    have h1 := hKN _ hcw y' hy'
    rw [show k * (x * y' * x⁻¹) * k⁻¹ =
      x * ((x⁻¹ * k * x) * y' * (x⁻¹ * k * x)⁻¹) * x⁻¹ by group]
    exact hMmem _ h1
  set N : Subgroup K := M.subgroupOf K with hNdef
  have hNn : N.Normal := ⟨fun n hn k => by
    rw [hNdef, mem_subgroupOf] at hn ⊢
    simp only [coe_mul, coe_inv]
    exact hMK k k.2 n hn⟩
  have := hs
  have := hNn
  have hKM : K ≤ M := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
    · exfalso
      obtain ⟨a, ha, ha1⟩ : ∃ a ∈ szA₁ (szT₁ L T), a ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have hbot' : szA₁ (szT₁ L T) = ⊥ := (eq_bot_iff_forall _).mpr hcon
        rw [hbot', card_bot] at hA₁card
        have : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := hW.step.start.two_le; omega)
        omega
      have haM : a ∈ M := by
        have h1 := hW.conj_szA₁_of_mem (inv_mem hxS₂) ha
        rw [inv_inv] at h1
        have h2 := hMmem _ (hA₁K h1)
        rwa [show x * (x⁻¹ * a * x) * x⁻¹ = a by group] at h2
      have haN : (⟨a, hA₁K ha⟩ : K) ∈ N := by
        rw [hNdef, mem_subgroupOf]
        exact haM
      rw [hbot, mem_bot] at haN
      exact ha1 (congrArg Subtype.val haN)
    · intro z hz
      have hzN : (⟨z, hz⟩ : K) ∈ N := by rw [htop]; exact mem_top _
      rw [hNdef, mem_subgroupOf] at hzN
      exact hzN
  have hMcard : Nat.card M = Nat.card K := card_map_of_injective (MulAut.conj x).injective
  have hKMeq : K = M := eq_of_le_of_card_ge hKM (by rw [hMcard])
  rw [hKMeq]
  exact hMmem y hy

theorem gmc_comm_szA₁_of_inner {x : G} (hxS₂ : x ∈ swapS₂ P U T) (hx2 : x ^ 2 = 1)
    {k : G} (hk : k ∈ L ⊓ centralizer ({w} : Set G))
    (hxk : ∀ y ∈ L ⊓ centralizer ({w} : Set G), x * y * x⁻¹ = k * y * k⁻¹)
    {a : G} (ha : a ∈ szA₁ (szT₁ L T)) : a * x = x * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hs, hnab, hB, hA₁K, -⟩ := hW.gmc_K_facts
  obtain ⟨-, hA₁card, -, -, -, -, -⟩ := hW.step.start.facts_of_card_sylow hW.step.card_sylow
  set K := L ⊓ centralizer ({w} : Set G) with hKdef
  have hxx : x * x = 1 := by rw [← sq]; exact hx2
  have hk2 : k * k = 1 := by
    have hZ := center_eq_bot_of_simple_nonabelian hs hnab
    have hmem : (⟨k * k, mul_mem hk hk⟩ : K) ∈ center K := by
      rw [mem_center_iff]
      intro y
      apply Subtype.ext
      simp only [coe_mul]
      have h1 := hxk y y.2
      have hyK : x * (y : G) * x⁻¹ ∈ K := by
        rw [h1]
        exact mul_mem (mul_mem hk y.2) (inv_mem hk)
      have h2 := hxk _ hyK
      have e2 : (k * k) * (y : G) * (k * k)⁻¹ = y := by
        calc (k * k) * (y : G) * (k * k)⁻¹ = k * (k * y * k⁻¹) * k⁻¹ := by group
          _ = k * (x * y * x⁻¹) * k⁻¹ := by rw [h1]
          _ = x * (x * y * x⁻¹) * x⁻¹ := h2.symm
          _ = (x * x) * y * (x * x)⁻¹ := by group
          _ = y := by rw [hxx]; group
      calc (y : G) * (k * k) = (k * k) * y * (k * k)⁻¹ * (k * k) := by rw [e2]
        _ = (k * k) * y := by group
    rw [hZ, mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hkinv : k⁻¹ = k := inv_eq_of_mul_eq_one_right hk2
  have hkA : ∀ b ∈ szA₁ (szT₁ L T), k * b * k⁻¹ ∈ szA₁ (szT₁ L T) := by
    intro b hb
    rw [← hxk b (hA₁K hb)]
    exact hW.conj_szA₁_of_mem hxS₂ hb
  have hkA₁ : k ∈ szA₁ (szT₁ L T) := by
    by_contra hkA₁
    have hkN : k ∈ normalizer (szA₁ (szT₁ L T) : Set G) :=
      mem_normalizer_of_forall_inv_mul_mul_mem fun b hb => by
        rw [hkinv]
        have h1 := hkA b hb
        rwa [hkinv] at h1
    have h2 := RankOne.Endings.relIndex_sup_zpowers_eq_two hkA₁ hkN hk2
    have h3 := relIndex_mul_card (H := szA₁ (szT₁ L T)) (K := szA₁ (szT₁ L T) ⊔ zpowers k)
    rw [h2, inf_of_le_left le_sup_left, hA₁card] at h3
    have hXK : szA₁ (szT₁ L T) ⊔ zpowers k ≤ K := sup_le hA₁K (zpowers_le.mpr hk)
    have hXc : Nat.card ((szA₁ (szT₁ L T) ⊔ zpowers k).subgroupOf K) = 2 ^ (f + 1) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hXK).toEquiv, ← h3]
      ring
    have hXp : IsPGroup 2 ((szA₁ (szT₁ L T) ⊔ zpowers k).subgroupOf K) := IsPGroup.of_card hXc
    obtain ⟨Q, hQ⟩ := hXp.exists_le_sylow
    obtain ⟨t₀, hc⟩ := hB.exists_benderCore Q
    have h4 := Subgroup.card_le_of_le hQ
    rw [hXc, hc.card_eq, pow_one] at h4
    have h5 : 2 ^ f < 2 ^ (f + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hka : k * a = a * k := mem_centralizer_iff.mp (mem_szA₁.mp ha).2 k (szA₁_le _ hkA₁)
  have e2 : x * a * x⁻¹ = a := by
    rw [hxk a (hA₁K ha), hka]
    group
  calc a * x = x * a * x⁻¹ * x := by rw [e2]
    _ = x * a := by group

end U3C1OuterSwapHigh

@[expose] def U3C1GmcInnerInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V U U₁ : Subgroup G) (w s : G) (P : Subgroup G),
    U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P → (∀ u ∈ U₁, s * u * s⁻¹ ∈ U₁) →
      (∃ S : Sylow 2 G, (S : Subgroup G) = swapS₂ P U T) →
        ∀ g : G, g * t * g⁻¹ ∈ swapS₂ P U T → g * t * g⁻¹ ∉ U ⊔ T →
          (g * t * g⁻¹) * t * (g * t * g⁻¹)⁻¹ = w →
            ∃ k ∈ L ⊓ centralizer ({w} : Set G), ∀ y ∈ L ⊓ centralizer ({w} : Set G),
              (g * t * g⁻¹) * y * (g * t * g⁻¹)⁻¹ = k * y * k⁻¹

theorem u3C1GmcCentInput_of_inner (hI : U3C1GmcInnerInput) :
    U3C1GmcCentInput := by
  intro G _ _ L f t T R₂ D d V U U₁ w s P hW h1 h2 g hg hgS a ha
  have hS := hW.step
  have hL := hW.level
  obtain ⟨c₁, hc₁T, hc₁⟩ := hL.norm_exists_conj hS hW.mu hW.w_mem hW.w_sq hW.w_not_mem
    hW.w_cent hW.isPGroup hW.le (mem_swapS₂.mp hg).2 (mem_swapS₂.mp hg).1 hgS
  have hc₁SU : c₁ ∈ U ⊔ T := mem_sup_left (hL.U₁_le (hW.T₁_le_U₁ hc₁T))
  have hc₁S : c₁ ∈ swapS₂ P U T := hW.le_S₂ hc₁SU
  have hx'eq : c₁ * (g * t * g⁻¹) * c₁⁻¹ = (c₁ * g) * t * (c₁ * g)⁻¹ := by group
  have hx'S₂ : (c₁ * g) * t * (c₁ * g)⁻¹ ∈ swapS₂ P U T := by
    rw [← hx'eq]
    exact mul_mem (mul_mem hc₁S hg) (inv_mem hc₁S)
  have hx'S : (c₁ * g) * t * (c₁ * g)⁻¹ ∉ U ⊔ T := by
    rw [← hx'eq]
    intro h'
    apply hgS
    rw [show g * t * g⁻¹ = c₁⁻¹ * (c₁ * (g * t * g⁻¹) * c₁⁻¹) * c₁ by group]
    exact mul_mem (mul_mem (inv_mem hc₁SU) h') hc₁SU
  have hc₁t : c₁ * t = t * c₁ := mem_centralizer_iff.mp hS.start.mem_centralizer_szT₁ c₁ hc₁T
  have hx't : ((c₁ * g) * t * (c₁ * g)⁻¹) * t * ((c₁ * g) * t * (c₁ * g)⁻¹)⁻¹ = w := by
    rw [← hx'eq, ← hc₁]
    have e : c₁⁻¹ * t * c₁ = t := by
      rw [mul_assoc, ← hc₁t, ← mul_assoc, inv_mul_cancel, one_mul]
    calc c₁ * (g * t * g⁻¹) * c₁⁻¹ * t * (c₁ * (g * t * g⁻¹) * c₁⁻¹)⁻¹ =
          c₁ * (g * t * g⁻¹) * (c₁⁻¹ * t * c₁) * (g * t * g⁻¹)⁻¹ * c₁⁻¹ := by group
      _ = c₁ * ((g * t * g⁻¹) * t * (g * t * g⁻¹)⁻¹) * c₁⁻¹ := by rw [e]; group
  obtain ⟨k, hk, hxk⟩ := hI G L f t T R₂ D d V U U₁ w s P hW h1 h2 (c₁ * g) hx'S₂ hx'S hx't
  have hx'2 : ((c₁ * g) * t * (c₁ * g)⁻¹) ^ 2 = 1 := by
    rw [show ((c₁ * g) * t * (c₁ * g)⁻¹) ^ 2 = (c₁ * g) * t ^ 2 * (c₁ * g)⁻¹ by
      rw [sq, sq]; group, hS.start.sq_eq_one]
    group
  have hcomm := hW.gmc_comm_szA₁_of_inner hx'S₂ hx'2 hk hxk ha
  rw [← hx'eq] at hcomm
  have hac₁ : a * c₁ = c₁ * a := (mem_centralizer_iff.mp (mem_szA₁.mp ha).2 c₁ hc₁T).symm
  have e1 : c₁⁻¹ * a * c₁ = a := by rw [mul_assoc, hac₁, ← mul_assoc, inv_mul_cancel, one_mul]
  calc a * (g * t * g⁻¹) = (c₁⁻¹ * a * c₁) * (g * t * g⁻¹) := by rw [e1]
    _ = c₁⁻¹ * (a * (c₁ * (g * t * g⁻¹) * c₁⁻¹)) * c₁ := by group
    _ = c₁⁻¹ * ((c₁ * (g * t * g⁻¹) * c₁⁻¹) * a) * c₁ := by rw [hcomm]
    _ = (g * t * g⁻¹) * (c₁⁻¹ * a * c₁) := by group
    _ = (g * t * g⁻¹) * a := by rw [e1]

theorem u3C1GmsFusionInput_of_inner (hI : U3C1GmcInnerInput) :
    U3C1GmsFusionInput :=
  u3C1GmsFusionInput_of_cent (u3C1GmcCentInput_of_inner hI)

end CFSG.SeitzReduction.RankOne
