module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYTwentyTwo

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section Defs

variable
  {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def yamadaC₃ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaR₃ d t ⊓ yamadaCstar d t

@[expose] noncomputable def yamadaE₃ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaL₃ d t ⊓ yamadaC₃ d t

@[expose] noncomputable def yamadaV₃ (d : G2Data L K) (t : G) : Subgroup G :=
  (yamadaR₃ d t ⊓ centralizer (d.J₂ : Set G)) ⊔ yamadaV₂ d t

@[expose] noncomputable def yamadaW₃ (d : G2Data L K) (t : G) : Subgroup G :=
  ⁅yamadaV₃ d t, d.J⁆

@[expose] noncomputable def yamadaF₃ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaW₃ d t ⊔ yamadaF₂ d t

@[expose] noncomputable def yamadaM₃ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaW₃ d t ⊔ yamadaM₂ d t

@[expose] noncomputable def yamadaS₃ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaW₃ d t ⊔ yamadaS₂ d t

@[expose] noncomputable def yamadaD₃ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaS₃ d t ⊓ yamadaC₃ d t

end Defs

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Light

theorem card_sup_zpowers (h : Setup G L f t) {A : Subgroup G} (htA : t ∈ normalizer (A : Set G))
    (htA' : t ∉ A) : Nat.card (A ⊔ zpowers t : Subgroup G) = 2 * Nat.card A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt := h.t_mul_t
  have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, htt]
  have h1 := Common.card_sup_mul_card_inf_eq (A := A) (B := zpowers t) ((zpowers_le).2 htA)
  have hinf : A ⊓ zpowers t = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxA, hxt⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hxt
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · rw [Subgroup.mem_bot, ← two_mul, zpow_mul, ht2, one_zpow]
    · exfalso
      refine htA' ?_
      rwa [zpow_add, zpow_mul, ht2, one_zpow, one_mul, zpow_one] at hxA
  have h2 : Nat.card (zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [sq, htt]) h.t_ne_one
  rw [hinf, Subgroup.card_bot, mul_one, h2] at h1
  rw [h1, mul_comm]

end Light

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem D_inf_yamadaY₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.D ⊓ yamadaY₂ d t = d.Y := by
  obtain ⟨-, hYX, -, hXF, -, hFD, -⟩ := d.inclusions
  refine le_antisymm ?_ (le_inf (hYX.trans (hXF.trans hFD)) (h.Y_le_yamadaY₂ d hK hD))
  rw [← h.yamadaY₂_inf_centralizer d hK hD, inf_comm]
  exact inf_le_inf_left _ ((d.image_le _).trans h.L_le_centralizer)

theorem card_yamadaD₂_F₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    Nat.card (yamadaD₂ d t) = Nat.card K ^ 7 ∧ Nat.card (yamadaF₂ d t) = Nat.card K ^ 6 := by
  obtain ⟨-, -, -, -, -, hFD, -, hDS, -⟩ := d.inclusions
  have hSY₂ := (h.yamada_5_13_3 d hK hD).1
  have hq : 0 < Nat.card K ^ 2 := by
    have : 0 < Nat.card K := Nat.card_pos
    positivity
  have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaY₂ d t) (B := d.D) (hDS.trans hSY₂)
  rw [inf_comm, h.D_inf_yamadaY₂ d hK hD, h.card_yamadaY₂ d hK hD, d.cards.2.2.2.2.2.1,
    d.cards.2.1] at h1
  have h2 := Common.card_sup_mul_card_inf_eq (A := yamadaY₂ d t) (B := d.F)
    ((hFD.trans hDS).trans hSY₂)
  rw [inf_comm, h.F_inf_yamadaY₂ d hK hD, h.card_yamadaY₂ d hK hD, d.cards.2.2.2.2.1,
    d.cards.2.1] at h2
  refine ⟨Nat.eq_of_mul_eq_mul_right hq ?_, Nat.eq_of_mul_eq_mul_right hq ?_⟩
  · rw [yamadaD₂, sup_comm, h1]
    ring
  · rw [yamadaF₂, sup_comm, h2]
    ring

theorem t_mem_normalizer_yamadaD₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : t ∈ normalizer (yamadaD₂ d t : Set G) ∧ t ∉ yamadaD₂ d t := by
  obtain ⟨-, hYX, -, hXF, -, hFD, -, hDS, -⟩ := d.inclusions
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  refine ⟨mem_normalizer_sup (mem_normalizer_of_conj_mem fun x hx => ?_)
    (h.yamadaL₂_le_normalizer_yamadaY₂ d hK hD htL₂), fun ht => ?_⟩
  · rw [← mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hx)),
      mul_inv_cancel_right]
    exact hx
  · obtain ⟨x, hx, y, hy, e⟩ := Common.exists_mul_of_le_normalizer' (A := d.D)
      (B := yamadaY₂ d t) (hDS.trans (h.yamada_5_13_3 d hK hD).1) t ht
    have hxt : x * t = t * x :=
      mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hx))
    have hxt' : x⁻¹ * t = t * x⁻¹ := by
      calc x⁻¹ * t = x⁻¹ * (t * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * t) * x⁻¹ := by rw [hxt]
        _ = t * x⁻¹ := by group
    have hyt : y ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have hy' : y = x⁻¹ * t := by
        rw [e]
        group
      rw [hy', mul_assoc, h.t_mul_t, mul_one, hxt', ← mul_assoc, h.t_mul_t, one_mul]
    have hyY : y ∈ d.Y := by
      rw [← h.yamadaY₂_inf_centralizer d hK hD]
      exact Subgroup.mem_inf.2 ⟨hy, hyt⟩
    have : t ∈ d.D := by
      rw [e]
      exact mul_mem hx (hYX.trans (hXF.trans hFD) hyY)
    exact h.t_not_mem_L (d.image_le _ this)

theorem card_yamadaC₂_E₂_V₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    Nat.card (yamadaC₂ d t) = 2 * Nat.card K ^ 7 ∧ Nat.card (yamadaE₂ d t) = 2 * Nat.card K ^ 6 ∧
      Nat.card (yamadaV₂ d t) = 2 * Nat.card K ^ 5 := by
  obtain ⟨hD₂, hF₂⟩ := h.card_yamadaD₂_F₂ d hK hD
  obtain ⟨htD, htD'⟩ := h.t_mem_normalizer_yamadaD₂ d hK hD
  obtain ⟨htF, htF'⟩ := h.t_mem_normalizer_yamadaF₂ d hK hD
  obtain ⟨htW, htW'⟩ := h.t_mem_normalizer_yamadaW₂ d hK hD
  exact ⟨by rw [yamadaC₂, h.card_sup_zpowers htD htD', hD₂],
    by rw [yamadaE₂, h.card_sup_zpowers htF htF', hF₂],
    by rw [yamadaV₂, h.card_sup_zpowers htW htW', h.card_yamadaW₂ d hK hD]⟩

theorem yamadaL₂_inf_S (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    yamadaL₂ d t ⊓ d.S = d.M := by
  obtain ⟨-, hL₂t, -, -⟩ := h.two_core_L₂ d hK
  refine le_antisymm (fun x hx => ?_) (le_inf (le_sup_left.trans (h.tM_le_yamadaL₂ d hK))
    d.inclusions.2.2.2.2.2.2.2.2.1)
  obtain ⟨hxL₂, hxS⟩ := Subgroup.mem_inf.1 hx
  have hxL : x ∈ L := d.image_le _ hxS
  have hxMt : x ∈ d.M ⊔ zpowers t := by
    rw [← hL₂t]
    exact Subgroup.mem_inf.2 ⟨hxL₂, h.L_le_centralizer hxL⟩
  rcases (h.mem_sup_zpowers_iff (d.image_le _)).1 hxMt with h1 | h1
  · exact h1
  · exfalso
    have := mul_mem (d.image_le _ h1) (inv_mem hxL)
    rw [mul_inv_cancel_right] at this
    exact h.t_not_mem_L this

theorem card_yamadaR₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    Nat.card (yamadaR₂ d t) = 2 * Nat.card K ^ 8 := by
  have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaL₂ d t) (B := d.S)
    (h.S_le_normalizer_yamadaL₂ d)
  rw [h.yamadaL₂_inf_S d hK, h.card_yamadaL₂ d hK, d.cards.2.2.2.2.2.2.1,
    d.cards.2.2.2.2.2.2.2] at h1
  have hq : 0 < Nat.card K ^ 5 := by
    have : 0 < Nat.card K := Nat.card_pos
    positivity
  refine Nat.eq_of_mul_eq_mul_right hq ?_
  rw [yamadaR₂, h1]
  ring

theorem yamadaL₃_facts (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaL₂ d t ≤ yamadaL₃ d t ∧
      d.S ≤ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ∧
      yamadaR₃ d t ≤ normalizer (yamadaL₃ d t : Set G) ∧
      yamadaR₃ d t ≤ normalizer (yamadaV₂ d t : Set G) ∧ yamadaL₃ d t ⊓ d.S = d.M := by
  have hL₂L₃ : yamadaL₂ d t ≤ yamadaL₃ d t := by
    rw [← (h.yamada_5_23_1 hW d hK hD).2.2.2.2]
    exact inf_le_left
  have hSH : d.S ≤ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) := fun s hs =>
    (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK hD).2
      (mem_sup_left (mem_sup_right hs))
  have hSV : d.S ≤ normalizer (yamadaV₂ d t : Set G) :=
    hSH.trans (h.normalizer_tY_le d hK hD).2.2
  have hL₃V : yamadaL₃ d t ≤ normalizer (yamadaV₂ d t : Set G) :=
    LieType.BorelTits.pCoreOf_le 2 _
  have hNL₃ : normalizer (yamadaV₂ d t : Set G) ≤ normalizer (yamadaL₃ d t : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 _
  refine ⟨hL₂L₃, hSH, sup_le Subgroup.le_normalizer (hSV.trans hNL₃), sup_le hL₃V hSV,
    le_antisymm (fun x hx => ?_) (le_inf ((le_sup_left.trans (h.tM_le_yamadaL₂ d hK)).trans hL₂L₃)
      d.inclusions.2.2.2.2.2.2.2.2.1)⟩
  obtain ⟨hxL₃, hxS⟩ := Subgroup.mem_inf.1 hx
  rw [← h.yamadaL₂_inf_S d hK]
  exact Subgroup.mem_inf.2 ⟨h.yamadaL₃_inf_le d hK hD (Subgroup.mem_inf.2 ⟨hxL₃, hSH hxS⟩), hxS⟩

theorem card_yamadaL₃_R₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    Nat.card (yamadaL₃ d t) = 2 * Nat.card K ^ 8 ∧
      Nat.card (yamadaR₃ d t) = 2 * Nat.card K ^ 9 := by
  obtain ⟨hL₂L₃, -, hR₃L₃, -, hL₃S⟩ := h.yamadaL₃_facts hW d hK hD
  obtain ⟨_, _, φ, -, -⟩ := h.yamada_5_23_3 hW d hK hD
  have hq : 0 < Nat.card K ^ 2 := by
    have : 0 < Nat.card K := Nat.card_pos
    positivity
  have hWY : Nat.card (d.W ⧸ d.Y.subgroupOf d.W) = Nat.card K := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (d.Y.subgroupOf d.W)
    rw [Nat.card_congr (subgroupOfEquivOfLe d.inclusions.2.2.1).toEquiv, d.cards.2.2.2.1,
      d.cards.2.1] at h1
    refine Nat.eq_of_mul_eq_mul_right hq ?_
    rw [← h1]
    ring
  have hL₃ : Nat.card (yamadaL₃ d t) = 2 * Nat.card K ^ 8 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((yamadaL₂ d t).subgroupOf (yamadaL₃ d t))
    rw [Nat.card_congr φ.toEquiv, Nat.card_congr (subgroupOfEquivOfLe hL₂L₃).toEquiv, hWY,
      h.card_yamadaL₂ d hK] at h1
    rw [h1]
    ring
  refine ⟨hL₃, ?_⟩
  have h2 := Common.card_sup_mul_card_inf_eq (A := yamadaL₃ d t) (B := d.S)
    (le_sup_right.trans hR₃L₃)
  rw [hL₃S, hL₃, d.cards.2.2.2.2.2.2.1, d.cards.2.2.2.2.2.2.2] at h2
  have hq5 : 0 < Nat.card K ^ 5 := by
    have : 0 < Nat.card K := Nat.card_pos
    positivity
  refine Nat.eq_of_mul_eq_mul_right hq5 ?_
  rw [yamadaR₃, h2]
  ring

theorem yamadaR₃_facts (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaR₃ d t ≤ yamadaRstar d t ∧ yamadaR₂ d t ≤ yamadaR₃ d t ∧
      yamadaR₃ d t ≤ normalizer (yamadaR₂ d t : Set G) ∧
      yamadaR₃ d t ≤ normalizer (yamadaCstar d t : Set G) ∧
      yamadaC₂ d t = yamadaCstar d t ⊓ yamadaR₂ d t := by
  have hR₃ := h.yamada_5_23_4 hW d hK hD
  obtain ⟨hR₂eq, -, hR₅, hR₅eq, -⟩ := h.yamada_5_21_2 hW d hK hD
  have hRC : yamadaRstar d t ≤ normalizer (yamadaCstar d t : Set G) :=
    sup_le Subgroup.le_normalizer (h.S_le_normalizer_yamadaCstar d)
  have hR₃R : yamadaR₃ d t ≤ yamadaRstar d t := by
    rw [hR₃]
    exact inf_le_left
  refine ⟨hR₃R, ?_, ?_, hR₃R.trans hRC, (h.yamada_5_19 d hK hD).2.2.2.2.1⟩
  · rw [hR₃, hR₂eq]
    exact inf_le_left
  · rw [hR₃]
    exact (le_sup_left.trans hR₅eq.ge).trans hR₅

theorem yamadaW₁_mul_self (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {a : G}
    (ha : a ∈ yamadaW₁ d t) : a * a = 1 := by
  obtain ⟨-, -, -, -, hWF, hFD, -⟩ := d.inclusions
  have hU₁W := h.yamadaU₁_le_normalizer_of_le_D d hK hD (hWF.trans hFD)
  obtain ⟨w, hw, u, hu, rfl⟩ := Common.exists_mul_of_le_normalizer hU₁W a ha
  have hU₁ := h.yamada_5_16 hW d hK hD
  have hu2 : u * u = 1 := by
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := yamadaU₁ d t) u hu
  have hwu : u * w = w * u :=
    mem_centralizer_iff.1 (hD.D_le_centralizer ((hWF.trans hFD) hw)) u hu
  calc w * u * (w * u) = w * (u * w) * u := by group
    _ = w * (w * u) * u := by rw [hwu]
    _ = (w * w) * (u * u) := by group
    _ = 1 := by rw [W_mul_self d hw, hu2, one_mul]

theorem yamada_5_30_1_R₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaR₃ d t ≤ normalizer (yamadaC₂ d t : Set G) ∧
      yamadaR₃ d t = yamadaC₃ d t ⊔ yamadaR₂ d t ∧
      yamadaC₃ d t ⊓ yamadaR₂ d t = yamadaC₂ d t ∧
      yamadaR₃ d t ≤ normalizer (yamadaC₃ d t : Set G) ∧
      yamadaR₃ d t ≤ normalizer (yamadaR₂ d t : Set G) ∧
      (∀ x ∈ yamadaR₃ d t, x * x ∈ yamadaC₂ d t) ∧
      (∀ x ∈ yamadaR₃ d t, ∀ y ∈ yamadaR₃ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaC₂ d t) ∧
      Nat.card (yamadaR₃ d t) = Nat.card K ^ 2 * Nat.card (yamadaC₂ d t) := by
  obtain ⟨hR₃R, hR₂R₃, hR₃R₂, hR₃C, hC₂⟩ := h.yamadaR₃_facts hW d hK hD
  obtain ⟨-, -, -, hXF, hWF, hFD, -⟩ := d.inclusions
  have hCV := h.yamadaCstar_eq d hK hD
  have hR₃ := h.yamada_5_23_4 hW d hK hD
  have hC₃R₂ : yamadaC₃ d t ⊓ yamadaR₂ d t = yamadaC₂ d t := by
    rw [hC₂, yamadaC₃, inf_comm (yamadaR₃ d t), inf_assoc, inf_eq_right.2 hR₂R₃]
  have hNC₃ : yamadaR₃ d t ≤ normalizer (yamadaC₃ d t : Set G) := fun g hg =>
    Common.mem_normalizer_inf (Subgroup.le_normalizer hg) (hR₃C hg)
  have hNC₂ : yamadaR₃ d t ≤ normalizer (yamadaC₂ d t : Set G) := fun g hg => by
    rw [hC₂]
    exact Common.mem_normalizer_inf (hR₃C hg) (hR₃R₂ hg)
  have hfac : ∀ g ∈ yamadaR₃ d t, ∃ x ∈ yamadaC₃ d t, x⁻¹ * g ∈ yamadaR₂ d t := fun g hg => by
    have hg' : g ∈ yamadaR₃star d t := hR₃ ▸ hg
    obtain ⟨hgR, hgκ⟩ := (h.mem_yamadaR₃star_iff d hK hD).1 hg'
    have hW₁D₁ : yamadaW₁ d t ≤ yamadaD₁ d t :=
      sup_le ((hWF.trans hFD).trans le_sup_right) hD.spec.1
    obtain ⟨x, hx, u, hu, e⟩ := (h.yamada_5_19 d hK hD).2.1.2 _ (hW₁D₁ hgκ)
    have hxR : x ∈ yamadaRstar d t := mem_sup_left hx
    have hκx : t * x * t * x⁻¹ = (t * g * t * g⁻¹) * u := by
      rw [show t * x * t * x⁻¹ = t * (x * t * x⁻¹) by group, e, ← mul_assoc, ← mul_assoc,
        h.t_mul_t, one_mul]
    have hxR₃ : x ∈ yamadaR₃ d t := by
      rw [hR₃]
      refine (h.mem_yamadaR₃star_iff d hK hD).2 ⟨hxR, ?_⟩
      rw [hκx]
      exact mul_mem hgκ (mem_sup_right hu)
    refine ⟨x, Subgroup.mem_inf.2 ⟨hxR₃, hx⟩, (h.mem_yamadaR₂_iff hW d hK hD).2
      ⟨mul_mem (inv_mem hxR) hgR, ?_⟩⟩
    have hxU₁ : x ∈ normalizer (yamadaU₁ d t : Set G) := (h.normalizer_yamadaC₁_le d hK hD).2
      ((h.normalizer_yamadaC₁_le d hK hD).1 (h.yamadaRstar_le_normalizer d hxR))
    rw [h.crossed_mul' x⁻¹ g, h.crossed_inv' x, hκx, show x⁻¹ * (t * g * t * g⁻¹ * u)⁻¹ * x *
      (x⁻¹ * (t * g * t * g⁻¹) * x⁻¹⁻¹) = x⁻¹ * u⁻¹ * x⁻¹⁻¹ by group]
    exact mem_sup_right ((mem_normalizer_iff.1 (inv_mem hxU₁) _).1 (inv_mem hu))
  have hR₃eq : yamadaR₃ d t = yamadaC₃ d t ⊔ yamadaR₂ d t := by
    refine le_antisymm (fun g hg => ?_) (sup_le inf_le_left hR₂R₃)
    obtain ⟨x, hx, hxg⟩ := hfac g hg
    have := mul_mem (mem_sup_left hx) (mem_sup_right hxg :
      x⁻¹ * g ∈ yamadaC₃ d t ⊔ yamadaR₂ d t)
    rwa [mul_inv_cancel_left] at this
  have hC₁C₂ : yamadaC₁ d t ≤ yamadaC₂ d t := by
    rw [(h.yamadaC₂_eq_sup d hK hD).1]
    exact le_sup_left
  have hsqC : ∀ c ∈ yamadaC₃ d t, c * c ∈ yamadaC₂ d t := fun c hc => by
    obtain ⟨hcR₃, hcC⟩ := Subgroup.mem_inf.1 hc
    have hcV : c ∈ h.yamadaV d hK hD := hCV ▸ hcC
    have hcN := ((h.mem_yamadaV d hK hD).1 hcV).1
    have hκ : t * c * t * c⁻¹ ∈ yamadaW₁ d t :=
      ((h.mem_yamadaR₃star_iff d hK hD).1 (hR₃ ▸ hcR₃)).2
    have h1 := h.crossed_mul_mem d hK hD hcV hcN
    rw [h.yamadaW₁_mul_self hW d hK hD hκ, inv_one, one_mul] at h1
    exact hC₁C₂ (h.mem_yamadaC₁_of_crossed_mem d hK hD (mul_mem hcV hcV) h1)
  have hF₁C₂ : yamadaF₁ d t ≤ yamadaC₂ d t := by
    rw [h.yamadaF₁_eq_sup d hK hD]
    exact sup_le ((hFD.trans ((le_sup_right : d.D ≤ yamadaD₁ d t).trans
      (h.yamadaD₁_le_yamadaC₁ d hK))).trans hC₁C₂) ((h.yamadaU₁_le_yamadaC₁ d hK hD).trans hC₁C₂)
  have hsqR : ∀ r ∈ yamadaR₂ d t, r * r ∈ yamadaC₂ d t := fun r hr => by
    refine hF₁C₂ ?_
    rw [← (h.yamada_5_15_3 d hK hD).1]
    exact subset_closure ⟨r, hr, (sq r).symm⟩
  have hsq : ∀ x ∈ yamadaR₃ d t, x * x ∈ yamadaC₂ d t := fun x hx => by
    obtain ⟨x₀, hx₀, hxg⟩ := hfac x hx
    have hcomm : x₀⁻¹ * ((x₀⁻¹ * x) * x₀ * (x₀⁻¹ * x)⁻¹) ∈ yamadaC₂ d t := by
      rw [← hC₃R₂]
      refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hx₀) ((mem_normalizer_iff.1
        (hNC₃ (hR₂R₃ hxg)) x₀).1 hx₀), ?_⟩
      rw [show x₀⁻¹ * ((x₀⁻¹ * x) * x₀ * (x₀⁻¹ * x)⁻¹) =
        (x₀⁻¹ * (x₀⁻¹ * x) * x₀⁻¹⁻¹) * (x₀⁻¹ * x)⁻¹ by group]
      exact mul_mem ((mem_normalizer_iff.1 (hR₃R₂ (inv_mem (Subgroup.mem_inf.1 hx₀).1)) _).1 hxg)
        (inv_mem hxg)
    rw [show x * x = (x₀ * x₀) * (x₀⁻¹ * ((x₀⁻¹ * x) * x₀ * (x₀⁻¹ * x)⁻¹)) *
      ((x₀⁻¹ * x) * (x₀⁻¹ * x)) by group]
    exact mul_mem (mul_mem (hsqC x₀ hx₀) hcomm) (hsqR _ hxg)
  have hcomm : ∀ x ∈ yamadaR₃ d t, ∀ y ∈ yamadaR₃ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaC₂ d t :=
    fun x hx y hy => by
      rw [show x * y * x⁻¹ * y⁻¹ = (x * y * (x * y)) * (y⁻¹ * (x * x)⁻¹ * y⁻¹⁻¹) *
        (y * y)⁻¹ by group]
      exact mul_mem (mul_mem (hsq _ (mul_mem hx hy))
        ((mem_normalizer_iff.1 (inv_mem (hNC₂ hy)) _).1 (inv_mem (hsq x hx))))
        (inv_mem (hsq y hy))
  have hcard : Nat.card (yamadaR₃ d t) = Nat.card K ^ 2 * Nat.card (yamadaC₂ d t) := by
    rw [(h.card_yamadaL₃_R₃ hW d hK hD).2, (h.card_yamadaC₂_E₂_V₂ d hK hD).1]
    ring
  exact ⟨hNC₂, hR₃eq, hC₃R₂, hNC₃, hR₃R₂, hsq, hcomm, hcard⟩

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
