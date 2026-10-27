module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYThirteen

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section SupZpowers

variable {G : Type*} [Group G] [Finite G] {A : Subgroup G} {t : G}

omit [Finite G] in
theorem mem_sup_zpowers_iff_of (htt : t * t = 1) (htA : t ∈ normalizer (A : Set G)) {x : G} :
    x ∈ A ⊔ zpowers t ↔ x ∈ A ∨ ∃ a ∈ A, x = a * t := by
  constructor
  · intro hx
    obtain ⟨a, ha, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer ((zpowers_le).2 htA) x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
    have ht2 : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, htt])
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [show m + m = 2 * m by ring, zpow_mul, zpow_two, htt, one_zpow, mul_one]
      exact ha
    · right
      refine ⟨a, ha, ?_⟩
      rw [zpow_add_one, zpow_mul, zpow_two, htt, one_zpow, one_mul]
  · rintro (hx | ⟨a, ha, rfl⟩)
    · exact mem_sup_left hx
    · exact mul_mem (mem_sup_left ha) (mem_sup_right (mem_zpowers t))

theorem le_of_mul_comm_of_le_sup_zpowers (htt : t * t = 1) (htA : t ∈ normalizer (A : Set G))
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcard : 2 * Nat.card (A ⊓ centralizer ({t} : Set G) : Subgroup G) < Nat.card A)
    {X : Subgroup G} (hX : X ≤ A ⊔ zpowers t) (hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hXc : Nat.card A ≤ Nat.card X) : X ≤ A := by
  by_contra hn
  obtain ⟨x, hxX, hxA⟩ := Set.not_subset.1 hn
  obtain hx | ⟨a, ha, rfl⟩ := (mem_sup_zpowers_iff_of htt htA).1 (hX hxX)
  · exact hxA hx
  have hXA : X ⊓ A ≤ A ⊓ centralizer ({t} : Set G) := by
    intro y hy
    obtain ⟨hyX, hyA⟩ := Subgroup.mem_inf.1 hy
    refine Subgroup.mem_inf.2 ⟨hyA, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := hXab y hyX _ hxX
    have h2 : y * a = a * y := hAab y hyA a ha
    have h3 : a * (y * t) = a * (t * y) := by
      calc a * (y * t) = y * (a * t) := by rw [← mul_assoc, ← h2, mul_assoc]
        _ = a * t * y := h1
        _ = a * (t * y) := by rw [mul_assoc]
    exact mul_left_cancel h3
  have h1 := Common.card_sup_mul_card_inf_eq (A := A) (B := X)
    (hX.trans (sup_le le_normalizer ((zpowers_le).2 htA)))
  have h2 : Nat.card (A ⊔ X : Subgroup G) ≤ 2 * Nat.card A := by
    have h3 := Common.card_sup_mul_card_inf_eq (A := A) (B := zpowers t) ((zpowers_le).2 htA)
    have h4 : Nat.card (zpowers t) ≤ 2 :=
      Nat.card_zpowers t ▸ Nat.le_of_dvd (by norm_num)
        (orderOf_dvd_of_pow_eq_one (by rw [sq, htt]))
    have h5 : Nat.card (A ⊔ zpowers t : Subgroup G) ≤ 2 * Nat.card A := by
      have hpos : 0 < Nat.card (A ⊓ zpowers t : Subgroup G) := Nat.card_pos
      calc Nat.card (A ⊔ zpowers t : Subgroup G) ≤
          Nat.card (A ⊔ zpowers t : Subgroup G) * Nat.card (A ⊓ zpowers t : Subgroup G) :=
            Nat.le_mul_of_pos_right _ hpos
        _ = Nat.card A * Nat.card (zpowers t) := h3
        _ ≤ Nat.card A * 2 := Nat.mul_le_mul_left _ h4
        _ = 2 * Nat.card A := mul_comm _ _
    exact (Subgroup.card_le_of_le (sup_le le_sup_left hX)).trans h5
  have hpos : 0 < Nat.card A := Nat.card_pos
  have h3 : Nat.card A * Nat.card X ≤ Nat.card A * (2 * Nat.card (X ⊓ A : Subgroup G)) := by
    rw [← h1, inf_comm]
    calc Nat.card (A ⊔ X : Subgroup G) * Nat.card (X ⊓ A : Subgroup G) ≤
        2 * Nat.card A * Nat.card (X ⊓ A : Subgroup G) := Nat.mul_le_mul_right _ h2
      _ = _ := by ring
  have h4 := Nat.le_of_mul_le_mul_left h3 hpos
  have h5 := Subgroup.card_le_of_le hXA
  omega

theorem normalizer_sup_zpowers_le (htt : t * t = 1) (htA : t ∈ normalizer (A : Set G))
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcard : 2 * Nat.card (A ⊓ centralizer ({t} : Set G) : Subgroup G) < Nat.card A) :
    normalizer ((A ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (A : Set G) := by
  intro g hg
  have hle : A.map (MulAut.conj g).toMonoidHom ≤ A := by
    refine le_of_mul_comm_of_le_sup_zpowers htt htA hAab hcard ?_ ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      exact (mem_normalizer_iff.1 hg u).1 (mem_sup_left hu)
    · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show g * u * g⁻¹ * (g * v * g⁻¹) = g * (u * v) * g⁻¹ by group, hAab u hu v hv]
      group
    · rw [card_map_of_injective (MulAut.conj g).injective]
  exact mem_normalizer_of_conj_mem fun u hu => hle ⟨u, hu, rfl⟩

theorem normalizer_sup_zpowers_le_inf (htt : t * t = 1) (htA : t ∈ normalizer (A : Set G))
    (htA' : t ∉ A) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAe : ∀ a ∈ A, a * a = 1)
    (hcard : 2 * Nat.card (A ⊓ centralizer ({t} : Set G) : Subgroup G) < Nat.card A) :
    normalizer ((A ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer (((A ⊓ centralizer ({t} : Set G)) ⊔ zpowers t : Subgroup G) : Set G) := by
  intro g hg
  have hgA := normalizer_sup_zpowers_le htt htA hAab hcard hg
  have hgt : g * t * g⁻¹ ∈ A ⊔ zpowers t :=
    (mem_normalizer_iff.1 hg t).1 (mem_sup_right (mem_zpowers t))
  obtain ⟨a, ha, hga⟩ : ∃ a ∈ A, g * t * g⁻¹ = a * t := by
    rcases (mem_sup_zpowers_iff_of htt htA).1 hgt with h1 | h1
    · exfalso
      refine htA' ?_
      have := (mem_normalizer_iff.1 (inv_mem hgA) _).1 h1
      rwa [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at this
    · exact h1
  have hat : a * t = t * a := by
    have h1 : (a * t) * (a * t) = 1 := by
      rw [← hga]
      calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
        _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
    have h2 : t * a * t = a⁻¹ := by
      calc t * a * t = a⁻¹ * (a * t * (a * t)) := by group
        _ = a⁻¹ := by rw [h1, mul_one]
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hAe a ha)
    calc a * t = t * (t * a * t) := by rw [← mul_assoc, ← mul_assoc, htt, one_mul]
      _ = t * a := by rw [h2, hainv]
  have hgC : g ∈ normalizer ((A ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) := by
    refine mem_normalizer_of_conj_mem fun w hw => ?_
    obtain ⟨hwA, hwt⟩ := Subgroup.mem_inf.1 hw
    have hz : g * w * g⁻¹ ∈ A := (mem_normalizer_iff.1 hgA w).1 hwA
    have hwt' : w * t = t * w := mem_centralizer_singleton_iff.1 hwt
    have h1 : g * w * g⁻¹ * (a * t) = a * t * (g * w * g⁻¹) := by
      rw [← hga]
      calc g * w * g⁻¹ * (g * t * g⁻¹) = g * (w * t) * g⁻¹ := by group
        _ = g * (t * w) * g⁻¹ := by rw [hwt']
        _ = g * t * g⁻¹ * (g * w * g⁻¹) := by group
    have h2 : g * w * g⁻¹ * a = a * (g * w * g⁻¹) := hAab _ hz a ha
    refine Subgroup.mem_inf.2 ⟨hz, mem_centralizer_singleton_iff.2 ?_⟩
    have h3 : a * (g * w * g⁻¹ * t) = a * (t * (g * w * g⁻¹)) := by
      calc a * (g * w * g⁻¹ * t) = g * w * g⁻¹ * (a * t) := by rw [← mul_assoc, ← h2, mul_assoc]
        _ = a * t * (g * w * g⁻¹) := h1
        _ = a * (t * (g * w * g⁻¹)) := by rw [mul_assoc]
    exact mul_left_cancel h3
  have htC : t ∈ normalizer ((A ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) :=
    Common.mem_normalizer_inf htA (le_normalizer (mem_centralizer_singleton_iff.2 rfl))
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨w, hw, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer ((zpowers_le).2 htC) x hx
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
  rw [show g * (w * t ^ k) * g⁻¹ = g * w * g⁻¹ * (g * t * g⁻¹) ^ k by rw [conj_zpow]; group, hga]
  refine mul_mem (mem_sup_left ((mem_normalizer_iff.1 hgC w).1 hw)) (zpow_mem ?_ k)
  exact mul_mem (mem_sup_left ⟨ha, mem_centralizer_singleton_iff.2 hat⟩)
    (mem_sup_right (mem_zpowers t))

end SupZpowers

namespace Model

variable
  {K : Type} [Field K]
  [CharP K 2]

theorem mem_borel_or_eq_mul_wb_mul {g : ModGL .G2 K} (hg : g ∈ adjointGroup .G2 K)
    (hgY : g ∈ normalizer (Y K : Set (ModGL .G2 K))) :
    g ∈ borelGroup .G2 K ∨
      ∃ b₁ ∈ borelGroup .G2 K, ∃ b₂ ∈ borelGroup .G2 K, g = b₁ * wb K * b₂ := by
  obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl, hw⟩ :=
    exists_bruhat_of_mem_normalizer AS81.G2.borelGroup_le_normalizer_g2BCGroup hg hgY
  have hY : ∀ γ, IsRoot .G2 γ → pinnedX .G2 K γ 1 ∈ Y K → (w • γ = g2b ∨ w • γ = g2c) :=
    fun γ hγ h => AS81.G2.eq_b_or_c_of_pinnedX_mem (IsRoot.smul hγ w) (hw γ hγ h)
  rcases AS81.G2.weyl_eq_of_bc (hY _ isRoot_g2b (AS81.G2.pinnedX_b_mem_g2BCGroup 1))
    (hY _ isRoot_g2c (AS81.G2.pinnedX_c_mem_g2BCGroup 1)) with rfl | rfl
  · left
    rw [canonicalRep_one, mul_one]
    exact mul_mem hb₁ hb₂
  · right
    refine ⟨b₁, hb₁, b₂, hb₂, ?_⟩
    rw [canonicalRep_simple]
    rfl

end Model

namespace G2Data

variable {G : Type*} [Group G]
  {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

theorem emb_mem_J_sup_S {b : adjointGroup .G2 K}
    (hb : (b : ModGL .G2 K) ∈ borelGroup .G2 K) : d.emb b ∈ d.J ⊔ d.S := by
  obtain ⟨h₁, hh₁, u, hu, he⟩ := exists_torus_mul_of_mem_borel hb
  have hb' : b = ⟨h₁, Model.J_le_adjointGroup K hh₁⟩ * ⟨u, Model.S_le_adjointGroup K hu⟩ :=
    Subtype.ext he
  rw [hb', map_mul]
  exact mul_mem (mem_sup_left (d.emb_mem_image hh₁)) (mem_sup_right (d.emb_mem_image hu))

end G2Data

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem yamadaY₂_mul_self (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {y : G}
    (hy : y ∈ yamadaY₂ d t) : y * y = 1 := by
  have := h.yamada_5_16 hW d hK hD
  have hsq : ∀ {u : G}, u ∈ yamadaU₁ d t → u * u = 1 := fun {u} hu => by
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian u hu
  obtain ⟨u, hu, v, hv, rfl⟩ :=
    Common.exists_mul_of_le_normalizer (h.map_wb_yamadaU₁_le_normalizer d hK hD) y hy
  have hc : v * u = u * v :=
    h.yamadaY₂_mul_comm d hK hD (mem_sup_right hv) (yamadaU₁_le_yamadaY₂ d t hu)
  obtain ⟨u', hu', rfl⟩ := hv
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hc ⊢
  calc u * (d.wb * u' * d.wb⁻¹) * (u * (d.wb * u' * d.wb⁻¹)) =
      u * (d.wb * u' * d.wb⁻¹ * u) * (d.wb * u' * d.wb⁻¹) := by group
    _ = u * u * (d.wb * (u' * u') * d.wb⁻¹) := by rw [hc]; group
    _ = 1 := by rw [hsq hu, hsq hu']; group

theorem two_mul_card_Y_lt (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    2 * Nat.card (yamadaY₂ d t ⊓ centralizer ({t} : Set G) : Subgroup G) <
      Nat.card (yamadaY₂ d t) := by
  have h4K : 4 ≤ Nat.card K := hK ▸ h.four_le
  rw [h.yamadaY₂_inf_centralizer d hK hD, d.cards.2.1, h.card_yamadaY₂ d hK hD]
  have : 2 < Nat.card K ^ 2 := by nlinarith
  nlinarith

theorem yamada_5_17_2 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    normalizer ((yamadaY₂ d t ⊔ zpowers t : Subgroup G) : Set G) =
      normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) := by
  have htt := h.t_mul_t
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  have htY₂ : t ∈ normalizer (yamadaY₂ d t : Set G) :=
    h.yamadaL₂_le_normalizer_yamadaY₂ d hK hD htL₂
  have htY₂' : t ∉ yamadaY₂ d t := fun ht =>
    h.t_not_mem_yamadaM₂ d hK hD ((le_sup_right : yamadaY₂ d t ≤ yamadaM₂ d t) ht)
  apply le_antisymm
  · have h1 := normalizer_sup_zpowers_le_inf htt htY₂ htY₂'
      (fun a ha b hb => h.yamadaY₂_mul_comm d hK hD ha hb)
      (fun a ha => h.yamadaY₂_mul_self hW d hK hD ha) (h.two_mul_card_Y_lt d hK hD)
    rwa [h.yamadaY₂_inf_centralizer d hK hD] at h1
  · intro g hg
    have hgL₂ := le_normalizer_yamadaL₂ d t hg
    have hgY₂ := (h.normalizer_yamadaL₂_le d hK hD).2 hgL₂
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨y, hy, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer ((zpowers_le).2 htY₂) x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
    have hgt : g * t * g⁻¹ ∈ yamadaY₂ d t ⊔ zpowers t :=
      sup_le_sup_right (h.Y_le_yamadaY₂ d hK hD) _
        ((mem_normalizer_iff.1 hg t).1 (mem_sup_right (mem_zpowers t)))
    rw [show g * (y * t ^ k) * g⁻¹ = g * y * g⁻¹ * (g * t * g⁻¹) ^ k by rw [conj_zpow]; group]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.1 hgY₂ y).1 hy)) (zpow_mem hgt k)

theorem card_yamadaY₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : Nat.card (yamadaY₁ d t) = Nat.card K ^ 3 := by
  obtain ⟨-, hUU₁, -⟩ := hD.spec
  have hU₁Y : yamadaU₁ d t ≤ normalizer (d.Y : Set G) :=
    ((h.yamadaU₁_le_yamadaL₂ d hK hD).trans le_sup_left).trans (h.yamadaR₂_le_normalizer_Y d hK)
  have h1 := Common.card_sup_mul_card_inf_eq (A := d.Y) (B := yamadaU₁ d t) hU₁Y
  have hinf : d.Y ⊓ yamadaU₁ d t = d.U := by
    refine le_antisymm ?_ (le_inf d.inclusions.1 hUU₁)
    rw [← hD.inf_centralizer, inf_comm]
    exact inf_le_inf_left _ ((d.image_le _).trans h.L_le_centralizer)
  rw [hinf, d.cards.1, d.cards.2.1, (hD.yamada_5_10_1).2.2] at h1
  have hq : 0 < Nat.card K := Nat.card_pos
  have h2 : Nat.card (yamadaY₁ d t) * Nat.card K = Nat.card K ^ 3 * Nat.card K := by
    rw [yamadaY₁, h1]
    ring
  exact Nat.eq_of_mul_eq_mul_right hq h2

theorem wb_not_mem_normalizer_yamadaY₁ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    d.wb ∉ normalizer (yamadaY₁ d t : Set G) := by
  have h4K : 4 ≤ Nat.card K := hK ▸ h.four_le
  intro hw
  have hle : yamadaY₂ d t ≤ yamadaY₁ d t := by
    refine sup_le le_sup_right ?_
    rintro _ ⟨u, hu, rfl⟩
    exact (mem_normalizer_iff.1 hw u).1 (mem_sup_right hu)
  have h1 := Subgroup.card_le_of_le hle
  rw [h.card_yamadaY₂ d hK hD, h.card_yamadaY₁ d hK hD] at h1
  have : Nat.card K ^ 3 < Nat.card K ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

theorem centralizer_inf_normalizer_S_le (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤ normalizer (yamadaC₁ d t : Set G) ∧
      centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤ normalizer (yamadaU₁ d t : Set G) ∧
      centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤ normalizer (d.Y : Set G) := by
  have h4K : 4 ≤ Nat.card K := hK ▸ h.four_le
  have hNR : centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤
      normalizer (yamadaR d t : Set G) := by
    rw [(h.yamada_5_3_3 d hK).1]
    exact le_sup_right
  have hC₁ := hNR.trans ((h.normalizer_yamadaR_le d).trans (le_normalizer_yamadaC₁ d t))
  refine ⟨hC₁, hC₁.trans ((h.normalizer_yamadaC₁_le d hK hD).1.trans
    (h.normalizer_yamadaC₁_le d hK hD).2), ?_⟩
  have h1 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (Subgroup.upperCentralSeries d.S 2)
  rw [(d.yamada_3_12_upperCentralSeries (by omega)).2.1] at h1
  exact inf_le_right.trans h1

theorem exists_mem_L_inv_mul_mem_normalizer (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) {c : G} (hc : c ∈ normalizer (L : Set G)) :
    ∃ g ∈ L, ∀ H : Subgroup (ModGL .G2 K),
      (∀ k : ℕ, H.map (Units.map (entrywiseHom (frobeniusEquiv K 2 ^ k).toRingHom)) = H) →
        g⁻¹ * c ∈ normalizer (d.image H : Set G) := by
  obtain ⟨g₀, k, -, hgk⟩ := Model.exists_eq_conj_mul_fieldAut_pow hK h.two_le (d.act ⟨c, hc⟩)
  refine ⟨d.emb g₀, d.emb_mem g₀, fun H hH => mem_normalizer_of_conj_mem fun y hy => ?_⟩
  obtain ⟨h₀, hh₀, rfl⟩ := d.mem_image.1 hy
  have e1 : (d.emb g₀)⁻¹ * c * d.emb h₀ * ((d.emb g₀)⁻¹ * c)⁻¹ =
      (d.emb g₀)⁻¹ * (c * d.emb h₀ * c⁻¹) * d.emb g₀ := by group
  have e3 : c * d.emb h₀ * c⁻¹ = d.emb (d.act ⟨c, hc⟩ h₀) := (d.emb_act_apply ⟨c, hc⟩ h₀).symm
  rw [e1, e3, hgk, ← map_inv, ← map_mul, ← map_mul]
  refine d.emb_mem_image ?_
  have e2 : g₀⁻¹ * (MulAut.conj g₀ * Model.fieldAut K ^ k) h₀ * g₀ =
      (Model.fieldAut K ^ k) h₀ := by
    rw [MulAut.mul_apply, MulAut.conj_apply]
    group
  rw [e2, Model.coe_fieldAut_pow_apply, ← hH k]
  exact ⟨_, hh₀, rfl⟩

theorem exists_mul_of_mem_normalizer_Y (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) {c : G} (hc : c ∈ centralizer ({t} : Set G))
    (hcY : c ∈ normalizer (d.Y : Set G)) :
    ∃ g ∈ L ⊓ normalizer (d.Y : Set G),
      ∃ x ∈ centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G), c = g * x := by
  obtain ⟨g, hgL, hg⟩ := h.exists_mem_L_inv_mul_mem_normalizer d hK (h.centralizer_le_normalizer hc)
  have hxS := hg (Model.S K) fun k => Model.map_entrywise_S _
  have hxY := hg (Model.Y K) fun k => Model.map_entrywise_Y _
  have hxC : g⁻¹ * c ∈ centralizer ({t} : Set G) := mul_mem (inv_mem (h.L_le_centralizer hgL)) hc
  refine ⟨g, ⟨hgL, ?_⟩, g⁻¹ * c, ⟨hxC, hxS⟩, by group⟩
  have := mul_mem hcY (inv_mem hxY)
  rwa [show c * (g⁻¹ * c)⁻¹ = g by group] at this

theorem mem_J_sup_S_of_mem_normalizer (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {g : G} (hg : g ∈ L ⊓ normalizer
    (d.Y : Set G))
    (hgY₁ : g ∈ normalizer (yamadaY₁ d t : Set G)) : g ∈ d.J ⊔ d.S := by
  obtain ⟨hNS₁, hNS₂, hNS₃⟩ := h.centralizer_inf_normalizer_S_le d hK hD
  have hJS : d.J ⊔ d.S ≤ normalizer (yamadaY₁ d t : Set G) := by
    rw [← (d.yamada_3_13_1_G).2.2]
    intro x hx
    have hx' : x ∈ centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) :=
      ⟨h.L_le_centralizer hx.1, hx.2⟩
    exact mem_normalizer_sup (hNS₃ hx') (hNS₂ hx')
  have hg' : g ∈ d.image (adjointGroup .G2 K ⊓ normalizer (Model.Y K : Set (ModGL .G2 K))) := by
    rw [d.image_inf_normalizer Model.Y_le_adjointGroup]
    exact hg
  obtain ⟨g₀, ⟨-, hg₀Y⟩, rfl⟩ := d.mem_image.1 hg'
  rcases Model.mem_borel_or_eq_mul_wb_mul g₀.2 hg₀Y with hb | ⟨b₁, hb₁, b₂, hb₂, he⟩
  · exact d.emb_mem_J_sup_S hb
  · exfalso
    obtain ⟨h₁, hh₁, u₁, hu₁, rfl⟩ := exists_torus_mul_of_mem_borel hb₁
    obtain ⟨h₂, hh₂, u₂, hu₂, rfl⟩ := exists_torus_mul_of_mem_borel hb₂
    have hA₁ : h₁ * u₁ ∈ adjointGroup .G2 K :=
      mul_mem (Model.J_le_adjointGroup K hh₁) (Model.S_le_adjointGroup K hu₁)
    have hA₂ : h₂ * u₂ ∈ adjointGroup .G2 K :=
      mul_mem (Model.J_le_adjointGroup K hh₂) (Model.S_le_adjointGroup K hu₂)
    have hwb : (⟨Model.wb K, Model.wb_mem_adjointGroup K⟩ : adjointGroup .G2 K) =
        (⟨h₁ * u₁, hA₁⟩ : adjointGroup .G2 K)⁻¹ * g₀ * (⟨h₂ * u₂, hA₂⟩)⁻¹ := by
      apply Subtype.ext
      simp only [coe_mul, coe_inv]
      rw [he]
      group
    refine h.wb_not_mem_normalizer_yamadaY₁ d hK hD ?_
    rw [G2Data.wb, hwb, map_mul, map_mul, map_inv, map_inv]
    exact mul_mem (mul_mem (inv_mem (hJS (d.emb_mem_J_sup_S hb₁))) hgY₁)
      (inv_mem (hJS (d.emb_mem_J_sup_S hb₂)))

theorem yamada_5_17_3 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    normalizer (yamadaR₁ d t : Set G) =
        normalizer ((yamadaY₁ d t ⊔ zpowers t : Subgroup G) : Set G) ∧
      normalizer ((yamadaY₁ d t ⊔ zpowers t : Subgroup G) : Set G) =
        yamadaR₂ d t ⊔ (centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G)) ∧
      ((normalizer ((yamadaY₁ d t ⊔ zpowers t : Subgroup G) : Set G) : Subgroup G) : Set G) =
        (yamadaR₂ d t : Set G) *
          ((centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) : Subgroup G) : Set G) := by
  have h4K : 4 ≤ Nat.card K := hK ▸ h.four_le
  have htt := h.t_mul_t
  obtain ⟨hNS₁, hNS₂, hNS₃⟩ := h.centralizer_inf_normalizer_S_le d hK hD
  have hR₂Y₁ := h.yamadaR₂_le_normalizer_yamadaY₁ d hK hD
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  have htY₁ : t ∈ normalizer (yamadaY₁ d t : Set G) := hR₂Y₁ (mem_sup_left htL₂)
  have htY₁' : t ∉ yamadaY₁ d t := fun ht => h.t_not_mem_yamadaM₂ d hK hD
    ((le_sup_right : yamadaY₂ d t ≤ yamadaM₂ d t) (h.yamadaY₁_le_yamadaY₂ d hK hD ht))
  have hab : ∀ a ∈ yamadaY₁ d t, ∀ b ∈ yamadaY₁ d t, a * b = b * a := fun a ha b hb =>
    h.yamadaY₂_mul_comm d hK hD (h.yamadaY₁_le_yamadaY₂ d hK hD ha)
      (h.yamadaY₁_le_yamadaY₂ d hK hD hb)
  have he : ∀ a ∈ yamadaY₁ d t, a * a = 1 := fun a ha =>
    h.yamadaY₂_mul_self hW d hK hD (h.yamadaY₁_le_yamadaY₂ d hK hD ha)
  have hcard : 2 * Nat.card (yamadaY₁ d t ⊓ centralizer ({t} : Set G) : Subgroup G) <
      Nat.card (yamadaY₁ d t) := by
    rw [h.yamadaY₁_inf_centralizer d hK hD, d.cards.2.1, h.card_yamadaY₁ d hK hD]
    have hq : 2 < Nat.card K := by omega
    calc 2 * Nat.card K ^ 2 < Nat.card K * Nat.card K ^ 2 :=
          Nat.mul_lt_mul_of_pos_right hq (by positivity)
      _ = Nat.card K ^ 3 := by ring
  have hNC : centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤
      normalizer (yamadaR₁ d t : Set G) := fun x hx => mem_normalizer_sup (hNS₁ hx) hx.2
  have hNR₂ : centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤
      normalizer (yamadaR₂ d t : Set G) := fun x hx => by
    have hxtY : x ∈ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) :=
      mem_normalizer_sup (hNS₃ hx) (mem_normalizer_zpowers (mem_centralizer_singleton_iff.1 hx.1))
    exact mem_normalizer_sup (le_normalizer_yamadaL₂ d t hxtY) hx.2
  have h1 : normalizer (yamadaR₁ d t : Set G) ≤
      normalizer ((yamadaY₁ d t ⊔ zpowers t : Subgroup G) : Set G) := by
    have := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (Subgroup.upperCentralSeries (yamadaR₁ d t) 2)
    rwa [(h.yamada_5_15_1 d hK hD).2.1] at this
  have h2 : normalizer ((yamadaY₁ d t ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) := by
    have := normalizer_sup_zpowers_le_inf htt htY₁ htY₁' hab he hcard
    rwa [h.yamadaY₁_inf_centralizer d hK hD] at this
  have h3 := normalizer_sup_zpowers_le htt htY₁ hab hcard
  have h4 : normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ⊓
      normalizer (yamadaY₁ d t : Set G) ≤
        yamadaR₂ d t ⊔ (centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G)) := by
    intro g hg
    obtain ⟨hg₁, hg₂⟩ := Subgroup.mem_inf.1 hg
    have hg₁' : g ∈ ((normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) : Subgroup G) :
        Set G) := hg₁
    rw [(h.yamada_5_5_1 d hK).2.2.1] at hg₁'
    obtain ⟨l, hl, c, hc, rfl⟩ := Set.mem_mul.1 hg₁'
    have hcY₁ : c ∈ normalizer (yamadaY₁ d t : Set G) := by
      have := mul_mem (inv_mem (hR₂Y₁ (mem_sup_left hl))) hg₂
      rwa [inv_mul_cancel_left] at this
    obtain ⟨g₁, hg₁L, x, hx, rfl⟩ := h.exists_mul_of_mem_normalizer_Y d hK hc.1 hc.2
    have hxY₁ : x ∈ normalizer (yamadaY₁ d t : Set G) := mem_normalizer_sup (hNS₃ hx) (hNS₂ hx)
    have hg₁Y₁ : g₁ ∈ normalizer (yamadaY₁ d t : Set G) := by
      have := mul_mem hcY₁ (inv_mem hxY₁)
      rwa [mul_inv_cancel_right] at this
    have hg₁JS := h.mem_J_sup_S_of_mem_normalizer d hK hD hg₁L hg₁Y₁
    rw [← (d.yamada_3_13_1_G).2.2] at hg₁JS
    have hg₁NS : g₁ ∈ centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) :=
      ⟨h.L_le_centralizer hg₁JS.1, hg₁JS.2⟩
    exact mul_mem (mem_sup_left (mem_sup_left hl)) (mem_sup_right (mul_mem hg₁NS hx))
  have h5 : yamadaR₂ d t ⊔ (centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G)) ≤
      normalizer (yamadaR₁ d t : Set G) := sup_le (h.yamada_5_6_1 d hK).2.2.1 hNC
  have h6 : normalizer ((yamadaY₁ d t ⊔ zpowers t : Subgroup G) : Set G) ≤
      yamadaR₂ d t ⊔ (centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G)) :=
    fun g hg => h4 ⟨h2 hg, h3 hg⟩
  have he1 : normalizer ((yamadaY₁ d t ⊔ zpowers t : Subgroup G) : Set G) =
      yamadaR₂ d t ⊔ (centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G)) :=
    le_antisymm h6 (h5.trans h1)
  refine ⟨le_antisymm h1 (h6.trans h5), he1, ?_⟩
  rw [he1]
  exact coe_mul_of_right_le_normalizer_left _ _ hNR₂

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
