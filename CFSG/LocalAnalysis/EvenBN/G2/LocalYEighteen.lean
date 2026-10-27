module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYSeventeen

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section Defs

variable
  {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def yamadaL₃ (d : G2Data L K) (t : G) : Subgroup G :=
  pCoreOf 2 (normalizer (yamadaV₂ d t : Set G))

@[expose] noncomputable def yamadaR₃ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaL₃ d t ⊔ d.S

end Defs

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem W_inf_yamadaY₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.W ⊓ yamadaY₂ d t = d.Y := by
  obtain ⟨-, -, hYW, -⟩ := d.inclusions
  refine le_antisymm ?_ (le_inf hYW (h.Y_le_yamadaY₂ d hK hD))
  rw [← h.yamadaY₂_inf_centralizer d hK hD, inf_comm]
  exact inf_le_inf_left _ ((d.image_le _).trans h.L_le_centralizer)

theorem W_le_centralizer_yamadaY₂ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    d.W ≤ centralizer (yamadaY₂ d t : Set G) := by
  obtain ⟨-, -, -, -, hWF, -, hFM, -⟩ := d.inclusions
  exact (hWF.trans hFM).trans (h.M_le_centralizer_yamadaY₂ d hK hD)

theorem yamadaY₂_le_normalizer_W (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaY₂ d t ≤ normalizer (d.W : Set G) := fun y hy =>
  mem_normalizer_of_conj_mem fun w hw => by
    rw [mem_centralizer_iff.1 (h.W_le_centralizer_yamadaY₂ d hK hD hw) y hy, mul_inv_cancel_right]
    exact hw

theorem yamadaW₂_le_centralizer (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaW₂ d t ≤ centralizer (yamadaW₂ d t : Set G) := by
  have hWab := d.isElementaryAbelian.2.2.2
  have hWW : d.W ≤ centralizer (d.W : Set G) := fun x hx => mem_centralizer_iff.2 fun y hy =>
    congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : d.W) ⟨x, hx⟩)
  have hWY := h.W_le_centralizer_yamadaY₂ d hK hD
  have hYY : yamadaY₂ d t ≤ centralizer (yamadaY₂ d t : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun y hy => h.yamadaY₂_mul_comm d hK hD hy hx
  exact sup_le ((Subgroup.le_centralizer_iff).2 (sup_le hWW ((Subgroup.le_centralizer_iff).1 hWY)))
    ((Subgroup.le_centralizer_iff).2 (sup_le hWY hYY))

theorem yamadaW₂_mul_self (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {a : G}
    (ha : a ∈ yamadaW₂ d t) : a * a = 1 := by
  obtain ⟨w, hw, y, hy, rfl⟩ :=
    Common.exists_mul_of_le_normalizer (h.yamadaY₂_le_normalizer_W d hK hD) a ha
  have hWab := d.isElementaryAbelian.2.2.2
  have hw2 : w * w = 1 := by
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := d.W) w hw
  have hwy : y * w = w * y := mem_centralizer_iff.1 (h.W_le_centralizer_yamadaY₂ d hK hD hw) y hy
  calc w * y * (w * y) = w * (y * w) * y := by group
    _ = w * (w * y) * y := by rw [hwy]
    _ = (w * w) * (y * y) := by group
    _ = 1 := by rw [hw2, h.yamadaY₂_mul_self hW d hK hD hy, one_mul]

theorem yamadaW₂_inf_centralizer (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaW₂ d t ⊓ centralizer ({t} : Set G) = d.W := by
  have hWC : d.W ≤ centralizer ({t} : Set G) := (d.image_le _).trans h.L_le_centralizer
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left hWC)
  obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨w, hw, y, hy, rfl⟩ :=
    Common.exists_mul_of_le_normalizer (h.yamadaY₂_le_normalizer_W d hK hD) x hx₁
  have hyC : y ∈ centralizer ({t} : Set G) := by
    have := mul_mem (inv_mem (hWC hw)) hx₂
    rwa [inv_mul_cancel_left] at this
  have hyY : y ∈ d.Y := by
    rw [← h.yamadaY₂_inf_centralizer d hK hD]
    exact Subgroup.mem_inf.2 ⟨hy, hyC⟩
  exact mul_mem hw (d.inclusions.2.2.1 hyY)

theorem card_yamadaW₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : Nat.card (yamadaW₂ d t) = Nat.card K ^ 5 := by
  have h1 := Common.card_sup_mul_card_inf_eq (h.yamadaY₂_le_normalizer_W d hK hD)
  rw [h.W_inf_yamadaY₂ d hK hD, d.cards.2.1, d.cards.2.2.2.1, h.card_yamadaY₂ d hK hD] at h1
  have hq : 0 < Nat.card K ^ 2 := by
    have : 0 < Nat.card K := Nat.card_pos
    positivity
  have h2 : Nat.card (yamadaW₂ d t) * Nat.card K ^ 2 = Nat.card K ^ 5 * Nat.card K ^ 2 := by
    rw [yamadaW₂, h1]
    ring
  exact Nat.eq_of_mul_eq_mul_right hq h2

theorem t_mem_normalizer_yamadaW₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : t ∈ normalizer (yamadaW₂ d t : Set G) ∧ t ∉ yamadaW₂ d t := by
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  refine ⟨mem_normalizer_sup (mem_normalizer_of_conj_mem fun x hx => ?_)
    (h.yamadaL₂_le_normalizer_yamadaY₂ d hK hD htL₂), fun ht => ?_⟩
  · rw [← mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hx)),
      mul_inv_cancel_right]
    exact hx
  · have := (h.yamadaW₂_inf_centralizer d hK hD).le
      (Subgroup.mem_inf.2 ⟨ht, mem_centralizer_singleton_iff.2 rfl⟩)
    exact h.t_not_mem_L (d.image_le _ this)

theorem conj_t_not_mem_yamadaW₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) (g : G) :
    g * t * g⁻¹ ∉ yamadaW₂ d t := by
  have h4K : 4 ≤ Nat.card K := hK ▸ h.four_le
  intro hg
  have hc := h.yamadaW₂_le_centralizer d hK hD
  set E := (yamadaW₂ d t).map (MulAut.conj g⁻¹).toMonoidHom with hEdef
  have hmem : ∀ x ∈ E, ∃ w ∈ yamadaW₂ d t, x = g⁻¹ * w * g := fun x hx => by
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hx
    exact ⟨w, hw, by simp⟩
  have hEC : E ≤ centralizer ({t} : Set G) := fun x hx => by
    obtain ⟨w, hw, rfl⟩ := hmem x hx
    rw [mem_centralizer_singleton_iff]
    have hwt : (g * t * g⁻¹) * w = w * (g * t * g⁻¹) := mem_centralizer_iff.1 (hc hw) _ hg
    calc g⁻¹ * w * g * t = g⁻¹ * (w * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * w) * g := by rw [hwt]
      _ = t * (g⁻¹ * w * g) := by group
  have hEab : IsElemAbelian 2 E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨u, hu, hua⟩ := hmem a a.2
      obtain ⟨v, hv, hvb⟩ := hmem b b.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hua, hvb]
      have huv : u * v = v * u := mem_centralizer_iff.1 (hc hv) u hu
      calc g⁻¹ * u * g * (g⁻¹ * v * g) = g⁻¹ * (u * v) * g := by group
        _ = g⁻¹ * (v * u) * g := by rw [huv]
        _ = g⁻¹ * v * g * (g⁻¹ * u * g) := by group
    · obtain ⟨u, hu, rfl⟩ := hmem x hx
      rw [sq, show g⁻¹ * u * g * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g by group,
        h.yamadaW₂_mul_self hW d hK hD hu, mul_one, inv_mul_cancel]
  have hcard : Nat.card E = Nat.card K ^ 5 := by
    rw [hEdef, card_map_conj, h.card_yamadaW₂ d hK hD]
  obtain ⟨h1, h2⟩ := h.card_le_of_isElemAbelian d hK hEC hEab
  rw [hcard] at h1
  have h3 : Nat.card K ^ 5 ≤ 2 * Nat.card K ^ 3 := h1.trans (Nat.mul_le_mul_left 2 h2)
  have h4 : 2 * Nat.card K ^ 3 < Nat.card K ^ 5 := by
    have : 2 < Nat.card K ^ 2 := by nlinarith
    calc 2 * Nat.card K ^ 3 < Nat.card K ^ 2 * Nat.card K ^ 3 :=
          Nat.mul_lt_mul_of_pos_right this (by positivity)
      _ = Nat.card K ^ 5 := by ring
  omega

theorem normalizer_yamadaV₂_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    normalizer (yamadaV₂ d t : Set G) ≤ normalizer (yamadaW₂ d t : Set G) ∧
      normalizer (yamadaV₂ d t : Set G) ≤ normalizer ((d.W ⊔ zpowers t : Subgroup G) : Set G) ∧
      normalizer (yamadaV₂ d t : Set G) ≤ normalizer (d.W : Set G) := by
  have h4K : 4 ≤ Nat.card K := hK ▸ h.four_le
  have htt := h.t_mul_t
  obtain ⟨htN, htW₂⟩ := h.t_mem_normalizer_yamadaW₂ d hK hD
  have hab : ∀ a ∈ yamadaW₂ d t, ∀ b ∈ yamadaW₂ d t, a * b = b * a := fun a ha b hb =>
    mem_centralizer_iff.1 (h.yamadaW₂_le_centralizer d hK hD hb) a ha
  have hcard : 2 * Nat.card (yamadaW₂ d t ⊓ centralizer ({t} : Set G) : Subgroup G) <
      Nat.card (yamadaW₂ d t) := by
    rw [h.yamadaW₂_inf_centralizer d hK hD, d.cards.2.2.2.1, h.card_yamadaW₂ d hK hD]
    have hq : 2 < Nat.card K ^ 2 := by nlinarith
    calc 2 * Nat.card K ^ 3 < Nat.card K ^ 2 * Nat.card K ^ 3 :=
          Nat.mul_lt_mul_of_pos_right hq (by positivity)
      _ = Nat.card K ^ 5 := by ring
  have h1 : normalizer (yamadaV₂ d t : Set G) ≤ normalizer (yamadaW₂ d t : Set G) :=
    normalizer_sup_zpowers_le (A := yamadaW₂ d t) htt htN hab hcard
  have h2 : normalizer (yamadaV₂ d t : Set G) ≤
      normalizer ((d.W ⊔ zpowers t : Subgroup G) : Set G) := by
    have := normalizer_sup_zpowers_le_inf (A := yamadaW₂ d t) htt htN htW₂ hab
      (fun a ha => h.yamadaW₂_mul_self hW d hK hD ha) hcard
    rwa [h.yamadaW₂_inf_centralizer d hK hD] at this
  have hWeq : yamadaW₂ d t ⊓ (d.W ⊔ zpowers t) = d.W := by
    refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left le_sup_left)
    obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
    rcases (h.mem_sup_zpowers_iff (d.image_le _)).1 hx₂ with h3 | h3
    · exact h3
    · exfalso
      have := mul_mem ((le_sup_left : d.W ≤ yamadaW₂ d t) h3) (inv_mem hx₁)
      rw [mul_inv_cancel_right] at this
      exact htW₂ this
  refine ⟨h1, h2, fun g hg => ?_⟩
  rw [← hWeq]
  exact Common.mem_normalizer_inf (h1 hg) (h2 hg)

theorem crossed_mem_W (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {g : G}
    (hg : g ∈ normalizer (yamadaV₂ d t : Set G)) : t * g * t * g⁻¹ ∈ d.W := by
  obtain ⟨-, h2, h3⟩ := h.normalizer_yamadaV₂_le hW d hK hD
  have hgt : g * t * g⁻¹ ∈ d.W ⊔ zpowers t :=
    (mem_normalizer_iff.1 (h2 hg) t).1 (mem_sup_right (mem_zpowers t))
  rcases (h.mem_sup_zpowers_iff (d.image_le _)).1 hgt with h4 | h4
  · exfalso
    have := (mem_normalizer_iff.1 (inv_mem (h3 hg)) _).1 h4
    rw [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at this
    exact h.t_not_mem_L (d.image_le _ this)
  · rwa [show t * g * t * g⁻¹ = t * (g * t * g⁻¹) by group]

theorem centralizer_inf_normalizer_Y_le_W (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G) ≤ normalizer (d.W : Set G) ∧
      centralizer ({t} : Set G) ⊓ normalizer (d.W : Set G) ≤ normalizer (d.Y : Set G) := by
  obtain ⟨hY, hW', -⟩ := d.yamada_3_13_3_G
  constructor
  · intro c hc
    obtain ⟨hct, hcY⟩ := Subgroup.mem_inf.1 hc
    obtain ⟨g, hg, x, hx, rfl⟩ := h.exists_mul_of_mem_normalizer_Y d hK hct hcY
    have hgW : g ∈ L ⊓ normalizer (d.W : Set G) := by
      rw [hW', ← hY]
      exact hg
    exact mul_mem (Subgroup.mem_inf.1 hgW).2
      (Subgroup.mem_inf.1 ((h.centralizer_inf_normalizer_F_le d hK hD).2 hx)).1
  · intro c hc
    obtain ⟨hct, hcW⟩ := Subgroup.mem_inf.1 hc
    obtain ⟨g, hgL, hg⟩ :=
      h.exists_mem_L_inv_mul_mem_normalizer d hK (h.centralizer_le_normalizer hct)
    have hxW : g⁻¹ * c ∈ normalizer (d.W : Set G) :=
      hg (Model.W K) fun k => Model.map_entrywise_W _
    have hxY : g⁻¹ * c ∈ normalizer (d.Y : Set G) :=
      hg (Model.Y K) fun k => Model.map_entrywise_Y _
    have hgW : g ∈ L ⊓ normalizer (d.W : Set G) := by
      refine Subgroup.mem_inf.2 ⟨hgL, ?_⟩
      have := mul_mem hcW (inv_mem hxW)
      rwa [show c * (g⁻¹ * c)⁻¹ = g by group] at this
    rw [hW', ← hY] at hgW
    rw [show c = g * (g⁻¹ * c) by group]
    exact mul_mem (Subgroup.mem_inf.1 hgW).2 hxY

theorem normalizer_tY_le (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (d.W : Set G) ∧
      normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (yamadaY₂ d t : Set G) ∧
      normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (yamadaV₂ d t : Set G) := by
  have hY₂ : normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer (yamadaY₂ d t : Set G) := fun g hg =>
    (h.normalizer_yamadaL₂_le d hK hD).2 (le_normalizer_yamadaL₂ d t hg)
  have hL₂W : yamadaL₂ d t ≤ normalizer (d.W : Set G) := by
    rw [h.yamadaL₂_eq_sup d hK hD]
    refine sup_le (sup_le (fun m hm => ?_) (h.yamadaY₂_le_normalizer_W d hK hD)) ?_
    · have : m ∈ L ⊓ normalizer (d.W : Set G) := by
        rw [(d.yamada_3_13_3_G).2.1]
        exact mem_sup_left hm
      exact (Subgroup.mem_inf.1 this).2
    · rw [zpowers_le]
      exact mem_normalizer_of_conj_mem fun x hx => by
        rw [← mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hx)),
          mul_inv_cancel_right]
        exact hx
  have hW : normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (d.W : Set G) := by
    rw [(h.yamada_5_5_1 d hK).2.1]
    exact sup_le hL₂W (h.centralizer_inf_normalizer_Y_le_W d hK hD).1
  refine ⟨hW, hY₂, fun g hg => ?_⟩
  refine mem_normalizer_sup_zpowers_of_conj_mem
    (A := yamadaW₂ d t) (mem_normalizer_sup (hW hg) (hY₂ hg)) ?_
  have := (mem_normalizer_iff.1 hg t).1 (mem_sup_right (mem_zpowers t))
  exact sup_le_sup_right ((d.inclusions.2.2.1).trans le_sup_left) _ this

omit [Finite G] [Finite K] in
theorem yamadaV₂_eq (d : G2Data L K) (t : G) :
    yamadaV₂ d t = (yamadaW₁ d t ⊔ zpowers t) ⊔ yamadaY₂ d t := by
  have hU₁Y₂ := yamadaU₁_le_yamadaY₂ d t
  show (d.W ⊔ yamadaY₂ d t) ⊔ zpowers t = ((d.W ⊔ yamadaU₁ d t) ⊔ zpowers t) ⊔ yamadaY₂ d t
  apply le_antisymm
  · exact sup_le (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left)) le_sup_right)
      (le_sup_right.trans le_sup_left)
  · exact sup_le (sup_le (sup_le (le_sup_left.trans le_sup_left)
      (hU₁Y₂.trans (le_sup_right.trans le_sup_left))) le_sup_right)
      (le_sup_right.trans le_sup_left)

theorem yamadaR₃star_le_normalizer (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaR₃star d t ≤ normalizer (yamadaV₂ d t : Set G) ⊓ normalizer (yamadaY₂ d t : Set G) := by
  obtain ⟨-, -, hR₅, hR₅eq, -⟩ := h.yamada_5_21_2 hW d hK hD
  obtain ⟨hRE, hEF, hFY⟩ := h.normalizer_yamadaR₂_le d hK hD
  intro g hg
  have hg₅ : g ∈ yamadaR₅star d t := by
    rw [hR₅eq]
    exact mem_sup_left hg
  have hgY₂ : g ∈ normalizer (yamadaY₂ d t : Set G) := hFY (hEF (hRE (hR₅ hg₅)))
  refine Subgroup.mem_inf.2 ⟨?_, hgY₂⟩
  rw [yamadaV₂_eq]
  exact mem_normalizer_sup (Subgroup.mem_inf.1 hg).2 hgY₂

theorem exists_conj_t_eq_mul_of_mem_W (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {w : G} (hw : w ∈ d.W) :
    ∃ g ∈ yamadaR₃star d t, ∃ l ∈ yamadaL₂ d t, g * l * t * (g * l)⁻¹ = t * w := by
  obtain ⟨-, h1⟩ := (h.yamada_5_21_1 d hK hD).1
  obtain ⟨g, hg, u, hu, e⟩ := h1 w (mem_sup_left hw)
  obtain ⟨hgV, hgY₂⟩ := Subgroup.mem_inf.1 (h.yamadaR₃star_le_normalizer hW d hK hD hg)
  have hκe : t * g * t * g⁻¹ = w * u := by
    rw [show t * g * t * g⁻¹ = t * (g * t * g⁻¹) by group, e,
      show t * (t * w * u) = (t * t) * w * u by group, h.t_mul_t, one_mul]
  have hwu : w * u ∈ d.W := by
    rw [← hκe]
    exact h.crossed_mem_W hW d hK hD hgV
  have huW : u ∈ d.W := by
    have := mul_mem (inv_mem hw) hwu
    rwa [inv_mul_cancel_left] at this
  have huY : u ∈ d.Y := by
    rw [← h.W_inf_yamadaY₂ d hK hD]
    exact Subgroup.mem_inf.2 ⟨huW, yamadaU₁_le_yamadaY₂ d t hu⟩
  have hgY : g ∈ normalizer (d.Y : Set G) := by
    rw [← h.W_inf_yamadaY₂ d hK hD]
    exact Common.mem_normalizer_inf ((h.normalizer_yamadaV₂_le hW d hK hD).2.2 hgV) hgY₂
  have hy : g⁻¹ * u⁻¹ * g ∈ d.Y := by
    have := (mem_normalizer_iff.1 (inv_mem hgY) u⁻¹).1 (inv_mem huY)
    rwa [inv_inv] at this
  obtain ⟨l₀, hl₀, el⟩ := (h.two_core_L₂ d hK).2.2.1 _ hy
  refine ⟨g, hg, l₀⁻¹, inv_mem hl₀, ?_⟩
  calc g * l₀⁻¹ * t * (g * l₀⁻¹)⁻¹ = g * (l₀⁻¹ * t * l₀) * g⁻¹ := by group
    _ = g * (t * (g⁻¹ * u⁻¹ * g)) * g⁻¹ := by rw [el]
    _ = (g * t * g⁻¹) * u⁻¹ := by group
    _ = t * w * u * u⁻¹ := by rw [e]
    _ = t * w := by group

theorem exists_mul_mem_centralizer (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {g : G}
    (hg : t * g * t * g⁻¹ ∈ d.W) :
    ∃ x ∈ normalizer (yamadaV₂ d t : Set G) ⊓ normalizer (yamadaY₂ d t : Set G),
      x⁻¹ * g ∈ centralizer ({t} : Set G) := by
  obtain ⟨x, hx, l, hl, e⟩ := h.exists_conj_t_eq_mul_of_mem_W hW d hK hD hg
  obtain ⟨hxV, hxY₂⟩ := Subgroup.mem_inf.1 (h.yamadaR₃star_le_normalizer hW d hK hD hx)
  obtain ⟨-, hNY₂, hNV₂⟩ := h.normalizer_tY_le d hK hD
  have hlN := yamadaL₂_le d t hl
  refine ⟨x * l, Subgroup.mem_inf.2 ⟨mul_mem hxV (hNV₂ hlN), mul_mem hxY₂ (hNY₂ hlN)⟩, ?_⟩
  have e' : g * t * g⁻¹ = x * l * t * (x * l)⁻¹ := by
    rw [e]
    calc g * t * g⁻¹ = (t * t) * (g * t * g⁻¹) := by rw [h.t_mul_t, one_mul]
      _ = t * (t * g * t * g⁻¹) := by group
  rw [mem_centralizer_singleton_iff]
  calc (x * l)⁻¹ * g * t = (x * l)⁻¹ * (g * t * g⁻¹) * g := by group
    _ = (x * l)⁻¹ * (x * l * t * (x * l)⁻¹) * g := by rw [e']
    _ = t * ((x * l)⁻¹ * g) := by group

theorem normalizer_yamadaV₂_le_normalizer_yamadaY₂ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    normalizer (yamadaV₂ d t : Set G) ≤ normalizer (yamadaY₂ d t : Set G) := by
  intro g hg
  obtain ⟨x, hx, hc⟩ := h.exists_mul_mem_centralizer hW d hK hD (h.crossed_mem_W hW d hK hD hg)
  obtain ⟨hxV, hxY₂⟩ := Subgroup.mem_inf.1 hx
  have hcW := (h.normalizer_yamadaV₂_le hW d hK hD).2.2 (mul_mem (inv_mem hxV) hg)
  have hcY := (h.centralizer_inf_normalizer_Y_le_W d hK hD).2 (Subgroup.mem_inf.2 ⟨hc, hcW⟩)
  have hcY₂ := (h.normalizer_tY_le d hK hD).2.1
    (h.centralizer_inf_normalizer_Y_le d (Subgroup.mem_inf.2 ⟨hc, hcY⟩))
  have := mul_mem hxY₂ hcY₂
  rwa [mul_inv_cancel_left] at this

theorem normalizer_yamadaV₂_le_normalizer_Y (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    normalizer (yamadaV₂ d t : Set G) ≤ normalizer (d.Y : Set G) := fun g hg => by
  rw [← h.W_inf_yamadaY₂ d hK hD]
  exact Common.mem_normalizer_inf ((h.normalizer_yamadaV₂_le hW d hK hD).2.2 hg)
    (h.normalizer_yamadaV₂_le_normalizer_yamadaY₂ hW d hK hD hg)

theorem crossed_mem_Y_iff (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {g : G}
    (hg : g ∈ normalizer (yamadaV₂ d t : Set G)) :
    t * g * t * g⁻¹ ∈ d.Y ↔ g ∈ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) := by
  have hgY := h.normalizer_yamadaV₂_le_normalizer_Y hW d hK hD hg
  constructor
  · intro hκ
    refine mem_normalizer_sup_zpowers_of_conj_mem hgY ?_
    rw [h.conj_t_eq_mul_crossed g]
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hκ)
  · intro hgN
    have hgt := (mem_normalizer_iff.1 hgN t).1 (mem_sup_right (mem_zpowers t))
    rcases (h.mem_sup_zpowers_iff (d.image_le _)).1 hgt with h1 | h1
    · exfalso
      have := (mem_normalizer_iff.1 (inv_mem hgY) _).1 h1
      rw [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at this
      exact h.t_not_mem_L (d.image_le _ this)
    · rwa [show t * g * t * g⁻¹ = t * (g * t * g⁻¹) by group]

theorem inv_mul_mem_normalizer_tY (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {p z y : G}
    (hp : p ∈ normalizer (yamadaV₂ d t : Set G)) (hz : z ∈ normalizer (yamadaV₂ d t : Set G))
    (hy : y ∈ d.Y) (e : t * p * t * p⁻¹ = t * z * t * z⁻¹ * y) :
    p⁻¹ * z ∈ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) := by
  have hpY := h.normalizer_yamadaV₂_le_normalizer_Y hW d hK hD hp
  refine (h.crossed_mem_Y_iff hW d hK hD (mul_mem (inv_mem hp) hz)).1 ?_
  rw [h.crossed_mul' p⁻¹ z, h.crossed_inv' p, e, show p⁻¹ * (t * z * t * z⁻¹ * y)⁻¹ * p *
    (p⁻¹ * (t * z * t * z⁻¹) * p⁻¹⁻¹) = p⁻¹ * y⁻¹ * p by group]
  have := (mem_normalizer_iff.1 (inv_mem hpY) y⁻¹).1 (inv_mem hy)
  rwa [inv_inv] at this

theorem yamadaL₃_inf_le (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    yamadaL₃ d t ⊓ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ≤ yamadaL₂ d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
    (fun g hg => Common.mem_normalizer_inf (LieType.BorelTits.le_normalizer_pCoreOf 2 _
      ((h.normalizer_tY_le d hK hD).2.2 hg)) (Subgroup.le_normalizer hg))
    ((LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
