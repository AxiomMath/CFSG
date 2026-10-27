module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYTwenty

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section Defs

variable
  {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def yamadaR₄ (d : G2Data L K) (t : G) : Subgroup G :=
  pCoreOf 2 (normalizer (yamadaU₂ d t : Set G))

end Defs

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite G] [Finite K] in
theorem X_mul_comm (d : G2Data L K) {u v : G} (hu : u ∈ d.X) (hv : v ∈ d.X) : u * v = v * u := by
  have hXab := d.isElementaryAbelian.2.2.1
  exact congrArg Subtype.val (mul_comm' (⟨u, hu⟩ : d.X) ⟨v, hv⟩)

omit [Finite G] [Finite K] in
theorem X_mul_self (d : G2Data L K) {u : G} (hu : u ∈ d.X) : u * u = 1 := by
  have hXab := d.isElementaryAbelian.2.2.1
  rw [← sq]
  exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := d.X) u hu

omit [Finite K] in
theorem X_le_normalizer_Y (d : G2Data L K) : d.X ≤ normalizer (d.Y : Set G) := fun a ha =>
  mem_normalizer_of_conj_mem fun y hy => by
    rw [X_mul_comm d ha (d.inclusions.2.1 hy), mul_inv_cancel_right]
    exact hy

theorem X_inf_yamadaY₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.X ⊓ yamadaY₂ d t = d.Y := by
  obtain ⟨-, hYX, -⟩ := d.inclusions
  refine le_antisymm ?_ (le_inf hYX (h.Y_le_yamadaY₂ d hK hD))
  rw [← h.yamadaY₂_inf_centralizer d hK hD, inf_comm]
  exact inf_le_inf_left _ ((d.image_le _).trans h.L_le_centralizer)

theorem X_le_centralizer_yamadaY₂ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    d.X ≤ centralizer (yamadaY₂ d t : Set G) := by
  obtain ⟨-, -, -, hXF, -, -, hFM, -⟩ := d.inclusions
  exact (hXF.trans hFM).trans (h.M_le_centralizer_yamadaY₂ d hK hD)

theorem yamadaY₂_le_normalizer_X (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaY₂ d t ≤ normalizer (d.X : Set G) := fun y hy =>
  mem_normalizer_of_conj_mem fun w hw => by
    rw [mem_centralizer_iff.1 (h.X_le_centralizer_yamadaY₂ d hK hD hw) y hy, mul_inv_cancel_right]
    exact hw

theorem yamadaX₂_le_centralizer (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaX₂ d t ≤ centralizer (yamadaX₂ d t : Set G) := by
  have hXX : d.X ≤ centralizer (d.X : Set G) := fun x hx => mem_centralizer_iff.2 fun y hy =>
    X_mul_comm d hy hx
  have hXY := h.X_le_centralizer_yamadaY₂ d hK hD
  have hYY : yamadaY₂ d t ≤ centralizer (yamadaY₂ d t : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun y hy => h.yamadaY₂_mul_comm d hK hD hy hx
  exact sup_le ((Subgroup.le_centralizer_iff).2 (sup_le hXX ((Subgroup.le_centralizer_iff).1 hXY)))
    ((Subgroup.le_centralizer_iff).2 (sup_le hXY hYY))

theorem yamadaX₂_mul_self (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {a : G}
    (ha : a ∈ yamadaX₂ d t) : a * a = 1 := by
  obtain ⟨w, hw, y, hy, rfl⟩ :=
    Common.exists_mul_of_le_normalizer (h.yamadaY₂_le_normalizer_X d hK hD) a ha
  have hwy : y * w = w * y := mem_centralizer_iff.1 (h.X_le_centralizer_yamadaY₂ d hK hD hw) y hy
  calc w * y * (w * y) = w * (y * w) * y := by group
    _ = w * (w * y) * y := by rw [hwy]
    _ = (w * w) * (y * y) := by group
    _ = 1 := by rw [X_mul_self d hw, h.yamadaY₂_mul_self hW d hK hD hy, one_mul]

theorem yamadaX₂_inf_centralizer (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaX₂ d t ⊓ centralizer ({t} : Set G) = d.X := by
  have hXC : d.X ≤ centralizer ({t} : Set G) := (d.image_le _).trans h.L_le_centralizer
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left hXC)
  obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨w, hw, y, hy, rfl⟩ :=
    Common.exists_mul_of_le_normalizer (h.yamadaY₂_le_normalizer_X d hK hD) x hx₁
  have hyC : y ∈ centralizer ({t} : Set G) := by
    have := mul_mem (inv_mem (hXC hw)) hx₂
    rwa [inv_mul_cancel_left] at this
  have hyY : y ∈ d.Y := by
    rw [← h.yamadaY₂_inf_centralizer d hK hD]
    exact Subgroup.mem_inf.2 ⟨hy, hyC⟩
  exact mul_mem hw (d.inclusions.2.1 hyY)

theorem card_yamadaX₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : Nat.card (yamadaX₂ d t) = Nat.card K ^ 5 := by
  have h1 := Common.card_sup_mul_card_inf_eq (h.yamadaY₂_le_normalizer_X d hK hD)
  rw [h.X_inf_yamadaY₂ d hK hD, d.cards.2.1, d.cards.2.2.1, h.card_yamadaY₂ d hK hD] at h1
  have hq : 0 < Nat.card K ^ 2 := by
    have : 0 < Nat.card K := Nat.card_pos
    positivity
  have h2 : Nat.card (yamadaX₂ d t) * Nat.card K ^ 2 = Nat.card K ^ 5 * Nat.card K ^ 2 := by
    rw [yamadaX₂, h1]
    ring
  exact Nat.eq_of_mul_eq_mul_right hq h2

theorem t_mem_normalizer_yamadaX₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : t ∈ normalizer (yamadaX₂ d t : Set G) ∧ t ∉ yamadaX₂ d t := by
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  refine ⟨mem_normalizer_sup (mem_normalizer_of_conj_mem fun x hx => ?_)
    (h.yamadaL₂_le_normalizer_yamadaY₂ d hK hD htL₂), fun ht => ?_⟩
  · rw [← mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hx)),
      mul_inv_cancel_right]
    exact hx
  · have := (h.yamadaX₂_inf_centralizer d hK hD).le
      (Subgroup.mem_inf.2 ⟨ht, mem_centralizer_singleton_iff.2 rfl⟩)
    exact h.t_not_mem_L (d.image_le _ this)

theorem conj_t_not_mem_of_card (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (_hD : h.DoublingFacts d) {A : Subgroup G} (hAc : A ≤ centralizer (A : Set G))
    (hAe : ∀ a ∈ A, a * a = 1) (hAcard : Nat.card A = Nat.card K ^ 5) (g : G) :
    g * t * g⁻¹ ∉ A := by
  have h4K : 4 ≤ Nat.card K := hK ▸ h.four_le
  intro hg
  set E := A.map (MulAut.conj g⁻¹).toMonoidHom with hEdef
  have hmem : ∀ x ∈ E, ∃ w ∈ A, x = g⁻¹ * w * g := fun x hx => by
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hx
    exact ⟨w, hw, by simp⟩
  have hEC : E ≤ centralizer ({t} : Set G) := fun x hx => by
    obtain ⟨w, hw, rfl⟩ := hmem x hx
    rw [mem_centralizer_singleton_iff]
    have hwt : (g * t * g⁻¹) * w = w * (g * t * g⁻¹) := mem_centralizer_iff.1 (hAc hw) _ hg
    calc g⁻¹ * w * g * t = g⁻¹ * (w * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * w) * g := by rw [hwt]
      _ = t * (g⁻¹ * w * g) := by group
  have hEab : IsElemAbelian 2 E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨u, hu, hua⟩ := hmem a a.2
      obtain ⟨v, hv, hvb⟩ := hmem b b.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hua, hvb]
      have huv : u * v = v * u := mem_centralizer_iff.1 (hAc hv) u hu
      calc g⁻¹ * u * g * (g⁻¹ * v * g) = g⁻¹ * (u * v) * g := by group
        _ = g⁻¹ * (v * u) * g := by rw [huv]
        _ = g⁻¹ * v * g * (g⁻¹ * u * g) := by group
    · obtain ⟨u, hu, rfl⟩ := hmem x hx
      rw [sq, show g⁻¹ * u * g * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g by group, hAe u hu, mul_one,
        inv_mul_cancel]
  have hcard : Nat.card E = Nat.card K ^ 5 := by
    rw [hEdef, card_map_conj, hAcard]
  obtain ⟨h1, h2⟩ := h.card_le_of_isElemAbelian d hK hEC hEab
  rw [hcard] at h1
  have h3 : Nat.card K ^ 5 ≤ 2 * Nat.card K ^ 3 := h1.trans (Nat.mul_le_mul_left 2 h2)
  have h4 : 2 * Nat.card K ^ 3 < Nat.card K ^ 5 := by
    have : 2 < Nat.card K ^ 2 := by nlinarith
    calc 2 * Nat.card K ^ 3 < Nat.card K ^ 2 * Nat.card K ^ 3 :=
          Nat.mul_lt_mul_of_pos_right this (by positivity)
      _ = Nat.card K ^ 5 := by ring
  omega

theorem conj_t_not_mem_yamadaX₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) (g : G) :
    g * t * g⁻¹ ∉ yamadaX₂ d t :=
  h.conj_t_not_mem_of_card d hK hD (h.yamadaX₂_le_centralizer d hK hD)
    (fun _ ha => h.yamadaX₂_mul_self hW d hK hD ha) (h.card_yamadaX₂ d hK hD) g

theorem normalizer_yamadaU₂_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    normalizer (yamadaU₂ d t : Set G) ≤ normalizer (yamadaX₂ d t : Set G) ∧
      normalizer (yamadaU₂ d t : Set G) ≤ normalizer ((d.X ⊔ zpowers t : Subgroup G) : Set G) ∧
      normalizer (yamadaU₂ d t : Set G) ≤ normalizer (d.X : Set G) := by
  have h4K : 4 ≤ Nat.card K := hK ▸ h.four_le
  have htt := h.t_mul_t
  obtain ⟨htN, htX₂⟩ := h.t_mem_normalizer_yamadaX₂ d hK hD
  have hab : ∀ a ∈ yamadaX₂ d t, ∀ b ∈ yamadaX₂ d t, a * b = b * a := fun a ha b hb =>
    mem_centralizer_iff.1 (h.yamadaX₂_le_centralizer d hK hD hb) a ha
  have hcard : 2 * Nat.card (yamadaX₂ d t ⊓ centralizer ({t} : Set G) : Subgroup G) <
      Nat.card (yamadaX₂ d t) := by
    rw [h.yamadaX₂_inf_centralizer d hK hD, d.cards.2.2.1, h.card_yamadaX₂ d hK hD]
    have hq : 2 < Nat.card K ^ 2 := by nlinarith
    calc 2 * Nat.card K ^ 3 < Nat.card K ^ 2 * Nat.card K ^ 3 :=
          Nat.mul_lt_mul_of_pos_right hq (by positivity)
      _ = Nat.card K ^ 5 := by ring
  have h1 : normalizer (yamadaU₂ d t : Set G) ≤ normalizer (yamadaX₂ d t : Set G) :=
    normalizer_sup_zpowers_le (A := yamadaX₂ d t) htt htN hab hcard
  have h2 : normalizer (yamadaU₂ d t : Set G) ≤
      normalizer ((d.X ⊔ zpowers t : Subgroup G) : Set G) := by
    have := normalizer_sup_zpowers_le_inf (A := yamadaX₂ d t) htt htN htX₂ hab
      (fun a ha => h.yamadaX₂_mul_self hW d hK hD ha) hcard
    rwa [h.yamadaX₂_inf_centralizer d hK hD] at this
  have hXeq : yamadaX₂ d t ⊓ (d.X ⊔ zpowers t) = d.X := by
    refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left le_sup_left)
    obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
    rcases (h.mem_sup_zpowers_iff (d.image_le _)).1 hx₂ with h3 | h3
    · exact h3
    · exfalso
      have := mul_mem ((le_sup_left : d.X ≤ yamadaX₂ d t) h3) (inv_mem hx₁)
      rw [mul_inv_cancel_right] at this
      exact htX₂ this
  refine ⟨h1, h2, fun g hg => ?_⟩
  rw [← hXeq]
  exact Common.mem_normalizer_inf (h1 hg) (h2 hg)

theorem crossed_mem_X (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {g : G}
    (hg : g ∈ normalizer (yamadaU₂ d t : Set G)) : t * g * t * g⁻¹ ∈ d.X := by
  obtain ⟨-, h2, h3⟩ := h.normalizer_yamadaU₂_le hW d hK hD
  have hgt : g * t * g⁻¹ ∈ d.X ⊔ zpowers t :=
    (mem_normalizer_iff.1 (h2 hg) t).1 (mem_sup_right (mem_zpowers t))
  rcases (h.mem_sup_zpowers_iff (d.image_le _)).1 hgt with h4 | h4
  · exfalso
    have := (mem_normalizer_iff.1 (inv_mem (h3 hg)) _).1 h4
    rw [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at this
    exact h.t_not_mem_L (d.image_le _ this)
  · rwa [show t * g * t * g⁻¹ = t * (g * t * g⁻¹) by group]

theorem centralizer_inf_normalizer_X_eq (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    centralizer ({t} : Set G) ⊓ normalizer (d.X : Set G) =
      centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) := by
  obtain ⟨hX, -, hS⟩ := d.yamada_3_13_1_G
  refine le_antisymm (fun c hc => ?_) (le_inf inf_le_left fun c hc =>
    (Subgroup.mem_inf.1 ((h.centralizer_inf_normalizer_F_le d hK hD).2 hc)).2)
  obtain ⟨hct, hcX⟩ := Subgroup.mem_inf.1 hc
  obtain ⟨g, hgL, hg⟩ :=
    h.exists_mem_L_inv_mul_mem_normalizer d hK (h.centralizer_le_normalizer hct)
  have hxX : g⁻¹ * c ∈ normalizer (d.X : Set G) :=
    hg (Model.X K) fun k => Model.map_entrywise_X _
  have hxS : g⁻¹ * c ∈ normalizer (d.S : Set G) :=
    hg (Model.S K) fun k => Model.map_entrywise_S _
  have hgX : g ∈ L ⊓ normalizer (d.X : Set G) := by
    refine Subgroup.mem_inf.2 ⟨hgL, ?_⟩
    have := mul_mem hcX (inv_mem hxX)
    rwa [show c * (g⁻¹ * c)⁻¹ = g by group] at this
  rw [hX, ← hS] at hgX
  refine Subgroup.mem_inf.2 ⟨hct, ?_⟩
  rw [show c = g * (g⁻¹ * c) by group]
  exact mul_mem (Subgroup.mem_inf.1 hgX).2 hxS

theorem le_normalizer_yamadaU₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤ normalizer (yamadaU₂ d t : Set G) ∧
      yamadaL₂ d t ≤ normalizer (yamadaU₂ d t : Set G) := by
  obtain ⟨hX, -, hS⟩ := d.yamada_3_13_1_G
  obtain ⟨hRE, hEF, hFY⟩ := h.normalizer_yamadaR₂_le d hK hD
  obtain ⟨hNR₂, -⟩ := h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK hD
  have hY₂L : normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer (yamadaY₂ d t : Set G) := fun g hg =>
    (h.normalizer_yamadaL₂_le d hK hD).2 (le_normalizer_yamadaL₂ d t hg)
  have hLX : yamadaL₂ d t ≤ normalizer (d.X : Set G) := by
    rw [h.yamadaL₂_eq_sup d hK hD]
    refine sup_le (sup_le (fun m hm => ?_) (h.yamadaY₂_le_normalizer_X d hK hD)) ?_
    · have : m ∈ L ⊓ normalizer (d.X : Set G) := by
        rw [hX, ← hS]
        exact Subgroup.mem_inf.2 ⟨d.image_le _ (d.inclusions.2.2.2.2.2.2.2.2.1 hm),
          Subgroup.le_normalizer (d.inclusions.2.2.2.2.2.2.2.2.1 hm)⟩
      exact (Subgroup.mem_inf.1 this).2
    · rw [zpowers_le]
      exact mem_normalizer_of_conj_mem fun x hx => by
        rw [← mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hx)),
          mul_inv_cancel_right]
        exact hx
  refine ⟨fun c hc => ?_, fun l hl => ?_⟩
  · have hcX := (Subgroup.mem_inf.1 ((h.centralizer_inf_normalizer_F_le d hK hD).2 hc)).2
    have hcY₂ := hFY (hEF (hRE (hNR₂ hc)))
    exact mem_normalizer_sup (mem_normalizer_sup hcX hcY₂)
      (mem_normalizer_zpowers (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hc).1))
  · have hlN := yamadaL₂_le d t hl
    refine mem_normalizer_sup_zpowers_of_conj_mem
      (A := yamadaX₂ d t) (mem_normalizer_sup (hLX hl) (hY₂L hlN)) ?_
    have := (mem_normalizer_iff.1 hlN t).1 (mem_sup_right (mem_zpowers t))
    exact sup_le_sup_right ((d.inclusions.2.1).trans le_sup_left) _ this

omit [Finite G] [Finite K] in
theorem yamadaU₂_eq (d : G2Data L K) (t : G) :
    yamadaU₂ d t = (yamadaX₁ d t ⊔ zpowers t) ⊔ yamadaY₂ d t := by
  have hU₁Y₂ := yamadaU₁_le_yamadaY₂ d t
  show (d.X ⊔ yamadaY₂ d t) ⊔ zpowers t = ((d.X ⊔ yamadaU₁ d t) ⊔ zpowers t) ⊔ yamadaY₂ d t
  apply le_antisymm
  · exact sup_le (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left)) le_sup_right)
      (le_sup_right.trans le_sup_left)
  · exact sup_le (sup_le (sup_le (le_sup_left.trans le_sup_left)
      (hU₁Y₂.trans (le_sup_right.trans le_sup_left))) le_sup_right)
      (le_sup_right.trans le_sup_left)

theorem yamadaR₄star_le_normalizer (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaR₄star d t ≤ normalizer (yamadaU₂ d t : Set G) ⊓ normalizer (yamadaY₂ d t : Set G) ∧
      yamadaR₄star d t ≤ normalizer (yamadaR₂ d t : Set G) := by
  obtain ⟨-, -, hR₅, hR₅eq, -⟩ := h.yamada_5_21_2 hW d hK hD
  obtain ⟨hRE, hEF, hFY⟩ := h.normalizer_yamadaR₂_le d hK hD
  have hR₄R₂ : yamadaR₄star d t ≤ normalizer (yamadaR₂ d t : Set G) := fun g hg => by
    have hg₅ : g ∈ yamadaR₅star d t := by
      rw [hR₅eq]
      exact mem_sup_right hg
    exact hR₅ hg₅
  refine ⟨fun g hg => ?_, hR₄R₂⟩
  have hgY₂ : g ∈ normalizer (yamadaY₂ d t : Set G) := hFY (hEF (hRE (hR₄R₂ hg)))
  refine Subgroup.mem_inf.2 ⟨?_, hgY₂⟩
  rw [yamadaU₂_eq]
  exact mem_normalizer_sup (Subgroup.mem_inf.1 hg).2 hgY₂

theorem exists_conj_t_eq_mul_of_mem_X (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {x : G} (hx : x ∈ d.X) :
    ∃ g ∈ yamadaR₄star d t, g * t * g⁻¹ = t * x := by
  obtain ⟨hR₂eq, -⟩ := h.yamada_5_21_2 hW d hK hD
  have hL₂R₄ : yamadaL₂ d t ≤ yamadaR₄star d t := fun l hl => by
    have : l ∈ yamadaR₂ d t := mem_sup_left hl
    rw [hR₂eq] at this
    exact (Subgroup.mem_inf.1 this).2
  obtain ⟨-, h1⟩ := (h.yamada_5_21_1 d hK hD).2.1
  obtain ⟨g, hg, u, hu, e⟩ := h1 x (mem_sup_left hx)
  obtain ⟨hgU, hgY₂⟩ := Subgroup.mem_inf.1 ((h.yamadaR₄star_le_normalizer hW d hK hD).1 hg)
  have hκe : t * g * t * g⁻¹ = x * u := by
    rw [show t * g * t * g⁻¹ = t * (g * t * g⁻¹) by group, e,
      show t * (t * x * u) = (t * t) * x * u by group, h.t_mul_t, one_mul]
  have hxu : x * u ∈ d.X := by
    rw [← hκe]
    exact h.crossed_mem_X hW d hK hD hgU
  have huX : u ∈ d.X := by
    have := mul_mem (inv_mem hx) hxu
    rwa [inv_mul_cancel_left] at this
  have huY : u ∈ d.Y := by
    rw [← h.X_inf_yamadaY₂ d hK hD]
    exact Subgroup.mem_inf.2 ⟨huX, yamadaU₁_le_yamadaY₂ d t hu⟩
  have hgY : g ∈ normalizer (d.Y : Set G) := by
    rw [← h.X_inf_yamadaY₂ d hK hD]
    exact Common.mem_normalizer_inf ((h.normalizer_yamadaU₂_le hW d hK hD).2.2 hgU) hgY₂
  have hy : g⁻¹ * u⁻¹ * g ∈ d.Y := by
    have := (mem_normalizer_iff.1 (inv_mem hgY) u⁻¹).1 (inv_mem huY)
    rwa [inv_inv] at this
  obtain ⟨l₀, hl₀, el⟩ := (h.two_core_L₂ d hK).2.2.1 _ hy
  refine ⟨g * l₀⁻¹, mul_mem hg (hL₂R₄ (inv_mem hl₀)), ?_⟩
  calc g * l₀⁻¹ * t * (g * l₀⁻¹)⁻¹ = g * (l₀⁻¹ * t * l₀) * g⁻¹ := by group
    _ = g * (t * (g⁻¹ * u⁻¹ * g)) * g⁻¹ := by rw [el]
    _ = (g * t * g⁻¹) * u⁻¹ := by group
    _ = t * x * u * u⁻¹ := by rw [e]
    _ = t * x := by group

theorem exists_mul_of_mem_normalizer_yamadaU₂ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d)
    {g : G} (hg : t * g * t * g⁻¹ ∈ d.X)
    (hgN : g ∈ normalizer ((d.X ⊔ zpowers t : Subgroup G) : Set G)) :
    ∃ x ∈ yamadaR₄star d t, x⁻¹ * g ∈ centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) := by
  obtain ⟨x, hx, e⟩ := h.exists_conj_t_eq_mul_of_mem_X hW d hK hD hg
  have hxU := (Subgroup.mem_inf.1 ((h.yamadaR₄star_le_normalizer hW d hK hD).1 hx)).1
  have hc : x⁻¹ * g ∈ centralizer ({t} : Set G) := by
    have e' : g * t * g⁻¹ = x * t * x⁻¹ := by
      rw [e]
      calc g * t * g⁻¹ = (t * t) * (g * t * g⁻¹) := by rw [h.t_mul_t, one_mul]
        _ = t * (t * g * t * g⁻¹) := by group
    rw [mem_centralizer_singleton_iff]
    calc x⁻¹ * g * t = x⁻¹ * (g * t * g⁻¹) * g := by group
      _ = x⁻¹ * (x * t * x⁻¹) * g := by rw [e']
      _ = t * (x⁻¹ * g) := by group
  have hcN : x⁻¹ * g ∈ normalizer ((d.X ⊔ zpowers t : Subgroup G) : Set G) :=
    mul_mem (inv_mem ((h.normalizer_yamadaU₂_le hW d hK hD).2.1 hxU)) hgN
  have hcX := h.mem_normalizer_of_mem_normalizer_sup_t (d.image_le _) hc hcN
  refine ⟨x, hx, ?_⟩
  rw [← h.centralizer_inf_normalizer_X_eq d hK hD]
  exact Subgroup.mem_inf.2 ⟨hc, hcX⟩

theorem le_yamadaR_of_normal (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    {Q : Subgroup G} (hQC : Q ≤ centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G))
    (hQn : centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤ normalizer (Q : Set G))
    (hQp : IsPGroup 2 Q) : Q ≤ yamadaR d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcore := (Model.yamada_3_23_1 hK h.two_le (h.inner_le_range_act d)).1
  set Q' := (Q.subgroupOf (centralizer ({t} : Set G))).map (h.act d) with hQ'
  have hQ'le : Q' ≤ Model.inn (Model.S K) := by
    rw [← hcore]
    refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_
      ((hQp.comap_subtype (K := centralizer ({t} : Set G))).map (h.act d))
    · rintro _ ⟨q, hq, rfl⟩
      refine Subgroup.mem_inf.2 ⟨⟨q, rfl⟩, ?_⟩
      rw [h.act_apply]
      exact (d.act_mem_normalizer_inn_iff _).2 (Subgroup.mem_inf.1 (hQC hq)).2
    · intro α hα
      obtain ⟨hαr, hαS⟩ := Subgroup.mem_inf.1 hα
      obtain ⟨c, rfl⟩ := MonoidHom.mem_range.1 hαr
      have hcS : (c : G) ∈ normalizer (d.S : Set G) := by
        rw [h.act_apply] at hαS
        exact (d.act_mem_normalizer_inn_iff _).1 hαS
      have hcQ : (c : G) ∈ normalizer (Q : Set G) := hQn (Subgroup.mem_inf.2 ⟨c.2, hcS⟩)
      rw [mem_normalizer_iff]
      intro β
      constructor
      · rintro ⟨q, hq, rfl⟩
        refine ⟨c * q * c⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
        show ((c * q * c⁻¹ : centralizer ({t} : Set G)) : G) ∈ Q
        rw [coe_mul, coe_mul, coe_inv]
        exact (mem_normalizer_iff.1 hcQ q).1 hq
      · rintro ⟨q, hq, hqe⟩
        refine ⟨c⁻¹ * q * c, ?_, ?_⟩
        · have hq' : (q : G) ∈ Q := hq
          show ((c⁻¹ * q * c : centralizer ({t} : Set G)) : G) ∈ Q
          rw [coe_mul, coe_mul, coe_inv]
          have := (mem_normalizer_iff.1 (inv_mem hcQ) q).1 hq'
          rwa [inv_inv] at this
        · rw [map_mul, map_mul, map_inv, hqe]
          group
  intro q hq
  have hqC := (Subgroup.mem_inf.1 (hQC hq)).1
  have hα : h.act d ⟨q, hqC⟩ ∈ Model.inn (Model.S K) := hQ'le ⟨⟨q, hqC⟩, hq, rfl⟩
  rw [h.act_apply] at hα
  have hq' := (d.act_mem_inn_iff _).1 hα
  have hZ : centralizer (L : Set G) ≤ normalizer (d.S : Set G) := fun z hz =>
    mem_normalizer_of_conj_mem fun x hx => by
      rw [← mem_centralizer_iff.1 hz x (d.image_le _ hx), mul_inv_cancel_right]
      exact hx
  obtain ⟨s, hs, z, hz, rfl⟩ := Common.exists_mul_of_le_normalizer hZ q hq'
  have hzt : z ∈ centralizer ({t} : Set G) := by
    have := mul_mem (inv_mem (h.L_le_centralizer (d.image_le _ hs))) hqC
    rwa [inv_mul_cancel_left] at this
  have hzt' : z ∈ zpowers t := by
    rw [← h.centralizer_L_inf]
    exact Subgroup.mem_inf.2 ⟨hz, hzt⟩
  rw [h.yamadaR_eq d]
  exact mul_mem (mem_sup_left hs) (mem_sup_right hzt')

theorem centralizer_inf_normalizer_S_le_normalizer_yamadaR₄star (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤
      normalizer (yamadaR₄star d t : Set G) := fun c hc => by
  obtain ⟨hNS₁, hNS₂, -⟩ := h.centralizer_inf_normalizer_S_le d hK hD
  obtain ⟨hct, hcS⟩ := Subgroup.mem_inf.1 hc
  have hcR : c ∈ normalizer (yamadaRstar d t : Set G) :=
    mem_normalizer_sup (LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hNS₁ hc)) hcS
  have hcX := (Subgroup.mem_inf.1 ((h.centralizer_inf_normalizer_F_le d hK hD).2 hc)).2
  have hcX₁ : c ∈ normalizer ((yamadaX₁ d t ⊔ zpowers t : Subgroup G) : Set G) :=
    mem_normalizer_sup (mem_normalizer_sup hcX (hNS₂ hc))
      (mem_normalizer_zpowers (mem_centralizer_singleton_iff.1 hct))
  exact Common.mem_normalizer_inf hcR (Subgroup.le_normalizer hcX₁)

theorem normalizer_yamadaU₂_eq (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    normalizer (yamadaU₂ d t : Set G) = normalizer ((d.X ⊔ zpowers t : Subgroup G) : Set G) ∧
      ((normalizer (yamadaU₂ d t : Set G) : Subgroup G) : Set G) = (yamadaR₄star d t : Set G) *
        ((centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) : Subgroup G) : Set G) := by
  have hR₄U := fun {g} (hg : g ∈ yamadaR₄star d t) =>
    (Subgroup.mem_inf.1 ((h.yamadaR₄star_le_normalizer hW d hK hD).1 hg)).1
  have hNU := (h.le_normalizer_yamadaU₂ d hK hD).1
  have hfac : ∀ g ∈ normalizer ((d.X ⊔ zpowers t : Subgroup G) : Set G), t * g * t * g⁻¹ ∈ d.X →
      g ∈ (yamadaR₄star d t : Set G) *
        ((centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) : Subgroup G) : Set G) :=
    fun g hgN hg => by
      obtain ⟨x, hx, hc⟩ := h.exists_mul_of_mem_normalizer_yamadaU₂ hW d hK hD hg hgN
      exact Set.mem_mul.2 ⟨x, hx, x⁻¹ * g, hc, by group⟩
  have hsub : ((yamadaR₄star d t : Set G) *
      ((centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) : Subgroup G) : Set G)) ⊆
      ((normalizer (yamadaU₂ d t : Set G) : Subgroup G) : Set G) := by
    rintro _ ⟨x, hx, c, hc, rfl⟩
    exact mul_mem (hR₄U hx) (hNU hc)
  refine ⟨le_antisymm (h.normalizer_yamadaU₂_le hW d hK hD).2.1 fun g hg => hsub (hfac g hg ?_),
    Set.Subset.antisymm (fun g hg => hfac g ((h.normalizer_yamadaU₂_le hW d hK hD).2.1 hg)
      (h.crossed_mem_X hW d hK hD hg)) hsub⟩
  have hgt : g * t * g⁻¹ ∈ d.X ⊔ zpowers t :=
    (mem_normalizer_iff.1 hg t).1 (mem_sup_right (mem_zpowers t))
  rcases (h.mem_sup_zpowers_iff (d.image_le _)).1 hgt with h1 | h1
  · exact absurd ((le_sup_left : d.X ≤ yamadaX₂ d t) h1) (h.conj_t_not_mem_yamadaX₂ hW d hK hD g)
  · rwa [show t * g * t * g⁻¹ = t * (g * t * g⁻¹) by group]

theorem yamada_5_25_4 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) : yamadaR₄ d t = yamadaR₄star d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hset⟩ := h.normalizer_yamadaU₂_eq hW d hK hD
  have hR₄U : yamadaR₄star d t ≤ normalizer (yamadaU₂ d t : Set G) := fun g hg =>
    (Subgroup.mem_inf.1 ((h.yamadaR₄star_le_normalizer hW d hK hD).1 hg)).1
  have hNU := (h.le_normalizer_yamadaU₂ d hK hD).1
  have hNR₄ := h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₄star d hK hD
  have hUN : normalizer (yamadaU₂ d t : Set G) ≤ normalizer (yamadaR₄star d t : Set G) :=
    fun g hg => by
      have hg' : g ∈ ((normalizer (yamadaU₂ d t : Set G) : Subgroup G) : Set G) := hg
      rw [hset] at hg'
      obtain ⟨x, hx, c, hc, rfl⟩ := Set.mem_mul.1 hg'
      exact mul_mem (Subgroup.le_normalizer hx) (hNR₄ hc)
  have hle : yamadaR₄star d t ≤ yamadaR₄ d t :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hR₄U hUN
      ((h.isPGroup_yamadaRstar d).to_le inf_le_left)
  obtain ⟨hR₂eq, -⟩ := h.yamada_5_21_2 hW d hK hD
  have hR₂R₄ : yamadaR₂ d t ≤ yamadaR₄star d t := by
    rw [hR₂eq]
    exact inf_le_right
  refine le_antisymm (fun z hz => ?_) hle
  have hz' : z ∈ ((normalizer (yamadaU₂ d t : Set G) : Subgroup G) : Set G) :=
    LieType.BorelTits.pCoreOf_le 2 _ hz
  rw [hset] at hz'
  obtain ⟨x, hx, c, hc, rfl⟩ := Set.mem_mul.1 hz'
  have hcR₄ : c ∈ yamadaR₄ d t := by
    have := mul_mem (inv_mem (hle hx)) hz
    rwa [inv_mul_cancel_left] at this
  have hcR : c ∈ yamadaR d t := by
    refine h.le_yamadaR_of_normal d hK (Q := yamadaR₄ d t ⊓
      (centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G))) inf_le_right
      (fun g hg => Common.mem_normalizer_inf (LieType.BorelTits.le_normalizer_pCoreOf 2 _
        (hNU hg)) (Subgroup.le_normalizer hg))
      ((LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left) (Subgroup.mem_inf.2 ⟨hcR₄, hc⟩)
  exact mul_mem hx (hR₂R₄ ((h.yamadaR₂_inf_centralizer d hK).1 hcR))

theorem yamada_5_25_1 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    normalizer (yamadaU₂ d t : Set G) = normalizer ((d.X ⊔ zpowers t : Subgroup G) : Set G) ∧
      normalizer (yamadaU₂ d t : Set G) =
        yamadaR₄ d t ⊔ (centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G)) ∧
      ((normalizer (yamadaU₂ d t : Set G) : Subgroup G) : Set G) = (yamadaR₄ d t : Set G) *
        ((centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) : Subgroup G) : Set G) ∧
      normalizer (yamadaU₂ d t : Set G) ≤ normalizer (yamadaR₂ d t : Set G) := by
  obtain ⟨h1, hset⟩ := h.normalizer_yamadaU₂_eq hW d hK hD
  rw [← h.yamada_5_25_4 hW d hK hD] at hset
  have hR₄U : yamadaR₄ d t ≤ normalizer (yamadaU₂ d t : Set G) :=
    LieType.BorelTits.pCoreOf_le 2 _
  have hNU := (h.le_normalizer_yamadaU₂ d hK hD).1
  have hR₄R₂ : yamadaR₄ d t ≤ normalizer (yamadaR₂ d t : Set G) := by
    rw [h.yamada_5_25_4 hW d hK hD]
    exact (h.yamadaR₄star_le_normalizer hW d hK hD).2
  obtain ⟨hNR₂, -⟩ := h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK hD
  refine ⟨h1, le_antisymm (fun g hg => ?_) (sup_le hR₄U hNU), hset, fun g hg => ?_⟩
  · have hg' : g ∈ ((normalizer (yamadaU₂ d t : Set G) : Subgroup G) : Set G) := hg
    rw [hset] at hg'
    obtain ⟨x, hx, c, hc, rfl⟩ := Set.mem_mul.1 hg'
    exact mul_mem (mem_sup_left hx) (mem_sup_right hc)
  · have hg' : g ∈ ((normalizer (yamadaU₂ d t : Set G) : Subgroup G) : Set G) := hg
    rw [hset] at hg'
    obtain ⟨x, hx, c, hc, rfl⟩ := Set.mem_mul.1 hg'
    exact mul_mem (hR₄R₂ hx) (hNR₂ hc)

theorem yamada_5_25_2 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    (∀ g ∈ yamadaR₄ d t, ∃ x ∈ d.X, g * t * g⁻¹ = t * x) ∧
      ∀ x ∈ d.X, ∃ g ∈ yamadaR₄ d t, g * t * g⁻¹ = t * x := by
  rw [h.yamada_5_25_4 hW d hK hD]
  refine ⟨fun g hg => ⟨_, h.crossed_mem_X hW d hK hD
    (Subgroup.mem_inf.1 ((h.yamadaR₄star_le_normalizer hW d hK hD).1 hg)).1,
      h.conj_t_eq_mul_crossed g⟩, fun x hx => h.exists_conj_t_eq_mul_of_mem_X hW d hK hD hx⟩

theorem yamada_5_25_3 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    ∃ _ : ((yamadaR₂ d t).subgroupOf (yamadaR₄ d t)).Normal,
      ∃ _ : (d.Y.subgroupOf d.X).Normal,
        ∃ φ : yamadaR₄ d t ⧸ (yamadaR₂ d t).subgroupOf (yamadaR₄ d t) ≃*
          d.X ⧸ d.Y.subgroupOf d.X,
        (∀ (x : yamadaR₄ d t) (y : d.X), (x : G) * t * (x : G)⁻¹ = t * y →
          φ (QuotientGroup.mk x) = QuotientGroup.mk y) ∧
        ∀ c ∈ centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G),
          ∀ (x : yamadaR₄ d t) (y : d.X), φ (QuotientGroup.mk x) = QuotientGroup.mk y →
            ∃ (hx : c * x * c⁻¹ ∈ yamadaR₄ d t) (hy : c * y * c⁻¹ ∈ d.X),
              φ (QuotientGroup.mk ⟨_, hx⟩) = QuotientGroup.mk ⟨_, hy⟩ := by
  obtain ⟨-, -, -, hXF, -⟩ := d.inclusions
  have hR₄ := h.yamada_5_25_4 hW d hK hD
  have hR₄U : yamadaR₄ d t ≤ normalizer (yamadaU₂ d t : Set G) :=
    LieType.BorelTits.pCoreOf_le 2 _
  have hR₄R : yamadaR₄ d t ≤ yamadaRstar d t := fun x hx =>
    (Subgroup.mem_inf.1 (hR₄.le hx)).1
  have hYXn : (d.Y.subgroupOf d.X).Normal :=
    (normal_subgroupOf_iff_le_normalizer d.inclusions.2.1).2 (X_le_normalizer_Y d)
  have hY₁Y₂ : yamadaY₁ d t ≤ yamadaY₂ d t :=
    sup_le (h.Y_le_yamadaY₂ d hK hD) (yamadaU₁_le_yamadaY₂ d t)
  have hκX : ∀ x : yamadaR₄ d t, t * (x : G) * t * (x : G)⁻¹ ∈ d.X := fun x =>
    h.crossed_mem_X hW d hK hD (hR₄U x.2)
  have hmul : ∀ x y : yamadaR₄ d t, ∃ y₁ ∈ d.Y,
      t * ((x : G) * y) * t * ((x : G) * y)⁻¹ =
        (t * x * t * (x : G)⁻¹) * (t * y * t * (y : G)⁻¹) * y₁ := fun x y => by
    have hxX := (h.normalizer_yamadaU₂_le hW d hK hD).2.2 (hR₄U x.2)
    have hκ := hκX y
    rw [h.crossed_mul' (x : G) y]
    generalize t * (y : G) * t * (y : G)⁻¹ = a at hκ ⊢
    generalize t * (x : G) * t * (x : G)⁻¹ = b
    have hz : (x : G) * a * (x : G)⁻¹ * a⁻¹ ∈ d.Y := by
      rw [← h.X_inf_yamadaY₂ d hK hD]
      exact Subgroup.mem_inf.2 ⟨mul_mem ((mem_normalizer_iff.1 hxX a).1 hκ) (inv_mem hκ),
        hY₁Y₂ ((h.commutator_mem_of_mem_yamadaRstar d hK hD (hR₄R x.2)).2 a
          (mem_sup_left (hXF hκ)))⟩
    refine ⟨(x : G) * a * (x : G)⁻¹ * a⁻¹, hz, ?_⟩
    have hcomm : a * ((x : G) * a * (x : G)⁻¹ * a⁻¹) = ((x : G) * a * (x : G)⁻¹ * a⁻¹) * a :=
      X_mul_comm d hκ (d.inclusions.2.1 hz)
    calc b * ((x : G) * a * (x : G)⁻¹) = b * (((x : G) * a * (x : G)⁻¹ * a⁻¹) * a) := by group
      _ = b * (a * ((x : G) * a * (x : G)⁻¹ * a⁻¹)) := by rw [hcomm]
      _ = b * a * ((x : G) * a * (x : G)⁻¹ * a⁻¹) := by group
  let ψ : yamadaR₄ d t →* d.X ⧸ d.Y.subgroupOf d.X :=
    { toFun := fun x => QuotientGroup.mk ⟨_, hκX x⟩
      map_one' := by
        apply (QuotientGroup.eq_one_iff _).2
        rw [mem_subgroupOf]
        show t * 1 * t * (1 : G)⁻¹ ∈ d.Y
        rw [mul_one, inv_one, mul_one, h.t_mul_t]
        exact one_mem _
      map_mul' := fun x y => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
        obtain ⟨y₁, hy₁, e⟩ := hmul x y
        show (t * ((x : G) * y) * t * ((x : G) * y)⁻¹)⁻¹ *
          ((t * x * t * (x : G)⁻¹) * (t * y * t * (y : G)⁻¹)) ∈ d.Y
        rw [e, show (t * x * t * (x : G)⁻¹ * (t * y * t * (y : G)⁻¹) * y₁)⁻¹ *
          (t * x * t * (x : G)⁻¹ * (t * y * t * (y : G)⁻¹)) = y₁⁻¹ by group]
        exact inv_mem hy₁ }
  have hψ : ∀ x : yamadaR₄ d t, ψ x = QuotientGroup.mk ⟨_, hκX x⟩ := fun _ => rfl
  have hform : ∀ (x : yamadaR₄ d t) (y : d.X), (x : G) * t * (x : G)⁻¹ = t * y →
      ψ x = QuotientGroup.mk y := by
    intro x y e
    rw [hψ]
    congr 1
    apply Subtype.ext
    show t * x * t * (x : G)⁻¹ = y
    rw [show t * (x : G) * t * (x : G)⁻¹ = t * ((x : G) * t * (x : G)⁻¹) by group, e,
      ← mul_assoc, h.t_mul_t, one_mul]
  have hker : ψ.ker = (yamadaR₂ d t).subgroupOf (yamadaR₄ d t) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, hψ, QuotientGroup.eq_one_iff, mem_subgroupOf]
    constructor
    · intro hx
      exact (h.mem_yamadaR₂_iff hW d hK hD).2 ⟨hR₄R x.2, mem_sup_left hx⟩
    · intro hx
      have h1 := ((h.mem_yamadaR₂_iff hW d hK hD).1 hx).2
      show t * (x : G) * t * (x : G)⁻¹ ∈ d.Y
      rw [← h.X_inf_yamadaY₂ d hK hD]
      exact Subgroup.mem_inf.2 ⟨hκX x, hY₁Y₂ h1⟩
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨g, hg, e⟩ := (h.yamada_5_25_2 hW d hK hD).2 y y.2
    exact ⟨⟨g, hg⟩, hform ⟨g, hg⟩ y e⟩
  have hR₂n : ((yamadaR₂ d t).subgroupOf (yamadaR₄ d t)).Normal := hker ▸ ψ.normal_ker
  set φ := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj) with hφdef
  have hφ : ∀ x : yamadaR₄ d t, φ (QuotientGroup.mk x) = ψ x := fun _ => rfl
  refine ⟨hR₂n, hYXn, φ, fun x y e => (hφ x).trans (hform x y e), ?_⟩
  intro c hc x y hxy
  obtain ⟨hct, -⟩ := Subgroup.mem_inf.1 hc
  have hcU := (h.le_normalizer_yamadaU₂ d hK hD).1 hc
  have hcR₄ : c ∈ normalizer (yamadaR₄ d t : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 _ hcU
  have hcX := (Subgroup.mem_inf.1 ((h.centralizer_inf_normalizer_F_le d hK hD).2 hc)).2
  have hcY := (h.centralizer_inf_normalizer_S_le d hK hD).2.2 hc
  have hx : c * x * c⁻¹ ∈ yamadaR₄ d t := (mem_normalizer_iff.1 hcR₄ x).1 x.2
  have hy : c * y * c⁻¹ ∈ d.X := (mem_normalizer_iff.1 hcX y).1 y.2
  refine ⟨hx, hy, ?_⟩
  rw [hφ, hψ, QuotientGroup.eq, mem_subgroupOf] at hxy ⊢
  have hcte : c * t = t * c := mem_centralizer_singleton_iff.1 hct
  have hct' : c⁻¹ * t * c = t := by rw [mul_assoc, ← hcte, inv_mul_cancel_left]
  have hκc : t * (c * x * c⁻¹) * t * (c * x * c⁻¹)⁻¹ = c * (t * x * t * (x : G)⁻¹) * c⁻¹ := by
    calc t * (c * x * c⁻¹) * t * (c * x * c⁻¹)⁻¹ =
          (t * c) * x * (c⁻¹ * t * c) * (x : G)⁻¹ * c⁻¹ := by group
      _ = (c * t) * x * t * (x : G)⁻¹ * c⁻¹ := by rw [hct', ← hcte]
      _ = c * (t * x * t * (x : G)⁻¹) * c⁻¹ := by group
  show (t * (c * x * c⁻¹) * t * (c * x * c⁻¹)⁻¹)⁻¹ * (c * y * c⁻¹) ∈ d.Y
  rw [hκc, show (c * (t * x * t * (x : G)⁻¹) * c⁻¹)⁻¹ * (c * y * c⁻¹) =
    c * ((t * x * t * (x : G)⁻¹)⁻¹ * y) * c⁻¹ by group]
  exact (mem_normalizer_iff.1 hcY _).1 hxy

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
