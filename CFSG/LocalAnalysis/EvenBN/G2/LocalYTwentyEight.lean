module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYTwentyFive

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section Defs

variable
  {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def yamadaC₄ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaR₄ d t ⊓ yamadaCstar d t

@[expose] noncomputable def yamadaL₄ (d : G2Data L K) (t : G) : Subgroup G :=
  (yamadaR₄ d t ⊓ centralizer (d.J₆ : Set G)) ⊔ yamadaL₂ d t

@[expose] noncomputable def yamadaE₄ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaL₄ d t ⊓ yamadaC₄ d t

@[expose] noncomputable def yamadaU₄ (d : G2Data L K) (t : G) : Subgroup G :=
  (yamadaR₄ d t ⊓ centralizer (d.J₆ : Set G)) ⊔ yamadaU₂ d t

@[expose] noncomputable def yamadaX₄ (d : G2Data L K) (t : G) : Subgroup G :=
  ⁅yamadaU₄ d t, d.J⁆

@[expose] noncomputable def yamadaF₄ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaX₄ d t ⊔ yamadaF₂ d t

@[expose] noncomputable def yamadaM₄ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaX₄ d t ⊔ yamadaM₂ d t

@[expose] noncomputable def yamadaS₄ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaX₄ d t ⊔ yamadaS₂ d t

@[expose] noncomputable def yamadaD₄ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaS₄ d t ⊓ yamadaC₄ d t

end Defs

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section TorusRoot

variable {K : Type} [Field K]

omit [Finite G] in
theorem J_le_normalizer_rootGroup (d : G2Data L K) {α : Fin Tag.G2.rank → ℤ}
    (hα : IsRoot .G2 α) : d.J ≤ normalizer (d.rootGroup α : Set G) := by
  have key : ∀ g ∈ Model.J K, ∀ y ∈ rootSubgroup .G2 K α,
      g * y * g⁻¹ ∈ rootSubgroup .G2 K α := fun g hg y hy => by
    obtain ⟨c, hc⟩ := exists_torus_scale hg hα
    obtain ⟨x, rfl⟩ := mem_rootSubgroup.1 hy
    rw [hc x]
    exact mem_rootSubgroup.2 ⟨_, rfl⟩
  refine d.image_le_normalizer (Model.J_le_adjointGroup K)
    (rootSubgroup_le_adjointGroup (K := K) (τ := .G2) α) fun g hg => ?_
  rw [mem_normalizer_iff]
  intro n
  refine ⟨key g hg n, fun hn => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hn
  rwa [show g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n by group] at this

end TorusRoot

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem J₆_facts (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    d.J₆ ≤ d.J ∧ Nat.card d.J₆ = Nat.card K - 1 ∧
      d.S ⊓ centralizer (d.J₆ : Set G) = d.rootGroup g2u ∧
      d.J₆ ≤ normalizer (d.rootGroup g2v : Set G) ∧
      (∀ x ∈ d.rootGroup g2v, x ≠ 1 → ∀ y ∈ d.rootGroup g2v, y ≠ 1 →
        ∃ j ∈ d.J₆, j * x * j⁻¹ = y) ∧
      ∀ x ∈ d.rootGroup g2v, x ≠ 1 → ∀ j ∈ d.J₆, j * x = x * j → j = 1 := by
  have hJ₆J : d.J₆ ≤ d.J := d.image_mono inf_le_left
  have h92 := d.yamada_3_9_2_G (i := 5) (k := 1) (by decide)
  obtain ⟨hbot, htr⟩ := h92.2 (Or.inr (by decide))
  refine ⟨hJ₆J, (d.yamada_3_9_1_G 5).2,
    S_inf_centralizer_Ji_of_four_le d (hK ▸ h.four_le) 5 (Or.inr (by decide)),
    fun j hj => J_le_normalizer_rootGroup d isRoot_g2v (hJ₆J hj), fun x hx hx1 y hy hy1 =>
    htr x hx hx1 y hy hy1, fun x hx hx1 j hj hjx => ?_⟩
  have hj' : j ∈ d.Ji 5 ⊓ centralizer {x} :=
    Subgroup.mem_inf.2 ⟨hj, mem_centralizer_singleton_iff.2 hjx⟩
  rw [h92.1 x hx hx1, hbot] at hj'
  exact (Subgroup.mem_bot).1 hj'

theorem J₆_conj_X (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {j x : G} (hj : j ∈ d.J₆) (hx : x ∈ d.X) :
    j * x * j⁻¹ ∈ d.X ∧ x⁻¹ * (j * x * j⁻¹) ∈ d.Y := by
  obtain ⟨hJ₆J, -, hC, -⟩ := h.J₆_facts d hK
  obtain ⟨-, -, hYW, -⟩ := d.inclusions
  have hXdef := d.yamada_defs.2.1
  have hjY : j ∈ normalizer (d.Y : Set G) :=
    (h.centralizer_inf_normalizer_S_le d hK hD).2.2 (h.J_le_centralizer_inf_normalizer_S d
      (hJ₆J hj))
  have hAS : d.rootGroup g2u ≤ d.S := hC.ge.trans inf_le_left
  have hAX : d.rootGroup g2u ≤ d.X := le_sup_left.trans hXdef.le
  have hYX : d.Y ≤ d.X := d.inclusions.2.1
  rw [← hXdef] at hx
  obtain ⟨a, ha, y, hy, rfl⟩ :=
    Common.exists_mul_of_le_normalizer' (hAS.trans d.S_le_normalizers.2.1) _ hx
  have hja : j * a = a * j := mem_centralizer_iff.1 (Subgroup.mem_inf.1 (hC.ge ha)).2 j hj
  have hjy : j * y * j⁻¹ ∈ d.Y := (mem_normalizer_iff.1 hjY _).1 hy
  have e1 : j * (a * y) * j⁻¹ = a * (j * y * j⁻¹) := by
    calc j * (a * y) * j⁻¹ = j * a * y * j⁻¹ := by group
      _ = a * (j * y * j⁻¹) := by rw [hja]; group
  rw [e1, show (a * y)⁻¹ * (a * (j * y * j⁻¹)) = y⁻¹ * (j * y * j⁻¹) by group]
  exact ⟨mul_mem (hAX ha) (hYX hjy), mul_mem (inv_mem hy) hjy⟩

theorem yamadaR₄_facts (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaR₄ d t ≤ yamadaRstar d t ∧ yamadaR₂ d t ≤ yamadaR₄ d t ∧
      yamadaR₄ d t ≤ normalizer (yamadaR₂ d t : Set G) ∧
      yamadaR₄ d t ≤ normalizer (yamadaCstar d t : Set G) ∧
      yamadaC₂ d t = yamadaCstar d t ⊓ yamadaR₂ d t ∧
      Nat.card (yamadaR₄ d t) = 2 * Nat.card K ^ 9 := by
  have hR₄ := h.yamada_5_25_4 hW d hK hD
  obtain ⟨hR₂eq, -⟩ := h.yamada_5_21_2 hW d hK hD
  have hRC : yamadaRstar d t ≤ normalizer (yamadaCstar d t : Set G) :=
    sup_le Subgroup.le_normalizer (h.S_le_normalizer_yamadaCstar d)
  have hR₄R : yamadaR₄ d t ≤ yamadaRstar d t := by
    rw [hR₄]
    exact inf_le_left
  have hR₂R₄ : yamadaR₂ d t ≤ yamadaR₄ d t := by
    rw [hR₄, hR₂eq]
    exact inf_le_right
  have hq : 0 < Nat.card K ^ 2 := by
    have : 0 < Nat.card K := Nat.card_pos
    positivity
  have hXY : Nat.card (d.X ⧸ d.Y.subgroupOf d.X) = Nat.card K := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (d.Y.subgroupOf d.X)
    rw [Nat.card_congr (subgroupOfEquivOfLe d.inclusions.2.1).toEquiv, d.cards.2.2.1,
      d.cards.2.1] at h1
    refine Nat.eq_of_mul_eq_mul_right hq ?_
    rw [← h1]
    ring
  obtain ⟨_, _, φ, -, -⟩ := h.yamada_5_25_3 hW d hK hD
  have hc : Nat.card (yamadaR₄ d t) = 2 * Nat.card K ^ 9 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((yamadaR₂ d t).subgroupOf (yamadaR₄ d t))
    rw [Nat.card_congr φ.toEquiv, Nat.card_congr (subgroupOfEquivOfLe hR₂R₄).toEquiv, hXY,
      h.card_yamadaR₂ d hK] at h1
    rw [h1]
    ring
  exact ⟨hR₄R, hR₂R₄, (LieType.BorelTits.pCoreOf_le 2 _).trans (h.yamada_5_25_1 hW d hK hD).2.2.2,
    hR₄R.trans hRC, (h.yamada_5_19 d hK hD).2.2.2.2.1, hc⟩

theorem yamadaX₁_mul_self (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {a : G}
    (ha : a ∈ yamadaX₁ d t) : a * a = 1 := by
  obtain ⟨-, -, -, hXF, -, hFD, -⟩ := d.inclusions
  have hU₁X := h.yamadaU₁_le_normalizer_of_le_D d hK hD (hXF.trans hFD)
  obtain ⟨w, hw, u, hu, rfl⟩ := Common.exists_mul_of_le_normalizer hU₁X a ha
  have hU₁ := h.yamada_5_16 hW d hK hD
  have hu2 : u * u = 1 := by
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := yamadaU₁ d t) u hu
  have hwu : u * w = w * u :=
    mem_centralizer_iff.1 (hD.D_le_centralizer ((hXF.trans hFD) hw)) u hu
  calc w * u * (w * u) = w * (u * w) * u := by group
    _ = w * (w * u) * u := by rw [hwu]
    _ = (w * w) * (u * u) := by group
    _ = 1 := by rw [X_mul_self d hw, hu2, one_mul]

theorem yamada_5_32_1_R₄ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaR₄ d t ≤ normalizer (yamadaC₂ d t : Set G) ∧
      yamadaR₄ d t = yamadaC₄ d t ⊔ yamadaR₂ d t ∧
      yamadaC₄ d t ⊓ yamadaR₂ d t = yamadaC₂ d t ∧
      yamadaR₄ d t ≤ normalizer (yamadaC₄ d t : Set G) ∧
      yamadaR₄ d t ≤ normalizer (yamadaR₂ d t : Set G) ∧
      (∀ x ∈ yamadaR₄ d t, x * x ∈ yamadaC₂ d t) ∧
      (∀ x ∈ yamadaR₄ d t, ∀ y ∈ yamadaR₄ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaC₂ d t) ∧
      Nat.card (yamadaR₄ d t) = Nat.card K ^ 2 * Nat.card (yamadaC₂ d t) := by
  obtain ⟨hR₃R, hR₂R₃, hR₃R₂, hR₃C, hC₂, -⟩ := h.yamadaR₄_facts hW d hK hD
  obtain ⟨-, -, -, hXF, hWF, hFD, -⟩ := d.inclusions
  have hCV := h.yamadaCstar_eq d hK hD
  have hR₃ := h.yamada_5_25_4 hW d hK hD
  have hC₃R₂ : yamadaC₄ d t ⊓ yamadaR₂ d t = yamadaC₂ d t := by
    rw [hC₂, yamadaC₄, inf_comm (yamadaR₄ d t), inf_assoc, inf_eq_right.2 hR₂R₃]
  have hNC₃ : yamadaR₄ d t ≤ normalizer (yamadaC₄ d t : Set G) := fun g hg =>
    Common.mem_normalizer_inf (Subgroup.le_normalizer hg) (hR₃C hg)
  have hNC₂ : yamadaR₄ d t ≤ normalizer (yamadaC₂ d t : Set G) := fun g hg => by
    rw [hC₂]
    exact Common.mem_normalizer_inf (hR₃C hg) (hR₃R₂ hg)
  have hfac : ∀ g ∈ yamadaR₄ d t, ∃ x ∈ yamadaC₄ d t, x⁻¹ * g ∈ yamadaR₂ d t := fun g hg => by
    have hg' : g ∈ yamadaR₄star d t := hR₃ ▸ hg
    obtain ⟨hgR, hgκ⟩ := (h.mem_yamadaR₄star_iff d hK hD).1 hg'
    have hW₁D₁ : yamadaX₁ d t ≤ yamadaD₁ d t :=
      sup_le ((hXF.trans hFD).trans le_sup_right) hD.spec.1
    obtain ⟨x, hx, u, hu, e⟩ := (h.yamada_5_19 d hK hD).2.1.2 _ (hW₁D₁ hgκ)
    have hxR : x ∈ yamadaRstar d t := mem_sup_left hx
    have hκx : t * x * t * x⁻¹ = (t * g * t * g⁻¹) * u := by
      rw [show t * x * t * x⁻¹ = t * (x * t * x⁻¹) by group, e, ← mul_assoc, ← mul_assoc,
        h.t_mul_t, one_mul]
    have hxR₃ : x ∈ yamadaR₄ d t := by
      rw [hR₃]
      refine (h.mem_yamadaR₄star_iff d hK hD).2 ⟨hxR, ?_⟩
      rw [hκx]
      exact mul_mem hgκ (mem_sup_right hu)
    refine ⟨x, Subgroup.mem_inf.2 ⟨hxR₃, hx⟩, (h.mem_yamadaR₂_iff hW d hK hD).2
      ⟨mul_mem (inv_mem hxR) hgR, ?_⟩⟩
    have hxU₁ : x ∈ normalizer (yamadaU₁ d t : Set G) := (h.normalizer_yamadaC₁_le d hK hD).2
      ((h.normalizer_yamadaC₁_le d hK hD).1 (h.yamadaRstar_le_normalizer d hxR))
    rw [h.crossed_mul' x⁻¹ g, h.crossed_inv' x, hκx, show x⁻¹ * (t * g * t * g⁻¹ * u)⁻¹ * x *
      (x⁻¹ * (t * g * t * g⁻¹) * x⁻¹⁻¹) = x⁻¹ * u⁻¹ * x⁻¹⁻¹ by group]
    exact mem_sup_right ((mem_normalizer_iff.1 (inv_mem hxU₁) _).1 (inv_mem hu))
  have hR₄eq : yamadaR₄ d t = yamadaC₄ d t ⊔ yamadaR₂ d t := by
    refine le_antisymm (fun g hg => ?_) (sup_le inf_le_left hR₂R₃)
    obtain ⟨x, hx, hxg⟩ := hfac g hg
    have := mul_mem (mem_sup_left hx) (mem_sup_right hxg :
      x⁻¹ * g ∈ yamadaC₄ d t ⊔ yamadaR₂ d t)
    rwa [mul_inv_cancel_left] at this
  have hC₁C₂ : yamadaC₁ d t ≤ yamadaC₂ d t := by
    rw [(h.yamadaC₂_eq_sup d hK hD).1]
    exact le_sup_left
  have hsqC : ∀ c ∈ yamadaC₄ d t, c * c ∈ yamadaC₂ d t := fun c hc => by
    obtain ⟨hcR₃, hcC⟩ := Subgroup.mem_inf.1 hc
    have hcV : c ∈ h.yamadaV d hK hD := hCV ▸ hcC
    have hcN := ((h.mem_yamadaV d hK hD).1 hcV).1
    have hκ : t * c * t * c⁻¹ ∈ yamadaX₁ d t :=
      ((h.mem_yamadaR₄star_iff d hK hD).1 (hR₃ ▸ hcR₃)).2
    have h1 := h.crossed_mul_mem d hK hD hcV hcN
    rw [h.yamadaX₁_mul_self hW d hK hD hκ, inv_one, one_mul] at h1
    exact hC₁C₂ (h.mem_yamadaC₁_of_crossed_mem d hK hD (mul_mem hcV hcV) h1)
  have hF₁C₂ : yamadaF₁ d t ≤ yamadaC₂ d t := by
    rw [h.yamadaF₁_eq_sup d hK hD]
    exact sup_le ((hFD.trans ((le_sup_right : d.D ≤ yamadaD₁ d t).trans
      (h.yamadaD₁_le_yamadaC₁ d hK))).trans hC₁C₂) ((h.yamadaU₁_le_yamadaC₁ d hK hD).trans hC₁C₂)
  have hsqR : ∀ r ∈ yamadaR₂ d t, r * r ∈ yamadaC₂ d t := fun r hr => by
    refine hF₁C₂ ?_
    rw [← (h.yamada_5_15_3 d hK hD).1]
    exact subset_closure ⟨r, hr, (sq r).symm⟩
  have hsq : ∀ x ∈ yamadaR₄ d t, x * x ∈ yamadaC₂ d t := fun x hx => by
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
  have hcomm : ∀ x ∈ yamadaR₄ d t, ∀ y ∈ yamadaR₄ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaC₂ d t :=
    fun x hx y hy => by
      rw [show x * y * x⁻¹ * y⁻¹ = (x * y * (x * y)) * (y⁻¹ * (x * x)⁻¹ * y⁻¹⁻¹) *
        (y * y)⁻¹ by group]
      exact mul_mem (mul_mem (hsq _ (mul_mem hx hy))
        ((mem_normalizer_iff.1 (inv_mem (hNC₂ hy)) _).1 (inv_mem (hsq x hx))))
        (inv_mem (hsq y hy))
  have hcard : Nat.card (yamadaR₄ d t) = Nat.card K ^ 2 * Nat.card (yamadaC₂ d t) := by
    rw [(h.yamadaR₄_facts hW d hK hD).2.2.2.2.2, (h.card_yamadaC₂_E₂_V₂ d hK hD).1]
    ring
  exact ⟨hNC₂, hR₄eq, hC₃R₂, hNC₃, hR₃R₂, hsq, hcomm, hcard⟩

theorem normalizer_yamadaR₂_le_normalizer_yamadaL₂ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    normalizer (yamadaR₂ d t : Set G) ≤ normalizer (yamadaL₂ d t : Set G) := by
  have := (h.yamada_5_15_6 d hK hD).1
  have h1 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    ((yamadaL₂ d t).subgroupOf (yamadaR₂ d t))
  rwa [subgroupOf_map_subtype, inf_of_le_left (show yamadaL₂ d t ≤ yamadaR₂ d t from le_sup_left)]
    at h1

theorem J_le_normalizer_yamadaR₄ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.J ≤ normalizer (yamadaR₄ d t : Set G) := fun _ hj =>
  LieType.BorelTits.le_normalizer_pCoreOf 2 _
    ((h.le_normalizer_yamadaU₂ d hK hD).1 (h.J_le_centralizer_inf_normalizer_S d hj))

theorem inv_mul_conj_mem_yamadaR₂_of_J₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {x j : G}
    (hx : x ∈ yamadaR₄ d t) (hj : j ∈ d.J₆) : x⁻¹ * (j * x * j⁻¹) ∈ yamadaR₂ d t := by
  obtain ⟨hJ₆J, -⟩ := h.J₆_facts d hK
  obtain ⟨_, _, φ, hφ, -⟩ := h.yamada_5_25_3 hW d hK hD
  obtain ⟨y, hy, hxy⟩ := (h.yamada_5_25_2 hW d hK hD).1 x hx
  have hjt : j * t = t * j := mem_centralizer_singleton_iff.1
    (Subgroup.mem_inf.1 (h.J_le_centralizer_inf_normalizer_S d (hJ₆J hj))).1
  have hjx : j * x * j⁻¹ ∈ yamadaR₄ d t :=
    (mem_normalizer_iff.1 (h.J_le_normalizer_yamadaR₄ d hK hD (hJ₆J hj)) _).1 hx
  obtain ⟨hjy, hyY⟩ := h.J₆_conj_X d hK hD hj hy
  have h1 := hφ ⟨x, hx⟩ ⟨y, hy⟩ hxy
  have h2 := hφ ⟨j * x * j⁻¹, hjx⟩ ⟨j * y * j⁻¹, hjy⟩ (conj_conj_t hjt hxy)
  have h3 : (QuotientGroup.mk ⟨y, hy⟩ : d.X ⧸ d.Y.subgroupOf d.X) =
      QuotientGroup.mk ⟨j * y * j⁻¹, hjy⟩ := by
    rw [QuotientGroup.eq, mem_subgroupOf]
    exact hyY
  have h4 := φ.injective (h1.trans (h3.trans h2.symm))
  rw [QuotientGroup.eq, mem_subgroupOf] at h4
  exact h4

theorem mem_yamadaL₂_of_forall_J₆ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {x : G} (hx : x ∈ yamadaR₂ d t)
    (hfix : ∀ j ∈ d.J₆, x⁻¹ * (j * x * j⁻¹) ∈ yamadaL₂ d t) : x ∈ yamadaL₂ d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hJ₆J, -, hC, -⟩ := h.J₆_facts d hK
  obtain ⟨-, -, -, hXF, -, -, hFM, -, hMS, -⟩ := d.inclusions
  have hJC := h.J_le_centralizer_inf_normalizer_S d
  have hML₂ : d.M ≤ yamadaL₂ d t := le_sup_left.trans (h.tM_le_yamadaL₂ d hK)
  have hR₂L₂ : yamadaR₂ d t ≤ normalizer (yamadaL₂ d t : Set G) :=
    sup_le Subgroup.le_normalizer (h.S_le_normalizer_yamadaL₂ d)
  have hJL₂ : d.J ≤ normalizer (yamadaL₂ d t : Set G) := fun j hj =>
    le_normalizer_yamadaL₂ d t ((h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK
      hD).2 (mem_sup_right (hJC hj)))
  have hJM : d.J ≤ normalizer (d.M : Set G) := fun j hj => by
    rw [← h.yamadaL₂_inf_S d hK]
    exact Common.mem_normalizer_inf (hJL₂ hj) (Subgroup.mem_inf.1 (hJC hj)).2
  obtain ⟨l, hl, s, hs, rfl⟩ :=
    Common.exists_mul_of_le_normalizer (h.S_le_normalizer_yamadaL₂ d) x hx
  have hfixs : ∀ j ∈ d.J₆, s⁻¹ * (j * s * j⁻¹) ∈ d.M := fun j hj => by
    rw [← h.yamadaL₂_inf_S d hK]
    refine Subgroup.mem_inf.2 ⟨?_, mul_mem (inv_mem hs)
      ((mem_normalizer_iff.1 (Subgroup.mem_inf.1 (hJC (hJ₆J hj))).2 _).1 hs)⟩
    have h1 : j * l⁻¹ * j⁻¹ ∈ yamadaL₂ d t :=
      (mem_normalizer_iff.1 (hJL₂ (hJ₆J hj)) _).1 (inv_mem hl)
    have h2 : (l * s)⁻¹ * (l * (j * l⁻¹ * j⁻¹)) * (l * s) ∈ yamadaL₂ d t := by
      have := (mem_normalizer_iff.1 (inv_mem (hR₂L₂ hx)) _).1 (mul_mem hl h1)
      rwa [inv_inv] at this
    rw [show s⁻¹ * (j * s * j⁻¹) = (l * s)⁻¹ * (l * (j * l⁻¹ * j⁻¹)) * (l * s) *
      ((l * s)⁻¹ * (j * (l * s) * j⁻¹)) by group]
    exact mul_mem h2 (hfix j hj)
  have hSp : IsPGroup 2 d.S := d.isSylowOf_S.isPGroup
  obtain ⟨c, hc, m, hm, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime
    (M := d.S) (N := d.M) (S := d.J₆) hMS d.S_le_normalizers.2.2.2.2.2.2
    (fun j hj => (Subgroup.mem_inf.1 (hJC (hJ₆J hj))).2)
    (fun j hj => hJM (hJ₆J hj))
    (have : Group.IsNilpotent d.S := hSp.isNilpotent; inferInstance)
    (by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hSp
      rw [hk]
      exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2
        ((odd_card_J d).of_dvd_nat (Subgroup.card_dvd_of_le hJ₆J))))
    hs hfixs
  have hcM : c ∈ d.M := by
    rw [hC] at hc
    exact hFM (hXF ((le_sup_left.trans d.yamada_defs.2.1.le) hc))
  exact mul_mem hl (mul_mem (hML₂ hcM) (hML₂ hm))

theorem yamadaL₄_facts (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaR₄ d t = (yamadaR₄ d t ⊓ centralizer (d.J₆ : Set G)) ⊔ yamadaR₂ d t ∧
      yamadaL₄ d t ⊓ yamadaR₂ d t = yamadaL₂ d t ∧
      yamadaL₄ d t ⊔ yamadaR₂ d t = yamadaR₄ d t ∧ yamadaL₄ d t ⊔ d.S = yamadaR₄ d t ∧
      yamadaL₄ d t ≤ yamadaR₄ d t ∧ Nat.card (yamadaL₄ d t) = 2 * Nat.card K ^ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hR₄R, hR₂R₄, hR₄R₂, -, -, hR₄c⟩ := h.yamadaR₄_facts hW d hK hD
  obtain ⟨hJ₆J, -⟩ := h.J₆_facts d hK
  have hR₄p : IsPGroup 2 (yamadaR₄ d t) := (h.isPGroup_yamadaRstar d).to_le hR₄R
  have hJR₄ := h.J_le_normalizer_yamadaR₄ d hK hD
  have hJR₂ : d.J ≤ normalizer (yamadaR₂ d t : Set G) := fun j hj =>
    (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK hD).1
      (h.J_le_centralizer_inf_normalizer_S d hj)
  have hL₂R₂ : yamadaL₂ d t ≤ yamadaR₂ d t := le_sup_left
  have hL₂R₄ : yamadaL₂ d t ≤ yamadaR₄ d t := hL₂R₂.trans hR₂R₄
  have hR₄L₂ : yamadaR₄ d t ≤ normalizer (yamadaL₂ d t : Set G) :=
    hR₄R₂.trans (h.normalizer_yamadaR₂_le_normalizer_yamadaL₂ d hK hD)
  have hcop : Nat.Coprime (Nat.card d.J₆) (Nat.card (yamadaR₄ d t)) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hR₄p
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2
      ((odd_card_J d).of_dvd_nat (Subgroup.card_dvd_of_le hJ₆J)))
  have hR₄eq : yamadaR₄ d t = (yamadaR₄ d t ⊓ centralizer (d.J₆ : Set G)) ⊔ yamadaR₂ d t := by
    refine le_antisymm (fun x hx => ?_) (sup_le inf_le_left hR₂R₄)
    have : Group.IsNilpotent (yamadaR₄ d t) := hR₄p.isNilpotent
    obtain ⟨c, hc, n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime
      (M := yamadaR₄ d t) (N := yamadaR₂ d t) (S := d.J₆) hR₂R₄ hR₄R₂
      (fun j hj => hJR₄ (hJ₆J hj)) (fun j hj => hJR₂ (hJ₆J hj)) inferInstance hcop hx
      fun j hj => h.inv_mul_conj_mem_yamadaR₂_of_J₆ hW d hK hD hx hj
    exact mul_mem (mem_sup_left hc) (mem_sup_right hn)
  have hAR₂ : ∀ x ∈ yamadaR₄ d t ⊓ centralizer (d.J₆ : Set G), x ∈ yamadaR₂ d t →
      x ∈ yamadaL₂ d t := fun x hx hxR => h.mem_yamadaL₂_of_forall_J₆ d hK hD hxR fun j hj => by
    rw [mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 j hj, mul_inv_cancel_right,
      inv_mul_cancel]
    exact one_mem _
  have hL₄R₄ : yamadaL₄ d t ≤ yamadaR₄ d t := sup_le inf_le_left hL₂R₄
  have hL₄R₂ : yamadaL₄ d t ⊓ yamadaR₂ d t = yamadaL₂ d t := by
    refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right hL₂R₂)
    obtain ⟨hxL, hxR⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨a, ha, l, hl, rfl⟩ :=
      Common.exists_mul_of_le_normalizer' (inf_le_left.trans hR₄L₂) x hxL
    have haR : a ∈ yamadaR₂ d t := by
      have := mul_mem hxR (inv_mem (hL₂R₂ hl))
      rwa [mul_inv_cancel_right] at this
    exact mul_mem (hAR₂ a ha haR) hl
  have hL₄R : yamadaL₄ d t ⊔ yamadaR₂ d t = yamadaR₄ d t :=
    le_antisymm (sup_le hL₄R₄ hR₂R₄) (hR₄eq.le.trans (sup_le_sup_right le_sup_left _))
  have hL₄S : yamadaL₄ d t ⊔ d.S = yamadaR₄ d t := by
    refine le_antisymm (sup_le hL₄R₄ ((le_sup_right : d.S ≤ yamadaR₂ d t).trans hR₂R₄)) ?_
    rw [← hL₄R]
    exact sup_le le_sup_left (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  have hL₄c : Nat.card (yamadaL₄ d t) = 2 * Nat.card K ^ 8 := by
    have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaR₂ d t) (B := yamadaL₄ d t)
      (hL₄R₄.trans hR₄R₂)
    rw [sup_comm, hL₄R, inf_comm, hL₄R₂, hR₄c, h.card_yamadaR₂ d hK, h.card_yamadaL₂ d hK] at h1
    refine Nat.eq_of_mul_eq_mul_left (show 0 < 2 * Nat.card K ^ 8 by
      have : 0 < Nat.card K := Nat.card_pos
      positivity) ?_
    rw [← h1]
    ring
  exact ⟨hR₄eq, hL₄R₂, hL₄R, hL₄S, hL₄R₄, hL₄c⟩

theorem rootGroup_a_inf_yamadaL₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    d.rootGroup g2a ⊓ yamadaL₂ d t = ⊥ ∧ yamadaR₂ d t ≤ d.rootGroup g2a ⊔ yamadaL₂ d t := by
  obtain ⟨-, -, -, -, -, hFD, hFM, hDS, hMS, -⟩ := d.inclusions
  obtain ⟨-, -, -, -, hD, -, -, hDM, hSDM⟩ := d.yamada_defs
  have hAD : d.rootGroup g2a ≤ d.D := le_sup_left.trans hD.le
  have hAS : d.rootGroup g2a ≤ d.S := hAD.trans hDS
  have hML₂ : d.M ≤ yamadaL₂ d t := le_sup_left.trans (h.tM_le_yamadaL₂ d hK)
  have hAc : Nat.card (d.rootGroup g2a) = Nat.card K :=
    (d.card_image (rootSubgroup_le_adjointGroup (K := K) (τ := .G2) g2a)).trans
      (card_rootSubgroup (τ := .G2) (K := K) g2a)
  have hAF : d.F ⊓ d.rootGroup g2a = ⊥ := by
    have h1 := Common.card_sup_mul_card_inf_eq (A := d.F) (B := d.rootGroup g2a)
      (hAS.trans d.S_le_normalizers.2.2.2.2.1)
    rw [sup_comm, hD, d.cards.2.2.2.2.2.1, d.cards.2.2.2.2.1, hAc] at h1
    have hq : 0 < Nat.card K ^ 5 := by
      have : 0 < Nat.card K := Nat.card_pos
      positivity
    refine Subgroup.card_eq_one.1 (Nat.eq_of_mul_eq_mul_left hq ?_)
    rw [h1]
    ring
  refine ⟨eq_bot_iff.2 fun x hx => ?_, ?_⟩
  · obtain ⟨hxA, hxL⟩ := Subgroup.mem_inf.1 hx
    have hxM : x ∈ d.M := by
      rw [← h.yamadaL₂_inf_S d hK]
      exact Subgroup.mem_inf.2 ⟨hxL, hAS hxA⟩
    rw [← hAF]
    refine Subgroup.mem_inf.2 ⟨?_, hxA⟩
    rw [← hDM]
    exact Subgroup.mem_inf.2 ⟨hAD hxA, hxM⟩
  · refine sup_le le_sup_right ?_
    rw [← hSDM, ← hD]
    exact sup_le (sup_le le_sup_left ((hFM.trans hML₂).trans le_sup_right))
      (hML₂.trans le_sup_right)

theorem yamada_5_32_1_L₄ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaR₄ d t ≤ normalizer (yamadaL₂ d t : Set G) ∧
      yamadaR₄ d t = yamadaL₄ d t ⊔ yamadaR₂ d t ∧
      yamadaL₄ d t ⊓ yamadaR₂ d t = yamadaL₂ d t ∧
      yamadaR₄ d t ≤ normalizer (yamadaL₄ d t : Set G) ∧
      (∀ x ∈ yamadaR₄ d t, x * x ∈ yamadaL₂ d t) ∧
      (∀ x ∈ yamadaR₄ d t, ∀ y ∈ yamadaR₄ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaL₂ d t) ∧
      Nat.card (yamadaR₄ d t) = Nat.card K ^ 2 * Nat.card (yamadaL₂ d t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hR₄R, hR₂R₄, hR₄R₂, -, hC₂, hR₄c⟩ := h.yamadaR₄_facts hW d hK hD
  obtain ⟨hR₄eq, hL₄R₂, hL₄R, -, hL₄R₄, -⟩ := h.yamadaL₄_facts hW d hK hD
  obtain ⟨hJ₆J, -⟩ := h.J₆_facts d hK
  obtain ⟨hAL₂, hR₂AL₂⟩ := h.rootGroup_a_inf_yamadaL₂ d hK
  obtain ⟨-, -, -, -, -, hsqR₄, -, -⟩ := h.yamada_5_32_1_R₄ hW d hK hD
  have hR₄p : IsPGroup 2 (yamadaR₄ d t) := (h.isPGroup_yamadaRstar d).to_le hR₄R
  have hR₄L₂ : yamadaR₄ d t ≤ normalizer (yamadaL₂ d t : Set G) :=
    hR₄R₂.trans (h.normalizer_yamadaR₂_le_normalizer_yamadaL₂ d hK hD)
  have hR₂L₂ : yamadaR₂ d t ≤ normalizer (yamadaL₂ d t : Set G) := hR₂R₄.trans hR₄L₂
  have hJC := h.J_le_centralizer_inf_normalizer_S d
  have hJL₂ : d.J ≤ normalizer (yamadaL₂ d t : Set G) := fun j hj =>
    le_normalizer_yamadaL₂ d t ((h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK
      hD).2 (mem_sup_right (hJC hj)))
  have hAS : d.rootGroup g2a ≤ d.S :=
    (le_sup_left.trans d.yamada_defs.2.2.2.2.1.le).trans d.inclusions.2.2.2.2.2.2.2.1
  have hAN : d.rootGroup g2a ≤ normalizer (yamadaL₂ d t : Set G) :=
    hAS.trans (h.S_le_normalizer_yamadaL₂ d)
  obtain ⟨-, htr⟩ := (d.yamada_3_9_2_G (i := 5) (k := 3) (by decide)).2 (Or.inr (by decide))
  have hreg : ∀ x ∈ d.rootGroup g2a, x ≠ 1 → ∀ j ∈ d.J₆, j * x = x * j → j = 1 :=
    fun x hx hx1 j hj hjx => by
      have h92 := d.yamada_3_9_2_G (i := 5) (k := 3) (by decide)
      have hj' : j ∈ d.Ji 5 ⊓ centralizer {x} :=
        Subgroup.mem_inf.2 ⟨hj, mem_centralizer_singleton_iff.2 hjx⟩
      rw [h92.1 x hx hx1, (h92.2 (Or.inr (by decide))).1] at hj'
      exact (Subgroup.mem_bot).1 hj'
  have hcomm : ∀ c ∈ yamadaR₄ d t ⊓ centralizer (d.J₆ : Set G), ∀ r ∈ yamadaR₂ d t,
      c * r * c⁻¹ * r⁻¹ ∈ yamadaL₂ d t := fun c hc => by
    obtain ⟨hcR, hcJ⟩ := Subgroup.mem_inf.1 hc
    obtain ⟨m, hm⟩ := hR₄p ⟨c, hcR⟩
    have hcm : c ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    exact conj_mul_inv_mem_of_regular (A := d.rootGroup g2a) (J := d.J₆)
      (hAS.trans le_sup_right) (fun e he => Common.exists_mul_of_le_normalizer' hAN e (hR₂AL₂ he))
      hR₂L₂ hAL₂ (fun j hj => J_le_normalizer_rootGroup d isRoot_g2a (hJ₆J hj))
      (fun j hj => hJL₂ (hJ₆J hj)) (fun j hj k hk => J_mul_comm d (hJ₆J hj) (hJ₆J hk))
      ((odd_card_J d).of_dvd_nat (Subgroup.card_dvd_of_le hJ₆J)) htr hreg (hR₄R₂ hcR)
      (hR₄L₂ hcR) hcJ hcm
  have hF₁L₂ : yamadaF₁ d t ≤ yamadaL₂ d t := inf_le_left.trans inf_le_left
  have hsqA : ∀ c ∈ yamadaR₄ d t ⊓ centralizer (d.J₆ : Set G), c * c ∈ yamadaL₂ d t :=
    fun c hc => by
      have hcc : c * c ∈ yamadaR₂ d t := (hC₂.le.trans inf_le_right) (hsqR₄ c (Subgroup.mem_inf.1
        hc).1)
      exact h.mem_yamadaL₂_of_forall_J₆ d hK hD hcc fun j hj => by
        rw [mem_centralizer_iff.1 (Subgroup.mem_inf.1 (mul_mem hc hc)).2 j hj,
          mul_inv_cancel_right, inv_mul_cancel]
        exact one_mem _
  have hsqB : ∀ r ∈ yamadaR₂ d t, r * r ∈ yamadaL₂ d t := fun r hr => by
    refine hF₁L₂ ?_
    rw [← (h.yamada_5_15_3 d hK hD).1]
    exact subset_closure ⟨r, hr, (sq r).symm⟩
  obtain ⟨hsq, hcomm'⟩ := mul_self_mem_of_sup (N := yamadaL₂ d t) (inf_le_left.trans hR₄R₂)
    (hR₄eq.ge.trans hR₄L₂) hsqA hsqB hcomm
  have hR₂L₄ : yamadaR₂ d t ≤ normalizer (yamadaL₄ d t : Set G) := fun r hr =>
    mem_normalizer_of_conj_mem fun x hx => by
      obtain ⟨a, ha, l, hl, rfl⟩ :=
        Common.exists_mul_of_le_normalizer' (inf_le_left.trans hR₄L₂) x hx
      have h1 : a⁻¹ * r * a⁻¹⁻¹ * r⁻¹ ∈ yamadaL₂ d t := hcomm _ (inv_mem ha) r hr
      rw [show r * (a * l) * r⁻¹ = a * (a⁻¹ * r * a⁻¹⁻¹ * r⁻¹) * (r * l * r⁻¹) by group]
      exact mul_mem (mul_mem (mem_sup_left ha) (mem_sup_right h1))
        (mem_sup_right ((mem_normalizer_iff.1 (hR₂L₂ hr) l).1 hl))
  have hR₄L₄ : yamadaR₄ d t ≤ normalizer (yamadaL₄ d t : Set G) := by
    rw [hR₄eq]
    exact sup_le (le_sup_left.trans Subgroup.le_normalizer) hR₂L₄
  refine ⟨hR₄L₂, hL₄R.symm, hL₄R₂, hR₄L₄, fun x hx => hsq x (hR₄eq.le hx),
    fun x hx y hy => hcomm' x (hR₄eq.le hx) y (hR₄eq.le hy), ?_⟩
  rw [hR₄c, h.card_yamadaL₂ d hK]
  ring

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
