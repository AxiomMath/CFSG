module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYTwentyNine

public section


namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite G] in
theorem Y_inf_rootGroup_u (d : G2Data L K) : d.Y ⊓ d.rootGroup g2u = ⊥ := by
  obtain ⟨-, hX, -⟩ := d.yamada_defs
  obtain ⟨-, -, -, hXF, -, hFD, -, hDS, -⟩ := d.inclusions
  have hAS : d.rootGroup g2u ≤ d.S := (le_sup_left.trans hX.le).trans (hXF.trans (hFD.trans hDS))
  have hAc : Nat.card (d.rootGroup g2u) = Nat.card K :=
    (d.card_image (rootSubgroup_le_adjointGroup (K := K) (τ := .G2) g2u)).trans
      (card_rootSubgroup (τ := .G2) (K := K) g2u)
  have h1 := Common.card_sup_mul_card_inf_eq (A := d.Y) (B := d.rootGroup g2u)
    (hAS.trans d.S_le_normalizers.2.1)
  rw [sup_comm, hX, d.cards.2.2.1, d.cards.2.1, hAc] at h1
  have hq : 0 < Nat.card K ^ 3 := by
    have : 0 < Nat.card K := Nat.card_pos
    positivity
  refine Subgroup.card_eq_one.1 (Nat.eq_of_mul_eq_mul_left hq ?_)
  rw [h1]
  ring

theorem mem_Y_of_forall_Ji (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {i : Fin 6} (hi : i ≠ 5) {x : G} (hx : x ∈ d.X)
    (hfix : ∀ k ∈ d.Ji i, x⁻¹ * (k * x * k⁻¹) ∈ d.Y) : x ∈ d.Y := by
  have hJiJ : d.Ji i ≤ d.J := d.image_mono inf_le_left
  have hJC := h.J_le_centralizer_inf_normalizer_S d
  have hJA := J_le_normalizer_rootGroup d isRoot_g2u
  obtain ⟨-, hXdef, -⟩ := d.yamada_defs
  obtain ⟨-, -, -, hXF, -, hFD, -, hDS, -⟩ := d.inclusions
  have hAS : d.rootGroup g2u ≤ d.S :=
    (le_sup_left.trans hXdef.le).trans (hXF.trans (hFD.trans hDS))
  have h92 := d.yamada_3_9_2_G (i := i) (k := 5) hi
  rw [← hXdef] at hx
  obtain ⟨a, ha, y, hy, rfl⟩ :=
    Common.exists_mul_of_le_normalizer' (hAS.trans d.S_le_normalizers.2.1) _ hx
  by_cases ha1 : a = 1
  · rw [ha1, one_mul]
    exact hy
  exfalso
  have hall : ∀ k ∈ d.Ji i, k = 1 := fun k hk => by
    have hkY : k ∈ normalizer (d.Y : Set G) :=
      (h.centralizer_inf_normalizer_S_le d hK hD).2.2 (hJC (hJiJ hk))
    have hmem : a⁻¹ * (k * a * k⁻¹) ∈ d.Y ⊓ d.rootGroup g2u := by
      refine Subgroup.mem_inf.2 ⟨?_, mul_mem (inv_mem ha)
        ((mem_normalizer_iff.1 (hJA (hJiJ hk)) _).1 ha)⟩
      rw [show a⁻¹ * (k * a * k⁻¹) =
        y * ((a * y)⁻¹ * (k * (a * y) * k⁻¹)) * (k * y * k⁻¹)⁻¹ by group]
      exact mul_mem (mul_mem hy (hfix k hk)) (inv_mem ((mem_normalizer_iff.1 hkY _).1 hy))
    rw [Y_inf_rootGroup_u d, Subgroup.mem_bot] at hmem
    have hka : k * a = a * k := by
      calc k * a = a * (a⁻¹ * (k * a * k⁻¹)) * k := by group
        _ = a * k := by rw [hmem, mul_one]
    have hk' : k ∈ d.Ji i ⊓ centralizer {a} :=
      Subgroup.mem_inf.2 ⟨hk, mem_centralizer_singleton_iff.2 hka⟩
    rw [h92.1 a ha ha1, (h92.2 (Or.inr fun h' => absurd h'.2 (by decide))).1] at hk'
    exact (Subgroup.mem_bot).1 hk'
  have hbot : d.Ji i = ⊥ := eq_bot_iff.2 fun k hk => (Subgroup.mem_bot).2 (hall k hk)
  have hc := (d.yamada_3_9_1_G i).2
  have h4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  rw [hbot, Subgroup.card_bot] at hc
  omega

theorem J_le_normalizer_X (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.J ≤ normalizer (d.X : Set G) := fun _ hj =>
  (Subgroup.mem_inf.1 ((h.centralizer_inf_normalizer_X_eq d hK hD).ge
    (h.J_le_centralizer_inf_normalizer_S d hj))).2

theorem eq_one_of_mem_yamadaX₂_of_forall_J (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {x : G} (hx : x ∈ yamadaX₂ d t)
    (hfix : ∀ k ∈ d.J, k * x = x * k) : x = 1 := by
  have hJ₂J : d.Ji 1 ≤ d.J := d.image_mono inf_le_left
  have hJY₂ := h.J_le_normalizer_yamadaY₂ d hK hD
  have hJX := h.J_le_normalizer_X d hK hD
  obtain ⟨w, hw, y, hy, rfl⟩ :=
    Common.exists_mul_of_le_normalizer (h.yamadaY₂_le_normalizer_X d hK hD) x hx
  have hwY : w ∈ d.Y := by
    refine h.mem_Y_of_forall_Ji d hK hD (i := 1) (by decide) hw fun k hk => ?_
    rw [← h.X_inf_yamadaY₂ d hK hD]
    have hkw : k * w * k⁻¹ ∈ d.X := (mem_normalizer_iff.1 (hJX (hJ₂J hk)) w).1 hw
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hw) hkw, ?_⟩
    have e : k * (w * y) * k⁻¹ = w * y := by
      rw [hfix k (hJ₂J hk)]
      group
    rw [show w⁻¹ * (k * w * k⁻¹) = y * (k * y * k⁻¹)⁻¹ by
      calc w⁻¹ * (k * w * k⁻¹) = w⁻¹ * (k * (w * y) * k⁻¹) * (k * y * k⁻¹)⁻¹ := by group
        _ = y * (k * y * k⁻¹)⁻¹ := by rw [e]; group]
    exact mul_mem hy (inv_mem ((mem_normalizer_iff.1 (hJY₂ (hJ₂J hk)) y).1 hy))
  exact h.eq_one_of_mem_yamadaY₂_of_forall_J d hK hD
    (mul_mem (h.Y_le_yamadaY₂ d hK hD hwY) hy) hfix

theorem mem_yamadaR₂_of_forall_Ji (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {i : Fin 6} (hi : i ≠ 5)
    {x : G} (hx : x ∈ yamadaR₄ d t) (hfix : ∀ k ∈ d.Ji i, x⁻¹ * (k * x * k⁻¹) ∈ yamadaR₂ d t) :
    x ∈ yamadaR₂ d t := by
  have hJiJ : d.Ji i ≤ d.J := d.image_mono inf_le_left
  have hJC := h.J_le_centralizer_inf_normalizer_S d
  have hJR₄ := h.J_le_normalizer_yamadaR₄ d hK hD
  have hJX := h.J_le_normalizer_X d hK hD
  obtain ⟨_, _, φ, hφ, -⟩ := h.yamada_5_25_3 hW d hK hD
  obtain ⟨w, hw, hxw⟩ := (h.yamada_5_25_2 hW d hK hD).1 x hx
  have hwY : w ∈ d.Y := by
    refine h.mem_Y_of_forall_Ji d hK hD hi hw fun k hk => ?_
    have hkt : k * t = t * k :=
      mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hJC (hJiJ hk))).1
    have hkx : k * x * k⁻¹ ∈ yamadaR₄ d t := (mem_normalizer_iff.1 (hJR₄ (hJiJ hk)) _).1 hx
    have hkw : k * w * k⁻¹ ∈ d.X := (mem_normalizer_iff.1 (hJX (hJiJ hk)) w).1 hw
    have h1 := hφ ⟨x, hx⟩ ⟨w, hw⟩ hxw
    have h2 := hφ ⟨k * x * k⁻¹, hkx⟩ ⟨k * w * k⁻¹, hkw⟩ (conj_conj_t hkt hxw)
    have h3 : (QuotientGroup.mk ⟨x, hx⟩ :
        yamadaR₄ d t ⧸ (yamadaR₂ d t).subgroupOf (yamadaR₄ d t)) =
        QuotientGroup.mk ⟨k * x * k⁻¹, hkx⟩ := by
      rw [QuotientGroup.eq, mem_subgroupOf]
      exact hfix k hk
    have h4 := h1.symm.trans ((congrArg φ h3).trans h2)
    rw [QuotientGroup.eq, mem_subgroupOf] at h4
    exact h4
  have h5 : φ (QuotientGroup.mk ⟨x, hx⟩) = 1 := by
    rw [hφ ⟨x, hx⟩ ⟨w, hw⟩ hxw, QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact hwY
  exact mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 ((MulEquiv.map_eq_one_iff φ).1 h5))

theorem yamadaE₄_inf_yamadaR₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaE₄ d t ⊓ yamadaR₂ d t = yamadaE₂ d t := by
  obtain ⟨hE₂E₄, -, -, -, hL₄C₂, -⟩ := h.yamadaE₄_facts hW d hK hD
  obtain ⟨-, -, -, -, hC₂, -⟩ := h.yamadaR₄_facts hW d hK hD
  refine le_antisymm (fun x hx => ?_)
    (le_inf hE₂E₄ ((h.yamadaE₂_le_yamadaL₂ d hK hD).2.trans le_sup_left))
  obtain ⟨hxE, hxR⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨hxL₄, hxC₄⟩ := Subgroup.mem_inf.1 hxE
  exact hL₄C₂ (Subgroup.mem_inf.2 ⟨hxL₄, hC₂.ge (Subgroup.mem_inf.2
    ⟨(Subgroup.mem_inf.1 hxC₄).2, hxR⟩)⟩)

theorem yamadaU₄_facts (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaU₂ d t ≤ yamadaU₄ d t ∧ yamadaU₄ d t ≤ yamadaE₄ d t ∧
      yamadaU₄ d t ⊓ yamadaR₂ d t = yamadaU₂ d t ∧
      Nat.card (yamadaU₄ d t) = 2 * Nat.card K ^ 6 ∧ yamadaU₄ d t ⊔ yamadaR₂ d t = yamadaR₄ d t ∧
      yamadaU₄ d t ≤ normalizer (yamadaR₂ d t : Set G) ∧
      yamadaU₄ d t ≤ normalizer (yamadaX₂ d t : Set G) ∧
      yamadaU₄ d t ≤ normalizer (yamadaY₂ d t : Set G) := by
  obtain ⟨-, hE₄eq, hU₄E₂, hE₄U₄, -, -, -, -⟩ := h.yamada_5_32_1_E₄ hW d hK hD
  obtain ⟨hE₂E₄, -, -, -, -, hcE₄, -⟩ := h.yamadaE₄_facts hW d hK hD
  obtain ⟨-, hR₂R₄, hR₄R₂, -, -, hR₄c⟩ := h.yamadaR₄_facts hW d hK hD
  obtain ⟨-, -, -, -, hL₄R₄, -⟩ := h.yamadaL₄_facts hW d hK hD
  have hU₂U₄ : yamadaU₂ d t ≤ yamadaU₄ d t := le_sup_right
  have hU₄E₄ : yamadaU₄ d t ≤ yamadaE₄ d t := le_sup_left.trans hE₄eq.ge
  have hU₄R₄ : yamadaU₄ d t ≤ yamadaR₄ d t := hU₄E₄.trans (inf_le_left.trans hL₄R₄)
  have hU₂E₂ : yamadaU₂ d t ≤ yamadaE₂ d t := hU₄E₂.ge.trans inf_le_right
  have hU₄R₂ : yamadaU₄ d t ⊓ yamadaR₂ d t = yamadaU₂ d t := by
    refine le_antisymm (fun x hx => ?_)
      (le_inf hU₂U₄ (hU₂E₂.trans ((h.yamadaE₂_le_yamadaL₂ d hK hD).2.trans le_sup_left)))
    obtain ⟨hxU, hxR⟩ := Subgroup.mem_inf.1 hx
    rw [← hU₄E₂, ← h.yamadaE₄_inf_yamadaR₂ hW d hK hD]
    exact Subgroup.mem_inf.2 ⟨hxU, Subgroup.mem_inf.2 ⟨hU₄E₄ hxU, hxR⟩⟩
  have hq : 0 < Nat.card K := Nat.card_pos
  obtain ⟨-, hE₂c, -⟩ := h.card_yamadaC₂_E₂_V₂ d hK hD
  have hU₂c : Nat.card (yamadaU₂ d t) = 2 * Nat.card K ^ 5 := by
    obtain ⟨htX, htX'⟩ := h.t_mem_normalizer_yamadaX₂ d hK hD
    rw [show yamadaU₂ d t = yamadaX₂ d t ⊔ zpowers t from rfl, h.card_sup_zpowers htX htX',
      h.card_yamadaX₂ d hK hD]
  have hU₄c : Nat.card (yamadaU₄ d t) = 2 * Nat.card K ^ 6 := by
    have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaU₄ d t) (B := yamadaE₂ d t)
      (hE₂E₄.trans hE₄U₄)
    rw [← hE₄eq, hU₄E₂, hcE₄, hU₂c, hE₂c] at h1
    refine Nat.eq_of_mul_eq_mul_right (show 0 < 2 * Nat.card K ^ 6 by positivity) ?_
    rw [← h1]
    ring
  have hU₄NR₂ : yamadaU₄ d t ≤ normalizer (yamadaR₂ d t : Set G) := hU₄R₄.trans hR₄R₂
  have hsup : yamadaU₄ d t ⊔ yamadaR₂ d t = yamadaR₄ d t := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hU₄R₄ hR₂R₄) ?_
    have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaR₂ d t) (B := yamadaU₄ d t) hU₄NR₂
    rw [inf_comm, hU₄R₂, h.card_yamadaR₂ d hK, hU₄c, hU₂c, sup_comm] at h1
    rw [hR₄c]
    have h2 : Nat.card (yamadaU₄ d t ⊔ yamadaR₂ d t : Subgroup G) = 2 * Nat.card K ^ 9 := by
      refine Nat.eq_of_mul_eq_mul_right (show 0 < 2 * Nat.card K ^ 5 by positivity) ?_
      rw [h1]
      ring
    exact h2.ge
  have hR₄U₂ : yamadaR₄ d t ≤ normalizer (yamadaU₂ d t : Set G) :=
    LieType.BorelTits.pCoreOf_le 2 _
  obtain ⟨hRE, hEF, hFY⟩ := h.normalizer_yamadaR₂_le d hK hD
  exact ⟨hU₂U₄, hU₄E₄, hU₄R₂, hU₄c, hsup, hU₄NR₂,
    (hU₄R₄.trans hR₄U₂).trans (h.normalizer_yamadaU₂_le hW d hK hD).1,
    hU₄NR₂.trans (hRE.trans (hEF.trans hFY))⟩

theorem J_le_normalizer_yamadaU₄ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    d.J ≤ normalizer (yamadaU₄ d t : Set G) ∧ d.J ≤ normalizer (yamadaU₂ d t : Set G) := by
  obtain ⟨hJ₆J, -⟩ := h.J₆_facts d hK
  obtain ⟨-, -, -, -, hJU₂⟩ := h.J_le_normalizers_four hW d hK hD
  have hJR₄ := h.J_le_normalizer_yamadaR₄ d hK hD
  exact ⟨fun j hj => mem_normalizer_sup (Common.mem_normalizer_inf (hJR₄ hj)
    (Subgroup.le_normalizer (mem_centralizer_iff.2 fun y hy => J_mul_comm d (hJ₆J hy) hj)))
    (hJU₂ hj), hJU₂⟩

theorem mul_self_mem_yamadaY₂_of_mem_yamadaU₂ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {v : G} (hv : v ∈ yamadaU₂ d t) :
    v * v ∈ yamadaY₂ d t := by
  obtain ⟨-, -, -, hXF, -, hFD, -, hDS, -⟩ := d.inclusions
  have hXY₂ : d.X ≤ normalizer (yamadaY₂ d t : Set G) :=
    (hXF.trans (hFD.trans hDS)).trans (h.yamada_5_13_3 d hK hD).1
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  have htY₂ := h.yamadaL₂_le_normalizer_yamadaY₂ d hK hD htL₂
  rcases (mem_sup_zpowers_iff_of h.t_mul_t (h.t_mem_normalizer_yamadaX₂ d hK hD).1).1 hv with
    h1 | ⟨a, ha, rfl⟩
  · obtain ⟨w, hw, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hXY₂ _ h1
    rw [show w * y * (w * y) = w * w * (w⁻¹ * y * w⁻¹⁻¹) * y by group, X_mul_self d hw, one_mul]
    exact mul_mem ((mem_normalizer_iff.1 (inv_mem (hXY₂ hw)) y).1 hy) hy
  · obtain ⟨w, hw, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hXY₂ _ ha
    have hwt : w * t = t * w :=
      mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hw))
    rw [show w * y * t * (w * y * t) = w * y * (t * w) * y * t by group, ← hwt,
      show w * y * (w * t) * y * t = w * w * (w⁻¹ * y * w⁻¹⁻¹) * (t * y * t⁻¹) * (t * t) by group,
      X_mul_self d hw, h.t_mul_t, one_mul, mul_one]
    exact mul_mem ((mem_normalizer_iff.1 (inv_mem (hXY₂ hw)) y).1 hy)
      ((mem_normalizer_iff.1 htY₂ y).1 hy)

theorem mul_self_mem_yamadaX₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {x : G}
    (hx : x ∈ yamadaU₄ d t) : x * x ∈ yamadaX₂ d t := by
  obtain ⟨-, hU₄E₄, hU₄R₂, -, hsup, hU₄NR₂, -, hU₄Y₂⟩ := h.yamadaU₄_facts hW d hK hD
  obtain ⟨-, hR₂R₄, -⟩ := h.yamadaR₄_facts hW d hK hD
  obtain ⟨-, -, -, -, -, hsqE₄, -, -⟩ := h.yamada_5_32_1_E₄ hW d hK hD
  obtain ⟨htX, htX'⟩ := h.t_mem_normalizer_yamadaX₂ d hK hD
  obtain ⟨-, -, -, hXF, -, hFD, -, hDS, -⟩ := d.inclusions
  have hU₄R₄ : yamadaU₄ d t ≤ yamadaR₄ d t := le_sup_left.trans hsup.le
  have hXY₂ : d.X ≤ normalizer (yamadaY₂ d t : Set G) :=
    (hXF.trans (hFD.trans hDS)).trans (h.yamada_5_13_3 d hK hD).1
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  rcases (mem_sup_zpowers_iff_of h.t_mul_t htX).1 (hsqE₄ x (hU₄E₄ hx)) with h1 | ⟨a, ha, ha'⟩
  · exact h1
  exfalso
  obtain ⟨w, hw, y₀, hy₀, hwy⟩ :=
    Common.exists_mul_of_le_normalizer' hXY₂ _ ((mem_normalizer_iff.1 htX a).1 ha)
  have hxx : x * x = t * (w * y₀) := by
    rw [ha', ← hwy]
    calc a * t = t * t * a * t⁻¹ := by rw [h.t_mul_t, one_mul, htinv]
      _ = t * (t * a * t⁻¹) := by group
  obtain ⟨g, hg, hgt⟩ := (h.yamada_5_25_2 hW d hK hD).2 w hw
  rw [← hsup] at hg
  obtain ⟨v, hv, l, hl, rfl⟩ := Common.exists_mul_of_le_normalizer' hU₄NR₂ _ hg
  have hlN : l ∈ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) :=
    (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK hD).2 (mem_sup_left hl)
  obtain ⟨y₁, hy₁, hlt⟩ : ∃ y₁ ∈ d.Y, l * t * l⁻¹ = t * y₁ :=
    ⟨_, (h.crossed_mem_Y_iff hW d hK hD ((h.normalizer_tY_le d hK hD).2.2 hlN)).2 hlN,
      h.conj_t_eq_mul_crossed l⟩
  have hvt : v * t * v⁻¹ = t * w * (v * y₁ * v⁻¹)⁻¹ := by
    have e : v * (l * t * l⁻¹) * v⁻¹ = t * w := by
      rw [← hgt]
      group
    rw [hlt] at e
    calc v * t * v⁻¹ = v * (t * y₁) * v⁻¹ * (v * y₁ * v⁻¹)⁻¹ := by group
      _ = t * w * (v * y₁ * v⁻¹)⁻¹ := by rw [e]
  have hvY₂ : v ∈ normalizer (yamadaY₂ d t : Set G) := hU₄Y₂ hv
  have hv₀ : v⁻¹ * y₀ * v ∈ yamadaY₂ d t := by
    have := (mem_normalizer_iff.1 (inv_mem hvY₂) y₀).1 hy₀
    rwa [inv_inv] at this
  have hy₂ : y₁ * (v⁻¹ * y₀ * v) ∈ yamadaY₂ d t := mul_mem (h.Y_le_yamadaY₂ d hK hD hy₁) hv₀
  have hyU : v⁻¹ * x * v ∈ yamadaU₄ d t := mul_mem (mul_mem (inv_mem hv) hx) hv
  have hyy : v⁻¹ * x * v * (v⁻¹ * x * v) = t * (y₁ * (v⁻¹ * y₀ * v)) := by
    have e1 : v⁻¹ * (t * w) * v = t * y₁ := by
      calc v⁻¹ * (t * w) * v = v⁻¹ * (v * t * v⁻¹ * (v * y₁ * v⁻¹)) * v := by rw [hvt]; group
        _ = t * y₁ := by group
    calc v⁻¹ * x * v * (v⁻¹ * x * v) = v⁻¹ * (x * x) * v := by group
      _ = v⁻¹ * (t * w) * v * (v⁻¹ * y₀ * v) := by rw [hxx]; group
      _ = t * (y₁ * (v⁻¹ * y₀ * v)) := by rw [e1]; group
  have hyN : v⁻¹ * x * v ∈ normalizer (yamadaY₂ d t : Set G) := hU₄Y₂ hyU
  have hyt : ∃ z ∈ yamadaY₂ d t, v⁻¹ * x * v * t * (v⁻¹ * x * v)⁻¹ = t * z := by
    refine ⟨y₁ * (v⁻¹ * y₀ * v) * (v⁻¹ * x * v * (y₁ * (v⁻¹ * y₀ * v))⁻¹ * (v⁻¹ * x * v)⁻¹),
      mul_mem hy₂ ((mem_normalizer_iff.1 hyN _).1 (inv_mem hy₂)), ?_⟩
    calc v⁻¹ * x * v * t * (v⁻¹ * x * v)⁻¹ = v⁻¹ * x * v *
          (v⁻¹ * x * v * (v⁻¹ * x * v) * (y₁ * (v⁻¹ * y₀ * v))⁻¹) * (v⁻¹ * x * v)⁻¹ := by
          rw [hyy]; group
      _ = v⁻¹ * x * v * (v⁻¹ * x * v) * (v⁻¹ * x * v * (y₁ * (v⁻¹ * y₀ * v))⁻¹ *
          (v⁻¹ * x * v)⁻¹) := by group
      _ = t * (y₁ * (v⁻¹ * y₀ * v) * (v⁻¹ * x * v * (y₁ * (v⁻¹ * y₀ * v))⁻¹ *
          (v⁻¹ * x * v)⁻¹)) := by rw [hyy]; group
  have hyR₄ : v⁻¹ * x * v ∈ yamadaR₄ d t := hU₄R₄ hyU
  have hyR₂ : v⁻¹ * x * v ∈ yamadaR₂ d t := by
    have hmem := ((h.yamada_5_21_3 hW d hK hD).2.2.1 (v⁻¹ * x * v)).1 ⟨hU₄NR₂ hyU, hyt⟩
    obtain ⟨r, hr, n, hn, e⟩ := Common.exists_mul_of_le_normalizer
      (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK hD).1 _ hmem
    have hnR : n ∈ yamadaR d t := by
      rw [← (h.yamada_5_27_1 hW d hK hD).2.2]
      refine Subgroup.mem_inf.2 ⟨?_, (Subgroup.mem_inf.1 hn).1⟩
      have hn' : n = r⁻¹ * (v⁻¹ * x * v) := by
        rw [e]
        group
      rw [hn']
      exact (le_sup_right.trans (h.yamada_5_27_2 hW d hK hD).1.1.ge)
        (mul_mem (inv_mem (hR₂R₄ hr)) hyR₄)
    rw [e]
    exact mul_mem hr ((h.yamadaR₂_inf_centralizer d hK).1 hnR)
  have hyU₂ : v⁻¹ * x * v ∈ yamadaU₂ d t := by
    rw [← hU₄R₂]
    exact Subgroup.mem_inf.2 ⟨hyU, hyR₂⟩
  have h1 := h.mul_self_mem_yamadaY₂_of_mem_yamadaU₂ d hK hD hyU₂
  rw [hyy] at h1
  have htY₂ : t ∈ yamadaY₂ d t := by
    have := mul_mem h1 (inv_mem hy₂)
    rwa [mul_inv_cancel_right] at this
  exact htX' ((le_sup_right : yamadaY₂ d t ≤ yamadaX₂ d t) htY₂)

theorem yamadaX₄_facts (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaX₄ d t ≤ yamadaU₄ d t ∧ yamadaU₄ d t ≤ normalizer (yamadaX₄ d t : Set G) ∧
      d.J ≤ normalizer (yamadaX₄ d t : Set G) ∧ yamadaX₂ d t ≤ yamadaX₄ d t ∧
      t ∉ yamadaX₄ d t ∧ yamadaX₄ d t ⊔ zpowers t = yamadaU₄ d t ∧
      Nat.card (yamadaX₄ d t) = Nat.card K ^ 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hU₂U₄, -, hU₄R₂, hU₄c, hsup, -, hU₄X₂, -⟩ := h.yamadaU₄_facts hW d hK hD
  obtain ⟨hJU₄, hJU₂⟩ := h.J_le_normalizer_yamadaU₄ hW d hK hD
  obtain ⟨hR₄R, -⟩ := h.yamadaR₄_facts hW d hK hD
  have hJ₂J : d.Ji 1 ≤ d.J := d.image_mono inf_le_left
  obtain ⟨-, htX'⟩ := h.t_mem_normalizer_yamadaX₂ d hK hD
  have hU₄R₄ : yamadaU₄ d t ≤ yamadaR₄ d t := le_sup_left.trans hsup.le
  have hU₄p : IsPGroup 2 (yamadaU₄ d t) := (h.isPGroup_yamadaRstar d).to_le (hU₄R₄.trans hR₄R)
  have hX₂U₄ : yamadaX₂ d t ≤ yamadaU₄ d t := le_sup_left.trans hU₂U₄
  have htU₄ : t ∈ yamadaU₄ d t := hU₂U₄ (mem_sup_right (mem_zpowers t))
  have hJX₂ : d.J ≤ normalizer (yamadaX₂ d t : Set G) :=
    hJU₂.trans (h.normalizer_yamadaU₂_le hW d hK hD).1
  have hX₄U₄ : yamadaX₄ d t ≤ yamadaU₄ d t := by
    show ⁅yamadaU₄ d t, d.J⁆ ≤ yamadaU₄ d t
    refine (Subgroup.commutator_le).2 fun v hv j hj => ?_
    rw [commutatorElement_def, show v * j * v⁻¹ * j⁻¹ = v * (j * v⁻¹ * j⁻¹) by group]
    exact mul_mem hv ((mem_normalizer_iff.1 (hJU₄ hj) _).1 (inv_mem hv))
  have hU₄N : yamadaU₄ d t ≤ normalizer (yamadaX₄ d t : Set G) :=
    le_normalizer_commutator_left _ _
  have hJN : d.J ≤ normalizer (yamadaX₄ d t : Set G) := fun j hj =>
    mem_normalizer_commutator (hJU₄ hj) (Subgroup.le_normalizer hj)
  have hcomm : ∀ v ∈ yamadaU₄ d t, ∀ j ∈ d.J, v⁻¹ * (j * v * j⁻¹) ∈ yamadaX₄ d t :=
    fun v hv j hj => by
      rw [show v⁻¹ * (j * v * j⁻¹) = ⁅v⁻¹, j⁆ by simp only [commutatorElement_def]; group]
      exact commutator_mem_commutator (inv_mem hv) hj
  have hsq : ∀ x ∈ yamadaU₄ d t, x * x ∈ yamadaX₂ d t := fun x hx =>
    h.mul_self_mem_yamadaX₂ hW d hK hD hx
  have hab : ∀ x ∈ yamadaU₄ d t, ∀ y ∈ yamadaU₄ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaX₂ d t :=
    fun x hx y hy => by
      rw [show x * y * x⁻¹ * y⁻¹ = x * y * (x * y) * (y⁻¹ * (x * x)⁻¹ * y⁻¹⁻¹) * (y * y)⁻¹ by
        group]
      exact mul_mem (mul_mem (hsq _ (mul_mem hx hy))
        ((mem_normalizer_iff.1 (inv_mem (hU₄X₂ hy)) _).1 (inv_mem (hsq x hx))))
        (inv_mem (hsq y hy))
  have htX₄ : t ∉ yamadaX₄ d t := fun ht => htX' (mem_of_mem_commutator_of_forall hX₂U₄ hU₄X₂
    hab hJU₄ hJX₂ (coprime_card_J d hU₄p) ht fun j hj => by
      have hjt : j * t = t * j := mem_centralizer_singleton_iff.1
        (Subgroup.mem_inf.1 (h.J_le_centralizer_inf_normalizer_S d hj)).1
      rw [hjt, mul_inv_cancel_right, inv_mul_cancel]
      exact one_mem _)
  have hX₂X₄ : yamadaX₂ d t ≤ yamadaX₄ d t := fun w hw => by
    have hXp : IsPGroup 2 (yamadaX₂ d t) := hU₄p.to_le hX₂U₄
    have : Group.IsNilpotent (yamadaX₂ d t) := hXp.isNilpotent
    obtain ⟨c, hc, n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime
      (M := yamadaX₂ d t) (N := yamadaX₂ d t ⊓ yamadaX₄ d t) (S := d.J) inf_le_left
      (fun x hx => Common.mem_normalizer_inf (Subgroup.le_normalizer hx) (hU₄N (hX₂U₄ hx)))
      hJX₂ (fun j hj => Common.mem_normalizer_inf (hJX₂ hj) (hJN hj)) inferInstance
      (coprime_card_J d hXp) hw fun j hj => Subgroup.mem_inf.2
        ⟨mul_mem (inv_mem hw) ((mem_normalizer_iff.1 (hJX₂ hj) w).1 hw),
          hcomm w (hX₂U₄ hw) j hj⟩
    have hc1 : c = 1 := h.eq_one_of_mem_yamadaX₂_of_forall_J d hK hD (Subgroup.mem_inf.1 hc).1
      fun k hk => mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 k hk
    rw [hc1, one_mul]
    exact (Subgroup.mem_inf.1 hn).2
  have hU₄eq : yamadaX₄ d t ⊔ zpowers t = yamadaU₄ d t := by
    refine le_antisymm (sup_le hX₄U₄ ((zpowers_le).2 htU₄)) fun v hv => ?_
    have : Group.IsNilpotent (yamadaU₄ d t) := hU₄p.isNilpotent
    obtain ⟨c, hc, n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime
      (M := yamadaU₄ d t) (N := yamadaX₄ d t) (S := d.J) hX₄U₄ hU₄N hJU₄ hJN inferInstance
      (coprime_card_J d hU₄p) hv (hcomm v hv)
    obtain ⟨hcU, hcJ⟩ := Subgroup.mem_inf.1 hc
    have hcR₂ : c ∈ yamadaR₂ d t := h.mem_yamadaR₂_of_forall_Ji hW d hK hD (i := 1) (by decide)
      (hU₄R₄ hcU) fun k hk => by
        rw [mem_centralizer_iff.1 hcJ k (hJ₂J hk), mul_inv_cancel_right, inv_mul_cancel]
        exact one_mem _
    have hcU₂ : c ∈ yamadaU₂ d t := hU₄R₂.le (Subgroup.mem_inf.2 ⟨hcU, hcR₂⟩)
    have hU₂le : yamadaU₂ d t ≤ yamadaX₄ d t ⊔ zpowers t :=
      sup_le (hX₂X₄.trans le_sup_left) le_sup_right
    exact mul_mem (hU₂le hcU₂) (mem_sup_left hn)
  have hX₄c : Nat.card (yamadaX₄ d t) = Nat.card K ^ 6 := by
    have h1 := h.card_sup_zpowers (hU₄N htU₄) htX₄
    rw [hU₄eq, hU₄c] at h1
    exact (Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num) h1).symm
  exact ⟨hX₄U₄, hU₄N, hJN, hX₂X₄, htX₄, hU₄eq, hX₄c⟩

theorem yamadaX₄_le_yamadaR₄ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaX₄ d t ≤ yamadaR₄ d t ∧ yamadaX₄ d t ⊓ yamadaR₂ d t = yamadaX₂ d t ∧
      d.J ≤ normalizer (yamadaX₄ d t : Set G) := by
  obtain ⟨hX₄U₄, -, hJN, hX₂X₄, htX₄, -⟩ := h.yamadaX₄_facts hW d hK hD
  obtain ⟨-, -, hU₄R₂, -, hsup, -⟩ := h.yamadaU₄_facts hW d hK hD
  refine ⟨hX₄U₄.trans (le_sup_left.trans hsup.le), le_antisymm (fun x hx => ?_)
    (le_inf hX₂X₄ ((le_sup_left : yamadaX₂ d t ≤ yamadaU₂ d t).trans
      (hU₄R₂.ge.trans inf_le_right))), hJN⟩
  obtain ⟨hxX, hxR⟩ := Subgroup.mem_inf.1 hx
  have hxU₂ : x ∈ yamadaU₂ d t := hU₄R₂.le (Subgroup.mem_inf.2 ⟨hX₄U₄ hxX, hxR⟩)
  rcases (mem_sup_zpowers_iff_of h.t_mul_t (h.t_mem_normalizer_yamadaX₂ d hK hD).1).1 hxU₂ with
    h1 | ⟨a, ha, rfl⟩
  · exact h1
  · exfalso
    refine htX₄ ?_
    have := mul_mem (inv_mem (hX₂X₄ ha)) hxX
    rwa [inv_mul_cancel_left] at this

theorem t_not_mem_yamadaX₄_sup (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {Z : Subgroup G}
    (hX₄Z : yamadaX₄ d t ≤ normalizer (Z : Set G)) (hXZ : yamadaX₂ d t ≤ Z) (htZ : t ∉ Z)
    (hUZ : yamadaU₄ d t ⊓ Z ≤ yamadaU₂ d t) : t ∉ yamadaX₄ d t ⊔ Z := by
  obtain ⟨hX₄U₄, -, -, hX₂X₄, htX₄, hU₄eq, -⟩ := h.yamadaX₄_facts hW d hK hD
  have htU₄ : t ∈ yamadaU₄ d t := hU₄eq.le (mem_sup_right (mem_zpowers t))
  intro ht
  obtain ⟨w, hw, x, hx, e⟩ := Common.exists_mul_of_le_normalizer' hX₄Z t ht
  have hxU₄ : x ∈ yamadaU₄ d t := by
    have : x = w⁻¹ * t := by rw [e, inv_mul_cancel_left]
    rw [this]
    exact mul_mem (inv_mem (hX₄U₄ hw)) htU₄
  rcases (mem_sup_zpowers_iff_of h.t_mul_t (h.t_mem_normalizer_yamadaX₂ d hK hD).1).1
      (hUZ (Subgroup.mem_inf.2 ⟨hxU₄, hx⟩)) with hxX | ⟨a, ha, rfl⟩
  · have h1 : w * x ∈ yamadaX₄ d t := mul_mem hw (hX₂X₄ hxX)
    rw [← e] at h1
    exact htX₄ h1
  · refine htZ ?_
    have := mul_mem (inv_mem (hXZ ha)) hx
    rwa [inv_mul_cancel_left] at this

theorem yamadaR₄_le_normalizers (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaR₄ d t ≤ normalizer (yamadaF₂ d t : Set G) ∧
      yamadaR₄ d t ≤ normalizer (yamadaM₂ d t : Set G) ∧
      yamadaR₄ d t ≤ normalizer (yamadaS₂ d t : Set G) := by
  obtain ⟨-, -, hR₄R₂, -⟩ := h.yamadaR₄_facts hW d hK hD
  obtain ⟨hR₄L₂, -⟩ := h.yamada_5_32_1_L₄ hW d hK hD
  obtain ⟨hRE, hEF, -⟩ := h.normalizer_yamadaR₂_le d hK hD
  have hLM : normalizer (yamadaL₂ d t : Set G) ≤ normalizer (yamadaM₂ d t : Set G) := by
    have := normalizer_le_normalizer_thompsonSubgroup (yamadaL₂ d t)
    rwa [h.yamada_5_13_2 d hK hD] at this
  have hRS : normalizer (yamadaR₂ d t : Set G) ≤ normalizer (yamadaS₂ d t : Set G) := by
    have := (h.yamada_5_15_6 d hK hD).2.2.2
    have h1 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      ((yamadaS₂ d t).subgroupOf (yamadaR₂ d t))
    rwa [subgroupOf_map_subtype, inf_of_le_left (h.yamada_5_13_3 d hK hD).2.1] at h1
  exact ⟨(hR₄R₂.trans hRE).trans hEF, hR₄L₂.trans hLM, hR₄R₂.trans hRS⟩

theorem yamada_5_32_2 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    ((yamadaF₄ d t : Set G) = (yamadaX₄ d t : Set G) * (yamadaF₂ d t : Set G) ∧
      (yamadaM₄ d t : Set G) = (yamadaX₄ d t : Set G) * (yamadaM₂ d t : Set G) ∧
      (yamadaS₄ d t : Set G) = (yamadaX₄ d t : Set G) * (yamadaS₂ d t : Set G)) ∧
    (yamadaU₄ d t ≤ normalizer (yamadaX₄ d t : Set G) ∧
      yamadaX₄ d t ⊔ zpowers t = yamadaU₄ d t ∧ t ∉ yamadaX₄ d t ∧
      yamadaX₂ d t < yamadaX₄ d t) ∧
    (yamadaF₄ d t ⊔ zpowers t = yamadaE₄ d t ∧ t ∉ yamadaF₄ d t) ∧
    (yamadaM₄ d t ⊔ zpowers t = yamadaL₄ d t ∧ t ∉ yamadaM₄ d t) ∧
    (yamadaS₄ d t ⊔ zpowers t = yamadaR₄ d t ∧ t ∉ yamadaS₄ d t) ∧
    (yamadaD₄ d t ⊔ zpowers t = yamadaC₄ d t ∧ t ∉ yamadaD₄ d t) := by
  obtain ⟨hX₄U₄, hU₄N, -, hX₂X₄, htX₄, hU₄eq, hX₄c⟩ := h.yamadaX₄_facts hW d hK hD
  obtain ⟨-, hU₄E₄, hU₄R₂, -, hsup, -⟩ := h.yamadaU₄_facts hW d hK hD
  obtain ⟨-, hE₄eq, -⟩ := h.yamada_5_32_1_E₄ hW d hK hD
  obtain ⟨hRF, hRM, hRS⟩ := h.yamadaR₄_le_normalizers hW d hK hD
  obtain ⟨-, -, -, hXF, -, -, -, -, hMS, -⟩ := d.inclusions
  obtain ⟨hE₂E₄, -⟩ := h.yamadaE₄_facts hW d hK hD
  obtain ⟨-, hR₂R₄, -⟩ := h.yamadaR₄_facts hW d hK hD
  obtain ⟨-, -, -, hL₄S, -⟩ := h.yamadaL₄_facts hW d hK hD
  obtain ⟨-, hS₂R₂, -, htS₂, hR₂S₂⟩ := h.yamada_5_13_3 d hK hD
  have hU₄R₄ : yamadaU₄ d t ≤ yamadaR₄ d t := le_sup_left.trans hsup.le
  have hX₄R₄ : yamadaX₄ d t ≤ yamadaR₄ d t := hX₄U₄.trans hU₄R₄
  have htU₄ : t ∈ yamadaU₄ d t := hU₄eq.le (mem_sup_right (mem_zpowers t))
  have hL₂eq := h.yamadaL₂_eq_sup d hK hD
  have hM₂L₂ : yamadaM₂ d t ≤ yamadaL₂ d t := le_sup_left.trans hL₂eq.ge
  have hM₂S₂ : yamadaM₂ d t ≤ yamadaS₂ d t := sup_le_sup_right hMS _
  have hX₂F₂ : yamadaX₂ d t ≤ yamadaF₂ d t := sup_le_sup_right hXF _
  have hF₂M₂ := (h.yamadaE₂_le_yamadaL₂ d hK hD).1
  have hL₂R₂ : yamadaL₂ d t ≤ yamadaR₂ d t := le_sup_left
  have hL₂L₄ : yamadaL₂ d t ≤ yamadaL₄ d t := le_sup_right
  have hsetF := coe_sup_eq_mul (hX₄R₄.trans hRF)
  have hsetM := coe_sup_eq_mul (hX₄R₄.trans hRM)
  have hsetS := coe_sup_eq_mul (hX₄R₄.trans hRS)
  have hUR : ∀ {Z : Subgroup G}, Z ≤ yamadaR₂ d t → yamadaU₄ d t ⊓ Z ≤ yamadaU₂ d t :=
    fun hZ => (inf_le_inf_left _ hZ).trans hU₄R₂.le
  have htF₄ : t ∉ yamadaF₄ d t := h.t_not_mem_yamadaX₄_sup hW d hK hD (hX₄R₄.trans hRF) hX₂F₂
    (h.t_mem_normalizer_yamadaF₂ d hK hD).2 (hUR ((hF₂M₂.trans hM₂L₂).trans hL₂R₂))
  have htM₄ : t ∉ yamadaM₄ d t := h.t_not_mem_yamadaX₄_sup hW d hK hD (hX₄R₄.trans hRM)
    (hX₂F₂.trans hF₂M₂) (h.yamada_5_13_1 d hK hD).2.2.2.2 (hUR (hM₂L₂.trans hL₂R₂))
  have htS₄ : t ∉ yamadaS₄ d t := h.t_not_mem_yamadaX₄_sup hW d hK hD (hX₄R₄.trans hRS)
    ((hX₂F₂.trans hF₂M₂).trans hM₂S₂) htS₂ (hUR hS₂R₂)
  have hE : yamadaF₄ d t ⊔ zpowers t = yamadaE₄ d t := by
    refine le_antisymm (sup_le (sup_le (hX₄U₄.trans hU₄E₄) (le_sup_left.trans hE₂E₄))
      ((zpowers_le).2 (hU₄E₄ htU₄))) ?_
    rw [hE₄eq, ← hU₄eq]
    exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  have hL : yamadaM₄ d t ⊔ zpowers t = yamadaL₄ d t := by
    refine le_antisymm (sup_le (sup_le ((hX₄U₄.trans hU₄E₄).trans inf_le_left)
      (hM₂L₂.trans hL₂L₄)) ((zpowers_le).2 ((hU₄E₄.trans inf_le_left) htU₄))) ?_
    have hC : yamadaR₄ d t ⊓ centralizer (d.J₆ : Set G) ≤ yamadaM₄ d t ⊔ zpowers t :=
      (le_sup_left : _ ≤ yamadaU₄ d t).trans (hU₄eq.ge.trans (sup_le_sup_right le_sup_left _))
    exact sup_le hC (hL₂eq.le.trans (sup_le_sup_right le_sup_right _))
  have hR : yamadaS₄ d t ⊔ zpowers t = yamadaR₄ d t := by
    refine le_antisymm (sup_le (sup_le hX₄R₄ (hS₂R₂.trans hR₂R₄))
      ((zpowers_le).2 (hU₄R₄ htU₄))) ?_
    rw [← hL₄S, ← hL]
    exact sup_le (sup_le (sup_le (le_sup_left.trans le_sup_left)
      (hM₂S₂.trans (le_sup_right.trans le_sup_left))) le_sup_right)
      ((le_sup_left.trans le_sup_right).trans le_sup_left)
  have htC₄ : t ∈ yamadaC₄ d t := by
    have htC₂ : t ∈ yamadaC₂ d t := mem_sup_right (mem_zpowers t)
    rw [← (h.yamada_5_32_1_R₄ hW d hK hD).2.2.1] at htC₂
    exact (Subgroup.mem_inf.1 htC₂).1
  have htS₄N : t ∈ normalizer (yamadaS₄ d t : Set G) :=
    mem_normalizer_sup (hU₄N htU₄) (hR₂S₂ ((le_sup_left : yamadaL₂ d t ≤ yamadaR₂ d t)
      (h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t)))))
  have hC : yamadaD₄ d t ⊔ zpowers t = yamadaC₄ d t := by
    refine le_antisymm (sup_le inf_le_right ((zpowers_le).2 htC₄)) fun x hx => ?_
    have hxR : x ∈ yamadaS₄ d t ⊔ zpowers t := hR.ge (Subgroup.mem_inf.1 hx).1
    rcases (mem_sup_zpowers_iff_of h.t_mul_t htS₄N).1 hxR with hxS | ⟨s, hs, rfl⟩
    · exact mem_sup_left (Subgroup.mem_inf.2 ⟨hxS, hx⟩)
    · have hsC : s ∈ yamadaC₄ d t := by
        have := mul_mem hx (inv_mem htC₄)
        rwa [mul_inv_cancel_right] at this
      exact mul_mem (mem_sup_left (Subgroup.mem_inf.2 ⟨hs, hsC⟩)) (mem_sup_right (mem_zpowers t))
  refine ⟨⟨hsetF, hsetM, hsetS⟩, ⟨hU₄N, hU₄eq, htX₄, lt_of_le_of_ne hX₂X₄ fun e => ?_⟩,
    ⟨hE, htF₄⟩, ⟨hL, htM₄⟩, ⟨hR, htS₄⟩, ⟨hC, fun ht => htS₄ (Subgroup.mem_inf.1 ht).1⟩⟩
  have h56 := hX₄c
  rw [← e, h.card_yamadaX₂ d hK hD] at h56
  have h4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  have := Nat.pow_right_injective (show 2 ≤ Nat.card K by omega) h56
  omega

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
