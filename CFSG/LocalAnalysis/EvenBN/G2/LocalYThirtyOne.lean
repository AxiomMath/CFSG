module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYThirty
public import CFSG.LocalAnalysis.EvenBN.G2.LocalYTwentySeven

public section


namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Torus

variable {K : Type} [Field K]
  [Finite K]

theorem eq_one_of_mem_U_of_forall_J₆ [CharP K 2] (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) {x : G} (hx : x ∈ d.U) (hfix : ∀ k ∈ d.J₆, k * x = x * k) :
    x = 1 := by
  by_contra hx1
  have h4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  have h92 := d.yamada_3_9_2_G (i := 5) (k := 0) (by decide)
  have hle : d.J₆ ≤ ⊥ := by
    rw [← (h92.2 (Or.inr (by decide))).1, ← h92.1 x hx hx1]
    exact fun k hk => Subgroup.mem_inf.2 ⟨hk, mem_centralizer_singleton_iff.2 (hfix k hk)⟩
  have hc := (d.yamada_3_9_1_G 5).2
  rw [show d.Ji 5 = d.J₆ from rfl, le_bot_iff.1 hle, Subgroup.card_bot] at hc
  omega

end Torus

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]


theorem wb_conj_mem_rootGroup_u (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    {y : G} (hy : y ∈ d.rootGroup g2r) : d.wb * y * d.wb⁻¹ ∈ d.rootGroup g2u := by
  obtain ⟨-, -, -, hwb, -, hconj⟩ := d.yamada_3_7_G (hK ▸ h.four_le)
  have hrefl : reflect .G2 g2ia g2r = g2u := List.ofFn_injective (by decide +kernel)
  have hinv : d.wb⁻¹ = d.wb := inv_eq_of_mul_eq_one_right hwb
  obtain ⟨g, hg, rfl⟩ := d.mem_image.1 hy
  obtain ⟨x, hx⟩ := mem_rootSubgroup.1 hg
  have hg' : g = ⟨pinnedX .G2 K g2r x, pinnedX_mem_adjointGroup g2r x⟩ := Subtype.ext hx.symm
  rw [hinv, hg', hconj isRoot_g2r x]
  refine d.emb_mem_image ?_
  rw [hrefl]
  exact mem_rootSubgroup.2 ⟨x, rfl⟩

theorem wb_inv_conj_mem_J₃ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    {k : G} (hk : k ∈ d.J₆) : d.wb⁻¹ * k * d.wb ∈ d.J₃ := by
  have hJ₃ : d.J₃ = d.J ⊓ centralizer (d.rootGroup g2r : Set G) :=
    d.image_inf_centralizer (Model.J K) (rootSubgroup_le_adjointGroup (K := K) (τ := .G2) g2r)
  have hJ₆ : d.J₆ = d.J ⊓ centralizer (d.rootGroup g2u : Set G) :=
    d.image_inf_centralizer (Model.J K) (rootSubgroup_le_adjointGroup (K := K) (τ := .G2) g2u)
  rw [hJ₆] at hk
  rw [hJ₃]
  have hwbJ := h.wb_mem_normalizer_J d hK
  refine Subgroup.mem_inf.2 ⟨?_, mem_centralizer_iff.2 fun y hy => ?_⟩
  · have := (mem_normalizer_iff.1 (inv_mem hwbJ) k).1 (Subgroup.mem_inf.1 hk).1
    rwa [inv_inv] at this
  · have e := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hk).2 _ (h.wb_conj_mem_rootGroup_u d hK hy)
    calc y * (d.wb⁻¹ * k * d.wb) = d.wb⁻¹ * ((d.wb * y * d.wb⁻¹) * k) * d.wb := by group
      _ = d.wb⁻¹ * (k * (d.wb * y * d.wb⁻¹)) * d.wb := by rw [e]
      _ = d.wb⁻¹ * k * d.wb * y := by group

theorem eq_one_of_mem_U_of_forall_J₆_conj (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) {x : G} (hx : x ∈ d.U)
    (hfix : ∀ k ∈ d.J₆, (d.wb⁻¹ * k * d.wb) * x = x * (d.wb⁻¹ * k * d.wb)) : x = 1 := by
  by_contra hx1
  have h4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  have h92 := d.yamada_3_9_2_G (i := 2) (k := 0) (by decide)
  have hbot : d.Ji 2 ⊓ centralizer {x} = ⊥ := by
    rw [h92.1 x hx hx1, (h92.2 (Or.inr (by decide))).1]
  have hle : d.J₆ ≤ ⊥ := fun k hk => by
    have hk' : d.wb⁻¹ * k * d.wb ∈ d.Ji 2 ⊓ centralizer {x} := Subgroup.mem_inf.2
      ⟨h.wb_inv_conj_mem_J₃ d hK hk, mem_centralizer_singleton_iff.2 (hfix k hk)⟩
    rw [hbot, Subgroup.mem_bot] at hk'
    rw [Subgroup.mem_bot]
    calc k = d.wb * (d.wb⁻¹ * k * d.wb) * d.wb⁻¹ := by group
      _ = 1 := by rw [hk']; group
  have hc := (d.yamada_3_9_1_G 5).2
  rw [show d.Ji 5 = d.J₆ from rfl, le_bot_iff.1 hle, Subgroup.card_bot] at hc
  omega

theorem eq_one_of_mem_yamadaU₁_of_forall (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {T : Set G}
    (hTt : ∀ k ∈ T, k * t = t * k) (hTU : ∀ x ∈ d.U, (∀ k ∈ T, k * x = x * k) → x = 1)
    {x : G} (hx : x ∈ yamadaU₁ d t) (hfix : ∀ k ∈ T, k * x = x * k) : x = 1 := by
  obtain ⟨-, -, -, -, -, hcross, -⟩ := hD.exists_coords hK
  have hc : x⁻¹ * t * x * t = 1 := by
    refine hTU _ (hcross hx) fun k hk => ?_
    have hkx := hfix k hk
    have hkt := hTt k hk
    have hkx' : k * x⁻¹ = x⁻¹ * k := by
      calc k * x⁻¹ = x⁻¹ * (x * k) * x⁻¹ := by group
        _ = x⁻¹ * (k * x) * x⁻¹ := by rw [hkx]
        _ = x⁻¹ * k := by group
    calc k * (x⁻¹ * t * x * t) = k * x⁻¹ * t * x * t := by group
      _ = x⁻¹ * k * t * x * t := by rw [hkx']
      _ = x⁻¹ * (k * t) * x * t := by group
      _ = x⁻¹ * (t * k) * x * t := by rw [hkt]
      _ = x⁻¹ * t * (k * x) * t := by group
      _ = x⁻¹ * t * (x * k) * t := by rw [hkx]
      _ = x⁻¹ * t * x * (k * t) := by group
      _ = x⁻¹ * t * x * (t * k) := by rw [hkt]
      _ = x⁻¹ * t * x * t * k := by group
  have hxt : x ∈ centralizer ({t} : Set G) := by
    have e1 : t * x * t = x := by
      calc t * x * t = x * (x⁻¹ * t * x * t) := by group
        _ = x := by rw [hc, mul_one]
    rw [mem_centralizer_singleton_iff]
    calc x * t = t * x * t * t := by rw [e1]
      _ = t * x * (t * t) := by group
      _ = t * x := by rw [h.t_mul_t, mul_one]
  have hxU : x ∈ d.U := by
    rw [← hD.inf_centralizer]
    exact Subgroup.mem_inf.2 ⟨hx, hxt⟩
  exact hTU x hxU hfix

theorem eq_one_of_mem_yamadaY₂_of_forall_J₆ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {x : G} (hx : x ∈ yamadaY₂ d t)
    (hfix : ∀ k ∈ d.J₆, k * x = x * k) : x = 1 := by
  obtain ⟨hJ₆J, -⟩ := h.J₆_facts d hK
  obtain ⟨⟨hU₁U₁', hU₁'C⟩, -⟩ := h.yamada_5_13_1 d hK hD
  have hwbJ := h.wb_mem_normalizer_J d hK
  have hkU₁ : ∀ k ∈ d.J, k ∈ normalizer (yamadaU₁ d t : Set G) := fun k hk =>
    (h.centralizer_inf_normalizer_S_le d hK hD).2.1 (h.J_le_centralizer_inf_normalizer_S d hk)
  have hk' : ∀ k ∈ d.J₆, d.wb⁻¹ * k * d.wb ∈ d.J := fun k hk => by
    have := (mem_normalizer_iff.1 (inv_mem hwbJ) k).1 (hJ₆J hk)
    rwa [inv_inv] at this
  have hkt : ∀ k ∈ d.J, k * t = t * k := fun k hk => mem_centralizer_singleton_iff.1
    (Subgroup.mem_inf.1 (h.J_le_centralizer_inf_normalizer_S d hk)).1
  have hconj : ∀ k u : G, k * (d.wb * u * d.wb⁻¹) * k⁻¹ =
      d.wb * ((d.wb⁻¹ * k * d.wb) * u * (d.wb⁻¹ * k * d.wb)⁻¹) * d.wb⁻¹ := fun k u => by group
  obtain ⟨u, hu, u', hu', rfl⟩ := Common.exists_mul_of_le_normalizer
    (hU₁'C.trans (Subgroup.centralizer_le_normalizer _)) x hx
  obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.1 hu'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hfix ⊢
  have hsplit : ∀ k ∈ d.J₆, k * u * k⁻¹ = u ∧
      (d.wb⁻¹ * k * d.wb) * u₀ * (d.wb⁻¹ * k * d.wb)⁻¹ = u₀ := fun k hk => by
    have e := hfix k hk
    have hku : k * u * k⁻¹ ∈ yamadaU₁ d t := (mem_normalizer_iff.1 (hkU₁ k (hJ₆J hk)) u).1 hu
    have hku₀ : (d.wb⁻¹ * k * d.wb) * u₀ * (d.wb⁻¹ * k * d.wb)⁻¹ ∈ yamadaU₁ d t :=
      (mem_normalizer_iff.1 (hkU₁ _ (hk' k hk)) u₀).1 hu₀
    have e1 : u⁻¹ * (k * u * k⁻¹) = d.wb * (u₀ *
        ((d.wb⁻¹ * k * d.wb) * u₀ * (d.wb⁻¹ * k * d.wb)⁻¹)⁻¹) * d.wb⁻¹ := by
      calc u⁻¹ * (k * u * k⁻¹) = u⁻¹ * (k * (u * (d.wb * u₀ * d.wb⁻¹)) * k⁻¹) *
            (k * (d.wb * u₀ * d.wb⁻¹) * k⁻¹)⁻¹ := by group
        _ = d.wb * u₀ * d.wb⁻¹ * (k * (d.wb * u₀ * d.wb⁻¹) * k⁻¹)⁻¹ := by rw [e]; group
        _ = d.wb * (u₀ * ((d.wb⁻¹ * k * d.wb) * u₀ * (d.wb⁻¹ * k * d.wb)⁻¹)⁻¹) * d.wb⁻¹ := by
          rw [hconj k u₀]; group
    have hmem : u⁻¹ * (k * u * k⁻¹) ∈ yamadaU₁ d t ⊓
        (yamadaU₁ d t).map (MulAut.conj d.wb).toMonoidHom := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hu) hku, Subgroup.mem_map.2
        ⟨u₀ * ((d.wb⁻¹ * k * d.wb) * u₀ * (d.wb⁻¹ * k * d.wb)⁻¹)⁻¹,
          mul_mem hu₀ (inv_mem hku₀), ?_⟩⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact e1.symm
    rw [hU₁U₁', Subgroup.mem_bot] at hmem
    have hku' : k * u * k⁻¹ = u := by
      calc k * u * k⁻¹ = u * (u⁻¹ * (k * u * k⁻¹)) := by group
        _ = u := by rw [hmem, mul_one]
    refine ⟨hku', ?_⟩
    have e2 : d.wb * ((d.wb⁻¹ * k * d.wb) * u₀ * (d.wb⁻¹ * k * d.wb)⁻¹) * d.wb⁻¹ =
        d.wb * u₀ * d.wb⁻¹ := by
      rw [← hconj k u₀]
      calc k * (d.wb * u₀ * d.wb⁻¹) * k⁻¹ =
            (k * u * k⁻¹)⁻¹ * (k * (u * (d.wb * u₀ * d.wb⁻¹)) * k⁻¹) := by group
        _ = d.wb * u₀ * d.wb⁻¹ := by rw [hku', e]; group
    exact mul_left_cancel (mul_right_cancel e2)
  have hu1 : u = 1 := h.eq_one_of_mem_yamadaU₁_of_forall d hK hD (T := d.J₆)
    (fun k hk => hkt k (hJ₆J hk)) (fun y hy hy' => h.eq_one_of_mem_U_of_forall_J₆ d hK hy hy')
    hu fun k hk => by
      calc k * u = k * u * k⁻¹ * k := by group
        _ = u * k := by rw [(hsplit k hk).1]
  have hu₀1 : u₀ = 1 := h.eq_one_of_mem_yamadaU₁_of_forall d hK hD
    (T := (fun k => d.wb⁻¹ * k * d.wb) '' (d.J₆ : Set G))
    (by rintro _ ⟨k, hk, rfl⟩; exact hkt _ (hk' k hk))
    (fun y hy hy' => h.eq_one_of_mem_U_of_forall_J₆_conj d hK hy fun k hk => hy' _ ⟨k, hk, rfl⟩)
    hu₀ (by
      rintro _ ⟨k, hk, rfl⟩
      calc d.wb⁻¹ * k * d.wb * u₀ =
            (d.wb⁻¹ * k * d.wb) * u₀ * (d.wb⁻¹ * k * d.wb)⁻¹ * (d.wb⁻¹ * k * d.wb) := by group
        _ = u₀ * (d.wb⁻¹ * k * d.wb) := by rw [(hsplit k hk).2])
  rw [hu1, hu₀1]
  group

theorem yamadaX₄_core (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d)
    (hYX : yamadaX₄ d t ≤ centralizer (yamadaY₂ d t : Set G)) :
    CFSG.IsElementaryAbelian 2 (yamadaX₄ d t) ∧ Nat.card (yamadaX₄ d t) = Nat.card K ^ 6 ∧
      yamadaR₄ d t ⊓ centralizer (yamadaX₂ d t : Set G) = yamadaX₄ d t ∧
      centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤
        normalizer (yamadaX₄ d t : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hX₄U₄, hU₄N, hJX₄, hX₂X₄, -, hU₄eq, hX₄c⟩ := h.yamadaX₄_facts hW d hK hD
  obtain ⟨hX₄R₄, hX₄R₂, -⟩ := h.yamadaX₄_le_yamadaR₄ hW d hK hD
  obtain ⟨-, -, -, -, -, -, hU₄X₂, hU₄Y₂⟩ := h.yamadaU₄_facts hW d hK hD
  obtain ⟨hJ₆J, -, hC, -⟩ := h.J₆_facts d hK
  obtain ⟨hJ₂J, -, -, -, htr, -⟩ := h.J₂_facts d hK
  obtain ⟨hR₄R, -⟩ := h.yamadaR₄_facts hW d hK hD
  obtain ⟨-, -, -, hXF, -, hFD, -, hDS, -⟩ := d.inclusions
  obtain ⟨-, hXdef, -⟩ := d.yamada_defs
  have h4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  have hX₄p : IsPGroup 2 (yamadaX₄ d t) := (h.isPGroup_yamadaRstar d).to_le (hX₄R₄.trans hR₄R)
  have hY₂X₂ : yamadaY₂ d t ≤ yamadaX₂ d t := le_sup_right
  have hJ₆X₄ : d.J₆ ≤ normalizer (yamadaX₄ d t : Set G) := fun j hj => hJX₄ (hJ₆J hj)
  have hJY₂ := h.J_le_normalizer_yamadaY₂ d hK hD
  have hJ₆Y₂ : d.J₆ ≤ normalizer (yamadaY₂ d t : Set G) := fun j hj => hJY₂ (hJ₆J hj)
  have hJX₂ : d.J ≤ normalizer (yamadaX₂ d t : Set G) :=
    (h.J_le_normalizer_yamadaU₄ hW d hK hD).2.trans (h.normalizer_yamadaU₂_le hW d hK hD).1
  have hJ₆X₂ : d.J₆ ≤ normalizer (yamadaX₂ d t : Set G) := fun j hj => hJX₂ (hJ₆J hj)
  have hAS : d.rootGroup g2u ≤ d.S := hC.ge.trans inf_le_left
  have hAX : d.rootGroup g2u ≤ d.X := le_sup_left.trans hXdef.le
  have hXY₂ : d.X ≤ normalizer (yamadaY₂ d t : Set G) :=
    (hXF.trans (hFD.trans hDS)).trans (h.yamada_5_13_3 d hK hD).1
  have hXCY₂ := h.X_le_centralizer_yamadaY₂ d hK hD
  have hY₂Z : yamadaY₂ d t ≤ centralizer (yamadaX₄ d t : Set G) :=
    (Subgroup.le_centralizer_iff).1 hYX
  have hA1 : ∀ w ∈ yamadaX₂ d t, ∀ j ∈ d.J₆, w⁻¹ * (j * w * j⁻¹) ∈ yamadaY₂ d t :=
    fun w hw j hj => by
      obtain ⟨a, ha, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hXY₂ w hw
      obtain ⟨-, haY⟩ := h.J₆_conj_X d hK hD hj ha
      rw [show (a * y)⁻¹ * (j * (a * y) * j⁻¹) = y⁻¹ * (a⁻¹ * (j * a * j⁻¹)) * (j * y * j⁻¹) by
        group]
      exact mul_mem (mul_mem (inv_mem hy) (h.Y_le_yamadaY₂ d hK hD haY))
        ((mem_normalizer_iff.1 (hJ₆Y₂ hj) y).1 hy)
  have hA2 : ∀ w ∈ yamadaX₄ d t, ∀ j ∈ d.J₆, w⁻¹ * (j * w * j⁻¹) ∈ yamadaX₂ d t :=
    fun w hw j hj => by
      rw [← hX₄R₂]
      exact Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hw) ((mem_normalizer_iff.1 (hJ₆X₄ hj) w).1 hw),
        h.inv_mul_conj_mem_yamadaR₂_of_J₆ hW d hK hD (hX₄R₄ hw) hj⟩
  have hA : ∀ w ∈ yamadaX₄ d t, ∀ j ∈ d.J₆, w⁻¹ * (j * w * j⁻¹) ∈ yamadaY₂ d t :=
    fun w hw j hj => by
      obtain ⟨c, hc, n, hn, rfl⟩ := exists_centralizer_J₆_mul d hX₂X₄ (hX₄U₄.trans hU₄X₂)
        hJ₆X₄ hJ₆X₂ hX₄p hw fun j hj => hA2 w hw j hj
      have hcj : j * c = c * j := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 j hj
      rw [show (c * n)⁻¹ * (j * (c * n) * j⁻¹) = n⁻¹ * (c⁻¹ * (j * c) * n * j⁻¹) by group, hcj,
        show n⁻¹ * (c⁻¹ * (c * j) * n * j⁻¹) = n⁻¹ * (j * n * j⁻¹) by group]
      exact hA1 n hn j hj
  have hdec : ∀ w ∈ yamadaX₄ d t, ∃ c ∈ yamadaX₄ d t ⊓ centralizer (d.J₆ : Set G),
      ∃ y ∈ yamadaY₂ d t, w = c * y := fun w hw =>
    exists_centralizer_J₆_mul d (hY₂X₂.trans hX₂X₄) (hX₄U₄.trans hU₄Y₂) hJ₆X₄ hJ₆Y₂ hX₄p hw
      (hA w hw)
  have hCX₂ : (yamadaX₄ d t ⊓ centralizer (d.J₆ : Set G)) ⊓ yamadaX₂ d t = d.rootGroup g2u := by
    refine le_antisymm (fun x hx => ?_) (le_inf (le_inf ((hAX.trans le_sup_left).trans hX₂X₄)
      (hC.ge.trans inf_le_right)) (hAX.trans le_sup_left))
    obtain ⟨hxC, hxX₂⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨a, ha, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hXY₂ x hxX₂
    rw [← hXdef] at ha
    obtain ⟨s, hs, y', hy', rfl⟩ :=
      Common.exists_mul_of_le_normalizer' (hAS.trans d.S_le_normalizers.2.1) a ha
    have hsJ : s ∈ centralizer (d.J₆ : Set G) := (Subgroup.mem_inf.1 (hC.ge hs)).2
    have hyy : y' * y ∈ yamadaY₂ d t := mul_mem (h.Y_le_yamadaY₂ d hK hD hy') hy
    have hyJ : y' * y = 1 := h.eq_one_of_mem_yamadaY₂_of_forall_J₆ d hK hD hyy fun k hk => by
      have e1 := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hxC).2 k hk
      have e2 : k * s = s * k := mem_centralizer_iff.1 hsJ k hk
      calc k * (y' * y) = s⁻¹ * (s * k * (y' * y)) := by group
        _ = s⁻¹ * (k * s * (y' * y)) := by rw [← e2]
        _ = s⁻¹ * (k * (s * y' * y)) := by group
        _ = s⁻¹ * (s * y' * y * k) := by rw [e1]
        _ = y' * y * k := by group
    rw [mul_assoc, hyJ, mul_one]
    exact hs
  set C := yamadaX₄ d t ⊓ centralizer (d.J₆ : Set G) with hCdef
  have hCp : IsPGroup 2 C := hX₄p.to_le inf_le_left
  have hSuC : d.rootGroup g2u ≤ C := hCX₂.ge.trans inf_le_left
  have hCN : C ≤ normalizer (d.rootGroup g2u : Set G) := fun c hc => by
    rw [← hCX₂]
    exact Common.mem_normalizer_inf (Subgroup.le_normalizer hc)
      ((hX₄U₄.trans hU₄X₂) (Subgroup.mem_inf.1 hc).1)
  have hAc : Nat.card (d.rootGroup g2u) = Nat.card K :=
    (d.card_image (rootSubgroup_le_adjointGroup (K := K) (τ := .G2) g2u)).trans
      (card_rootSubgroup (τ := .G2) (K := K) g2u)
  have hSu1 : d.rootGroup g2u ≠ ⊥ := fun h0 => by
    rw [h0, Subgroup.card_bot] at hAc
    omega
  have hJ₂Cn : ∀ k ∈ d.J₂, k ∈ normalizer ((centralizer (C : Set G) : Subgroup G) : Set G) :=
    fun k hk => by
      have hkC : k ∈ normalizer (C : Set G) := Common.mem_normalizer_inf (hJX₄ (hJ₂J hk))
        (Subgroup.le_normalizer (mem_centralizer_iff.2 fun y hy => J_mul_comm d (hJ₆J hy)
          (hJ₂J hk)))
      exact mem_normalizer_centralizer hkC
  obtain ⟨x₀, hx₀, hx₀1, hx₀C⟩ := exists_ne_one_mem_centralizer_of_le hCp hSuC hCN hSu1
  have hSuZ : d.rootGroup g2u ≤ centralizer (C : Set G) := fun s hs => by
    by_cases hs1 : s = 1
    · rw [hs1]
      exact one_mem _
    obtain ⟨k, hk, rfl⟩ := htr x₀ hx₀ hx₀1 s hs hs1
    exact (mem_normalizer_iff.1 (hJ₂Cn k hk) x₀).1 hx₀C
  have hsX₄ : d.rootGroup g2u ≤ centralizer (yamadaX₄ d t : Set G) := fun s hs =>
    mem_centralizer_iff.2 fun w hw => by
      obtain ⟨c, hc, y, hy, rfl⟩ := hdec w hw
      have e1 : c * s = s * c := mem_centralizer_iff.1 (hSuZ hs) c hc
      have e2 : y * s = s * y := mem_centralizer_iff.1 (hXCY₂ (hAX hs)) y hy
      calc c * y * s = c * (y * s) := by group
        _ = c * (s * y) := by rw [e2]
        _ = c * s * y := by group
        _ = s * c * y := by rw [e1]
        _ = s * (c * y) := by group
  have hX₂Z : yamadaX₂ d t ≤ centralizer (yamadaX₄ d t : Set G) := fun x hx => by
    obtain ⟨a, ha, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hXY₂ x hx
    rw [← hXdef] at ha
    obtain ⟨s, hs, y', hy', rfl⟩ :=
      Common.exists_mul_of_le_normalizer' (hAS.trans d.S_le_normalizers.2.1) a ha
    exact mul_mem (mul_mem (hsX₄ hs) (hY₂Z (h.Y_le_yamadaY₂ d hK hD hy'))) (hY₂Z hy)
  obtain ⟨⟨-, -, hsetS⟩, -, -, -, ⟨hR, -⟩, -⟩ := h.yamada_5_32_2 hW d hK hD
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  have htU₄ : t ∈ yamadaU₄ d t := hU₄eq.le (mem_sup_right (mem_zpowers t))
  obtain ⟨hSY₂, -, -, -, hR₂S₂⟩ := h.yamada_5_13_3 d hK hD
  have htS₄N : t ∈ normalizer (yamadaS₄ d t : Set G) :=
    mem_normalizer_sup (hU₄N htU₄) (hR₂S₂ ((le_sup_left : yamadaL₂ d t ≤ yamadaR₂ d t) htL₂))
  have hX₂ab : yamadaX₂ d t ≤ centralizer (yamadaX₂ d t : Set G) :=
    h.yamadaX₂_le_centralizer d hK hD
  have hLX := (d.yamada_3_17_2_G).1
  have hXC : ∀ z ∈ centralizer (yamadaX₂ d t : Set G), z ∈ centralizer (d.X : Set G) :=
    fun z hz => Subgroup.centralizer_le (le_sup_left : d.X ≤ yamadaX₂ d t) hz
  have hdecS : ∀ s₄ ∈ yamadaS₄ d t, ∃ w ∈ yamadaX₄ d t, ∃ s ∈ d.S, ∃ y ∈ yamadaY₂ d t,
      s₄ = w * (s * y) := fun s₄ hs₄ => by
    have hs₄' : s₄ ∈ ((yamadaS₄ d t : Subgroup G) : Set G) := hs₄
    rw [hsetS] at hs₄'
    obtain ⟨w, hw, s₂, hs₂, rfl⟩ := Set.mem_mul.1 hs₄'
    obtain ⟨s, hs, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hSY₂ s₂ hs₂
    exact ⟨w, hw, s, hs, y, hy, rfl⟩
  have hsX : ∀ s ∈ d.S, s ∈ centralizer (d.X : Set G) → s ∈ d.X := fun s hs hsC => by
    rw [← hLX]
    exact Subgroup.mem_inf.2 ⟨d.image_le _ hs, hsC⟩
  have hCR₄ : yamadaR₄ d t ⊓ centralizer (yamadaX₂ d t : Set G) = yamadaX₄ d t := by
    refine le_antisymm (fun x hx => ?_) (le_inf hX₄R₄ ((Subgroup.le_centralizer_iff).1 hX₂Z))
    obtain ⟨hxR, hxC⟩ := Subgroup.mem_inf.1 hx
    rw [← hR] at hxR
    rcases (mem_sup_zpowers_iff_of h.t_mul_t htS₄N).1 hxR with hxS | ⟨s₄, hs₄, rfl⟩
    · obtain ⟨w, hw, s, hs, y, hy, rfl⟩ := hdecS x hxS
      have hsC : s ∈ centralizer (d.X : Set G) := by
        have := mul_mem (mul_mem (inv_mem ((Subgroup.le_centralizer_iff).1 hX₂Z hw)) hxC)
          (inv_mem (hX₂ab (hY₂X₂ hy)))
        rw [show w⁻¹ * (w * (s * y)) * y⁻¹ = s by group] at this
        exact hXC s this
      exact mul_mem hw (mul_mem (((le_sup_left : d.X ≤ yamadaX₂ d t).trans hX₂X₄) (hsX s hs hsC))
        ((hY₂X₂.trans hX₂X₄) hy))
    · exfalso
      obtain ⟨w, hw, s, hs, y, hy, rfl⟩ := hdecS s₄ hs₄
      have htC : t ∈ centralizer (d.X : Set G) := mem_centralizer_iff.2 fun z hz =>
        mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hz))
      have hwC : w ∈ centralizer (d.X : Set G) :=
        hXC w ((Subgroup.le_centralizer_iff).1 hX₂Z hw)
      have hyC : y ∈ centralizer (d.X : Set G) := hXC y (hX₂ab (hY₂X₂ hy))
      have hsC : s ∈ centralizer (d.X : Set G) := by
        have := mul_mem (mul_mem (mul_mem (inv_mem hwC) (hXC _ hxC)) (inv_mem htC)) (inv_mem hyC)
        rwa [show w⁻¹ * (w * (s * y) * t) * t⁻¹ * y⁻¹ = s by group] at this
      have hsX' : s ∈ d.X := hsX s hs hsC
      have htX₂ : t ∈ centralizer (yamadaX₂ d t : Set G) := by
        have := mul_mem (mul_mem (mul_mem (inv_mem (hX₂ab (hY₂X₂ hy)))
          (inv_mem (hX₂ab ((le_sup_left : d.X ≤ yamadaX₂ d t) hsX'))))
          (inv_mem ((Subgroup.le_centralizer_iff).1 hX₂Z hw))) hxC
        rwa [show y⁻¹ * s⁻¹ * w⁻¹ * (w * (s * y) * t) = t by group] at this
      have hle : yamadaX₂ d t ≤ d.X := by
        rw [← h.yamadaX₂_inf_centralizer d hK hD]
        exact le_inf le_rfl fun z hz => mem_centralizer_singleton_iff.2
          (mem_centralizer_iff.1 htX₂ z hz)
      have hc := Subgroup.card_le_of_le hle
      rw [h.card_yamadaX₂ d hK hD, d.cards.2.2.1] at hc
      exact absurd hc (not_le.2 (pow_lt_pow_right₀ (by omega : 1 < Nat.card K)
        (by norm_num : 3 < 5)))
  have hNX₄ : centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤
      normalizer (yamadaX₄ d t : Set G) := fun g hg => by
    have hgU : g ∈ normalizer (yamadaU₂ d t : Set G) := (h.le_normalizer_yamadaU₂ d hK hD).1 hg
    rw [← hCR₄]
    exact Common.mem_normalizer_inf (LieType.BorelTits.le_normalizer_pCoreOf 2 _ hgU)
      (mem_normalizer_centralizer ((h.normalizer_yamadaU₂_le hW d hK hD).1 hgU))
  have hsqS : ∀ w ∈ yamadaX₄ d t, w * w ∈ d.rootGroup g2u := fun w hw => by
    obtain ⟨c, hc, y, hy, rfl⟩ := hdec w hw
    have hcy : c * y = y * c := mem_centralizer_iff.1 (hY₂Z hy) c (Subgroup.mem_inf.1 hc).1
    rw [show c * y * (c * y) = c * (y * c) * y by group, ← hcy,
      show c * (c * y) * y = c * c * (y * y) by group, h.yamadaY₂_mul_self hW d hK hD hy,
      mul_one, ← hCX₂]
    exact Subgroup.mem_inf.2 ⟨mul_mem hc hc,
      h.mul_self_mem_yamadaX₂ hW d hK hD (hX₄U₄ (Subgroup.mem_inf.1 hc).1)⟩
  have hsq : ∀ w ∈ yamadaX₄ d t, w * w = 1 := by
    intro w₀ hw₀
    by_contra hw₀1
    have hSN : d.S ≤ normalizer (d.rootGroup g2u : Set G) := fun σ hσ => by
      have hσX₄ : σ ∈ normalizer (yamadaX₄ d t : Set G) := hNX₄ (Subgroup.mem_inf.2
        ⟨h.L_le_centralizer (d.image_le _ hσ), Subgroup.le_normalizer hσ⟩)
      refine mem_normalizer_of_conj_mem fun s hs => ?_
      by_cases hs1 : s = 1
      · rw [hs1, mul_one, mul_inv_cancel]
        exact one_mem _
      obtain ⟨k, hk, rfl⟩ := htr _ (hsqS w₀ hw₀) hw₀1 s hs hs1
      have hkw : k * w₀ * k⁻¹ ∈ yamadaX₄ d t := (mem_normalizer_iff.1 (hJX₄ (hJ₂J hk)) w₀).1 hw₀
      rw [show σ * (k * (w₀ * w₀) * k⁻¹) * σ⁻¹ =
        (σ * (k * w₀ * k⁻¹) * σ⁻¹) * (σ * (k * w₀ * k⁻¹) * σ⁻¹) by group]
      exact hsqS _ ((mem_normalizer_iff.1 hσX₄ _).1 hkw)
    obtain ⟨x, hx, hx1, hxC⟩ := exists_ne_one_mem_centralizer_of_le d.isSylowOf_S.isPGroup hAS
      hSN hSu1
    have hxU : x ∈ d.U := by
      rw [← (d.yamada_3_12_centers).1]
      exact Subgroup.mem_inf.2 ⟨hAS hx, hxC⟩
    have hxY : x ∈ d.Y ⊓ d.rootGroup g2u := Subgroup.mem_inf.2 ⟨d.inclusions.1 hxU, hx⟩
    rw [Y_inf_rootGroup_u d, Subgroup.mem_bot] at hxY
    exact hx1 hxY
  have hcomm : ∀ x ∈ yamadaX₄ d t, ∀ y ∈ yamadaX₄ d t, x * y = y * x := fun x hx y hy => by
    have h1 := hsq _ (mul_mem hx hy)
    have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x hx)
    have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hsq y hy)
    calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hx', hy']
  exact ⟨isElementaryAbelian_two_of_forall hcomm hsq, hX₄c, hCR₄, hNX₄⟩

theorem yamadaS₄_inf_yamadaR₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaS₄ d t ⊓ yamadaR₂ d t = yamadaS₂ d t := by
  obtain ⟨⟨-, -, hsetS⟩, -⟩ := h.yamada_5_32_2 hW d hK hD
  obtain ⟨-, hX₄R₂, -⟩ := h.yamadaX₄_le_yamadaR₄ hW d hK hD
  obtain ⟨-, hS₂R₂, -⟩ := h.yamada_5_13_3 d hK hD
  have hX₂S₂ : yamadaX₂ d t ≤ yamadaS₂ d t := sup_le_sup_right
    (d.inclusions.2.2.2.1.trans (d.inclusions.2.2.2.2.2.1.trans
      d.inclusions.2.2.2.2.2.2.2.1)) _
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right hS₂R₂)
  obtain ⟨hxS₄, hxR₂⟩ := Subgroup.mem_inf.1 hx
  have hxS₄' : x ∈ ((yamadaS₄ d t : Subgroup G) : Set G) := hxS₄
  rw [hsetS] at hxS₄'
  obtain ⟨w, hw, s, hs, rfl⟩ := Set.mem_mul.1 hxS₄'
  have hwR₂ : w ∈ yamadaR₂ d t := by
    have := mul_mem hxR₂ (inv_mem (hS₂R₂ hs))
    rwa [mul_inv_cancel_right] at this
  exact mul_mem (hX₂S₂ (hX₄R₂.le (Subgroup.mem_inf.2 ⟨hw, hwR₂⟩))) hs

theorem yamadaS₄_center (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d)
    (hUX : yamadaX₄ d t ≤ centralizer (yamadaU₁ d t : Set G))
    (hXY : ∀ w ∈ yamadaX₄ d t, ∀ y ∈ yamadaY₂ d t, w * y * w⁻¹ * y⁻¹ ∈ yamadaU₁ d t) :
    yamadaS₄ d t ⊓ centralizer (yamadaS₄ d t : Set G) = yamadaU₁ d t ∧
      (Subgroup.upperCentralSeries (yamadaS₄ d t) 1).map (yamadaS₄ d t).subtype =
        yamadaU₁ d t ∧
      (Subgroup.upperCentralSeries (yamadaS₄ d t) 2).map (yamadaS₄ d t).subtype =
        yamadaY₂ d t := by
  obtain ⟨⟨-, -, hsetS⟩, -⟩ := h.yamada_5_32_2 hW d hK hD
  obtain ⟨hZS₂, -⟩ := h.yamada_5_13_5 d hK hD
  have hS₂S₄ : yamadaS₂ d t ≤ yamadaS₄ d t := le_sup_right
  have hU₁S₂ : yamadaU₁ d t ≤ yamadaS₂ d t := (yamadaU₁_le_yamadaY₂ d t).trans le_sup_right
  have hY₂S₂ : yamadaY₂ d t ≤ yamadaS₂ d t := le_sup_right
  have hS₁S₂ : yamadaS₁ d t ≤ yamadaS₂ d t := by
    rw [h.yamadaS₁_eq_sup d hK hD]
    exact sup_le_sup_left (yamadaU₁_le_yamadaY₂ d t) _
  have hU₁S₁ : yamadaU₁ d t ≤ yamadaS₁ d t := by
    rw [h.yamadaS₁_eq_sup d hK hD]
    exact le_sup_right
  obtain ⟨-, -, -, -, ⟨hR, -⟩, -⟩ := h.yamada_5_32_2 hW d hK hD
  have hS₄R₄ : yamadaS₄ d t ≤ yamadaR₄ d t := le_sup_left.trans hR.le
  have hR₄R₅ : yamadaR₄ d t ≤ yamadaR₅ d t :=
    le_sup_right.trans (h.yamada_5_27_2 hW d hK hD).1.1.ge
  have hS₁N : ∀ x ∈ yamadaS₄ d t, x ∈ normalizer (yamadaS₁ d t : Set G) → x ∈ yamadaS₂ d t :=
    fun x hx hxN => by
      rw [← h.yamadaS₄_inf_yamadaR₂ hW d hK hD]
      refine Subgroup.mem_inf.2 ⟨hx, ?_⟩
      rw [← (h.yamada_5_28 hW d hK hD).2.1]
      exact Subgroup.mem_inf.2 ⟨hR₄R₅ (hS₄R₄ hx), hxN⟩
  have hU₁C : yamadaU₁ d t ≤ centralizer (yamadaS₄ d t : Set G) := by
    rw [← Subgroup.le_centralizer_iff]
    show yamadaX₄ d t ⊔ yamadaS₂ d t ≤ _
    exact sup_le hUX ((Subgroup.le_centralizer_iff).1 (hZS₂.ge.trans inf_le_right))
  have hZ : yamadaS₄ d t ⊓ centralizer (yamadaS₄ d t : Set G) = yamadaU₁ d t := by
    refine le_antisymm (fun z hz => ?_) (le_inf (hU₁S₂.trans hS₂S₄) hU₁C)
    obtain ⟨hzS, hzC⟩ := Subgroup.mem_inf.1 hz
    have hzS₂ := hS₁N z hzS (Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (hS₁S₂.trans hS₂S₄) hzC))
    rw [← hZS₂]
    exact Subgroup.mem_inf.2 ⟨hzS₂, Subgroup.centralizer_le hS₂S₄ hzC⟩
  have hiff : ∀ {x : G}, x ∈ yamadaS₄ d t →
      (x ∈ yamadaY₂ d t ↔ ∀ g ∈ yamadaS₄ d t, x * g * x⁻¹ * g⁻¹ ∈ yamadaU₁ d t) := by
    intro x hx
    constructor
    · intro hxY g hg
      have hg' : g ∈ ((yamadaS₄ d t : Subgroup G) : Set G) := hg
      rw [hsetS] at hg'
      obtain ⟨w, hw, s, hs, rfl⟩ := Set.mem_mul.1 hg'
      have h1 : x * w * x⁻¹ * w⁻¹ ∈ yamadaU₁ d t := by
        have := inv_mem (hXY w hw x hxY)
        rwa [show (w * x * w⁻¹ * x⁻¹)⁻¹ = x * w * x⁻¹ * w⁻¹ by group] at this
      have h2 := ((h.mem_yamadaY₂_iff d hK hD (hY₂S₂ hxY)).1 hxY) s hs
      have h3 : w * (x * s * x⁻¹ * s⁻¹) * w⁻¹ = x * s * x⁻¹ * s⁻¹ := by
        rw [← mem_centralizer_iff.1 (hUX hw) _ h2, mul_inv_cancel_right]
      rw [show x * (w * s) * x⁻¹ * (w * s)⁻¹ =
        (x * w * x⁻¹ * w⁻¹) * (w * (x * s * x⁻¹ * s⁻¹) * w⁻¹) by group, h3]
      exact mul_mem h1 h2
    · intro hc
      have hxN : x ∈ normalizer (yamadaS₁ d t : Set G) := mem_normalizer_of_conj_mem fun y hy => by
        rw [show x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y by group]
        exact mul_mem (hU₁S₁ (hc y (hS₂S₄ (hS₁S₂ hy)))) hy
      have hxS₂ := hS₁N x hx hxN
      exact (h.mem_yamadaY₂_iff d hK hD hxS₂).2 fun g hg => hc g (hS₂S₄ hg)
  have hmem1 : ∀ x : yamadaS₄ d t,
      x ∈ Subgroup.upperCentralSeries (yamadaS₄ d t) 1 ↔ (x : G) ∈ yamadaU₁ d t := by
    intro x
    rw [Subgroup.upperCentralSeries_one, ← hZ]
    constructor
    · intro hx
      exact ⟨x.2, mem_centralizer_iff.2 fun y hy =>
        congrArg Subtype.val (mem_center_iff.1 hx ⟨y, hy⟩)⟩
    · rintro ⟨-, hc⟩
      exact mem_center_iff.2 fun y => Subtype.ext (mem_centralizer_iff.1 hc y y.2)
  have hmem2 : ∀ x : yamadaS₄ d t,
      x ∈ Subgroup.upperCentralSeries (yamadaS₄ d t) 2 ↔ (x : G) ∈ yamadaY₂ d t := by
    intro x
    rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff, hiff x.2]
    constructor
    · intro hx g hg
      have := (hmem1 _).1 (hx ⟨g, hg⟩)
      simpa [commutatorElement_def] using this
    · intro hx y
      rw [hmem1]
      simpa [commutatorElement_def] using hx y y.2
  refine ⟨hZ, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hmem1 y).1 hy
    · intro hx
      exact ⟨⟨x, (hU₁S₂.trans hS₂S₄) hx⟩, (hmem1 _).2 hx, rfl⟩
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hmem2 y).1 hy
    · intro hx
      exact ⟨⟨x, (hY₂S₂.trans hS₂S₄) hx⟩, (hmem2 _).2 hx, rfl⟩

theorem yamadaS₄_le_centralizer_yamadaU₁ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (h8 : 8 ≤ Nat.card K) :
    yamadaS₄ d t ≤ centralizer (yamadaU₁ d t : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.doublingFacts_of_eight d hK h8
  obtain ⟨-, -, -, -, ⟨hR, htS₄⟩, -⟩ := h.yamada_5_32_2 hW d hK hD
  obtain ⟨hR₄R, -⟩ := h.yamadaR₄_facts hW d hK hD
  obtain ⟨-, -, hRS⟩ := h.yamadaR₄_le_normalizers hW d hK hD
  obtain ⟨-, -, hJX₄, -⟩ := h.yamadaX₄_facts hW d hK hD
  obtain ⟨hZS₂, -⟩ := h.yamada_5_13_5 d hK hD
  have hJ₁J : d.J₁ ≤ d.J := d.image_mono inf_le_left
  have hJC := h.J_le_centralizer_inf_normalizer_S d
  have hS₄R₄ : yamadaS₄ d t ≤ yamadaR₄ d t := le_sup_left.trans hR.le
  have hS₄p : IsPGroup 2 (yamadaS₄ d t) := (h.isPGroup_yamadaRstar d).to_le (hS₄R₄.trans hR₄R)
  have hS₂S₄ : yamadaS₂ d t ≤ yamadaS₄ d t := le_sup_right
  have hU₁S₂ : yamadaU₁ d t ≤ yamadaS₂ d t := (yamadaU₁_le_yamadaY₂ d t).trans le_sup_right
  have hJS₂ : d.J ≤ normalizer (yamadaS₂ d t : Set G) := h.J_le_normalizer_yamadaS₂ d hK hD
  have hJS₄ : d.J ≤ normalizer (yamadaS₄ d t : Set G) := fun j hj =>
    mem_normalizer_sup (hJX₄ hj) (hJS₂ hj)
  have hS₄U₁ : yamadaS₄ d t ≤ normalizer (yamadaU₁ d t : Set G) := fun x hx => by
    rw [← hZS₂]
    exact Common.mem_normalizer_inf (hRS (hS₄R₄ hx)) (mem_normalizer_centralizer (hRS (hS₄R₄ hx)))
  have htR₄ : t ∈ yamadaR₄ d t := hR.le (mem_sup_right (mem_zpowers t))
  have hU₁R₄ : yamadaU₁ d t ≤ yamadaR₄ d t := (hU₁S₂.trans hS₂S₄).trans hS₄R₄
  have hCR₄ := h.eq_yamadaU₁_sup_of_isPGroup d hK h8 ((h.isPGroup_yamadaRstar d).to_le
    (inf_le_left.trans hR₄R)) inf_le_right (le_inf (sup_le hU₁R₄ ((zpowers_le).2 htR₄))
      (sup_le hD.le_centralizer_J₁ ((zpowers_le).2 (mem_centralizer_iff.2 fun j hj =>
        mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hj))))))
  have hCS₄ : yamadaS₄ d t ⊓ centralizer (d.J₁ : Set G) ≤ yamadaU₁ d t := fun x hx => by
    obtain ⟨hxS, hxJ⟩ := Subgroup.mem_inf.1 hx
    have hxT : x ∈ yamadaU₁ d t ⊔ zpowers t := by
      rw [← hCR₄]
      exact Subgroup.mem_inf.2 ⟨hS₄R₄ hxS, hxJ⟩
    have htU₁ : t ∈ normalizer (yamadaU₁ d t : Set G) := (h.t_mem_normalizer_yamadaU₁ d hK hD).1
    rcases (mem_sup_zpowers_iff_of h.t_mul_t htU₁).1 hxT with h1 | ⟨u, hu, rfl⟩
    · exact h1
    · exfalso
      refine htS₄ ?_
      have := mul_mem (inv_mem ((hU₁S₂.trans hS₂S₄) hu)) hxS
      rwa [inv_mul_cancel_left] at this
  have hcomm : ⁅yamadaS₄ d t, d.J₁⁆ ≤ centralizer (yamadaU₁ d t : Set G) :=
    (Subgroup.commutator_le).2 fun s hs j hj => mem_centralizer_iff.2 fun u hu => by
      have hu' : s⁻¹ * u * s ∈ yamadaU₁ d t := by
        have := (mem_normalizer_iff.1 (inv_mem (hS₄U₁ hs)) u).1 hu
        rwa [inv_inv] at this
      have hju : j * u = u * j := mem_centralizer_iff.1 (hD.le_centralizer_J₁ hu) j hj
      have hju' : j * (s⁻¹ * u * s) = (s⁻¹ * u * s) * j :=
        mem_centralizer_iff.1 (hD.le_centralizer_J₁ hu') j hj
      have e1 : j⁻¹ * u = u * j⁻¹ := by
        calc j⁻¹ * u = j⁻¹ * (u * j) * j⁻¹ := by group
          _ = j⁻¹ * (j * u) * j⁻¹ := by rw [hju]
          _ = u * j⁻¹ := by group
      rw [commutatorElement_def]
      calc u * (s * j * s⁻¹ * j⁻¹) = s * ((s⁻¹ * u * s) * j) * s⁻¹ * j⁻¹ := by group
        _ = s * (j * (s⁻¹ * u * s)) * s⁻¹ * j⁻¹ := by rw [hju']
        _ = s * j * s⁻¹ * (u * j⁻¹) := by group
        _ = s * j * s⁻¹ * (j⁻¹ * u) := by rw [e1]
        _ = s * j * s⁻¹ * j⁻¹ * u := by group
  have hJ₁odd : Odd (Nat.card d.J₁) := (odd_card_J d).of_dvd_nat (Subgroup.card_dvd_of_le hJ₁J)
  have hcop : Nat.Coprime (Nat.card d.J₁) (Nat.card (yamadaS₄ d t)) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS₄p
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hJ₁odd)
  have hJ₁S₄ : d.J₁ ≤ normalizer (yamadaS₄ d t : Set G) := fun j hj => hJS₄ (hJ₁J hj)
  have hNS₄ : ⁅yamadaS₄ d t, d.J₁⁆ ≤ yamadaS₄ d t := (Subgroup.commutator_le).2 fun s hs j hj => by
    rw [commutatorElement_def, show s * j * s⁻¹ * j⁻¹ = s * (j * s⁻¹ * j⁻¹) by group]
    exact mul_mem hs ((mem_normalizer_iff.1 (hJ₁S₄ hj) _).1 (inv_mem hs))
  refine (Subgroup.le_centralizer_iff).1 fun u hu => mem_centralizer_iff.2 fun s hs => ?_
  have : Group.IsNilpotent (yamadaS₄ d t) := hS₄p.isNilpotent
  obtain ⟨c, hc, n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime
    (M := yamadaS₄ d t) (N := ⁅yamadaS₄ d t, d.J₁⁆) (S := d.J₁) hNS₄
    (le_normalizer_commutator_left _ _) hJ₁S₄
    (fun j hj => mem_normalizer_commutator (hJ₁S₄ hj) (Subgroup.le_normalizer hj)) inferInstance
    hcop hs fun j hj => by
      rw [show s⁻¹ * (j * s * j⁻¹) = ⁅s⁻¹, j⁆ by simp only [commutatorElement_def]; group]
      exact commutator_mem_commutator (inv_mem hs) hj
  have hcU : c ∈ yamadaU₁ d t := hCS₄ hc
  have e1 : c * u = u * c := hD.mul_comm hcU hu
  have e2 : n * u = u * n := (mem_centralizer_iff.1 (hcomm hn) u hu).symm
  calc c * n * u = c * (n * u) := by group
    _ = c * (u * n) := by rw [e2]
    _ = c * u * n := by group
    _ = u * c * n := by rw [e1]
    _ = u * (c * n) := by group

theorem yamadaS₂_inf_centralizer_J₅_le (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (h8 : 8 ≤ Nat.card K) :
    yamadaS₂ d t ⊓ centralizer (d.J₅ : Set G) ≤ yamadaY₂ d t := fun c hc => by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.doublingFacts_of_eight d hK h8
  obtain ⟨hcS, hcJ⟩ := Subgroup.mem_inf.1 hc
  obtain ⟨hSY₂, -⟩ := h.yamada_5_13_3 d hK hD
  obtain ⟨-, hYX, -, hXF, -, hFD, -, hDS, -⟩ := d.inclusions
  obtain ⟨s, hs, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hSY₂ _ hcS
  have hJ₅J := d.J₅_le_J
  have hJC := h.J_le_centralizer_inf_normalizer_S d
  have hJ₅S : d.J₅ ≤ normalizer (d.S : Set G) := fun j hj =>
    (Subgroup.mem_inf.1 (hJC (hJ₅J hj))).2
  have hJ₅Y : d.J₅ ≤ normalizer (d.Y : Set G) := fun j hj =>
    (h.centralizer_inf_normalizer_S_le d hK hD).2.2 (hJC (hJ₅J hj))
  have hJY₂ := h.J_le_normalizer_yamadaY₂ d hK hD
  have hSY : d.S ⊓ yamadaY₂ d t ≤ d.Y := fun x hx => by
    rw [← h.yamadaY₂_inf_centralizer d hK hD]
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2,
      h.L_le_centralizer (d.image_le _ (Subgroup.mem_inf.1 hx).1)⟩
  have hfix : ∀ j ∈ d.J₅, s⁻¹ * (j * s * j⁻¹) ∈ d.Y := fun j hj => by
    have hjc : j * (s * y) = s * y * j := mem_centralizer_iff.1 hcJ j hj
    refine hSY (Subgroup.mem_inf.2
      ⟨mul_mem (inv_mem hs) ((mem_normalizer_iff.1 (hJ₅S hj) s).1 hs), ?_⟩)
    rw [show s⁻¹ * (j * s * j⁻¹) = y * (j * y * j⁻¹)⁻¹ by
      calc s⁻¹ * (j * s * j⁻¹) = s⁻¹ * (j * (s * y) * j⁻¹) * (j * y * j⁻¹)⁻¹ := by group
        _ = y * (j * y * j⁻¹)⁻¹ := by rw [hjc]; group]
    exact mul_mem hy (inv_mem ((mem_normalizer_iff.1 (hJY₂ (hJ₅J hj)) y).1 hy))
  have hSp : IsPGroup 2 d.S := d.isSylowOf_S.isPGroup
  have : Group.IsNilpotent d.S := hSp.isNilpotent
  obtain ⟨c', hc', n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime
    (M := d.S) (N := d.Y) (S := d.J₅) (hYX.trans (hXF.trans (hFD.trans hDS)))
    d.S_le_normalizers.2.1 hJ₅S hJ₅Y inferInstance
    (Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hJ₅J) (coprime_card_J d hSp)) hs hfix
  have hc'Y : c' ∈ d.Y := by
    rw [d.S_inf_centralizer_J₅ h8] at hc'
    rw [← (d.yamada_defs).1]
    exact mem_sup_left hc'
  exact mul_mem (mul_mem (h.Y_le_yamadaY₂ d hK hD hc'Y) (h.Y_le_yamadaY₂ d hK hD hn)) hy

theorem yamadaS₄_inf_centralizer_J₅_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (h8 : 8 ≤ Nat.card K) :
    yamadaS₄ d t ⊓ centralizer (d.J₅ : Set G) ≤ yamadaY₂ d t := fun c hc => by
  have hD := h.doublingFacts_of_eight d hK h8
  obtain ⟨hcS, hcJ⟩ := Subgroup.mem_inf.1 hc
  obtain ⟨-, -, -, -, ⟨hR, -⟩, -⟩ := h.yamada_5_32_2 hW d hK hD
  have hS₄R₄ : yamadaS₄ d t ≤ yamadaR₄ d t := le_sup_left.trans hR.le
  have hcR₂ : c ∈ yamadaR₂ d t := h.mem_yamadaR₂_of_forall_Ji hW d hK hD (i := 4) (by decide)
    (hS₄R₄ hcS) fun k hk => by
      rw [mem_centralizer_iff.1 hcJ k hk, mul_inv_cancel_right, inv_mul_cancel]
      exact one_mem _
  have hcS₂ : c ∈ yamadaS₂ d t := by
    rw [← h.yamadaS₄_inf_yamadaR₂ hW d hK hD]
    exact Subgroup.mem_inf.2 ⟨hcS, hcR₂⟩
  exact h.yamadaS₂_inf_centralizer_J₅_le d hK h8 (Subgroup.mem_inf.2 ⟨hcS₂, hcJ⟩)

theorem commutator_mem_yamadaU₁_of_mem_yamadaS₄ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (h8 : 8 ≤ Nat.card K)
    {s y : G} (hs : s ∈ yamadaS₄ d t) (hy : y ∈ yamadaY₂ d t) :
    s * y * s⁻¹ * y⁻¹ ∈ yamadaU₁ d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.doublingFacts_of_eight d hK h8
  obtain ⟨-, -, -, -, ⟨hR, -⟩, -⟩ := h.yamada_5_32_2 hW d hK hD
  obtain ⟨hR₄R, -, hR₄R₂, -⟩ := h.yamadaR₄_facts hW d hK hD
  obtain ⟨-, -, hRS⟩ := h.yamadaR₄_le_normalizers hW d hK hD
  obtain ⟨-, -, hJX₄, -⟩ := h.yamadaX₄_facts hW d hK hD
  obtain ⟨hZS₂, -⟩ := h.yamada_5_13_5 d hK hD
  obtain ⟨hRE, hEF, hFY⟩ := h.normalizer_yamadaR₂_le d hK hD
  have hS₄R₄ : yamadaS₄ d t ≤ yamadaR₄ d t := le_sup_left.trans hR.le
  have hS₄p : IsPGroup 2 (yamadaS₄ d t) := (h.isPGroup_yamadaRstar d).to_le (hS₄R₄.trans hR₄R)
  have hSY₂ : yamadaS₄ d t ≤ normalizer (yamadaY₂ d t : Set G) :=
    hS₄R₄.trans (hR₄R₂.trans (hRE.trans (hEF.trans hFY)))
  have hSU₁ : yamadaS₄ d t ≤ normalizer (yamadaU₁ d t : Set G) := fun x hx => by
    rw [← hZS₂]
    exact Common.mem_normalizer_inf (hRS (hS₄R₄ hx)) (mem_normalizer_centralizer (hRS (hS₄R₄ hx)))
  have hK₀ : ∀ g ∈ yamadaS₄ d t, ∀ y ∈ yamadaY₂ d t, g * y * g⁻¹ ∈ yamadaY₂ d t :=
    fun g hg y hy => (mem_normalizer_iff.1 (hSY₂ hg) y).1 hy
  have hB : ∀ g ∈ yamadaS₄ d t, ∀ b ∈ yamadaU₁ d t, g * b * g⁻¹ ∈ yamadaU₁ d t :=
    fun g hg b hb => (mem_normalizer_iff.1 (hSU₁ hg) b).1 hb
  set N := Common.centralizerMod (yamadaS₄ d t) (yamadaY₂ d t) (yamadaU₁ d t) hK₀ hB with hNdef
  have hJS₂ : d.J ≤ normalizer (yamadaS₂ d t : Set G) := h.J_le_normalizer_yamadaS₂ d hK hD
  have hJ₅S : d.J₅ ≤ normalizer (yamadaS₄ d t : Set G) := fun j hj =>
    mem_normalizer_sup (hJX₄ (d.J₅_le_J hj)) (hJS₂ (d.J₅_le_J hj))
  have hJ₅U₁ : d.J₅ ≤ normalizer (yamadaU₁ d t : Set G) := fun j hj =>
    h.J_le_normalizer_yamadaU₁ d hK hD (d.J₅_le_J hj)
  have hJ₅Y₂ : d.J₅ ≤ normalizer (yamadaY₂ d t : Set G) := fun j hj =>
    mem_normalizer_sup (hJ₅U₁ hj)
      (Subgroup.centralizer_le_normalizer _ (h.J₅_le_centralizer_map_wb d hD hj))
  have hsolv : Group.IsSolvable (yamadaS₄ d t) := by
    have := hS₄p.isNilpotent
    infer_instance
  have hcop : (Nat.card d.J₅).Coprime (Nat.card (yamadaS₄ d t)) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le d.J₅_le_J) (coprime_card_J d hS₄p)
  have hyN : ∀ {y : G}, y ∈ yamadaY₂ d t → y ∈ normalizer (yamadaU₁ d t : Set G) :=
    fun hy => h.yamadaY₂_le_normalizer_yamadaU₁ d hK hD hy
  have hfix : ∀ j ∈ d.J₅, s⁻¹ * (j * s * j⁻¹) ∈ N := by
    intro j hj
    have hs' : j * s * j⁻¹ ∈ yamadaS₄ d t := (mem_normalizer_iff.1 (hJ₅S hj) s).1 hs
    refine ⟨mul_mem (inv_mem hs) hs', fun y hy => ?_⟩
    have ha := h.mul_conj_mem_yamadaU₁_of_mem_J₅ d hK hD (inv_mem hj) hy
    rw [inv_inv] at ha
    have hb := h.mul_conj_mem_yamadaU₁_of_mem_J₅ d hK hD hj (hK₀ s hs y hy)
    have ha' : j * (s * (y⁻¹ * (j⁻¹ * y * j)) * s⁻¹) * j⁻¹ ∈ yamadaU₁ d t :=
      (mem_normalizer_iff.1 (hJ₅U₁ hj) _).1 (hB s hs _ ha)
    have key : s⁻¹ * (j * s * j⁻¹) * y * (s⁻¹ * (j * s * j⁻¹))⁻¹ * y⁻¹ =
        y * (s⁻¹ * (((s * y * s⁻¹)⁻¹ * (j * (s * y * s⁻¹) * j⁻¹)) *
          (j * (s * (y⁻¹ * (j⁻¹ * y * j)) * s⁻¹) * j⁻¹)) * s) * y⁻¹ := by group
    rw [key]
    have h1 := (mem_normalizer_iff.1 (inv_mem (hSU₁ hs)) _).1 (mul_mem hb ha')
    rw [inv_inv] at h1
    exact (mem_normalizer_iff.1 (hyN hy) _).1 h1
  obtain ⟨c, hc, n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime (N := N)
    (fun x hx => hx.1) (fun x hx => mem_normalizer_of_conj_mem fun z hz =>
      Common.conj_mem_centralizerMod hx hz) hJ₅S (fun j hj => mem_normalizer_of_conj_mem
      fun z hz => ⟨(mem_normalizer_iff.1 (hJ₅S hj) z).1 hz.1, fun y hy => by
        have hy' : j⁻¹ * y * j ∈ yamadaY₂ d t := by
          have := (mem_normalizer_iff.1 (inv_mem (hJ₅Y₂ hj)) y).1 hy
          rwa [inv_inv] at this
        have h1 := (mem_normalizer_iff.1 (hJ₅U₁ hj) _).1 (hz.2 _ hy')
        rwa [show j * (z * (j⁻¹ * y * j) * z⁻¹ * (j⁻¹ * y * j)⁻¹) * j⁻¹ =
          j * z * j⁻¹ * y * (j * z * j⁻¹)⁻¹ * y⁻¹ by group] at h1⟩)
    hsolv hcop hs hfix
  have hcY₂ : c ∈ yamadaY₂ d t := h.yamadaS₄_inf_centralizer_J₅_le hW d hK h8 hc
  have hcy : c * y * c⁻¹ * y⁻¹ ∈ yamadaU₁ d t := by
    rw [h.yamadaY₂_mul_comm d hK hD hcY₂ hy, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  rw [show c * n * y * (c * n)⁻¹ * y⁻¹ = c * (n * y * n⁻¹ * y⁻¹) * c⁻¹ * (c * y * c⁻¹ * y⁻¹) by
    group]
  exact mul_mem (hB c hc.1 _ (hn.2 y hy)) hcy

theorem yamada_5_33_1_S₄ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (h8 : 8 ≤ Nat.card K) :
    yamadaS₄ d t ⊓ centralizer (yamadaS₄ d t : Set G) = yamadaU₁ d t ∧
      (Subgroup.upperCentralSeries (yamadaS₄ d t) 1).map (yamadaS₄ d t).subtype =
        yamadaU₁ d t ∧
      (Subgroup.upperCentralSeries (yamadaS₄ d t) 2).map (yamadaS₄ d t).subtype =
        yamadaY₂ d t :=
  h.yamadaS₄_center hW d hK (h.doublingFacts_of_eight d hK h8)
    ((le_sup_left : yamadaX₄ d t ≤ yamadaS₄ d t).trans
      (h.yamadaS₄_le_centralizer_yamadaU₁ hW d hK h8))
    fun _ hw _ hy => h.commutator_mem_yamadaU₁_of_mem_yamadaS₄ hW d hK h8
      ((le_sup_left : yamadaX₄ d t ≤ yamadaS₄ d t) hw) hy

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
