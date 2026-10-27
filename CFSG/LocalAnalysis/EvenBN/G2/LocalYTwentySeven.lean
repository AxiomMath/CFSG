module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYTwentySix

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section Generic

variable {G : Type*} [Group G]

theorem exists_ne_one_mem_centralizer_of_le [Finite G] {p : ℕ} [Fact p.Prime] {P E : Subgroup G}
    (hP : IsPGroup p P) (hEP : E ≤ P) (hPE : P ≤ normalizer (E : Set G)) (hE : E ≠ ⊥) :
    ∃ x ∈ E, x ≠ 1 ∧ x ∈ centralizer (P : Set G) := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have : (E.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff hEP).2
    fun a b ha hb => (mem_normalizer_iff.1 (hPE hb) a).1 ha
  have hne : E.subgroupOf P ≠ ⊥ := by
    intro h0
    refine hE (eq_bot_iff.2 fun x hx => ?_)
    have : (⟨x, hEP hx⟩ : P) ∈ E.subgroupOf P := hx
    rw [h0, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)
  obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨((y : P) : G), (Subgroup.mem_inf.1 y.2).1, fun e => hy1 (Subtype.ext (Subtype.ext e)),
    ?_⟩
  rw [mem_centralizer_iff]
  intro z hz
  have := (Subgroup.mem_center_iff.1 (Subgroup.mem_inf.1 y.2).2) ⟨z, hz⟩
  exact congrArg Subtype.val this

theorem mem_normalizer_centralizer [Finite G] {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) :
    g ∈ normalizer ((centralizer (H : Set G) : Subgroup G) : Set G) :=
  mem_normalizer_of_conj_mem fun x hx => mem_centralizer_iff.2 fun y hy => by
    have hy' : g⁻¹ * y * g ∈ H := by
      have := (mem_normalizer_iff.1 (inv_mem hg) y).1 hy
      rwa [inv_inv] at this
    have e := mem_centralizer_iff.1 hx _ hy'
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [e]
      _ = g * x * g⁻¹ * y := by group

theorem isElementaryAbelian_two_of_forall {A : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hsq : ∀ x ∈ A, x * x = 1) :
    CFSG.IsElementaryAbelian 2 A := CFSG.IsElementaryAbelian.two_of_forall_mul_self hcomm hsq

end Generic

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem yamadaL₂_inf_yamadaS₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaL₂ d t ⊓ yamadaS₂ d t = yamadaM₂ d t := by
  obtain ⟨-, -, -, htS₂, -⟩ := h.yamada_5_13_3 d hK hD
  have hL₂eq := h.yamadaL₂_eq_sup d hK hD
  have hM₂S₂ : yamadaM₂ d t ≤ yamadaS₂ d t :=
    sup_le_sup_right d.inclusions.2.2.2.2.2.2.2.2.1 _
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  refine le_antisymm (fun x hx => ?_) (le_inf (le_sup_left.trans hL₂eq.ge) hM₂S₂)
  obtain ⟨hxL, hxS⟩ := Subgroup.mem_inf.1 hx
  rw [hL₂eq] at hxL
  rcases (mem_sup_zpowers_iff_of h.t_mul_t
      (h.yamadaL₂_le_normalizer_yamadaM₂ d hK hD htL₂)).1 hxL with h1 | ⟨m, hm, rfl⟩
  · exact h1
  · exfalso
    refine htS₂ ?_
    have := mul_mem (inv_mem (hM₂S₂ hm)) hxS
    rwa [inv_mul_cancel_left] at this

theorem yamadaM₁_le_yamadaM₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaM₁ d t ≤ yamadaM₂ d t := by
  rw [← h.yamadaL₂_inf_yamadaS₂ d hK hD]
  refine inf_le_inf inf_le_left ?_
  rw [h.yamadaS₁_eq_sup d hK hD]
  exact sup_le_sup_left (yamadaU₁_le_yamadaY₂ d t) _

theorem wb_mem_normalizer_rootGroup_v (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) : d.wb ∈ normalizer (d.rootGroup g2v : Set G) := by
  obtain ⟨-, -, -, hwb, -, hconj⟩ := d.yamada_3_7_G (hK ▸ h.four_le)
  have hrefl : reflect .G2 g2ia g2v = g2v := List.ofFn_injective (by decide +kernel)
  have hinv : d.wb⁻¹ = d.wb := inv_eq_of_mul_eq_one_right hwb
  refine mem_normalizer_of_conj_mem fun y hy => ?_
  obtain ⟨g, hg, rfl⟩ := d.mem_image.1 hy
  obtain ⟨x, hx⟩ := mem_rootSubgroup.1 hg
  have hg' : g = ⟨pinnedX .G2 K g2v x, pinnedX_mem_adjointGroup g2v x⟩ := Subtype.ext hx.symm
  rw [hinv, hg', hconj isRoot_g2v x]
  refine d.emb_mem_image ?_
  rw [hrefl]
  exact mem_rootSubgroup.2 ⟨x, rfl⟩

theorem wb_mem_normalizer_J₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    d.wb ∈ normalizer (d.J₂ : Set G) := by
  have hJ₂ : d.J₂ = d.J ⊓ centralizer (d.rootGroup g2v : Set G) :=
    d.image_inf_centralizer (Model.J K) (rootSubgroup_le_adjointGroup (K := K) (τ := .G2) g2v)
  have hv := h.wb_mem_normalizer_rootGroup_v d hK
  rw [hJ₂]
  refine Common.mem_normalizer_inf (h.wb_mem_normalizer_J d hK)
    (mem_normalizer_of_conj_mem fun x hx => mem_centralizer_iff.2 fun y hy => ?_)
  have hy' : d.wb⁻¹ * y * d.wb ∈ d.rootGroup g2v := by
    have := (mem_normalizer_iff.1 (inv_mem hv) y).1 hy
    rwa [inv_inv] at this
  have e := mem_centralizer_iff.1 hx _ hy'
  calc y * (d.wb * x * d.wb⁻¹) = d.wb * ((d.wb⁻¹ * y * d.wb) * x) * d.wb⁻¹ := by group
    _ = d.wb * (x * (d.wb⁻¹ * y * d.wb)) * d.wb⁻¹ := by rw [e]
    _ = d.wb * x * d.wb⁻¹ * y := by group

theorem eq_one_of_mem_yamadaY₂_of_forall_J₂ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {x : G} (hx : x ∈ yamadaY₂ d t)
    (hfix : ∀ k ∈ d.J₂, k * x = x * k) : x = 1 := by
  obtain ⟨hJ₂J, -⟩ := h.J₂_facts d hK
  obtain ⟨⟨hU₁U₁', hU₁'C⟩, -⟩ := h.yamada_5_13_1 d hK hD
  have hwbJ := h.wb_mem_normalizer_J₂ d hK
  have hkU₁ : ∀ k ∈ d.J₂, k ∈ normalizer (yamadaU₁ d t : Set G) := fun k hk =>
    (h.centralizer_inf_normalizer_S_le d hK hD).2.1
      (h.J_le_centralizer_inf_normalizer_S d (hJ₂J hk))
  have hk' : ∀ k ∈ d.J₂, d.wb⁻¹ * k * d.wb ∈ d.J₂ := fun k hk => by
    have := (mem_normalizer_iff.1 (inv_mem hwbJ) k).1 hk
    rwa [inv_inv] at this
  have hconj : ∀ k u : G, k * (d.wb * u * d.wb⁻¹) * k⁻¹ =
      d.wb * ((d.wb⁻¹ * k * d.wb) * u * (d.wb⁻¹ * k * d.wb)⁻¹) * d.wb⁻¹ := fun k u => by group
  obtain ⟨u, hu, u', hu', rfl⟩ := Common.exists_mul_of_le_normalizer
    (hU₁'C.trans (Subgroup.centralizer_le_normalizer _)) x hx
  obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.1 hu'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hfix ⊢
  have hsplit : ∀ k ∈ d.J₂, k * u * k⁻¹ = u ∧
      (d.wb⁻¹ * k * d.wb) * u₀ * (d.wb⁻¹ * k * d.wb)⁻¹ = u₀ := fun k hk => by
    have e := hfix k hk
    have hku : k * u * k⁻¹ ∈ yamadaU₁ d t := (mem_normalizer_iff.1 (hkU₁ k hk) u).1 hu
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
  have hfix₁ : ∀ v ∈ yamadaU₁ d t, (∀ k ∈ d.J₂, k * v * k⁻¹ = v) → v = 1 := fun v hv hv' =>
    h.eq_one_of_mem_yamadaU₁_of_forall_J₂ d hK hD hv fun k hk => by
      calc k * v = k * v * k⁻¹ * k := by group
        _ = v * k := by rw [hv' k hk]
  have hu1 : u = 1 := hfix₁ u hu fun k hk => (hsplit k hk).1
  have hu₀1 : u₀ = 1 := hfix₁ u₀ hu₀ fun k hk => by
    have hk₂ : d.wb * k * d.wb⁻¹ ∈ d.J₂ := (mem_normalizer_iff.1 hwbJ k).1 hk
    have := (hsplit _ hk₂).2
    rwa [show d.wb⁻¹ * (d.wb * k * d.wb⁻¹) * d.wb = k by group] at this
  rw [hu1, hu₀1]
  group

theorem inv_mul_conj_mem_yamadaL₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {x j : G}
    (hx : x ∈ yamadaL₃ d t) (hj : j ∈ d.J₂) : x⁻¹ * (j * x * j⁻¹) ∈ yamadaL₂ d t := by
  obtain ⟨-, hJC, -⟩ := h.J₂_facts d hK
  obtain ⟨-, hJL₃, -, -⟩ := h.centralizer_inf_normalizer_S_le_normalizers hW d hK hD
  obtain ⟨_, _, φ, hφ, -⟩ := h.yamada_5_23_3 hW d hK hD
  obtain ⟨w, hw, hxw⟩ := (h.yamada_5_23_2 hW d hK hD).1 x hx
  have hjC := hJC hj
  have hjt : j * t = t * j := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hjC).1
  have hjx : j * x * j⁻¹ ∈ yamadaL₃ d t := (mem_normalizer_iff.1 (hJL₃ hjC) _).1 hx
  obtain ⟨hjw, hwY⟩ := h.J₂_conj_W d hK hD hj hw
  have h1 := hφ ⟨x, hx⟩ ⟨w, hw⟩ hxw
  have h2 := hφ ⟨j * x * j⁻¹, hjx⟩ ⟨j * w * j⁻¹, hjw⟩ (conj_conj_t hjt hxw)
  have h3 : (QuotientGroup.mk ⟨w, hw⟩ : d.W ⧸ d.Y.subgroupOf d.W) =
      QuotientGroup.mk ⟨j * w * j⁻¹, hjw⟩ := by
    rw [QuotientGroup.eq, mem_subgroupOf]
    exact hwY
  have h4 := φ.injective (h1.trans (h3.trans h2.symm))
  rw [QuotientGroup.eq, mem_subgroupOf] at h4
  exact h4

theorem yamadaW₃_core (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d)
    (hYW : yamadaW₃ d t ≤ centralizer (yamadaY₂ d t : Set G)) :
    CFSG.IsElementaryAbelian 2 (yamadaW₃ d t) ∧ Nat.card (yamadaW₃ d t) = Nat.card K ^ 6 ∧
      yamadaL₃ d t ⊓ centralizer (yamadaW₂ d t : Set G) = yamadaW₃ d t ∧
      centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G) ≤
        normalizer (yamadaW₃ d t : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hW₃V₃, hV₃N, hJW₃, hW₂W₃, htW₃, hV₃eq, hW₃c⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨hV₂V₃, hV₃E₃, hV₃L₂, -, -, -, -, hV₃W₂, hV₃Y₂⟩ := h.yamadaV₃_facts hW d hK hD
  obtain ⟨hJ₂J, hJC, hC, -⟩ := h.J₂_facts d hK
  obtain ⟨hR₃R, -⟩ := h.yamadaR₃_facts hW d hK hD
  obtain ⟨-, -, hYW', -, hWF, hFD, hFM, hDS, -⟩ := d.inclusions
  obtain ⟨-, -, hWdef, -⟩ := d.yamada_defs
  obtain ⟨htW, -⟩ := h.t_mem_normalizer_yamadaW₂ d hK hD
  have h4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  have hW₃L₃ : yamadaW₃ d t ≤ yamadaL₃ d t := (hW₃V₃.trans hV₃E₃).trans inf_le_left
  have hW₃p : IsPGroup 2 (yamadaW₃ d t) := (h.isPGroup_yamadaRstar d).to_le
    ((hW₃L₃.trans (le_sup_left : yamadaL₃ d t ≤ yamadaR₃ d t)).trans hR₃R)
  have hW₂V₃ : yamadaW₂ d t ≤ yamadaV₃ d t := le_sup_left.trans hV₂V₃
  have hY₂W₂ : yamadaY₂ d t ≤ yamadaW₂ d t := le_sup_right
  have hNtY : ∀ g ∈ centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G),
      g ∈ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) := fun g hg =>
    (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK hD).2 (mem_sup_right hg)
  have hJ₂W₃ : d.J₂ ≤ normalizer (yamadaW₃ d t : Set G) := fun j hj => hJW₃ (hJ₂J hj)
  have hJ₂Y₂ : d.J₂ ≤ normalizer (yamadaY₂ d t : Set G) := fun j hj =>
    (h.normalizer_tY_le d hK hD).2.1 (hNtY j (hJC hj))
  have hJ₂W₂ : d.J₂ ≤ normalizer (yamadaW₂ d t : Set G) := fun j hj =>
    (h.normalizer_yamadaV₂_le hW d hK hD).1 ((h.normalizer_tY_le d hK hD).2.2 (hNtY j (hJC hj)))
  have hAS : d.rootGroup g2v ≤ d.S := hC.ge.trans inf_le_left
  have hAW : d.rootGroup g2v ≤ d.W := le_sup_left.trans hWdef.le
  have hWY₂ : d.W ≤ normalizer (yamadaY₂ d t : Set G) :=
    (hWF.trans (hFD.trans hDS)).trans (h.yamada_5_13_3 d hK hD).1
  have hWCY₂ := h.W_le_centralizer_yamadaY₂ d hK hD
  have hY₂Z : yamadaY₂ d t ≤ centralizer (yamadaW₃ d t : Set G) :=
    (Subgroup.le_centralizer_iff).1 hYW
  have hA1 : ∀ w ∈ yamadaW₂ d t, ∀ j ∈ d.J₂, w⁻¹ * (j * w * j⁻¹) ∈ yamadaY₂ d t :=
    fun w hw j hj => by
      obtain ⟨a, ha, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hWY₂ w hw
      obtain ⟨-, haY⟩ := h.J₂_conj_W d hK hD hj ha
      rw [show (a * y)⁻¹ * (j * (a * y) * j⁻¹) = y⁻¹ * (a⁻¹ * (j * a * j⁻¹)) * (j * y * j⁻¹) by
        group]
      exact mul_mem (mul_mem (inv_mem hy) (h.Y_le_yamadaY₂ d hK hD haY))
        ((mem_normalizer_iff.1 (hJ₂Y₂ hj) y).1 hy)
  have hV₂W₃ : yamadaV₂ d t ⊓ yamadaW₃ d t ≤ yamadaW₂ d t := fun x hx => by
    obtain ⟨hxV, hxW⟩ := Subgroup.mem_inf.1 hx
    rcases (mem_sup_zpowers_iff_of h.t_mul_t htW).1 hxV with h1 | ⟨a, ha, rfl⟩
    · exact h1
    · exfalso
      refine htW₃ ?_
      have := mul_mem (inv_mem (hW₂W₃ ha)) hxW
      rwa [inv_mul_cancel_left] at this
  have hA2 : ∀ w ∈ yamadaW₃ d t, ∀ j ∈ d.J₂, w⁻¹ * (j * w * j⁻¹) ∈ yamadaW₂ d t :=
    fun w hw j hj => by
      have h1 := h.inv_mul_conj_mem_yamadaL₂ hW d hK hD (hW₃L₃ hw) hj
      have h2 : w⁻¹ * (j * w * j⁻¹) ∈ yamadaW₃ d t :=
        mul_mem (inv_mem hw) ((mem_normalizer_iff.1 (hJ₂W₃ hj) w).1 hw)
      exact hV₂W₃ (Subgroup.mem_inf.2 ⟨hV₃L₂.le (Subgroup.mem_inf.2 ⟨hW₃V₃ h2, h1⟩), h2⟩)
  have hA : ∀ w ∈ yamadaW₃ d t, ∀ j ∈ d.J₂, w⁻¹ * (j * w * j⁻¹) ∈ yamadaY₂ d t :=
    fun w hw j hj => by
      obtain ⟨c, hc, n, hn, rfl⟩ := exists_centralizer_J₂_mul d hK hW₂W₃ (hW₃V₃.trans hV₃W₂)
        hJ₂W₃ hJ₂W₂ hW₃p hw fun j hj => hA2 w hw j hj
      have hcj : j * c = c * j := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 j hj
      rw [show (c * n)⁻¹ * (j * (c * n) * j⁻¹) = n⁻¹ * (c⁻¹ * (j * c) * n * j⁻¹) by group, hcj,
        show n⁻¹ * (c⁻¹ * (c * j) * n * j⁻¹) = n⁻¹ * (j * n * j⁻¹) by group]
      exact hA1 n hn j hj
  have hdec : ∀ w ∈ yamadaW₃ d t, ∃ c ∈ yamadaW₃ d t ⊓ centralizer (d.J₂ : Set G),
      ∃ y ∈ yamadaY₂ d t, w = c * y := fun w hw =>
    exists_centralizer_J₂_mul d hK (hY₂W₂.trans hW₂W₃) (hW₃V₃.trans hV₃Y₂) hJ₂W₃ hJ₂Y₂ hW₃p hw
      (hA w hw)
  have hCW₂ : (yamadaW₃ d t ⊓ centralizer (d.J₂ : Set G)) ⊓ yamadaW₂ d t = d.rootGroup g2v := by
    refine le_antisymm (fun x hx => ?_) (le_inf (le_inf ((hAW.trans le_sup_left).trans hW₂W₃)
      (hC.ge.trans inf_le_right)) (hAW.trans le_sup_left))
    obtain ⟨hxC, hxW₂⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨a, ha, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hWY₂ x hxW₂
    rw [← hWdef] at ha
    obtain ⟨s, hs, y', hy', rfl⟩ :=
      Common.exists_mul_of_le_normalizer' (hAS.trans d.S_le_normalizers.2.1) a ha
    have hsJ : s ∈ centralizer (d.J₂ : Set G) := (Subgroup.mem_inf.1 (hC.ge hs)).2
    have hyy : y' * y ∈ yamadaY₂ d t := mul_mem (h.Y_le_yamadaY₂ d hK hD hy') hy
    have hyJ : y' * y = 1 := h.eq_one_of_mem_yamadaY₂_of_forall_J₂ d hK hD hyy fun k hk => by
      have e1 := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hxC).2 k hk
      have e2 : k * s = s * k := mem_centralizer_iff.1 hsJ k hk
      calc k * (y' * y) = s⁻¹ * (s * k * (y' * y)) := by group
        _ = s⁻¹ * (k * s * (y' * y)) := by rw [← e2]
        _ = s⁻¹ * (k * (s * y' * y)) := by group
        _ = s⁻¹ * (s * y' * y * k) := by rw [e1]
        _ = y' * y * k := by group
    rw [mul_assoc, hyJ, mul_one]
    exact hs
  set C := yamadaW₃ d t ⊓ centralizer (d.J₂ : Set G) with hCdef
  have hCp : IsPGroup 2 C := hW₃p.to_le inf_le_left
  have hSvC : d.rootGroup g2v ≤ C := hCW₂.ge.trans inf_le_left
  have hCN : C ≤ normalizer (d.rootGroup g2v : Set G) := fun c hc => by
    rw [← hCW₂]
    exact Common.mem_normalizer_inf (Subgroup.le_normalizer hc)
      ((hW₃V₃.trans hV₃W₂) (Subgroup.mem_inf.1 hc).1)
  have hAc : Nat.card (d.rootGroup g2v) = Nat.card K :=
    (d.card_image (rootSubgroup_le_adjointGroup (K := K) (τ := .G2) g2v)).trans
      (card_rootSubgroup (τ := .G2) (K := K) g2v)
  have hSv1 : d.rootGroup g2v ≠ ⊥ := fun h0 => by
    rw [h0, Subgroup.card_bot] at hAc
    omega
  obtain ⟨-, htr⟩ := (d.yamada_3_9_2_G (i := 3) (k := 1) (by decide)).2 (Or.inr (by decide))
  have hJ₄J : d.J₄ ≤ d.J := d.image_mono inf_le_left
  have hJ₄C : ∀ k ∈ d.J₄, k ∈ normalizer ((centralizer (C : Set G) : Subgroup G) : Set G) :=
    fun k hk => by
      have hkC : k ∈ normalizer (C : Set G) := Common.mem_normalizer_inf (hJW₃ (hJ₄J hk))
        (Subgroup.le_normalizer (mem_centralizer_iff.2 fun y hy => J_mul_comm d (hJ₂J hy)
          (hJ₄J hk)))
      exact mem_normalizer_centralizer hkC
  obtain ⟨x₀, hx₀, hx₀1, hx₀C⟩ := exists_ne_one_mem_centralizer_of_le hCp hSvC hCN hSv1
  have hSvZ : d.rootGroup g2v ≤ centralizer (C : Set G) := fun s hs => by
    by_cases hs1 : s = 1
    · rw [hs1]
      exact one_mem _
    obtain ⟨k, hk, rfl⟩ := htr x₀ hx₀ hx₀1 s hs hs1
    exact (mem_normalizer_iff.1 (hJ₄C k hk) x₀).1 hx₀C
  have hsW₃ : d.rootGroup g2v ≤ centralizer (yamadaW₃ d t : Set G) := fun s hs =>
    mem_centralizer_iff.2 fun w hw => by
      obtain ⟨c, hc, y, hy, rfl⟩ := hdec w hw
      have e1 : c * s = s * c := mem_centralizer_iff.1 (hSvZ hs) c hc
      have e2 : y * s = s * y := mem_centralizer_iff.1 (hWCY₂ (hAW hs)) y hy
      calc c * y * s = c * (y * s) := by group
        _ = c * (s * y) := by rw [e2]
        _ = c * s * y := by group
        _ = s * c * y := by rw [e1]
        _ = s * (c * y) := by group
  have hW₂Z : yamadaW₂ d t ≤ centralizer (yamadaW₃ d t : Set G) := fun x hx => by
    obtain ⟨a, ha, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hWY₂ x hx
    rw [← hWdef] at ha
    obtain ⟨s, hs, y', hy', rfl⟩ :=
      Common.exists_mul_of_le_normalizer' (hAS.trans d.S_le_normalizers.2.1) a ha
    exact mul_mem (mul_mem (hsW₃ hs) (hY₂Z (h.Y_le_yamadaY₂ d hK hD hy'))) (hY₂Z hy)
  obtain ⟨⟨-, hsetM, -⟩, -, -, ⟨hL, htM₃⟩, -⟩ := h.yamada_5_30_2 hW d hK hD
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  have htM₃N : t ∈ normalizer (yamadaM₃ d t : Set G) :=
    mem_normalizer_sup (hV₃N (hV₂V₃ (mem_sup_right (mem_zpowers t))))
      (h.yamadaL₂_le_normalizer_yamadaM₂ d hK hD htL₂)
  have hMY₂ : d.M ≤ normalizer (yamadaY₂ d t : Set G) :=
    d.inclusions.2.2.2.2.2.2.2.2.1.trans (h.yamada_5_13_3 d hK hD).1
  have hW₂ab : yamadaW₂ d t ≤ centralizer (yamadaW₂ d t : Set G) := fun x hx =>
    Subgroup.centralizer_le hW₂W₃ (hW₂Z hx)
  have hLW := (d.yamada_3_17_2_G).2
  have hCL₃ : yamadaL₃ d t ⊓ centralizer (yamadaW₂ d t : Set G) = yamadaW₃ d t := by
    refine le_antisymm (fun x hx => ?_) (le_inf hW₃L₃ ((Subgroup.le_centralizer_iff).1 hW₂Z))
    obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.1 hx
    have hWC : ∀ z ∈ centralizer (yamadaW₂ d t : Set G), z ∈ centralizer (d.W : Set G) :=
      fun z hz => Subgroup.centralizer_le (le_sup_left : d.W ≤ yamadaW₂ d t) hz
    have hdecM : ∀ m₃ ∈ yamadaM₃ d t, ∃ w ∈ yamadaW₃ d t, ∃ m ∈ d.M, ∃ y ∈ yamadaY₂ d t,
        m₃ = w * (m * y) := fun m₃ hm₃ => by
      have hm₃' : m₃ ∈ ((yamadaM₃ d t : Subgroup G) : Set G) := hm₃
      rw [hsetM] at hm₃'
      obtain ⟨w, hw, m₂, hm₂, rfl⟩ := Set.mem_mul.1 hm₃'
      obtain ⟨m, hm, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hMY₂ m₂ hm₂
      exact ⟨w, hw, m, hm, y, hy, rfl⟩
    rw [← hL] at hxL
    rcases (mem_sup_zpowers_iff_of h.t_mul_t htM₃N).1 hxL with hxM | ⟨m₃, hm₃, rfl⟩
    · obtain ⟨w, hw, m, hm, y, hy, rfl⟩ := hdecM x hxM
      have hmC : m ∈ centralizer (d.W : Set G) := by
        have := mul_mem (mul_mem (inv_mem ((Subgroup.le_centralizer_iff).1 hW₂Z hw)) hxC)
          (inv_mem (hW₂ab (hY₂W₂ hy)))
        rw [show w⁻¹ * (w * (m * y)) * y⁻¹ = m by group] at this
        exact hWC m this
      have hmW : m ∈ d.W := by
        rw [← hLW]
        exact Subgroup.mem_inf.2 ⟨(d.inclusions.2.2.2.2.2.2.2.2.1.trans (d.image_le _)) hm, hmC⟩
      exact mul_mem hw (mul_mem (((le_sup_left : d.W ≤ yamadaW₂ d t).trans hW₂W₃) hmW)
        ((hY₂W₂.trans hW₂W₃) hy))
    · exfalso
      obtain ⟨w, hw, m, hm, y, hy, rfl⟩ := hdecM m₃ hm₃
      have htC : t ∈ centralizer (d.W : Set G) := mem_centralizer_iff.2 fun z hz =>
        mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hz))
      have hwC : w ∈ centralizer (d.W : Set G) :=
        hWC w ((Subgroup.le_centralizer_iff).1 hW₂Z hw)
      have hyC : y ∈ centralizer (d.W : Set G) := hWC y (hW₂ab (hY₂W₂ hy))
      have hmC : m ∈ centralizer (d.W : Set G) := by
        have := mul_mem (mul_mem (mul_mem (inv_mem hwC) (hWC _ hxC)) (inv_mem htC)) (inv_mem hyC)
        rwa [show w⁻¹ * (w * (m * y) * t) * t⁻¹ * y⁻¹ = m by group] at this
      have hmW : m ∈ d.W := by
        rw [← hLW]
        exact Subgroup.mem_inf.2 ⟨(d.inclusions.2.2.2.2.2.2.2.2.1.trans (d.image_le _)) hm, hmC⟩
      have htW₂ : t ∈ centralizer (yamadaW₂ d t : Set G) := by
        have := mul_mem (mul_mem (mul_mem (inv_mem (hW₂ab (hY₂W₂ hy)))
          (inv_mem (hW₂ab ((le_sup_left : d.W ≤ yamadaW₂ d t) hmW))))
          (inv_mem ((Subgroup.le_centralizer_iff).1 hW₂Z hw))) hxC
        rwa [show y⁻¹ * m⁻¹ * w⁻¹ * (w * (m * y) * t) = t by group] at this
      have hle : yamadaW₂ d t ≤ d.W := by
        rw [← h.yamadaW₂_inf_centralizer d hK hD]
        exact le_inf le_rfl fun z hz => mem_centralizer_singleton_iff.2
          (mem_centralizer_iff.1 htW₂ z hz)
      have hc := Subgroup.card_le_of_le hle
      rw [h.card_yamadaW₂ d hK hD, d.cards.2.2.2.1] at hc
      exact absurd hc (not_le.2 (pow_lt_pow_right₀ (by omega : 1 < Nat.card K)
        (by norm_num : 3 < 5)))
  have hNW₃ : centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G) ≤
      normalizer (yamadaW₃ d t : Set G) := fun g hg => by
    have hgV : g ∈ normalizer (yamadaV₂ d t : Set G) :=
      (h.normalizer_tY_le d hK hD).2.2 (h.centralizer_inf_normalizer_Y_le d hg)
    rw [← hCL₃]
    exact Common.mem_normalizer_inf (LieType.BorelTits.le_normalizer_pCoreOf 2 _ hgV)
      (mem_normalizer_centralizer ((h.normalizer_yamadaV₂_le hW d hK hD).1 hgV))
  have hsqS : ∀ w ∈ yamadaW₃ d t, w * w ∈ d.rootGroup g2v := fun w hw => by
    obtain ⟨c, hc, y, hy, rfl⟩ := hdec w hw
    have hcy : c * y = y * c := mem_centralizer_iff.1 (hY₂Z hy) c (Subgroup.mem_inf.1 hc).1
    rw [show c * y * (c * y) = c * (y * c) * y by group, ← hcy,
      show c * (c * y) * y = c * c * (y * y) by group, h.yamadaY₂_mul_self hW d hK hD hy,
      mul_one, ← hCW₂]
    exact Subgroup.mem_inf.2 ⟨mul_mem hc hc,
      h.mul_self_mem_yamadaW₂ hW d hK hD (hW₃V₃ (Subgroup.mem_inf.1 hc).1)⟩
  have hsq : ∀ w ∈ yamadaW₃ d t, w * w = 1 := by
    intro w₀ hw₀
    by_contra hw₀1
    have hSN : d.S ≤ normalizer (d.rootGroup g2v : Set G) := fun σ hσ => by
      have hσW₃ : σ ∈ normalizer (yamadaW₃ d t : Set G) := hNW₃ (Subgroup.mem_inf.2
        ⟨h.L_le_centralizer (d.image_le _ hσ), d.S_le_normalizers.2.1 hσ⟩)
      refine mem_normalizer_of_conj_mem fun s hs => ?_
      by_cases hs1 : s = 1
      · rw [hs1, mul_one, mul_inv_cancel]
        exact one_mem _
      obtain ⟨k, hk, rfl⟩ := htr _ (hsqS w₀ hw₀) hw₀1 s hs hs1
      have hkw : k * w₀ * k⁻¹ ∈ yamadaW₃ d t := (mem_normalizer_iff.1 (hJW₃ (hJ₄J hk)) w₀).1 hw₀
      rw [show σ * (k * (w₀ * w₀) * k⁻¹) * σ⁻¹ =
        (σ * (k * w₀ * k⁻¹) * σ⁻¹) * (σ * (k * w₀ * k⁻¹) * σ⁻¹) by group]
      exact hsqS _ ((mem_normalizer_iff.1 hσW₃ _).1 hkw)
    obtain ⟨x, hx, hx1, hxC⟩ := exists_ne_one_mem_centralizer_of_le d.isSylowOf_S.isPGroup hAS
      hSN hSv1
    have hxU : x ∈ d.U := by
      rw [← (d.yamada_3_12_centers).1]
      exact Subgroup.mem_inf.2 ⟨hAS hx, hxC⟩
    have hxY : x ∈ d.Y ⊓ d.rootGroup g2v := Subgroup.mem_inf.2 ⟨d.inclusions.1 hxU, hx⟩
    rw [Y_inf_rootGroup_v d, Subgroup.mem_bot] at hxY
    exact hx1 hxY
  have hcomm : ∀ x ∈ yamadaW₃ d t, ∀ y ∈ yamadaW₃ d t, x * y = y * x := fun x hx y hy => by
    have h1 := hsq _ (mul_mem hx hy)
    have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x hx)
    have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hsq y hy)
    calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hx', hy']
  exact ⟨isElementaryAbelian_two_of_forall hcomm hsq, hW₃c, hCL₃, hNW₃⟩

theorem yamadaS₃_inf_yamadaR₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaS₃ d t ⊓ yamadaR₂ d t = yamadaS₂ d t := by
  obtain ⟨⟨-, -, hsetS⟩, -⟩ := h.yamada_5_30_2 hW d hK hD
  obtain ⟨hW₃V₃, -, -, hW₂W₃, htW₃, -⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨-, -, -, hV₃R₂, -⟩ := h.yamadaV₃_facts hW d hK hD
  obtain ⟨-, hS₂R₂, -⟩ := h.yamada_5_13_3 d hK hD
  have hW₂S₂ : yamadaW₂ d t ≤ yamadaS₂ d t := sup_le_sup_right
    (d.inclusions.2.2.2.2.1.trans (d.inclusions.2.2.2.2.2.1.trans
      d.inclusions.2.2.2.2.2.2.2.1)) _
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right hS₂R₂)
  obtain ⟨hxS₃, hxR₂⟩ := Subgroup.mem_inf.1 hx
  have hxS₃' : x ∈ ((yamadaS₃ d t : Subgroup G) : Set G) := hxS₃
  rw [hsetS] at hxS₃'
  obtain ⟨w, hw, s, hs, rfl⟩ := Set.mem_mul.1 hxS₃'
  have hwR₂ : w ∈ yamadaR₂ d t := by
    have := mul_mem hxR₂ (inv_mem (hS₂R₂ hs))
    rwa [mul_inv_cancel_right] at this
  have hwV₂ : w ∈ yamadaV₂ d t := hV₃R₂.le (Subgroup.mem_inf.2 ⟨hW₃V₃ hw, hwR₂⟩)
  rcases (mem_sup_zpowers_iff_of h.t_mul_t (h.t_mem_normalizer_yamadaW₂ d hK hD).1).1 hwV₂ with
    hwW | ⟨a, ha, rfl⟩
  · exact mul_mem (hW₂S₂ hwW) hs
  · exfalso
    refine htW₃ ?_
    have := mul_mem (inv_mem (hW₂W₃ ha)) hw
    rwa [inv_mul_cancel_left] at this

theorem yamadaS₃_center (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d)
    (hUW : yamadaW₃ d t ≤ centralizer (yamadaU₁ d t : Set G))
    (hWY : ∀ w ∈ yamadaW₃ d t, ∀ y ∈ yamadaY₂ d t, w * y * w⁻¹ * y⁻¹ ∈ yamadaU₁ d t) :
    yamadaS₃ d t ⊓ centralizer (yamadaS₃ d t : Set G) = yamadaU₁ d t ∧
      (Subgroup.upperCentralSeries (yamadaS₃ d t) 1).map (yamadaS₃ d t).subtype =
        yamadaU₁ d t ∧
      (Subgroup.upperCentralSeries (yamadaS₃ d t) 2).map (yamadaS₃ d t).subtype =
        yamadaY₂ d t := by
  obtain ⟨⟨-, -, hsetS⟩, -⟩ := h.yamada_5_30_2 hW d hK hD
  obtain ⟨hZS₂, -⟩ := h.yamada_5_13_5 d hK hD
  have hS₂S₃ : yamadaS₂ d t ≤ yamadaS₃ d t := le_sup_right
  have hU₁S₂ : yamadaU₁ d t ≤ yamadaS₂ d t := (yamadaU₁_le_yamadaY₂ d t).trans le_sup_right
  have hY₂S₂ : yamadaY₂ d t ≤ yamadaS₂ d t := le_sup_right
  have hS₁S₂ : yamadaS₁ d t ≤ yamadaS₂ d t := by
    rw [h.yamadaS₁_eq_sup d hK hD]
    exact sup_le_sup_left (yamadaU₁_le_yamadaY₂ d t) _
  have hU₁S₁ : yamadaU₁ d t ≤ yamadaS₁ d t := by
    rw [h.yamadaS₁_eq_sup d hK hD]
    exact le_sup_right
  obtain ⟨-, -, -, ⟨hL, -⟩, ⟨hR, -⟩, -⟩ := h.yamada_5_30_2 hW d hK hD
  have hS₃R₃ : yamadaS₃ d t ≤ yamadaR₃ d t := le_sup_left.trans hR.le
  have hR₃R₅ : yamadaR₃ d t ≤ yamadaR₅ d t :=
    le_sup_left.trans (h.yamada_5_27_2 hW d hK hD).1.1.ge
  have hS₁N : ∀ x ∈ yamadaS₃ d t, x ∈ normalizer (yamadaS₁ d t : Set G) → x ∈ yamadaS₂ d t :=
    fun x hx hxN => by
      rw [← h.yamadaS₃_inf_yamadaR₂ hW d hK hD]
      refine Subgroup.mem_inf.2 ⟨hx, ?_⟩
      rw [← (h.yamada_5_28 hW d hK hD).2.1]
      exact Subgroup.mem_inf.2 ⟨hR₃R₅ (hS₃R₃ hx), hxN⟩
  have hU₁C : yamadaU₁ d t ≤ centralizer (yamadaS₃ d t : Set G) := by
    rw [← Subgroup.le_centralizer_iff]
    show yamadaW₃ d t ⊔ yamadaS₂ d t ≤ _
    exact sup_le hUW ((Subgroup.le_centralizer_iff).1 (hZS₂.ge.trans inf_le_right))
  have hZ : yamadaS₃ d t ⊓ centralizer (yamadaS₃ d t : Set G) = yamadaU₁ d t := by
    refine le_antisymm (fun z hz => ?_) (le_inf (hU₁S₂.trans hS₂S₃) hU₁C)
    obtain ⟨hzS, hzC⟩ := Subgroup.mem_inf.1 hz
    have hzS₂ := hS₁N z hzS (Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (hS₁S₂.trans hS₂S₃) hzC))
    rw [← hZS₂]
    exact Subgroup.mem_inf.2 ⟨hzS₂, Subgroup.centralizer_le hS₂S₃ hzC⟩
  have hiff : ∀ {x : G}, x ∈ yamadaS₃ d t →
      (x ∈ yamadaY₂ d t ↔ ∀ g ∈ yamadaS₃ d t, x * g * x⁻¹ * g⁻¹ ∈ yamadaU₁ d t) := by
    intro x hx
    constructor
    · intro hxY g hg
      have hg' : g ∈ ((yamadaS₃ d t : Subgroup G) : Set G) := hg
      rw [hsetS] at hg'
      obtain ⟨w, hw, s, hs, rfl⟩ := Set.mem_mul.1 hg'
      have h1 : x * w * x⁻¹ * w⁻¹ ∈ yamadaU₁ d t := by
        have := inv_mem (hWY w hw x hxY)
        rwa [show (w * x * w⁻¹ * x⁻¹)⁻¹ = x * w * x⁻¹ * w⁻¹ by group] at this
      have h2 := ((h.mem_yamadaY₂_iff d hK hD (hY₂S₂ hxY)).1 hxY) s hs
      have h3 : w * (x * s * x⁻¹ * s⁻¹) * w⁻¹ = x * s * x⁻¹ * s⁻¹ := by
        rw [← mem_centralizer_iff.1 (hUW hw) _ h2, mul_inv_cancel_right]
      rw [show x * (w * s) * x⁻¹ * (w * s)⁻¹ =
        (x * w * x⁻¹ * w⁻¹) * (w * (x * s * x⁻¹ * s⁻¹) * w⁻¹) by group, h3]
      exact mul_mem h1 h2
    · intro hc
      have hxN : x ∈ normalizer (yamadaS₁ d t : Set G) := mem_normalizer_of_conj_mem fun y hy => by
        rw [show x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y by group]
        exact mul_mem (hU₁S₁ (hc y (hS₂S₃ (hS₁S₂ hy)))) hy
      have hxS₂ := hS₁N x hx hxN
      exact (h.mem_yamadaY₂_iff d hK hD hxS₂).2 fun g hg => hc g (hS₂S₃ hg)
  have hmem1 : ∀ x : yamadaS₃ d t,
      x ∈ Subgroup.upperCentralSeries (yamadaS₃ d t) 1 ↔ (x : G) ∈ yamadaU₁ d t := by
    intro x
    rw [Subgroup.upperCentralSeries_one, ← hZ]
    constructor
    · intro hx
      exact ⟨x.2, mem_centralizer_iff.2 fun y hy =>
        congrArg Subtype.val (mem_center_iff.1 hx ⟨y, hy⟩)⟩
    · rintro ⟨-, hc⟩
      exact mem_center_iff.2 fun y => Subtype.ext (mem_centralizer_iff.1 hc y y.2)
  have hmem2 : ∀ x : yamadaS₃ d t,
      x ∈ Subgroup.upperCentralSeries (yamadaS₃ d t) 2 ↔ (x : G) ∈ yamadaY₂ d t := by
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
      exact ⟨⟨x, (hU₁S₂.trans hS₂S₃) hx⟩, (hmem1 _).2 hx, rfl⟩
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hmem2 y).1 hy
    · intro hx
      exact ⟨⟨x, (hY₂S₂.trans hS₂S₃) hx⟩, (hmem2 _).2 hx, rfl⟩

theorem yamadaS₃_le_centralizer_yamadaU₁ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (h8 : 8 ≤ Nat.card K) :
    yamadaS₃ d t ≤ centralizer (yamadaU₁ d t : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.doublingFacts_of_eight d hK h8
  obtain ⟨⟨-, -, hsetS⟩, ⟨hV₃N, -, -, -⟩, -, -, ⟨hR, htS₃⟩, -⟩ := h.yamada_5_30_2 hW d hK hD
  obtain ⟨hR₃R, -⟩ := h.yamadaR₃_facts hW d hK hD
  obtain ⟨-, -, hRS⟩ := h.yamadaR₃_le_normalizers hW d hK hD
  obtain ⟨-, -, hJW₃, -⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨hZS₂, -⟩ := h.yamada_5_13_5 d hK hD
  have hJ₁J : d.J₁ ≤ d.J := d.image_mono inf_le_left
  have hJC := h.J_le_centralizer_inf_normalizer_S d
  have hS₃R₃ : yamadaS₃ d t ≤ yamadaR₃ d t := le_sup_left.trans hR.le
  have hS₃p : IsPGroup 2 (yamadaS₃ d t) := (h.isPGroup_yamadaRstar d).to_le (hS₃R₃.trans hR₃R)
  have hS₂S₃ : yamadaS₂ d t ≤ yamadaS₃ d t := le_sup_right
  have hU₁S₂ : yamadaU₁ d t ≤ yamadaS₂ d t := (yamadaU₁_le_yamadaY₂ d t).trans le_sup_right
  have hJS₂ : d.J ≤ normalizer (yamadaS₂ d t : Set G) := h.J_le_normalizer_yamadaS₂ d hK hD
  have hJS₃ : d.J ≤ normalizer (yamadaS₃ d t : Set G) := fun j hj =>
    mem_normalizer_sup (hJW₃ hj) (hJS₂ hj)
  have hS₃U₁ : yamadaS₃ d t ≤ normalizer (yamadaU₁ d t : Set G) := fun x hx => by
    rw [← hZS₂]
    exact Common.mem_normalizer_inf (hRS (hS₃R₃ hx)) (mem_normalizer_centralizer (hRS (hS₃R₃ hx)))
  have htR₃ : t ∈ yamadaR₃ d t := hR.le (mem_sup_right (mem_zpowers t))
  have hU₁R₃ : yamadaU₁ d t ≤ yamadaR₃ d t := (hU₁S₂.trans hS₂S₃).trans hS₃R₃
  have hCR₃ := h.eq_yamadaU₁_sup_of_isPGroup d hK h8 ((h.isPGroup_yamadaRstar d).to_le
    (inf_le_left.trans hR₃R)) inf_le_right (le_inf (sup_le hU₁R₃ ((zpowers_le).2 htR₃))
      (sup_le hD.le_centralizer_J₁ ((zpowers_le).2 (mem_centralizer_iff.2 fun j hj =>
        mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hj))))))
  have hCS₃ : yamadaS₃ d t ⊓ centralizer (d.J₁ : Set G) ≤ yamadaU₁ d t := fun x hx => by
    obtain ⟨hxS, hxJ⟩ := Subgroup.mem_inf.1 hx
    have hxT : x ∈ yamadaU₁ d t ⊔ zpowers t := by
      rw [← hCR₃]
      exact Subgroup.mem_inf.2 ⟨hS₃R₃ hxS, hxJ⟩
    have htU₁ : t ∈ normalizer (yamadaU₁ d t : Set G) := (h.t_mem_normalizer_yamadaU₁ d hK hD).1
    rcases (mem_sup_zpowers_iff_of h.t_mul_t htU₁).1 hxT with h1 | ⟨u, hu, rfl⟩
    · exact h1
    · exfalso
      refine htS₃ ?_
      have := mul_mem (inv_mem ((hU₁S₂.trans hS₂S₃) hu)) hxS
      rwa [inv_mul_cancel_left] at this
  have hcomm : ⁅yamadaS₃ d t, d.J₁⁆ ≤ centralizer (yamadaU₁ d t : Set G) :=
    (Subgroup.commutator_le).2 fun s hs j hj => mem_centralizer_iff.2 fun u hu => by
      have hu' : s⁻¹ * u * s ∈ yamadaU₁ d t := by
        have := (mem_normalizer_iff.1 (inv_mem (hS₃U₁ hs)) u).1 hu
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
  have hcop : Nat.Coprime (Nat.card d.J₁) (Nat.card (yamadaS₃ d t)) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS₃p
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hJ₁odd)
  have hJ₁S₃ : d.J₁ ≤ normalizer (yamadaS₃ d t : Set G) := fun j hj => hJS₃ (hJ₁J hj)
  have hNS₃ : ⁅yamadaS₃ d t, d.J₁⁆ ≤ yamadaS₃ d t := (Subgroup.commutator_le).2 fun s hs j hj => by
    rw [commutatorElement_def, show s * j * s⁻¹ * j⁻¹ = s * (j * s⁻¹ * j⁻¹) by group]
    exact mul_mem hs ((mem_normalizer_iff.1 (hJ₁S₃ hj) _).1 (inv_mem hs))
  refine (Subgroup.le_centralizer_iff).1 fun u hu => mem_centralizer_iff.2 fun s hs => ?_
  have : Group.IsNilpotent (yamadaS₃ d t) := hS₃p.isNilpotent
  obtain ⟨c, hc, n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime
    (M := yamadaS₃ d t) (N := ⁅yamadaS₃ d t, d.J₁⁆) (S := d.J₁) hNS₃
    (le_normalizer_commutator_left _ _) hJ₁S₃
    (fun j hj => mem_normalizer_commutator (hJ₁S₃ hj) (Subgroup.le_normalizer hj)) inferInstance
    hcop hs fun j hj => by
      rw [show s⁻¹ * (j * s * j⁻¹) = ⁅s⁻¹, j⁆ by simp only [commutatorElement_def]; group]
      exact commutator_mem_commutator (inv_mem hs) hj
  have hcU : c ∈ yamadaU₁ d t := hCS₃ hc
  have e1 : c * u = u * c := hD.mul_comm hcU hu
  have e2 : n * u = u * n := (mem_centralizer_iff.1 (hcomm hn) u hu).symm
  calc c * n * u = c * (n * u) := by group
    _ = c * (u * n) := by rw [e2]
    _ = c * u * n := by group
    _ = u * c * n := by rw [e1]
    _ = u * (c * n) := by group

theorem yamadaM₃_le_centralizer_yamadaY₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (h8 : 8 ≤ Nat.card K) :
    yamadaM₃ d t ≤ centralizer (yamadaY₂ d t : Set G) := by
  have hD := h.doublingFacts_of_eight d hK h8
  have hU := h.yamadaS₃_le_centralizer_yamadaU₁ hW d hK h8
  have hM₃S₃ : yamadaM₃ d t ≤ yamadaS₃ d t :=
    sup_le_sup_left (sup_le_sup_right d.inclusions.2.2.2.2.2.2.2.2.1 _) _
  have hwb : d.wb ∈ normalizer (yamadaM₃ d t : Set G) :=
    h.yamada_5_30_3 hW d hK hD d.wb_mem_normalizer.1
  have hU₁M₃ : yamadaU₁ d t ≤ centralizer (yamadaM₃ d t : Set G) :=
    (Subgroup.le_centralizer_iff).1 (hM₃S₃.trans hU)
  rw [← Subgroup.le_centralizer_iff]
  refine sup_le hU₁M₃ fun x hx => ?_
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hx
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine mem_centralizer_iff.2 fun m hm => ?_
  have hm' : d.wb⁻¹ * m * d.wb ∈ yamadaM₃ d t := by
    have := (mem_normalizer_iff.1 (inv_mem hwb) m).1 hm
    rwa [inv_inv] at this
  have e := mem_centralizer_iff.1 (hU₁M₃ hu) _ hm'
  calc m * (d.wb * u * d.wb⁻¹) = d.wb * ((d.wb⁻¹ * m * d.wb) * u) * d.wb⁻¹ := by group
    _ = d.wb * (u * (d.wb⁻¹ * m * d.wb)) * d.wb⁻¹ := by rw [e]
    _ = d.wb * u * d.wb⁻¹ * m := by group

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
