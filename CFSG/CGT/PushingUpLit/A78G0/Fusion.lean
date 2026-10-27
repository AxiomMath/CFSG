module

public import CFSG.CGT.PushingUpLit.A78G0.Data
public import CFSG.CGT.PushingUpLit.A78G0.Basic
public import CFSG.CGT.PushingUpLit.A78.Sp4Fusion

public section

namespace CFSG.CGT.PushingUpLit.A78G0

open CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4 CFSG.CGT.PushingUpLit.A78S4
  CFSG.ABGLocalTools

section Generic

variable {G : Type} [Group G]

theorem elemAb2_of_abelian_sq {E : Subgroup G} (hab : ∀ x ∈ E, ∀ y ∈ E, Commute x y)
    (hsq : ∀ x ∈ E, x * x = 1) : ElemAb2 E :=
  fun x hx y hy => ⟨(hab x hx y hy).eq, hsq x hx⟩

end Generic

namespace G0Core

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ : Subgroup G} {e : ℕ}
  (h : G0Core G L₁ L₂ V W Z Z₂ e)

include h

theorem two_le : 2 ≤ e := h.pair.side₁.two_le

theorem jst : JStructure G (V ⊔ W) V W e := h.pair.side₁.jst

theorem elemAb2_V : ElemAb2 V := elemAb2_of_abelian_sq h.jst.abelian_V h.jst.sq_V

theorem elemAb2_W : ElemAb2 W := elemAb2_of_abelian_sq h.jst.abelian_V₂ h.jst.sq_V₂

theorem isPGroup_J : IsPGroup 2 ↥(V ⊔ W) := h.sylow.isPGroup

theorem odd_index_J : ¬ 2 ∣ (V ⊔ W).index := by
  have := (isSylowOf_iff.1 h.sylow).2.2
  rwa [Subgroup.relIndex_top_right] at this

theorem fusionData : FusionData (V ⊔ W) V W where
  pgroup := h.isPGroup_J
  odd_index := h.odd_index_J
  le := le_sup_left
  normalizes := le_normalizer_of_conj' h.jst.conj_V
  normalizes₂ := le_normalizer_of_conj' h.jst.conj_V₂
  ne := fun hVW => h.jst.not_le_V₂ (hVW ▸ le_rfl)
  abelian := h.jst.abelian_V
  sq := h.jst.sq_V
  mem := fun _ hA _ hsq hcard => h.jst.mem_of_card hA hsq hcard

theorem fusionData₂ : FusionData (V ⊔ W) W V where
  pgroup := h.isPGroup_J
  odd_index := h.odd_index_J
  le := le_sup_right
  normalizes := le_normalizer_of_conj' h.jst.conj_V₂
  normalizes₂ := le_normalizer_of_conj' h.jst.conj_V
  ne := fun hWV => h.jst.not_le_V₂ (hWV ▸ le_rfl)
  abelian := h.jst.abelian_V₂
  sq := h.jst.sq_V₂
  mem := fun _ hA _ hsq hcard => by
    rcases h.jst.mem_of_card hA hsq (hcard.trans h.jst.card_V₂_eq) with h1 | h1
    · exact Or.inr h1
    · exact Or.inl h1

theorem normalizer_J_eq :
    Subgroup.normalizer ((V ⊔ W : Subgroup G) : Set G) =
      Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (W : Set G) := by
  apply le_antisymm
  · intro b hb
    constructor
    · rcases h.fusionData.conjSub_mem hb with h1 | h1
      · exact mem_normalizer_of_cs_eq h1
      · exact absurd h1 (h.fusionData.conjSub_ne hb)
    · rcases h.fusionData₂.conjSub_mem hb with h1 | h1
      · exact mem_normalizer_of_cs_eq h1
      · exact absurd h1 (h.fusionData₂.conjSub_ne hb)
  · intro b hb
    apply mem_normalizer_of_cs_eq
    rw [cs_sup, cs_of_mem_normalizer hb.1, cs_of_mem_normalizer hb.2]

theorem normalizer_J_le_V : Subgroup.normalizer ((V ⊔ W : Subgroup G) : Set G) ≤
    Subgroup.normalizer (V : Set G) := h.normalizer_J_eq.le.trans inf_le_left

theorem normalizer_J_le_W : Subgroup.normalizer ((V ⊔ W : Subgroup G) : Set G) ≤
    Subgroup.normalizer (W : Set G) := h.normalizer_J_eq.le.trans inf_le_right

theorem Z_le_N : Z ≤ V ⊓ W := h.pair.side₁.Z_le_N

theorem Z₂_le_N : Z₂ ≤ V ⊓ W := h.pair.Z₂_le_N

theorem Z_le_V : Z ≤ V := h.Z_le_N.trans inf_le_left

theorem Z_le_W : Z ≤ W := h.Z_le_N.trans inf_le_right

theorem Z₂_le_V : Z₂ ≤ V := h.Z₂_le_N.trans inf_le_left

theorem Z₂_ne_bot : Z₂ ≠ ⊥ := h.pair.Z₂_ne_bot h.hZ

theorem card_Z : Nat.card Z = 2 ^ e := h.pair.card_Z h.hZ

theorem inf_Z : Z ⊓ Z₂ = ⊥ := h.pair.inf_Z

theorem sq_Z : ∀ z ∈ Z, z * z = 1 := fun z hz => h.jst.sq_V z (h.Z_le_V hz)

theorem ex_ne_one_Z : ∃ z ∈ Z, z ≠ 1 := by
  by_contra hcon
  push Not at hcon
  exact h.hZ ((Subgroup.eq_bot_iff_forall _).2 hcon)

theorem kl {g b : G} (hbg : b ∈ cs Z g) (hbV : b ∈ V) (hb1 : b ≠ 1) : cs Z g = Z := by
  have hz : g⁻¹ * b * g ∈ Z := mem_cs.1 hbg
  have hz1 : g⁻¹ * b * g ≠ 1 := fun h1 => hb1 (by
    have : b = g * (g⁻¹ * b * g) * g⁻¹ := by group
    rw [this, h1]
    group)
  have hC := h.side₁.cent_z _ hz hz1
  have hVg : cs V g⁻¹ ≤ Subgroup.normalizer (V : Set G) := by
    intro x hx
    rw [mem_cs, inv_inv] at hx
    apply hC
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hvb : (g * x * g⁻¹) * b = b * (g * x * g⁻¹) := (h.jst.abelian_V _ hx b hbV).eq
    have key : (g⁻¹ * b * g) * x = x * (g⁻¹ * b * g) := by
      calc (g⁻¹ * b * g) * x = g⁻¹ * (b * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * b) * g := by rw [hvb]
        _ = x * (g⁻¹ * b * g) := by group
    first | exact key | exact key.symm
  have hV2 : IsPGroup 2 ↥(cs V g⁻¹) := (elemAb2_cj h.elemAb2_V g⁻¹).isPGroup
  obtain ⟨m, hm, hmJ⟩ := exists_conj_le_of_isSylowOf h.side₁.sylow_T hVg hV2
  have hcj : cj m (cs V g⁻¹) = cs V (m * g⁻¹) := cj_cj m g⁻¹ V
  have hmJ' : cs V (m * g⁻¹) ≤ V ⊔ W := hcj ▸ hmJ
  have hwc : cs V (m * g⁻¹) = V := h.fusionData.weaklyClosed (g := m * g⁻¹) hmJ'
  have hn : m * g⁻¹ ∈ Subgroup.normalizer (V : Set G) := mem_normalizer_of_cs_eq hwc
  have hM : (Subgroup.normalizer (V : Set G)).carrier = (Subgroup.normalizer (V : Set G)).carrier :=
    rfl
  have hg' : g⁻¹ ∈ Subgroup.normalizer (V : Set G) := by
    have := (Subgroup.normalizer (V : Set G)).mul_mem
      ((Subgroup.normalizer (V : Set G)).inv_mem hm) hn
    simpa [mul_assoc] using this
  have hgM : g ∈ Subgroup.normalizer (V : Set G) := by
    simpa using (Subgroup.normalizer (V : Set G)).inv_mem hg'
  exact cs_of_mem_normalizer (h.side₁.normalizer_Z ▸ hgM)

theorem cs_inf_V {g : G} (hg : cs Z g ≠ Z) : cs Z g ⊓ V = ⊥ := by
  by_contra hne
  obtain ⟨⟨b, hb⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  exact hg (h.kl hb.1 hb.2 (fun h1 => hb1 (Subtype.ext h1)))

theorem eq_of_cs_le_V {g : G} (hg : cs Z g ≤ V) : cs Z g = Z := by
  obtain ⟨z, hz, hz1⟩ := h.ex_ne_one_Z
  exact h.kl (b := g * z * g⁻¹) (conj_mem_cs g hz) (hg (conj_mem_cs g hz))
    (fun h1 => hz1 (by
      have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
      rw [this, h1]
      group))

theorem cs_le_J {g : G} (hg : cs Z g ≤ V ⊔ W) : cs Z g = Z ∨ cs Z g ≤ W := by
  have hsq : ∀ x ∈ cs Z g, x * x = 1 := sq_of_mem_conjSub h.sq_Z g
  rcases h.jst.elemAbelian_le hg hsq with h1 | h1
  · exact Or.inl (h.eq_of_cs_le_V h1)
  · exact Or.inr h1

theorem exists_normalizer_of_cs_le_W {g : G} (hg : cs Z g ≤ W) :
    ∃ n ∈ Subgroup.normalizer (W : Set G), cs Z g = cs Z n := by
  obtain ⟨z, hz, hz1⟩ := h.ex_ne_one_Z
  have hZW' : Z ≤ cs W g⁻¹ := by
    have := cs_mono hg g⁻¹
    rwa [cs_cs_inv] at this
  have hWM : cs W g⁻¹ ≤ Subgroup.normalizer (V : Set G) := by
    intro w hw
    apply h.side₁.cent_z z hz hz1
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_of_mem_conjSub h.jst.abelian_V₂ g⁻¹ z (hZW' hz) w hw).eq.symm
  have hW2 : IsPGroup 2 ↥(cs W g⁻¹) := (elemAb2_cj h.elemAb2_W g⁻¹).isPGroup
  obtain ⟨m, hm, hmJ⟩ := exists_conj_le_of_isSylowOf h.side₁.sylow_T hWM hW2
  have hcj : cj m (cs W g⁻¹) = cs W (m * g⁻¹) := cj_cj m g⁻¹ W
  have hmJ' : cs W (m * g⁻¹) ≤ V ⊔ W := hcj ▸ hmJ
  have hwc : cs W (m * g⁻¹) = W := h.fusionData₂.weaklyClosed (g := m * g⁻¹) hmJ'
  have hn : m * g⁻¹ ∈ Subgroup.normalizer (W : Set G) := mem_normalizer_of_cs_eq hwc
  refine ⟨(m * g⁻¹)⁻¹, (Subgroup.normalizer (W : Set G)).inv_mem hn, ?_⟩
  have hmZ : cs Z m = Z := cs_of_mem_normalizer (h.side₁.normalizer_Z ▸ hm)
  have e1 : g = (m * g⁻¹)⁻¹ * m := by group
  conv_lhs => rw [e1]
  rw [cs_mul, hmZ]

theorem cs_le_W_of_mem {n : G} (hn : n ∈ Subgroup.normalizer (W : Set G)) : cs Z n ≤ W := by
  have := cs_mono h.Z_le_W n
  rwa [cs_of_mem_normalizer hn] at this

end G0Core

end CFSG.CGT.PushingUpLit.A78G0
