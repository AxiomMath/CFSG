module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYFourFacts

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

theorem normalizer_le_normalizer_center {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    normalizer (H : Set G) ≤
      normalizer ((H ⊓ centralizer (H : Set G) : Subgroup G) : Set G) := by
  intro n hn
  refine mem_normalizer_of_conj_mem fun x hx => ⟨(mem_normalizer_iff.1 hn x).1 hx.1,
    mem_centralizer_iff.2 fun y hy => ?_⟩
  have hy' : n⁻¹ * y * n ∈ H := by
    have := (mem_normalizer_iff.1 (inv_mem hn) y).1 hy
    rwa [inv_inv] at this
  have e := mem_centralizer_iff.1 hx.2 _ hy'
  calc y * (n * x * n⁻¹) = n * ((n⁻¹ * y * n) * x) * n⁻¹ := by group
    _ = n * (x * (n⁻¹ * y * n)) * n⁻¹ := by rw [e]
    _ = n * x * n⁻¹ * y := by group

section AutImage

variable {G : Type*} [Group G] {H : Subgroup G}

@[expose] def autImage (φ : H ≃* H) (E : Subgroup G) : Subgroup G :=
  (E.subgroupOf H).map (H.subtype.comp φ.toMonoidHom)

theorem mem_autImage {φ : H ≃* H} {E : Subgroup G} {x : G} :
    x ∈ autImage φ E ↔ ∃ y : H, (y : G) ∈ E ∧ ((φ y : H) : G) = x := by
  simp only [autImage, mem_map, mem_subgroupOf, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]

theorem autImage_le (φ : H ≃* H) (E : Subgroup G) : autImage φ E ≤ H := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := mem_autImage.1 hx
  exact (φ y).2

theorem autImage_mono (φ : H ≃* H) {E E' : Subgroup G} (h : E ≤ E') :
    autImage φ E ≤ autImage φ E' := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_autImage.1 hx
  exact mem_autImage.2 ⟨y, h hy, rfl⟩

theorem autImage_symm (φ : H ≃* H) {E : Subgroup G} (hE : E ≤ H) :
    autImage φ.symm (autImage φ E) = E := by
  ext x
  rw [mem_autImage]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hze⟩ := mem_autImage.1 hy
    have : y = φ z := Subtype.ext hze.symm
    rw [this, MulEquiv.symm_apply_apply]
    exact hz
  · intro hx
    refine ⟨φ ⟨x, hE hx⟩, mem_autImage.2 ⟨⟨x, hE hx⟩, hx, rfl⟩, ?_⟩
    rw [MulEquiv.symm_apply_apply]

theorem autImage_self (φ : H ≃* H) : autImage φ H = H := by
  refine le_antisymm (autImage_le φ H) fun x hx => mem_autImage.2 ⟨φ.symm ⟨x, hx⟩, (φ.symm _).2, ?_⟩
  rw [MulEquiv.apply_symm_apply]

theorem autImage_injective (φ : H ≃* H) {E E' : Subgroup G} (hE : E ≤ H) (hE' : E' ≤ H)
    (h : autImage φ E = autImage φ E') : E = E' := by
  rw [← autImage_symm φ hE, h, autImage_symm φ hE']

theorem autImage_inf_centralizer (φ : H ≃* H) {E : Subgroup G} (hE : E ≤ H) :
    autImage φ (E ⊓ centralizer (E : Set G)) =
      autImage φ E ⊓ centralizer (autImage φ E : Set G) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, ⟨hy₁, hy₂⟩, rfl⟩ := mem_autImage.1 hx
    refine ⟨mem_autImage.2 ⟨y, hy₁, rfl⟩, mem_centralizer_iff.2 fun w hw => ?_⟩
    obtain ⟨z, hz, rfl⟩ := mem_autImage.1 hw
    have e : z * y = y * z := Subtype.ext (mem_centralizer_iff.1 hy₂ _ hz)
    rw [← Subgroup.coe_mul, ← map_mul, e, map_mul, Subgroup.coe_mul]
  · rintro ⟨hx₁, hx₂⟩
    obtain ⟨y, hy, rfl⟩ := mem_autImage.1 hx₁
    refine mem_autImage.2 ⟨y, ⟨hy, mem_centralizer_iff.2 fun w hw => ?_⟩, rfl⟩
    have h1 := mem_centralizer_iff.1 hx₂ _ (mem_autImage.2 ⟨⟨w, hE hw⟩, hw, rfl⟩)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (φ.injective (Subtype.ext h1))

theorem autImage_closure_sq (φ : H ≃* H) {E : Subgroup G} (hE : E ≤ H) :
    autImage φ (closure {z | ∃ g ∈ E, z = g ^ 2}) =
      closure {z | ∃ g ∈ autImage φ E, z = g ^ 2} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_autImage.1 hx
    set T' : Subgroup H := (closure {z | ∃ g ∈ autImage φ E, z = g ^ 2}).comap
      (H.subtype.comp φ.toMonoidHom) with hT'
    have hle : closure {z | ∃ g ∈ E, z = g ^ 2} ≤ T'.map H.subtype := by
      rw [closure_le]
      rintro _ ⟨g, hg, rfl⟩
      refine ⟨⟨g, hE hg⟩ ^ 2, ?_, by simp⟩
      rw [hT', SetLike.mem_coe, mem_comap, map_pow]
      exact subset_closure ⟨_, mem_autImage.2 ⟨⟨g, hE hg⟩, hg, rfl⟩, rfl⟩
    obtain ⟨y', hy', hyy'⟩ := hle hy
    have : y' = y := Subtype.ext hyy'
    rw [this] at hy'
    exact hy'
  · rw [closure_le]
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨y, hy, rfl⟩ := mem_autImage.1 hg
    exact mem_autImage.2 ⟨y ^ 2, subset_closure ⟨y, hy, by simp⟩, by simp⟩

theorem elemModulo_autImage (φ : H ≃* H) {N E : Subgroup G} (h : ElemModulo N E) :
    ElemModulo (autImage φ N) (autImage φ E) := by
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := mem_autImage.1 hx
  obtain ⟨b, hb, rfl⟩ := mem_autImage.1 hy
  obtain ⟨h1, h2⟩ := h _ ha _ hb
  refine ⟨mem_autImage.2 ⟨a * a, by simpa using h1, by simp⟩,
    mem_autImage.2 ⟨⁅a, b⁆, by simpa [commutatorElement_def] using h2, ?_⟩⟩
  simp [commutatorElement_def]

theorem characteristic_of_autImage {E : Subgroup G}
    (h : ∀ φ : H ≃* H, autImage φ E = E) : (E.subgroupOf H).Characteristic := by
  refine ⟨fun φ => ?_⟩
  ext x
  rw [mem_comap, mem_subgroupOf, mem_subgroupOf, MulEquiv.coe_toMonoidHom]
  constructor
  · intro hx
    rw [← h φ] at hx
    obtain ⟨y, hy, hyx⟩ := mem_autImage.1 hx
    rwa [φ.injective (Subtype.ext hyx)] at hy
  · intro hx
    rw [← h φ]
    exact mem_autImage.2 ⟨x, hx, rfl⟩

end AutImage

namespace Model

variable
  {K : Type} [Field K] [CharP K 2]

theorem map_wa_W_le_D : (W K).map (MulAut.conj (wa K)).toMonoidHom ≤ Model.D K := by
  rintro _ ⟨_, ⟨D, E, F, rfl⟩, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, wa]
  rw [weylElt_r_conj_g2N]
  exact g2N_mem_D_iff.2 rfl

theorem D_le_sup_map_wa : Model.D K ≤ W K ⊔ (W K).map (MulAut.conj (wa K)).toMonoidHom := by
  intro g hg
  obtain ⟨B, C, D, E, F, rfl⟩ := mem_D.1 hg
  have h : g2N 0 B C D E F = g2N 0 B C 0 0 0 * g2N 0 0 0 D E F := by
    rw [g2N_mul_coords]
    refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  rw [h]
  exact mul_mem (mem_sup_right (mem_map_wa_W (F := 0))) (mem_sup_left
    (g2N_mem_W_iff.2 ⟨rfl, rfl, rfl⟩))

end Model

namespace G2Data

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

variable
  [CharP K 2]

theorem D_eq_W_sup_map_wa : d.D = d.W ⊔ d.W.map (MulAut.conj d.wa).toMonoidHom ∧
    d.W.map (MulAut.conj d.wa).toMonoidHom ≤ d.D := by
  have hWa : (Model.W K).map (MulAut.conj (Model.wa K)).toMonoidHom ≤ adjointGroup .G2 K :=
    Model.map_wa_W_le_S.trans (Model.S_le_adjointGroup K)
  have h1 := d.image_conj.1
  refine ⟨le_antisymm ?_ (sup_le (d.inclusions.2.2.2.2.1.trans d.inclusions.2.2.2.2.2.1) ?_), ?_⟩
  · rw [G2Data.D, ← h1, G2Data.W, ← d.image_sup Model.W_le_adjointGroup hWa]
    exact d.image_mono Model.D_le_sup_map_wa
  · rw [← h1, G2Data.D]
    exact d.image_mono Model.map_wa_W_le_D
  · rw [← h1, G2Data.D]
    exact d.image_mono Model.map_wa_W_le_D

theorem wa_mem_inf_normalizer_U [Finite K] : d.wa ∈ L ⊓ normalizer (d.U : Set G) := by
  rw [(d.yamada_3_13_2_G).1]
  exact mem_sup_right (mem_sup_left (d.emb_mem_image (weylElt_mem_g2RankOne g2ir 1)))

theorem not_M_le_D : ¬ d.M ≤ d.D := fun h =>
  Model.not_M_le_D.1 ((d.image_le_image_iff Model.M_le_adjointGroup).1 h)

theorem mem_D_or_M_of_mul_self_mem {s : G} (hs : s ∈ d.S) (hss : s * s ∈ d.Y) :
    s ∈ d.D ∨ s ∈ d.M := by
  obtain ⟨g, hg, rfl⟩ := d.mem_image.1 hs
  rw [← map_mul] at hss
  have hss' : (g : ModGL .G2 K) * g ∈ Model.Y K := d.emb_mem_image_iff.1 hss
  rcases Model.mem_D_or_M_of_mul_self_mem (Or.inl Model.Y_le_W) hg hss' with h1 | h1
  · exact Or.inl (d.emb_mem_image h1)
  · exact Or.inr (d.emb_mem_image h1)

end G2Data

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem S_le_normalizer_yamadaU₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.S ≤ normalizer (yamadaU₁ d t : Set G) := by
  rw [(hD.yamada_5_10_3).1]
  exact ((h.S_le_inf_normalizer_U d).trans (h.inf_normalizer_U_le_normalizer_yamadaD₁ d hK)).trans
    (normalizer_le_normalizer_center _)

theorem commutator_mem_U_of_mem_S (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {s u : G} (hs : s ∈ d.S) (hu : u ∈ yamadaU₁ d t) : ⁅s, u⁆ ∈ d.U := by
  obtain ⟨hC₁U, -, -, -⟩ := h.two_core_C₁ d hK
  obtain ⟨hU₁D₁, -, -⟩ := hD.spec
  have hc₁ := h.cosetData_tU d hK
  have hU₁C₁ : yamadaU₁ d t ≤ yamadaC₁ d t := hU₁D₁.trans (h.yamadaD₁_le_yamadaC₁ d hK)
  have hV : ∀ {g : G}, g ∈ yamadaU₁ d t → g ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) :
      Set G) ⊓ centralizer (d.U : Set G) := fun hg =>
    ⟨yamadaC₁_le d t (hU₁C₁ hg), hC₁U (hU₁C₁ hg)⟩
  have hsu : s * u * s⁻¹ ∈ yamadaU₁ d t :=
    (mem_normalizer_iff.1 (h.S_le_normalizer_yamadaU₁ d hK hD hs) u).1 hu
  have hst : s * t = t * s := mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs)
  have hκ := hc₁.crossed_mem_of_mem (hV hu)
  have hsκ : s * (u⁻¹ * t * u * t) * s⁻¹ = u⁻¹ * t * u * t := by
    have h1 : s ∈ centralizer (d.U : Set G) := by
      exact mem_centralizer_iff.2 fun w hw => by
        rw [← (d.yamada_3_12_centers).1] at hw
        exact (mem_centralizer_iff.1 hw.2 s hs).symm
    rw [← mem_centralizer_iff.1 h1 _ (hc₁.crossed_mem_of_mem (hV hu)), mul_inv_cancel_right]
  have hw : ⁅s, u⁆ ∈ yamadaU₁ d t := by
    rw [commutatorElement_def]
    exact mul_mem hsu (inv_mem hu)
  have h1 : (s * u * s⁻¹ * u⁻¹)⁻¹ * t * (s * u * s⁻¹ * u⁻¹) * t = 1 := by
    rw [hc₁.crossed_mul_of_mem (hV hsu) (hV (inv_mem hu)),
      CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj hst, hsκ, hc₁.crossed_inv_of_mem (hV hu),
      mul_inv_cancel]
  rw [← hD.inf_centralizer]
  refine ⟨hw, mem_centralizer_singleton_iff.2 ?_⟩
  rw [commutatorElement_def]
  have e' := (hc₁.crossed_eq_iff (one_mem _)).1 h1
  rw [mul_one] at e'
  calc s * u * s⁻¹ * u⁻¹ * t =
      s * u * s⁻¹ * u⁻¹ * ((s * u * s⁻¹ * u⁻¹)⁻¹ * t * (s * u * s⁻¹ * u⁻¹)) := by rw [e']
    _ = t * (s * u * s⁻¹ * u⁻¹) := by group

theorem S_le_centralizer_yamadaU₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.S ≤ centralizer (yamadaU₁ d t : Set G) := by
  refine hD.le_centralizer_of hK le_rfl (h.S_le_normalizer_yamadaU₁ d hK hD)
    (fun j hj => ?_) fun hp hu => h.commutator_mem_U_of_mem_S d hK hD hp hu
  have hjJ : j ∈ d.J := d.image_mono inf_le_left hj
  have : j ∈ L ⊓ normalizer (d.S : Set G) := by
    rw [(d.yamada_3_13_1_G).2.2]
    exact mem_sup_left hjJ
  exact this.2

omit [Finite K] in
theorem yamadaS₁_eq_sup (h : Setup G L f t) (d : G2Data L K) (_hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaS₁ d t = d.S ⊔ yamadaU₁ d t := by
  rw [yamadaS₁, hD.D₁_eq, ← sup_assoc,
    sup_eq_left.2 d.inclusions.2.2.2.2.2.2.2.1]

theorem yamada_5_11_1 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    yamadaS₁ d t ⊓ centralizer (yamadaS₁ d t : Set G) = yamadaU₁ d t := by
  obtain ⟨hU₁D₁, hUU₁, -⟩ := hD.spec
  have hS₁ := h.yamadaS₁_eq_sup d hK hD
  have hSU₁ := h.S_le_centralizer_yamadaU₁ d hK hD
  have hU₁Z : yamadaU₁ d t ≤ centralizer (yamadaS₁ d t : Set G) := by
    rw [← Subgroup.le_centralizer_iff, hS₁]
    refine sup_le hSU₁ fun x hx => mem_centralizer_iff.2 fun y hy => ?_
    exact hD.mul_comm hy hx
  refine le_antisymm (fun z hz => ?_) (le_inf (hS₁ ▸ le_sup_right) hU₁Z)
  obtain ⟨hz₁, hz₂⟩ := Subgroup.mem_inf.1 hz
  rw [hS₁] at hz₁
  obtain ⟨s, hs, u, hu, rfl⟩ := Common.exists_mul_of_le_normalizer'
    (h.S_le_normalizer_yamadaU₁ d hK hD) _ hz₁
  have hsZ : s ∈ d.S ⊓ centralizer (d.S : Set G) := by
    refine ⟨hs, mem_centralizer_iff.2 fun w hw => ?_⟩
    have hwS₁ : w ∈ yamadaS₁ d t := (le_sup_left : d.S ≤ yamadaS₁ d t) hw
    have h1 := mem_centralizer_iff.1 hz₂ w hwS₁
    have h2 := mem_centralizer_iff.1 (hU₁Z hu) w hwS₁
    calc w * s = w * (s * u) * u⁻¹ := by group
      _ = s * u * w * u⁻¹ := by rw [h1]
      _ = s * (u * w) * u⁻¹ := by group
      _ = s * (w * u) * u⁻¹ := by rw [h2]
      _ = s * w := by group
  rw [(d.yamada_3_12_centers).1] at hsZ
  exact mul_mem (hUU₁ hsZ) hu

theorem card_yamadaC₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    Nat.card (yamadaC₁ d t) = 2 * Nat.card (yamadaD₁ d t) := by
  have htN : zpowers t ≤ normalizer (yamadaD₁ d t : Set G) :=
    (zpowers_le).2 (h.yamadaC₁_le_normalizer_yamadaD₁ d hK (h.t_mem_yamadaC₁ d hK))
  have hinf : yamadaD₁ d t ⊓ zpowers t = ⊥ := by
    refine le_bot_iff.1 fun x hx => ?_
    obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx₂
    rcases h.zpow_eq_one_or_eq k with hk | hk
    · rw [hk]
      exact one_mem _
    · rw [hk] at hx₁
      exact absurd hx₁ (h.t_not_mem_yamadaD₁ d hK)
  have h1 := Common.card_sup_mul_card_inf_eq htN
  rw [← (h.yamada_5_8_1 d hK).2.1, hinf, Subgroup.card_bot, mul_one, h.card_zpowers_t] at h1
  rw [h1, mul_comm]

theorem card_le_two_mul_card_inf_yamadaD₁ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) {B : Subgroup G} (hB : B ≤ yamadaC₁ d t) :
    Nat.card B ≤ 2 * Nat.card (B ⊓ yamadaD₁ d t : Subgroup G) := by
  have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaD₁ d t) (B := B)
    (hB.trans (h.yamadaC₁_le_normalizer_yamadaD₁ d hK))
  have h2 : Nat.card (yamadaD₁ d t ⊔ B : Subgroup G) ≤ 2 * Nat.card (yamadaD₁ d t) := by
    rw [← h.card_yamadaC₁ d hK]
    exact Subgroup.card_le_of_le (sup_le (h.yamadaD₁_le_yamadaC₁ d hK) hB)
  have hpos : 0 < Nat.card (yamadaD₁ d t) := Nat.card_pos
  rw [inf_comm] at h1
  have h3 : Nat.card (yamadaD₁ d t) * Nat.card B ≤
      Nat.card (yamadaD₁ d t) * (2 * Nat.card (B ⊓ yamadaD₁ d t : Subgroup G)) := by
    rw [← h1]
    calc Nat.card (yamadaD₁ d t ⊔ B : Subgroup G) * Nat.card (B ⊓ yamadaD₁ d t : Subgroup G) ≤
        2 * Nat.card (yamadaD₁ d t) * Nat.card (B ⊓ yamadaD₁ d t : Subgroup G) :=
          Nat.mul_le_mul_right _ h2
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h3 hpos

theorem card_le_of_le_yamadaD₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {A : Subgroup G} (hAD : A ≤ yamadaD₁ d t)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : Nat.card A ≤ Nat.card K ^ 4 := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨hU₁D₁, hUU₁, -⟩ := hD.spec
  obtain ⟨hU₁Z, -⟩ := hD.yamada_5_10_3
  have hD₁ := hD.D₁_eq
  have hU₁c : ∀ {x y : G}, x ∈ yamadaD₁ d t → y ∈ yamadaU₁ d t → x * y = y * x :=
    fun {x y} hx hy => by
      rw [hU₁Z] at hy
      exact mem_centralizer_iff.1 hy.2 x hx
  have hUD : d.U ≤ d.D := d.inclusions.1.trans (d.inclusions.2.1.trans
    (d.inclusions.2.2.2.1.trans d.inclusions.2.2.2.2.2.1))
  have hA'c : ∀ x ∈ A ⊔ yamadaU₁ d t, ∀ y ∈ A ⊔ yamadaU₁ d t, x * y = y * x := by
    have : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext (hA a a.2 b b.2)⟩⟩
    have : IsMulCommutative (yamadaU₁ d t) :=
      ⟨⟨fun a b => Subtype.ext (hD.mul_comm a.2 b.2)⟩⟩
    have hc := isMulCommutative_sup (A := A) (B := yamadaU₁ d t) fun a ha b hb =>
      hU₁c (hAD ha) hb
    exact fun x hx y hy => congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : (A ⊔ yamadaU₁ d t :
      Subgroup G)) ⟨y, hy⟩)
  set A' := A ⊔ yamadaU₁ d t with hA'def
  set A'' := A' ⊓ d.D with hA''def
  have hA'D₁ : A' ≤ yamadaD₁ d t := sup_le hAD hU₁D₁
  have hU₁A' : yamadaU₁ d t ≤ A' := le_sup_right
  have hle : A' ≤ A'' ⊔ yamadaU₁ d t := by
    intro x hx
    have hx' := hA'D₁ hx
    rw [hD₁] at hx'
    obtain ⟨δ, hδ, u, hu, rfl⟩ := Common.exists_mul_of_le_normalizer
      (hU₁D₁.trans ((h.yamadaD₁_le_yamadaC₁ d hK).trans (h.yamadaC₁_le_normalizer_D d hK))) _ hx'
    have hδA' : δ ∈ A' := by
      have := mul_mem hx (inv_mem (hU₁A' hu))
      rwa [mul_inv_cancel_right] at this
    exact mul_mem (mem_sup_left ⟨hδA', hδ⟩) (mem_sup_right hu)
  have hN : yamadaU₁ d t ≤ normalizer (A'' : Set G) := fun u hu =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun x hx =>
      hA'c x hx.1 u (hU₁A' hu))
  have h1 := Common.card_sup_mul_card_inf_eq hN
  have h2 : Nat.card A'' ≤ Nat.card K ^ 3 :=
    d.yamada_3_17_4_G hK4 (Or.inl inf_le_right) fun x hx y hy => hA'c x hx.1 y hy.1
  have h3 : Nat.card d.U ≤ Nat.card (A'' ⊓ yamadaU₁ d t : Subgroup G) :=
    Subgroup.card_le_of_le (le_inf (le_inf ((hUU₁).trans hU₁A') hUD) hUU₁)
  rw [d.cards.1] at h3
  have hU₁card := (hD.yamada_5_10_1).2.2
  have hpos : 0 < Nat.card K := Nat.card_pos
  have h4 : Nat.card A' * Nat.card K ≤ Nat.card K ^ 4 * Nat.card K := by
    calc Nat.card A' * Nat.card K ≤
        Nat.card (A'' ⊔ yamadaU₁ d t : Subgroup G) * Nat.card (A'' ⊓ yamadaU₁ d t : Subgroup G) :=
          Nat.mul_le_mul (Subgroup.card_le_of_le hle) h3
      _ = Nat.card A'' * Nat.card (yamadaU₁ d t) := h1
      _ ≤ Nat.card K ^ 3 * Nat.card K ^ 2 := by rw [hU₁card]; exact Nat.mul_le_mul_right _ h2
      _ = Nat.card K ^ 4 * Nat.card K := by ring
  exact (Subgroup.card_le_of_le (le_sup_left : A ≤ A')).trans (Nat.le_of_mul_le_mul_right h4 hpos)

theorem card_le_of_not_le_yamadaD₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {B : Subgroup G} (hBC : B ≤ yamadaC₁ d t)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hBD : ¬ B ≤ yamadaD₁ d t) :
    Nat.card B ≤ 2 * Nat.card K ^ 3 := by
  obtain ⟨hU₁D₁, -, -⟩ := hD.spec
  obtain ⟨hU₁Z, -⟩ := hD.yamada_5_10_3
  have hU₁c : ∀ {x y : G}, x ∈ yamadaD₁ d t → y ∈ yamadaU₁ d t → x * y = y * x :=
    fun {x y} hx hy => by
      rw [hU₁Z] at hy
      exact mem_centralizer_iff.1 hy.2 x hx
  obtain ⟨b, hb, hbD⟩ := Set.not_subset.1 hBD
  have htN : zpowers t ≤ normalizer (yamadaD₁ d t : Set G) :=
    (zpowers_le).2 (h.yamadaC₁_le_normalizer_yamadaD₁ d hK (h.t_mem_yamadaC₁ d hK))
  have hbC := hBC hb
  rw [(h.yamada_5_8_1 d hK).2.1] at hbC
  obtain ⟨δ, hδ, τ, hτ, hbe⟩ := Common.exists_mul_of_le_normalizer htN b hbC
  have hτt : τ = t := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
    rcases h.zpow_eq_one_or_eq k with hk | hk
    · exfalso
      rw [hk, mul_one] at hbe
      exact hbD (hbe ▸ hδ)
    · exact hk
  have hBU : B ⊓ yamadaU₁ d t ≤ d.U := by
    intro x hx
    rw [← hD.inf_centralizer]
    refine ⟨hx.2, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : x * δ = δ * x := (hU₁c hδ hx.2).symm
    have h2 : x * b = b * x := hB x hx.1 b hb
    have ht : t = δ⁻¹ * b := by rw [hbe, hτt]; group
    have hxδ : x * δ⁻¹ = δ⁻¹ * x := by
      calc x * δ⁻¹ = δ⁻¹ * (δ * x) * δ⁻¹ := by group
        _ = δ⁻¹ * (x * δ) * δ⁻¹ := by rw [← h1]
        _ = δ⁻¹ * x := by group
    rw [ht]
    calc x * (δ⁻¹ * b) = (x * δ⁻¹) * b := by group
      _ = (δ⁻¹ * x) * b := by rw [hxδ]
      _ = δ⁻¹ * (x * b) := by group
      _ = δ⁻¹ * (b * x) := by rw [h2]
      _ = δ⁻¹ * b * x := by group
  set B' := B ⊓ yamadaD₁ d t with hB'def
  have hN : yamadaU₁ d t ≤ normalizer (B' : Set G) := fun u hu =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun x hx => hU₁c hx.2 hu)
  have h1 := Common.card_sup_mul_card_inf_eq hN
  have h2 : Nat.card (B' ⊔ yamadaU₁ d t : Subgroup G) ≤ Nat.card K ^ 4 := by
    refine h.card_le_of_le_yamadaD₁ d hK hD (sup_le inf_le_right hU₁D₁) ?_
    have : IsMulCommutative B' := ⟨⟨fun a b => Subtype.ext (hB a a.2.1 b b.2.1)⟩⟩
    have : IsMulCommutative (yamadaU₁ d t) :=
      ⟨⟨fun a b => Subtype.ext (hD.mul_comm a.2 b.2)⟩⟩
    have hc := isMulCommutative_sup (A := B') (B := yamadaU₁ d t) fun a ha b hb =>
      hU₁c ha.2 hb
    exact fun x hx y hy => congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : (B' ⊔ yamadaU₁ d t :
      Subgroup G)) ⟨y, hy⟩)
  have h3 : Nat.card (B' ⊓ yamadaU₁ d t : Subgroup G) ≤ Nat.card K := by
    rw [← d.cards.1]
    exact Subgroup.card_le_of_le ((inf_le_inf_right _ inf_le_left).trans hBU)
  have hU₁card := (hD.yamada_5_10_1).2.2
  have hpos : 0 < Nat.card K := Nat.card_pos
  have h4 : Nat.card B' * Nat.card (yamadaU₁ d t) ≤
      Nat.card K ^ 3 * Nat.card (yamadaU₁ d t) := by
    rw [← h1, hU₁card]
    calc Nat.card (B' ⊔ yamadaU₁ d t : Subgroup G) * Nat.card (B' ⊓ yamadaU₁ d t : Subgroup G) ≤
        Nat.card K ^ 4 * Nat.card K := Nat.mul_le_mul h2 h3
      _ = Nat.card K ^ 3 * Nat.card K ^ 2 := by ring
  have h5 := Nat.le_of_mul_le_mul_right h4 Nat.card_pos
  calc Nat.card B ≤ 2 * Nat.card B' := h.card_le_two_mul_card_inf_yamadaD₁ d hK hBC
    _ ≤ 2 * Nat.card K ^ 3 := Nat.mul_le_mul_left _ h5

theorem exists_abelian_yamadaD₁ (h : Setup G L f t) (d : G2Data L K) (_hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    ∃ A₁ A₂ : Subgroup G, A₁ ⊔ A₂ = yamadaD₁ d t ∧
      (A₁ ≤ yamadaD₁ d t ∧ (∀ x ∈ A₁, ∀ y ∈ A₁, x * y = y * x) ∧
        Nat.card A₁ = Nat.card K ^ 4) ∧
      (A₂ ≤ yamadaD₁ d t ∧ (∀ x ∈ A₂, ∀ y ∈ A₂, x * y = y * x) ∧
        Nat.card A₂ = Nat.card K ^ 4) := by
  obtain ⟨hU₁D₁, hUU₁, hU₁D⟩ := hD.spec
  obtain ⟨hDW, hWaD⟩ := d.D_eq_W_sup_map_wa
  obtain ⟨hUY, -, hYW, -, hWF, hFD, -⟩ := d.inclusions
  have hDU₁ := hD.D_le_centralizer
  have hD₁ := hD.D₁_eq
  have hU₁card := (hD.yamada_5_10_1).2.2
  have hDD₁ : d.D ≤ yamadaD₁ d t := le_sup_right
  have hwaU : d.U.map (MulAut.conj d.wa).toMonoidHom = d.U :=
    map_conj_eq_of_mem_normalizer d.wa_mem_inf_normalizer_U.2
  have key : ∀ E : Subgroup G, E ≤ d.D → d.U ≤ E → CFSG.IsElementaryAbelian 2 E →
      Nat.card E = Nat.card K ^ 3 →
      E ⊔ yamadaU₁ d t ≤ yamadaD₁ d t ∧
        (∀ x ∈ E ⊔ yamadaU₁ d t, ∀ y ∈ E ⊔ yamadaU₁ d t, x * y = y * x) ∧
        Nat.card (E ⊔ yamadaU₁ d t : Subgroup G) = Nat.card K ^ 4 := by
    intro E hED hUE hE hEc
    have : IsMulCommutative E := hE.toIsMulCommutative
    have : IsMulCommutative (yamadaU₁ d t) :=
      ⟨⟨fun a b => Subtype.ext (hD.mul_comm a.2 b.2)⟩⟩
    have hc := isMulCommutative_sup (A := E) (B := yamadaU₁ d t) fun a ha b hb =>
      (mem_centralizer_iff.1 (hDU₁ (hED ha)) b hb).symm
    refine ⟨sup_le (hED.trans hDD₁) hU₁D₁, fun x hx y hy => congrArg Subtype.val
      (mul_comm' (⟨x, hx⟩ : (E ⊔ yamadaU₁ d t : Subgroup G)) ⟨y, hy⟩), ?_⟩
    have hN : yamadaU₁ d t ≤ normalizer (E : Set G) := fun u hu =>
      Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun x hx =>
        mem_centralizer_iff.1 (hDU₁ (hED hx)) u hu |>.symm)
    have h1 := Common.card_sup_mul_card_inf_eq hN
    have hinf : E ⊓ yamadaU₁ d t = d.U := le_antisymm
      (by rw [← hU₁D]; exact fun x hx => ⟨hx.2, hED hx.1⟩) (le_inf hUE hUU₁)
    rw [hinf, d.cards.1, hEc, hU₁card] at h1
    have hpos : 0 < Nat.card K := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans (by ring))
  have hUW : d.U ≤ d.W := hUY.trans hYW
  refine ⟨d.W ⊔ yamadaU₁ d t, d.W.map (MulAut.conj d.wa).toMonoidHom ⊔ yamadaU₁ d t, ?_,
    key _ (hWF.trans hFD) hUW d.isElementaryAbelian.2.2.2 d.cards.2.2.2.1,
    key _ hWaD (hwaU ▸ map_mono hUW) (isElementaryAbelian_map_conj d.isElementaryAbelian.2.2.2 _)
      (by rw [card_map_conj, d.cards.2.2.2.1])⟩
  rw [hD₁, hDW]
  apply le_antisymm
  · exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  · exact sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right))
      (le_sup_right.trans le_sup_left)

theorem yamada_5_11_2 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : CFSG.Open.thompsonSubgroup (yamadaC₁ d t) = yamadaD₁ d t := by
  have hD₁C₁ := h.yamadaD₁_le_yamadaC₁ d hK
  have hq : 2 * Nat.card K ^ 3 < Nat.card K ^ 4 := by
    have : 2 < Nat.card K := by have := hK ▸ h.four_le; omega
    calc 2 * Nat.card K ^ 3 < Nat.card K * Nat.card K ^ 3 :=
          Nat.mul_lt_mul_of_pos_right this (by positivity)
      _ = Nat.card K ^ 4 := by ring
  have hcomm : ∀ {A : Subgroup G}, IsMulCommutative A → ∀ x ∈ A, ∀ y ∈ A, x * y = y * x :=
    fun {A} _ x hx y hy => congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hmax : ∀ B : Subgroup G, B ≤ yamadaC₁ d t → IsMulCommutative B →
      Nat.card B ≤ Nat.card K ^ 4 := fun B hB hBc => by
    by_cases hBD : B ≤ yamadaD₁ d t
    · exact h.card_le_of_le_yamadaD₁ d hK hD hBD (hcomm hBc)
    · exact (h.card_le_of_not_le_yamadaD₁ d hK hD hB (hcomm hBc) hBD).trans hq.le
  obtain ⟨A₁, A₂, hA, ⟨hA₁D, hA₁c, hA₁card⟩, ⟨hA₂D, hA₂c, hA₂card⟩⟩ :=
    h.exists_abelian_yamadaD₁ d hK hD
  rw [CFSG.Open.thompsonSubgroup_eq_iSup]
  have hmem : ∀ {A : Subgroup G}, A ≤ yamadaD₁ d t → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
      Nat.card A = Nat.card K ^ 4 →
      A ≤ ⨆ (A' : Subgroup G) (_ : A' ≤ yamadaC₁ d t) (_ : IsMulCommutative A')
        (_ : ∀ B : Subgroup G, B ≤ yamadaC₁ d t → IsMulCommutative B →
          Nat.card B ≤ Nat.card A'), A' := by
    intro A hAD hAc hAcard
    have hAc' : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext (hAc a a.2 b b.2)⟩⟩
    have hAm : ∀ B : Subgroup G, B ≤ yamadaC₁ d t → IsMulCommutative B →
        Nat.card B ≤ Nat.card A := fun B hB hBc => (hmax B hB hBc).trans hAcard.ge
    exact le_iSup_of_le A (le_iSup_of_le (hAD.trans hD₁C₁) (le_iSup_of_le hAc'
      (le_iSup_of_le hAm le_rfl)))
  refine le_antisymm (iSup_le fun A => iSup_le fun hAC => iSup_le fun hAc =>
    iSup_le fun hAm => ?_) ?_
  swap
  · rw [← hA]
    exact sup_le (hmem hA₁D hA₁c hA₁card) (hmem hA₂D hA₂c hA₂card)
  by_contra hAD
  have h1 := hAm A₁ (hA₁D.trans hD₁C₁) ⟨⟨fun a b => Subtype.ext (hA₁c a a.2 b b.2)⟩⟩
  have h2 := h.card_le_of_not_le_yamadaD₁ d hK hD hAC (hcomm hAc) hAD
  rw [hA₁card] at h1
  omega

theorem yamadaC₁_inf_S (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    yamadaC₁ d t ⊓ d.S = d.D := by
  obtain ⟨-, hC₁t, -, -⟩ := h.two_core_C₁ d hK
  refine le_antisymm (fun x hx => ?_) (le_inf (le_sup_left.trans (h.tD_le_yamadaC₁ d hK))
    d.inclusions.2.2.2.2.2.2.2.1)
  obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
  exact h.mem_D_of_mem_sup d (by
    rw [← hC₁t]
    exact ⟨hx₁, h.S_le_centralizer d hx₂⟩) (d.image_le _ hx₂)

theorem tM_le_yamadaL₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    d.M ⊔ zpowers t ≤ yamadaL₁ d t :=
  le_inf (h.tM_le_yamadaL₂ d hK) (sup_le (d.inclusions.2.2.2.2.2.2.2.2.1.trans le_sup_right)
    ((zpowers_le).2 (mem_sup_left (h.t_mem_yamadaC₁ d hK))))

theorem yamadaL₁_eq_sup (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaL₁ d t = (d.M ⊔ zpowers t) ⊔ yamadaU₁ d t := by
  obtain ⟨-, hL₂t, -, -⟩ := h.two_core_L₂ d hK
  obtain ⟨hU₁D₁, -, -⟩ := hD.spec
  have hU₁C₁ : yamadaU₁ d t ≤ yamadaC₁ d t := hU₁D₁.trans (h.yamadaD₁_le_yamadaC₁ d hK)
  have hU₁L₂ : yamadaU₁ d t ≤ yamadaL₂ d t := fun x hx => ((hD.yamada_5_10_3).2 hx).1.1
  have hU₁L₁ : yamadaU₁ d t ≤ yamadaL₁ d t := fun x hx => ⟨hU₁L₂ hx, mem_sup_left (hU₁C₁ hx)⟩
  refine le_antisymm (fun x hx => ?_) (sup_le (h.tM_le_yamadaL₁ d hK) hU₁L₁)
  obtain ⟨hxL₂, hxR₁⟩ := Subgroup.mem_inf.1 hx
  have hxU := (h.mem_yamadaR₁_iff d hK (mem_sup_left hxL₂)).1 hxR₁
  obtain ⟨u, hu, hut⟩ := hD.exists_mem_crossed hK hxU
  have e : x⁻¹ * t * x = u⁻¹ * t * u := mul_right_cancel hut.symm
  have hC := Common.mul_inv_mem_centralizer_of_conj_eq e
  have hm : u * x⁻¹ ∈ d.M ⊔ zpowers t := by
    rw [← hL₂t]
    exact Subgroup.mem_inf.2 ⟨mul_mem (hU₁L₂ hu) (inv_mem hxL₂), hC⟩
  rw [show x = (u * x⁻¹)⁻¹ * u by group]
  exact mul_mem (mem_sup_left (inv_mem hm)) (mem_sup_right hu)

theorem yamadaR₁_eq_sup (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    yamadaR₁ d t = (d.S ⊔ zpowers t) ⊔ yamadaU₁ d t ∧
      d.S ⊔ zpowers t ≤ normalizer (yamadaU₁ d t : Set G) := by
  obtain ⟨hU₁D₁, -, -⟩ := hD.spec
  have hU₁C₁ : yamadaU₁ d t ≤ yamadaC₁ d t := hU₁D₁.trans (h.yamadaD₁_le_yamadaC₁ d hK)
  have htC₁ := h.t_mem_yamadaC₁ d hK
  refine ⟨le_antisymm (sup_le ?_ (le_sup_left.trans le_sup_left)) (sup_le (sup_le le_sup_right
    ((zpowers_le).2 (mem_sup_left htC₁))) (hU₁C₁.trans le_sup_left)),
    sup_le (h.S_le_normalizer_yamadaU₁ d hK hD)
      ((zpowers_le).2 (hD.yamadaC₁_le_normalizer hK htC₁))⟩
  rw [(h.yamada_5_8_1 d hK).2.1, hD.D₁_eq]
  exact sup_le (sup_le ((d.inclusions.2.2.2.2.2.2.2.1.trans le_sup_left).trans le_sup_left)
    le_sup_right) (le_sup_right.trans le_sup_left)

theorem mem_or_mem_of_mul_self_mem_Y (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {x : G} (hx : x ∈ yamadaR₁ d t)
    (hxx : x * x ∈ d.Y) : x ∈ yamadaL₁ d t ∨ x ∈ yamadaC₁ d t := by
  obtain ⟨hR₁, hRN⟩ := h.yamadaR₁_eq_sup d hK hD
  obtain ⟨hU₁D₁, hUU₁, -⟩ := hD.spec
  obtain ⟨hUY, hYX, -, hXF, -, hFD, -, hDS, -, -⟩ := d.inclusions
  have hYS : d.Y ≤ d.S := hYX.trans (hXF.trans (hFD.trans hDS))
  have hU₁C₁ : yamadaU₁ d t ≤ yamadaC₁ d t := hU₁D₁.trans (h.yamadaD₁_le_yamadaC₁ d hK)
  rw [hR₁] at hx
  obtain ⟨r, hr, u, hu, rfl⟩ := Common.exists_mul_of_le_normalizer' hRN x hx
  have hrN := hRN hr
  have hru : r⁻¹ * u * r ∈ yamadaU₁ d t := by
    have := (mem_normalizer_iff.1 (inv_mem hrN) u).1 hu
    rwa [inv_inv] at this
  have hrr : r * r ∈ d.Y := by
    have e : r * r = (r * u * (r * u)) * (r⁻¹ * u * r * u)⁻¹ := by group
    have hv : (r * u * (r * u))⁻¹ * (r * r) ∈ d.U := by
      rw [← hD.inf_centralizer]
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [e, show (r * u * (r * u))⁻¹ * ((r * u * (r * u)) * (r⁻¹ * u * r * u)⁻¹) =
          (r⁻¹ * u * r * u)⁻¹ by group]
        exact inv_mem (mul_mem hru hu)
      · have hRC : d.S ⊔ zpowers t ≤ centralizer ({t} : Set G) := by
          rw [← h.yamadaR_eq d]
          exact h.yamadaR_le_centralizer d
        exact mul_mem (inv_mem (((hYS.trans le_sup_left).trans hRC) hxx))
          (mul_mem (hRC hr) (hRC hr))
    have := mul_mem hxx (hUY hv)
    rwa [mul_inv_cancel_left] at this
  have htS : zpowers t ≤ normalizer (d.S : Set G) := (zpowers_le).2
    (Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun s hs =>
      mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs)))
  obtain ⟨s, hs, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer htS r hr
  have hτs : s * τ = τ * s := commute_of_mem_zpowers hτ (h.S_le_centralizer d hs)
  have hττ : τ * τ = 1 := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
    rcases h.zpow_eq_one_or_eq k with hk | hk <;> rw [hk]
    · rw [mul_one]
    · exact h.t_mul_t
  have hss : s * s ∈ d.Y := by
    rw [show s * s = s * τ * (s * τ) by
      rw [show s * τ * (s * τ) = s * (τ * s) * τ by group, ← hτs,
        show s * (s * τ) * τ = s * s * (τ * τ) by group, hττ, mul_one]]
    exact hrr
  rcases d.mem_D_or_M_of_mul_self_mem hs hss with hsD | hsM
  · right
    exact mul_mem (h.tD_le_yamadaC₁ d hK (mul_mem (mem_sup_left hsD) (mem_sup_right hτ)))
      (hU₁C₁ hu)
  · left
    rw [h.yamadaL₁_eq_sup d hK hD]
    exact mul_mem (mem_sup_left (mul_mem (mem_sup_left hsM) (mem_sup_right hτ)))
      (mem_sup_right hu)

theorem elemModulo_Y (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    ElemModulo d.Y (yamadaL₁ d t) ∧ ElemModulo d.Y (yamadaC₁ d t) := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨hC₁U, -, -, -⟩ := h.two_core_C₁ d hK
  obtain ⟨hL₂Y, -, -, -⟩ := h.two_core_L₂ d hK
  obtain ⟨hU₁D₁, hUU₁, -⟩ := hD.spec
  obtain ⟨hUY, -, -, -, -, -, -, -, hMS, -⟩ := d.inclusions
  have hU₁C₁ : yamadaU₁ d t ≤ yamadaC₁ d t := hU₁D₁.trans (h.yamadaD₁_le_yamadaC₁ d hK)
  have hc₁ := h.cosetData_tU d hK
  have hEU := h.elemModulo_U_yamadaC₁ d hK
  refine ⟨elemModulo_of_mul_self_mem
    ((inf_le_left.trans hL₂Y).trans (Subgroup.centralizer_le_normalizer _)) fun x hx => ?_,
    fun x hx y hy => ⟨hUY (hEU x hx y hy).1, hUY (hEU x hx y hy).2⟩⟩
  have htU₁ : zpowers t ≤ normalizer (yamadaU₁ d t : Set G) :=
    (zpowers_le).2 (hD.yamadaC₁_le_normalizer hK (h.t_mem_yamadaC₁ d hK))
  have hMU₁ : d.M ≤ centralizer (yamadaU₁ d t : Set G) :=
    hMS.trans (h.S_le_centralizer_yamadaU₁ d hK hD)
  have hmN : d.M ⊔ zpowers t ≤ normalizer (yamadaU₁ d t : Set G) :=
    sup_le (hMU₁.trans (Subgroup.centralizer_le_normalizer _)) htU₁
  rw [h.yamadaL₁_eq_sup d hK hD] at hx
  obtain ⟨m, hm, u, hu, rfl⟩ := Common.exists_mul_of_le_normalizer' hmN x hx
  have htM : zpowers t ≤ normalizer (d.M : Set G) := (zpowers_le).2
    (Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun s hs =>
      mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hs))))
  obtain ⟨μ, hμ, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer htM m hm
  have hμt : μ * τ = τ * μ := commute_of_mem_zpowers hτ (h.L_le_centralizer (d.image_le _ hμ))
  have hττ : τ * τ = 1 := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
    rcases h.zpow_eq_one_or_eq k with hk | hk <;> rw [hk]
    · rw [mul_one]
    · exact h.t_mul_t
  have hμu : μ * u = u * μ := mem_centralizer_iff.1 (hMU₁ hμ) u hu |>.symm
  have hτu : ∃ w ∈ d.U, τ * u * τ⁻¹ = u * w := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
    rcases h.zpow_eq_one_or_eq k with hk | hk <;> rw [hk]
    · exact ⟨1, one_mem _, by group⟩
    · refine ⟨u⁻¹ * t * u * t, hc₁.crossed_mem_of_mem ⟨yamadaC₁_le d t (hU₁C₁ hu),
        hC₁U (hU₁C₁ hu)⟩, ?_⟩
      rw [show t⁻¹ = t from inv_eq_of_mul_eq_one_right h.t_mul_t]
      group
  obtain ⟨w, hw, hwe⟩ := hτu
  have hμμ : μ * μ ∈ d.Y := by
    have h1 : μ ^ 2 ∈ closure {z | ∃ g ∈ d.M, z = g ^ 2} := subset_closure ⟨μ, hμ, rfl⟩
    rwa [(d.yamada_3_12_mho hK4).2.1, sq] at h1
  have huu : u * u ∈ d.U := ((hEU u (hU₁C₁ hu) u (hU₁C₁ hu)).1)
  have hwu : w * u = u * w := mem_centralizer_iff.1 (hC₁U (hU₁C₁ hu)) w hw
  have e : μ * τ * u * (μ * τ * u) = (μ * μ) * ((u * u) * w) := by
    calc μ * τ * u * (μ * τ * u) = μ * (τ * u * τ⁻¹) * (τ * μ) * τ * u := by group
      _ = μ * (u * w) * (μ * τ) * τ * u := by rw [hwe, ← hμt]
      _ = μ * u * w * μ * (τ * τ) * u := by group
      _ = μ * u * w * μ * u := by rw [hττ]; group
      _ = μ * (u * w) * (μ * u) := by group
      _ = μ * (u * w) * (u * μ) := by rw [hμu]
      _ = μ * (u * (w * u)) * μ := by group
      _ = μ * (u * (u * w)) * μ := by rw [hwu]
      _ = μ * ((u * u) * w) * μ := by group
      _ = μ * μ * ((u * u) * w) := by
          rw [mul_assoc μ ((u * u) * w) μ, mem_centralizer_iff.1 (hMU₁ hμ) _
            (hUU₁ (mul_mem huu hw)), ← mul_assoc]
  rw [e]
  exact mul_mem hμμ (mul_mem (hUY huu) (hUY hw))

theorem yamada_5_11_3 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) (E : Subgroup G) :
    Maximal (fun E' : Subgroup G => d.Y ≤ E' ∧ E' ≤ yamadaR₁ d t ∧ ElemModulo d.Y E') E ↔
      E = yamadaL₁ d t ∨ E = yamadaC₁ d t := by
  obtain ⟨-, hL₂t, -, -⟩ := h.two_core_L₂ d hK
  obtain ⟨hUY, hYX, -, hXF, -, hFD, hFM, hDS, hMS, -⟩ := d.inclusions
  obtain ⟨hEL, hEC⟩ := h.elemModulo_Y d hK hD
  have hYM : d.Y ≤ d.M := hYX.trans (hXF.trans hFM)
  have hYD : d.Y ≤ d.D := hYX.trans (hXF.trans hFD)
  have hL₁R₁ : yamadaL₁ d t ≤ yamadaR₁ d t := inf_le_right
  have hC₁R₁ : yamadaC₁ d t ≤ yamadaR₁ d t := le_sup_left
  have key : ∀ E' : Subgroup G, E' ≤ yamadaR₁ d t → ElemModulo d.Y E' →
      E' ≤ yamadaL₁ d t ∨ E' ≤ yamadaC₁ d t := fun E' hE'R hE' =>
    le_or_le_of_subset_union fun x hx =>
      h.mem_or_mem_of_mul_self_mem_Y d hK hD (hE'R hx) (hE' x hx x hx).1
  have hL : d.Y ≤ yamadaL₁ d t ∧ yamadaL₁ d t ≤ yamadaR₁ d t ∧ ElemModulo d.Y (yamadaL₁ d t) :=
    ⟨(hYM.trans le_sup_left).trans (h.tM_le_yamadaL₁ d hK), hL₁R₁, hEL⟩
  have hC : d.Y ≤ yamadaC₁ d t ∧ yamadaC₁ d t ≤ yamadaR₁ d t ∧ ElemModulo d.Y (yamadaC₁ d t) :=
    ⟨(hYD.trans le_sup_left).trans (h.tD_le_yamadaC₁ d hK), hC₁R₁, hEC⟩
  have hne1 : ¬ yamadaL₁ d t ≤ yamadaC₁ d t := by
    intro hle
    refine d.not_M_le_D ?_
    rw [← h.yamadaC₁_inf_S d hK]
    exact le_inf ((le_sup_left.trans (h.tM_le_yamadaL₁ d hK)).trans hle) hMS
  have hne2 : ¬ yamadaC₁ d t ≤ yamadaL₁ d t := by
    intro hle
    refine d.not_D_le_M fun x hxD => ?_
    have hxB : x ∈ d.M ⊔ zpowers t := by
      rw [← hL₂t]
      exact ⟨(hle (le_sup_left.trans (h.tD_le_yamadaC₁ d hK) hxD)).1,
        h.S_le_centralizer d (hDS hxD)⟩
    rcases (h.mem_sup_zpowers_iff (d.image_le _)).1 hxB with h1 | h1
    · exact h1
    · exfalso
      refine h.t_not_mem_L ?_
      have := mul_mem (d.image_le _ h1) (inv_mem (d.image_le _ hxD))
      rwa [mul_inv_cancel_right] at this
  constructor
  · rintro ⟨⟨-, hER, hE⟩, hmax⟩
    rcases key E hER hE with h' | h'
    · exact Or.inl (le_antisymm h' (hmax hL h'))
    · exact Or.inr (le_antisymm h' (hmax hC h'))
  · rintro (rfl | rfl)
    · refine ⟨hL, fun E' hE' hLE' => ?_⟩
      rcases key E' hE'.2.1 hE'.2.2 with h' | h'
      · exact h'
      · exact absurd (hLE'.trans h') hne1
    · refine ⟨hC, fun E' hE' hCE' => ?_⟩
      rcases key E' hE'.2.1 hE'.2.2 with h' | h'
      · exact absurd (hCE'.trans h') hne2
      · exact h'

theorem yamada_5_11_4 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    ((yamadaL₁ d t).subgroupOf (yamadaR₁ d t)).Characteristic ∧
      ((yamadaC₁ d t).subgroupOf (yamadaR₁ d t)).Characteristic := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨hUY, hYX, -, hXF, -, hFD, hFM, hDS, hMS, -⟩ := d.inclusions
  have hSR₁ : d.S ≤ yamadaR₁ d t := le_sup_right
  have hFR₁ : d.F ≤ yamadaR₁ d t := (hFD.trans hDS).trans hSR₁
  have hYF : d.Y ≤ d.F := hYX.trans hXF
  have hL₁R₁ : yamadaL₁ d t ≤ yamadaR₁ d t := inf_le_right
  have hC₁R₁ : yamadaC₁ d t ≤ yamadaR₁ d t := le_sup_left
  have hY : ∀ φ : yamadaR₁ d t ≃* yamadaR₁ d t, autImage φ d.Y = d.Y := by
    intro φ
    have hF : autImage φ d.F = d.F := by
      rw [← (h.yamada_5_8_2 d hK).1, autImage_closure_sq φ le_rfl, autImage_self]
    rw [← (d.yamada_3_12_centers).2.2.2, autImage_inf_centralizer φ hFR₁, hF]
  set P : Subgroup G → Prop := fun E' => d.Y ≤ E' ∧ E' ≤ yamadaR₁ d t ∧ ElemModulo d.Y E'
    with hPdef
  have hP : ∀ (φ : yamadaR₁ d t ≃* yamadaR₁ d t) {E : Subgroup G}, P E → P (autImage φ E) := by
    rintro φ E ⟨hYE, hER, hEm⟩
    refine ⟨(hY φ).symm.le.trans (autImage_mono φ hYE), autImage_le φ E, ?_⟩
    have := elemModulo_autImage φ hEm
    rwa [hY φ] at this
  have hmax : ∀ (φ : yamadaR₁ d t ≃* yamadaR₁ d t) {E : Subgroup G}, Maximal P E →
      Maximal P (autImage φ E) := by
    rintro φ E ⟨hE, hEm⟩
    refine ⟨hP φ hE, fun E'' hE'' hle => ?_⟩
    have h1 : E ≤ autImage φ.symm E'' := by
      rw [← autImage_symm φ hE.2.1]
      exact autImage_mono φ.symm hle
    have h2 := hEm (hP φ.symm hE'') h1
    have h3 := autImage_symm φ.symm hE''.2.1
    rw [MulEquiv.symm_symm] at h3
    rw [← h3]
    exact autImage_mono φ h2
  have hL₁m : Maximal P (yamadaL₁ d t) := (h.yamada_5_11_3 d hK hD _).2 (Or.inl rfl)
  have hC₁m : Maximal P (yamadaC₁ d t) := (h.yamada_5_11_3 d hK hD _).2 (Or.inr rfl)
  have hYL₁ : d.Y ≤ closure {z | ∃ g ∈ yamadaL₁ d t, z = g ^ 2} := by
    rw [← (d.yamada_3_12_mho hK4).2.1]
    exact closure_mono fun z ⟨g, hg, e⟩ =>
      ⟨g, (le_sup_left.trans (h.tM_le_yamadaL₁ d hK)) hg, e⟩
  have hYU : ¬ d.Y ≤ d.U := by
    intro hYU
    have h1 := Subgroup.card_le_of_le hYU
    rw [d.cards.1, d.cards.2.1] at h1
    have h2 : 1 < Nat.card K := by omega
    nlinarith
  have hL₁C₁ : yamadaL₁ d t ≠ yamadaC₁ d t := by
    intro e
    refine d.not_M_le_D ?_
    rw [← h.yamadaC₁_inf_S d hK, ← e]
    exact le_inf (le_sup_left.trans (h.tM_le_yamadaL₁ d hK)) hMS
  have hL₁φ : ∀ φ : yamadaR₁ d t ≃* yamadaR₁ d t, autImage φ (yamadaL₁ d t) = yamadaL₁ d t := by
    intro φ
    rcases (h.yamada_5_11_3 d hK hD _).1 (hmax φ hL₁m) with e | e
    · exact e
    · exfalso
      refine hYU ?_
      rw [← h.yamada_5_6_4 d hK, ← e, ← autImage_closure_sq φ hL₁R₁, ← hY φ]
      exact autImage_mono φ hYL₁
  refine ⟨characteristic_of_autImage hL₁φ, characteristic_of_autImage fun φ => ?_⟩
  rcases (h.yamada_5_11_3 d hK hD _).1 (hmax φ hC₁m) with e | e
  · exfalso
    exact hL₁C₁ (autImage_injective φ hL₁R₁ hC₁R₁ ((hL₁φ φ).trans e.symm))
  · exact e

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
