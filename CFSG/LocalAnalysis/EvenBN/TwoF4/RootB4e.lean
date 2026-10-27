module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootB4d

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open scoped commutatorElement

section Model

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem sylowVec_eq_of_mem_S4 (hK : Nat.card K = 2 ^ (2 * a + 1)) {x : Fin 12 → K}
    (hx : ∀ n ∈ ({0, 1, 3} : Finset (Fin 12)), x n = 0) :
    sylowVec a K x = rootElt K a .i2 (x 2) * rootElt K a .i8 (x 4) * rootElt K a .i6 (x 5) *
      rootElt K a .i11 (x 6) * rootElt K a .i5 (x 7) * (rootElt K a .i12 (x 8) *
        rootElt K a .i7 (x 9) * rootElt K a .i9 (x 10) * rootElt K a .i10 (x 11)) := by
  rw [sylowVec_eq_prod_rootElt hK, hx 0 (by decide), hx 1 (by decide), hx 3 (by decide)]
  simp only [rootElt_zero, one_mul, mul_assoc]

end Model

variable {G : Type} [Group G] [Finite G]

namespace Setup

variable (h : Setup G)

theorem exists_mul_of_mem_S₄ {x : G} (hx : x ∈ h.S₄) :
    ∃ c₂ c₈ c₆ c₁₁ c₅ : h.K, ∃ u ∈ h.S₃, x = h.elt (rootElt h.K h.a .i2 c₂) *
      h.elt (rootElt h.K h.a .i8 c₈) * h.elt (rootElt h.K h.a .i6 c₆) *
        h.elt (rootElt h.K h.a .i11 c₁₁) * h.elt (rootElt h.K h.a .i5 c₅) * u := by
  obtain ⟨g, hg, hgΓ, rfl⟩ := (h.mem_pull_iff_elt).1 hx
  have hg' : g ∈ (S4 h.K h.a : Set (ModGL F4.tag h.K)) := hg
  rw [(S4_spec h.card_K).2.1] at hg'
  obtain ⟨y, hy, rfl⟩ := hg'
  have hΓ : ∀ k c, rootElt h.K h.a k c ∈ F4.reeGamma h.K h.a := fun k c =>
    rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _)
  have h3 : ∀ k ∈ ({.i7, .i9, .i10, .i11, .i12} : Finset Idx), ∀ c,
      rootElt h.K h.a k c ∈ S3 h.K h.a := fun k hk c =>
    rootV_le_rootJoin hk (rootElt_mem_rootV _ _)
  have hu : rootElt h.K h.a .i12 (y 8) * rootElt h.K h.a .i7 (y 9) *
      rootElt h.K h.a .i9 (y 10) * rootElt h.K h.a .i10 (y 11) ∈ S3 h.K h.a :=
    mul_mem (mul_mem (mul_mem (h3 _ (by decide) _) (h3 _ (by decide) _)) (h3 _ (by decide) _))
      (h3 _ (by decide) _)
  refine ⟨y 2, y 4, y 5, y 6, y 7, _, (h.elt_mem_pull (h.S3_le_reeGamma hu)).2 hu, ?_⟩
  rw [sylowVec_eq_of_mem_S4 h.card_K hy,
    h.elt_mul' (mul_mem (mul_mem (mul_mem (mul_mem (hΓ _ _) (hΓ _ _)) (hΓ _ _)) (hΓ _ _))
      (hΓ _ _)) (h.S3_le_reeGamma hu),
    h.elt_mul' (mul_mem (mul_mem (mul_mem (hΓ _ _) (hΓ _ _)) (hΓ _ _)) (hΓ _ _)) (hΓ _ _),
    h.elt_mul' (mul_mem (mul_mem (hΓ _ _) (hΓ _ _)) (hΓ _ _)) (hΓ _ _),
    h.elt_mul' (mul_mem (hΓ _ _) (hΓ _ _)) (hΓ _ _), h.elt_mul' (hΓ _ _) (hΓ _ _)]

theorem r1c_ten_elt (c d e : h.K) :
    h.r1c (h.elt (rootElt h.K h.a .i10 c * rootElt h.K h.a .i11 d *
      rootElt h.K h.a .i12 e)) .i10 = c := by
  have hΓ : ∀ k c, rootElt h.K h.a k c ∈ F4.reeGamma h.K h.a := fun k c =>
    rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _)
  have hR : ∀ k ∈ ({.i8, .i9, .i10, .i11, .i12} : Finset Idx), ∀ c,
      h.elt (rootElt h.K h.a k c) ∈ h.R₁ := fun k hk c =>
    h.V_le_R₁ hk (h.elt_rootElt_mem_V k c)
  rw [h.elt_mul' (mul_mem (hΓ _ _) (hΓ _ _)) (hΓ _ _), h.elt_mul' (hΓ _ _) (hΓ _ _),
    h.r1c_mul (mul_mem (hR _ (by decide) _) (hR _ (by decide) _)) (hR _ (by decide) _) rfl,
    h.r1c_mul (hR _ (by decide) _) (hR _ (by decide) _) rfl, h.r1c_elt_rootElt rfl _ rfl,
    h.r1c_elt_rootElt rfl _ rfl, h.r1c_elt_rootElt rfl _ rfl, Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide), Pi.single_eq_of_ne (by decide), add_zero, add_zero]

theorem mem_S₃_of_comm_mem_S₁ {x : G} (hx : x ∈ h.S₄) (hc : ∀ y ∈ h.S₄, ⁅x, y⁆ ∈ h.S₁) :
    x ∈ h.S₃ := by
  obtain ⟨c₂, c₈, c₆, c₁₁, c₅, u, hu, rfl⟩ := h.exists_mul_of_mem_S₄ hx
  have hΓ : ∀ k c, rootElt h.K h.a k c ∈ F4.reeGamma h.K h.a := fun k c =>
    rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _)
  have hS4 : ∀ (k : Idx), k ∈ ({.i2, .i5, .i6, .i8, .i7, .i9, .i10, .i11, .i12} : Finset Idx) →
      ∀ c, h.elt (rootElt h.K h.a k c) ∈ h.S₄ := fun k hk c =>
    h.V_le_S₄ hk (h.elt_rootElt_mem_V k c)
  have hu4 : u ∈ h.S₄ := h.S₂_le_S₃_le_S₄_le_S.2.1 hu
  have hadd : ∀ {w w' y : G}, w ∈ h.S₄ → w' ∈ h.S₄ → y ∈ h.S₄ →
      h.r1c ⁅w * w', y⁆ .i10 = h.r1c ⁅w, y⁆ .i10 + h.r1c ⁅w', y⁆ .i10 := by
    intro w w' y hw hw' hy
    have h1 := h.comm_S₄_S₄_mem hw hy
    have h2 := h.comm_S₄_S₄_mem hw' hy
    rw [commutatorElement_mul_left_eq, mem_centralizer_iff.1 (h.S₂_le_centralizer_S₄ h2) w hw,
      mul_inv_cancel_right, h.r1c_mul (h.S₂_le_R₁ h2) (h.S₂_le_R₁ h1) rfl, add_comm]
  have hzero : ∀ {w y : G}, w ∈ h.S₃ → y ∈ h.S₄ → h.r1c ⁅w, y⁆ .i10 = 0 := by
    intro w y hw hy
    have h1 : ⁅w, y⁆ ∈ h.pull (rootJoin h.K h.a {.i11, .i12}) := by
      rw [← commutatorElement_inv]
      exact inv_mem (h.comm_S₄_S₃_mem hy hw)
    exact h.r1c_eq_zero_of_mem (by decide) h1 rfl (by decide)
  have hA := hS4 .i2 (by decide) c₂
  have hB := hS4 .i8 (by decide) c₈
  have hC := hS4 .i6 (by decide) c₆
  have hD := hS4 .i11 (by decide) c₁₁
  have hE := hS4 .i5 (by decide) c₅
  have hD3 : h.elt (rootElt h.K h.a .i11 c₁₁) ∈ h.S₃ :=
    h.V_le_S₃ (by decide) (h.elt_rootElt_mem_V .i11 c₁₁)
  have hsum : ∀ {y : G}, y ∈ h.S₄ → h.r1c ⁅h.elt (rootElt h.K h.a .i2 c₂) *
      h.elt (rootElt h.K h.a .i8 c₈) * h.elt (rootElt h.K h.a .i6 c₆) *
        h.elt (rootElt h.K h.a .i11 c₁₁) * h.elt (rootElt h.K h.a .i5 c₅) * u, y⁆ .i10 = 0 →
      h.r1c ⁅h.elt (rootElt h.K h.a .i2 c₂), y⁆ .i10 +
        h.r1c ⁅h.elt (rootElt h.K h.a .i8 c₈), y⁆ .i10 +
          h.r1c ⁅h.elt (rootElt h.K h.a .i6 c₆), y⁆ .i10 +
            h.r1c ⁅h.elt (rootElt h.K h.a .i5 c₅), y⁆ .i10 = 0 := by
    intro y hy e
    rwa [hadd (mul_mem (mul_mem (mul_mem (mul_mem hA hB) hC) hD) hE) hu4 hy, hzero hu hy,
      add_zero, hadd (mul_mem (mul_mem (mul_mem hA hB) hC) hD) hE hy,
      hadd (mul_mem (mul_mem hA hB) hC) hD hy, hzero hD3 hy, add_zero,
      hadd (mul_mem hA hB) hC hy, hadd hA hB hy] at e
  have hS1' : ∀ {z : G}, z ∈ h.S₁ → h.r1c z .i10 = 0 := fun {z} hz => by
    have hz' : z ∈ h.pull (rootJoin h.K h.a {.i11, .i12}) := hz
    exact h.r1c_eq_zero_of_mem (by decide) hz' rfl (by decide)
  have hS1 : ∀ {y : G}, y ∈ h.S₄ → h.r1c ⁅h.elt (rootElt h.K h.a .i2 c₂) *
      h.elt (rootElt h.K h.a .i8 c₈) * h.elt (rootElt h.K h.a .i6 c₆) *
        h.elt (rootElt h.K h.a .i11 c₁₁) * h.elt (rootElt h.K h.a .i5 c₅) * u, y⁆ .i10 = 0 :=
    fun hy => hS1' (hc _ hy)
  have hone : ∀ {g g' : ModGL F4.tag h.K}, g ∈ F4.reeGamma h.K h.a →
      g' ∈ F4.reeGamma h.K h.a → ⁅g, g'⁆ = 1 → h.r1c ⁅h.elt g, h.elt g'⁆ .i10 = 0 :=
    fun hg hg' e => by rw [← h.elt_commutator hg hg', e, h.elt_one', h.r1c_one rfl]
  have hswap : ∀ {g g' : ModGL F4.tag h.K}, ⁅g', g⁆ = 1 → ⁅g, g'⁆ = 1 := fun e => by
    rw [← commutatorElement_inv, e, inv_one]
  have hlin : ∀ (k : Idx), k.isSz = false → ∀ c d : h.K,
      ⁅rootElt h.K h.a k c, rootElt h.K h.a k d⁆ = 1 := fun k hk c d =>
    commutatorElement_eq_one_iff_mul_comm.2 (by
      rw [← rootElt_add h.card_K hk, ← rootElt_add h.card_K hk, add_comm])
  have hsz : ∀ (k : Idx), k.isSz = true → k.center.isR1 = true → k.center ≠ .i10 →
      ∀ c d : h.K,
        h.r1c ⁅h.elt (rootElt h.K h.a k c), h.elt (rootElt h.K h.a k d)⁆ .i10 = 0 := by
    intro k hk hkR hk10 c d
    rw [← h.elt_commutator (hΓ _ _) (hΓ _ _), rootElt_comm_self_of_isSz h.card_K hk,
      h.r1c_elt_rootElt hkR _ rfl, Pi.single_eq_of_ne (Ne.symm hk10)]
  have h28 : ∀ s t : h.K, h.r1c ⁅h.elt (rootElt h.K h.a .i2 s),
      h.elt (rootElt h.K h.a .i8 t)⁆ .i10 = s * t := fun s t => by
    rw [← h.elt_commutator (hΓ _ _) (hΓ _ _), rootElt_comm_2_8 h.card_K, h.r1c_ten_elt]
  have h65 : ∀ s t : h.K, h.r1c ⁅h.elt (rootElt h.K h.a .i6 s),
      h.elt (rootElt h.K h.a .i5 t)⁆ .i10 = s * t := fun s t => by
    rw [← h.elt_commutator (hΓ _ _) (hΓ _ _), rootElt_comm_6_5 h.card_K,
      h.r1c_elt_rootElt rfl _ rfl, Pi.single_eq_same]
  have hrev : ∀ {w y : G}, w ∈ h.S₄ → y ∈ h.S₄ → h.r1c ⁅w, y⁆ .i10 = h.r1c ⁅y, w⁆ .i10 :=
    fun hw hy => by
      rw [← commutatorElement_inv, h.r1c_inv (h.S₂_le_R₁ (h.comm_S₄_S₄_mem hy hw)) rfl]
  have t8 := hsum (hS4 .i8 (by decide) 1) (hS1 (hS4 .i8 (by decide) 1))
  rw [h28, mul_one, hone (hΓ _ _) (hΓ _ _) (hlin .i8 rfl c₈ 1),
    hone (hΓ _ _) (hΓ _ _) (hswap (rootElt_comm_8_6 h.card_K 1 c₆)),
    hone (hΓ _ _) (hΓ _ _) (hswap (rootElt_comm_8_5 h.card_K 1 c₅)), add_zero, add_zero,
    add_zero] at t8
  have t2 := hsum (hS4 .i2 (by decide) 1) (hS1 (hS4 .i2 (by decide) 1))
  rw [hone (hΓ _ _) (hΓ _ _) (hlin .i2 rfl c₂ 1), hrev hB (hS4 .i2 (by decide) 1), h28, one_mul,
    hone (hΓ _ _) (hΓ _ _) (hswap (rootElt_comm_2_6 h.card_K 1 c₆)),
    hone (hΓ _ _) (hΓ _ _) (hswap (rootElt_comm_2_5 h.card_K 1 c₅)), zero_add, add_zero,
    add_zero] at t2
  have t5 := hsum (hS4 .i5 (by decide) 1) (hS1 (hS4 .i5 (by decide) 1))
  rw [hone (hΓ _ _) (hΓ _ _) (rootElt_comm_2_5 h.card_K c₂ 1),
    hone (hΓ _ _) (hΓ _ _) (rootElt_comm_8_5 h.card_K c₈ 1), h65, mul_one,
    hsz .i5 rfl rfl (by decide) c₅ 1, zero_add, zero_add, add_zero] at t5
  have t6 := hsum (hS4 .i6 (by decide) 1) (hS1 (hS4 .i6 (by decide) 1))
  rw [hone (hΓ _ _) (hΓ _ _) (rootElt_comm_2_6 h.card_K c₂ 1),
    hone (hΓ _ _) (hΓ _ _) (rootElt_comm_8_6 h.card_K c₈ 1), hsz .i6 rfl rfl (by decide) c₆ 1,
    hrev hE (hS4 .i6 (by decide) 1), h65, one_mul, zero_add, zero_add, zero_add] at t6
  rw [t8, t2, t5, t6, rootElt_zero, rootElt_zero, rootElt_zero, rootElt_zero, h.elt_one',
    one_mul, one_mul, one_mul, mul_one]
  exact mul_mem hD3 hu

end Setup

namespace LevelOneData

variable {h : Setup G} (d : LevelOneData h)

theorem mem_S₃_sup_B2_of_comm_mem_B1 {q : G} (hq : q ∈ d.Q4)
    (hc : ∀ y ∈ d.B4, ⁅q, y⁆ ∈ d.B1) : q ∈ h.S₃ ⊔ d.B2 := by
  have hqQ : q ∈ ((h.S₄ ⊔ d.B2 : Subgroup G) : Set G) := hq
  rw [coe_mul_of_left_le_normalizer_right _ _ (h.S₄_le_Kp.trans d.Kp_le_normalizer_B2),
    Set.mem_mul] at hqQ
  obtain ⟨v, hv, b, hb, rfl⟩ := hqQ
  refine mul_mem (mem_sup_left (h.mem_S₃_of_comm_mem_S₁ hv fun y hy => ?_)) (mem_sup_right hb)
  have hby : ⁅b, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
    (mem_centralizer_iff.1 (d.B2_le_centralizer_S₄ hb) y hy).symm
  have h1 := hc y (d.S₄_le_Q4.trans d.Q4_le_B4 hy)
  rw [commutatorElement_mul_left_eq, hby, mul_one, mul_inv_cancel] at h1
  rw [one_mul] at h1
  have h2 := h.comm_S₄_S₄_mem hv hy
  exact d.mem_S₁_of_mem_B1 h1 (commutatorElement_eq_one_iff_mul_comm.2
    (h.mul_t_comm (h.pull_le_L _ h2)))

theorem comm_comm_t_inv_mem_B1 {x : G} (hx : x ∈ d.B4) (hc : ∀ y ∈ d.B4, ⁅x, y⁆ ∈ d.B1)
    {y : G} (hy : y ∈ d.B4) : ⁅⁅x, h.t⁆⁻¹, y⁆ ∈ d.B1 := by
  have htK : h.t ∈ h.Kp := h.P_sup_Tsyl_le_J_Kp.2 (mem_sup_right h.t_mem_Tsyl)
  have hy' := d.conj_Kp_mem_B4 (inv_mem htK) hy
  have h1 := (mem_normalizer_iff.1 (d.Kp_le_normalizer_B1 htK) _).1 (hc _ hy')
  have hv : ⁅x, h.t⁆⁻¹ ∈ d.B4 := inv_mem (d.Q4_le_B4 hx.2.2.2.2)
  have h2 : ⁅x, h.t⁆⁻¹ * ⁅x, y⁆ * ⁅x, h.t⁆⁻¹⁻¹ ∈ d.B1 :=
    (mem_normalizer_iff.1 (centralizer_le_normalizer _ (d.B4_le_centralizer_B1 hv)) _).1 (hc y hy)
  have e : ⁅⁅x, h.t⁆⁻¹, y⁆ = (⁅x, h.t⁆⁻¹ * ⁅x, y⁆ * ⁅x, h.t⁆⁻¹⁻¹)⁻¹ *
      (h.t * ⁅x, h.t⁻¹ * y * h.t⁻¹⁻¹⁆ * h.t⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact mul_mem (inv_mem h2) h1

theorem mem_B3_of_comm_mem_B1 {x : G} (hx : x ∈ d.B4) (hc : ∀ y ∈ d.B4, ⁅x, y⁆ ∈ d.B1) :
    x ∈ d.B3 := by
  have hS3B : h.S₃ ⊔ d.B2 ≤ d.B3 := sup_le d.S₃_le_B3 d.B2_le_B3
  have hv := d.mem_S₃_sup_B2_of_comm_mem_B1 (inv_mem hx.2.2.2.2)
    fun y hy => d.comm_comm_t_inv_mem_B1 hx hc hy
  rw [inv_mem_iff] at hv
  obtain ⟨v, hv, b, hb, hvb⟩ := d.exists_mul_of_mem_S₃_sup_B2 hv
  obtain ⟨w, hw, hwt⟩ := d.exists_B3_comm_t hv
  rw [← d.B3_eq] at hw
  have hwB := d.B3_le_B4 hw
  have hq : w⁻¹ * x ∈ d.Q4 := d.inv_mul_mem_Q4_of_comm hwB hx (by
    rw [hwt, hvb, inv_mul_cancel_left]
    exact hb)
  have hqc : ∀ y ∈ d.B4, ⁅w⁻¹ * x, y⁆ ∈ d.B1 := by
    intro y hy
    rw [commutatorElement_mul_left_eq]
    refine mul_mem ((mem_normalizer_iff.1 (centralizer_le_normalizer _
      (d.B4_le_centralizer_B1 (inv_mem hwB))) _).1 (hc y hy)) ?_
    rw [← commutatorElement_inv]
    exact inv_mem (d.comm_B4_B3_mem_B1 hy (inv_mem hw))
  have e : x = w * (w⁻¹ * x) := by group
  rw [e]
  exact mul_mem hw (hS3B (d.mem_S₃_sup_B2_of_comm_mem_B1 hq hqc))

theorem mem_B3_iff {x : G} : x ∈ d.B3 ↔ x ∈ d.B4 ∧ ∀ y ∈ d.B4, ⁅x, y⁆ ∈ d.B1 := by
  refine ⟨fun hx => ⟨d.B3_le_B4 hx, fun y hy => ?_⟩, fun hx => d.mem_B3_of_comm_mem_B1 hx.1 hx.2⟩
  rw [← commutatorElement_inv]
  exact inv_mem (d.comm_B4_B3_mem_B1 hy hx)

theorem sec3_8_three :
    zIn d.B4 = d.B2 ∧ d.B4 ≤ normalizer (d.B3 : Set G) ∧
      ∀ x : G, x ∈ d.B3 ↔ x ∈ d.B4 ∧ ∀ y ∈ d.B4, ⁅x, y⁆ ∈ d.B1 :=
  ⟨d.zIn_B4, d.B4_le_normalizer_B3, fun _ => d.mem_B3_iff⟩

end LevelOneData

end CFSG.LocalAnalysis.EvenBN.TwoF4
