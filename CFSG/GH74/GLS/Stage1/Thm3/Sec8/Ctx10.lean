module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx9
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen5

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

theorem normedBy_iff_le_normalizer {G : Type} [Group G] {A X : Subgroup G} :
    NormedBy A X ↔ X ≤ normalizer (A : Set G) := by
  constructor
  · intro hN x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy; exact hN x hx y hy
    · intro hy
      have h1 := hN x⁻¹ (inv_mem hx) _ hy
      have e : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
      rwa [e] at h1
  · intro hX x hx w hw
    exact ((Subgroup.mem_normalizer_iff.1 (hX hx)) w).1 hw

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem relIndex_V₁ (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    (Vof S K₁ W₂).relIndex (Pof S K₁) = 2 := by
  have h1 := Basic.card_mul_relIndex_of_le (A := Vof S K₁ W₂) (B := Pof S K₁) inf_le_right
  have h2 := hs.card_V₁ hII hq
  have hpos : 0 < Nat.card ↥(Vof S K₁ W₂) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (by omega)

theorem relIndex_V₂ (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    (Vof S K₂ W₁).relIndex (Pof S K₂) = 2 := by
  have h1 := Basic.card_mul_relIndex_of_le (A := Vof S K₂ W₁) (B := Pof S K₂) inf_le_right
  have h2 := hs.card_V₂ hII hq
  have hpos : 0 < Nat.card ↥(Vof S K₂ W₁) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (by omega)

theorem V₂_cyclic (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) : IsCyclic ↥(Vof S K₂ W₁) :=
  Basic.isCyclic_of_le inf_le_left hs.W₁_max.2.1

theorem V₂_card_eq (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) :
    Nat.card ↥(Vof S K₂ W₁) = 2 ^ k := by
  obtain ⟨e, he, -, hNN, -⟩ := hs.lemma82_core hII hq hrec
  have h1 := hs.card_V₁ hII hq
  have h2 := hs.card_V₂ hII hq
  omega

theorem z_mem_V₂ (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk2 : 2 ≤ k)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) : z ∈ Vof S K₂ W₁ := by
  have hk' := hs.V₂_card_eq hII hq hrec hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨x, hxV, hx2, hx1⟩ := Basic.exists_involution_of_cyclic hs.V₂_cyclic hk'
  have hxP : x ∈ Pof S K₂ := hxV.2
  rcases (hs.gq_P hII hq (Or.inr rfl)).uniq x hxP hx2 with h' | h'
  · exact absurd h' hx1
  · rw [← h']; exact hxV

theorem V₂V_comm (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    ∀ c ∈ Vof S K₂ W₁, ∀ v ∈ conjugate (Vof S K₁ W₂) h, c * v = v * c :=
  hs.comm_V hII hq hrec (K := K₂) (X := Vof S K₂ W₁) (Or.inr rfl) inf_le_right
    (hs.V₂_le_W hII hq) (hs.V₂_normal hII)

theorem V₂_le_A (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) :
    Vof S K₂ W₁ ≤ Aof S K₁ W₂ h := by
  intro x hx
  have hxS : x ∈ S := hx.2.1
  have hxc : ∀ a ∈ Aof S K₁ W₂ h, x * a = a * x := by
    intro a ha
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hs.A_mem hII hq hrec ha
    have h1 : x * a₁ = a₁ * x := (hs.P_comm hII a₁ ha₁.2 x hx.2).symm
    have h2 : x * a₂ = a₂ * x := hs.V₂V_comm hII hq hrec x hx a₂ ha₂
    calc x * (a₁ * a₂) = (x * a₁) * a₂ := by group
      _ = (a₁ * x) * a₂ := by rw [h1]
      _ = a₁ * (x * a₂) := by group
      _ = a₁ * (a₂ * x) := by rw [h2]
      _ = a₁ * a₂ * x := by group
  have hx1 : x ^ (2 ^ k) = 1 := by
    have := Basic.pow_card_of_mem hx
    rwa [hs.V₂_card_eq hII hq hrec hk] at this
  exact hs.cent_mem_A hII hq hrec hk hxS hxc hx1

theorem cent_P (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {x : G}
    (hx : x ∈ Pz S z) (hx1 : ∀ a ∈ Vof S K₁ W₂, x * a = a * x)
    (hx2 : ∀ a ∈ Vof S K₂ W₁, x * a = a * x) :
    ∃ a ∈ Vof S K₁ W₂, ∃ b ∈ Vof S K₂ W₁, x = a * b := by
  rw [hs.Pz_eq_sup hII] at hx
  obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := Basic.mem_sup_of_commute' (hs.P_comm hII) hx
  have hc1 : ∀ a ∈ Vof S K₁ W₂, p₁ * a = a * p₁ := by
    intro a ha
    have h1 := hx1 a ha
    have h2 : a * p₂ = p₂ * a := hs.P_comm hII a ha.2 p₂ hp₂
    have h3 : (p₁ * a) * p₂ = (a * p₁) * p₂ := by
      calc (p₁ * a) * p₂ = p₁ * (a * p₂) := by group
        _ = p₁ * (p₂ * a) := by rw [h2]
        _ = p₁ * p₂ * a := by group
        _ = a * (p₁ * p₂) := h1
        _ = (a * p₁) * p₂ := by group
    exact mul_right_cancel h3
  have hc2 : ∀ b ∈ Vof S K₂ W₁, p₂ * b = b * p₂ := by
    intro b hb
    have h1 := hx2 b hb
    have h2 : p₁ * b = b * p₁ := hs.P_comm hII p₁ hp₁ b hb.2
    have h3 : p₁ * (p₂ * b) = p₁ * (b * p₂) := by
      calc p₁ * (p₂ * b) = p₁ * p₂ * b := by group
        _ = b * (p₁ * p₂) := h1
        _ = (b * p₁) * p₂ := by group
        _ = (p₁ * b) * p₂ := by rw [h2]
        _ = p₁ * (b * p₂) := by group
    exact mul_left_cancel h3
  refine ⟨p₁, ?_, p₂, ?_, rfl⟩
  · exact (hs.gq_P hII hq (Or.inl rfl)).mem_of_commute (W := Vof S K₁ W₂) (V := Vof S K₁ W₂)
      inf_le_right hs.V₁_cyclic (hs.relIndex_V₁ hII hq) le_rfl (hs.four_le_V₁ hII hq) hp₁ hc1
  · exact (hs.gq_P hII hq (Or.inr rfl)).mem_of_commute (W := Vof S K₂ W₁) (V := Vof S K₂ W₁)
      inf_le_right hs.V₂_cyclic (hs.relIndex_V₂ hII hq) le_rfl (hs.four_le_V₂ hII hq) hp₂ hc2

theorem A_ne_V₁V₂ (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk2 : 2 ≤ k)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) :
    Aof S K₁ W₂ h ≠ Vof S K₁ W₂ ⊔ Vof S K₂ W₁ := by
  intro heq
  have hV₁₂ : ∀ a ∈ Vof S K₁ W₂, ∀ b ∈ Vof S K₂ W₁, a * b = b * a :=
    fun a ha b hb => hs.P_comm hII a ha.2 b hb.2
  have hc12 := M.card_sup_mul_card_inf (A := Vof S K₁ W₂) (B := Vof S K₂ W₁)
    (M.le_normalizer_of_commute hV₁₂)
  have hVV : Vof S K₁ W₂ ⊓ conjugate (Vof S K₁ W₂) h = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ conjugate (Vof S K₁ W₂) h ⊓ Qof S K₂ :=
      ⟨hx.2, hs.P₁_le_Q₂ hII hx.1.2⟩
    rw [hs.V₁h_inf_Q hII hq (Or.inr rfl)] at this
    exact this
  have hVc : Nat.card ↥(conjugate (Vof S K₁ W₂) h) = 2 ^ k := by rw [conjugate_card, hk]
  have hAcard : Nat.card ↥(Aof S K₁ W₂ h) = 2 ^ k * 2 ^ k := by
    have h1 := M.card_sup_mul_card_inf (A := Vof S K₁ W₂) (B := conjugate (Vof S K₁ W₂) h)
      (M.le_normalizer_of_commute (hs.V₁V_comm hII hq hrec))
    rw [hVV, Subgroup.card_bot, mul_one, hk, hVc] at h1
    exact h1
  have hz1 : z ∈ Vof S K₁ W₂ := hs.z_mem_V₁ hII hq hk2 hk
  have hz2 : z ∈ Vof S K₂ W₁ := hs.z_mem_V₂ hII hq hrec hk2 hk
  have hzle : zpowers z ≤ Vof S K₁ W₂ ⊓ Vof S K₂ W₁ := le_inf (zpowers_le.2 hz1) (zpowers_le.2 hz2)
  have h2 : 2 ≤ Nat.card ↥(Vof S K₁ W₂ ⊓ Vof S K₂ W₁) := by
    have := Subgroup.card_le_of_le hzle
    rwa [M.card_zpowers_of_sq hs.z_sq hs.z_ne] at this
  have hVcard := hs.V₂_card_eq hII hq hrec hk
  rw [hk, hVcard] at hc12
  rw [heq] at hAcard
  have hpos : 0 < Nat.card ↥(Vof S K₁ W₂ ⊔ Vof S K₂ W₁) := Nat.card_pos
  have := Nat.mul_le_mul_left (Nat.card ↥(Vof S K₁ W₂ ⊔ Vof S K₂ W₁)) h2
  omega

theorem exists_A_not_mem_P (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk2 : 2 ≤ k)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) : ∃ a ∈ Aof S K₁ W₂ h, a ∉ Pz S z := by
  by_contra hcon
  push Not at hcon
  have hV₂A := hs.V₂_le_A hII hq hrec hk
  have hA : Aof S K₁ W₂ h ≤ Vof S K₁ W₂ ⊔ Vof S K₂ W₁ := by
    intro a ha
    obtain ⟨b₁, hb₁, b₂, hb₂, hab⟩ := hs.cent_P hII hq (hcon a ha)
      (fun c hc => hs.A_comm hII hq hrec a ha c (Subgroup.mem_sup_left hc))
      (fun c hc => hs.A_comm hII hq hrec a ha c (hV₂A hc))
    rw [hab]; exact Subgroup.mul_mem_sup hb₁ hb₂
  have hge : Vof S K₁ W₂ ⊔ Vof S K₂ W₁ ≤ Aof S K₁ W₂ h := sup_le le_sup_left hV₂A
  exact hs.A_ne_V₁V₂ hII hq hrec hk2 hk (le_antisymm hA hge)

theorem KL_e1 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk2 : 2 ≤ k)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) (he : (Pz S z).relIndex (S1 S K₁) = 2) {x : G}
    (hxS : x ∈ S) (hx1 : ∀ a ∈ Vof S K₁ W₂, x * a = a * x)
    (hx2 : ∀ a ∈ Vof S K₂ W₁, x * a = a * x) : x ∈ Aof S K₁ W₂ h := by
  have hV₂A := hs.V₂_le_A hII hq hrec hk
  have hxS1 : x ∈ S1 S K₁ := hs.cent_le_S1 hII hq hxS hx1
  by_cases hxP : x ∈ Pz S z
  · obtain ⟨a, ha, b, hb, hab⟩ := hs.cent_P hII hq hxP hx1 hx2
    rw [hab]
    exact mul_mem (Subgroup.mem_sup_left ha) (hV₂A hb)
  · obtain ⟨a, haA, haP⟩ := hs.exists_A_not_mem_P hII hq hrec hk2 hk
    have haS1 : a ∈ S1 S K₁ := hs.A_le_S1 hII hq hrec haA
    have hxa : x * a⁻¹ ∈ Pz S z := Basic.mul_inv_mem_of_relIndex_two he hxS1 haS1 hxP haP
    have hAcomm := hs.A_comm hII hq hrec
    have c1 : ∀ c ∈ Vof S K₁ W₂, (x * a⁻¹) * c = c * (x * a⁻¹) := by
      intro c hc
      have h1 : a * c = c * a := hAcomm a haA c (Subgroup.mem_sup_left hc)
      have h2 : a⁻¹ * c = c * a⁻¹ := (Commute.inv_left (show Commute a c from h1)).eq
      calc x * a⁻¹ * c = x * (a⁻¹ * c) := by group
        _ = x * (c * a⁻¹) := by rw [h2]
        _ = (x * c) * a⁻¹ := by group
        _ = (c * x) * a⁻¹ := by rw [hx1 c hc]
        _ = c * (x * a⁻¹) := by group
    have c2 : ∀ c ∈ Vof S K₂ W₁, (x * a⁻¹) * c = c * (x * a⁻¹) := by
      intro c hc
      have h1 : a * c = c * a := hAcomm a haA c (hV₂A hc)
      have h2 : a⁻¹ * c = c * a⁻¹ := (Commute.inv_left (show Commute a c from h1)).eq
      calc x * a⁻¹ * c = x * (a⁻¹ * c) := by group
        _ = x * (c * a⁻¹) := by rw [h2]
        _ = (x * c) * a⁻¹ := by group
        _ = (c * x) * a⁻¹ := by rw [hx2 c hc]
        _ = c * (x * a⁻¹) := by group
    obtain ⟨b₁, hb₁, b₂, hb₂, hb⟩ := hs.cent_P hII hq hxa c1 c2
    have e : x = (x * a⁻¹) * a := by group
    rw [e, hb]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left hb₁) (hV₂A hb₂)) haA

theorem swap_P₁ (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {t x : G} (ht : t ∈ S)
    (hn : t ∉ S1 S K₁) (hx : x ∈ Pof S K₁) : t * x * t⁻¹ ∈ Pof S K₂ := by
  obtain ⟨-, hK⟩ := hs.swap_of_not_mem hII ht hn
  have h1 : x ∈ conjugate K₂ t := by rw [hK]; exact hx.2
  have h2 : t * x * t⁻¹ ∈ K₂ := mem_conjugate_iff.1 h1
  have hxS : x ∈ S := hx.1
  exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem ht hxS) (inv_mem ht), h2⟩

theorem swap_P₂ (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {t x : G} (ht : t ∈ S)
    (hn : t ∉ S1 S K₁) (hx : x ∈ Pof S K₂) : t * x * t⁻¹ ∈ Pof S K₁ := by
  obtain ⟨hK, -⟩ := hs.swap_of_not_mem hII ht hn
  have h1 : x ∈ conjugate K₁ t := by rw [hK]; exact hx.2
  have h2 : t * x * t⁻¹ ∈ K₁ := mem_conjugate_iff.1 h1
  have hxS : x ∈ S := hx.1
  exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem ht hxS) (inv_mem ht), h2⟩

theorem swap_Q₂ (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {t x : G} (ht : t ∈ S)
    (hn : t ∉ S1 S K₁) (hx : x ∈ Qof S K₂) : t * x * t⁻¹ ∈ Qof S K₁ := by
  obtain ⟨hK, -⟩ := hs.swap_of_not_mem hII ht hn
  have h1 : x ∈ cSec (conjugate K₁ t) := by rw [hK]; exact hx.2
  have h2 : t * x * t⁻¹ ∈ cSec K₁ := mem_cSec_conjugate.1 h1
  have hxS : x ∈ S := hx.1
  exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem ht hxS) (inv_mem ht), h2⟩

theorem swap_Q₁ (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {t x : G} (ht : t ∈ S)
    (hn : t ∉ S1 S K₁) (hx : x ∈ Qof S K₁) : t * x * t⁻¹ ∈ Qof S K₂ := by
  obtain ⟨-, hK⟩ := hs.swap_of_not_mem hII ht hn
  have h1 : x ∈ cSec (conjugate K₂ t) := by rw [hK]; exact hx.2
  have h2 : t * x * t⁻¹ ∈ cSec K₂ := mem_cSec_conjugate.1 h1
  have hxS : x ∈ S := hx.1
  exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem ht hxS) (inv_mem ht), h2⟩

theorem conj_W₂_eq_W₁ (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (h16 : 16 ≤ Nat.card ↥(Qof S K₁)) {t : G} (ht : t ∈ S)
    (hn : t ∉ S1 S K₁) : conjugate W₂ t⁻¹ = W₁ := by
  obtain ⟨e, he, hri, hNN, hq1, hq2⟩ := hs.lemma82_core hII hq hrec
  have hQQ : Nat.card ↥(Qof S K₁) = Nat.card ↥(Qof S K₂) := by rw [hq1, hq2, hNN]
  refine (hs.gq_Q₁ hII).cyclic_unique h16 ?_ ?_ ?_ hs.W₁_le_Q₁ hs.W₁_max.2.1 (hs.card_W₁ hII)
  · intro x hx
    have hx' : t⁻¹ * x * t ∈ W₂ := by
      have := mem_conjugate_iff.1 hx
      rwa [inv_inv] at this
    have h1 := hs.swap_Q₂ hII ht hn (hs.W₂_le_Q₂ hx')
    have e : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
    rwa [e] at h1
  · rw [conjugate_eq_comap]; exact Basic.cyclic_comap_conj _ hs.W₂_max.2.1 t⁻¹
  · rw [conjugate_card]
    have := hs.card_W₂ hII
    omega

theorem conj_W₁_eq_W₂ (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (h16 : 16 ≤ Nat.card ↥(Qof S K₁)) {t : G} (ht : t ∈ S)
    (hn : t ∉ S1 S K₁) : conjugate W₁ t⁻¹ = W₂ := by
  obtain ⟨e, he, hri, hNN, hq1, hq2⟩ := hs.lemma82_core hII hq hrec
  have hQQ : Nat.card ↥(Qof S K₁) = Nat.card ↥(Qof S K₂) := by rw [hq1, hq2, hNN]
  have h16' : 16 ≤ Nat.card ↥(Qof S K₂) := hQQ ▸ h16
  refine (hs.gq_Q₂ hII).cyclic_unique h16' ?_ ?_ ?_ hs.W₂_le_Q₂ hs.W₂_max.2.1 (hs.card_W₂ hII)
  · intro x hx
    have hx' : t⁻¹ * x * t ∈ W₁ := by
      have := mem_conjugate_iff.1 hx
      rwa [inv_inv] at this
    have h1 := hs.swap_Q₁ hII ht hn (hs.W₁_le_Q₁ hx')
    have e : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
    rwa [e] at h1
  · rw [conjugate_eq_comap]; exact Basic.cyclic_comap_conj _ hs.W₁_max.2.1 t⁻¹
  · rw [conjugate_card]
    have := hs.card_W₁ hII
    omega

theorem swap_V (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (h16 : 16 ≤ Nat.card ↥(Qof S K₁)) {t : G} (ht : t ∈ S)
    (hn : t ∉ S1 S K₁) :
    (∀ x ∈ Vof S K₁ W₂, t * x * t⁻¹ ∈ Vof S K₂ W₁) ∧
      (∀ x ∈ Vof S K₂ W₁, t * x * t⁻¹ ∈ Vof S K₁ W₂) := by
  obtain ⟨e, he, hri, hNN, hq1, hq2⟩ := hs.lemma82_core hII hq hrec
  have hQQ : Nat.card ↥(Qof S K₁) = Nat.card ↥(Qof S K₂) := by rw [hq1, hq2, hNN]
  have h16' : 16 ≤ Nat.card ↥(Qof S K₂) := hQQ ▸ h16
  have hD := hs.conj_W₂_eq_W₁ hII hq hrec h16 ht hn
  have hD' := hs.conj_W₁_eq_W₂ hII hq hrec h16 ht hn
  constructor
  · intro x hx
    have hxD : t * x * t⁻¹ ∈ conjugate W₂ t⁻¹ := by
      rw [mem_conjugate_iff]
      have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
      rw [e]; exact hx.1
    rw [hD] at hxD
    exact ⟨hxD, hs.swap_P₁ hII ht hn hx.2⟩
  · intro x hx
    have hxD : t * x * t⁻¹ ∈ conjugate W₁ t⁻¹ := by
      rw [mem_conjugate_iff]
      have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
      rw [e]; exact hx.1
    rw [hD'] at hxD
    exact ⟨hxD, hs.swap_P₂ hII ht hn hx.2⟩

theorem A_normedBy_S_of (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk2 : 2 ≤ k)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k)
    (hU : ∀ t ∈ S, t ∉ S1 S K₁ → (∀ x ∈ Vof S K₁ W₂, t * x * t⁻¹ ∈ Vof S K₂ W₁) ∧
      (∀ x ∈ Vof S K₂ W₁, t * x * t⁻¹ ∈ Vof S K₁ W₂))
    (hKL : ∀ x ∈ S, (∀ a ∈ Vof S K₁ W₂, x * a = a * x) → (∀ a ∈ Vof S K₂ W₁, x * a = a * x) →
      x ^ (2 ^ k) = 1 → x ∈ Aof S K₁ W₂ h) :
    NormedBy (Aof S K₁ W₂ h) S := by
  intro t ht a ha
  by_cases hts : t ∈ S1 S K₁
  · exact hs.A_normedBy_S1 hII hq hrec hk2 hk t hts a ha
  · obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hs.A_mem hII hq hrec ha
    obtain ⟨hU₁, hU₂⟩ := hU t ht hts
    have htinv : t⁻¹ ∈ S := inv_mem ht
    have htn' : t⁻¹ ∉ S1 S K₁ := fun h' => hts (by have := inv_mem h'; rwa [inv_inv] at this)
    obtain ⟨hU₁', hU₂'⟩ := hU t⁻¹ htinv htn'
    have e : t * (a₁ * a₂) * t⁻¹ = (t * a₁ * t⁻¹) * (t * a₂ * t⁻¹) := by group
    rw [e]
    refine mul_mem (hs.V₂_le_A hII hq hrec hk (hU₁ a₁ ha₁)) ?_
    have ha₂S : a₂ ∈ S := (hs.V₁h_le_S1 hII hq hrec ha₂).1
    apply hKL _ (mul_mem (mul_mem ht ha₂S) (inv_mem ht))
    · intro c hc
      have hc' : t⁻¹ * c * t ∈ Vof S K₂ W₁ := by
        have := hU₁' c hc
        rwa [inv_inv] at this
      have key := hs.V₂V_comm hII hq hrec _ hc' a₂ ha₂
      calc (t * a₂ * t⁻¹) * c = t * (a₂ * (t⁻¹ * c * t)) * t⁻¹ := by group
        _ = t * ((t⁻¹ * c * t) * a₂) * t⁻¹ := by rw [key]
        _ = c * (t * a₂ * t⁻¹) := by group
    · intro c hc
      have hc' : t⁻¹ * c * t ∈ Vof S K₁ W₂ := by
        have := hU₂' c hc
        rwa [inv_inv] at this
      have key := hs.V₁V_comm hII hq hrec _ hc' a₂ ha₂
      calc (t * a₂ * t⁻¹) * c = t * (a₂ * (t⁻¹ * c * t)) * t⁻¹ := by group
        _ = t * ((t⁻¹ * c * t) * a₂) * t⁻¹ := by rw [key]
        _ = c * (t * a₂ * t⁻¹) := by group
    · rw [conj_pow, hs.V_pow hk a₂ ha₂]; group

theorem A_normedBy_Sh (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k)
    (hS : NormedBy (Aof S K₁ W₂ h) S) : NormedBy (Aof S K₁ W₂ h) (S ⊔ zpowers h) := by
  rw [normedBy_iff_le_normalizer]
  exact sup_le (normedBy_iff_le_normalizer.1 hS)
    (normedBy_iff_le_normalizer.1 (hs.A_normedBy_h hII hq hrec hk))

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
