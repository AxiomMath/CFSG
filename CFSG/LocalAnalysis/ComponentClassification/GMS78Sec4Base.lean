module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4Prelim

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

variable {G : Type} [Group G]

structure Sec4Base (L T U₁ : Subgroup G) : Prop where
  A_le : gmsA L T ≤ U₁
  mul_comm : ∀ a ∈ U₁, ∀ b ∈ U₁, a * b = b * a
  le_normalizer : T ≤ normalizer (U₁ : Set G)
  inf_eq_bot : (T ⊓ centralizer (L : Set G)) ⊓ U₁ = ⊥
  centralizer_eq : ∀ t ∈ T ⊓ centralizer (L : Set G), t ≠ 1 →
    U₁ ⊓ centralizer ({t} : Set G) = gmsA L T
  comm_mem : ∀ t ∈ T ⊓ centralizer (L : Set G), ∀ u ∈ U₁, t * u * t⁻¹ * u⁻¹ ∈ gmsA L T

namespace Sec4Base

variable {L T U₁ : Subgroup G}

theorem comm (hE : Sec4Base L T U₁) {u v : G} (hu : u ∈ U₁) (hv : v ∈ U₁) : u * v = v * u :=
  hE.mul_comm u hu v hv

theorem T₀_le_normalizer (hE : Sec4Base L T U₁) :
    T ⊓ centralizer (L : Set G) ≤ normalizer (U₁ : Set G) :=
  inf_le_left.trans hE.le_normalizer

theorem conj_mem (hE : Sec4Base L T U₁) {t : G} (ht : t ∈ T ⊓ centralizer (L : Set G))
    {u : G} (hu : u ∈ U₁) : t * u * t⁻¹ ∈ U₁ :=
  (mem_normalizer_iff.mp (hE.T₀_le_normalizer ht) u).mp hu

theorem exists_mul_eq (hE : Sec4Base L T U₁) {x : G}
    (hx : x ∈ U₁ ⊔ (T ⊓ centralizer (L : Set G))) :
    ∃ u ∈ U₁, ∃ t ∈ T ⊓ centralizer (L : Set G), u * t = x := by
  obtain ⟨t, ht, u, hu, rfl⟩ :=
    CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hE.T₀_le_normalizer (by rwa [sup_comm] at hx)
  exact ⟨t * u * t⁻¹, hE.conj_mem ht hu, t, ht, by group⟩

theorem V_le (hE : Sec4Base L T U₁) :
    gmsV L T ≤ U₁ ⊔ (T ⊓ centralizer (L : Set G)) :=
  sup_le (hE.A_le.trans le_sup_left) le_sup_right

theorem commute_mul_iff (hE : Sec4Base L T U₁) {u a t : G} (hu : u ∈ U₁)
    (ha : a ∈ gmsA L T) : u * (a * t) = (a * t) * u ↔ u * t = t * u := by
  have hau : u * a = a * u := hE.comm hu (hE.A_le ha)
  constructor
  · intro h
    have : a * (u * t) = a * (t * u) := by
      calc a * (u * t) = u * (a * t) := by rw [← mul_assoc, ← hau, mul_assoc]
        _ = (a * t) * u := h
        _ = a * (t * u) := by rw [mul_assoc]
    exact mul_left_cancel this
  · intro h
    rw [← mul_assoc, hau, mul_assoc, h, mul_assoc]

theorem inf_V (hE : Sec4Base L T U₁) : U₁ ⊓ gmsV L T = gmsA L T := by
  apply le_antisymm _ (le_inf hE.A_le le_sup_left)
  intro x hx
  obtain ⟨hxU, hxV⟩ := mem_inf.mp hx
  obtain ⟨a, ha, t, ht, rfl⟩ := exists_mul_eq_of_mem_V hxV
  have htU : t ∈ U₁ := by simpa using mul_mem (inv_mem (hE.A_le ha)) hxU
  have ht1 : t = 1 := by
    have : t ∈ (T ⊓ centralizer (L : Set G)) ⊓ U₁ := mem_inf.mpr ⟨ht, htU⟩
    rwa [hE.inf_eq_bot, mem_bot] at this
  rw [ht1, mul_one]
  exact ha

theorem centralizer_eq_of_mem_V (hE : Sec4Base L T U₁) {v : G} (hv : v ∈ gmsV L T)
    (hvA : v ∉ gmsA L T) : U₁ ⊓ centralizer ({v} : Set G) = gmsA L T := by
  obtain ⟨a, ha, t, ht, rfl⟩ := exists_mul_eq_of_mem_V hv
  have ht1 : t ≠ 1 := by
    rintro rfl
    exact hvA (by simpa using ha)
  rw [← hE.centralizer_eq t ht ht1]
  ext u
  simp only [mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hu, h⟩
    exact ⟨hu, (hE.commute_mul_iff hu ha).mp h⟩
  · rintro ⟨hu, h⟩
    exact ⟨hu, (hE.commute_mul_iff hu ha).mpr h⟩

theorem card_T₀_le [Finite G] (hE : Sec4Base L T U₁) (hlt : gmsA L T < U₁) :
    Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) ≤ Nat.card (gmsA L T) := by
  obtain ⟨u, huU, huA⟩ := IsConcreteLE.exists_of_lt hlt
  let φ : (T ⊓ centralizer (L : Set G) : Subgroup G) → gmsA L T := fun t =>
    ⟨t * u * (t : G)⁻¹ * u⁻¹, hE.comm_mem t t.2 u huU⟩
  refine Nat.card_le_card_of_injective φ fun t t' htt' => ?_
  have h1 : (t : G) * u * (t : G)⁻¹ * u⁻¹ = t' * u * (t' : G)⁻¹ * u⁻¹ := congrArg Subtype.val htt'
  have h2 : ((t' : G)⁻¹ * t) * u * ((t' : G)⁻¹ * t)⁻¹ = u := by
    have h3 : (t : G) * u * (t : G)⁻¹ = t' * u * (t' : G)⁻¹ := by simpa using h1
    calc ((t' : G)⁻¹ * t) * u * ((t' : G)⁻¹ * t)⁻¹ = (t' : G)⁻¹ * (t * u * (t : G)⁻¹) * t' := by
          group
      _ = (t' : G)⁻¹ * (t' * u * (t' : G)⁻¹) * t' := by rw [h3]
      _ = u := by group
  have hmem : (t' : G)⁻¹ * t ∈ T ⊓ centralizer (L : Set G) := mul_mem (inv_mem t'.2) t.2
  by_contra hne
  have hne' : (t' : G)⁻¹ * t ≠ 1 := fun h0 => hne (Subtype.ext (by
    have := congrArg (fun z => (t' : G) * z) h0
    simpa using this))
  apply huA
  rw [← hE.centralizer_eq _ hmem hne']
  refine mem_inf.mpr ⟨huU, mem_centralizer_singleton_iff.mpr ?_⟩
  calc u * ((t' : G)⁻¹ * t) = ((t' : G)⁻¹ * t) * u * ((t' : G)⁻¹ * t)⁻¹ * ((t' : G)⁻¹ * t) := by
        rw [h2]
    _ = ((t' : G)⁻¹ * t) * u := by group

theorem S₀_le_normalizer (hE : Sec4Base L T U₁) :
    U₁ ⊔ T ≤ normalizer (U₁ : Set G) :=
  sup_le Subgroup.le_normalizer hE.le_normalizer

variable [Finite G] {f : ℕ}

theorem inf_T (hE : Sec4Base L T U₁) (h : Sec3 G L T)
    (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) : U₁ ⊓ T = gmsA L T := by
  apply le_antisymm _ (le_inf hE.A_le (inf_le_left.trans inf_le_left))
  intro u hu
  obtain ⟨huU, huT⟩ := mem_inf.mp hu
  obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h.T₀_ne_bot
  have ht1' : t ≠ 1 := fun h1 => ht1 (Subtype.ext h1)
  have hZ := odd_card_center_of_psl2 h.hyp.standard.1.1 hf e
  have hc1 : t * u * t⁻¹ * u⁻¹ ∈ gmsA L T := hE.comm_mem t ht u huU
  have hc2 : t * u * t⁻¹ * u⁻¹ ∈ T ⊓ centralizer (L : Set G) := by
    have := mul_mem ht (h.conj_mem_T₀ huT (inv_mem ht))
    simpa [mul_assoc] using this
  have hc : t * u * t⁻¹ * u⁻¹ = 1 := by
    have : t * u * t⁻¹ * u⁻¹ ∈ (T ⊓ L) ⊓ (T ⊓ centralizer (L : Set G)) :=
      mem_inf.mpr ⟨(mem_inf.mp hc1).1, hc2⟩
    rwa [h.inf_eq_bot_of_odd hZ, mem_bot] at this
  rw [← hE.centralizer_eq t ht ht1']
  refine mem_inf.mpr ⟨huU, mem_centralizer_singleton_iff.mpr ?_⟩
  have h2 : t * u = u * t := by
    calc t * u = t * u * t⁻¹ * u⁻¹ * (u * t) := by group
      _ = u * t := by rw [hc, one_mul]
  exact h2.symm

omit [Finite G] in
theorem exists_mul_eq_S₀ (hE : Sec4Base L T U₁) {x : G} (hx : x ∈ U₁ ⊔ T) :
    ∃ u ∈ U₁, ∃ w ∈ T, u * w = x := by
  obtain ⟨w, hw, u, hu, rfl⟩ :=
    CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hE.le_normalizer (by rwa [sup_comm] at hx)
  exact ⟨w * u * w⁻¹, (mem_normalizer_iff.mp (hE.le_normalizer hw) u).mp hu, w, hw, by group⟩

theorem mul_mem_W_iff (hE : Sec4Base L T U₁)
    (h : Sec3 G L T) (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {u w : G}
    (hu : u ∈ U₁) (hw : w ∈ T) :
    u * w ∈ U₁ ⊔ (T ⊓ centralizer (L : Set G)) ↔ w ∈ gmsV L T := by
  constructor
  · intro hx
    have hwW : w ∈ U₁ ⊔ (T ⊓ centralizer (L : Set G)) := by
      simpa using mul_mem (mem_sup_left (inv_mem hu)) hx
    obtain ⟨u', hu', t, ht, hut⟩ := hE.exists_mul_eq hwW
    have hu'T : u' ∈ U₁ ⊓ T := by
      refine mem_inf.mpr ⟨hu', ?_⟩
      have : u' = w * t⁻¹ := by rw [← hut]; group
      rw [this]
      exact mul_mem hw (inv_mem (mem_inf.mp ht).1)
    rw [hE.inf_T h hf e] at hu'T
    rw [← hut]
    exact mul_mem (mem_sup_left hu'T) (mem_sup_right ht)
  · intro hwV
    exact mul_mem (mem_sup_left hu) (hE.V_le hwV)

theorem sq_mem_A (hE : Sec4Base L T U₁) (h : Sec3 G L T)
    (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {u w : G} (hu : u ∈ U₁)
    (hw : w ∈ T) (hx : u * w * (u * w) = 1) : w * w ∈ gmsA L T := by
  rw [← hE.inf_T h hf e]
  refine mem_inf.mpr ⟨?_, mul_mem hw hw⟩
  have h1 : w * u * w⁻¹ ∈ U₁ := (mem_normalizer_iff.mp (hE.le_normalizer hw) u).mp hu
  have : w * w = (w * u * w⁻¹)⁻¹ * u⁻¹ := by
    calc w * w = (w * u * w⁻¹)⁻¹ * u⁻¹ * (u * w * (u * w)) := by group
      _ = (w * u * w⁻¹)⁻¹ * u⁻¹ := by rw [hx, mul_one]
  rw [this]
  exact mul_mem (inv_mem h1) (inv_mem hu)

theorem mem_W_of_commute (hE : Sec4Base L T U₁)
    (h : Sec3 G L T) (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {x : G}
    (hx : x ∈ U₁ ⊔ T) (hxA : ∀ a ∈ gmsA L T, x * a = a * x) :
    x ∈ U₁ ⊔ (T ⊓ centralizer (L : Set G)) := by
  obtain ⟨u, hu, w, hw, rfl⟩ := hE.exists_mul_eq_S₀ hx
  refine (hE.mul_mem_W_iff h hf e hu hw).mpr (h.mem_V_of_commute hf e hw fun a ha => ?_)
  have h1 := hxA a ha
  have hua : u * a = a * u := hE.comm hu (hE.A_le ha)
  have : u * (w * a) = u * (a * w) := by
    calc u * (w * a) = u * w * a := by group
      _ = a * (u * w) := h1
      _ = u * (a * w) := by rw [← mul_assoc, ← hua, mul_assoc]
  exact mul_left_cancel this

theorem mul_mem_W (hE : Sec4Base L T U₁) (h : Sec3 G L T)
    (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {x₁ x₂ : G} (h₁ : x₁ ∈ U₁ ⊔ T)
    (h₂ : x₂ ∈ U₁ ⊔ T) (h₁₁ : x₁ * x₁ = 1) (h₂₂ : x₂ * x₂ = 1)
    (h₁W : x₁ ∉ U₁ ⊔ (T ⊓ centralizer (L : Set G)))
    (h₂W : x₂ ∉ U₁ ⊔ (T ⊓ centralizer (L : Set G))) :
    x₁ * x₂ ∈ U₁ ⊔ (T ⊓ centralizer (L : Set G)) := by
  obtain ⟨u₁, hu₁, w₁, hw₁, rfl⟩ := hE.exists_mul_eq_S₀ h₁
  obtain ⟨u₂, hu₂, w₂, hw₂, rfl⟩ := hE.exists_mul_eq_S₀ h₂
  rw [hE.mul_mem_W_iff h hf e hu₁ hw₁] at h₁W
  rw [hE.mul_mem_W_iff h hf e hu₂ hw₂] at h₂W
  have hs₁ := hE.sq_mem_A h hf e hu₁ hw₁ h₁₁
  have hs₂ := hE.sq_mem_A h hf e hu₂ hw₂ h₂₂
  have hmul := h.mul_inv_mem_V hf e hw₁ hw₂ h₁W h₂W (mem_sup_left hs₁) (mem_sup_left hs₂)
  have hw : w₁ * w₂ ∈ gmsV L T := by
    have : w₁ * w₂ = w₁ * w₂⁻¹ * (w₂ * w₂) := by group
    rw [this]
    exact mul_mem hmul (mem_sup_left hs₂)
  have hu : u₁ * (w₁ * u₂ * w₁⁻¹) ∈ U₁ :=
    mul_mem hu₁ ((mem_normalizer_iff.mp (hE.le_normalizer hw₁) u₂).mp hu₂)
  have : u₁ * w₁ * (u₂ * w₂) = u₁ * (w₁ * u₂ * w₁⁻¹) * (w₁ * w₂) := by group
  rw [this]
  exact mul_mem (mem_sup_left hu) (hE.V_le hw)

theorem card_le_two_mul (hE : Sec4Base L T U₁)
    (h : Sec3 G L T) (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f))
    {E : Subgroup G} (hES : E ≤ U₁ ⊔ T) (hE2 : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 2 * Nat.card (E ⊓ (U₁ ⊔ (T ⊓ centralizer (L : Set G))) : Subgroup G) := by
  refine card_le_two_mul_of_mul_mem fun x₁ hx₁ x₂ hx₂ h₁ h₂ => mem_inf.mpr
    ⟨mul_mem hx₁ hx₂, ?_⟩
  have h₁W : x₁ ∉ U₁ ⊔ (T ⊓ centralizer (L : Set G)) := fun h' => h₁ (mem_inf.mpr ⟨hx₁, h'⟩)
  have h₂W : x₂ ∉ U₁ ⊔ (T ⊓ centralizer (L : Set G)) := fun h' => h₂ (mem_inf.mpr ⟨hx₂, h'⟩)
  exact hE.mul_mem_W h hf e (hES hx₁) (hES hx₂) (hE2 _ hx₁) (hE2 _ hx₂) h₁W h₂W

theorem card_sq_le_of_involution (hE : Sec4Base L T U₁)
    (h : Sec3 G L T) (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f))
    (hX : Sec3.Facts L T (2 ^ f)) {x : G} (hx : x ∈ U₁ ⊔ T) (hxx : x * x = 1)
    (hxW : x ∉ U₁ ⊔ (T ⊓ centralizer (L : Set G))) :
    Nat.card (gmsA L T ⊓ centralizer ({x} : Set G) : Subgroup G) ^ 2 ≤ 2 ^ f := by
  obtain ⟨u, hu, w, hw, rfl⟩ := hE.exists_mul_eq_S₀ hx
  rw [hE.mul_mem_W_iff h hf e hu hw] at hxW
  have hs := hE.sq_mem_A h hf e hu hw hxx
  have heq : gmsA L T ⊓ centralizer ({u * w} : Set G) = gmsA L T ⊓ centralizer ({w} : Set G) := by
    ext a
    simp only [mem_inf, mem_centralizer_singleton_iff]
    refine and_congr_right fun ha => ?_
    have hua : u * a = a * u := hE.comm hu (hE.A_le ha)
    constructor
    · intro h1
      have : u * (a * w) = u * (w * a) := by
        calc u * (a * w) = a * (u * w) := by rw [← mul_assoc, hua, mul_assoc]
          _ = u * w * a := h1
          _ = u * (w * a) := by group
      exact mul_left_cancel this
    · intro h1
      calc a * (u * w) = u * (a * w) := by rw [← mul_assoc, ← hua, mul_assoc]
        _ = u * (w * a) := by rw [h1]
        _ = u * w * a := by group
  rw [heq]
  exact h.card_sq_le hf e hX hw hxW (mem_sup_left hs)

end Sec4Base

end CFSG.ComponentClassification.GMS78
