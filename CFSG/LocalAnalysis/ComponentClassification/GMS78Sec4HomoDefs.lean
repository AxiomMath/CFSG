module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4Base

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

variable {G : Type} [Group G]

structure Sec4Homo (L T U₁ : Subgroup G) (q : ℕ) : Prop extends Sec4Base L T U₁ where
  lt : gmsA L T < U₁
  exp4 : ∀ u ∈ U₁, u ^ 4 = 1
  omega : ∀ u ∈ U₁, u ^ 2 = 1 → u ∈ gmsA L T
  card : Nat.card U₁ = q ^ 2
  dichotomy : ∀ t ∈ T ⊓ centralizer (L : Set G), t ≠ 1 →
    (∀ u ∈ U₁, t * u * t⁻¹ = u⁻¹) ∨ ∀ u ∈ U₁, (u * t) ^ 2 = 1 → u ∈ gmsA L T
  sylow : IsSylowOf 2 (U₁ ⊔ T) (normalizer (gmsV L T : Set G))

namespace Sec4Base

variable {L T U₁ : Subgroup G}

theorem le_normalizer_V (hE : Sec4Base L T U₁) : U₁ ≤ normalizer (gmsV L T : Set G) := by
  have hc : ∀ u ∈ U₁, ∀ v ∈ gmsV L T, u * v * u⁻¹ ∈ gmsV L T := by
    intro u hu v hv
    obtain ⟨a, ha, t, ht, rfl⟩ := exists_mul_eq_of_mem_V hv
    have h1 : u * t * u⁻¹ * t⁻¹ ∈ gmsA L T := by
      have := inv_mem (hE.comm_mem t ht u hu)
      simpa [mul_assoc] using this
    have hau : u * a = a * u := hE.comm hu (hE.A_le ha)
    have : u * (a * t) * u⁻¹ = a * (u * t * u⁻¹ * t⁻¹) * t := by
      calc u * (a * t) * u⁻¹ = u * a * t * u⁻¹ := by group
        _ = a * u * t * u⁻¹ := by rw [hau]
        _ = a * (u * t * u⁻¹ * t⁻¹) * t := by group
    rw [this]
    exact mul_mem (mul_mem (mem_sup_left ha) (mem_sup_left h1)) (mem_sup_right ht)
  exact fun u hu => mem_normalizer_of_conj_mem (hc u hu)
    (fun v hv => by simpa using hc u⁻¹ (inv_mem hu) v hv)

theorem S₀_le_normalizer_V [Finite G]
    (hE : Sec4Base L T U₁) (h : Sec3 G L T) (hF : Foundation) {f : ℕ} (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) :
    U₁ ⊔ T ≤ normalizer (gmsV L T : Set G) := by
  have hV : gmsV L T = (T ⊓ L) ⊔ (T ⊓ centralizer (L : Set G)) := by
    show gmsA L T ⊔ _ = _
    rw [h.gmsA_eq_of_psl2 hf e]
  refine sup_le hE.le_normalizer_V fun t ht => ?_
  rw [hV]
  exact h.normalizer_le_of_psl2 hF hf e (Subgroup.le_normalizer ht)

end Sec4Base

namespace Sec4Homo

variable {L T U₁ : Subgroup G} {q : ℕ}

theorem exists_of_not_mem_V (hE : Sec4Homo L T U₁ q) {x : G}
    (hx : x ∈ U₁ ⊔ (T ⊓ centralizer (L : Set G))) (hxx : x * x = 1) (hxV : x ∉ gmsV L T) :
    ∃ u ∈ U₁, ∃ t ∈ T ⊓ centralizer (L : Set G), t ≠ 1 ∧ u ∉ gmsA L T ∧ u * t = x ∧
      ∀ v ∈ U₁, t * v * t⁻¹ = v⁻¹ := by
  obtain ⟨u, hu, t, ht, rfl⟩ := hE.exists_mul_eq hx
  have huA : u ∉ gmsA L T := fun h1 => hxV (mul_mem (mem_sup_left h1) (mem_sup_right ht))
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [mul_one] at hxx
    exact huA (hE.omega u hu (by rw [sq]; exact hxx))
  rcases hE.dichotomy t ht ht1 with hinv | hinv
  · exact ⟨u, hu, t, ht, ht1, huA, rfl, hinv⟩
  · exact absurd (hinv u hu (by rw [sq]; exact hxx)) huA

theorem eq_of_inverts (hE : Sec4Homo L T U₁ q) (hT₀ : IsElemAbelian 2 (T ⊓ centralizer
    (L : Set G))) {t t' : G} (ht : t ∈ T ⊓ centralizer (L : Set G))
    (ht' : t' ∈ T ⊓ centralizer (L : Set G)) (hinv : ∀ v ∈ U₁, t * v * t⁻¹ = v⁻¹)
    (hinv' : ∀ v ∈ U₁, t' * v * t'⁻¹ = v⁻¹) : t = t' := by
  have hc : U₁ ≤ U₁ ⊓ centralizer ({t * t'} : Set G) := by
    intro u hu
    refine mem_inf.mpr ⟨hu, mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : t * t' * u * (t * t')⁻¹ = u := by
      calc t * t' * u * (t * t')⁻¹ = t * (t' * u * t'⁻¹) * t⁻¹ := by group
        _ = t * u⁻¹ * t⁻¹ := by rw [hinv' u hu]
        _ = (t * u * t⁻¹)⁻¹ := by group
        _ = u := by rw [hinv u hu, inv_inv]
    calc u * (t * t') = t * t' * u * (t * t')⁻¹ * (t * t') := by rw [h1]
      _ = t * t' * u := by group
  by_cases h1 : t * t' = 1
  · have ht'2 : t' * t' = 1 := by rw [← sq]; exact hT₀.2 t' ht'
    calc t = t * (t' * t') := by rw [ht'2, mul_one]
      _ = t * t' * t' := by group
      _ = t' := by rw [h1, one_mul]
  · rw [hE.centralizer_eq _ (mul_mem ht ht') h1] at hc
    exact absurd hc (not_le_of_gt hE.lt)

theorem mem_A_of_commute (hE : Sec4Homo L T U₁ q)
    (hT₀ : IsElemAbelian 2 (T ⊓ centralizer (L : Set G))) {u t₀ : G} (hu : u ∈ U₁)
    (huA : u ∉ gmsA L T) (ht₀ : t₀ ∈ T ⊓ centralizer (L : Set G)) {v : G}
    (hv : v ∈ gmsV L T) (hc : v * (u * t₀) = u * t₀ * v) : v ∈ gmsA L T := by
  obtain ⟨a, ha, t, ht, rfl⟩ := exists_mul_eq_of_mem_V hv
  have hau : a * u = u * a := hE.comm (hE.A_le ha) hu
  have hat₀ : a * t₀ = t₀ * a :=
    mem_centralizer_iff.mp (mem_inf.mp ht₀).2 a (mem_inf.mp (mem_inf.mp ha).1).2
  have htt₀ : t * t₀ = t₀ * t := congrArg Subtype.val (hT₀.1.is_comm.comm ⟨t, ht⟩ ⟨t₀, ht₀⟩)
  have h1 : t * u = u * t := by
    have h2 : a * (t * (u * t₀)) = a * ((u * t₀) * t) := by
      calc a * (t * (u * t₀)) = a * t * (u * t₀) := by group
        _ = u * t₀ * (a * t) := hc
        _ = a * (u * t₀ * t) := by
          rw [show u * t₀ * (a * t) = u * (t₀ * a) * t by group, ← hat₀,
            show u * (a * t₀) * t = u * a * t₀ * t by group, ← hau]
          group
    have h3 := mul_left_cancel h2
    have h4 : t * u * t₀ = u * t * t₀ := by
      calc t * u * t₀ = t * (u * t₀) := by group
        _ = u * t₀ * t := h3
        _ = u * t * t₀ := by rw [mul_assoc, ← htt₀, ← mul_assoc]
    exact mul_right_cancel h4
  by_cases ht1 : t = 1
  · rw [ht1, mul_one]
    exact ha
  · exfalso
    apply huA
    rw [← hE.centralizer_eq t ht ht1]
    exact mem_inf.mpr ⟨hu, mem_centralizer_singleton_iff.mpr h1.symm⟩

theorem elem_le_W [Finite G] (hE : Sec4Homo L T U₁ q)
    (hT₀ : IsElemAbelian 2 (T ⊓ centralizer (L : Set G)))
    {E : Subgroup G} (hEW : E ≤ U₁ ⊔ (T ⊓ centralizer (L : Set G))) (hEel : IsElemAbelian 2 E)
    (hEV : ¬ E ≤ gmsV L T) :
    (∃ u ∈ U₁, ∃ t₀ ∈ T ⊓ centralizer (L : Set G), t₀ ≠ 1 ∧ u ∉ gmsA L T ∧ u * t₀ ∈ E ∧
        ∀ v ∈ U₁, t₀ * v * t₀⁻¹ = v⁻¹) ∧
      E ⊓ gmsV L T ≤ gmsA L T ∧ Nat.card E ≤ 2 * Nat.card (E ⊓ gmsV L T : Subgroup G) := by
  have hE2 : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact hEel.2 x hx
  obtain ⟨x, hxE, hxV⟩ := IsConcreteLE.not_le_iff_exists.mp hEV
  obtain ⟨u, hu, t₀, ht₀, ht₀1, huA, rfl, hinv⟩ :=
    hE.exists_of_not_mem_V (hEW hxE) (hE2 _ hxE) hxV
  refine ⟨⟨u, hu, t₀, ht₀, ht₀1, huA, hxE, hinv⟩, fun v hv => ?_, ?_⟩
  · obtain ⟨hvE, hvV⟩ := mem_inf.mp hv
    exact hE.mem_A_of_commute hT₀ hu huA ht₀ hvV
      (congrArg Subtype.val (hEel.1.is_comm.comm ⟨v, hvE⟩ ⟨_, hxE⟩))
  · refine card_le_two_mul_of_mul_mem fun e₁ he₁ e₂ he₂ h₁ h₂ => ?_
    have h₁V : e₁ ∉ gmsV L T := fun h' => h₁ (mem_inf.mpr ⟨he₁, h'⟩)
    have h₂V : e₂ ∉ gmsV L T := fun h' => h₂ (mem_inf.mpr ⟨he₂, h'⟩)
    obtain ⟨u₁, hu₁, t₁, ht₁, -, -, rfl, hinv₁⟩ :=
      hE.exists_of_not_mem_V (hEW he₁) (hE2 _ he₁) h₁V
    obtain ⟨u₂, hu₂, t₂, ht₂, -, -, rfl, hinv₂⟩ :=
      hE.exists_of_not_mem_V (hEW he₂) (hE2 _ he₂) h₂V
    have h12 : t₁ = t₂ := hE.eq_of_inverts hT₀ ht₁ ht₂ hinv₁ hinv₂
    subst h12
    have ht₁t₁ : t₁ * t₁ = 1 := by rw [← sq]; exact hT₀.2 t₁ ht₁
    have heq : u₁ * t₁ * (u₂ * t₁) = u₁ * u₂⁻¹ := by
      calc u₁ * t₁ * (u₂ * t₁) = u₁ * (t₁ * u₂ * t₁⁻¹) * (t₁ * t₁) := by group
        _ = u₁ * u₂⁻¹ := by rw [hinv₁ u₂ hu₂, ht₁t₁, mul_one]
    have hmem := mul_mem he₁ he₂
    have hsq : (u₁ * u₂⁻¹) ^ 2 = 1 := by rw [← heq, sq]; exact hE2 _ hmem
    rw [heq] at hmem ⊢
    exact mem_inf.mpr ⟨hmem, mem_sup_left (hE.omega _ (mul_mem hu₁ (inv_mem hu₂)) hsq)⟩

theorem card_le_commutator [Finite G]
    (hE : Sec4Homo L T U₁ q) (h : Sec3 G L T) (hF : Foundation) (hX : Sec3.Facts L T q)
    {u t₀ : G} (hu : u ∈ U₁) (huA : u ∉ gmsA L T) (ht₀ : t₀ ∈ T ⊓ centralizer (L : Set G)) :
    Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) ≤
      Nat.card (⁅gmsV L T, zpowers (u * t₀)⁆ : Subgroup G) := by
  have hT₀ := h.isElemAbelian_T₀ hF
  obtain ⟨hVcard, hVel, -, -, -⟩ := hX.vFacts h hF
  have hxN : u * t₀ ∈ normalizer (gmsV L T : Set G) :=
    mul_mem (hE.le_normalizer_V hu) (le_normalizer (mem_sup_right ht₀))
  have h1 := card_le_card_inf_centralizer_mul hVel.1 hxN
  have h2 : Nat.card (gmsV L T ⊓ centralizer ({u * t₀} : Set G) : Subgroup G) ≤ q := by
    rw [← (hX.sylow h).1]
    refine card_le_of_le fun v hv => hE.mem_A_of_commute hT₀ hu huA ht₀ (mem_inf.mp hv).1 ?_
    exact mem_centralizer_singleton_iff.mp (mem_inf.mp hv).2
  rw [hVcard] at h1
  have h3 : q * Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) ≤
      q * Nat.card (⁅gmsV L T, zpowers (u * t₀)⁆ : Subgroup G) :=
    h1.trans (Nat.mul_le_mul_right _ h2)
  have hq : 0 < q := by have := hX.four_le; omega
  exact Nat.le_of_mul_le_mul_left h3 hq

end Sec4Homo

end CFSG.ComponentClassification.GMS78
