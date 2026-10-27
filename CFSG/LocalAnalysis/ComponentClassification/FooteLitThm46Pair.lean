module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitFooteM

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem le_normalizer_of_commutator_le_right {A B : Subgroup G} (h : ⁅A, B⁆ ≤ B) :
    A ≤ normalizer (B : Set G) := by
  intro x hx
  refine mem_normalizer_of_map_conj_le ?_
  rintro _ ⟨y, hy, rfl⟩
  have h1 := h (commutator_mem_commutator hx hy)
  rw [commutatorElement_def] at h1
  show x * y * x⁻¹ ∈ B
  rw [show x * y * x⁻¹ = x * y * x⁻¹ * y⁻¹ * y by group]
  exact mul_mem h1 hy

theorem le_normalizer_of_commutator_le_left {A B : Subgroup G} (h : ⁅A, B⁆ ≤ A) :
    B ≤ normalizer (A : Set G) := by
  rw [commutator_comm] at h
  exact le_normalizer_of_commutator_le_right h

omit [Finite G] in
theorem le_coreActionKernel_of_commutator_le_oddCoreIn {M₁ M₂ : Subgroup G}
    (hN : M₁ ≤ normalizer (M₂ : Set G)) (h : ⁅M₁, M₂⁆ ≤ oddCoreIn M₂) :
    M₁ ≤ coreActionKernel M₂ := by
  intro x hx
  refine ⟨hN hx, fun j hj => ?_⟩
  have h1 := h (commutator_mem_commutator (inv_mem hx) (inv_mem hj))
  rw [commutatorElement_def, inv_inv, inv_inv] at h1
  have h2 := inv_mem h1
  rwa [show (x⁻¹ * j⁻¹ * x * j)⁻¹ = j⁻¹ * x⁻¹ * j * x by group] at h2

theorem le_of_le_sup_odd {M N A : Subgroup G} (hM : M ≤ oddResidualIn M)
    (hAN : A ≤ normalizer (N : Set G)) (hA : Odd (Nat.card A)) (hMN : M ≤ A ⊔ N) : M ≤ N := by
  refine hM.trans ((closure_le _).mpr fun g hg => ?_)
  obtain ⟨hgM, h2⟩ := hg
  exact mem_of_two_element_of_mem_sup hAN (by rw [oddResidualIn_eq_bot_of_odd hA]; exact bot_le)
    (hMN hgM) h2

theorem foote_thm46_pair (h : FooteSec4 G L) {M₁ M₂ : Subgroup G} (hM₁ : IsFooteM L M₁)
    (hM₂ : IsFooteM L M₂) (hc : ⁅M₁, M₂⁆ ≤ M₁ ⊓ M₂) :
    M₁ = M₂ ∨ (⁅M₁, M₂⁆ ≤ oddCoreIn M₁ ⊓ oddCoreIn M₂ ∧ M₁ ≤ coreActionKernel M₂ ∧
      M₂ ≤ coreActionKernel M₁) := by
  have h12 : M₁ ≤ normalizer (M₂ : Set G) :=
    le_normalizer_of_commutator_le_right (hc.trans inf_le_right)
  have h21 : M₂ ≤ normalizer (M₁ : Set G) :=
    le_normalizer_of_commutator_le_left (hc.trans inf_le_left)
  have hN₁ : M₁ ≤ normalizer ((M₁ ⊓ M₂ : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_inf' (le_normalizer hx) (h12 hx)
  have hN₂ : M₂ ≤ normalizer ((M₁ ⊓ M₂ : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_inf' (h21 hx) (le_normalizer hx)
  have hsub₂ : M₂ ≤ (M₁ ⊓ M₂) ⊔ oddCoreIn M₂ → M₂ ≤ M₁ := fun hcov =>
    le_of_le_sup_odd (hM₂.le_oddResidualIn h) (fun x hx => h21 (map_subtype_le _ hx))
      (odd_card_oddCoreIn M₂) (hcov.trans (sup_le (inf_le_left.trans le_sup_right) le_sup_left))
  have hsub₁ : M₁ ≤ (M₁ ⊓ M₂) ⊔ oddCoreIn M₁ → M₁ ≤ M₂ := fun hcov =>
    le_of_le_sup_odd (hM₁.le_oddResidualIn h) (fun x hx => h12 (map_subtype_le _ hx))
      (odd_card_oddCoreIn M₁) (hcov.trans (sup_le (inf_le_right.trans le_sup_right) le_sup_left))
  rcases hM₂.le_or_le h inf_le_right hN₂ with h2 | h2 <;>
    rcases hM₁.le_or_le h inf_le_left hN₁ with h1 | h1
  · right
    have hcO : ⁅M₁, M₂⁆ ≤ oddCoreIn M₁ ⊓ oddCoreIn M₂ := le_inf (hc.trans h1) (hc.trans h2)
    refine ⟨hcO, le_coreActionKernel_of_commutator_le_oddCoreIn h12 (hcO.trans inf_le_right),
      le_coreActionKernel_of_commutator_le_oddCoreIn h21 ?_⟩
    rw [commutator_comm]
    exact hcO.trans inf_le_left
  · exfalso
    apply hM₁.not_odd h
    have hle : M₁ ≤ oddCoreIn M₂ := (le_inf le_rfl (hsub₁ h1)).trans h2
    exact Odd.of_dvd_nat (odd_card_oddCoreIn M₂) (card_dvd_of_le hle)
  · exfalso
    apply hM₂.not_odd h
    have hle : M₂ ≤ oddCoreIn M₁ := (le_inf (hsub₂ h2) le_rfl).trans h1
    exact Odd.of_dvd_nat (odd_card_oddCoreIn M₁) (card_dvd_of_le hle)
  · left
    exact le_antisymm (hsub₁ h1) (hsub₂ h2)

omit [Finite G] in
theorem not_odd_card_of_isQuasisimple {Q : Type*} [Group Q] [Finite Q] (hQ : IsQuasisimple Q) :
    ¬ Odd (Nat.card Q) := by
  intro hodd
  obtain ⟨-, hs, a, b, hab⟩ := hQ
  have hsol : Group.IsSolvable Q := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hsol' : Group.IsSolvable (Q ⧸ center Q) := inferInstance
  exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsol') a b)

theorem foote_thm46_no_involution (h : FooteSec4 G L) {M₁ M₂ : Subgroup G}
    (hM₁ : IsFooteM L M₁) (hM₂ : IsFooteM L M₂) (hc : ⁅M₁, M₂⁆ ≤ oddCoreIn M₁) {t : G}
    (ht : orderOf t = 2) (ht₁ : t ∈ coreActionKernel M₁) (ht₂ : t ∈ coreActionKernel M₂) :
    False := by
  obtain ⟨hfix₁, -, hBmax, -⟩ := foote_lemma_4_5_i h hM₁ ht ht₁
  obtain ⟨hfix₂, -, -, -⟩ := foote_lemma_4_5_i h hM₂ ht ht₂
  set B := footeF L t with hB
  set Y₁ := oddResidualIn (M₁ ⊓ centralizer ({t} : Set G)) with hY₁
  set Y₂ := oddResidualIn (M₂ ⊓ centralizer ({t} : Set G)) with hY₂
  have hY₁B : Y₁ ≤ B := hfix₁ ▸ oddResidualIn_inf_le_footeFixed M₁ t
  have hY₂B : Y₂ ≤ B := hfix₂ ▸ oddResidualIn_inf_le_footeFixed M₂ t
  have hBt : IsTwoComponentAt t B := hBmax.1
  have hcov₁ : B ≤ Y₁ ⊔ oddCoreIn B := by
    have h1 := (footeFixed_le_oddResidualIn_sup_oddCoreIn (hfix₁ ▸ hBt)).2
    rwa [hfix₁] at h1
  have hcov₂ : B ≤ Y₂ ⊔ oddCoreIn B := by
    have h1 := (footeFixed_le_oddResidualIn_sup_oddCoreIn (hfix₂ ▸ hBt)).2
    rwa [hfix₂] at h1
  set π := QuotientGroup.mk' (pPrimeCore 2 B) with hπ
  have himage : ∀ {Y : Subgroup G}, Y ≤ B → B ≤ Y ⊔ oddCoreIn B → (Y.subgroupOf B).map π = ⊤ := by
    intro Y hYB hcov
    refine eq_top_iff.mpr fun q _ => ?_
    obtain ⟨⟨b, hb⟩, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 B) q
    have hYO : Y ≤ normalizer ((oddCoreIn B : Subgroup G) : Set G) := fun x hx =>
      mem_normalizer_oddCoreIn (le_normalizer (hYB hx))
    have hb' := hcov hb
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right Y (oddCoreIn B) hYO] at hb'
    obtain ⟨y, hy, o, ho, hyo⟩ := hb'
    obtain ⟨o', ho', rfl⟩ := mem_map.mp ho
    refine ⟨⟨y, hYB hy⟩, hy, ?_⟩
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have e1 : (⟨y, hYB hy⟩ : B)⁻¹ * ⟨b, hb⟩ = o' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hyo]
      simp
    rw [e1]
    exact ho'
  have hq := isQuasisimple_quotient_of_isPComponent hBt.2.1 hBt.2.2
  have hperf : ⁅(⊤ : Subgroup (B ⧸ pPrimeCore 2 B)), (⊤ : Subgroup (B ⧸ pPrimeCore 2 B))⁆ = ⊤ := by
    have h1 := hq.1.commutator_eq_top
    rwa [commutator_def] at h1
  have hYc : ⁅Y₁.subgroupOf B, Y₂.subgroupOf B⁆ ≤ (oddCoreIn M₁).subgroupOf B := by
    intro x hx
    have h1 : (x : G) ∈ ⁅Y₁, Y₂⁆ := by
      have h2 := mem_map_of_mem B.subtype hx
      rwa [Subgroup.map_commutator, map_subgroupOf_eq_of_le hY₁B,
        map_subgroupOf_eq_of_le hY₂B] at h2
    have h3 : ⁅Y₁, Y₂⁆ ≤ ⁅M₁, M₂⁆ :=
      commutator_mono ((oddResidualIn_le _).trans inf_le_left)
        ((oddResidualIn_le _).trans inf_le_left)
    exact hc (h3 h1)
  have htop : ((oddCoreIn M₁).subgroupOf B).map π = ⊤ := by
    refine eq_top_iff.mpr ?_
    calc (⊤ : Subgroup (B ⧸ pPrimeCore 2 B)) = ⁅⊤, ⊤⁆ := hperf.symm
      _ = ⁅(Y₁.subgroupOf B).map π, (Y₂.subgroupOf B).map π⁆ := by
          rw [himage hY₁B hcov₁, himage hY₂B hcov₂]
      _ = ⁅Y₁.subgroupOf B, Y₂.subgroupOf B⁆.map π := (Subgroup.map_commutator _ _ _).symm
      _ ≤ _ := map_mono hYc
  have hodd : Odd (Nat.card ((oddCoreIn M₁).subgroupOf B)) := by
    have h1 : Nat.card ((oddCoreIn M₁).subgroupOf B) = Nat.card ↥(oddCoreIn M₁ ⊓ B) := by
      rw [← Subgroup.card_map_of_injective B.subtype_injective, subgroupOf_map_subtype]
    rw [h1]
    exact Odd.of_dvd_nat (odd_card_oddCoreIn M₁) (card_dvd_of_le inf_le_left)
  apply not_odd_card_of_isQuasisimple hq
  have h1 := card_map_dvd ((oddCoreIn M₁).subgroupOf B) π
  rw [htop, Subgroup.card_top] at h1
  exact Odd.of_dvd_nat hodd h1

theorem odd_card_coreActionKernel_inf (h : FooteSec4 G L) {M₁ M₂ : Subgroup G}
    (hM₁ : IsFooteM L M₁) (hM₂ : IsFooteM L M₂) (hc : ⁅M₁, M₂⁆ ≤ oddCoreIn M₁) :
    Odd (Nat.card ↥(coreActionKernel M₁ ⊓ coreActionKernel M₂)) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hodd)
  exact foote_thm46_no_involution h hM₁ hM₂ hc (by rw [Subgroup.orderOf_coe]; exact hx)
    (mem_inf.mp x.2).1 (mem_inf.mp x.2).2

end CFSG.ComponentClassification.FooteLit
