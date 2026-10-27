module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.ElimFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.GoldFusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.GoldHCount

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup

namespace Gold

theorem exists_goldschmidtClass {G : Type} [Group G] [Finite G] {T : Sylow 2 G}
    {A : Subgroup G} (hAT : A ≤ T) (hab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hsq : ∀ a ∈ A, a * a = 1) (hw : WClosed T A) {t : G} (htT : t ∈ (T : Subgroup G))
    (htA : t ∉ A) (ht2 : t * t = 1) (hconj : ∃ g : G, g * t * g⁻¹ ∈ A) :
    ∃ D : Subgroup G, GoldschmidtClass (T : Subgroup G) A D ∧
      Nat.card (⁅A, zpowers t⁆ : Subgroup G) ≤ (centralizer (A : Set G)).relIndex D ∧
      Nat.card A ≤ Nat.card D * (centralizer (A : Set G)).relIndex D := by
  classical
  obtain ⟨g₀, hg₀⟩ := hconj
  have ht₀ : t ∈ cj g₀⁻¹ A := by
    rw [mem_cj]
    simpa using hg₀
  have : Fintype (Subgroup G) := Fintype.ofFinite _
  let 𝒳 : Finset (Subgroup G) :=
    Finset.univ.filter (fun A' => (∃ h : G, A' = cj h A) ∧ t ∈ A')
  have h𝒳 : 𝒳.Nonempty :=
    ⟨cj g₀⁻¹ A, Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨g₀⁻¹, rfl⟩, ht₀⟩⟩
  obtain ⟨A', hA'𝒳, hmax⟩ := Finset.exists_max_image 𝒳 (fun A' => Nat.card ↥(A ⊓ A')) h𝒳
  simp only [𝒳, Finset.mem_filter, Finset.mem_univ, true_and] at hA'𝒳 hmax
  obtain ⟨⟨h, rfl⟩, htA'⟩ := hA'𝒳
  set B₁ : Subgroup G := A ⊓ cj h A with hB₁
  have hB₁A : B₁ ≤ A := inf_le_left
  have hB₁A' : B₁ ≤ cj h A := inf_le_right
  have hab' := comm_cj (g := h) hab
  have hB₁t : ∀ b ∈ B₁, t * b * t⁻¹ = b := by
    intro b hb
    rw [hab' t htA' b (hB₁A' hb)]
    group
  have hnorm : ∀ a ∈ A, t * a * t⁻¹ ∈ A := fun a ha => hw.conj_mem hAT htT ha
  obtain ⟨B₂, hB₁B₂, hB₂A, hB₂c, hcard1, hcard2⟩ := goldH_count hab hsq ht2 hnorm hB₁A hB₁t
  set H : Subgroup G := B₁ ⊔ zpowers t with hH
  have htH : t ∈ H := Subgroup.mem_sup_right (mem_zpowers t)
  have hHA' : H ≤ cj h A := sup_le hB₁A' ((zpowers_le).2 htA')
  have hyH : cj h⁻¹ H ≤ A := by
    rw [cj_le_iff, inv_inv]
    exact hHA'
  obtain ⟨g, hgH, hgN⟩ := hw.exists_cj_le hAT hab hyH
  have hcjH : ∀ y ∈ B₂, cj y H ≤ H := by
    intro y hy
    rw [hH, cj_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨b, hb, rfl⟩
      have hyA : y ∈ A := hB₂A hy
      have : (MulAut.conj y).toMonoidHom b = b := by
        change y * b * y⁻¹ = b
        rw [hab y hyA b (hB₁A hb)]
        group
      rw [this]
      exact Subgroup.mem_sup_left hb
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
      have hyt : y * t * y⁻¹ ∈ H := by
        have hc := hB₂c y hy
        have : y * t * y⁻¹ = (t * y * t⁻¹ * y⁻¹)⁻¹ * t := by group
        rw [this]
        exact H.mul_mem (H.inv_mem (Subgroup.mem_sup_left hc)) htH
      have : (MulAut.conj y).toMonoidHom (t ^ k) = (y * t * y⁻¹) ^ k := by
        simp [MulAut.conj_apply, conj_zpow]
      rw [this]
      exact H.zpow_mem hyt k
  have hB₂N : B₂ ≤ normalizer (H : Set G) := fun y hy =>
    mem_normalizer_of_cj_le (hcjH y hy) (hcjH y⁻¹ (B₂.inv_mem hy))
  have hDT : cj g B₂ ≤ T := (cj_le_cj.2 (le_inf (hB₂A.trans hAT) hB₂N)).trans hgN
  have htg : t ∈ cj g⁻¹ A := by
    rw [mem_cj]
    simpa using hgH (conj_mem_cj htH)
  have hB₁g : B₁ ≤ cj g⁻¹ A := cj_le_iff.1 ((cj_le_cj.2 (le_sup_left : B₁ ≤ H)).trans hgH)
  have hle : Nat.card ↥(A ⊓ cj g⁻¹ A) ≤ Nat.card B₁ := hmax _ ⟨⟨g⁻¹, rfl⟩, htg⟩
  have hB₁eq : B₁ = A ⊓ cj g⁻¹ A := Subgroup.eq_of_le_of_card_ge (le_inf hB₁A hB₁g) hle
  have hE : cj g B₁ = cj g A ⊓ A := by
    rw [hB₁eq, cj_inf, cj_cj_inv]
  set D : Subgroup G := cj g B₂ with hD
  have hDA : D ⊓ A = cj g B₁ := by
    apply le_antisymm
    · rw [hE]
      exact inf_le_inf_right _ (cj_le_cj.2 hB₂A)
    · exact le_inf (cj_le_cj.2 hB₁B₂) (by rw [hE]; exact inf_le_right)
  have hDC : D ⊓ centralizer (A : Set G) = D ⊓ A := by
    apply le_antisymm
    · have hsub : D ⊓ centralizer (A : Set G) ≤ A := by
        refine hw.le_of_centralizes hAT hab (y := g⁻¹) ?_ ?_
        · intro b hb a ha
          exact (mem_centralizer_iff.1 hb.2 a ha).symm
        · calc cj g⁻¹ (D ⊓ centralizer (A : Set G)) ≤ cj g⁻¹ D := cj_le_cj.2 inf_le_left
            _ = B₂ := by rw [hD, cj_inv_cj]
            _ ≤ A := hB₂A
      exact le_inf inf_le_left hsub
    · refine le_inf inf_le_left fun x hx => mem_centralizer_iff.2 fun a ha => ?_
      exact hab a ha x hx.2
  have hDcard : Nat.card D = Nat.card B₂ := card_cj g B₂
  have hq : (centralizer (A : Set G)).relIndex D * Nat.card B₁ = Nat.card B₂ := by
    have := Subgroup.relIndex_mul_card (centralizer (A : Set G)) D
    rw [inf_comm, hDC, hDA, card_cj] at this
    rw [← hDcard, ← this]
  have hpos : 0 < Nat.card B₁ := Nat.card_pos
  refine ⟨D, ?_, ?_, ?_⟩
  · unfold GoldschmidtClass
    refine ⟨hDT, ?_, g⁻¹, ?_⟩
    · intro hDA'
      have h1 : D = cj g B₁ := by
        rw [← hDA]
        exact (inf_eq_left.2 hDA').symm
      have h2 : Nat.card B₂ = Nat.card B₁ := by rw [← hDcard, h1, card_cj]
      have h3 : Nat.card A ≤ Nat.card B₁ := by
        rw [h2] at hcard2
        have : Nat.card A * Nat.card B₁ ≤ Nat.card B₁ * Nat.card B₁ := by
          simpa [sq] using hcard2
        exact Nat.le_of_mul_le_mul_right this hpos
      have h4 : B₁ = A := Subgroup.eq_of_le_of_card_ge hB₁A h3
      have h5 : A ≤ cj h A := h4 ▸ hB₁A'
      have h6 : A = cj h A := Subgroup.eq_of_le_of_card_ge h5 (by rw [card_cj])
      exact htA (h6 ▸ htA')
    · change cj g⁻¹ D ≤ A
      rw [hD, cj_inv_cj]
      exact hB₂A
  · have : Nat.card (⁅A, zpowers t⁆ : Subgroup G) * Nat.card B₁ ≤
        (centralizer (A : Set G)).relIndex D * Nat.card B₁ := by
      rw [hq]
      exact hcard1
    exact Nat.le_of_mul_le_mul_right this hpos
  · rw [hDcard]
    have h1 : Nat.card A * Nat.card B₁ ≤
        (Nat.card B₂ * (centralizer (A : Set G)).relIndex D) * Nat.card B₁ := by
      calc Nat.card A * Nat.card B₁ ≤ Nat.card B₂ ^ 2 := hcard2
        _ = Nat.card B₂ * ((centralizer (A : Set G)).relIndex D * Nat.card B₁) := by
          rw [hq]
          ring
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right h1 hpos

end Gold

open Gold in
theorem goldschmidt74Cor4 : Goldschmidt74Cor4 := by
  intro G _ _ T C hCT hab hsq hweak hns
  classical
  have hw : WClosed (T : Subgroup G) C := fun g hg => hweak g hg
  have : Fintype (Subgroup G) := Fintype.ofFinite _
  obtain ⟨c, hc, g₀, hgT, hgC⟩ := hns
  have ht₀2 : g₀ * c * g₀⁻¹ * (g₀ * c * g₀⁻¹) = 1 := by
    calc g₀ * c * g₀⁻¹ * (g₀ * c * g₀⁻¹) = g₀ * (c * c) * g₀⁻¹ := by group
      _ = 1 := by rw [hsq c hc]; group
  have ht₀conj : ∃ g : G, g * (g₀ * c * g₀⁻¹) * g⁻¹ ∈ C :=
    ⟨g₀⁻¹, by simpa [mul_assoc] using hc⟩
  obtain ⟨D₀, hD₀, -, -⟩ := exists_goldschmidtClass hCT hab hsq hw hgT hgC ht₀2 ht₀conj
  obtain ⟨B₀, hB₀S, hB₀max⟩ := Finset.exists_max_image
    (Finset.univ.filter fun B => GoldschmidtClass (T : Subgroup G) C B)
    (fun B => (centralizer (C : Set G)).relIndex B)
    ⟨D₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, hD₀⟩⟩
  have hB₀ := (Finset.mem_filter.1 hB₀S).2
  have hmax : ∀ B, GoldschmidtClass (T : Subgroup G) C B →
      (centralizer (C : Set G)).relIndex B ≤ (centralizer (C : Set G)).relIndex B₀ :=
    fun B hB => hB₀max B (Finset.mem_filter.2 ⟨Finset.mem_univ _, hB⟩)
  refine ⟨(centralizer (C : Set G)).relIndex B₀, ⟨B₀, hB₀, rfl⟩, hmax, ?_, ?_⟩
  · obtain ⟨D, hD, -, hDcard⟩ := exists_goldschmidtClass hCT hab hsq hw hgT hgC ht₀2 ht₀conj
    exact ⟨D, hD, hDcard.trans (Nat.mul_le_mul_left _ (hmax D hD))⟩
  · intro t htT ht2 hconj
    have ht2' : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht2, pow_two] at this
    by_cases htC : t ∈ C
    · have hbot : (⁅C, zpowers t⁆ : Subgroup G) ≤ ⊥ := by
        rw [Subgroup.commutator_le]
        intro a ha s hs
        have hsC : s ∈ C := (zpowers_le.2 htC) hs
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact hab a ha s hsC
      calc Nat.card (⁅C, zpowers t⁆ : Subgroup G) ≤ Nat.card (⊥ : Subgroup G) :=
          Subgroup.card_le_of_le hbot
        _ = 1 := Subgroup.card_bot
        _ ≤ _ := Nat.one_le_iff_ne_zero.2 (by
          change ((centralizer (C : Set G)).subgroupOf B₀).index ≠ 0
          exact Subgroup.index_ne_zero_of_finite)
    · obtain ⟨D, hD, hDcomm, -⟩ := exists_goldschmidtClass hCT hab hsq hw htT htC ht2' hconj
      exact hDcomm.trans (hmax D hD)

end CFSG.EvenSporadicStandard.M24Std
