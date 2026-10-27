module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualHigherRead

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup

section Simple

variable {G : Type*} [Group G]

theorem center_eq_bot_of_simple_of_not_comm {H : Type*} [Group H] [IsSimpleGroup H]
    (hnc : ∃ a b : H, a * b ≠ b * a) : Subgroup.center H = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center H) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have ha : a ∈ Subgroup.center H := by rw [h]; exact mem_top a
    exact hab ((Subgroup.mem_center_iff.mp ha b).symm)

theorem le_of_isPGroup_of_simple [Finite G] {N M : Subgroup G} [N.Normal] [M.Normal]
    [IsSimpleGroup (G ⧸ M)] (hnc : ∃ a b : G ⧸ M, a * b ≠ b * a) {p : ℕ} [Fact p.Prime]
    (hN : IsPGroup p N) : N ≤ M := by
  have : (N.map (QuotientGroup.mk' M)).Normal :=
    Subgroup.Normal.map ‹_› _ (QuotientGroup.mk'_surjective M)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' M)) with hb | ht
  · intro x hx
    have : ((x : G) : G ⧸ M) ∈ N.map (QuotientGroup.mk' M) := ⟨x, hx, rfl⟩
    rw [hb, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at this
    exact this
  · exfalso
    have hP : IsPGroup p (G ⧸ M) := by
      have h1 := hN.map (QuotientGroup.mk' M)
      rw [ht] at h1
      exact h1.of_equiv Subgroup.topEquiv
    have : Nontrivial (Subgroup.center (G ⧸ M)) := hP.center_nontrivial
    rw [center_eq_bot_of_simple_of_not_comm hnc] at this
    exact ((Subgroup.nontrivial_iff_ne_bot _).mp this) rfl

theorem le_or_le_of_inf_le {N₁ N₂ M : Subgroup G} [N₁.Normal] [N₂.Normal] [M.Normal]
    [IsSimpleGroup (G ⧸ M)] (hnc : ∃ a b : G ⧸ M, a * b ≠ b * a) (h : N₁ ⊓ N₂ ≤ M) :
    N₁ ≤ M ∨ N₂ ≤ M := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h₁, h₂⟩ := hcon
  have himg : ∀ (N : Subgroup G), N.Normal → ¬ N ≤ M → N.map (QuotientGroup.mk' M) = ⊤ := by
    intro N hNn hN
    have : (N.map (QuotientGroup.mk' M)).Normal := hNn.map _ (QuotientGroup.mk'_surjective M)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' M)) with hb | ht
    · exfalso
      apply hN
      intro x hx
      have : ((x : G) : G ⧸ M) ∈ N.map (QuotientGroup.mk' M) := ⟨x, hx, rfl⟩
      rw [hb, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at this
      exact this
    · exact ht
  obtain ⟨a, b, hab⟩ := hnc
  apply hab
  have ha : a ∈ N₁.map (QuotientGroup.mk' M) := by rw [himg N₁ inferInstance h₁]; exact mem_top a
  have hb : b ∈ N₂.map (QuotientGroup.mk' M) := by rw [himg N₂ inferInstance h₂]; exact mem_top b
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  have hc₁ : x * y * x⁻¹ * y⁻¹ ∈ N₁ := by
    rw [mul_assoc, mul_assoc]
    exact mul_mem hx (by rw [← mul_assoc]; exact ‹N₁.Normal›.conj_mem _ (inv_mem hx) y)
  have hc₂ : x * y * x⁻¹ * y⁻¹ ∈ N₂ :=
    mul_mem (‹N₂.Normal›.conj_mem y hy x) (inv_mem hy)
  have hc : x * y * x⁻¹ * y⁻¹ ∈ M := h ⟨hc₁, hc₂⟩
  have hc' : ((x * y * x⁻¹ * y⁻¹ : G) : G ⧸ M) = 1 := (QuotientGroup.eq_one_iff _).mpr hc
  simp only [QuotientGroup.mk'_apply]
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.mk_inv] at hc'
  calc (x : G ⧸ M) * (y : G ⧸ M) =
      ((x : G ⧸ M) * (y : G ⧸ M) * (x : G ⧸ M)⁻¹ * (y : G ⧸ M)⁻¹) * ((y : G ⧸ M) * (x : G ⧸ M)) := by
        group
    _ = (y : G ⧸ M) * (x : G ⧸ M) := by rw [hc', one_mul]

end Simple

section Two

variable {C : Type*} [Group C] [Finite C] {L : Type*} [Field L]

theorem readsThrough_of_three (fp : MulAut C →* (L ≃+* L)) {X : Subgroup C} {Y : Type*}
    [Group Y] [IsSimpleGroup Y] (hnc : ∃ a b : Y, a * b ≠ b * a)
    {R : MulAut Y → (L ≃+* L) → Prop} (N₁ N₂ N₃ : Subgroup ↥X) [N₁.Normal] [N₂.Normal]
    [N₃.Normal] (h123 : IsPGroup 2 ↥(N₁ ⊓ N₂ ⊓ N₃))
    (hq : ∀ N ∈ ({N₁, N₂, N₃} : Set (Subgroup ↥X)),
      ∀ M : Subgroup ↥X, M.Normal → N ≤ M → M = N ∨ M = ⊤)
    (hr : ∀ (N : Subgroup ↥X) [N.Normal], N ∈ ({N₁, N₂, N₃} : Set (Subgroup ↥X)) →
      ∀ (ε : ↥X ⧸ N ≃* Y) (β : MulAut C) (hβ : ∀ x ∈ X, β x ∈ X)
        (hN : ∀ m ∈ N, restrictAutOfMapsTo β X hβ m ∈ N),
        R ((ε.symm.trans (quotAutOfMapsTo N (restrictAutOfMapsTo β X hβ) hN)).trans ε) (fp β)) :
    ReadsThrough fp X Y R := by
  intro M _ ε β hβ hM
  have : IsSimpleGroup (↥X ⧸ M) := MulEquiv.isSimpleGroup ε
  have hnc' : ∃ a b : ↥X ⧸ M, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    refine ⟨ε.symm a, ε.symm b, fun h => hab ?_⟩
    have h' := congrArg ε h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinf : N₁ ⊓ N₂ ⊓ N₃ ≤ M := le_of_isPGroup_of_simple hnc' h123
  have hMtop : M ≠ ⊤ := by
    rintro rfl
    have hnt : Nontrivial (↥X ⧸ (⊤ : Subgroup ↥X)) := IsSimpleGroup.toNontrivial
    exact (not_nontrivial_iff_subsingleton.mpr QuotientGroup.subsingleton_quotient_top) hnt
  have key : ∀ N : Subgroup ↥X, N.Normal → N ∈ ({N₁, N₂, N₃} : Set (Subgroup ↥X)) → N ≤ M →
      R ((ε.symm.trans (quotAutOfMapsTo M (restrictAutOfMapsTo β X hβ) hM)).trans ε) (fp β) := by
    intro N hNn hmem hNM
    rcases hq N hmem M inferInstance hNM with rfl | hM'
    · exact hr M hmem ε β hβ hM
    · exact absurd hM' hMtop
  rcases le_or_le_of_inf_le hnc' hinf with h | h
  · rcases le_or_le_of_inf_le hnc' h with h' | h'
    · exact key N₁ inferInstance (by simp) h'
    · exact key N₂ inferInstance (by simp) h'
  · exact key N₃ inferInstance (by simp) h

theorem eq_or_eq_top_of_simple_quotient {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    [IsSimpleGroup (G ⧸ N)] (M : Subgroup G) (hM : M.Normal) (hNM : N ≤ M) :
    M = N ∨ M = ⊤ := by
  have : (M.map (QuotientGroup.mk' N)).Normal := hM.map _ (QuotientGroup.mk'_surjective N)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map (QuotientGroup.mk' N)) with hb | ht
  · left
    refine le_antisymm (fun x hx => ?_) hNM
    have : ((x : G) : G ⧸ N) ∈ M.map (QuotientGroup.mk' N) := ⟨x, hx, rfl⟩
    rw [hb, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at this
    exact this
  · right
    rw [eq_top_iff]
    intro x _
    have : ((x : G) : G ⧸ N) ∈ M.map (QuotientGroup.mk' N) := by rw [ht]; exact mem_top _
    obtain ⟨y, hy, hyx⟩ := this
    have hxy : y⁻¹ * x ∈ N := QuotientGroup.eq.mp hyx
    have := mul_mem hy (hNM hxy)
    rwa [mul_inv_cancel_left] at this

end Two

end CFSG.SeitzReduction.OmegaPilot
