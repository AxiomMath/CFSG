module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitTData

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

theorem lit_mem_iff_of_simple {G : Type} [Group G] [Finite G] {M : Subgroup G} [M.Normal]
    (hs : IsSimpleGroup ↥M) (hC : centralizer (M : Set G) = ⊥) (σ : G ≃* G) :
    ∀ x, x ∈ M ↔ σ x ∈ M := by
  set M' : Subgroup G := M.map σ.toMonoidHom with hM'
  haveI : M'.Normal := Subgroup.Normal.map inferInstance σ.toMonoidHom σ.surjective
  have hcard : Nat.card M' = Nat.card M := Subgroup.card_map_of_injective σ.injective
  have hmem : ∀ x, x ∈ M' ↔ σ.symm x ∈ M := fun x => Subgroup.mem_map_equiv
  have hMM' : M = M' := by
    haveI : (M ⊓ M').Normal := inferInstance
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((M ⊓ M').subgroupOf M) with h | h
    · exfalso
      have hinf : ∀ x, x ∈ M → x ∈ M' → x = 1 := by
        intro x hxM hxM'
        have hx : (⟨x, hxM⟩ : ↥M) ∈ (M ⊓ M').subgroupOf M :=
          Subgroup.mem_subgroupOf.mpr ⟨hxM, hxM'⟩
        rw [h, Subgroup.mem_bot] at hx
        exact congrArg Subtype.val hx
      have hcomm : ∀ x ∈ M', ∀ m ∈ M, m * x = x * m := by
        intro x hx m hm
        have h1 : x * m * x⁻¹ * m⁻¹ ∈ M := M.mul_mem (Normal.conj_mem inferInstance m hm x)
          (M.inv_mem hm)
        have h2 : x * (m * x⁻¹ * m⁻¹) ∈ M' :=
          M'.mul_mem hx (Normal.conj_mem inferInstance x⁻¹ (M'.inv_mem hx) m)
        have h3 : x * m * x⁻¹ * m⁻¹ = 1 := hinf _ h1 (by simpa [mul_assoc] using h2)
        have h4 : x * m = m * x := by
          calc x * m = (x * m * x⁻¹ * m⁻¹) * (m * x) := by group
            _ = m * x := by rw [h3, one_mul]
        exact h4.symm
      have hbot : M' = ⊥ := by
        refine (Subgroup.eq_bot_iff_forall M').2 fun x hx => ?_
        have hxC : x ∈ centralizer (M : Set G) := fun m hm => hcomm x hx m hm
        rw [hC] at hxC
        exact hxC
      have h1 : Nat.card M = 1 := by rw [← hcard, hbot]; exact Subgroup.card_bot
      haveI : Subsingleton ↥M := (Nat.card_eq_one_iff_unique.mp h1).1
      haveI := hs.toNontrivial
      exact false_of_nontrivial_of_subsingleton ↥M
    · have hle : M ≤ M' := by
        have := Subgroup.subgroupOf_eq_top.mp h
        exact this.trans inf_le_right
      exact Subgroup.eq_of_le_of_card_ge hle hcard.le
  intro x
  have h := hmem (σ x)
  rw [MulEquiv.symm_apply_apply, ← hMM'] at h
  exact h.symm

theorem lit_restrict_one {G : Type} [Group G] {M : Subgroup G} [M.Normal]
    (hC : centralizer (M : Set G) = ⊥) (σ : G ≃* G) (hM : ∀ x, x ∈ M ↔ σ x ∈ M)
    (h1 : litRestrict σ M hM = 1) : ∀ x, σ x = x := by
  have hfix : ∀ m ∈ M, σ m = m := by
    intro m hm
    have := congrArg (fun φ : ↥M ≃* ↥M => (φ ⟨m, hm⟩ : G)) h1
    simpa [litRestrict_coe] using this
  intro g
  have hcomm : ∀ m ∈ M, m * (g⁻¹ * σ g) = (g⁻¹ * σ g) * m := by
    intro m hm
    have hgm : g * m * g⁻¹ ∈ M := Normal.conj_mem inferInstance m hm g
    have h2 := hfix _ hgm
    rw [map_mul, map_mul, map_inv, hfix m hm] at h2
    calc m * (g⁻¹ * σ g) = g⁻¹ * (g * m * g⁻¹) * σ g := by group
      _ = g⁻¹ * (σ g * m * (σ g)⁻¹) * σ g := by rw [h2]
      _ = (g⁻¹ * σ g) * m := by group
  have hc : g⁻¹ * σ g ∈ centralizer (M : Set G) := fun m hm => hcomm m hm
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact hc.symm

theorem lit_card_le_mulAut {G : Type} [Group G] [Finite G] {M : Subgroup G} [M.Normal]
    (hC : centralizer (M : Set G) = ⊥) : Nat.card G ≤ Nat.card (MulAut ↥M) := by
  haveI : Finite (MulAut ↥M) :=
    Finite.of_injective (fun α : MulAut ↥M => (α : ↥M → ↥M)) DFunLike.coe_injective
  refine Nat.card_le_card_of_injective (MulAut.conjNormal (H := M)) ?_
  rw [injective_iff_map_eq_one]
  intro g hg
  have hcomm : ∀ m ∈ M, m * g = g * m := by
    intro m hm
    have := congrArg (fun φ : MulAut ↥M => (φ ⟨m, hm⟩ : G)) hg
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    have h2 : g * m = m * g := by
      calc g * m = (g * m * g⁻¹) * g := by group
        _ = m * g := by rw [this]
    exact h2.symm
  have hgC : g ∈ centralizer (M : Set G) := fun m hm => hcomm m hm
  rw [hC] at hgC
  exact hgC

theorem lit_mem_of_pow_nine {G : Type} [Group G] [Finite G] {M : Subgroup G} [M.Normal]
    (hcard : Nat.card G ≤ 2 * Nat.card ↥M) {x : G} (hx : x ^ 9 = 1) : x ∈ M := by
  have hmul : Nat.card G = Nat.card (G ⧸ M) * Nat.card M :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup M
  have hMpos : 0 < Nat.card M := Nat.card_pos
  have hQpos : 0 < Nat.card (G ⧸ M) := Nat.card_pos
  have hle : Nat.card (G ⧸ M) ≤ 2 := by
    by_contra hlt
    rw [not_le] at hlt
    have : 3 * Nat.card M ≤ Nat.card (G ⧸ M) * Nat.card M :=
      Nat.mul_le_mul_right _ hlt
    omega
  have h9 : (QuotientGroup.mk x : G ⧸ M) ^ 9 = 1 := by
    rw [← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one]
  have hc : (QuotientGroup.mk x : G ⧸ M) ^ Nat.card (G ⧸ M) = 1 := pow_card_eq_one'
  have hcop : Nat.Coprime 9 (Nat.card (G ⧸ M)) := by
    interval_cases h : Nat.card (G ⧸ M) <;> decide
  have : (QuotientGroup.mk x : G ⧸ M) = 1 := by
    have h1 := orderOf_dvd_of_pow_eq_one h9
    have h2 := orderOf_dvd_of_pow_eq_one hc
    have := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    exact orderOf_eq_one_iff.mp this
  exact (QuotientGroup.eq_one_iff x).mp this

theorem lit_outer_reduce {G : Type} [Group G] [Finite G] {M : Subgroup G} [M.Normal]
    (hs : IsSimpleGroup ↥M) (hC : centralizer (M : Set G) = ⊥)
    (hcard : Nat.card (MulAut ↥M) ≤ 2 * Nat.card ↥M) (σ : G ≃* G)
    (hσ2 : ∀ x, σ (σ x) = x) (hσ1 : ∃ x, σ x ≠ x) :
    ∃ α : MulAut ↥M, α * α = 1 ∧ α ≠ 1 ∧ ∀ P : Subgroup G, Nat.card P = 9 → P ≤ litFixSub σ →
      ∃ P' : Subgroup ↥M, Nat.card P' = 9 ∧ ∀ x ∈ P', α x = x := by
  have hM : ∀ x, x ∈ M ↔ σ x ∈ M := lit_mem_iff_of_simple hs hC σ
  refine ⟨litRestrict σ M hM, ?_, ?_, ?_⟩
  · apply MulEquiv.ext
    intro x
    apply Subtype.ext
    simp only [MulAut.mul_apply, MulAut.one_apply, litRestrict_coe]
    exact hσ2 x
  · intro h
    obtain ⟨x, hx⟩ := hσ1
    exact hx (lit_restrict_one hC σ hM h x)
  · intro P hP9 hPle
    have hGM : Nat.card G ≤ 2 * Nat.card ↥M := (lit_card_le_mulAut hC).trans hcard
    have hPM : P ≤ M := by
      intro x hx
      apply lit_mem_of_pow_nine hGM
      have h1 : (⟨x, hx⟩ : ↥P) ^ Nat.card ↥P = 1 := pow_card_eq_one'
      rw [hP9] at h1
      simpa using congrArg (fun y : ↥P => (y : G)) h1
    refine ⟨P.subgroupOf M, ?_, ?_⟩
    · rw [← hP9]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv
    · intro x hx
      apply Subtype.ext
      rw [litRestrict_coe]
      exact hPle (Subgroup.mem_subgroupOf.mp hx)

end CFSG.OddStandard.HigherRank.YamadaG23
