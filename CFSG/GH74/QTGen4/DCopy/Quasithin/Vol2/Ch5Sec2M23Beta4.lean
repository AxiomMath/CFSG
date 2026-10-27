module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23Beta4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2M23GxNorm

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.Blueprint CFSG.M23Pair CFSG.Monster.B.Classical.Plane CFSG.Fischer
  CFSG.Quasithin.Asc94 CFSG.ComponentClassification.WittDesign
  CFSG.EvenSmallLie.UnitarySix.MathieuExt CFSG.Open CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Vol2Native.L239
open scoped Pointwise Matrix

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem exists_beta4_F4
    (h526 : Stmt5_2_6_F4) (h527 : Stmt5_2_7_F4) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz_F4)
    (hU4 : Stmt5_2_8_U4_F4) (hsp : Stmt5_2_8_special_F4) (hQ : Stmt5_2_8_Q_F4)
    (hset : Stmt5_2_10_setting_F4) (hfus : M23Fusion3_F4) (h515 : Stmt5_2_15_F4) (h516 : Stmt5_2_16_F4)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) :
    ∃ β₄ : ↥(m23Gx T M L H B D) ≃* ↥Gbar,
      (∀ g : ↥(m23Gx T M L H B D),
        (g : G) ∈ m23G0 M L H B D ↔ (β₄ g : ↥NativeSporadic.M23) ∈ fix21) ∧
      (∀ g : ↥(m23Gx T M L H B D), (g : G) ∈ L → (β₄ g : ↥NativeSporadic.M23) ∈ Lbar) ∧
      (∀ g : ↥(m23Gx T M L H B D), (g : G) ∈ M2 → (β₄ g : ↥NativeSporadic.M23) ∈ M2bar) := by
  classical
  set G0 := m23G0 M L H B D with hG0def
  set Gx := m23Gx T M L H B D with hGxdef
  obtain ⟨ρ, t₁, A, ht₁, hρinj, ht₁T, ht₁G0, hsplit, hρG0, hρt, hdetA, hρU, hρV, hcard⟩ :=
    exists_rho_normalized_F4 h526 h527 h1284 hSz hU4 hsp hQ hset hfus h515 h516 hyp hM23 hS
  have hLG0 : L ≤ G0 := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hKG0 : oTwoUpper H ≤ G0 := le_sup_right.trans le_sup_right
  have hG0Gx : G0 ≤ Gx := le_sup_left
  obtain ⟨-, hU16, -⟩ := hQ G T M L V H B D L₂ n M2 hyp hM23 hS.K_lt hS.maximal hS.excA7
  obtain ⟨-, -, h16, -, -⟩ := setting_L_facts_F4 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  obtain ⟨-, -, hQeq, -, -⟩ := setting_K_facts_F4 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hUK : pCoreOf 2 M2 ≤ oTwoUpper H := hQeq ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hUGx : pCoreOf 2 M2 ≤ Gx := hUK.trans (hKG0.trans hG0Gx)
  have hVGx : pCoreOf 2 L ≤ Gx := (CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans (hLG0.trans hG0Gx)

  have himg : ∀ (X : Subgroup G) (E : Subgroup (Equiv.Perm (Fin 21))), X ≤ Gx →
      Nat.card X = 16 → Nat.card E = 16 →
      (∀ (g : G) (hg : g ∈ Gx), g ∈ X → ρ ⟨g, hg⟩ ∈ E) →
      ∀ p ∈ E, ∃ (g : G) (hg : g ∈ Gx), g ∈ X ∧ ρ ⟨g, hg⟩ = p := by
    intro X E hXGx hX16 hE16 hXE p hp
    have hle : (X.subgroupOf Gx).map ρ ≤ E := by
      rintro _ ⟨g, hg, rfl⟩
      exact hXE g g.2 (Subgroup.mem_subgroupOf.mp hg)
    have hc : Nat.card ↥((X.subgroupOf Gx).map ρ) = 16 := by
      have h1 := Subgroup.card_map_of_injective (K := X.subgroupOf Gx) hρinj
      rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXGx).toEquiv, hX16]
    have heq : (X.subgroupOf Gx).map ρ = E := Subgroup.eq_of_le_of_card_ge hle (by
      rw [hE16, hc])
    rw [← heq] at hp
    obtain ⟨g, hg, rfl⟩ := hp
    exact ⟨g, g.2, Subgroup.mem_subgroupOf.mp hg, rfl⟩
  have hUEa := himg _ Ea hUGx hU16 card_Ea hρU
  have hVEc := himg _ Ec hVGx h16 card_Ec hρV

  have hτ : planePerm (semΓ A frobF4) * (psiBar sbarG)⁻¹ ∈ P0 := by
    rw [psiBar_sbar]
    exact planePerm_mul_inv_mem A A0GL (by rw [hdetA, det_A0GL])
  have hrange : ∀ g : ↥Gx, ρ g ∈ psiBar.range := by
    intro g
    rcases hsplit g g.2 with hg | hg
    · have h1 := hρG0 g g.2 hg
      rw [← map_fix21_eq_P0] at h1
      obtain ⟨x, -, hx⟩ := h1
      exact ⟨x, hx⟩
    · have hgt : (g : G) * t₁⁻¹ ∈ Gx := Gx.mul_mem g.2 (Gx.inv_mem ht₁)
      have e1 : g = ⟨(g : G) * t₁⁻¹, hgt⟩ * ⟨t₁, ht₁⟩ := Subtype.ext (by simp)
      have h1 := hρG0 _ hgt hg
      have h2 : ρ ⟨(g : G) * t₁⁻¹, hgt⟩ * (planePerm (semΓ A frobF4) * (psiBar sbarG)⁻¹) ∈
          psiBar.range := by
        rw [← map_fix21_eq_P0] at h1
        obtain ⟨x, -, hx⟩ := h1
        rw [← map_fix21_eq_P0] at hτ
        obtain ⟨y, -, hy⟩ := hτ
        exact ⟨x * y, by rw [map_mul, hx, hy]⟩
      rw [e1, map_mul, hρt]
      have h3 := psiBar.range.mul_mem h2 ⟨sbarG, rfl⟩
      rwa [mul_assoc, mul_assoc, inv_mul_cancel, mul_one] at h3

  set β : ↥Gx →* ↥Gbar :=
    (MonoidHom.ofInjective psiBar_injective).symm.toMonoidHom.comp (ρ.codRestrict _ hrange)
    with hβ
  have hpsiβ : ∀ g, psiBar (β g) = ρ g := by
    intro g
    have h := MulEquiv.apply_symm_apply (MonoidHom.ofInjective psiBar_injective)
      (ρ.codRestrict _ hrange g)
    exact congrArg Subtype.val h
  have hβinj : Function.Injective β := by
    intro x y hxy
    apply hρinj
    rw [← hpsiβ, ← hpsiβ, hxy]
  have hβbij : Function.Bijective β := by
    refine hβinj.bijective_of_nat_card_le ?_
    rw [card_Gbar, hcard]
  set β₄ := MulEquiv.ofBijective β hβbij with hβ₄
  have hpsiβ₄ : ∀ g, psiBar (β₄ g) = ρ g := hpsiβ
  refine ⟨β₄, fun g => ?_, fun g hg => ?_, fun g hg => ?_⟩
  · rw [← psiBar_mem_P0_iff, hpsiβ₄]
    constructor
    · exact hρG0 g g.2
    · intro hP
      by_contra hg
      rcases hsplit g g.2 with h | h
      · exact hg h
      · have hgt : (g : G) * t₁⁻¹ ∈ Gx := Gx.mul_mem g.2 (Gx.inv_mem ht₁)
        have e1 : g = ⟨(g : G) * t₁⁻¹, hgt⟩ * ⟨t₁, ht₁⟩ := Subtype.ext (by simp)
        have h1 := hρG0 _ hgt h
        rw [e1, map_mul, hρt] at hP
        apply planePerm_semΓ_frob_not_mem A
        have := P0.mul_mem (P0.inv_mem h1) hP
        rwa [inv_mul_cancel_left] at this
  ·
    have h5 : ρ g 5 = 5 := by
      apply apply_five_of_normalizes_Ec
      intro p hp
      obtain ⟨v, hv, hvV, rfl⟩ := hVEc p hp
      have hgvg : (g : G) * v * (g : G)⁻¹ ∈ pCoreOf 2 L := by
        have hLN : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
          Subgroup.le_normalizer.trans
            (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
        exact (Subgroup.mem_normalizer_iff.mp (hLN hg) v).mp hvV
      have e1 : ρ g * ρ ⟨v, hv⟩ * (ρ g)⁻¹ = ρ ⟨(g : G) * v * (g : G)⁻¹, hVGx hgvg⟩ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e1]
      exact hρV _ _ hgvg
    have hfix := (psiBar_mem_P0_iff (β₄ g)).mp (by rw [hpsiβ₄]; exact hρG0 g g.2 (hLG0 hg))
    obtain ⟨h21, h22⟩ := mem_fix21_iff.mp hfix
    refine mem_Lbar_iff.mpr ⟨?_, h21, h22⟩
    have e2 := lam_psiBar (β₄ g) 5
    rw [hpsiβ₄, h5, lam_five] at e2
    exact e2.symm
  ·
    apply mem_M2bar_of_psiBar
    intro p hp
    rw [hpsiβ₄]
    refine mem_projLine_zero_of_normalizes_Ea (fun e he => ?_) hp
    obtain ⟨u, hu, huU, rfl⟩ := hUEa e he
    have hgug : (g : G)⁻¹ * u * (g : G) ∈ pCoreOf 2 M2 := by
      have hMN : M2 ≤ Subgroup.normalizer (pCoreOf 2 M2 : Set G) :=
        Subgroup.le_normalizer.trans
          (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M2)
      have := (Subgroup.mem_normalizer_iff.mp (hMN (M2.inv_mem hg)) u).mp huU
      simpa using this
    have e1 : (ρ g)⁻¹ * ρ ⟨u, hu⟩ * ρ g = ρ ⟨(g : G)⁻¹ * u * (g : G), hUGx hgug⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e1]
    exact hρU _ _ hgug

end CFSG.Quasithin.H13
