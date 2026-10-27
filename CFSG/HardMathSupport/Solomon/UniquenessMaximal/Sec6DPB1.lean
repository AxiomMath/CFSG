module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DCore
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DPhase2

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem normalizer_core (p : ℕ) {X : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (GLAPPrimeCoreOf p X : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at hg ⊢
  rw [← glaPPrimeCoreOf_gLBConj, hg]

theorem inf_core_le (p : ℕ) {K X : Subgroup G} (hKX : K ≤ X) :
    K ⊓ GLAPPrimeCoreOf p X ≤ GLAPPrimeCoreOf p K := by
  set N : Subgroup ↥K := (K ⊓ GLAPPrimeCoreOf p X).subgroupOf K with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨?_, ?_⟩
    · simpa using K.mul_mem (K.mul_mem k.2 hn.1) (K.inv_mem k.2)
    · have hk := normalizer_core p (X := X) (Subgroup.le_normalizer (hKX k.2))
      have := (Subgroup.mem_normalizer_iff.1 hk (n : G)).1 hn.2
      simpa using this
  have hcop : Nat.Coprime p (Nat.card N) := by
    refine (coprime_card_core p X).coprime_dvd_right ?_
    have : Nat.card N = Nat.card ↥(K ⊓ GLAPPrimeCoreOf p X) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [this]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hle : N ≤ GLAPPrimeCore p ↥K := le_sSup ⟨hNn, hcop⟩
  have := Subgroup.map_mono (f := K.subtype) hle
  rw [hN, Subgroup.map_subgroupOf_eq_of_le inf_le_left] at this
  exact this

theorem barCenterX_gLBConj (p : ℕ) {X : Subgroup G} {g : G} (hg : g ∈ X) (T : Subgroup G) :
    barCenterX p X (GLBConj g T) =
      GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨g, hg⟩) (barCenterX p X T) := by
  set ĝ := QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨g, hg⟩ with hĝ
  have hb : barX p X (GLBConj g T) = GLBConj ĝ (barX p X T) := barX_gLBConj_of_mem p hg T
  ext ζ
  rw [mem_barCenterX_iff, mem_gLBConj, mem_barCenterX_iff, hb, mem_gLBConj]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun v hv => ?_⟩
    have hu : ĝ⁻¹ * v * ĝ ∈ GLBConj ĝ (barX p X T) := by
      rw [mem_gLBConj]; simpa [mul_assoc] using hv
    have := h2 _ hu
    have e : ĝ * (ĝ⁻¹ * v * ĝ) * ĝ⁻¹ = v := by group
    calc ĝ * ζ * ĝ⁻¹ * v = ĝ * (ζ * (ĝ⁻¹ * v * ĝ)) * ĝ⁻¹ := by group
      _ = ĝ * ((ĝ⁻¹ * v * ĝ) * ζ) * ĝ⁻¹ := by rw [this]
      _ = v * (ĝ * ζ * ĝ⁻¹) := by group
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun u hu => ?_⟩
    rw [mem_gLBConj] at hu
    have := h2 _ hu
    calc ζ * u = ĝ⁻¹ * ((ĝ * ζ * ĝ⁻¹) * (ĝ * u * ĝ⁻¹)) * ĝ := by group
      _ = ĝ⁻¹ * ((ĝ * u * ĝ⁻¹) * (ĝ * ζ * ĝ⁻¹)) * ĝ := by rw [this]
      _ = u * ζ := by group

omit [Finite G] in
theorem normalizer_Zc {R : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (R : Set G)) :
    g ∈ Subgroup.normalizer (Zc R : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at hg ⊢
  unfold Zc
  rw [gLBConj_inf, gLBConj_centralizer, hg]

section WFix

variable {Q : Type*} [Group Q] [Finite Q] {σ : Q} {R₁ : Subgroup Q}

namespace Triple

theorem Zc_le_W₁ : Zc R₁ ≤ W σ R₁ := le_sup_left.trans le_sup_left

theorem Zc_le_W₂ : Zc (cj σ R₁) ≤ W σ R₁ := le_sup_right.trans le_sup_left

theorem Zc_le_W₃ : Zc (cj σ (cj σ R₁)) ≤ W σ R₁ := le_sup_right

theorem isPGroup_W (h : Triple σ R₁) : IsPGroup 3 ↥(W σ R₁) := by
  intro g
  exact ⟨1, Subtype.ext (by simpa using h.exp3_R (W_le_R (σ := σ) (R₁ := R₁) g.2))⟩

theorem card_fix_W_le (h : Triple σ R₁) (hW : Nat.card (W σ R₁) ≤ 9) :
    Nat.card ↥(W σ R₁ ⊓ Subgroup.centralizer ({σ} : Set Q)) ≤ 3 := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hcen : W σ R₁ ≤ Subgroup.centralizer ({σ} : Set Q)
  · rw [inf_eq_left.2 hcen]
    have hz : ∀ z ∈ W σ R₁, σ⁻¹ * z * σ = z := by
      intro z hz
      have := Subgroup.mem_centralizer_singleton_iff.1 (hcen hz)
      calc σ⁻¹ * z * σ = σ⁻¹ * (z * σ) := by group
        _ = σ⁻¹ * (σ * z) := by rw [this]
        _ = z := by group
    have h2 : Zc (cj σ R₁) ≤ Zc R₁ := by
      intro z hzz
      have hzW := Zc_le_W₂ hzz
      rw [Zc_cj, mem_cj, hz z hzW] at hzz
      exact hzz
    have h3 : Zc (cj σ (cj σ R₁)) ≤ Zc R₁ := by
      intro z hzz
      have hzW := Zc_le_W₃ hzz
      rw [Zc_cj, mem_cj, hz z hzW] at hzz
      exact h2 hzz
    have hWe : W σ R₁ = Zc R₁ := le_antisymm (sup_le (sup_le le_rfl h2) h3) Zc_le_W₁
    rw [hWe]
    exact h.heis.card_Zc.le
  · set C := W σ R₁ ⊓ Subgroup.centralizer ({σ} : Set Q) with hC
    have hCW : C ≤ W σ R₁ := inf_le_left
    have hCp : IsPGroup 3 ↥C := h.isPGroup_W.to_le hCW
    have hlt : Nat.card C < Nat.card (W σ R₁) := by
      by_contra hge
      push Not at hge
      exact hcen (Subgroup.eq_of_le_of_card_ge hCW hge ▸ inf_le_right)
    obtain ⟨i, hi⟩ := exists_card_eq_pow hCp
    by_contra hgt
    push Not at hgt
    have hi2 : 2 ≤ i := by
      by_contra hlt2
      push Not at hlt2
      have : 3 ^ i ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : 3 ^ 2 ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) hi2
    omega

end Triple

end WFix

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
