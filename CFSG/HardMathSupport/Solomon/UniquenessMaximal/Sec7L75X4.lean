module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs7
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.LocalAnalysis.GLTheoremB.GammaBasic

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem gLBConj_le_iff (g : G) (H T : Subgroup G) :
    GLBConj g H ≤ T ↔ H ≤ GLBConj g⁻¹ T := by
  constructor
  · intro h
    have := gLBConj_mono g⁻¹ h
    rwa [gLBConj_inv_gLBConj] at this
  · intro h
    have := gLBConj_mono g h
    rwa [gLBConj_gLBConj_inv] at this

omit [Finite G] in
theorem le_normalizer_normalClosure {B K0 L : Subgroup G}
    (hK0 : B ≤ Subgroup.normalizer (K0 : Set G)) (hL : B ≤ Subgroup.normalizer (L : Set G)) :
    B ≤ Subgroup.normalizer ((⨆ g ∈ L, GLBConj g K0 : Subgroup G) : Set G) := by
  have key : ∀ b ∈ B, GLBConj b (⨆ g ∈ L, GLBConj g K0) ≤ ⨆ g ∈ L, GLBConj g K0 := by
    intro b hb
    rw [gLBConj_le_iff]
    refine iSup₂_le fun g hg => ?_
    rw [← gLBConj_le_iff, gLBConj_gLBConj]
    have hg' : b⁻¹ * g * b⁻¹⁻¹ ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (hL (B.inv_mem hb)) g).1 hg
      exact this
    have hgb : g * b = b * (b⁻¹ * g * b) := by group
    have hg'' : b⁻¹ * g * b ∈ L := by simpa using hg'
    have e : GLBConj (g * b) K0 = GLBConj (b⁻¹ * g * b) K0 := by
      rw [hgb, ← gLBConj_gLBConj, gLBConj_eq_of_mem_normalizer (hK0 hb)]
    rw [e]
    exact le_iSup₂ (f := fun g _ => GLBConj g K0) (b⁻¹ * g * b) hg''
  intro b hb
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm (key b hb) ?_
  have h2 := (gLBConj_le_iff b⁻¹ _ _).1 (key b⁻¹ (B.inv_mem hb))
  rwa [inv_inv] at h2

omit [Finite G] in
private theorem centralizer_zpowers_eq (x : G) :
    Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
  ext z
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq, SetLike.mem_coe]
  constructor
  · intro h
    exact h x (Subgroup.mem_zpowers x)
  · intro h y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_left (show Commute x z from h) n).eq

omit [Finite G] in
private theorem exists_pow_of_mem_zpowers {x : G} (hx3 : x ^ 3 = 1) {e : G}
    (he : e ∈ Subgroup.zpowers x) : e = 1 ∨ e = x ∨ e = x * x := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
  have h1 : x ^ n = x ^ (n % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv n 3, zpow_add, zpow_mul]
    have : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
    rw [this, one_zpow, mul_one]
  have h2 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h2 with h | h | h
  · left; rw [h1, h]; simp
  · right; left; rw [h1, h]; simp
  · right; right; rw [h1, h]; simp [pow_two]

omit [Finite G] in
private theorem glaPComponent_ne_bot {p : ℕ} {X J : Subgroup G} (hJ : GLAPComponent p X J) :
    J ≠ ⊥ := by
  intro h
  have hq := hJ.2.2.1.2.2
  change CFSG.Open.IsQuasisimple ↥((J.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p X)))
    at hq
  rw [h, Subgroup.bot_subgroupOf, Subgroup.map_bot] at hq
  exact (Subgroup.nontrivial_iff_ne_bot _).1
    (CFSG.ComponentClassification.Quasisimple.nontrivial hq) rfl

theorem dichotomy_of_input18_3_4 (i : Input18_3_4) {N : Subgroup G} (hN : CFSG.Open.IsKGroup ↥N)
    {x : G} (hxN : x ∈ N) (hx3 : x ^ 3 = 1) {J : Subgroup G}
    (hJ : GLAPComponent 3 (N ⊓ Subgroup.centralizer ({x} : Set G)) J) :
    (∃ L : Subgroup G, GLAPComponent 3 N L ∧ J ≤ L ∧
        (⨆ g ∈ GLAPLayer 3 N, GLBConj g J) = L ∧ GLBConj x L = L) ∨
    (∃ L₁ L₂ L₃ : Subgroup G, GLAPComponent 3 N L₁ ∧ GLAPComponent 3 N L₂ ∧
        GLAPComponent 3 N L₃ ∧ L₁ ≠ L₂ ∧ L₂ ≠ L₃ ∧ L₃ ≠ L₁ ∧ GLBConj x L₁ = L₂ ∧
        GLBConj x L₂ = L₃ ∧ GLBConj x L₃ = L₁ ∧
        (⨆ g ∈ GLAPLayer 3 N, GLBConj g J) = L₁ ⊔ L₂ ⊔ L₃ ∧ J ≤ L₁ ⊔ L₂ ⊔ L₃) := by
  have hE : IsElemAbelian 3 (Subgroup.zpowers x) := by
    refine ⟨inferInstance, fun y hy => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
    simp [this]
  have hEN : Subgroup.zpowers x ≤ N := (Subgroup.zpowers_le).2 hxN
  have hJ' : GLAPComponent 3
      (N ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)) J := by
    rwa [centralizer_zpowers_eq]
  obtain ⟨C, hC1, hC2, hC3, hC4⟩ :=
    i G N hN 3 Nat.prime_three (Subgroup.zpowers x) hEN hE J hJ'
  have hJI : J ≤ ⨆ g ∈ GLAPLayer 3 N, GLBConj g J := by
    have := le_iSup₂ (f := fun g (_ : g ∈ GLAPLayer 3 N) => GLBConj g J) 1 (one_mem _)
    rwa [gLBConj_one] at this
  have hCne : ∃ L₁, L₁ ∈ C := by
    by_contra hne
    push Not at hne
    rw [← hC2] at hJI
    have : (⨆ L ∈ C, L) = ⊥ := by
      simp only [iSup_eq_bot]
      exact fun L hL => (hne L hL).elim
    rw [this] at hJI
    exact glaPComponent_ne_bot hJ (le_bot_iff.1 hJI)
  obtain ⟨L₁, hL₁⟩ := hCne
  have hcl : ∀ L ∈ C, L = L₁ ∨ L = GLBConj x L₁ ∨ L = GLBConj x (GLBConj x L₁) := by
    intro L hL
    obtain ⟨e, he, rfl⟩ := hC4 L₁ hL₁ L hL
    rcases exists_pow_of_mem_zpowers hx3 he with rfl | rfl | rfl
    · left; exact gLBConj_one _
    · right; left; rfl
    · right; right; rw [gLBConj_gLBConj]
  have hx_mem : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
  by_cases hfix : GLBConj x L₁ = L₁
  · left
    have hall : ∀ L ∈ C, L = L₁ := by
      intro L hL
      rcases hcl L hL with h | h | h
      · exact h
      · rw [h, hfix]
      · rw [h, hfix, hfix]
    have hsup : (⨆ L ∈ C, L) = L₁ :=
      le_antisymm (iSup₂_le fun L hL => (hall L hL).le) (le_iSup₂ (f := fun L (_ : L ∈ C) => L) L₁ hL₁)
    refine ⟨L₁, hC1 L₁ hL₁, ?_, by rw [← hC2, hsup], hfix⟩
    rw [← hsup, hC2]; exact hJI
  · right
    set L₂ := GLBConj x L₁ with hL₂
    set L₃ := GLBConj x L₂ with hL₃
    have hL₂C : L₂ ∈ C := hC3 L₁ hL₁ x hx_mem
    have hL₃C : L₃ ∈ C := hC3 L₂ hL₂C x hx_mem
    have h31 : GLBConj x L₃ = L₁ := by
      rw [hL₃, hL₂, gLBConj_gLBConj, gLBConj_gLBConj,
        show x * (x * x) = x ^ 3 by simp [pow_succ, mul_assoc], hx3, gLBConj_one]
    have h21 : L₂ ≠ L₁ := hfix
    have h31' : L₃ ≠ L₁ := by
      intro h
      apply hfix
      rw [← h31, h]
    have h23 : L₂ ≠ L₃ := by
      intro h
      apply h21
      have : L₃ = L₂ := h.symm
      rw [← h31, this]
      exact h
    have hsup : (⨆ L ∈ C, L) = L₁ ⊔ L₂ ⊔ L₃ := by
      refine le_antisymm (iSup₂_le fun L hL => ?_) ?_
      · rcases hcl L hL with h | h | h
        · rw [h]; exact le_sup_left.trans le_sup_left
        · rw [h]; exact le_sup_right.trans le_sup_left
        · rw [h]; exact le_sup_right
      · exact sup_le (sup_le (le_iSup₂ (f := fun L (_ : L ∈ C) => L) L₁ hL₁)
          (le_iSup₂ (f := fun L (_ : L ∈ C) => L) L₂ hL₂C))
          (le_iSup₂ (f := fun L (_ : L ∈ C) => L) L₃ hL₃C)
    refine ⟨L₁, L₂, L₃, hC1 L₁ hL₁, hC1 L₂ hL₂C, hC1 L₃ hL₃C, h21.symm, h23, h31', rfl, rfl, h31,
      by rw [← hC2, hsup], ?_⟩
    rw [← hsup, hC2]; exact hJI

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
