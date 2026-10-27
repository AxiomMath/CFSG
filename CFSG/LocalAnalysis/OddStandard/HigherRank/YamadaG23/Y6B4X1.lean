module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4X0
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4N2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4S
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y55

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y6b_M3_conj_forms (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hF : c.Facts5)
    (hRT : c.s.R ≠ c.s.T) {m : G} (hm : m ∈ M3 c.s) :
    m * c.g * m⁻¹ = c.g ∧
      (∀ f ∈ c.s.fr.F, m * f * m⁻¹ = f) ∧
      (∃ f ∈ c.s.fr.F, m * c.s.t * m⁻¹ = f * c.s.t) := by
  haveI := y6e_M3_comm c hF
  have hgm : c.g * m * c.g⁻¹ = m := hF.2.2.2.1 hRT m hm
  refine ⟨?_, ?_, ?_⟩
  · have hcomm : c.g * m = m * c.g := by
      calc c.g * m = (c.g * m * c.g⁻¹) * c.g := by group
        _ = m * c.g := by rw [hgm]
    calc m * c.g * m⁻¹ = c.g * m * m⁻¹ := by rw [hcomm]
      _ = c.g := by group
  · intro f hf
    have hfM : f ∈ M3 c.s := (le_sup_right : c.s.fr.F ≤ M3 c.s) hf
    have hcomm : m * f = f * m := mul_comm_of_mem_isMulCommutative (M3 c.s) hm hfM
    calc m * f * m⁻¹ = f * m * m⁻¹ := by rw [hcomm]
      _ = f := by group
  · have hmem : m * c.s.t * m⁻¹ ∈ conjClass (M3 c.s) c.s.t := ⟨m, hm, rfl⟩
    rw [y54_conjClass_M3 c hH] at hmem
    simpa only [Setting3.tCoset, Set.mem_setOf_eq] using hmem

private lemma y6b_NL_conj_forms (c : Ctx5 G L) (hH : F33Hyp c.s c.e)
    (hRT : c.s.R ≠ c.s.T) {n : G} (hn : n ∈ normIn L c.s.fr.F) :
    (∀ f ∈ c.s.fr.F, n * f * n⁻¹ ∈ c.s.fr.F) ∧
      (∃ f ∈ c.s.fr.F, n * c.g * n⁻¹ = f * c.g) ∧
      n * c.s.t * n⁻¹ = c.s.t := by
  obtain ⟨hnL, hnN⟩ := Subgroup.mem_inf.mp hn
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    exact (Subgroup.mem_set_normalizer_iff.mp hnN f).mp hf
  · set c₀ : G := ⁅c.g, n⁆ with hc₀
    have hc₀F : c₀ ∈ c.s.fr.F := by
      rw [hc₀]
      exact y55_g_comm_NL c hH hRT n hn
    refine ⟨c₀⁻¹, (c.s.fr.F).inv_mem hc₀F, ?_⟩
    have hgn : c.g * n * c.g⁻¹ = c₀ * n := by
      rw [hc₀, commutatorElement_def]
      group
    have h2 : c₀ * (n * c.g * n⁻¹) = c.g := by
      calc c₀ * (n * c.g * n⁻¹) = (c₀ * n) * c.g * n⁻¹ := by group
        _ = (c.g * n * c.g⁻¹) * c.g * n⁻¹ := by rw [← hgn]
        _ = c.g := by group
    calc n * c.g * n⁻¹ = c₀⁻¹ * (c₀ * (n * c.g * n⁻¹)) := by group
      _ = c₀⁻¹ * c.g := by rw [h2]
  · have hcomm : n * c.s.t = c.s.t * n :=
      Subgroup.mem_centralizer_iff.mp c.s.t_mem n hnL
    calc n * c.s.t * n⁻¹ = c.s.t * n * n⁻¹ := by rw [hcomm]
      _ = c.s.t := by group

private lemma y6b_NL_conj_mem_E (c : Ctx5 G L) (hH : F33Hyp c.s c.e)
    (hRT : c.s.R ≠ c.s.T) {n : G} (hn : n ∈ normIn L c.s.fr.F)
    {x : G} (hx : x ∈ y6bE c) : n * x * n⁻¹ ∈ y6bE c := by
  obtain ⟨hnF, ⟨f₀, hf₀, hng⟩, hnt⟩ := y6b_NL_conj_forms c hH hRT hn
  rw [y6b_mem_E c hH hRT] at hx ⊢
  obtain ⟨f, hf, hx1 | hx1 | hx1 | hx1⟩ := hx
  · rw [hx1]
    exact ⟨n * f * n⁻¹, hnF f hf, Or.inl rfl⟩
  · rw [hx1]
    refine ⟨n * f * n⁻¹ * f₀, mul_mem (hnF f hf) hf₀, Or.inr (Or.inl ?_)⟩
    calc n * (f * c.g) * n⁻¹
        = (n * f * n⁻¹) * (n * c.g * n⁻¹) := by group
      _ = (n * f * n⁻¹) * (f₀ * c.g) := by rw [hng]
      _ = (n * f * n⁻¹ * f₀) * c.g := by group
  · rw [hx1]
    refine ⟨n * f * n⁻¹, hnF f hf, Or.inr (Or.inr (Or.inl ?_))⟩
    calc n * (f * c.s.t) * n⁻¹
        = (n * f * n⁻¹) * (n * c.s.t * n⁻¹) := by group
      _ = (n * f * n⁻¹) * c.s.t := by rw [hnt]
  · rw [hx1]
    refine ⟨n * f * n⁻¹ * f₀, mul_mem (hnF f hf) hf₀, Or.inr (Or.inr (Or.inr ?_))⟩
    calc n * (f * (c.g * c.s.t)) * n⁻¹
        = (n * f * n⁻¹) * (n * c.g * n⁻¹) * (n * c.s.t * n⁻¹) := by group
      _ = (n * f * n⁻¹) * (f₀ * c.g) * c.s.t := by rw [hng, hnt]
      _ = (n * f * n⁻¹ * f₀) * (c.g * c.s.t) := by group

theorem y6b_M3_conj_E (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hF : c.Facts5)
    (hRT : c.s.R ≠ c.s.T) : ∀ m ∈ M3 c.s, ∀ x ∈ y6bE c, m * x * m⁻¹ ∈ y6bE c := by
  intro m hm x hx
  obtain ⟨hmg, hmf, f', hf', hmt⟩ := y6b_M3_conj_forms c hH hF hRT hm
  rw [y6b_mem_E c hH hRT] at hx ⊢
  obtain ⟨f, hf, hx1 | hx1 | hx1 | hx1⟩ := hx
  · rw [hx1]
    exact ⟨f, hf, Or.inl (hmf f hf)⟩
  · rw [hx1]
    refine ⟨f, hf, Or.inr (Or.inl ?_)⟩
    calc m * (f * c.g) * m⁻¹
        = (m * f * m⁻¹) * (m * c.g * m⁻¹) := by group
      _ = f * c.g := by rw [hmf f hf, hmg]
  · rw [hx1]
    refine ⟨f * f', mul_mem hf hf', Or.inr (Or.inr (Or.inl ?_))⟩
    calc m * (f * c.s.t) * m⁻¹
        = (m * f * m⁻¹) * (m * c.s.t * m⁻¹) := by group
      _ = f * (f' * c.s.t) := by rw [hmf f hf, hmt]
      _ = (f * f') * c.s.t := by group
  · rw [hx1]
    refine ⟨f * f', mul_mem hf hf', Or.inr (Or.inr (Or.inr ?_))⟩
    calc m * (f * (c.g * c.s.t)) * m⁻¹
        = (m * f * m⁻¹) * (m * c.g * m⁻¹) * (m * c.s.t * m⁻¹) := by group
      _ = f * c.g * (f' * c.s.t) := by rw [hmf f hf, hmg, hmt]
      _ = (f * f') * (c.g * c.s.t) := by
            have hgf' : c.g * f' = f' * c.g := y6b_g_comm_F c hH hRT f' hf'
            calc f * c.g * (f' * c.s.t) = f * (c.g * f') * c.s.t := by group
              _ = f * (f' * c.g) * c.s.t := by rw [hgf']
              _ = (f * f') * (c.g * c.s.t) := by group

theorem y6b_M3_le_X (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hF : c.Facts5)
    (hRT : c.s.R ≠ c.s.T) : M3 c.s ≤ y6bX c := by
  intro m hm
  change m ∈ normalizer ((y6bE c : Subgroup G) : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact y6b_M3_conj_E c hH hF hRT m hm x
  · intro hx
    have h := y6b_M3_conj_E c hH hF hRT m⁻¹ ((M3 c.s).inv_mem hm) (m * x * m⁻¹) hx
    rwa [show m⁻¹ * (m * x * m⁻¹) * (m⁻¹)⁻¹ = x from by group] at h

theorem y6b_NL_le_X (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    normIn L c.s.fr.F ≤ y6bX c := by
  intro n hn
  change n ∈ normalizer ((y6bE c : Subgroup G) : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact y6b_NL_conj_mem_E c hH hRT hn
  · intro hx
    have hn' : n⁻¹ ∈ normIn L c.s.fr.F := (normIn L c.s.fr.F).inv_mem hn
    have h := y6b_NL_conj_mem_E c hH hRT hn' hx
    rwa [show n⁻¹ * (n * x * n⁻¹) * (n⁻¹)⁻¹ = x from by group] at h

theorem y6b_T3_le_X (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hF : c.Facts5)
    (hRT : c.s.R ≠ c.s.T) : y6bT3 c ≤ y6bX c :=
  sup_le (y6b_T_le_X c hH hRT) (y6b_M3_le_X c hH hF hRT)

theorem y6b_X_conj_t (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hF : c.Facts5)
    (hRT : c.s.R ≠ c.s.T) :
    ∀ x ∈ y6bX c, ∃ e ∈ y6bE16 c, x * c.s.t * x⁻¹ = e * c.s.t := by
  intro x hx
  have hx' : x ∈ normalizer ((y6bE c : Subgroup G) : Set G) := hx
  have hxe : x * c.s.t * x⁻¹ ∈ y6bE c :=
    (Subgroup.mem_set_normalizer_iff.mp hx' c.s.t).mp (y6b_t_mem_E c)
  rw [y6b_mem_E c hH hRT] at hxe
  obtain ⟨f, hf, h | h | h | h⟩ := hxe
  · exact absurd h (y6b_not_conj_t c hH hF hRT x f (y6b_F_le_E16 c hf))
  · exact absurd h (y6b_not_conj_t c hH hF hRT x (f * c.g) (by
      rw [y6b_mem_E16 c hH hRT]
      exact ⟨f, hf, Or.inr rfl⟩))
  · exact ⟨f, y6b_F_le_E16 c hf, h⟩
  · refine ⟨f * c.g, ?_, ?_⟩
    · rw [y6b_mem_E16 c hH hRT]
      exact ⟨f, hf, Or.inr rfl⟩
    · rw [h]
      group
theorem y6b_conj_t_surj (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hF : c.Facts5)
    (hRT : c.s.R ≠ c.s.T) (h1 : Y6bHasX1 c) :
    ∀ e ∈ y6bE16 c, ∃ x ∈ y6bX c, x * c.s.t * x⁻¹ = e * c.s.t := by
  intro e he
  rw [y6b_mem_E16 c hH hRT] at he
  obtain ⟨f, hf, he1 | he1⟩ := he
  · rw [he1]
    obtain ⟨m, hm, hmt⟩ : ∃ m ∈ M3 c.s, m * c.s.t * m⁻¹ = f * c.s.t := by
      have hmem : f * c.s.t ∈ conjClass (M3 c.s) c.s.t := by
        rw [y54_conjClass_M3 c hH]
        exact ⟨f, hf, rfl⟩
      simp only [conjClass, Set.mem_setOf_eq] at hmem
      obtain ⟨m, hm, hmf⟩ := hmem
      exact ⟨m, hm, hmf.symm⟩
    exact ⟨m, y6b_M3_le_X c hH hF hRT hm, hmt⟩
  · rw [he1]
    obtain ⟨x₁, hx₁X, hx₁⟩ := h1
    obtain ⟨m, hm, hmt⟩ : ∃ m ∈ M3 c.s, m * c.s.t * m⁻¹ = f * c.s.t := by
      have hmem : f * c.s.t ∈ conjClass (M3 c.s) c.s.t := by
        rw [y54_conjClass_M3 c hH]
        exact ⟨f, hf, rfl⟩
      simp only [conjClass, Set.mem_setOf_eq] at hmem
      obtain ⟨m, hm, hmf⟩ := hmem
      exact ⟨m, hm, hmf.symm⟩
    obtain ⟨hmg, -, -⟩ := y6b_M3_conj_forms c hH hF hRT hm
    refine ⟨m * x₁, (y6bX c).mul_mem (y6b_M3_le_X c hH hF hRT hm) hx₁X, ?_⟩
    calc m * x₁ * c.s.t * (m * x₁)⁻¹
        = m * (x₁ * c.s.t * x₁⁻¹) * m⁻¹ := by group
      _ = m * (c.g * c.s.t) * m⁻¹ := by rw [hx₁]
      _ = (m * c.g * m⁻¹) * (m * c.s.t * m⁻¹) := by group
      _ = c.g * (f * c.s.t) := by rw [hmg, hmt]
      _ = (f * c.g) * c.s.t := by
            have hgf : c.g * f = f * c.g := y6b_g_comm_F c hH hRT f hf
            calc c.g * (f * c.s.t) = (c.g * f) * c.s.t := by group
              _ = (f * c.g) * c.s.t := by rw [hgf]

private lemma y6b_X_conj_E16_mem (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hF : c.Facts5)
    (hRT : c.s.R ≠ c.s.T) (h1 : Y6bHasX1 c) {x : G} (hx : x ∈ y6bX c)
    {e : G} (he : e ∈ y6bE16 c) : x * e * x⁻¹ ∈ y6bE16 c := by
  have hx' : x ∈ normalizer ((y6bE c : Subgroup G) : Set G) := hx
  have hxe : x * e * x⁻¹ ∈ y6bE c :=
    (Subgroup.mem_set_normalizer_iff.mp hx' e).mp ((y6b_E16_le_E c) he)
  by_contra hnot
  rw [y6b_mem_E c hH hRT] at hxe
  obtain ⟨f, hf, h | h | h | h⟩ := hxe
  · exact hnot (by rw [h]; exact y6b_F_le_E16 c hf)
  · refine hnot ?_
    rw [h, y6b_mem_E16 c hH hRT]
    exact ⟨f, hf, Or.inr rfl⟩
  · obtain ⟨y, -, hy⟩ := y6b_conj_t_surj c hH hF hRT h1 f (y6b_F_le_E16 c hf)
    rw [← h] at hy
    exact y6b_not_conj_t c hH hF hRT (x⁻¹ * y) e he (by
      calc (x⁻¹ * y) * c.s.t * (x⁻¹ * y)⁻¹
          = x⁻¹ * (y * c.s.t * y⁻¹) * x := by group
        _ = x⁻¹ * (x * e * x⁻¹) * x := by rw [hy]
        _ = e := by group)
  · obtain ⟨y, -, hy⟩ := y6b_conj_t_surj c hH hF hRT h1 (f * c.g) (by
      rw [y6b_mem_E16 c hH hRT]
      exact ⟨f, hf, Or.inr rfl⟩)
    have hy' : y * c.s.t * y⁻¹ = x * e * x⁻¹ := by rw [hy, h]; group
    exact y6b_not_conj_t c hH hF hRT (x⁻¹ * y) e he (by
      calc (x⁻¹ * y) * c.s.t * (x⁻¹ * y)⁻¹
          = x⁻¹ * (y * c.s.t * y⁻¹) * x := by group
        _ = x⁻¹ * (x * e * x⁻¹) * x := by rw [hy']
        _ = e := by group)

theorem y6b_X_le_normalizer_E16 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hF : c.Facts5)
    (hRT : c.s.R ≠ c.s.T) (h1 : Y6bHasX1 c) :
    y6bX c ≤ normalizer ((y6bE16 c : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_set_normalizer_iff]
  intro e
  constructor
  · exact y6b_X_conj_E16_mem c hH hF hRT h1 hx
  · intro he
    have hx' : x⁻¹ ∈ y6bX c := (y6bX c).inv_mem hx
    have h := y6b_X_conj_E16_mem c hH hF hRT h1 hx' he
    rwa [show x⁻¹ * (x * e * x⁻¹) * (x⁻¹)⁻¹ = e from by group] at h

end CFSG.OddStandard.HigherRank.YamadaG23
