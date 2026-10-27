module

public import CFSG.GH74.GLS.C3.Layer1.PU3Cfg
public import CFSG.GH74.GLS.C3.Layer1.Th2P64C

public section

namespace CFSG.GH74.GLS.PU3

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem cj_top (g : G) : cj g (⊤ : Subgroup G) = ⊤ := by
  ext x
  simp only [mem_cj_iff, Subgroup.mem_top]

omit [Finite G] in
theorem cj_bot (g : G) : cj g (⊥ : Subgroup G) = ⊥ := by
  ext x
  simp only [mem_cj_iff, Subgroup.mem_bot]
  constructor
  · intro h
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, h]; group
  · intro h; rw [h]; group

omit [Finite G] in
theorem isCoatom_cj {M : Subgroup G} (h : IsCoatom M) (g : G) : IsCoatom (cj g M) := by
  refine ⟨fun htop => h.1 ?_, fun b hb => ?_⟩
  · have := congrArg (cj g⁻¹) htop
    rwa [cj_cj_inv, cj_top] at this
  · have hlt : M < cj g⁻¹ b := by
      refine lt_of_le_of_ne ((cj_le_iff g).1 hb.le) ?_
      intro heq
      exact hb.ne (by rw [heq, cj_inv_cj])
    have htop : cj g⁻¹ b = ⊤ := h.2 _ hlt
    calc b = cj g (cj g⁻¹ b) := (cj_inv_cj g b).symm
      _ = ⊤ := by rw [htop, cj_top]

omit [Finite G] in
theorem cj_injective (g : G) {H K : Subgroup G} (h : cj g H = cj g K) : H = K := by
  have := congrArg (cj g⁻¹) h
  rwa [cj_cj_inv, cj_cj_inv] at this

omit [Finite G] in
theorem mem_cj_iff' (g : G) (H : Subgroup G) (b : G) : g * b * g⁻¹ ∈ cj g H ↔ b ∈ H := by
  rw [mem_cj_iff]
  have : g⁻¹ * (g * b * g⁻¹) * g = b := by group
  rw [this]

omit [Finite G] in
theorem cj_cj (a b : G) (H : Subgroup G) : cj a (cj b H) = cj (a * b) H := by
  ext x
  rw [mem_cj_iff, mem_cj_iff, mem_cj_iff]
  have : (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b := by group
  rw [this]

omit [Finite G] in
theorem normalizer_le_cj_normalizer {R : Subgroup G} (g : G) :
    normalizer ((cj g R : Subgroup G) : Set G) ≤ cj g (normalizer (R : Set G)) := by
  intro n hn
  rw [mem_cj_iff, Subgroup.mem_normalizer_iff]
  rw [Subgroup.mem_normalizer_iff] at hn
  intro h
  have e2 : g⁻¹ * (n * (g * h * g⁻¹) * n⁻¹) * g = (g⁻¹ * n * g) * h * (g⁻¹ * n * g)⁻¹ := by group
  have := hn (g * h * g⁻¹)
  rw [mem_cj_iff' g R h, mem_cj_iff g R (n * (g * h * g⁻¹) * n⁻¹), e2] at this
  exact this

omit [Finite G] in
theorem cj_commutator (g : G) (Y : Subgroup G) : cj g ⁅Y, Y⁆ = ⁅cj g Y, cj g Y⁆ := by
  unfold cj
  rw [Subgroup.map_commutator]

theorem Good.conj {M L : Subgroup G} (h : Good M L) (g : G) : Good (cj g M) (cj g L) where
  comp := Stage1.Thm2.Recip.isPCompIn_map_conj h.comp g
  normalizer_le := by
    intro R hR hR2 hR1
    have hR' : cj g⁻¹ R ≤ L := (cj_le_iff g⁻¹).2 (by simpa using hR)
    have hR2' : IsPGroup 2 ↥(cj g⁻¹ R) := hR2.of_equiv ((MulAut.conj g⁻¹).subgroupMap R)
    have hR1' : cj g⁻¹ R ≠ ⊥ := by
      intro hb
      apply hR1
      have := congrArg (cj g) hb
      rwa [cj_inv_cj, cj_bot] at this
    have hN := h.normalizer_le _ hR' hR2' hR1'
    have h1 := normalizer_le_cj_normalizer (R := cj g⁻¹ R) g
    rw [cj_inv_cj] at h1
    exact h1.trans (Subgroup.map_mono hN)
  centralizer_le := by
    intro s hs hs2 hsc
    set s' := g⁻¹ * s * g with hs'
    have hs'M : s' ∈ M := (mem_cj_iff g M s).1 hs
    have hs'2 : orderOf s' = 2 := by
      have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective s
      rw [hs2] at this
      simpa [hs', MulAut.conj_apply] using this
    have hsc' : ∀ l ∈ L, ⁅l, s'⁆ ∈ pPrimeCoreOf 2 M := by
      intro l hl
      have hl'' : g * l * g⁻¹ ∈ cj g L := (mem_cj_iff' g L l).2 hl
      have := hsc _ hl''
      rw [pPrimeCoreOf_cj, mem_cj_iff] at this
      have e : g⁻¹ * ⁅g * l * g⁻¹, s⁆ * g = ⁅l, s'⁆ := by
        simp only [hs', commutatorElement_def]
        group
      rwa [e] at this
    have hC := h.centralizer_le s' hs'M hs'2 hsc'
    have hs_eq : s = g * s' * g⁻¹ := by
      simp only [hs']
      group
    rw [hs_eq, ← cj_centralizer_singleton]
    exact Subgroup.map_mono hC
  simple := (MulEquiv.isSimpleGroup_congr (Th2.Obs.kBarConjEquiv g L)).1 h.simple
  nonab := by
    obtain ⟨a, b, hab⟩ := h.nonab
    refine ⟨Th2.Obs.kBarConjEquiv g L a, Th2.Obs.kBarConjEquiv g L b, fun hc => hab ?_⟩
    apply (Th2.Obs.kBarConjEquiv g L).injective
    simpa using hc
  rank := by
    rw [pRank_cj]
    exact h.rank

theorem Cfg.conj {M L₁ L₂ : Subgroup G} (h : Cfg M L₁ L₂) (g : G) :
    Cfg (cj g M) (cj g L₁) (cj g L₂) where
  maximal := isCoatom_cj h.maximal g
  good₁ := h.good₁.conj g
  good₂ := h.good₂.conj g
  ne := fun heq => h.ne (cj_injective g heq)
  only := by
    intro L'' hL''
    have h1 : IsPCompIn 2 M (cj g⁻¹ L'') := by
      have := Stage1.Thm2.Recip.isPCompIn_map_conj hL'' g⁻¹
      change IsPCompIn 2 (cj g⁻¹ (cj g M)) (cj g⁻¹ L'') at this
      rwa [cj_cj_inv] at this
    rcases h.only _ h1 with h2 | h2
    · left
      rw [← h2, cj_inv_cj]
    · right
      rw [← h2, cj_inv_cj]
  swap := by
    obtain ⟨s, hs, hsL⟩ := h.swap
    refine ⟨g * s * g⁻¹, (mem_cj_iff g M _).2 (by simpa [mul_assoc] using hs), ?_⟩
    rw [cj_cj, ← hsL, cj_cj]
    congr 1
    group
  perf := by
    intro Y hY hperf
    have hY' : cj g⁻¹ Y ≤ M := (cj_le_iff g⁻¹).2 (by simpa using hY)
    have hperf' : ⁅cj g⁻¹ Y, cj g⁻¹ Y⁆ = cj g⁻¹ Y := by
      rw [← cj_commutator, hperf]
    have h1 := h.perf _ hY' hperf'
    have h2 : cj g (cj g⁻¹ Y) ≤ cj g (L₁ ⊔ L₂ ⊔ pPrimeCoreOf 2 M) := Subgroup.map_mono h1
    rw [cj_inv_cj] at h2
    have h3 : cj g (L₁ ⊔ L₂ ⊔ pPrimeCoreOf 2 M) =
        cj g L₁ ⊔ cj g L₂ ⊔ pPrimeCoreOf 2 (cj g M) := by
      rw [pPrimeCoreOf_cj]
      unfold cj
      rw [Subgroup.map_sup, Subgroup.map_sup]
    rw [← h3]
    exact h2

end CFSG.GH74.GLS.PU3
