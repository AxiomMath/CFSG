module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4A
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y53T1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4JF

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y6b_R_decomp (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ r ∈ c.s.R, ∃ s ∈ c.s.fr.S, ∃ i : ℕ, r = s * c.s.t ^ i := by
  intro r hr
  have hrS : r ∈ c.s.fr.S ⊔ zpowers c.s.t := by
    rw [← y5_R_eq hH]
    exact hr
  have hSL : c.s.fr.S ⊔ zpowers c.s.t ≤ L ⊔ zpowers c.s.t :=
    sup_le ((s3_S_le_L c.s).trans le_sup_left) le_sup_right
  have hrL : r ∈ L ⊔ zpowers c.s.t := hSL hrS
  obtain ⟨ℓ, hℓL, i, hi⟩ := y5_mem_L_sup_t c.s hrL
  have htR : c.s.t ∈ c.s.R := s3_t_mem_R c.s
  have hℓR : ℓ ∈ c.s.R := by
    have h : ℓ = r * (c.s.t ^ i)⁻¹ := by rw [hi]; group
    rw [h]
    exact c.s.R.mul_mem hr (c.s.R.inv_mem (c.s.R.zpow_mem htR i))
  have hℓS : ℓ ∈ c.s.fr.S := by
    rw [← s3_R_inf_L c.s]
    exact Subgroup.mem_inf.mpr ⟨hℓR, hℓL⟩
  have ht2 : c.s.t ^ (2 : ℕ) = 1 := by rw [pow_two]; exact y6b_t_sq c
  have hmod : c.s.t ^ i = c.s.t ^ (i % (2 : ℤ)) := zpow_eq_zpow_emod' i ht2
  rcases Int.emod_two_eq_zero_or_one i with h2 | h2
  · refine ⟨ℓ, hℓS, 0, ?_⟩
    rw [hi, hmod, h2]
    simp
  · refine ⟨ℓ, hℓS, 1, ?_⟩
    rw [hi, hmod, h2]
    simp

private theorem y6b_conj_g_R_le_R (c : Ctx5 G L) (hH : F33Hyp c.s c.e)
    (hRT : c.s.R ≠ c.s.T) {r : G} (hr : r ∈ c.s.R) : c.g * r * c.g⁻¹ ∈ c.s.R := by
  have hgT : c.g ∈ c.s.T := y6b_g_mem_T c hRT
  have hgR : c.g ∉ c.s.R := (c.g_spec hRT).2.1
  have hyT : c.g * r * c.g⁻¹ ∈ c.s.T :=
    c.s.T.mul_mem (c.s.T.mul_mem hgT (c.s.R_le_T hr)) (c.s.T.inv_mem hgT)
  rcases y5_T_cosets hH (c.g * r * c.g⁻¹) hyT c.g hgT with hy | hg | hxy
  · exact hy
  · exact absurd hg hgR
  · exfalso
    have hmem : c.g * r⁻¹ ∈ c.s.R := by
      have heq : (c.g * r * c.g⁻¹)⁻¹ * c.g = c.g * r⁻¹ := by group
      rwa [heq] at hxy
    have hg_eq : c.g = (c.g * r⁻¹) * r := by group
    exact hgR (by rw [hg_eq]; exact c.s.R.mul_mem hmem hr)

theorem y6b_S_conj_g_mem (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    ∀ s ∈ c.s.fr.S, ∃ f ∈ c.s.fr.F, s * c.g * s⁻¹ = f * c.g := by
  have hg2 : c.g ^ 2 = 1 := (c.g_spec hRT).2.2.2.1
  have hact : ActsAs L c.g c.s.fr'.σ := (c.g_spec hRT).2.2.1
  have h13 : (frameWith c.s c.g).Fact13 := (hH.hLF.sigma c.g hg2 hact).1
  have h1 : centEl c.s.fr.S c.g = c.s.fr.F := h13.1
  have h3 : {y : G | ∃ d ∈ centEl c.s.fr.S c.g, y = d * c.g} = conjClass c.s.fr.S c.g :=
    h13.2.2.1
  intro s hs
  have hmem : s * c.g * s⁻¹ ∈ conjClass c.s.fr.S c.g := ⟨s, hs, rfl⟩
  rw [← h3] at hmem
  simp only [Set.mem_setOf_eq] at hmem
  obtain ⟨f, hf, hfeq⟩ := hmem
  rw [h1] at hf
  exact ⟨f, hf, hfeq⟩

theorem y6b_S_conj_g_surj (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    ∀ f ∈ c.s.fr.F, ∃ s ∈ c.s.fr.S, s * c.g * s⁻¹ = f * c.g := by
  have hg2 : c.g ^ 2 = 1 := (c.g_spec hRT).2.2.2.1
  have hact : ActsAs L c.g c.s.fr'.σ := (c.g_spec hRT).2.2.1
  have h13 : (frameWith c.s c.g).Fact13 := (hH.hLF.sigma c.g hg2 hact).1
  have h1 : centEl c.s.fr.S c.g = c.s.fr.F := h13.1
  have h3 : {y : G | ∃ d ∈ centEl c.s.fr.S c.g, y = d * c.g} = conjClass c.s.fr.S c.g :=
    h13.2.2.1
  intro f hf
  have hf' : f ∈ centEl c.s.fr.S c.g := by rw [h1]; exact hf
  have hmem : f * c.g ∈ conjClass c.s.fr.S c.g := by rw [← h3]; exact ⟨f, hf', rfl⟩
  obtain ⟨s, hs, hseq⟩ := hmem
  exact ⟨s, hs, hseq.symm⟩

theorem y6b_T_decomp (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    ∀ x ∈ c.s.T, ∃ s ∈ c.s.fr.S, ∃ i j : ℕ, x = s * c.s.t ^ i * c.g ^ j := by
  intro x hx
  have hgT : c.g ∈ c.s.T := y6b_g_mem_T c hRT
  have hgR : c.g ∉ c.s.R := (c.g_spec hRT).2.1
  rcases y5_T_cosets hH x hx c.g hgT with hxR | hg | hxig
  · obtain ⟨s, hs, i, hi⟩ := y6b_R_decomp c hH x hxR
    exact ⟨s, hs, i, 0, by rw [hi]; simp⟩
  · exact absurd hg hgR
  · have hr : x⁻¹ * c.g ∈ c.s.R := hxig
    have hxeq : x = c.g * (x⁻¹ * c.g)⁻¹ := by group
    have hr' : c.g * (x⁻¹ * c.g)⁻¹ * c.g⁻¹ ∈ c.s.R :=
      y6b_conj_g_R_le_R c hH hRT (c.s.R.inv_mem hr)
    obtain ⟨s, hs, i, hi⟩ := y6b_R_decomp c hH (c.g * (x⁻¹ * c.g)⁻¹ * c.g⁻¹) hr'
    refine ⟨s, hs, i, 1, ?_⟩
    rw [hxeq, ← hi]
    rw [pow_one]
    group

theorem y6b_T_le_normalizer_F (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    c.s.T ≤ normalizer (c.s.fr.F : Set G) :=
  y4_T_normF hH

theorem y6b_T_conj_g_mem (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    ∀ x ∈ c.s.T, ∃ f ∈ c.s.fr.F, x * c.g * x⁻¹ = f * c.g := by
  intro x hx
  obtain ⟨s, hs, i, j, rfl⟩ := y6b_T_decomp c hH hRT x hx
  have hgt : Commute c.s.t c.g := (y6b_g_comm_t c hRT).symm
  have hcomm : Commute (c.s.t ^ i * c.g ^ j) c.g :=
    (hgt.pow_left i).mul_left ((Commute.refl c.g).pow_left j)
  have hconj : c.s.t ^ i * c.g ^ j * c.g * (c.s.t ^ i * c.g ^ j)⁻¹ = c.g := by
    rw [hcomm.eq]
    group
  have hxconj : (s * c.s.t ^ i * c.g ^ j) * c.g * (s * c.s.t ^ i * c.g ^ j)⁻¹
      = s * c.g * s⁻¹ := by
    calc (s * c.s.t ^ i * c.g ^ j) * c.g * (s * c.s.t ^ i * c.g ^ j)⁻¹
        = s * (c.s.t ^ i * c.g ^ j * c.g * (c.s.t ^ i * c.g ^ j)⁻¹) * s⁻¹ := by group
      _ = s * c.g * s⁻¹ := by rw [hconj]
  obtain ⟨f, hf, hfeq⟩ := y6b_S_conj_g_mem c hH hRT s hs
  exact ⟨f, hf, by rw [hxconj, hfeq]⟩

theorem y6b_T_le_X (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    c.s.T ≤ y6bX c := by
  rw [y6bX]
  refine Subgroup.le_normalizer_iff.mpr ?_
  intro x hx y hy
  have hFnorm : ∀ f ∈ c.s.fr.F, x * f * x⁻¹ ∈ c.s.fr.F :=
    fun f hf => (Subgroup.le_set_normalizer_iff.mp (y6b_T_le_normalizer_F c hH hRT)) x hx f hf
  have hF : c.s.fr.F ≤ (y6bE c).comap (MulAut.conj x).toMonoidHom := by
    intro f hf
    rw [Subgroup.mem_comap]
    change (MulAut.conj x) f ∈ y6bE c
    rw [MulAut.conj_apply]
    exact y6b_F_le_E c (hFnorm f hf)
  have hg : Subgroup.zpowers c.g ≤ (y6bE c).comap (MulAut.conj x).toMonoidHom := by
    rw [Subgroup.zpowers_le, Subgroup.mem_comap]
    change (MulAut.conj x) c.g ∈ y6bE c
    rw [MulAut.conj_apply]
    obtain ⟨f', hf', hf'eq⟩ := y6b_T_conj_g_mem c hH hRT x hx
    rw [hf'eq]
    exact (y6bE c).mul_mem (y6b_F_le_E c hf') (y6b_E16_le_E c (y6b_g_mem_E16 c))
  have ht : Subgroup.zpowers c.s.t ≤ (y6bE c).comap (MulAut.conj x).toMonoidHom := by
    rw [Subgroup.zpowers_le, Subgroup.mem_comap]
    change (MulAut.conj x) c.s.t ∈ y6bE c
    rw [MulAut.conj_apply]
    have hxt : x * c.s.t = c.s.t * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (c.s.sylow_T.1 hx)
    have : x * c.s.t * x⁻¹ = c.s.t := by rw [hxt]; group
    rw [this]
    exact y6b_t_mem_E c
  have hE : y6bE c ≤ (y6bE c).comap (MulAut.conj x).toMonoidHom := by
    rw [y6bE, y6bE16]
    exact sup_le (sup_le hF hg) ht
  exact hE hy

end CFSG.OddStandard.HigherRank.YamadaG23
