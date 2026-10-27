module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4JF
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31SylConj
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5Frame
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3B1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3Dec

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y7b_isPGroup_zpowers_of_sq_mem {P : Subgroup G} (hP : IsPGroup 2 P) {a : G}
    (ha : a ^ 2 ∈ P) : IsPGroup 2 (Subgroup.zpowers a) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hdvd1 : orderOf a ∣ 2 * orderOf (a ^ 2) :=
    orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_mul, pow_orderOf_eq_one])
  have hdvd2 : orderOf (a ^ 2) ∣ 2 ^ k := by
    rw [← hk]
    exact Subgroup.orderOf_dvd_natCard P ha
  refine IsPGroup.of_card_dvd_pow (n := k + 1) ?_
  rw [Nat.card_zpowers]
  calc orderOf a ∣ 2 * orderOf (a ^ 2) := hdvd1
    _ ∣ 2 * 2 ^ k := Nat.mul_dvd_mul_left 2 hdvd2
    _ = 2 ^ (k + 1) := by rw [pow_succ]; ring

private theorem y7b_f3P_le_R (s : Setting3 G L) : f3P s ≤ s.R := by
  refine sup_le ?_ ?_
  · exact (s3_B_le_S s).trans s.S_le_R
  · rw [Subgroup.zpowers_le]
    exact s3_t_mem_R s

private theorem y7b_f3P_le_NF (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    f3P c.s ≤ normalizer (c.s.fr.F : Set G) := by
  refine sup_le ?_ ?_
  · exact ((s3_B_le_S c.s).trans (s3_S_le_T c.s)).trans (y4_T_normF hH)
  · rw [Subgroup.zpowers_le]
    have hFL : (c.s.fr.F : Set G) ⊆ (L : Set G) := y54_F_le_L c.s
    exact Subgroup.centralizer_le_normalizer (c.s.fr.F : Set G)
      (Subgroup.centralizer_le hFL c.s.t_mem)

theorem y7b_f3X0_eq_P {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    (hRT : s.R = s.T) : f3X0 s = f3P s := by
  refine le_antisymm ?_ (f3_P_le_X0 s)
  intro a ha
  by_contra haP
  have ha2 : a ^ 2 ∈ f3P s := by
    have h := f3_X0_cosets hH a⁻¹ (Subgroup.inv_mem (f3X0 s) ha) a ha
    rcases h with h | h | h
    · exact absurd (by simpa using Subgroup.inv_mem (f3P s) h) haP
    · exact absurd h haP
    · simpa [pow_two] using h
  have hP2 : IsPGroup 2 (f3P s) := f3_P_isPGroup s
  have hQ : IsPGroup 2 (Subgroup.zpowers a) := y7b_isPGroup_zpowers_of_sq_mem hP2 ha2
  obtain ⟨h, hhH, hconj⟩ :=
    exists_conj_le_isSylowIn s.sylow_T hQ (Subgroup.zpowers_le.mpr ha.1)
  have hmem : h * a * h⁻¹ ∈ conjSub h (Subgroup.zpowers a) := by
    rw [conjSub]
    simpa [MulAut.conj_apply] using
      (Subgroup.mem_map_of_mem (MulAut.conj h).toMonoidHom (Subgroup.mem_zpowers a))
  have hxaT : h * a * h⁻¹ ∈ s.T := hconj hmem
  have hxaR : h * a * h⁻¹ ∈ s.R := hRT.symm ▸ hxaT
  rw [s3_R_eq s hH.hS] at hxaR
  have hxaQ : h * a * h⁻¹ ∈ L ⊔ centIn s.H L := (Subgroup.mem_inf.mp hxaR).2
  have hnorm := (Subgroup.normal_subgroupOf_iff (s3_M_le_H s hH.hS)).mp
    (s3_M_normal_H s hH.hS)
  have haQ : a ∈ L ⊔ centIn s.H L := by
    have h1 := hnorm (h * a * h⁻¹) h⁻¹ hxaQ (s.H.inv_mem hhH)
    have h2 : h⁻¹ * (h * a * h⁻¹) * h⁻¹⁻¹ = a := by group
    rwa [h2] at h1
  exact haP (f3_X0_inf_M hH a ha haQ)

theorem y7b_g_mem_f3X0 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    c.g ∈ f3X0 c.s := by
  obtain ⟨hgT, -, hact, hg2, -⟩ := c.g_spec hRT
  refine Subgroup.mem_inf.mpr ⟨c.s.sylow_T.1 hgT, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hgv := y5_g_cent_V hH hg2 hact v hv
  calc v * c.g = (c.g * v * c.g⁻¹) * c.g := by rw [hgv]
    _ = c.g * v := by group

theorem y7b_g_not_mem_f3P (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    c.g ∉ f3P c.s :=
  fun hgP => (c.g_spec hRT).2.1 (y7b_f3P_le_R c.s hgP)

theorem y7b_f3X0_cases_g (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    ∀ x ∈ f3X0 c.s, x ∈ f3P c.s ∨ c.g * x ∈ f3P c.s := by
  intro x hx
  have hgX0 : c.g ∈ f3X0 c.s := y7b_g_mem_f3X0 c hH hRT
  have hgP : c.g ∉ f3P c.s := y7b_g_not_mem_f3P c hH hRT
  rcases f3_X0_cosets hH c.g hgX0 x hx with h | h | h
  · exact absurd h hgP
  · exact Or.inl h
  · refine Or.inr ?_
    have hginv : c.g⁻¹ = c.g := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_two]
      exact (c.g_spec hRT).2.2.2.1
    rwa [hginv] at h

theorem y7b_f3X0_le_NF (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    f3X0 c.s ≤ normalizer (c.s.fr.F : Set G) := by
  intro x hx
  by_cases hRT : c.s.R = c.s.T
  · rw [y7b_f3X0_eq_P hH hRT] at hx
    exact y7b_f3P_le_NF c hH hx
  · rcases y7b_f3X0_cases_g c hH hRT x hx with hxP | hxgP
    · exact y7b_f3P_le_NF c hH hxP
    · have hgN : c.g ∈ normalizer (c.s.fr.F : Set G) :=
        y4_T_normF hH (c.g_spec hRT).1
      have hgxN : c.g * x ∈ normalizer (c.s.fr.F : Set G) := y7b_f3P_le_NF c hH hxgP
      have hmem := Subgroup.mul_mem (normalizer (c.s.fr.F : Set G))
        (Subgroup.inv_mem _ hgN) hgxN
      have h2 : c.g⁻¹ * (c.g * x) = x := by group
      rwa [h2] at hmem

theorem y7b_N_le_NF (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    normIn c.s.H c.s.fr.B ≤ normalizer (c.s.fr.F : Set G) := by
  intro n hn
  obtain ⟨ℓ, hℓ, a, ha, hn_eq⟩ := f3_N_decomp hH n hn
  have hℓN : ℓ ∈ normalizer (c.s.fr.F : Set G) :=
    (Subgroup.mem_inf.mp (hH.hLF.fact18.2.1.2.1 hℓ)).2
  have haN : a ∈ normalizer (c.s.fr.F : Set G) := y7b_f3X0_le_NF c hH ha
  rw [hn_eq]
  exact Subgroup.mul_mem _ hℓN haN

end CFSG.OddStandard.HigherRank.YamadaG23
