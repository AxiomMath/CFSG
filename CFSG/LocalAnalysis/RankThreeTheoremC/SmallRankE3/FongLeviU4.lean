module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviU4Model
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.H13.U4Par

variable {m : ℕ} {K : Type} [Field K]

theorem eq_parP2_of_borel (h : UnitaryFieldData 2 m K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpr : ¬ p ∣ Nat.card K - 1) {M : Subgroup (hypSU h 2 0)}
    (hBM : hypBorel h 2 0 ≤ M) (hne : M ≠ ⊤) {z : hypSU h 2 0} (hz : orderOf z = p)
    (hzM : z ∈ M) : M = parP2 h := by
  classical
  haveI := h.finite
  haveI : Finite (hypSU h 2 0) := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  obtain ⟨c, hc, hc0⟩ := exists_mem_traceZero_ne_zero' h
  obtain ⟨hI, hMI, -, -⟩ :=
    UnitaryHigher.unitary_Borel_overgroups h (by norm_num) (by norm_num) hc hc0 M hBM
  set I := UnitaryHigher.overgroupCuts 0 h c hc M with hIdef
  by_cases h1 : 1 ∈ I
  · exfalso
    have hMP : M ≤ parP h := by
      rw [hMI]
      intro g hg
      exact UnitaryHigher.mem_isoStabilizer.mpr (UnitaryHigher.mem_flagStabilizer.mp hg 1 h1)
    have hpP : p ∣ Nat.card (parP h) := by
      have h1' : orderOf (⟨z, hMP hzM⟩ : ↥(parP h)) ∣ Nat.card (parP h) := orderOf_dvd_natCard _
      rwa [Subgroup.orderOf_mk, hz] at h1'
    rw [card_parP h] at hpP
    rcases (Nat.Prime.dvd_mul hp).1 hpP with h2 | h2
    · have h3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
        (hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow h2))
      exact hp2 h3
    · apply hpr
      have h3 := hp.dvd_of_dvd_pow h2
      rwa [h.card, pow_mul']
  · have hI2 : I = {2} := by
      have hne' : I.Nonempty := by
        rw [Set.nonempty_iff_ne_empty]
        intro hI0
        apply hne
        rw [hMI, hI0, UnitaryHigher.flagStabilizer_empty]
      obtain ⟨j, hj⟩ := hne'
      have hj' := hI hj
      have hj2 : j = 2 := by
        rcases hj' with ⟨hj1, hj2⟩
        by_contra hj2'
        have : j = 1 := by omega
        exact h1 (this ▸ hj)
      ext i
      constructor
      · intro hi
        have hi' := hI hi
        rcases hi' with ⟨hi1, hi2⟩
        by_contra hi2'
        have : i = 1 := by
          rw [Set.mem_singleton_iff] at hi2'
          omega
        exact h1 (this ▸ hi)
      · intro hi
        rw [Set.mem_singleton_iff] at hi
        rw [hi]
        exact hj2 ▸ hj
    rw [hI2, UnitaryHigher.flagStabilizer_singleton] at hMI
    exact hMI

theorem two_le_pRank_of_hypSU {A : Type} [Group A] [Finite A] {K₁ : Subgroup A} {p : ℕ}
    (hp : p.Prime) (h : UnitaryFieldData 2 m K) (e0 : ↥K₁ ≃* hypSU h 2 0)
    (hr : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (hypSU h 2 0))) : 2 ≤ CFSG.Open.pRank p K₁ := by
  haveI : Finite (hypSU h 2 0) := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  have h3 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e0.symm
  have h4 : CFSG.Open.pRank p K₁ = CFSG.Open.pRank p (⊤ : Subgroup ↥K₁) :=
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup K₁
  omega

theorem u4_reduce {A : Type} [Group A] [Finite A] {K₁ K₀ : Subgroup A} {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hKr : CFSG.Open.pRank p K₁ ≤ 1)
    (hpar : CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.IsParabolicTwo A K₁ K₀) (hne : K₀ ≠ K₁)
    {z : A} (hz : orderOf z = p) (hzK₀ : z ∈ K₀) (h : UnitaryFieldData 2 m K)
    (e0 : ↥K₁ ≃* hypSU h 2 0) :
    ¬ p ∣ Nat.card K - 1 ∧
      ∃ (ε : hypSU h 2 0 ≃* ↥K₁) (z' : hypSU h 2 0), z' ∈ parP2 h ∧ orderOf z' = p ∧
        ((ε z' : ↥K₁) : A) = z ∧ (parP2 h).map ε.toMonoidHom = K₀.subgroupOf K₁ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := h.finite
  haveI : Finite (hypSU h 2 0) := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  have hp2 : p ≠ 2 := by omega
  have hK₀K : K₀ ≤ K₁ := hpar.1
  have hzK : z ∈ K₁ := hK₀K hzK₀
  have hpr : ¬ p ∣ Nat.card K - 1 := by
    intro hd
    have hfac : Nat.card K - 1 = (2 ^ m - 1) * (2 ^ m + 1) := by
      have hq : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      obtain ⟨r, hr⟩ : ∃ r, 2 ^ m = r + 1 := ⟨2 ^ m - 1, by omega⟩
      rw [h.card, pow_mul', hr]
      have : (r + 1) ^ 2 = r * (r + 1 + 1) + 1 := by ring
      simp only [Nat.add_sub_cancel]
      omega
    rw [hfac] at hd
    rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h1
    · have := two_le_pRank_of_hypSU hp h e0 (hypSU_two_le_pRank_of_dvd_sub h hp2 h1)
      omega
    · have := two_le_pRank_of_hypSU hp h e0 (hypSU_two_le_pRank_of_dvd_add h hp2 h1)
      omega
  obtain ⟨-, U, hUsyl, hN⟩ := hpar
  obtain ⟨Q, hQU⟩ := hUsyl
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨P, hP⟩, -⟩ := unitary_order_and_Sylow h (r := 2) (ε := 0) (by norm_num) (by norm_num)
  obtain ⟨ε, hε⟩ := CFSG.ProperTwoGeneratedCore.RootCenter.exists_mulEquiv_map_eq e0 P Q
  set M : Subgroup (hypSU h 2 0) := (K₀.subgroupOf K₁).comap ε.toMonoidHom with hM
  have hBM : hypBorel h 2 0 ≤ M := by
    intro g hg
    rw [← (UnitaryHigher.unitary_Sylow_normalizers h (by norm_num) (by norm_num)).1] at hg
    have h1 : ε g ∈ Subgroup.normalizer ((Q : Subgroup ↥K₁) : Set ↥K₁) := by
      rw [← hε, ← Subgroup.map_equiv_normalizer_eq]
      refine ⟨g, ?_, rfl⟩
      rw [hP]
      exact hg
    have hUle : U ≤ K₁.subtype.range := by
      rw [← hQU, Subgroup.range_subtype]
      exact Subgroup.map_subtype_le _
    have hUc : U.comap K₁.subtype = (Q : Subgroup ↥K₁) := by
      rw [← hQU]
      exact Subgroup.comap_map_eq_self_of_injective K₁.subtype_injective _
    have h2 : ε g ∈ (Subgroup.normalizer (U : Set A)).comap K₁.subtype := by
      rw [Subgroup.comap_normalizer_eq_of_le_range hUle, hUc]
      exact h1
    have h3 : ((ε g : ↥K₁) : A) ∈ K₀ := hN ⟨h2, (ε g).2⟩
    exact Subgroup.mem_subgroupOf.mpr h3
  have hMne : M ≠ ⊤ := by
    intro htop
    apply hne
    apply le_antisymm hK₀K
    intro x hx
    have h1 : ε.symm ⟨x, hx⟩ ∈ M := by rw [htop]; exact Subgroup.mem_top _
    have h2 : ε (ε.symm ⟨x, hx⟩) ∈ K₀.subgroupOf K₁ := h1
    rw [MulEquiv.apply_symm_apply] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  set z' : hypSU h 2 0 := ε.symm ⟨z, hzK⟩ with hz'def
  have hεz : ε z' = ⟨z, hzK⟩ := by rw [hz'def, MulEquiv.apply_symm_apply]
  have hz'M : z' ∈ M := by
    show ε z' ∈ K₀.subgroupOf K₁
    rw [hεz]
    exact Subgroup.mem_subgroupOf.mpr hzK₀
  have hz'ord : orderOf z' = p := by
    have h1 : orderOf (ε.symm ⟨z, hzK⟩) = orderOf (⟨z, hzK⟩ : ↥K₁) :=
      orderOf_injective ε.symm.toMonoidHom ε.symm.injective _
    rw [Subgroup.orderOf_mk z hzK, hz] at h1
    exact h1
  have hMP2 : M = parP2 h := eq_parP2_of_borel h hp hp2 hpr hBM hMne hz'ord hz'M
  have hMmap : M.map ε.toMonoidHom = K₀.subgroupOf K₁ :=
    Subgroup.map_comap_eq_self_of_surjective ε.surjective _
  refine ⟨hpr, ε, z', ?_, hz'ord, by rw [hεz], ?_⟩
  · rw [← hMP2]
    exact hz'M
  · rw [← hMP2]
    exact hMmap

theorem u4_levi_of_equiv {A : Type} [Group A] [Finite A] {K₁ K₀ : Subgroup A} {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hKr : CFSG.Open.pRank p K₁ ≤ 1)
    (hpar : CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.IsParabolicTwo A K₁ K₀) (hne : K₀ ≠ K₁)
    {z : A} (hz : orderOf z = p) (hzK₀ : z ∈ K₀) (h : UnitaryFieldData 2 m K) (hm : 2 ≤ m)
    (e0 : ↥K₁ ≃* hypSU h 2 0) :
    ¬ p ∣ Nat.card K - 1 ∧ LeviSec p K₀ z ∧
      LeviHom K₀ (Matrix.SpecialLinearGroup (Fin 2) K) := by
  classical
  obtain ⟨hpr, ε, z', hz'P, hz'ord, hεz0, hmap⟩ := u4_reduce hp hp5 hKr hpar hne hz hzK₀ h e0
  haveI := h.finite
  haveI : Finite (hypSU h 2 0) := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  have hp2 : p ≠ 2 := by omega
  have hK₀K : K₀ ≤ K₁ := hpar.1
  obtain ⟨hsec, hhom⟩ := hypSU_parP2_levi h hm hp hp2 hpr hz'ord hz'P
  have hεz : ε.toMonoidHom z' = ⟨z, hK₀K hzK₀⟩ := Subtype.ext hεz0
  have h1s := hsec.map ε.toMonoidHom ε.injective
  have h1h := hhom.map ε.toMonoidHom ε.injective
  rw [hmap, hεz] at h1s
  rw [hmap] at h1h
  have h2s := h1s.map K₁.subtype K₁.subtype_injective
  have h2h := h1h.map K₁.subtype K₁.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hK₀K] at h2s h2h
  exact ⟨hpr, h2s, h2h⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
