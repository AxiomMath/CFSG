module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Ctx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Layer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Pair

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

private lemma sec5b517_exists_pair_idx : ∀ k l : Fin 4, k ≠ l →
    ∃ i j : Fin 4, i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l := by
  decide

theorem sec5b517_exists_pair (h514 : Asc82Lemma514) (c : Sec5HCtx G t L S z r B A K₁ K₂ h)
    {k l : Fin 4} (hkl : k ≠ l) :
    ∃ d ∈ Delta5 z (Gamma5 K₁ K₂ h),
      IsKOf (Gamma5 K₁ K₂ h) d (Kfam5 K₁ K₂ h k ⊔ Kfam5 K₁ K₂ h l) := by
  have hq := sec5b517_quad h514 c
  obtain ⟨i, j, hij, hik, hil, hjk, hjl⟩ := sec5b517_exists_pair_idx k l hkl
  obtain ⟨d, hdij, hd2, hd1, hdz, -⟩ := hq.exists_pair_invol hij
  have hdord : orderOf d = 2 := orderOf_eq_prime (by simpa [pow_two] using hd2) hd1
  refine ⟨d, ⟨hdord, hdz, ?_⟩, ?_⟩
  · refine ⟨Kfam5 K₁ K₂ h i, ?_, Kfam5 K₁ K₂ h j, ?_, hq.ne hij, hdij⟩
    · rw [sec5b517_gamma_eq]; exact Set.mem_range.mpr ⟨i, rfl⟩
    · rw [sec5b517_gamma_eq]; exact Set.mem_range.mpr ⟨j, rfl⟩
  · refine ⟨Kfam5 K₁ K₂ h k, ?_, Kfam5 K₁ K₂ h l, ?_, hq.ne hkl, rfl, ?_⟩
    · rw [sec5b517_gamma_eq]; exact Set.mem_range.mpr ⟨k, rfl⟩
    · rw [sec5b517_gamma_eq]; exact Set.mem_range.mpr ⟨l, rfl⟩
    · exact sup_le (Sec5B517Quad.le_centralizer_of_mem_pair hq hik.symm hjk.symm hdij)
        (Sec5B517Quad.le_centralizer_of_mem_pair hq hil.symm hjl.symm hdij)

theorem sec5b517_pair12 (h514 : Asc82Lemma514) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {d : G}
    (hd : d ∈ K₁ ⊔ K₂) (hd2 : orderOf d = 2) (hdz : d ≠ z) :
    d ∈ Delta5 z (Gamma5 K₁ K₂ h) ∧
      IsKOf (Gamma5 K₁ K₂ h) d (CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) := by
  have hq := sec5b517_quad h514 c
  have hd01 : d ∈ Kfam5 K₁ K₂ h 0 ⊔ Kfam5 K₁ K₂ h 1 := hd
  refine ⟨⟨hd2, hdz, Kfam5 K₁ K₂ h 0, ?_, Kfam5 K₁ K₂ h 1, ?_, hq.ne (by decide), hd01⟩, ?_⟩
  · rw [sec5b517_gamma_eq]; exact Set.mem_range.mpr ⟨0, rfl⟩
  · rw [sec5b517_gamma_eq]; exact Set.mem_range.mpr ⟨1, rfl⟩
  · refine ⟨Kfam5 K₁ K₂ h 2, ?_, Kfam5 K₁ K₂ h 3, ?_, hq.ne (by decide), rfl, ?_⟩
    · rw [sec5b517_gamma_eq]; exact Set.mem_range.mpr ⟨2, rfl⟩
    · rw [sec5b517_gamma_eq]; exact Set.mem_range.mpr ⟨3, rfl⟩
    · exact sup_le
        (Sec5B517Quad.le_centralizer_of_mem_pair hq (i := 0) (j := 1) (l := 2)
          (by decide) (by decide) hd01)
        (Sec5B517Quad.le_centralizer_of_mem_pair hq (i := 0) (j := 1) (l := 3)
          (by decide) (by decide) hd01)

theorem sec5b517_cov (h515b : Asc82Lemma515b) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {g d : G}
    (hg : g ∈ centralizer ({z} : Set G)) (hd : d ∈ Delta5 z (Gamma5 K₁ K₂ h))
    (hd' : g⁻¹ * d * g ∈ Delta5 z (Gamma5 K₁ K₂ h)) {P P' : Subgroup G}
    (hP : IsKOf (Gamma5 K₁ K₂ h) d P) (hP' : IsKOf (Gamma5 K₁ K₂ h) (g⁻¹ * d * g) P') :
    CFSG.conjugate P g = P' := by
  have hdP := (h515b G t L S z r B A K₁ K₂ h c d hd).2 P hP
  have hdP' := (h515b G t L S z r B A K₁ K₂ h c (g⁻¹ * d * g) hd').2 P' hP'
  rw [hdP, hdP']
  exact (sec5b517_twoRes_cov hg d).symm

theorem sec5b517_conj_pair (h37 : Asc82Lemma37) (h514 : Asc82Lemma514)
    (h515b : Asc82Lemma515b) (h515c : Asc82Lemma515c) (fuse : Asc82Fact517Fuse)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {n : G}
    (hn : n ∈ normalizer (Qsub K₁ K₂ h : Set G)) {k l : Fin 4} (hkl : k ≠ l) :
    ∃ k' l' : Fin 4, k' ≠ l' ∧
      CFSG.conjugate (Kfam5 K₁ K₂ h k ⊔ Kfam5 K₁ K₂ h l) n =
        Kfam5 K₁ K₂ h k' ⊔ Kfam5 K₁ K₂ h l' := by
  obtain ⟨d, hd, hPd⟩ := sec5b517_exists_pair h514 c hkl
  have hnz : n ∈ centralizer ({z} : Set G) := sec5b517_normalizer_le h514 c hn
  have hd' : n⁻¹ * d * n ∈ Delta5 z (Gamma5 K₁ K₂ h) :=
    sec5b517_delta_conj h37 h514 h515c fuse c hn hd
  obtain ⟨P', hP'⟩ := (h515b G t L S z r B A K₁ K₂ h c (n⁻¹ * d * n) hd').1
  have hcov : CFSG.conjugate (Kfam5 K₁ K₂ h k ⊔ Kfam5 K₁ K₂ h l) n = P' :=
    sec5b517_cov h515b c hnz hd hd' hPd hP'
  obtain ⟨P₁, hP₁, P₂, hP₂, hne, hPeq, -⟩ := hP'
  rw [sec5b517_gamma_eq] at hP₁ hP₂
  obtain ⟨k', hk'⟩ := Set.mem_range.mp hP₁
  obtain ⟨l', hl'⟩ := Set.mem_range.mp hP₂
  refine ⟨k', l', ?_, ?_⟩
  · intro hkl'
    exact hne (by rw [← hk', ← hl', hkl'])
  · rw [hcov, hPeq, ← hk', ← hl']

theorem sec5b517_perm (h37 : Asc82Lemma37) (h514 : Asc82Lemma514) (h515b : Asc82Lemma515b)
    (h515c : Asc82Lemma515c) (fuse : Asc82Fact517Fuse)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    ∀ n ∈ normalizer (Qsub K₁ K₂ h : Set G), ∀ P ∈ Gamma5 K₁ K₂ h,
      CFSG.conjugate P n ∈ Gamma5 K₁ K₂ h := by
  intro n hn P hP
  rw [sec5b517_gamma_eq] at hP ⊢
  obtain ⟨a, ha⟩ := Set.mem_range.mp hP
  obtain ⟨m, hm⟩ := Sec5B517Quad.conj_family (sec5b517_quad h514 c)
    (g := n) (fun k l hkl => sec5b517_conj_pair h37 h514 h515b h515c fuse c hn hkl) a
  refine Set.mem_range.mpr ⟨m, ?_⟩
  rw [← ha, hm]

end CFSG.OddStandard.SmallF3.Omega
