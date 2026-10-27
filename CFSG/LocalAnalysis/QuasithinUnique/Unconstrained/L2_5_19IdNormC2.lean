module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdCase2

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section NormC2

variable {G : Type} [Group G] [Finite G] {K Ki : Subgroup G} {t i : G}

theorem normalC_case2 (hI : Inputs2519) (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hq : QTKECore G) (c : Case2 K Ki t i)
    (hK32 : IsL32 K) (hKe : 2 ∣ Nat.card K)
    (hK4 : ∃ E : Subgroup G, E ≤ K ∧ IsElemAbelian 2 E ∧ Nat.card E = 4)
    (hi1 : i ≠ 1) (hi2 : i * i = 1) {j : G} (hj1 : j ≠ 1)
    (hj2 : j * j = 1) (hji : j * i = i * j) (hjt : j * t = t * j)
    (hjKi : j ∈ Subgroup.centralizer (Ki : Set G)) :
    Subgroup.centralizer ({j} : Set G) ≤ Subgroup.normalizer (Ki : Set G) := by
  have hKiq := c.quasisimple
  have htCj : t ∈ Subgroup.centralizer ({j} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hjt.symm
  have hiCj : i ∈ Subgroup.centralizer ({j} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hji.symm
  have hKj : Ki ≤ Subgroup.centralizer ({j} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hjKi x hx)
  have hX : IsComponentIn Ki
      (Subgroup.centralizer ({j} : Set G) ⊓ Subgroup.centralizer ({i} : Set G)) :=
    BenderBranch.isComponentIn_of_le c.comp (le_inf hKj c.comp.1) inf_le_right
  have hXe : 2 ∣ Nat.card Ki := hKe.trans (Subgroup.card_dvd_of_le c.K_le)
  have hX4 : ∃ E : Subgroup G, E ≤ Ki ∧ IsElemAbelian 2 E ∧ Nat.card E = 4 := by
    obtain ⟨E, hEK, hE, hE4⟩ := hK4
    exact ⟨E, hEK.trans c.K_le, hE, hE4⟩
  have hj2' : j ^ 2 = 1 := by rw [sq]; exact hj2
  have hi2' : i ^ 2 = 1 := by rw [sq]; exact hi2
  have hpc : pCoreOf 2 (Subgroup.centralizer ({j} : Set G)) ≠ ⊥ := pCoreOf_centralizer_ne_bot hj1 hj2
  obtain ⟨hKY, hcase⟩ := step2 hI.i32 hI.p121_3 hI.p121_5 hsimple hnonab hq hj1 hj2' hi1 hi2' hji
    hX hXe hX4
  have hE9 := c.hasE9_quotient hI.threeRank
  rcases hcase with ⟨J, hJ, hYJ, hiJ⟩ | ⟨J, hJ, hJne, hYJ, -, hiso⟩
  ·
    have hKJ : Ki ≤ J := hYJ ▸ hKY
    have hJq : CFSG.IsQuasisimple ↥J := BenderBranch.isQuasisimple_of_isComponentIn hJ
    have hJc : J ∈ cComp (Subgroup.centralizer ({j} : Set G)) := mem_cComp_of_isComponentIn hJ
    have hKiJ : IsComponentIn Ki (J ⊓ Subgroup.centralizer ({i} : Set G)) :=
      BenderBranch.isComponentIn_of_le c.comp (le_inf hKJ c.comp.1) inf_le_right
    rcases commutator_dichotomy hJq hiJ with hJi | hJi
    ·
      exfalso
      have htJ : t ∈ Subgroup.normalizer (J : Set G) := by
        have := mem_normalizer_iSup_oddLayer htCj c.tN
        rwa [hYJ] at this
      have hJt : ⁅J, Subgroup.zpowers t⁆ = J := by
        rcases commutator_dichotomy hJq htJ with h | h
        · exact h
        · exact absurd (show Ki ≤ Subgroup.centralizer ({t} : Set G) from fun x hx => h (hKJ hx))
            c.not_le_centralizer
      have hKJt : IsComponentIn K (J ⊓ Subgroup.centralizer ({t} : Set G)) :=
        BenderBranch.isComponentIn_of_le c.K_compC (le_inf (c.K_le.trans hKJ) c.K_compC.1)
          inf_le_right
      obtain ⟨z, hz⟩ := exists_lemma115Cases hI.list115 hsimple hnonab hq hj1 hj2 hJ
      obtain ⟨hJ2, -, -, hpat, -⟩ := hI.ident G J K t hJq ⟨z, hz⟩ htJ c.t_sq hJt hKJt
        (Or.inr (Or.inl hK32))
      have hcase34 : StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 3 2 2 ∨
          Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* CFSG.Blueprint.NativeSporadic.Carrier .J2) := by
        rcases hpat hK32 with hP | hP
        · exact Or.inl hP.2.1
        · exact Or.inr hP.2.1
      have hno := hI.nonEmbed.no_comp G J Ki i hJq hJ2 hcase34 hiJ hi2 hJi hKiJ
      apply hno
      rcases c.pat32 hK32 with hP | hP
      · exact Or.inl hP.2.1
      · exact Or.inr hP.2.1
    ·
      have hJKi : Ki = J := by
        have : J ⊓ Subgroup.centralizer ({i} : Set G) = J := inf_eq_left.mpr hJi
        rw [this] at hKiJ
        exact eq_of_isComponentIn_of_isQuasisimple hKiJ hJq
      subst hJKi
      rcases hI.p121_3 G hsimple hnonab hq _ hpc Ki hJc with hnorm | ⟨-, hlist⟩
      · exact hnorm
      · exact (false_of_isList_of_hasE9 hI.threeRank hKiq hE9 hlist).elim
  ·
    exfalso
    have hJq : CFSG.IsQuasisimple ↥J := BenderBranch.isQuasisimple_of_isComponentIn hJ
    have hJc : J ∈ cComp (Subgroup.centralizer ({j} : Set G)) := mem_cComp_of_isComponentIn hJ
    rcases hI.p121_3 G hsimple hnonab hq _ hpc J hJc with hnorm | ⟨-, hlist⟩
    · exact hJne ((BenderBranch.conjugate_eq_iff_mem_normalizer.mpr (hnorm hiCj)).symm)
    · obtain ⟨f⟩ := hiso
      exact false_of_isList_of_hasE9 hI.threeRank hJq (HasElemAb.of_mulEquiv f.symm hE9) hlist

end NormC2

end CFSG.QuasithinUnique.Id2519
