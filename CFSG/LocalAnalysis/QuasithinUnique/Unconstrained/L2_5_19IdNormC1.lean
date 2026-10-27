module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdCase1

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section NormC1

variable {G : Type} [Group G] [Finite G] {K Ki KP : Subgroup G} {t i : G}

theorem normalC_case1 (hI : Inputs2519) (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hq : QTKECore G) (c : Case1 K Ki KP t i)
    (hKe : 2 ∣ Nat.card K) (hK4 : ∃ E : Subgroup G, E ≤ K ∧ IsElemAbelian 2 E ∧ Nat.card E = 4)
    (hi1 : i ≠ 1) (hi2 : i * i = 1) (hti : t * i = i * t) {j : G} (hj1 : j ≠ 1) (hj2 : j * j = 1)
    (hji : j * i = i * j) (hjt : j * t = t * j) (hjKP : j ∈ Subgroup.centralizer (KP : Set G)) :
    Subgroup.centralizer ({j} : Set G) ≤ Subgroup.normalizer (KP : Set G) := by
  obtain ⟨e⟩ := c.iso
  have hKiq : CFSG.IsQuasisimple ↥Ki := BenderBranch.isQuasisimple_of_isComponentIn c.comp
  have htCj : t ∈ Subgroup.centralizer ({j} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hjt.symm
  have hiCj : i ∈ Subgroup.centralizer ({j} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hji.symm
  have hKiKP : Ki ≤ KP := by rw [c.KP_eq]; exact le_sup_left
  have hKj : Ki ≤ Subgroup.centralizer ({j} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hjKP x (hKiKP hx))
  have hX : IsComponentIn Ki
      (Subgroup.centralizer ({j} : Set G) ⊓ Subgroup.centralizer ({i} : Set G)) :=
    BenderBranch.isComponentIn_of_le c.comp (le_inf hKj c.comp.1) inf_le_right
  have hXe : 2 ∣ Nat.card Ki := by rw [Nat.card_congr e.toEquiv]; exact hKe
  have hX4 : ∃ E : Subgroup G, E ≤ Ki ∧ IsElemAbelian 2 E ∧ Nat.card E = 4 := by
    obtain ⟨E, hEK, hE, hE4⟩ := hK4
    exact HasElemAb.exists_subgroup (HasElemAb.of_mulEquiv e.symm (HasElemAb.of_subgroup hEK hE hE4))
  have hj2' : j ^ 2 = 1 := by rw [sq]; exact hj2
  have hi2' : i ^ 2 = 1 := by rw [sq]; exact hi2
  have hKiType : IsL2pType ↥Ki := IsL2pType.of_mulEquiv e c.type
  have hpc : pCoreOf 2 (Subgroup.centralizer ({j} : Set G)) ≠ ⊥ := pCoreOf_centralizer_ne_bot hj1 hj2
  obtain ⟨hKY, hcase⟩ := step2 hI.i32 hI.p121_3 hI.p121_5 hsimple hnonab hq hj1 hj2' hi1 hi2' hji
    hX hXe hX4
  have hcneT : CFSG.conjugate Ki t ≠ Ki := fun h => c.ne h.symm
  rcases hcase with ⟨J, hJ, hYJ, hiJ⟩ | ⟨J, hJ, hJne, hYJ, hcomm, hiso⟩
  ·
    have hKJ : Ki ≤ J := hYJ ▸ hKY
    have hJq : CFSG.IsQuasisimple ↥J := BenderBranch.isQuasisimple_of_isComponentIn hJ
    have hJc : J ∈ cComp (Subgroup.centralizer ({j} : Set G)) := mem_cComp_of_isComponentIn hJ
    have hKiJ : IsComponentIn Ki (J ⊓ Subgroup.centralizer ({i} : Set G)) :=
      BenderBranch.isComponentIn_of_le c.comp (le_inf hKJ c.comp.1) inf_le_right
    rcases commutator_dichotomy hJq hiJ with hJi | hJi
    ·
      exfalso
      obtain ⟨z, hz⟩ := exists_lemma115Cases hI.list115 hsimple hnonab hq hj1 hj2 hJ
      obtain ⟨hJ2, -, hnbig, hpat, -⟩ := hI.ident G J Ki i hJq ⟨z, hz⟩ hiJ hi2 hJi hKiJ
        (IsKType.of_isL2pType hKiType)
      have hL32 : IsL32 Ki := isL32_of_isL2pType_of_not_big hKiType hnbig
      have hcase34 : StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 3 2 2 ∨
          Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* CFSG.Blueprint.NativeSporadic.Carrier .J2) := by
        rcases hpat hL32 with hP | hP
        · exact Or.inl hP.2.1
        · exact Or.inr hP.2.1
      have hpat' : IsCaseGroup J := by
        rcases hpat hL32 with hP | hP
        · exact isCaseGroup_of_pat (K := Ki) (t := i) (Or.inl hP)
        · exact isCaseGroup_of_pat (K := Ki) (t := i) (Or.inr (Or.inl hP))
      rcases hI.p121_3 G hsimple hnonab hq _ hpc J hJc with hnorm | ⟨-, hlist⟩
      · have htJ : t ∈ Subgroup.normalizer (J : Set G) := hnorm htCj
        have hJt : CFSG.conjugate J t = J := BenderBranch.conjugate_eq_iff_mem_normalizer.mpr htJ
        have hKitJ : CFSG.conjugate Ki t ≤ J := by
          have := BenderBranch.conjugate_mono hKJ t
          rwa [hJt] at this
        obtain ⟨e'⟩ := nonempty_conjugateEquiv Ki t
        exact hI.nonEmbed.no_pair G J Ki (CFSG.conjugate Ki t) hJq hJ2 hcase34 hKJ hKitJ c.comm
          c.inf hKiType (IsL2pType.of_mulEquiv e'.symm hKiType)
      · obtain ⟨A, hAJ, hA3, hA9⟩ := hI.threeRank.nine G J hJq hJ2 hpat'
        have hE9 : HasElemAb 3 9 (↥J ⧸ Subgroup.center ↥J) :=
          HasElemAb.quotient_two _ hJ2 (HasElemAb.of_subgroup hAJ hA3 hA9)
        exact false_of_isList_of_hasE9 hI.threeRank hJq hE9 hlist
    ·
      have hJKi : Ki = J := by
        have : J ⊓ Subgroup.centralizer ({i} : Set G) = J := inf_eq_left.mpr hJi
        rw [this] at hKiJ
        exact eq_of_isComponentIn_of_isQuasisimple hKiJ hJq
      subst hJKi
      rcases hI.p121_3 G hsimple hnonab hq _ hpc Ki hJc with hnorm | ⟨hcard, -⟩
      · exact absurd (BenderBranch.conjugate_eq_iff_mem_normalizer.mpr (hnorm htCj)).symm c.ne
      · have := normalizes_sup_of_two_orbit hcard htCj hcneT
        rwa [← c.KP_eq] at this
  ·
    exfalso
    have hJq : CFSG.IsQuasisimple ↥J := BenderBranch.isQuasisimple_of_isComponentIn hJ
    have hJc : J ∈ cComp (Subgroup.centralizer ({j} : Set G)) := mem_cComp_of_isComponentIn hJ
    have hJneC : CFSG.conjugate J i ≠ J := fun h => hJne h.symm
    rcases hI.p121_3 G hsimple hnonab hq _ hpc J hJc with hnorm | ⟨hcard, -⟩
    · exact hJneC (BenderBranch.conjugate_eq_iff_mem_normalizer.mpr (hnorm hiCj))
    · have hN := normalizes_sup_of_two_orbit hcard hiCj hJneC
      have htY : t ∈ Subgroup.normalizer ((J ⊔ CFSG.conjugate J i : Subgroup G) : Set G) := hN htCj
      obtain ⟨z, hz⟩ := exists_lemma115Cases hI.list115 hsimple hnonab hq hj1 hj2 hJ
      have hiso' : Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* ↥Ki) := by
        obtain ⟨f⟩ := hiso
        exact ⟨f.trans ((QuotientGroup.quotientMulEquivOfEq c.center).trans
          QuotientGroup.quotientBot)⟩
      obtain ⟨eJ⟩ := hI.cover G J Ki hJq ⟨z, hz⟩ hKiType hiso'
      have hZJ : Subgroup.center ↥J = ⊥ := by
        have hmap : (Subgroup.center ↥J).map eJ.toMonoidHom = Subgroup.center ↥Ki :=
          Subgroup.map_center_eq eJ
        rw [c.center] at hmap
        exact (Subgroup.map_eq_bot_iff_of_injective _ eJ.injective).mp hmap
      have hinfJ : J ⊓ CFSG.conjugate J i = ⊥ := inf_eq_bot_of_center_eq_bot hcomm hZJ
      have hKiY : Ki ≤ (J ⊔ CFSG.conjugate J i) ⊓ Subgroup.centralizer ({i} : Set G) :=
        le_inf (hYJ ▸ hKY) c.comp.1
      have hcard' : Nat.card ↥J ≤ Nat.card ↥Ki := (Nat.card_congr eJ.toEquiv).le
      have hKiEq := eq_diag_of_le_of_card_ge (A := J) (B := CFSG.conjugate J i) (t := i) hi2 rfl
        hinfJ hcomm hKiY hcard'
      have htKi : t ∈ Subgroup.normalizer (Ki : Set G) := by
        rw [hKiEq]
        exact mem_normalizer_inf htY (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr
          hti))
      exact c.ne (BenderBranch.conjugate_eq_iff_mem_normalizer.mpr htKi).symm

end NormC1

end CFSG.QuasithinUnique.Id2519
