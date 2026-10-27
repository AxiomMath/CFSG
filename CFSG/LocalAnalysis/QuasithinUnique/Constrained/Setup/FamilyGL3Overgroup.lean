module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Aut

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ABGLocalTools CFSG.QuasithinUnique.Setup.X6
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem hasTwoGeneratingOvergroups_inner {X : Type} [Group X] [Finite X]
    (hZ : Subgroup.center X = ⊥) {U Q₁ Q₂ : Subgroup X} (hU : IsSylowOf 2 U ⊤)
    (hUQ₁ : U ≤ Q₁) (hUQ₂ : U ≤ Q₂) (h₁ : Q₁ ≠ ⊤) (h₂ : Q₂ ≠ ⊤) (hgen : Q₁ ⊔ Q₂ = ⊤)
    {R : Subgroup (MulAut X)} (hR : IsSylowOf 2 R (inner X)) :
    HasTwoGeneratingOvergroups (inner X) R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj := conj_injective_of_center_eq_bot hZ
  set ι : X →* MulAut X := MulAut.conj with hι
  have hinner : inner X = (⊤ : Subgroup X).map ι := by
    rw [← MonoidHom.range_eq_map]
    rfl
  have hU' : IsSylowOf 2 (U.map ι) (inner X) := by
    have := isSylowOf_map_injective ι hinj hU
    rwa [← hinner] at this
  obtain ⟨k, hk, hkconj⟩ := hU'.exists_mem_conj hR
  have hbase : HasTwoGeneratingOvergroups (inner X) (U.map ι) := by
    refine ⟨Q₁.map ι, Q₂.map ι, Subgroup.map_mono hUQ₁, Subgroup.map_mono hUQ₂, ?_, ?_, ?_⟩
    · rw [hinner]
      exact (Subgroup.map_lt_map_iff_of_injective hinj).2 (lt_top_iff_ne_top.2 h₁)
    · rw [hinner]
      exact (Subgroup.map_lt_map_iff_of_injective hinj).2 (lt_top_iff_ne_top.2 h₂)
    · rw [← Subgroup.map_sup, hgen, ← hinner]
  have h2 := hbase.map (MulAut.conj k)
  rw [map_conj_eq_of_mem' hk] at h2
  have hR' : (U.map ι).map (MulAut.conj k).toMonoidHom = R := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    exact (hkconj x).symm
  rwa [hR'] at h2

theorem flagStabilizer_sup_eq_top_of_disjoint {K : Type*} [Field K] {n : ℕ} {I J : Set ℕ}
    (hIJ : ∀ i, 1 ≤ i → i < n → i ∉ I ∨ i ∉ J) :
    flagStabilizer n K I ⊔ flagStabilizer n K J = ⊤ := by
  set A := flagStabilizer n K I ⊔ flagStabilizer n K J with hA
  have hBA : upperTriangular n K ≤ A :=
    (upperTriangular_le_flagStabilizer (K := K) (n := n) I).trans le_sup_left
  obtain ⟨hAeq, -⟩ := borel_overgroups A hBA
  have hcuts : borelOvergroupCuts A = ∅ := by
    ext i
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hi, hin, hnot⟩
    apply hnot
    rcases hIJ i hi hin with h | h
    · exact Subgroup.mem_sup_left
        (((subflag_stabilizer_generation (K := K) (n := n) I).2.2 i hi hin).2 h)
    · exact Subgroup.mem_sup_right
        (((subflag_stabilizer_generation (K := K) (n := n) J).2.2 i hi hin).2 h)
  rw [hAeq, hcuts]
  exact flagStabilizer_empty n K

theorem GL3_overgroup_data : ∃ U Q₁ Q₂ : Subgroup GL32, IsSylowOf 2 U ⊤ ∧ U ≤ Q₁ ∧ U ≤ Q₂ ∧
    Q₁ ≠ ⊤ ∧ Q₂ ≠ ⊤ ∧ Q₁ ⊔ Q₂ = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e := slEquivGL 3
  obtain ⟨S, hS⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := 3) (by norm_num)
  have hU₀ : IsSylowOf 2 (unitriangular 3 (ZMod 2)) ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, ?_, ?_⟩
    · rw [← hS]
      exact S.isPGroup'
    · rw [Subgroup.relIndex_top_right, ← hS]
      exact S.not_dvd_index
  have hB : unitriangular 3 (ZMod 2) ≤ upperTriangular 3 (ZMod 2) :=
    unitriangular_le_upperTriangular 3 (ZMod 2)
  have hQ₁ : unitriangular 3 (ZMod 2) ≤ flagStabilizer 3 (ZMod 2) {1} :=
    hB.trans (upperTriangular_le_flagStabilizer {1})
  have hQ₂ : unitriangular 3 (ZMod 2) ≤ flagStabilizer 3 (ZMod 2) {2} :=
    hB.trans (upperTriangular_le_flagStabilizer {2})
  have hne₁ : flagStabilizer 3 (ZMod 2) {1} ≠ ⊤ := fun h => by
    refine not_normal_flagStabilizer (K := ZMod 2) (n := 3) (I := {1}) (d := 1) ?_
      (Set.mem_singleton 1) le_rfl (by norm_num) ?_
    · intro i hi
      rw [Set.mem_singleton_iff.1 hi]
      norm_num
    · rw [h]
      exact Subgroup.normal_top
  have hne₂ : flagStabilizer 3 (ZMod 2) {2} ≠ ⊤ := fun h => by
    refine not_normal_flagStabilizer (K := ZMod 2) (n := 3) (I := {2}) (d := 2) ?_
      (Set.mem_singleton 2) (by norm_num) (by norm_num) ?_
    · intro i hi
      rw [Set.mem_singleton_iff.1 hi]
      norm_num
    · rw [h]
      exact Subgroup.normal_top
  have hgen : flagStabilizer 3 (ZMod 2) {1} ⊔ flagStabilizer 3 (ZMod 2) {2} = ⊤ :=
    flagStabilizer_sup_eq_top_of_disjoint (K := ZMod 2) (n := 3) (fun i hi1 hi3 => by
      simp only [Set.mem_singleton_iff]
      omega)
  have hmapne : ∀ Q : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)), Q ≠ ⊤ →
      Q.map e.toMonoidHom ≠ ⊤ := fun Q hQ h => by
    apply hQ
    exact Subgroup.map_injective e.injective
      (h.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm)
  refine ⟨(unitriangular 3 (ZMod 2)).map e.toMonoidHom,
    (flagStabilizer 3 (ZMod 2) {1}).map e.toMonoidHom,
    (flagStabilizer 3 (ZMod 2) {2}).map e.toMonoidHom, ?_, Subgroup.map_mono hQ₁,
    Subgroup.map_mono hQ₂, hmapne _ hne₁, hmapne _ hne₂, ?_⟩
  · have := isSylowOf_map_injective (p := 2) e.toMonoidHom e.injective hU₀
    rwa [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at this
  · rw [← Subgroup.map_sup, hgen, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]

theorem GL3_outer_of_unique_max {Q : Type} [Group Q] (e : Q ≃* GL32) {D R P : Subgroup (MulAut Q)}
    (hD : inner Q ≤ D) (hR : CFSG.QuasithinUnique.IsSylowTwoOf R D)
    (hP : R ≤ P ∧ P ⋖ D ∧ ∀ M, M ⋖ D → R ≤ M → M = P) : ∃ α ∈ D, α ∉ inner Q := by
  by_contra hcon
  have hDle : D ≤ inner Q := fun α hα => by
    by_contra h
    exact hcon ⟨α, hα, h⟩
  have hDeq : D = inner Q := le_antisymm hDle hD
  subst hDeq
  have : Finite Q := Finite.of_equiv GL32 e.symm.toEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, Q₁, Q₂, hU, h1, h2, h1', h2', hgen⟩ := GL3_overgroup_data
  have hZ : Subgroup.center Q = ⊥ := by
    have := Subgroup.map_center_eq e
    rw [center_GL32, Subgroup.map_eq_bot_iff_of_injective _ e.injective] at this
    exact this
  have hmapne : ∀ Q' : Subgroup GL32, Q' ≠ ⊤ → Q'.map e.symm.toMonoidHom ≠ ⊤ := fun Q' hQ h => by
    apply hQ
    exact Subgroup.map_injective e.symm.injective
      (h.trans (Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective).symm)
  have hU' : IsSylowOf 2 (U.map e.symm.toMonoidHom) ⊤ := by
    have := isSylowOf_map_injective (p := 2) e.symm.toMonoidHom e.symm.injective hU
    rwa [Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective] at this
  have hgen' := hasTwoGeneratingOvergroups_inner hZ hU' (Subgroup.map_mono h1)
    (Subgroup.map_mono h2) (hmapne _ h1') (hmapne _ h2')
    (by rw [← Subgroup.map_sup, hgen,
      Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective])
    (isSylowTwoOf_iff_isSylowOf.1 hR)
  exact hgen'.not_uniqueMaximal hP

end CFSG.QuasithinUnique.Setup.Family
