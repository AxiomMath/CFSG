module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusFamRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusFamPoly

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open Polynomial CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.RankThree.Classical
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

private theorem sp_false_of_three_components {K : Type} [Field K] [Finite K] {r s : ℕ}
    (hs : 1 ≤ s) (hK : Nat.card K = 2 ^ s) (hr : 1 ≤ r) (x : StatedSp r K) (hx : x ^ 3 = 1)
    (hx1 : SymplecticFlag.proj r K x ≠ 1)
    {J₁ J₂ J₃ : Subgroup (StatedProj (StatedSp r K))}
    (h1 : IsComponentOf J₁ (fixSubgroup (MulAut.conj (SymplecticFlag.proj r K x))))
    (h2 : IsComponentOf J₂ (fixSubgroup (MulAut.conj (SymplecticFlag.proj r K x))))
    (h3 : IsComponentOf J₃ (fixSubgroup (MulAut.conj (SymplecticFlag.proj r K x))))
    (h12 : J₁ ≠ J₂) (h13 : J₁ ≠ J₃) (h23 : J₂ ≠ J₃) : False := by
  classical
  haveI := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := s) (by rw [Fintype.card_eq_nat_card, hK])
  have ha : orderOf (SymplecticFlag.proj r K x) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hx, map_one]) hx1
  have hxp : orderOf x = 3 := orderOf_eq_prime hx (fun h => hx1 (by rw [h, map_one]))
  have blocks := (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two hs hK
    Nat.prime_three (by norm_num) (by norm_num) hr _ ha).2 x rfl hxp
  have hpK : ((3 : ℕ) : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K 2] at h
    norm_num at h
  have hsq := (altPrimaryData_spLin (p := 3) hpK hx).squarefree
  have hq2 : 2 ≤ 2 ^ s := Nat.le_self_pow (by omega) 2
  haveI : Finite (reciprocalOrbits (spEnd x)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  have hZc : (SymplecticFlag.proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [SymplecticHigher.ker_proj]
    exact SymplecticHigher.spScalars_le_center
  have hcomp := components_conj_of_orbit_family (SymplecticFlag.proj r K)
    SymplecticHigher.proj_surjective hZc x
    (fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set K[X]))
    (fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb)
    hjoin (fun O => CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.quasisimple_or_solvable_spSupported
      (by norm_num) hq2 hsq
      blocks O)
  obtain ⟨O₁, -, e₁⟩ := hcomp J₁ h1
  obtain ⟨O₂, -, e₂⟩ := hcomp J₂ h2
  obtain ⟨O₃, -, e₃⟩ := hcomp J₃ h3
  have hy : spEnd x ^ 3 = 1 := spEnd_pow hx
  have hO : ∀ O : reciprocalOrbits (spEnd x), ∃ h ∈ primaryFactors (spEnd x),
      ({h, reciprocalPolynomial h} : Set K[X]) = O.1 := by
    rintro ⟨O, h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩
  rcases exists_eq_of_three_reciprocalOrbits hy (hO O₁) (hO O₂) (hO O₃) with h | h | h
  · exact h12 (by rw [e₁, e₂, Subtype.ext h])
  · exact h13 (by rw [e₁, e₃, Subtype.ext h])
  · exact h23 (by rw [e₂, e₃, Subtype.ext h])

private theorem censusBodyB_at (d : TauCeti.ValidLieTypeIndex) {n : ℕ} {q : TauCeti.PrimePower}
    (hd : d.1 = TauCeti.LieTypeIndex.B n q) (hq2 : q.p = 2) : CensusBody d := by
  intro η hmem hη3 hη1 r hr hr1 J₁ J₂ J₃ hJ₁ hJ₂ hJ₃ h12 h13 h23 _ _ _
  exfalso
  classical
  have hS : KD264Lie.isSymplecticIdx d.1 := by
    rw [hd]
    exact Or.inr hq2
  obtain ⟨r', hr', hne, hcard, ⟨eP⟩⟩ := KD264Lie.exists_mulEquiv_statedProj_of_isSymplecticIdx hS
  haveI : Finite ↥d.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  have hfs : KD264Lie.fieldSize d.1 = 2 ^ q.exponent := by
    rw [hd]
    show q.card = _
    rw [TauCeti.PrimePower.card_def, hq2]
  have hK : Nat.card ↥d.fixedField = 2 ^ q.exponent := hcard.trans hfs
  have hne' : ¬ (r' = 2 ∧ 2 ^ q.exponent = 2) := fun h => hne ⟨h.1, hfs.trans h.2⟩
  let θ : (TauCeti.CFSGIndex.lie d).Group ≃* StatedProj (StatedSp r' ↥d.fixedField) := eP.symm
  let β' : MulAut (StatedProj (StatedSp r' ↥d.fixedField)) := θ.symm.trans (η.trans θ)
  have hβ'mem : β' ∈ innAutDerived (StatedProj (StatedSp r' ↥d.fixedField)) :=
    (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr θ).2 hmem
  have hβ'3 : β' ^ 3 = 1 := by
    have h3 := map_pow (MulAut.congr θ) η 3
    rw [hη3, map_one] at h3
    exact h3.symm
  have hβ'1 : β' ≠ 1 := by
    intro h1
    apply hη1
    exact (MulAut.congr θ).injective (by rw [map_one]; exact h1)
  obtain ⟨t, ht⟩ := KD264Lie.mem_inner_of_mem_innAutDerived_statedSp (f := q.exponent)
    Nat.prime_three (by norm_num) Nat.prime_two q.exponent_pos hK hr' hne' hβ'mem hβ'3
  have hZ : Subgroup.center (StatedProj (StatedSp r' ↥d.fixedField)) = ⊥ := by
    obtain ⟨hsimple, hperf⟩ :=
      CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (k := ↥d.fixedField) hr'
        (fun h => hne' ⟨h.1, hK.symm.trans h.2⟩)
    haveI := hsimple
    have hnc : ∃ u v : StatedProj (StatedSp r' ↥d.fixedField), u * v ≠ v * u := by
      by_contra h
      push Not at h
      exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨fun u v => h u v⟩⟩
    exact CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hnc
  have ht3 : t ^ 3 = 1 :=
    CFSG.mulAutConj_injective_of_center_eq_bot hZ (by rw [map_pow, ht, hβ'3, map_one])
  obtain ⟨x, hx, hx3⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_proj_eq_pow_eq_one_sp
      (r := r') (K := ↥d.fixedField) (by omega) Nat.prime_three (by norm_num) ht3
  have hβeq : β' = MulAut.conj (SymplecticFlag.proj r' ↥d.fixedField x) := by rw [← ht, ← hx]
  have hx1 : SymplecticFlag.proj r' ↥d.fixedField x ≠ 1 := by
    intro h1
    apply hβ'1
    rw [hβeq, h1, map_one]
  have hfix := CFSG.LocalAnalysis.GLTheoremA.map_fixSubgroup θ η
  have hJ' : ∀ {J : Subgroup (TauCeti.CFSGIndex.lie d).Group},
      IsComponentOf J (fixSubgroup η) → IsComponentOf (J.map θ.toMonoidHom)
        (fixSubgroup (MulAut.conj (SymplecticFlag.proj r' ↥d.fixedField x))) := by
    intro J hJ
    have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map θ hJ
    rw [← hβeq]
    exact hfix ▸ h1
  exact sp_false_of_three_components q.exponent_pos hK (by omega) x hx3 hx1 (hJ' hJ₁) (hJ' hJ₂)
    (hJ' hJ₃) (fun h => h12 (Subgroup.map_injective θ.injective h))
    (fun h => h13 (Subgroup.map_injective θ.injective h))
    (fun h => h23 (Subgroup.map_injective θ.injective h))

theorem censusBodyB : CensusBodyB := fun n q hv hq2 =>
  censusBodyB_at ⟨TauCeti.LieTypeIndex.B n q, hv⟩ rfl hq2

end CFSG.LocalAnalysis.GLTheoremA.T1428
