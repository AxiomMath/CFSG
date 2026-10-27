module

public import CFSG.ClassicalGroups.Orthogonal.DiagTorusNormalizesUnipotent
public import CFSG.RankThree.PartOne.KF.ClsOmega
public import CFSG.GroupTheory.SteinbergBSPrimeCoreAbsorption
public import CFSG.CGT.PushingUpLit.A78Sp4.Torus

public section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.Open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel

theorem exists_piSubgroup_three_le_pRank_in_borel_projective {m : Nat} (hm : 4 <= m)
    {F : Type} [Field F] [Finite F] [CharP F 2] {q : Nat} (hq : q.Prime) (hq2 : q != 2)
    (hdvd : q ∣ Nat.card F - 1) :
    exists H : Subgroup (StatedProj (StatedOmega (StatedQuadPlus m F))),
      H <= Subgroup.normalizer (plusProjectiveUnipotent m F) ∧
      IsPiSubgroup {p : Nat.Primes | (p : Nat) != 2} H ∧ 3 <= CFSG.Open.pRank q H := by
  classical
  have hbot : (StatedScalars (Fin m ⊕ Fin m) F).subgroupOf
      (StatedOmega (StatedQuadPlus m F)) = ⊥ :=
    CFSG.RankThree.PartOne.KFU.statedScalars_subgroupOf_statedOmega_quadPlus_eq_bot
      (K := F) (n := m) (by omega)
  have hmk : Function.Injective
      (QuotientGroup.mk' ((StatedScalars (Fin m ⊕ Fin m) F).subgroupOf
        (StatedOmega (StatedQuadPlus m F)))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact hbot
  refine ⟨(diagTorusOrth m F).map (QuotientGroup.mk' ((StatedScalars (Fin m ⊕ Fin m) F).subgroupOf
    (StatedOmega (StatedQuadPlus m F)))), ?_, ?_, ?_⟩
  ·
    have hN : diagTorusOrth m F ≤ Subgroup.normalizer
        (plusDerivedUnipotent m F : Set (StatedOmega (StatedQuadPlus m F))) :=
      diagTorusOrth_le_normalizer_plusDerivedUnipotent (m := m) (F := F) hm
    have h := (Subgroup.map_mono
        (f := QuotientGroup.mk' ((StatedScalars (Fin m ⊕ Fin m) F).subgroupOf
          (StatedOmega (StatedQuadPlus m F)))) hN).trans
      (Subgroup.le_normalizer_map (QuotientGroup.mk' ((StatedScalars (Fin m ⊕ Fin m) F).subgroupOf
        (StatedOmega (StatedQuadPlus m F)))))
    simpa [plusProjectiveUnipotent] using h
  ·
    have hoddUnits : Odd (Nat.card Fˣ) :=
      CFSG.CGT.PushingUpLit.A78Sp4.odd_card_units (K := F)
    have hoddFun : Odd (Nat.card (Fin m → Fˣ)) := by
      rw [Nat.card_fun, Nat.card_fin]
      exact hoddUnits.pow
    have hdvdPlus : Nat.card (diagTorusPlus m F) ∣ Nat.card (Fin m → Fˣ) := by
      rw [diagTorusPlus]
      exact Subgroup.card_range_dvd (diagGLPlusHom m F)
    have hoddPlus : Odd (Nat.card (diagTorusPlus m F)) := hoddFun.of_dvd_nat hdvdPlus
    have hdvdOrth : Nat.card (diagTorusOrth m F) ∣ Nat.card (diagTorusPlus m F) :=
      Subgroup.card_comap_dvd_of_injective (K := diagTorusPlus m F)
        (f := Subgroup.subtype (StatedOmega (StatedQuadPlus m F)))
        (Subgroup.subtype_injective _)
    have hoddOrth : Odd (Nat.card (diagTorusOrth m F)) := hoddPlus.of_dvd_nat hdvdOrth
    have hcardT : Nat.card ((diagTorusOrth m F).map
        (QuotientGroup.mk' ((StatedScalars (Fin m ⊕ Fin m) F).subgroupOf
          (StatedOmega (StatedQuadPlus m F))))) = Nat.card (diagTorusOrth m F) :=
      Subgroup.card_map_of_injective (K := diagTorusOrth m F)
        (f := QuotientGroup.mk' ((StatedScalars (Fin m ⊕ Fin m) F).subgroupOf
          (StatedOmega (StatedQuadPlus m F)))) hmk
    have hset : {p : Nat.Primes | (p : Nat) != 2} = {p : Nat.Primes | (p : Nat) ≠ 2} := by
      ext p
      simp
    rw [hset, CFSG.GroupTheory.SteinbergBS.isPiSubgroup_compl_iff (q := 2) Nat.prime_two,
      hcardT]
    exact Nat.coprime_two_left.mpr hoddOrth
  ·
    have hbase := three_le_pRank_diagTorus_orthogonal (m := m) (F := F) hm hq hdvd
    have hle := CFSG.SectionRank.pRank_le_map (p := q) hq.one_lt
      (QuotientGroup.mk' ((StatedScalars (Fin m ⊕ Fin m) F).subgroupOf
        (StatedOmega (StatedQuadPlus m F)))) hmk (diagTorusOrth m F)
    exact hbase.trans hle

end CFSG.ClassicalGroups.Orthogonal

end
