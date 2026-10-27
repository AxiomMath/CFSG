module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5Asc25Main
public import CFSG.GF2Type.Aschbacher1976Common.NotZStar
public import CFSG.GF2Type.Aschbacher1976Common.DihedralEvenRank

public section

namespace CFSG.GF2Type.Aschbacher1976Common

open CFSG.EvenSporadicStandard.Finkelstein77 CFSG.ComponentClassification.AschbacherKnownGroup

private theorem hasDihedralSylowTwo_of_mulEquiv' {X Y : Type} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y) (h : HasDihedralSylowTwo X) : HasDihedralSylowTwo Y := by
  obtain ⟨S, n, hn, ⟨eS⟩⟩ := h
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, n, hn, ⟨?_⟩⟩
  exact ((S : Subgroup X).equivMapOfInjective e.toMonoidHom e.injective).symm.trans eS

private theorem hasSemidihedralSylowTwo_of_mulEquiv' {X Y : Type} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y) (h : HasSemidihedralSylowTwo X) : HasSemidihedralSylowTwo Y := by
  obtain ⟨S, n, hn, ⟨eS⟩⟩ := h
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, n, hn, ⟨?_⟩⟩
  exact ((S : Subgroup X).equivMapOfInjective e.toMonoidHom e.injective).symm.trans eS

section Certified

theorem dihedral_or_semidihedral_of_weaklyClosed {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {x : G} (hx : orderOf x = 4)
    (hwc : WeaklyClosedInNormalizer (Subgroup.zpowers x)) :
    HasDihedralSylowTwo G ∨ HasSemidihedralSylowTwo G := by
  have hdvd : 2 ∣ orderOf x := by rw [hx]; norm_num
  have hz2 : orderOf (x ^ 2) = 2 := by
    have h : orderOf (x ^ 2) = orderOf x / 2 := orderOf_pow_of_dvd (by norm_num) hdvd
    rw [hx] at h
    exact h
  have htop : Subgroup.normalClosure ({x ^ 2} : Set G) = ⊤ := by
    apply Subgroup.normalClosure_normal.eq_bot_or_eq_top.resolve_left
    intro hbot
    have hmem : x ^ 2 ∈ Subgroup.normalClosure ({x ^ 2} : Set G) :=
      Subgroup.subset_normalClosure (Set.mem_singleton _)
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [hmem, orderOf_one] at hz2
    omega
  let e : ↥(Subgroup.normalClosure ({x ^ 2} : Set G)) ≃* G :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  rcases CFSG.ComponentClassification.Foote5.Asc25.asc76Lemma25 G x hx hwc with hz | hD | hSD
  · exact absurd hz (not_inZStar_of_isSimpleGroup hnab hz2)
  · exact Or.inl (hasDihedralSylowTwo_of_mulEquiv' e hD)
  · exact Or.inr (hasSemidihedralSylowTwo_of_mulEquiv' e hSD)

theorem not_weaklyClosed_of_charTwo {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hchar : CFSG.Open.IsCharTwoType G)
    (he : 2 ≤ CFSG.Open.evenRank G) {x : G} (hx : orderOf x = 4) :
    ¬ WeaklyClosedInNormalizer (Subgroup.zpowers x) := by
  intro hwc
  have h := dihedral_or_semidihedral_of_weaklyClosed hnab hx hwc
  have h1 := evenRank_le_one_of_dihedral_or_semidihedral h hchar
  omega

end Certified

end CFSG.GF2Type.Aschbacher1976Common
