module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6PropSDefs
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalPairGeometry
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34f
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Residues

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_of_lineWeaklyClosed_three {P : Subgroup G} (hP : IsPGroup 3 P) {x : G}
    (hxP : x ∈ P) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hwc : LineWeaklyClosed x (P ⊓ centralizer ({x} : Set G))) :
    P ≤ centralizer ({x} : Set G) := by
  by_contra hnot
  set Q : Subgroup G := P ⊓ centralizer ({x} : Set G) with hQ
  have hlt : Q < P := inf_lt_left.mpr hnot
  have hgrow := pGroup_proper_subgroup_lt_internal_normalizer 3 Nat.prime_three P Q hP hlt
  obtain ⟨y, hy, hyQ⟩ := IsConcreteLE.exists_of_lt hgrow
  have hyP : y ∈ P := hy.1
  have hyN : y ∈ normalizer (Q : Set G) := hy.2
  have hxQ : x ∈ Q := ⟨hxP, mem_centralizer_singleton_iff.mpr rfl⟩
  have hx'Q : y * x * y⁻¹ ∈ Q := (mem_normalizer_iff.mp hyN x).mp hxQ
  have hle : (zpowers x).map (MulAut.conj y).toMonoidHom ≤ Q := by
    rw [MonoidHom.map_zpowers]
    exact zpowers_le.mpr hx'Q
  have hclosed := hwc y hle
  have hmem : y * x * y⁻¹ ∈ zpowers x := by
    have h : y * x * y⁻¹ ∈ (zpowers x).map (MulAut.conj y).toMonoidHom :=
      ⟨x, mem_zpowers x, rfl⟩
    rw [hclosed] at h
    exact h
  obtain ⟨m, hm⟩ := hP ⟨y, hyP⟩
  have hym : y ^ (3 ^ m) = 1 := congrArg Subtype.val hm
  have hxy := p34_conj_eq_of_pow hx1 hx3 hym hmem
  exact hyQ ⟨hyP, mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hxy)⟩

theorem GL83GenericPrimeThreeA6ShapeI.holds :
    GenericA6At G fun p P _ x J => A6Prop34 p P J x → A6ShapeI p P x := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ _
  subst hp3
  obtain ⟨hxP, hlo, -, -⟩ := hgen
  obtain ⟨-, hx1, hx3, -, -⟩ := hlo
  exact fun hwc => le_centralizer_of_lineWeaklyClosed_three P.isPGroup' hxP hx3 hx1 hwc

theorem GL83GenericPrimeThreeA6Lemma43.of_S (hVI : GL83GenericPrimeThreeA6ShapeVI G)
    (h : GL83GenericPrimeThreeA6Lemma43S G) : GL83GenericPrimeThreeA6Lemma43 G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ h34
  refine h p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hQ
    ⟨h34, ?_, ?_⟩
  · exact GL83GenericPrimeThreeA6ShapeI.holds p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt
      hmin hnot Q ψ hψ hker hQ h34
  · exact hVI p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hQ h34

end CFSG.LocalAnalysis.RankThreeTheoremC
