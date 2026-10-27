module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIIOut
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltDefs
public import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd

public section

namespace CFSG.AGLEmbedding

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem mem_sup_centralizer_of_not_dvd_card_outer {Y : Type*} [Group Y] {L : Subgroup Y}
    {p k : ℕ} (hp : p.Prime) (hout : ¬ p ∣ Nat.card (Outer L)) {x : Y}
    (hx : x ∈ Subgroup.normalizer (L : Set Y)) (hxp : x ^ p ^ k = 1) :
    x ∈ L ⊔ Subgroup.centralizer (L : Set Y) := by
  set a : MulAut L := L.normalizerMonoidHom ⟨x, hx⟩ with ha
  have hak : a ^ p ^ k = 1 := by
    rw [ha, ← map_pow]
    have : (⟨x, hx⟩ : Subgroup.normalizer (L : Set Y)) ^ p ^ k = 1 :=
      Subtype.ext (by simpa using hxp)
    rw [this, map_one]
  have hcop : (p ^ k).Coprime (Nat.card (Outer L)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hout)
  have hψ : QuotientGroup.mk' (inner L) a = 1 :=
    (pow_eq_one_iff_of_coprime hcop).mp ⟨by rw [← map_pow, hak, map_one], pow_card_eq_one'⟩
  obtain ⟨l, hl⟩ := (QuotientGroup.eq_one_iff _).mp hψ
  have hcent : (l : Y)⁻¹ * x ∈ Subgroup.centralizer (L : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hl ⟨y, hy⟩)
    change (l : Y) * y * (l : Y)⁻¹ = x * y * x⁻¹ at h1
    calc y * ((l : Y)⁻¹ * x) = (l : Y)⁻¹ * ((l : Y) * y * (l : Y)⁻¹) * x := by group
      _ = (l : Y)⁻¹ * (x * y * x⁻¹) * x := by rw [h1]
      _ = (l : Y)⁻¹ * x * y := by group
  rw [show x = (l : Y) * ((l : Y)⁻¹ * x) by group]
  exact Subgroup.mul_mem_sup l.2 hcent

theorem card_outer_dvd_card_outer_centerQuotient (L : Type*) [Group L] [Group.IsPerfect L] :
    Nat.card (Outer L) ∣ Nat.card (Outer (L ⧸ Subgroup.center L)) :=
  Subgroup.card_dvd_of_injective _
    (CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_outer_injective L)

theorem five_le_of_isPerfect_mulEquiv_alternatingGroup {X : Type*} [Group X]
    [Group.IsPerfect X] [Nontrivial X] {m : ℕ} (e : X ≃* alternatingGroup (Fin m)) : 5 ≤ m := by
  by_contra h5
  have hsolv : Group.IsSolvable (alternatingGroup (Fin m)) :=
    alternatingGroup.isSolvable (by rw [Nat.card_fin]; omega)
  have : Group.IsSolvable X :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact Group.IsPerfect.not_isSolvable X this

theorem kFactBlockOutPrime_of_orthTwo : KFactBlockOutPrime := by
  have h := kFactOutOrthTwoPrime_holds
  intro Y _ _ L hL p hp hp5 hOA x hx hxp
  refine mem_sup_centralizer_of_not_dvd_card_outer (k := 1) hp ?_ hx (by simpa using hxp)
  have hq := hL.2.2
  have : Group.IsPerfect L := Group.isPerfect_def.mpr hq.1
  have : Nontrivial (L ⧸ Subgroup.center L) := hq.2.toNontrivial
  have : Nontrivial L := (QuotientGroup.mk'_surjective (Subgroup.center L)).nontrivial
  have hp2 : p ≠ 2 := by omega
  rcases hOA with hO | ⟨m, hm⟩
  · rcases hO with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
      exact h d hd p hp hp5
    · rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
      exact not_dvd_card_outer_alternatingGroup n (by omega) p hp hp2
  · rcases hm with hm | hm
    · obtain ⟨e⟩ := hm
      rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
      exact not_dvd_card_outer_alternatingGroup m
        (five_le_of_isPerfect_mulEquiv_alternatingGroup e) p hp hp2
    · obtain ⟨e⟩ := hm
      intro hdvd
      refine not_dvd_card_outer_alternatingGroup m
        (five_le_of_isPerfect_mulEquiv_alternatingGroup e) p hp hp2 ?_
      rw [← Nat.card_congr
        (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
      exact hdvd.trans (card_outer_dvd_card_outer_centerQuotient L)

theorem kFactBlockOutPrime_holds : KFactBlockOutPrime :=
  kFactBlockOutPrime_of_orthTwo

end CFSG.AGLEmbedding
