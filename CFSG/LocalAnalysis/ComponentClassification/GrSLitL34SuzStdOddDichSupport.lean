module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCyclic
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroSupport

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

theorem l34SuzOddDich_support (hcat : L34CyclicProperFixedCatalog) {H : Type} [Group H]
    [Finite H] (hK : SectionRank.IsKGroupCat H) {s : H} (hs : orderOf s = 2) {Λ : Subgroup H}
    (hΛs : Λ ≤ centralizer ({s} : Set H)) (hΛq : IsQuasisimple ↥Λ)
    (hΛn : (Λ.subgroupOf (centralizer ({s} : Set H))).Normal)
    (hΛodd : Odd (Nat.card (center ↥Λ))) (hΛL : IsL34Type (↥Λ ⧸ center ↥Λ)) :
    IsComponent (Λ.map (QuotientGroup.mk' (pPrimeCore 2 H))) ∨
      (∃ L : Subgroup (H ⧸ pPrimeCore 2 H), IsComponent L ∧ Λ.map (QuotientGroup.mk' (pPrimeCore 2 H)) ≤ L ∧
        (Blueprint.NativeSporadic.IsSporadic (↥L ⧸ center ↥L) .Suz ∨
          Blueprint.NativeSporadic.IsSporadic (↥L ⧸ center ↥L) .ONan ∨
          Blueprint.LieModel (↥L ⧸ center ↥L) .PSL 3 2 4)) ∨
      (∃ L : Subgroup (H ⧸ pPrimeCore 2 H), IsComponent L ∧
        L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 H) s)).toMonoidHom ≠ L ∧ IsL34Type (↥L ⧸ center ↥L) ∧
        ((Λ.map (QuotientGroup.mk' (pPrimeCore 2 H)) : Subgroup (H ⧸ pPrimeCore 2 H)) : Set (H ⧸ pPrimeCore 2 H)) =
          {g | ∃ k ∈ L, k * (QuotientGroup.mk' (pPrimeCore 2 H) s * k * (QuotientGroup.mk' (pPrimeCore 2 H) s)⁻¹) = g} ∧
        ∀ L' : Subgroup (H ⧸ pPrimeCore 2 H), IsComponent L' →
          (⁅Λ.map (QuotientGroup.mk' (pPrimeCore 2 H)), L'⁆ ≠ ⊥ ↔
            L' = L ∨ L' = L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 H) s)).toMonoidHom)) := by
  have hΛcomp : IsComponent (Λ.subgroupOf (centralizer ({s} : Set H))) :=
    ⟨(CFSG.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hΛs)).mpr hΛq,
      hΛn.isSubnormal⟩
  rcases l34Zero_support hcat hK hs hΛs hΛcomp hΛodd hΛL with
    h | ⟨L, hL, hLe, -, htype⟩ | ⟨L, hL, hne, hL34, hdiag, hsupp⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨L, hL, hLe, htype⟩)
  · exact Or.inr (Or.inr ⟨L, hL, hne, hL34, hdiag, hsupp⟩)

end CFSG.ComponentClassification.GrSLit.L34Sec5S
