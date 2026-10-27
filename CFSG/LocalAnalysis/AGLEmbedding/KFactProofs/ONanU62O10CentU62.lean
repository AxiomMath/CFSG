module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU62O10CentU62Diag
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.U62ThreeCentMain
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU62Fix
import CFSG.RankThree.PartOne.Q1327C.BU5Diag

public section

namespace CFSG.AGLEmbedding.U62O10Cent

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62
  CFSG.AGLEmbedding.U62ThreeCent

theorem exists_diag_conj {x : P6} (hx : orderOf x = 3) :
    ∃ (P : GU6) (a : gramSU uData M6) (κ : Fin 6 → ZMod 3),
      (a : GL (Fin 6) F4) = dK κ ∧ conj6 P (a : P6) = x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hg3 : (g : GL (Fin 6) F4) ^ 3 = 1 := by
    refine pow_three_eq_one_of_mem g ?_
    have := pow_orderOf_eq_one (g : P6)
    rwa [hx] at this
  set g' : GU6 := ⟨(g : GL (Fin 6) F4), g.2.1⟩ with hg'
  have hg'3 : g' ^ 3 = 1 := Subtype.ext hg3
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_three
  have hcomm : ∀ u ∈ Subgroup.zpowers g', ∀ v ∈ Subgroup.zpowers g', u * v = v * u := by
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    exact ((Commute.refl g').zpow_zpow m n).eq
  have hpow : ∀ u ∈ Subgroup.zpowers g', u ^ 3 = 1 := by
    rintro _ ⟨m, rfl⟩
    have := zpow_comm g' m 3
    simpa [hg'3] using this
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.Q1327C.exists_unitary_conj_diag_m uData hζ
    (by norm_num : 3 ∣ 2 ^ 1 + 1) (Subgroup.zpowers g') hcomm hpow
  have hdiag := hP g' (Subgroup.mem_zpowers g')
  let a : gramSU uData M6 := ⟨(P : GL (Fin 6) F4)⁻¹ * g * (P : GL (Fin 6) F4), by
    simpa using conj_mem_gramSU uData M6 (inv_mem P.2) g.2⟩
  obtain ⟨δ, hδ⟩ := exists_units_diag (g := (a : GL (Fin 6) F4)) hdiag
  choose κ hκ using fun i => exists_rootUnit (δ i)
  refine ⟨P, a, κ, ?_, ?_⟩
  · rw [hδ]
    congr 1
    funext i
    exact (hκ i).symm
  · rw [primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    change (P : GL (Fin 6) F4) * ((P : GL (Fin 6) F4)⁻¹ * g * (P : GL (Fin 6) F4)) *
      (P : GL (Fin 6) F4)⁻¹ = g
    group

theorem centAlt_P6 {x : P6} (hx : orderOf x = 3) : CentAlt x := by
  obtain ⟨P, a, κ, ha, hconj⟩ := exists_diag_conj hx
  have hord : orderOf (a : P6) = 3 := by
    rw [← hx, ← hconj]
    exact (MulEquiv.orderOf_eq (conj6 P) (a : P6)).symm
  have := centAlt_map (conj6 P) (centAlt_diag κ a ha hord)
  rwa [hconj] at this

theorem u62ThreeCentAut {L : Type} [Group L] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsUSixTwoIndex d) (h : Nonempty (L ≃* CatGroup d)) {x : L} (hx : orderOf x = 3) :
    CentAlt x := by
  obtain ⟨e⟩ := nonempty_equiv_P6 hd h
  have h1 := centAlt_map e.symm (centAlt_P6 (x := e x) (by rw [MulEquiv.orderOf_eq, hx]))
  rwa [MulEquiv.symm_apply_apply] at h1

end CFSG.AGLEmbedding.U62O10Cent
