module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

section Asm


theorem i1431LieS_of_residuals (hT : LieSTypeChar) (h3 : LieS3) (hI : LieSInn) (hO : LieSOut)
    (h2 : LieSTwo) (h8 : LieSEight) : I1431LieS := by
  intro Y _ _ hY hcore hRk hcat ξ hξ3 hξ1 J hJ hJT
  have hJ0 : GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup ξ) J := hJ
  obtain ⟨hTy, hSp48⟩ := hJT
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | lie d =>
    obtain ⟨J', hJ', ψ, hψs, hψk⟩ := component_to_simple_explicit hJ0
    have hq : CFSG.Open.IsQuasisimple (PQuot 3 J) :=
      CFSG.HardMathSupport.Solomon.LocalBalance.isQuasisimple_quotient_of_glaPComponent hJ0
    have hq' : CFSG.Open.IsQuasisimple (PQuot 3 J') :=
      CFSG.HardMathSupport.Solomon.LocalBalance.isQuasisimple_quotient_of_glaPComponent hJ'
    haveI : Nontrivial (PQuot 3 J') := by
      have := hq'.2.toNontrivial
      obtain ⟨a, b, hab⟩ := exists_pair_ne (PQuot 3 J' ⧸ Subgroup.center (PQuot 3 J'))
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      exact ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
    obtain ⟨eP⟩ := CFSG.LocalAnalysis.GLTheoremA.psimple_equiv_of_central_surj hq ψ hψs hψk
    have htr : ∀ {T : TauCeti.CFSGIndex → Prop}, catalogIs (PSimple 3 J) T →
        catalogIs (PSimple 3 J') T := by
      intro T hT0
      obtain ⟨i', hi', ⟨f⟩⟩ := hT0
      exact ⟨i', hi', ⟨eP.symm.trans f⟩⟩
    have htr' : ∀ {T : TauCeti.CFSGIndex → Prop}, catalogIs (PSimple 3 J') T →
        catalogIs (PSimple 3 J) T := by
      intro T hT0
      obtain ⟨i', hi', ⟨f⟩⟩ := hT0
      exact ⟨i', hi', ⟨eP.trans f⟩⟩
    have hβ3 : inducedAut ξ ^ 3 = 1 := by
      rw [show inducedAut ξ =
          CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot Y ξ from rfl,
        ← map_pow, hξ3, map_one]
    have hβ1 : inducedAut ξ ≠ 1 := fun h => hξ1 (eq_one_of_inducedAut_eq_one hY.1 h)
    have hS : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hY.2
    have hnab : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hY
    have hchS : IsChevSimple d.1.characteristic (Y ⧸ Subgroup.center Y) :=
      Or.inl ⟨.lie d, rfl, ⟨e⟩⟩
    have hchJ := CFSG.LocalAnalysis.GLTheoremA.kdChevDownQ_three_of_lieComp
      CFSG.LocalAnalysis.GLTheoremA.lieComp_holds d.1.characteristic (Y ⧸ Subgroup.center Y) hS
      hnab hchS (inducedAut ξ) hβ3 J' hJ'
    rcases hT _ _ (htr hTy) hchJ with ⟨h2c, hSp | hSp⟩ | ⟨h3c, hL⟩
    ·
      by_cases hin : inducedAut ξ ∈ innAutDerived (Y ⧸ Subgroup.center Y)
      · have hf := (hI _ hS hnab d h2c ⟨e⟩ _ hin hβ3 hβ1).1 ⟨J', hJ', hSp⟩
        rcases (h2 Y hY hcore hRk d h2c hf ⟨e⟩ _ hin hβ3 hβ1).1 ⟨J', hJ', hSp⟩ with h | h
        · exact ⟨.lie d, Or.inl h, ⟨e⟩⟩
        · exact ⟨.lie d, Or.inr (Or.inl h), ⟨e⟩⟩
      · exact ⟨.lie d, Or.inr (Or.inr (Or.inl
          ((hO _ hS hnab d h2c ⟨e⟩ _ hin hβ3).1 ⟨J', hJ', hSp⟩))), ⟨e⟩⟩
    ·
      by_cases hin : inducedAut ξ ∈ innAutDerived (Y ⧸ Subgroup.center Y)
      · rcases (hI _ hS hnab d h2c ⟨e⟩ _ hin hβ3 hβ1).2 ⟨J', hJ', hSp⟩ with hf | hf
        · exact ((h2 Y hY hcore hRk d h2c hf ⟨e⟩ _ hin hβ3 hβ1).2 ⟨J', hJ', hSp⟩).elim
        · have hSpJ : catalogIs (PSimple 3 J) S8.L84.isSp48 := htr' hSp
          exact ⟨.lie d, Or.inr (Or.inr (Or.inl (h8 Y hY hcore hRk d h2c hf ⟨e⟩ ξ hξ3 hξ1 hin J
            hJ0 hSpJ (hSp48 hSpJ)))), ⟨e⟩⟩
      · exact ⟨.lie d, Or.inr (Or.inr (Or.inr (Or.inl
          ((hO _ hS hnab d h2c ⟨e⟩ _ hin hβ3).2 ⟨J', hJ', hSp⟩)))), ⟨e⟩⟩
    ·
      exact ⟨.lie d, Or.inr (Or.inr (Or.inr (Or.inr
        (h3 _ hS hnab d h3c ⟨e⟩ _ hβ3 hβ1 ⟨J', hJ', hL⟩)))), ⟨e⟩⟩
  | _ => exact hi.elim

end Asm

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
