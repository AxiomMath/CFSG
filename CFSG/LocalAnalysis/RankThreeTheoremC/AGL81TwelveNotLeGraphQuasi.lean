module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphHatDefs
import CFSG.GH74.GLS.Stage2.Bender.Thm2.L128LyBridge
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Reduce
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe

open CFSG.Open Subgroup

theorem not_isPerfect_perm_three : ¬ Group.IsPerfect (Equiv.Perm (Fin 3)) := by
  intro h
  haveI : Group.IsPerfect ℤˣ := Group.IsPerfect.ofSurjective (Equiv.Perm.sign_surjective (Fin 3))
  haveI : Subsingleton ℤˣ := inferInstance
  exact absurd (Subsingleton.elim (1 : ℤˣ) (-1)) (by decide)

theorem false_of_subnormal_symThree_of_isQuasisimple {R : Type} [Group R]
    (hR : Open.IsQuasisimple R) {X : Subgroup R} (hX : Sym.IsSymThree X)
    (hXs : IsSubnormal X ⊤) : False := by
  have hq := CFSG.GH74.GLS.Stage2.Bender.Thm2.L128.isQuasisimple_of_open hR
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hq
    (IsSubnormal.top_iff.1 hXs) with htop | hcen
  · obtain ⟨e⟩ := hX
    have hperf : Group.IsPerfect R := ⟨hR.1⟩
    let e' : R ≃* Equiv.Perm (Fin 3) :=
      (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans e
    haveI : Group.IsPerfect (Equiv.Perm (Fin 3)) :=
      Group.IsPerfect.ofSurjective (f := e'.toMonoidHom) e'.surjective
    exact not_isPerfect_perm_three inferInstance
  · obtain ⟨a, haX, ha1, ha3, hXa, ⟨s, hs, hs2, hs1⟩, -⟩ := Sym.symThree_data hX
    obtain ⟨hinv, -⟩ := hXa s hs hs2 hs1
    have hac : s * a * s⁻¹ = a := by
      have := Subgroup.mem_center_iff.1 (hcen haX) s
      rw [this]
      group
    rw [hinv] at hac
    have ha2 : a ^ 2 = 1 := by
      calc a ^ 2 = a * a := pow_two a
        _ = a * a⁻¹ := by rw [hac]
        _ = 1 := mul_inv_cancel a
    apply ha1
    calc a = a ^ 3 * (a ^ 2)⁻¹ := by group
      _ = 1 := by rw [ha3, ha2]; group

theorem noTwoSymThree_of_quasisimple {A : Type} [Group A] {Y : Subgroup A}
    (hY : Open.IsQuasisimple ↥Y) (hO : pCoreOf 2 Y = ⊥) : NoTwoSymThree Y := by
  intro X X' hX hX' hXs hXs'
  have hP : CFSG.pCore 2 ↥Y = ⊥ := ParabCensus.pCore_eq_bot_of_pCoreOf_eq_bot hO
  let e : (↥Y ⧸ CFSG.pCore 2 ↥Y) ≃* ↥Y :=
    (QuotientGroup.quotientMulEquivOfEq hP).trans QuotientGroup.quotientBot
  exact (false_of_subnormal_symThree_of_isQuasisimple (Open.IsQuasisimple.of_mulEquiv e hY)
    hX hXs).elim

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe
