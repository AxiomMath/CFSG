module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Inv10

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG CFSG.LocalCores CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

section Sig3

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}
  (hb : PAB G L t E W z) (a : PA7 L t E z) {K : Subgroup ↥(Cen a.ub)} (hK : IsComponent K)
  (hcj : cj (tG hb a.toPA6.toPA5) K = K)
  (hall : ∀ K' : Subgroup ↥(Cen a.ub), IsComponent K' → K' = K)

include hb a hK hcj hall

theorem Jtilde_equiv : Nonempty (↥(Jtilde hb a K) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨eJ⟩ := s8_J_equiv a.Abar a.eAbar
  have hJK := JG_le_K hb a hK hcj hall
  let mk : ↥K →* ↥K ⧸ center ↥K := QuotientGroup.mk' (center ↥K)
  have hcen : center ↥(JG hb a.toPA6.toPA5) = ⊥ :=
    center_eq_bot_of_simple (JG_simple hb a.toPA6.toPA5) (JG_nonab hb a.toPA6.toPA5)
  have hinj : Function.Injective (mk.comp (JKsub hb a K).subtype) := by
    rw [injective_iff_map_eq_one]
    intro j hj
    have hz : ((j : ↥K)) ∈ center ↥K := (QuotientGroup.eq_one_iff _).1 hj
    have hjJ : ((j : ↥K) : ↥(Cen a.ub)) ∈ JG hb a.toPA6.toPA5 := j.2
    have hmem : (⟨((j : ↥K) : ↥(Cen a.ub)), hjJ⟩ : ↥(JG hb a.toPA6.toPA5)) ∈
        center ↥(JG hb a.toPA6.toPA5) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := Subgroup.mem_center_iff.1 hz ⟨(g : ↥(Cen a.ub)), hJK g.2⟩
      have h2 : (g : ↥(Cen a.ub)) * ((j : ↥K) : ↥(Cen a.ub)) =
          ((j : ↥K) : ↥(Cen a.ub)) * (g : ↥(Cen a.ub)) :=
        congrArg (fun x : ↥K => (x : ↥(Cen a.ub))) this
      exact Subtype.ext h2
    rw [hcen, Subgroup.mem_bot] at hmem
    exact Subtype.ext (Subtype.ext
      (congrArg (fun x : ↥(JG hb a.toPA6.toPA5) => (x : ↥(Cen a.ub))) hmem))
  exact ⟨(MonoidHom.ofInjective hinj).symm.trans
    ((Subgroup.subgroupOfEquivOfLe hJK).trans ((JG_equiv hb a.toPA6.toPA5).trans eJ))⟩

theorem inv_derived :
    Nonempty (↥(commutator ↥(autCentralizer (tauHat hb a hK hcj hall))) ≃*
      alternatingGroup (Fin 6)) := by
  obtain ⟨eJt⟩ := Jtilde_equiv hb a hK hcj hall
  set N := autCentralizer (tauHat hb a hK hcj hall) with hN
  have hle : Jtilde hb a K ≤ N := Jtilde_le hb a hK hcj hall
  set Jt' : Subgroup ↥N := (Jtilde hb a K).subgroupOf N with hJt'
  let e1 : ↥Jt' ≃* ↥(Jtilde hb a K) := Subgroup.subgroupOfEquivOfLe hle
  have hs : IsSimpleGroup ↥Jt' := (MulEquiv.isSimpleGroup_congr (e1.trans eJt)).2 s8_A6_simple
  have hna : ∃ x y : ↥Jt', x * y ≠ y * x := by
    obtain ⟨a1, b1, h⟩ := s8_A6_nonab
    exact ⟨(e1.trans eJt).symm a1, (e1.trans eJt).symm b1, fun hh => h (by
      have := congrArg (e1.trans eJt) hh
      simpa using this)⟩
  have hperf : ⁅Jt', Jt'⁆ = Jt' := commutator_eq_self_of_simple hs hna
  have hEq : commutator ↥N = Jt' := by
    apply le_antisymm
    · rw [_root_.commutator_def, Subgroup.commutator_le]
      intro x _ y _
      show ((⁅x, y⁆ : ↥N) : ↥K ⧸ center ↥K) ∈ Jtilde hb a K
      have := inv_comm_mem hb a hK hcj hall x.2 y.2
      simpa [commutatorElement_def] using this
    · calc Jt' = ⁅Jt', Jt'⁆ := hperf.symm
        _ ≤ commutator ↥N := by
          rw [_root_.commutator_def]; exact Subgroup.commutator_mono le_top le_top
  exact ⟨(MulEquiv.subgroupCongr hEq).trans (e1.trans eJt)⟩

end Sig3

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
