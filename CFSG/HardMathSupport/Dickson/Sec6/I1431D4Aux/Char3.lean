module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Descent
public import CFSG.HardMathSupport.Dickson.KD.CharPAux.ClassOrth
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Defs

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.RankThree.PartTwo.KFacts CFSG.HardMathSupport.Dickson.KD

theorem d4_fixSub_conj_eq_centralizer {T : Type*} [Group T] (u : T) :
    fixSub (MulAut.conj u) = Subgroup.centralizer ({u} : Set T) := by
  ext y
  rw [mem_fixSub, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    exact (mul_inv_eq_iff_eq_mul.1 h).symm
  · intro h
    exact mul_inv_eq_iff_eq_mul.2 h.symm

theorem center_quotient_center_eq_bot {Y : Type} [Group Y] (hq : CFSG.Open.IsQuasisimple Y) :
    Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ := by
  haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hq.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.center (Y ⧸ Subgroup.center Y)) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := CFSG.HardMathSupport.Dickson.Sec6.I923.exists_not_comm_of_quasisimple hq
    have ha : a ∈ Subgroup.center (Y ⧸ Subgroup.center Y) := by rw [h]; trivial
    exact hab ((Subgroup.mem_center_iff.1 ha b).symm)

theorem exists_order_three_of_inner {Y : Type} [Group Y] (hq : CFSG.Open.IsQuasisimple Y)
    {ξ : MulAut Y} (hξ : IsInnerAut ξ) (hξ3 : ξ ^ 3 = 1) (hξ1 : ξ ≠ 1) :
    ∃ u : Y ⧸ Subgroup.center Y, orderOf u = 3 ∧
      centerDescend Y ξ = MulAut.conj u := by
  haveI : Group.IsPerfect Y := ⟨hq.1⟩
  obtain ⟨x, hx⟩ := hξ
  have hψ : centerDescend Y ξ = MulAut.conj (x : Y ⧸ Subgroup.center Y) := by
    rw [← hx, CFSG.RankThree.PartTwo.KFacts.centerDescend_conj]
  have hcen := center_quotient_center_eq_bot hq
  have h3 : (x : Y ⧸ Subgroup.center Y) ^ 3 = 1 := by
    have h1 : (MulAut.conj (x : Y ⧸ Subgroup.center Y)) ^ 3 = 1 := by
      rw [← hψ, ← map_pow, hξ3, map_one]
    have h2 : MulAut.conj ((x : Y ⧸ Subgroup.center Y) ^ 3) = 1 := by
      rw [map_pow]
      exact h1
    have hz : (x : Y ⧸ Subgroup.center Y) ^ 3 ∈ Subgroup.center (Y ⧸ Subgroup.center Y) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h4 := congrArg (fun φ : MulAut (Y ⧸ Subgroup.center Y) => φ g) h2
      simp only [MulAut.conj_apply, MulAut.one_apply] at h4
      exact (mul_inv_eq_iff_eq_mul.1 h4).symm
    rw [hcen] at hz
    exact Subgroup.mem_bot.1 hz
  have h1 : (x : Y ⧸ Subgroup.center Y) ≠ 1 := by
    intro h
    apply hξ1
    refine eq_one_of_forall_mul_inv_mem_center fun s => ?_
    have h5 : centerDescend Y ξ = 1 := by rw [hψ, h, map_one]
    have h6 := congrArg (fun τ : MulAut (Y ⧸ Subgroup.center Y) => τ (s : Y ⧸ Subgroup.center Y))
      h5
    simp only [centerDescend_mk, MulAut.one_apply] at h6
    exact QuotientGroup.eq.mp h6.symm
  exact ⟨(x : Y ⧸ Subgroup.center Y), orderOf_eq_prime h3 h1, hψ⟩

theorem Y1431Cfg.false_of_char3 {V : InndiagVocab} {Y : Type} [Group Y] [Finite Y]
    {Â : Subgroup (MulAut Y)} {ξ : MulAut Y} {J : Subgroup Y} {q : ℕ}
    (c : Y1431Cfg V Y Â ξ J q) {f : ℕ}
    (hm : StatedClassicalModel (Y ⧸ Subgroup.center Y) .POmegaPlus 4 3 f)
    (hξ : IsInnerAut ξ) : False := by
  have hKD : KDCharPAt 3 (Y ⧸ Subgroup.center Y) :=
    kdCharPAt_of_model_POmegaPlus hm (by norm_num)
  obtain ⟨u, hu, hψ⟩ := exists_order_three_of_inner c.quasisimple hξ
    (c.elemAbelian.2 ξ c.mem) c.ne_one
  obtain ⟨A, hA, -⟩ := exists_comp_typeL2_quotient ξ c.comp c.typeL2
  rw [hψ, d4_fixSub_conj_eq_centralizer] at hA
  have hle : A ≤ GLAPLayer 3 (Subgroup.centralizer ({u} : Set (Y ⧸ Subgroup.center Y))) :=
    le_sSup hA
  rw [hKD u hu] at hle
  exact glaPComponent_ne_bot hA (le_bot_iff.1 hle)

end CFSG.HardMathSupport.Dickson.Sec6.I1431
