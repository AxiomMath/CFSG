module

public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem le_centralizer_of_isCyclic_of_normal {G : Type*} [Group G] {J P : Subgroup G}
    (hJ : ⁅J, J⁆ = J) [P.Normal] [IsCyclic P] : J ≤ Subgroup.centralizer (P : Set G) := by
  let f : G →* (ZMod (Nat.card P))ˣ :=
    (IsCyclic.mulAutMulEquiv P).toMonoidHom.comp MulAut.conjNormal
  have hker : ⁅J, J⁆ ≤ f.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm,
      mul_comm]
  intro j hj
  rw [← hJ] at hj
  have hfj : f j = 1 := MonoidHom.mem_ker.mp (hker hj)
  have hj1 : MulAut.conjNormal j = (1 : MulAut P) :=
    (IsCyclic.mulAutMulEquiv P).injective (hfj.trans (map_one _).symm)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' := congrArg Subtype.val (DFunLike.congr_fun hj1 ⟨x, hx⟩)
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at hx'
  calc x * j = j * x * j⁻¹ * j := by rw [hx']
    _ = j * x := by group

namespace JStarHyp

variable {Y : Type} [Group Y] [Finite Y] {p n : ℕ} [Fact p.Prime] {Rb : Sylow p Y}
  {Y₀ Jt Xt : Subgroup Y} {φ : Jt →* PSL2GF p n}

theorem false_of_forall_le_centralizer (h : JStarHyp p n Rb Y₀ Jt Xt φ) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤)
    (hall : ∀ K : Subgroup Y, IsComponentOf K ⊤ → Jt ≤ Subgroup.centralizer (K : Set Y)) :
    False := by
  have : (CFSG.pCore p Y).Normal := CFSG.pCore_normal
  have : IsCyclic (CFSG.pCore p Y) := h.red.isCyclic_pCore_of_component hL
  have hF : CFSG.generalizedFitting Y ≤ Subgroup.centralizer (Jt : Set Y) := by
    refine sup_le ?_ (sSup_le fun K hK => ?_)
    · rw [CFSG.Fitting_eq_pcore Y p h.red.core_eq_bot]
      exact Subgroup.le_centralizer_iff.mp (le_centralizer_of_isCyclic_of_normal h.commutator_eq)
    · exact Subgroup.le_centralizer_iff.mp (hall K ((CFSG.isComponent_iff_open K).mp hK))
  have hJF : Jt ≤ Subgroup.centralizer (CFSG.generalizedFitting Y : Set Y) :=
    Subgroup.le_centralizer_iff.mp hF
  have hJJ : Jt ≤ Subgroup.centralizer (Jt : Set Y) :=
    hJF.trans (Subgroup.centralizer_le (hJF.trans (CFSG.centralizer_generalizedFitting_le Y)))
  have hbot : Jt = ⊥ := by
    rw [← h.commutator_eq]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hJJ
  exact (Subgroup.nontrivial_iff_ne_bot Jt).mp h.nontrivial hbot

theorem false_of_not_le_centralizer (h : JStarHyp p n Rb Y₀ Jt Xt φ) (hβ : KFactBeta)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hcyc : IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    (hJL : ¬ Jt ≤ Subgroup.centralizer (L : Set Y)) : False := by
  have hp : p.Prime := Fact.out
  have hker := (h.le_centralizer_or_inf_le_ker hL).resolve_left hJL
  obtain ⟨E, hEJ, hE, hEcard⟩ := h.exists_isElemAbelian
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  have hEC : E ⊓ Subgroup.centralizer (L : Set Y) = ⊥ := by
    rw [eq_bot_iff, ← h.inf_ker_eq_bot hEp]
    exact le_inf inf_le_left ((inf_le_inf_right _ hEJ).trans hker)
  have hineq := pRank_le_pRank_inf_centralizer_add_pRank_mulAut hp
    (hEJ.trans (h.le_normalizer_component hL))
  rw [hEC, pRank_bot_eq_zero hp] at hineq
  have h2 := h.red.pRank_mulAut_le_two_of_isCyclic h.catalog hβ hL hcyc
  have hn : n ≤ Open.pRank p E :=
    le_csSup (PreuniquenessRankFour.Helpers.pRank_bddAbove p hp E) ⟨E, le_rfl, hE, hEcard⟩
  have := h.three_le
  omega

theorem false_of_forall_isCyclic (h : JStarHyp p n Rb Y₀ Jt Xt φ) (hβ : KFactBeta)
    (hE : ∃ L : Subgroup Y, IsComponentOf L ⊤)
    (hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ →
      IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y)) : False := by
  obtain ⟨L, hL⟩ := hE
  by_cases hall : ∀ K : Subgroup Y, IsComponentOf K ⊤ → Jt ≤ Subgroup.centralizer (K : Set Y)
  · exact h.false_of_forall_le_centralizer hL hall
  · push Not at hall
    obtain ⟨K, hK, hJK⟩ := hall
    exact h.false_of_not_le_centralizer hβ hK (hcyc K hK) hJK

end JStarHyp

theorem jStarII (hβ : KFactBeta) : StmtJStarII := fun h hE hcyc =>
  h.false_of_forall_isCyclic hβ hE hcyc

end CFSG.AGLEmbedding
