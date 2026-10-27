module

public import CFSG.ClassicalInvolution.Q3.TA3FrameLayer
public import CFSG.ClassicalInvolution.Q3.TA3SOLSp4
public import CFSG.ClassicalInvolution.Q3.TA3SmallTools

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Frame

open CFSG CFSG.Blueprint CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank
open CFSG.Open (IsComponentOf IsSubnormal)
open CFSG.ComponentClassification.CatFactsSp4
open scoped MatrixGroups

section General

variable {X : Type} [Group X]

theorem isQuasisimple_of_simple {L : Subgroup X} (hs : IsSimpleGroup L)
    (hp : Group.IsPerfect L) : CFSG.Open.IsQuasisimple L := by
  have hZ : Subgroup.center L = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
    · exact h
    · exfalso
      have hc : commutator L ≤ ⊥ := by
        rw [commutator_def, Subgroup.commutator_le]
        intro a _ b _
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a
      rw [hp.commutator_eq_top] at hc
      obtain ⟨x, hx⟩ := exists_ne (1 : L)
      exact hx (Subgroup.mem_bot.mp (hc (Subgroup.mem_top x)))
  have := hs
  exact ⟨hp.commutator_eq_top,
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup⟩

theorem layerExcludesQ8_of_normalSimpleShape {t : X} (h : NormalSimpleShape X t) :
    LayerExcludesQ8 X t := by
  obtain ⟨L, hLC, hCN, hs, hp, hab⟩ := h
  have hn : (L.subgroupOf (Subgroup.centralizer ({t} : Set X))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLC]
    intro l c hl hc
    exact (Subgroup.mem_normalizer_iff.mp (hCN hc) l).mp hl
  refine layerExcludesQ8_of_cent (isComponentOf_of_normal hLC hn (isQuasisimple_of_simple hs hp))
    fun a _ b _ ha hb ha2 hb2 => hab a ?_ b ?_ ha2 hb2
  · exact Subgroup.mem_centralizer_iff.mpr fun k hk => (ha k hk).symm
  · exact Subgroup.mem_centralizer_iff.mpr fun k hk => (hb k hk).symm

theorem statedClassicalModel_of_lieModel_psp {n p f : ℕ} (h : LieModel X .PSp n p f) :
    StatedClassicalModel X .PSp n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

end General

section Model

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem normal_X0 : ((X0 K).subgroupOf (Subgroup.centralizer ({u1 K} : Set _))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff X0_le_centralizer]
  intro x c hx hc
  exact conj_mem_map_centralizer (T1 K) hc hx

theorem isComponentOf_E1 (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) :
    IsComponentOf (E1 K) (Subgroup.centralizer ({u1 K} : Set _)) := by
  have hn : ((E1 K).subgroupOf (X0 K)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (E1_le_X0 h2)]
    intro e x he hx
    exact conj_mem_E1 h2 hx he
  exact ⟨(E1_le_X0 h2).trans X0_le_centralizer, IsSubnormal.step (E1_le_X0 h2) hn
    (IsSubnormal.step X0_le_centralizer normal_X0 (IsSubnormal.refl _)),
    isQuasisimple_of_equiv_sl2 h4 (E1Equiv h2).symm⟩

theorem isComponentOf_E2 (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) :
    IsComponentOf (E2 K) (Subgroup.centralizer ({u1 K} : Set _)) := by
  have hn : ((E2 K).subgroupOf (X0 K)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (E2_le_X0 h2)]
    intro e x he hx
    exact conj_mem_E2 h2 hx he
  exact ⟨(E2_le_X0 h2).trans X0_le_centralizer, IsSubnormal.step (E2_le_X0 h2) hn
    (IsSubnormal.step X0_le_centralizer normal_X0 (IsSubnormal.refl _)),
    isQuasisimple_of_equiv_sl2 h4 (E2Equiv h2).symm⟩

theorem layerExcludesQ8_u1 [Finite (StatedProj (StatedSp 2 K))]
    (hF : TwoSubgroupsFourGenerated (StatedProj (StatedSp 2 K))) (hodd : Odd (Nat.card K))
    (h4 : 4 ≤ Nat.card K) : LayerExcludesQ8 (StatedProj (StatedSp 2 K)) (u1 K) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  exact layerExcludesQ8_of_sl2Pair hF (isComponentOf_E1 h2 h4) (isComponentOf_E2 h2 h4) le_rfl
    le_rfl (fun _ ha _ hb => commute_E1_E2 ha hb) hodd hodd (E1Equiv h2).symm (E2Equiv h2).symm

theorem layerExcludesQ8_u2 (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K) :
    LayerExcludesQ8 (StatedProj (StatedSp 2 K)) (u2 K) :=
  layerExcludesQ8_of_normalSimpleShape
    (Sp4.normalSimpleShape_u2 (two_ne_zero_of_odd_card hodd) h4)

end Model

theorem layerExcludesQ8_psp4 {X : Type} [Group X] [Finite X] (hF : TwoSubgroupsFourGenerated X)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hm : LieModel X .PSp 2 p f) (t : X)
    (ht : orderOf t = 2) : LayerExcludesQ8 X t := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := statedClassicalModel_of_lieModel_psp hm
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.odd_of_ne_two hp2).pow
  have h4 : 4 ≤ Nat.card K := by rw [hK]; omega
  have hu : orderOf (e t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
  obtain ⟨g, hg⟩ := ComponentClassification.CatFactsSp4.exists_conj_of_orderOf_eq_two hodd hu
  let e' : X ≃* StatedProj (StatedSp 2 K) := e.trans (MulAut.conj g⁻¹)
  have hte : e' t = g⁻¹ * e t * g := by
    simp only [e', MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
  have : Finite (StatedProj (StatedSp 2 K)) := Finite.of_equiv X e'.toEquiv
  refine LayerExcludesQ8.of_mulEquiv e' ?_
  rw [hte]
  rcases hg with hg | hg <;> rw [hg]
  · exact layerExcludesQ8_u1 (twoSubgroupsFourGenerated_of_surjective e'.toMonoidHom
      e'.surjective hF) hodd h4
  · exact layerExcludesQ8_u2 hodd h4

end CFSG.ClassicalInvolution.Q3.TA3.Frame
