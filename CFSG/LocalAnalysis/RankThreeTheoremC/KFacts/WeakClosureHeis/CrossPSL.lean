module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.LieDispatch
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.Transfer
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SigmaDich
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.AbelianTransfer
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossTorus
public import CFSG.GroupTheory.WeirSylow.GL

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

namespace PSLCross

open CFSG.Open CFSG.Open.StatedAPI CFSG.GroupTheory.WeirSylow

variable {F : Type} [Field F] [Finite F]

theorem index_statedSL_dvd (n : ℕ) : (StatedSL n F).index ∣ Nat.card F - 1 := by
  rw [statedSL_eq_ker_det, Subgroup.index_ker, ← Nat.card_units]
  exact Subgroup.card_subgroup_dvd_card _

theorem card_scalars_subgroupOf_dvd (n : ℕ) :
    Nat.card ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F)) ∣ Nat.card F - 1 := by
  have h1 : Nat.card ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F)) =
      Nat.card ↥(StatedScalars (Fin n) F ⊓ StatedSL n F) := by
    rw [← Subgroup.subgroupOf_map_subtype]
    exact (Subgroup.card_map_of_injective (StatedSL n F).subtype_injective).symm
  rw [h1]
  refine (Subgroup.card_dvd_of_le inf_le_left).trans ?_
  have h2 := Subgroup.card_range_dvd
    (Matrix.GeneralLinearGroup.scalar (Fin n) : Fˣ →* GL (Fin n) F)
  rwa [Nat.card_units] at h2

theorem orderOf_pos_card [Fintype F] {p : ℕ} (hp : p.Prime) (hpF : ¬ p ∣ Fintype.card F) :
    0 < orderOf (Fintype.card F : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hne : (Fintype.card F : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  rw [orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
  exact ⟨p - 1, Nat.sub_pos_of_lt hp.one_lt, ZMod.pow_card_sub_one_eq_one hne⟩

theorem one_le_padicValNat_card [Fintype F] {p : ℕ} (hp : p.Prime) (hpF : ¬ p ∣ Fintype.card F) :
    1 ≤ padicValNat p (Fintype.card F ^ orderOf (Fintype.card F : ZMod p) - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have he := orderOf_pos_card (F := F) hp hpF
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hlt : 1 < Fintype.card F ^ orderOf (Fintype.card F : ZMod p) := Nat.one_lt_pow he.ne' hq
  refine one_le_padicValNat_of_dvd (by omega) ?_
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hlt.le, Nat.cast_pow, pow_orderOf_eq_one,
    Nat.cast_one, sub_self]


theorem sylowDichotomyAt_proj_SL {n p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hpF : ¬ p ∣ Nat.card F) : SylowDichotomyAt (StatedProj (StatedSL n F)) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hp1 : Odd p := hp.odd_of_ne_two (by omega)
  have hpF' : ¬ p ∣ Fintype.card F := by rwa [← Nat.card_eq_fintype_card]
  have hGL : ∀ P : Sylow p (GL (Fin n) F), Nonempty (P ≃* sigmaModel p
      (orderOf (Fintype.card F : ZMod p))
      (padicValNat p (Fintype.card F ^ orderOf (Fintype.card F : ZMod p) - 1)) n) :=
    fun P => sylow_GL hp1 F hpF' n P
  by_cases hn4 : n ≤ 4
  ·
    have hc := sylow_isMulCommutative_of_sigmaModel_of_lt hp
      (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega : n < p)) hGL
    exact SylowDichotomyAt.of_sylow_comm (sylow_comm_of_surjective (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _) (sylow_comm_of_subgroup (StatedSL n F) hc))
  · push Not at hn4
    by_cases hA : p ∣ Nat.card F - 1
    · obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by rwa [Nat.card_units])
      by_cases hnp : 6 ≤ n ∨ ¬ p ∣ n
      · have hH : ∀ u : Fin n → Fˣ, (∀ i, u i ∈ Subgroup.zpowers ζ) →
            (∀ i : Fin n, 5 ≤ i.val → u i = 1) → ∏ i, u i = 1 →
            diagGL n u ∈ StatedSL n F := by
          intro u _ _ hprod
          rw [mem_statedSL_iff, det_diagGL, ← Units.coe_prod, hprod, Units.val_one]
        obtain ⟨E, hE, hEcard⟩ :=
          exists_elemAbelian_four_projDiag hp hn4 hnp hζ (StatedSL n F) hH
        exact SylowDichotomyAt.of_elemAbelian hp hE hEcard le_rfl
      · push Not at hnp
        obtain rfl : n = 5 := by omega
        have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hnp.2
        subst hp5
        have hd : diagGL 5 ![ζ, ζ⁻¹, 1, 1, 1] ∈ StatedSL 5 F := by
          rw [mem_statedSL_iff, det_diagGL]
          simp [Fin.prod_univ_five]
        have hc : permGL 5 (finRotate 5) ∈ StatedSL 5 F := by
          rw [mem_statedSL_iff, det_permGL, sign_finRotate]
          simp
        obtain ⟨U, hU, hnc⟩ := exists_not_cyclic_derived_projFive hζ (StatedSL 5 F) hd hc
        exact SylowDichotomyAt.of_not_cyclic_derived hU hnc
    · have hdichGL : SylowDichotomyAt (GL (Fin n) F) p :=
        SylowDichotomyAt.of_sylow_sigmaModel hp h5 (one_le_padicValNat_card hp hpF') hGL
      haveI : (StatedSL n F).Normal := by rw [statedSL_eq_ker_det]; infer_instance
      have hSL : SylowDichotomyAt (StatedSL n F) p :=
        SylowDichotomyAt.of_normal_coprime_index hp (StatedSL n F)
          (fun hd => hA (hd.trans (index_statedSL_dvd n))) hdichGL
      refine SylowDichotomyAt.of_surjective_coprime_ker hp (QuotientGroup.mk' _)
        (QuotientGroup.mk'_surjective _) ?_ hSL
      rw [QuotientGroup.ker_mk']
      exact fun hd => hA (hd.trans (card_scalars_subgroupOf_dvd n))

end PSLCross

theorem sdLieCross_PSL : SDLieCrossAt .PSL := by
  intro K _ _ _ _ n ℓ f hadm hmodel p hp h5 hpℓ _
  obtain ⟨_, F, hF, hFin, hcard, ⟨e⟩⟩ :=
    LieModel.statedClassicalModel hmodel (by simp [classicalTags])
  have hpF : ¬ p ∣ Nat.card F := by
    rw [hcard]
    intro h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hadm.1).1 (hp.dvd_of_dvd_pow h))
  exact SylowDichotomyAt.of_mulEquiv hp e (PSLCross.sylowDichotomyAt_proj_SL hp h5 hpF)

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
