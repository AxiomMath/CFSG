module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.LieDispatch
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.Transfer
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SigmaDich
public import CFSG.GroupTheory.WeirSylow.Symplectic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

private theorem one_le_padicValNat_pow_orderOf_sub_one {p q : ℕ} [hp : Fact p.Prime] (hq : 1 < q)
    (hpq : ¬ p ∣ q) :
    1 ≤ padicValNat p (q ^ orderOf (q : ZMod p) - 1) := by
  have hq0 : (q : ZMod p) ≠ 0 := fun h => hpq ((ZMod.natCast_eq_zero_iff q p).1 h)
  have hepos : 0 < orderOf (q : ZMod p) := by
    rw [orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
    exact ⟨p - 1, Nat.sub_pos_of_lt hp.out.one_lt, ZMod.pow_card_sub_one_eq_one hq0⟩
  have h1 : 1 < q ^ orderOf (q : ZMod p) := Nat.one_lt_pow hepos.ne' hq
  refine one_le_padicValNat_of_dvd (by omega) ?_
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1.le, Nat.cast_pow, pow_orderOf_eq_one, Nat.cast_one,
    sub_self]

private theorem sylowDichotomyAt_statedSp {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (F : Type) [Field F]
    [Finite F] (hpF : ¬ p ∣ Nat.card F) (n : ℕ) : SylowDichotomyAt (StatedSp n F) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := Fintype.ofFinite F
  have hpF' : ¬ p ∣ Fintype.card F := by rwa [← Nat.card_eq_fintype_card]
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  exact SylowDichotomyAt.of_sylow_sigmaModel hp h5
    (one_le_padicValNat_pow_orderOf_sub_one Fintype.one_lt_card hpF')
    (fun P => CFSG.GroupTheory.WeirSylow.sylow_Sp hodd F hpF' n P)

private theorem sq_eq_one_of_mem_scalars_statedSp {n : ℕ} (hn : 1 ≤ n) {F : Type} [Field F]
    (g : StatedSp n F)
    (hg : g ∈ (StatedScalars (Fin n ⊕ Fin n) F).subgroupOf (StatedSp n F)) : g ^ 2 = 1 := by
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hg
  have hc2 : c ^ 2 = 1 :=
    (CFSG.Open.StatedAPI.scalar_mem_statedSp_iff hn c).1 (by rw [hc]; exact g.2)
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← hc, ← map_pow, hc2, map_one, Subgroup.coe_one]

private theorem not_dvd_card_ker_statedSp {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {n : ℕ} (hn : 1 ≤ n)
    {F : Type} [Field F] [Finite F] :
    ¬ p ∣ Nat.card (QuotientGroup.mk'
      ((StatedScalars (Fin n ⊕ Fin n) F).subgroupOf (StatedSp n F))).ker := by
  intro hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hx2 : x ^ 2 = 1 := by
    apply Subtype.ext
    have hmem := (QuotientGroup.ker_mk' _).le x.2
    exact sq_eq_one_of_mem_scalars_statedSp hn _ hmem
  have h2 := orderOf_dvd_of_pow_eq_one hx2
  rw [hx] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem sdLieCross_PSp : SDLieCrossAt .PSp := by
  intro K _ _ _ _ n ℓ f hadm hmodel p hp h5 hpℓ _
  obtain ⟨_, F, _, _, hF, ⟨e⟩⟩ := hmodel.statedClassicalModel (by simp [classicalTags])
  have hℓ : ℓ.Prime := hadm.1
  have hpF : ¬ p ∣ Nat.card F := by
    rw [hF]
    intro h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow h))
  have hn : 1 ≤ n := by have := hadm.2.2.1; omega
  exact SylowDichotomyAt.of_mulEquiv hp e
    (SylowDichotomyAt.of_surjective_coprime_ker hp (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _) (not_dvd_card_ker_statedSp hp h5 hn)
      (sylowDichotomyAt_statedSp hp h5 F hpF n))

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
