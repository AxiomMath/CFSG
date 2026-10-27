module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.MSide
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.KeyF
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Critical
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionLift
import CFSG.LocalAnalysis.RankThreeTheoremC.PSLTwoPElements

public section

open Subgroup
open scoped MatrixGroups commutatorElement

open CFSG.LocalAnalysis.RankThreeTheoremC (perfectCore perfectCore_le le_perfectCore
  commutator_perfectCore eq_one_of_commute_of_mulEquiv_psl_two)

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

omit [Finite G] in
private theorem le_normalizer_perfectCore (N : Subgroup G) :
    N ≤ normalizer (perfectCore N : Set G) := by
  have key : ∀ g ∈ N, perfectCore N ≤ (perfectCore N).comap (MulAut.conj g).toMonoidHom := by
    intro g hg
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_perfectCore ?_ ?_
    · rintro _ ⟨k, hk, rfl⟩
      exact N.mul_mem (N.mul_mem hg (perfectCore_le N hk)) (N.inv_mem hg)
    · rw [← Subgroup.map_commutator, commutator_perfectCore]
  intro n hn
  rw [mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key n hn hh, fun hh => ?_⟩
  have h1 := key n⁻¹ (N.inv_mem hn) hh
  simpa [mul_assoc] using h1

private theorem isSimpleGroup_psl_gen {p n : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hn : 3 ≤ n) :
    IsSimpleGroup PSL(2, GaloisField p n) := by
  refine Matrix.ProjectiveSpecialLinearGroup.rank_two_simple ?_
  rw [GaloisField.card p n (by omega)]
  have h := Nat.pow_le_pow_right (by omega : p > 0) (by omega : 1 ≤ n)
  rw [Nat.pow_one] at h
  omega

omit [Finite G] in
private theorem commutator_eq_self_psl_gen {p n : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hn : 3 ≤ n)
    {L : Subgroup G} (e : L ≃* PSL(2, GaloisField p n)) : ⁅L, L⁆ = L := by
  have : IsSimpleGroup PSL(2, GaloisField p n) := isSimpleGroup_psl_gen hp5 hn
  have : IsSimpleGroup L := e.isSimpleGroup
  rw [← Subgroup.isPerfect_iff, Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator L) with h | h
  · exfalso
    obtain ⟨l, hl1⟩ := exists_ne (1 : L)
    refine hl1 (Subtype.ext (eq_one_of_commute_of_mulEquiv_psl_two e l.2 fun m hm => ?_))
    have hmem : ⁅(⟨m, hm⟩ : L), l⁆ ∈ commutator L := by
      rw [_root_.commutator_def]
      exact commutator_mem_commutator (mem_top _) (mem_top _)
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact congrArg Subtype.val hmem
  · exact h

omit [Finite G] in
private theorem le_centralizer_of_three_subgroups {L X J O : Subgroup G} (hLp : ⁅L, L⁆ = L)
    (hLJ : L ≤ J) (hXLO : ⁅X, L⁆ ≤ O) (hJO : ⁅J, O⁆ = ⊥) : X ≤ centralizer (L : Set G) := by
  have hOL : ⁅O, L⁆ = ⊥ := by
    rw [eq_bot_iff, ← hJO, commutator_comm]
    exact commutator_mono hLJ le_rfl
  have h1 : ⁅⁅X, L⁆, L⁆ = ⊥ := eq_bot_iff.mpr (hOL ▸ commutator_mono hXLO le_rfl)
  have h2 : ⁅⁅L, X⁆, L⁆ = ⊥ := by rw [commutator_comm L X]; exact h1
  have h3 := commutator_commutator_eq_bot_of_rotate h2 h1
  rw [hLp, commutator_comm] at h3
  exact (commutator_eq_bot_iff_le_centralizer).mp h3

theorem fr_L52_odd [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x) {X : Subgroup G}
    (hX : Nat.Coprime p (Nat.card X)) (hLX : layerOf x ≤ normalizer (X : Set G)) :
    Odd (Nat.card X) := by
  have hUL : frU P x ≤ layerOf x := inf_le_right
  have hXM : X ≤ M := fr_coprime_le hG hl hX (hUL.trans hLX)
  exact CFSG.AGLEmbedding.odd_card_of_twoLocals_le (Fact.out : p.Prime)
    (P.isPGroup'.to_inf_left : IsPGroup p (frU P x)) (hUL.trans hLX)
    (fun h => hl.not_le (hLX.trans h)) le_normalizer
    ((normal_subgroupOf_iff_le_normalizer le_normalizer).mpr le_rfl) hX hXM
    fun T hT2 hT1 hUT => fr_normalizer_two_le hG hl hT2 hT1 hUT

theorem fr_L52_centralizes [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x)
    {X : Subgroup G} (hX : Nat.Coprime p (Nat.card X))
    (hLX : layerOf x ≤ normalizer (X : Set G)) :
    X ≤ centralizer ((layerOf x : Subgroup G) : Set G) := by
  have hp5 : 5 ≤ p := hl.p5
  have hpX : ¬ p ∣ Nat.card X := (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp hX
  have hodd : Odd (Nat.card X) := fr_L52_odd hG hl hX hLX
  have hUL : frU P x ≤ layerOf x := inf_le_right
  have hXM : X ≤ M := fr_coprime_le hG hl hX (hUL.trans hLX)
  obtain ⟨n, hn3, ⟨e⟩, -, -, hUcard⟩ := fr_layer_rank hG hl
  have hpL : p ∣ Nat.card (layerOf x) := by
    refine dvd_trans ?_ (card_dvd_of_le hUL)
    rw [hUcard]
    exact dvd_pow_self p (by omega)
  have hLs : IsSimpleGroup (layerOf x) := by
    have : IsSimpleGroup PSL(2, GaloisField p n) := isSimpleGroup_psl_gen hp5 hn3
    exact e.isSimpleGroup
  have hLp : ⁅layerOf x, layerOf x⁆ = layerOf x := commutator_eq_self_psl_gen hp5 hn3 e
  have hXL : X ⊓ layerOf x = ⊥ := by
    have hnX : (X.subgroupOf (layerOf x)).Normal := ⟨fun y hy g => by
      rw [mem_subgroupOf] at hy ⊢
      exact (mem_normalizer_iff.mp (hLX g.2) y).mp hy⟩
    rcases hLs.eq_bot_or_eq_top_of_normal (X.subgroupOf (layerOf x)) with h | h
    · rw [← subgroupOf_map_subtype, h, Subgroup.map_bot]
    · exact absurd (hpL.trans (card_dvd_of_le (subgroupOf_eq_top.mp h))) hpX
  set J : Subgroup G := perfectCore (layerOf x ⊔ X)
  have hLJ : layerOf x ≤ J := le_perfectCore le_sup_left hLp
  have hJH : J ≤ layerOf x ⊔ X := perfectCore_le _
  have hJJ : ⁅J, J⁆ = J := commutator_perfectCore _
  have hXJ : X ≤ normalizer (J : Set G) := le_sup_right.trans (le_normalizer_perfectCore _)
  have hJX : J ≤ normalizer (X : Set G) := hJH.trans (sup_le hLX le_normalizer)
  set O : Subgroup G := J ⊓ X
  have hOX : O ≤ X := inf_le_right
  have hOJ : O ≤ J := inf_le_left
  have hOodd : Odd (Nat.card O) := hodd.of_dvd_nat (card_dvd_of_le hOX)
  have hpO : ¬ p ∣ Nat.card O := fun h => hpX (h.trans (card_dvd_of_le hOX))
  have hOn : (O.subgroupOf J).Normal := ⟨fun y hy g => by
    rw [mem_subgroupOf] at hy ⊢
    exact ⟨J.mul_mem (J.mul_mem g.2 hy.1) (J.inv_mem g.2),
      (mem_normalizer_iff.mp (hJX g.2) y).mp hy.2⟩⟩
  let f : layerOf x →* J ⧸ O.subgroupOf J :=
    (QuotientGroup.mk' (O.subgroupOf J)).comp (inclusion hLJ)
  have hf : Function.Bijective f := by
    constructor
    · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro l hlk
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, mem_subgroupOf] at hlk
      have hmem : (l : G) ∈ X ⊓ layerOf x := ⟨hlk.2, l.2⟩
      rw [hXL, mem_bot] at hmem
      exact (mem_bot).mpr (Subtype.ext hmem)
    · intro q
      obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (O.subgroupOf J) q
      have hj : (j : G) ∈ ((layerOf x ⊔ X : Subgroup G) : Set G) := hJH j.2
      rw [coe_mul_of_left_le_normalizer_right (layerOf x) X hLX] at hj
      obtain ⟨l, hlL, y, hy, hly⟩ := hj
      refine ⟨⟨l, hlL⟩, ?_⟩
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, mem_subgroupOf]
      have hyj : ((inclusion hLJ ⟨l, hlL⟩)⁻¹ * j : J) = (y : G) := by
        rw [coe_mul, coe_inv, coe_inclusion, ← hly]
        group
      exact ⟨((inclusion hLJ ⟨l, hlL⟩)⁻¹ * j).2, hyj ▸ hy⟩
  have eQ : (J ⧸ O.subgroupOf J) ≃* PSL(2, GaloisField p n) :=
    (MulEquiv.ofBijective f hf).symm.trans e
  have hJO : ⁅J, O⁆ = ⊥ := by
    by_contra hne
    obtain ⟨q, D, hq, hDO, hDn, hDp, hrank⟩ := criticalRankFour G p hp5 n hn3 J O hOJ hOodd hpO
      hJJ (J ⧸ O.subgroupOf J) (QuotientGroup.mk' (O.subgroupOf J))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) ⟨eQ⟩ hne
    have hq2 : q ≠ 2 := by
      rintro rfl
      obtain ⟨E, hED, -, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 2 hq D
      have h2E : 2 ∣ Nat.card E := by
        rw [hEcard]
        exact dvd_pow_self 2 (by omega)
      have h2O : 2 ∣ Nat.card O := h2E.trans (card_dvd_of_le (hED.trans hDO))
      exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h2O)
    haveI : Fact q.Prime := ⟨hq⟩
    have hDJ : D ≤ J := hDO.trans hOJ
    have hDM : D ≤ M := hDO.trans (hOX.trans hXM)
    have hLD : layerOf x ≤ normalizer (D : Set G) :=
      hLJ.trans ((normal_subgroupOf_iff_le_normalizer hDJ).mp hDn)
    exact fr_keyF hG hl hq2 hDp hDM hrank hLD
  have hXLO : ⁅X, layerOf x⁆ ≤ O := by
    rw [commutator_le]
    intro y hy l hlL
    rw [commutatorElement_def]
    refine ⟨J.mul_mem ((mem_normalizer_iff.mp (hXJ hy) l).mp (hLJ hlL)) (J.inv_mem (hLJ hlL)), ?_⟩
    have h1 : l * y⁻¹ * l⁻¹ ∈ X := (mem_normalizer_iff.mp (hLX hlL) y⁻¹).mp (X.inv_mem hy)
    have h2 := X.mul_mem hy h1
    simpa [mul_assoc] using h2
  exact le_centralizer_of_three_subgroups hLp hLJ hXLO hJO

theorem fr_L52 [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x) {X : Subgroup G}
    (hX : Nat.Coprime p (Nat.card X)) (hLX : layerOf x ≤ normalizer (X : Set G)) :
    X ≤ centralizer ((layerOf x : Subgroup G) : Set G) ∧ Odd (Nat.card X) :=
  ⟨fr_L52_centralizes hG hl hX hLX, fr_L52_odd hG hl hX hLX⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
