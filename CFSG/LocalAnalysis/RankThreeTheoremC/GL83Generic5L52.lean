module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Ctx
import CFSG.LocalAnalysis.AGLEmbedding.Extremal
import CFSG.LocalAnalysis.RankThreeTheoremC.CentralOfRankLeThree
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Setup
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionLift
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerOdd

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

section Psl

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

variable {p : ℕ} [Fact p.Prime]

omit [Finite G] in
theorem commutator_eq_self_of_mulEquiv_psl (hp5 : 5 ≤ p) {L : Subgroup G}
    (e : L ≃* PSL(2, GaloisField p 2)) : ⁅L, L⁆ = L := by
  have hK : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by norm_num)
  have : IsSimpleGroup PSL(2, GaloisField p 2) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hK]; nlinarith)
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

theorem le_centralizer_of_rank_le_three_psl (hp5 : 5 ≤ p) {L X : Subgroup G}
    (e : L ≃* PSL(2, GaloisField p 2)) (hpL : p ∣ Nat.card L)
    (hLX : L ≤ normalizer (X : Set G)) (hodd : Odd (Nat.card X)) (hpX : ¬ p ∣ Nat.card X)
    (hrank : ∀ q : ℕ, q.Prime → ∀ E : Subgroup G, E ≤ X → IsElemAbelian q E →
      Nat.card E ≤ q ^ 3) :
    X ≤ centralizer (L : Set G) := by
  have hK : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by norm_num)
  have : IsSimpleGroup PSL(2, GaloisField p 2) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hK]; nlinarith)
  have hLs : IsSimpleGroup L := e.isSimpleGroup
  have hLp : ⁅L, L⁆ = L := commutator_eq_self_of_mulEquiv_psl hp5 e
  have hXL : X ⊓ L = ⊥ := by
    have hn : (X.subgroupOf L).Normal := ⟨fun n hn g => by
      rw [mem_subgroupOf] at hn ⊢
      exact (mem_normalizer_iff.mp (hLX g.2) n).mp hn⟩
    rcases hLs.eq_bot_or_eq_top_of_normal (X.subgroupOf L) with h | h
    · rw [← subgroupOf_map_subtype, h, Subgroup.map_bot]
    · exact absurd (hpL.trans (card_dvd_of_le (subgroupOf_eq_top.mp h))) hpX
  set J : Subgroup G := perfectCore (L ⊔ X)
  have hLJ : L ≤ J := le_perfectCore le_sup_left hLp
  have hJH : J ≤ L ⊔ X := perfectCore_le _
  have hXJ : X ≤ normalizer (J : Set G) := le_sup_right.trans (le_normalizer_perfectCore _)
  have hJX : J ≤ normalizer (X : Set G) := hJH.trans (sup_le hLX le_normalizer)
  set O : Subgroup G := J ⊓ X
  have hOX : O ≤ X := inf_le_right
  have hOn : (O.subgroupOf J).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    exact ⟨J.mul_mem (J.mul_mem g.2 hn.1) (J.inv_mem g.2),
      (mem_normalizer_iff.mp (hJX g.2) n).mp hn.2⟩⟩
  let f : L →* J ⧸ O.subgroupOf J := (QuotientGroup.mk' (O.subgroupOf J)).comp (inclusion hLJ)
  have hf : Function.Bijective f := by
    constructor
    · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro l hl
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, mem_subgroupOf] at hl
      have hmem : (l : G) ∈ X ⊓ L := ⟨hl.2, l.2⟩
      rw [hXL, mem_bot] at hmem
      exact (mem_bot).mpr (Subtype.ext hmem)
    · intro q
      obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (O.subgroupOf J) q
      have hj : (j : G) ∈ ((L ⊔ X : Subgroup G) : Set G) := hJH j.2
      rw [coe_mul_of_left_le_normalizer_right L X hLX] at hj
      obtain ⟨l, hl, y, hy, hly⟩ := hj
      refine ⟨⟨l, hl⟩, ?_⟩
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, mem_subgroupOf]
      have hyj : ((inclusion hLJ ⟨l, hl⟩)⁻¹ * j : J) = (y : G) := by
        rw [coe_mul, coe_inv, coe_inclusion, ← hly]
        group
      exact ⟨((inclusion hLJ ⟨l, hl⟩)⁻¹ * j).2, hyj ▸ hy⟩
  have eQ : (J ⧸ O.subgroupOf J) ≃* PSL(2, GaloisField p 2) :=
    (MulEquiv.ofBijective f hf).symm.trans e
  have hJO : ⁅J, O⁆ = ⊥ :=
    central_of_rank_le_three_psl G p hp5 J O inf_le_left (hodd.of_dvd_nat (card_dvd_of_le hOX))
      (fun h => hpX (h.trans (card_dvd_of_le hOX))) (commutator_perfectCore _)
      (J ⧸ O.subgroupOf J) (QuotientGroup.mk' (O.subgroupOf J)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _) ⟨eQ⟩ fun q hq E hEO hE => hrank q hq E (hEO.trans hOX) hE
  have hXLO : ⁅X, L⁆ ≤ O := by
    rw [commutator_le]
    intro y hy l hl
    rw [commutatorElement_def]
    refine ⟨J.mul_mem ((mem_normalizer_iff.mp (hXJ hy) l).mp (hLJ hl)) (J.inv_mem (hLJ hl)), ?_⟩
    have h1 : l * y⁻¹ * l⁻¹ ∈ X := (mem_normalizer_iff.mp (hLX hl) y⁻¹).mp (X.inv_mem hy)
    have h2 := X.mul_mem hy h1
    simpa [mul_assoc] using h2
  have hOL : ⁅O, L⁆ = ⊥ := by
    rw [eq_bot_iff, ← hJO, commutator_comm]
    exact commutator_mono hLJ le_rfl
  have h1 : ⁅⁅X, L⁆, L⁆ = ⊥ := eq_bot_iff.mpr (hOL ▸ commutator_mono hXLO le_rfl)
  have h2 : ⁅⁅L, X⁆, L⁆ = ⊥ := by rw [commutator_comm L X]; exact h1
  have h3 := commutator_commutator_eq_bot_of_rotate h2 h1
  rw [hLp, commutator_comm] at h3
  exact (commutator_eq_bot_iff_le_centralizer).mp h3

end Psl

section Gen5

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem gen5_normalizer_two_le (hG : Gen5Global G) (hl : Gen5Local G p P M x) {T : Subgroup G}
    (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥) (hUT : gen5U (P : Subgroup G) x ≤ normalizer (T : Set G)) :
    normalizer (T : Set G) ≤ M := by
  have hp := gen5_prime hl
  have : Fact p.Prime := ⟨hp⟩
  have hΓ : rankThreeGamma 1 p (gen5U (P : Subgroup G) x) ≤ M := by
    refine (gamma_le_iff 1 p _ M).mpr fun Q hQU hQ1 => gen5_normalizer_le hG hl hQU ?_
    rintro rfl
    obtain ⟨E, hE, -, hcard⟩ := pRank_attained p ⊥ hQ1
    rw [le_bot_iff.mp hE, card_bot] at hcard
    have := Nat.one_lt_pow (by omega : CFSG.Open.pRank p (⊥ : Subgroup G) ≠ 0) hp.one_lt
    omega
  exact le_of_isTwoLocal_of_gamma_one_le hG.setting hG.d2 hG.u0 hl.sigma (gen5_five_le hG hl)
    hl.core ⟨T, hT1, hT2, rfl⟩ hUT
    (inf_le_left.trans (sylow_le_of_isCoreMaxLocal hG.setting hl.sigma hl.core).1)
    (P.isPGroup'.to_le inf_le_left)
    (not_isCyclic_of_elemAbelian (gen5_U_elemAbelian hG hl).1 (gen5_U_elemAbelian hG hl).2
      le_rfl) hΓ

theorem gen5_L52 (hG : Gen5Global G) (hl : Gen5Local G p P M x) {X : Subgroup G}
    (hX : Nat.Coprime p (Nat.card X)) (hLX : gen5L x ≤ normalizer (X : Set G)) :
    X ≤ centralizer ((gen5L x : Subgroup G) : Set G) ∧ Odd (Nat.card X) := by
  have hp := gen5_prime hl
  have : Fact p.Prime := ⟨hp⟩
  have hUL : gen5U (P : Subgroup G) x ≤ gen5L x := inf_le_right
  have hpX : ¬ p ∣ Nat.card X := (Nat.Prime.coprime_iff_not_dvd hp).mp hX
  have hXM : X ≤ M := gen5_coprime_le hG hl hpX (hUL.trans hLX)
  have hodd : Odd (Nat.card X) :=
    CFSG.AGLEmbedding.odd_card_of_twoLocals_le hp (P.isPGroup'.to_le inf_le_left)
      (hUL.trans hLX) (fun h => gen5_not_le hG hl (hLX.trans h)) le_normalizer
      ((normal_subgroupOf_iff_le_normalizer le_normalizer).mpr le_rfl) hX hXM
      fun T hT2 hT1 hUT => gen5_normalizer_two_le hG hl hT2 hT1 hUT
  refine ⟨?_, hodd⟩
  obtain ⟨e⟩ := gen5_psl hG hl
  have hpL : p ∣ Nat.card (gen5L x) := by
    refine dvd_trans ?_ (card_dvd_of_le hUL)
    rw [(gen5_U_elemAbelian hG hl).2]
    exact dvd_pow_self p two_ne_zero
  refine le_centralizer_of_rank_le_three_psl (gen5_five_le hG hl) e hpL hLX hodd hpX
    fun q hq E hEX hE => ?_
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨k, hk⟩ := (elementary_isPGroup q E hE).exists_card_eq
  rw [hk]
  by_cases hq2 : q = 2
  · subst hq2
    have hEodd : Odd (Nat.card E) := hodd.of_dvd_nat (card_dvd_of_le hEX)
    have hk0 : k = 0 := by
      by_contra hk0
      rw [hk] at hEodd
      exact (Nat.not_even_iff_odd.mpr hEodd) (Nat.even_pow.mpr ⟨even_two, hk0⟩)
    rw [hk0]
    norm_num
  · have hkM := le_pRank_of_elemAbelian_card (hEX.trans hXM) hE hk
    have hloc := local_pRank_le_evenRank q hq hq2 M hl.core.1.1
    have hk3 : k ≤ 3 := by
      have := hG.setting.rank
      omega
    exact Nat.pow_le_pow_right hq.pos hk3

end Gen5

end CFSG.LocalAnalysis.RankThreeTheoremC
