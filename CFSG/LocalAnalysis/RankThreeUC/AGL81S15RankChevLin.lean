module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTable
public import CFSG.Open.GriessAllModelsStatement
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankArith
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevSigma
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.GroupTheory.WeirSylow.Orthogonal
import CFSG.LocalAnalysis.SectionRank.OddCover.ScalarCover
import CFSG.RankThree.PartOne.N143.Inspect613Even

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace RankChevLinProof

open CFSG.Open CFSG.SectionRank CFSG.GroupTheory.WeirSylow

theorem pRank_top_eq_of_pow_mem {r : ℕ} [hr : Fact r.Prime] {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) (hN : ∀ x : G, x ^ r = 1 → x ∈ N) :
    CFSG.Open.pRank r (⊤ : Subgroup ↥N) = CFSG.Open.pRank r (⊤ : Subgroup G) := by
  have hp1 : 1 < r := hr.out.one_lt
  refine le_antisymm (pRank_top_le_of_injective hp1 N.subtype N.subtype_injective) ?_
  obtain ⟨E, -, hE, hcard⟩ := exists_pRank hp1 (⊤ : Subgroup G)
  have hEN : E ≤ N := fun x hx => hN x (hE.2 x hx)
  have key := RankChevProof.card_le_pow_pRank_of_injective (p := r) (A := ↥E) (G := ↥N)
    (fun a b => hE.1.is_comm.comm a b) (fun a => Subtype.ext (by simpa using hE.2 a a.2))
    (Subgroup.inclusion hEN) (Subgroup.inclusion_injective hEN)
  rw [hcard] at key
  exact (Nat.pow_le_pow_iff_right hp1).1 key

theorem eq_one_of_pow_eq_one_of_not_dvd {H : Type*} [Group H] {r N : ℕ} (hr : r.Prime)
    (hN : ¬ r ∣ N) {x : H} (h1 : x ^ r = 1) (h2 : x ^ N = 1) : x = 1 := by
  have hcop : Nat.Coprime r N := (Nat.Prime.coprime_iff_not_dvd hr).2 hN
  have h5 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1)
    (orderOf_dvd_of_pow_eq_one h2)
  exact orderOf_eq_one_iff.1 h5

theorem mem_statedSL_of_pow_eq_one {F : Type} [Field F] [Fintype F] {r : ℕ} (hr : r.Prime)
    (hrF : ¬ r ∣ Fintype.card F - 1) {m : ℕ} {x : GL (Fin m) F} (hx : x ^ r = 1) :
    x ∈ StatedSL m F := by
  have h1 : (Matrix.GeneralLinearGroup.det x) ^ r = 1 := by rw [← map_pow, hx, map_one]
  have h2 : (Matrix.GeneralLinearGroup.det x) ^ (Fintype.card F - 1) = 1 := by
    rw [← Nat.card_eq_fintype_card, ← CFSG.SectionRank.OddCover.card_units_eq]
    exact pow_card_eq_one'
  have h3 := eq_one_of_pow_eq_one_of_not_dvd hr hrF h1 h2
  rw [CFSG.Open.StatedAPI.mem_statedSL_iff, ← Matrix.GeneralLinearGroup.val_det_apply, h3,
    Units.val_one]

theorem dvd_or_eq_two_of_dvd_mul_two_pow {r a k : ℕ} (hr : r.Prime) (h : r ∣ a * 2 ^ k) :
    r ∣ a ∨ r = 2 := by
  rcases (Nat.Prime.dvd_mul hr).1 h with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h1))

theorem card_scalars_statedSL_dvd {F : Type} [Field F] [Finite F] {m : ℕ} (hm : 1 ≤ m) :
    Nat.card ((StatedScalars (Fin m) F).subgroupOf (StatedSL m F)) ∣ m ∧
      Nat.card ((StatedScalars (Fin m) F).subgroupOf (StatedSL m F)) ∣ Nat.card F - 1 := by
  refine ⟨CFSG.SectionRank.OddCover.card_scalars_dvd hm _ fun x c hc => ?_,
    CFSG.SectionRank.OddCover.card_scalars_dvd hm _ fun x c _ => ?_⟩
  · have hdet := CFSG.SectionRank.OddCover.det_of_mem_statedSL x.1.2
    rw [hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
  · rw [← CFSG.SectionRank.OddCover.card_units_eq]
    exact pow_card_eq_one'

theorem not_dvd_card_scalars_statedSL {F : Type} [Field F] [Fintype F] {r m : ℕ} (hm : 1 ≤ m)
    (hZ : ¬ r ∣ Nat.gcd m (Fintype.card F - 1)) :
    ¬ r ∣ Nat.card ((StatedScalars (Fin m) F).subgroupOf (StatedSL m F)) := fun h => by
  obtain ⟨h1, h2⟩ := card_scalars_statedSL_dvd (F := F) hm
  rw [Nat.card_eq_fintype_card (α := F)] at h2
  exact hZ (h.trans (Nat.dvd_gcd h1 h2))

end RankChevLinProof

open CFSG.Open in
theorem pRank_statedSL_of_not_dvd {F : Type} [Field F] [Fintype F] {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hrp : ¬ r ∣ Fintype.card F) (hrF : ¬ r ∣ Fintype.card F - 1) (m : ℕ) :
    CFSG.Open.pRank r (⊤ : Subgroup ↥(StatedSL m F)) = m / orderOf (Fintype.card F : ZMod r) := by
  haveI : Fact r.Prime := ⟨hr⟩
  rw [RankChevLinProof.pRank_top_eq_of_pow_mem (StatedSL m F) fun x hx =>
    RankChevLinProof.mem_statedSL_of_pow_eq_one hr hrF hx]
  exact RankChevProof.pRank_eq_of_sylow_sigmaModel r (CFSG.GroupTheory.WeirSylow.one_le_weirA hrp)
    fun P => CFSG.GroupTheory.WeirSylow.sylow_GL (hr.odd_of_ne_two hr2) F hrp m P

open RankChevLinProof CFSG.Open CFSG.Blueprint.Multiplier in
theorem chevA_reduce_to_SL (hG : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) {l : ℕ} {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A l Q).Valid) (hQ : Q.p = 2)
    (e : (K ⧸ Subgroup.center K) ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A l Q, hv⟩)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hZ : ¬ r ∣ Nat.gcd (l + 1) (Q.card - 1)) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = Q.card ∧
      CFSG.Open.pRank r (⊤ : Subgroup K) =
        CFSG.Open.pRank r (⊤ : Subgroup ↥(StatedSL (l + 1) F)) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hm : CFSG.Open.StatedClassicalModel (K ⧸ Subgroup.center K) .PSL (l + 1) Q.p Q.exponent :=
    CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
  have hLM : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .PSL (l + 1) Q.p Q.exponent :=
    ⟨hm.1, Or.inl hm⟩
  have hdvd := ksm_card_center_dvd hG hq hLM
  rw [hQ] at hdvd
  have hgen : genericOrders .PSL (l + 1) 2 Q.exponent =
      (Nat.gcd (l + 1) (2 ^ Q.exponent - 1), 1) := rfl
  obtain ⟨k, hk⟩ := ksm_exc_two .PSL (l + 1) Q.exponent
  rw [hgen, hk] at hdvd
  have hQc : Q.card = 2 ^ Q.exponent := by rw [TauCeti.PrimePower.card_def, hQ]
  have hrZ : ¬ r ∣ Nat.card (Subgroup.center K) := fun h => by
    rcases dvd_or_eq_two_of_dvd_mul_two_pow hr (h.trans (by simpa using hdvd)) with h1 | h1
    · exact hZ (by rwa [hQc])
    · exact hr2 h1
  obtain ⟨-, F, instF, instFin, hcard, ⟨φ⟩⟩ := hm
  haveI : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = Q.card := by
    rw [Fintype.card_eq_nat_card, hcard, TauCeti.PrimePower.card_def]
  refine ⟨F, instF, inferInstance, hFc, ?_⟩
  have hZ0 := not_dvd_card_scalars_statedSL (F := F) (r := r) (m := l + 1) (by omega)
    (by rwa [hFc])
  rw [← CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) hrZ,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt φ]
  exact CFSG.SectionRank.pRank_quotient_eq
    ((StatedScalars (Fin (l + 1)) F).subgroupOf (StatedSL (l + 1) F)) hZ0

open RankChevLinProof CFSG.Open CFSG.Blueprint.Multiplier in
theorem pRank_chev_A_largeE (hG : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K]
    [Finite K] (hq : CFSG.Open.IsQuasisimple K) {l : ℕ} {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A l Q).Valid) (hQ : Q.p = 2)
    (e : (K ⧸ Subgroup.center K) ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A l Q, hv⟩)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hc : ¬ r ∣ Q.card - 1) :
    CFSG.Open.pRank r (⊤ : Subgroup K) =
      rkLin (l + 1) true Q.card r (Nat.card (Subgroup.center K)) := by
  obtain ⟨F, instF, instFin, hF, hrank⟩ := chevA_reduce_to_SL hG hq hv hQ e hr hr2
    (fun h => hc (h.trans (Nat.gcd_dvd_right _ _)))
  have hQc : Q.card = 2 ^ Q.exponent := by rw [TauCeti.PrimePower.card_def, hQ]
  have hrp : ¬ r ∣ Fintype.card F := by
    rw [hF, hQc]
    exact fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  have hrF : ¬ r ∣ Fintype.card F - 1 := by rwa [hF]
  rw [hrank, pRank_statedSL_of_not_dvd hr hr2 hrp hrF (l + 1), hF]
  have hne : eP Q.card r ≠ 1 := fun h =>
    hc ((eP_eq_one_iff (by rw [hQc]; exact Nat.one_le_two_pow)).1 h)
  unfold rkLin
  simp only [if_true, hne, if_false]
  rfl

end CFSG.LocalAnalysis.RankThreeUC.S15
