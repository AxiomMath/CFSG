module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28KFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28FrobModel
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Model
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28ThreeProved

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open CFSG.Quasithin.F6.L28Res (G8)

private theorem l28m_one_le_pRank {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    {H : Subgroup K} {t : K} (htH : t ∈ H) (ht : orderOf t = p) : 1 ≤ CFSG.Open.pRank p H := by
  have hcard : Nat.card (Subgroup.zpowers t) = p ^ 1 := by
    rw [Nat.card_zpowers, ht, pow_one]
  have hel : IsElemAbelian p (Subgroup.zpowers t) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    have h := pow_card_eq_one' (G := Subgroup.zpowers t) (x := ⟨x, hx⟩)
    rw [Nat.card_zpowers, ht] at h
    exact congrArg Subtype.val h
  unfold CFSG.Open.pRank
  refine le_csSup ?_ ⟨Subgroup.zpowers t, (Subgroup.zpowers_le).mpr htH, hel, hcard⟩
  refine ⟨Nat.card K, ?_⟩
  rintro j ⟨F, -, -, hj⟩
  have h1 : Nat.card F ≤ Nat.card K := Subgroup.card_le_card_group F
  have h2 : j < p ^ j := Nat.lt_pow_self hp.one_lt
  rw [hj] at h1
  exact h2.le.trans h1

theorem l28m_exists_invariant_two_group {K : Type} [Group K] (hK : IsRankThreeL28 K)
    {α : MulAut K} (hα3 : orderOf α = 3) (hα : ∀ k : K, α ≠ MulAut.conj k) :
    ∃ V : Subgroup K, IsPGroup 2 V ∧ Nat.card V = 8 ∧ V.map α.toMonoidHom = V := by
  obtain ⟨e⟩ := l28m_equiv hK
  have hα'3 : orderOf (MulAut.congr e α) = 3 := by rw [MulEquiv.orderOf_eq]; exact hα3
  have hcongr : ∀ y : G8, (MulAut.congr e α) y = e (α (e.symm y)) := fun y => rfl
  have hα'out : ∀ g : G8, MulAut.conj g ≠ MulAut.congr e α := by
    intro g h
    refine hα (e.symm g) ?_
    refine MulEquiv.ext fun y => e.injective ?_
    have h1 := congrArg (fun γ : MulAut G8 => γ (e y)) h
    simp only [MulAut.conj_apply, hcongr, MulEquiv.symm_apply_apply] at h1
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact h1.symm
  obtain ⟨U, hU2, hU8, hU⟩ := l28m_outer_three_invariant hα'3 hα'out
  have hcard : Nat.card (U.map e.symm.toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective e.symm.injective, hU8]
  refine ⟨U.map e.symm.toMonoidHom, IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num), hcard, ?_⟩
  have hsymm : ∀ w : G8, (MulAut.congr e α).symm w = e (α.symm (e.symm w)) := fun w => rfl
  ext y
  have h1 := Subgroup.ext_iff.mp hU (e y)
  rw [Subgroup.mem_map_equiv, hsymm, MulEquiv.symm_apply_apply] at h1
  simp only [Subgroup.mem_map_equiv, MulEquiv.symm_symm]
  exact h1

theorem l28FieldSignalizer_proved : KFactL28FieldSignalizer := by
  intro K _ _ hK T α hα3 hα _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨V, hV2, hV8, hVα⟩ := l28m_exists_invariant_two_group hK hα3 hα
  set N : Subgroup K := normalizer ((T : Subgroup K) : Set K) with hN
  have hVN : ¬ V ≤ N := by
    intro h
    have := Subgroup.card_dvd_of_le h
    rw [hV8, hN, l28m_card_normalizer hK T] at this
    omega
  obtain ⟨t₁, ht₁⟩ := exists_prime_orderOf_dvd_card' (G := (T : Subgroup K)) 3
    (by rw [l28m_card_sylow hK T]; exact dvd_pow_self 3 two_ne_zero)
  have hrank : 1 ≤ CFSG.Open.pRank 3 (T : Subgroup K) :=
    l28m_one_le_pRank Nat.prime_three t₁.2 (by rw [Subgroup.orderOf_coe]; exact ht₁)
  have hNΓ : N ≤ rankThreeGamma 1 3 (T : Subgroup K) :=
    le_sSup ⟨(T : Subgroup K), le_rfl, hrank, rfl⟩
  have hco : N ⊔ V = N ∨ N ⊔ V = ⊤ := (l28Three_proved K hK T).2 (N ⊔ V) le_sup_left
  rcases hco with h | h
  · exact absurd (le_sup_right.trans h.le) hVN
  · refine h.symm.le.trans (sup_le_sup hNΓ ?_)
    exact le_sSup ⟨hV2, hVα⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
