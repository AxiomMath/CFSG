module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Out
public import CFSG.RankThree.PartTwo.Sec4.Item413AutL3
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Cross
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofCoverLie
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem od_nine_dvd_cube_sub_one {t : ℕ} (ht : 1 ≤ t ^ 3) (h : 3 ∣ t ^ 3 - 1) : 9 ∣ t ^ 3 - 1 := by
  have h9 : t ^ 3 % 9 = 0 ∨ t ^ 3 % 9 = 1 ∨ t ^ 3 % 9 = 8 := by
    have : t % 9 < 9 := Nat.mod_lt _ (by norm_num)
    rw [Nat.pow_mod]
    interval_cases t % 9 <;> simp
  omega

theorem od_nine_dvd_cube_add_one {t : ℕ} (h : 3 ∣ t ^ 3 + 1) : 9 ∣ t ^ 3 + 1 := by
  have h9 : t ^ 3 % 9 = 0 ∨ t ^ 3 % 9 = 1 ∨ t ^ 3 % 9 = 8 := by
    have : t % 9 < 9 := Nat.mod_lt _ (by norm_num)
    rw [Nat.pow_mod]
    interval_cases t % 9 <;> simp
  omega

theorem od_not_three_dvd_three_pow_sub_one {f : ℕ} (hf : 1 ≤ f) : ¬ 3 ∣ 3 ^ f - 1 := by
  intro h
  have h1 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
  have h2 : 1 ≤ 3 ^ f := Nat.one_le_pow _ _ (by norm_num)
  omega

theorem od_exists_elemAbelian_mulAut_of_equiv {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    [L.Normal] (hcen : centralizer (L : Set Y) = ⊥) {X : Type} [Group X] (e : ↥L ≃* X)
    {E : Subgroup Y} (hE : IsElemAbelian 3 E) (hc : Nat.card E = 27) :
    ∃ B : Subgroup (MulAut X), IsElemAbelian 3 B ∧ Nat.card B = 27 := by
  let ρ : Y →* MulAut X :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : Y →* MulAut ↥L)
  have hρ : Function.Injective ρ :=
    (MulAut.congr e).injective.comp (i294_conjNormal_injective hcen)
  exact ⟨E.map ρ, IsElemAbelian.map hE ρ, by rw [Subgroup.card_map_of_injective hρ, hc]⟩

theorem linThree_nine_dvd {K : Type} [Field K] [Finite K] (h3K : 3 ∣ Nat.card K - 1)
    (B : Subgroup (MulAut (projectiveSL 3 K))) (hB : IsElemAbelian 3 B)
    (hc : 27 ≤ Nat.card B) : 9 ∣ Nat.card K - 1 := by
  obtain ⟨r, f, hr, hchar, hf, hK⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.exists_char_pow_card K
  have hr3 : r ≠ 3 := by
    rintro rfl
    rw [hK] at h3K
    exact od_not_three_dvd_three_pow_sub_one hf h3K
  have h30 : (3 : K) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : K) = 0 := by exact_mod_cast h
    have := (CharP.cast_eq_zero_iff K r 3).1 h'
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 this)
  by_contra h9
  have hle : B ≤ linearAutGroup 3 K := by
    intro b hb
    by_contra hbD
    obtain ⟨σ, hσ, -⟩ :=
      CFSG.RankThree.PartTwo.KFacts.linear_order_three_field_descent (by norm_num) b
        (hB.2 b hb) hbD
    have hcard := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hr K hK).1
    have h3f : 3 ∣ f := by
      rw [← hcard, ← hσ]
      exact orderOf_dvd_natCard σ
    obtain ⟨m, rfl⟩ := h3f
    have hq : Nat.card K = (r ^ m) ^ 3 := by rw [hK, mul_comm, pow_mul]
    rw [hq] at h3K h9
    exact h9 (od_nine_dvd_cube_sub_one (Nat.one_le_pow _ _ (pow_pos hr.pos _)) h3K)
  have h := CFSG.RankThree.PartTwo.Sec4.card_inf_linearAutGroup_three_le h30 hB
  rw [inf_eq_left.2 hle] at h
  omega

theorem linThree_eightyOne_dvd {K : Type} [Field K] [Finite K] (h3K : 3 ∣ Nat.card K - 1)
    (h9K : 9 ∣ Nat.card K - 1) : 81 ∣ Nat.card (StatedProj (StatedSL 3 K)) := by
  rw [← Nat.card_congr
    (CFSG.LocalAnalysis.RankFourTheoremC.l212in_projectiveSLEquivStated 3 K).toEquiv,
    CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_projectiveSL_three,
    CFSG.GH74.GLS.Stage2.Signalizer.Odd87.psl3Order, Nat.gcd_eq_left h3K]
  set q := Nat.card K with hqdef
  have hq1 : 1 ≤ q := Nat.card_pos
  obtain ⟨m, hm⟩ := h9K
  have hq : q = 9 * m + 1 := by omega
  have e2 : q ^ 2 - 1 = 9 * m * (9 * m + 2) := by
    rw [hq]; apply Nat.sub_eq_of_eq_add; ring
  have e3 : q ^ 3 - 1 = 27 * m * (27 * m ^ 2 + 9 * m + 1) := by
    rw [hq]; apply Nat.sub_eq_of_eq_add; ring
  apply Nat.dvd_div_of_mul_dvd
  rw [e2, e3]
  exact ⟨q ^ 3 * (m * (9 * m + 2)) * (m * (27 * m ^ 2 + 9 * m + 1)), by ring⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
