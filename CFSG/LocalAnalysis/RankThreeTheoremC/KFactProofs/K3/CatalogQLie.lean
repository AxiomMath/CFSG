module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.CatalogQ
public import CFSG.LocalAnalysis.AGLEmbeddingD2.FiveCover
public import CFSG.ClassicalInvolution.Asc77.AscSCH19
public import CFSG.ClassicalInvolution.WeakCT.Center
public import CFSG.ClassicalInvolution.Phan.Center

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3

open CFSG.Open Subgroup
open CFSG.Assembly.LowTwoRank CFSG.Models CFSG.Blueprint.Multiplier
open CFSG.RankThree.PerfectCover (hopfMultiplier)
open scoped MatrixGroups

theorem nine_dvd_pow_six_mul (q : ℕ) (hq : 1 ≤ q) : 9 ∣ q ^ 6 * (q ^ 2 - 1) * (q ^ 4 - 1) := by
  by_cases h3 : 3 ∣ q
  · have h9 : 9 ∣ q ^ 6 := by
      have h36 : 3 ^ 6 ∣ q ^ 6 := pow_dvd_pow_of_dvd h3 6
      have h32 : 3 ^ 2 ∣ 3 ^ 6 := pow_dvd_pow 3 (by norm_num)
      simpa using h32.trans h36
    exact (h9.mul_right _).mul_right _
  · have hmod : q % 3 = 1 ∨ q % 3 = 2 := by omega
    have h2 : q ^ 2 % 3 = 1 := by
      rcases hmod with h | h <;> simp [Nat.pow_mod, h]
    have h4 : q ^ 4 % 3 = 1 := by
      rcases hmod with h | h <;> simp [Nat.pow_mod, h]
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    have h1' : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq
    have d2 : 3 ∣ q ^ 2 - 1 := by omega
    have d4 : 3 ∣ q ^ 4 - 1 := by omega
    have h33 : 3 * 3 ∣ (q ^ 2 - 1) * (q ^ 4 - 1) := Nat.mul_dvd_mul d2 d4
    refine dvd_trans (by simpa using h33) ⟨q ^ 6, ?_⟩
    rw [mul_assoc, mul_comm]

theorem nine_dvd_card_statedProj_sl (n : ℕ) (hn : 5 ≤ n) (K : Type) [Field K] [Finite K] :
    9 ∣ Nat.card (StatedProj (StatedSL n K)) := by
  have h4 : 0 + 4 ≤ n := by omega
  let θ : SL(n, K) →* StatedProj (StatedSL n K) :=
    (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K))).comp
      (specialLinearGroupEquivStatedSL n K).toMonoidHom
  have hθ : θ.ker ≤ Subgroup.center SL(n, K) := by
    intro A hA
    have h1 : specialLinearGroupEquivStatedSL n K A ∈
        (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) := (QuotientGroup.eq_one_iff _).mp hA
    rw [← map_center_eq_statedScalars n K] at h1
    obtain ⟨B, hB, hBA⟩ := h1
    rwa [← (specialLinearGroupEquivStatedSL n K).injective hBA]
  have hinj : Function.Injective
      (θ.comp (CFSG.ClassicalInvolution.WeakCT.blockSL K n 4 0 h4)) :=
    CFSG.ClassicalInvolution.WeakCT.comp_blockSL_injective hθ h4 (by omega)
  have hdvd : Nat.card SL(4, K) ∣ Nat.card (StatedProj (StatedSL n K)) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hcard : Nat.card SL(4, K) = Nat.card K ^ 6 * (Nat.card K ^ 2 - 1) *
      (Nat.card K ^ 3 - 1) * (Nat.card K ^ 4 - 1) :=
    (Nat.card_congr (specialLinearGroupEquivStatedSL 4 K).toEquiv).trans
      CFSG.ClassicalInvolution.Asc77.SCH.card_statedSL_four
  refine dvd_trans ?_ hdvd
  rw [hcard]
  have h9 := nine_dvd_pow_six_mul (Nat.card K) Nat.card_pos
  exact h9.trans (Dvd.intro (Nat.card K ^ 3 - 1) (mul_right_comm _ _ _))

theorem nine_dvd_card_statedProj_su (n : ℕ) (hn : 5 ≤ n) {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) :
    9 ∣ Nat.card (StatedProj (StatedSU n (p ^ f) K)) := by
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := hUF.charP
  have h4 : 0 + 4 ≤ n := by omega
  let θ : CFSG.ClassicalInvolution.Phan.Su K p f n →* StatedProj (StatedSU n (p ^ f) K) :=
    (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K))).comp
      (MulEquiv.subgroupCongr
        (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK n)).toMonoidHom
  have hθ : θ.ker ≤ Subgroup.center (CFSG.ClassicalInvolution.Phan.Su K p f n) := by
    intro g hg
    have h1 : (MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK n) g :
        StatedSU n (p ^ f) K) ∈ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K) :=
      (QuotientGroup.eq_one_iff _).mp hg
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h1
    obtain ⟨c, hc⟩ := h1
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    have hcen : (Matrix.GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) ∈
        Subgroup.center (GL (Fin n) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩
    have hgc : ((g : GL (Fin n) K)) = Matrix.GeneralLinearGroup.scalar (Fin n) c := hc.symm
    have := Subgroup.mem_center_iff.mp hcen (h : GL (Fin n) K)
    show (h : GL (Fin n) K) * (g : GL (Fin n) K) = (g : GL (Fin n) K) * (h : GL (Fin n) K)
    rw [hgc]
    exact this
  have hinj : Function.Injective
      (θ.comp (CFSG.ClassicalInvolution.Phan.blockEmb K p f n 4 0 h4)) :=
    CFSG.ClassicalInvolution.Phan.comp_blockEmb_injective hK hθ h4 (by omega) (by omega)
  have hdvd : Nat.card (CFSG.ClassicalInvolution.Phan.Su K p f 4) ∣
      Nat.card (StatedProj (StatedSU n (p ^ f) K)) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hcard : Nat.card (CFSG.ClassicalInvolution.Phan.Su K p f 4) = (p ^ f) ^ 6 *
      ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1) :=
    (Nat.card_congr (MulEquiv.subgroupCongr
      (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 4)).toEquiv).trans
      (CFSG.ClassicalInvolution.Asc77.SCH.card_statedSU_four hUF)
  refine dvd_trans ?_ hdvd
  rw [hcard]
  have h9 := nine_dvd_pow_six_mul (p ^ f) (Nat.one_le_pow _ _ hp.pos)
  exact h9.trans (Dvd.intro ((p ^ f) ^ 3 + 1) (mul_right_comm _ _ _))

theorem k3CatalogQLie_of_table (hGA : GriessAllModelsStatement) : K3CatalogQLie := by
  intro d S _ _ hS hnab ⟨e⟩ h3 h9
  obtain ⟨t, n, p, f, hm⟩ := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.exists_lieModel d
  have hM : Nat.card (hopfMultiplier S) =
      CFSG.RankThree.PartTwo.Sec4.Census.tableOrder t n p f := by
    rw [CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.card_hopfMultiplier_eq_of_mulEquiv
      e]
    exact (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.finite_and_card_hopf hGA hm).2
  by_cases hex : ∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ q ∣ Nat.card (hopfMultiplier S)
  · exfalso
    obtain ⟨q₀, hq₀, hq₀5, hq₀d⟩ := hex
    rw [hM] at hq₀d
    rcases CFSG.AGLEmbeddingD2.FiveCover.five_le_dvd_tableOrder_cases hq₀ hq₀5 hq₀d with
      ⟨rfl, hq₀n, -⟩ | ⟨rfl, hq₀n, -⟩
    · obtain ⟨hadm, hcl | ⟨h0, -⟩⟩ := hm
      · obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hcl
        have hn2 : 2 ≤ n := hadm.2.2.1
        have hn5 : 5 ≤ n := hq₀5.trans (Nat.le_of_dvd (by omega) hq₀n)
        apply h9
        rw [Nat.card_congr (e.trans e').toEquiv]
        exact nine_dvd_card_statedProj_sl n hn5 K
      · have := hadm.2.2.1
        omega
    · obtain ⟨hadm, hcl | ⟨h0, -⟩⟩ := hm
      · obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hcl
        have hn3 : 3 ≤ n := hadm.2.2.1
        have hn5 : 5 ≤ n := hq₀5.trans (Nat.le_of_dvd (by omega) hq₀n)
        apply h9
        rw [Nat.card_congr (e.trans e').toEquiv]
        exact nine_dvd_card_statedProj_su n hn5 hadm.1 hadm.2.1 K hK
      · have := hadm.2.2.1
        omega
  · obtain ⟨q, hq, hq5, hqd⟩ := exists_prime_five_le_dvd_of_simple hS hnab
    exact ⟨q, hq, hq5, hqd, fun hdvd => hex ⟨q, hq, hq5, hdvd⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3
