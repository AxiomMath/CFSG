module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.LinHard
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTables

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.SectionRank.OddCover CFSG.Blueprint.Multiplier
open CFSG.RankThree.PerfectCover (hopfMultiplier)

section Three

variable {F : Type} [Field F] [Finite F]

theorem equiv_of_cover_three {L : Type} [Group L] [Finite L] (hLperf : Group.IsPerfect L)
    {p f : ℕ} {H : Subgroup (GL (Fin 3) F)}
    (hH : (Nat.card F = p ^ f ∧ H = StatedSL 3 F ∧ 3 ∣ p ^ f - 1) ∨
      (Nat.card F = (p ^ f) ^ 2 ∧ H = StatedSU 3 (p ^ f) F ∧ 3 ∣ p ^ f + 1))
    (hHperf : Group.IsPerfect H) (hq1 : 1 ≤ p ^ f)
    (θ : L ⧸ Subgroup.center L ≃* StatedProj H) (hZ : Nat.card (Subgroup.center L) = 3)
    [Finite (hopfMultiplier (StatedProj H))]
    (hM : (Nat.card (hopfMultiplier (StatedProj H))).factorization 3 ≤
      (Nat.card ((StatedScalars (Fin 3) F).subgroupOf H)).factorization 3) :
    Nonempty (L ≃* H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHK : (Nat.card F = p ^ f ∧ H = StatedSL 3 F) ∨
      (Nat.card F = (p ^ f) ^ 2 ∧ H = StatedSU 3 (p ^ f) F) := by
    rcases hH with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  set D := (StatedScalars (Fin 3) F).subgroupOf H with hD
  have hDc : D ≤ Subgroup.center H := scalars_le_center H
  let α : H →* StatedProj H := QuotientGroup.mk' D
  have hα : Function.Surjective α := QuotientGroup.mk'_surjective D
  have hαk : α.ker = D := QuotientGroup.ker_mk' D
  let β : L →* StatedProj H := CFSG.GH74.Generic.centralQuotientMap θ
  have hβ : Function.Surjective β := CFSG.GH74.Generic.centralQuotientMap_surjective θ
  have hβk : β.ker = Subgroup.center L := CFSG.GH74.Generic.centralQuotientMap_ker θ
  have hβp : IsPGroup 3 β.ker := by
    rw [hβk]
    obtain ⟨k, hk⟩ : ∃ k, Nat.card (Subgroup.center L) = 3 ^ k := ⟨1, by rw [hZ]; simp⟩
    exact IsPGroup.of_card hk
  obtain ⟨φ, hφs, hβφ⟩ := exists_hom_of_cover hHperf hLperf α hα (hαk ▸ hDc) β hβ hβk.le
    Nat.prime_three hβp (by rw [hαk]; exact hM)
  have hD3 : Nat.card D = 3 := by
    refine Nat.dvd_antisymm ?_ ?_
    · refine card_scalars_dvd (by norm_num) H fun x c hc => ?_
      have hdet := det_eq_one_of_linUni hHK x.1.2
      rw [hc] at hdet
      have h1 : ((c : F)) ^ 3 = 1 := by
        simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal] using hdet
      exact Units.ext (by simpa using h1)
    · refine dvd_card_scalars (q := p ^ f) (by norm_num) hq1 ?_
      rcases hH with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact Or.inl ⟨h1, h2, dvd_rfl, h3⟩
      · exact Or.inr ⟨h1, h2, dvd_rfl, h3⟩
  have hc1 := CFSG.GH74.Generic.card_eq_card_mul_card_ker α hα
  have hc2 := CFSG.GH74.Generic.card_eq_card_mul_card_ker β hβ
  have hc3 := CFSG.GH74.Generic.card_eq_card_mul_card_ker φ hφs
  rw [hαk, hD3] at hc1
  rw [hβk, hZ] at hc2
  have hXpos : 0 < Nat.card (StatedProj H) := Nat.card_pos
  have hker1 : Nat.card φ.ker = 1 := by
    have : Nat.card (StatedProj H) * 3 = Nat.card (StatedProj H) * 3 * Nat.card φ.ker := by
      calc Nat.card (StatedProj H) * 3 = Nat.card H := hc1.symm
        _ = Nat.card L * Nat.card φ.ker := hc3
        _ = Nat.card (StatedProj H) * 3 * Nat.card φ.ker := by rw [hc2]
    have h3 : 0 < Nat.card (StatedProj H) * 3 := by positivity
    exact (Nat.eq_of_mul_eq_mul_left h3 (by rw [mul_one]; exact this)).symm
  have hker : φ.ker = ⊥ := Subgroup.card_eq_one.1 hker1
  exact ⟨(MulEquiv.ofBijective φ ⟨(MonoidHom.ker_eq_bot_iff φ).1 hker, hφs⟩).symm⟩

theorem isSLThree_of_cover (hGA : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K]
    [Finite K] (hperf : Group.IsPerfect K) (hZ : Nat.card (Subgroup.center K) = 3) {X : Type}
    [Group X] (e : K ⧸ Subgroup.center K ≃* X) {p f : ℕ}
    (hm : CFSG.Models.LieModel X .PSL 3 p f) (h3 : 3 ∣ p ^ f - 1) :
    IsSLThreeWith (fun q => q % 3 = 1) K := by
  obtain ⟨-, hcl | ⟨h0, -⟩⟩ := hm
  swap
  · exact absurd h0 (by norm_num)
  obtain ⟨hadm, F, _, _, hF, ⟨e'⟩⟩ := hcl
  have hp : p.Prime := hadm.1
  have hq0 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have hmm : CFSG.Models.LieModel (StatedProj (StatedSL 3 F)) .PSL 3 p f :=
    lieModel_of_classical ⟨hadm, F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨hfin, hcard⟩ := finite_and_card_hopf hGA hmm
  have hga : (genericOrders .PSL 3 p f).1 = Nat.gcd 3 (p ^ f - 1) := rfl
  have h3g : 3 ∣ (genericOrders .PSL 3 p f).1 := by rw [hga]; exact Nat.dvd_gcd dvd_rfl h3
  have hdv : (genericOrders .PSL 3 p f).1 ∣
      Nat.card ((StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F)) :=
    dvd_card_scalars (q := p ^ f) (by norm_num) hq0
      (Or.inl ⟨hF, rfl, hga ▸ Nat.gcd_dvd_left _ _, hga ▸ Nat.gcd_dvd_right _ _⟩)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hfin
  have hM : (Nat.card (hopfMultiplier (StatedProj (StatedSL 3 F)))).factorization 3 ≤
      (Nat.card ((StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F))).factorization 3 := by
    rw [hcard]
    refine (factorization_card_table Nat.prime_three (by norm_num) hadm (Or.inl rfl) h3g).trans ?_
    exact (Nat.factorization_le_iff_dvd (genericOrders_fst_pos hadm).ne'
      Nat.card_pos.ne').2 hdv 3
  have hHperf : Group.IsPerfect (StatedSL 3 F) := by
    have := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := F) (n := 3)
      le_rfl
    exact Group.IsPerfect.ofSurjective (f := (specialLinearGroupEquivStatedSL 3 F).toMonoidHom)
      (specialLinearGroupEquivStatedSL 3 F).surjective
  obtain ⟨eq⟩ := equiv_of_cover_three hperf (H := StatedSL 3 F) (Or.inl ⟨hF, rfl, h3⟩) hHperf hq0
    (e.trans e') hZ hM
  exact ⟨F, inferInstance, inferInstance, by rw [hF]; omega, ⟨eq⟩⟩

theorem isSUThree_of_cover (hGA : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K]
    [Finite K] (hperf : Group.IsPerfect K) (hZ : Nat.card (Subgroup.center K) = 3) {X : Type}
    [Group X] (e : K ⧸ Subgroup.center K ≃* X) {p f : ℕ}
    (hm : CFSG.Models.LieModel X .PSU 3 p f) (h3 : 3 ∣ p ^ f + 1) :
    IsSUThreeWith (fun q => q % 3 = 2) K := by
  obtain ⟨-, hcl | ⟨h0, -⟩⟩ := hm
  swap
  · exact absurd h0 (by norm_num)
  obtain ⟨hadm, F, _, _, hF, ⟨e'⟩⟩ := hcl
  have hp : p.Prime := hadm.1
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have hmm : CFSG.Models.LieModel (StatedProj (StatedSU 3 (p ^ f) F)) .PSU 3 p f :=
    lieModel_of_classical ⟨hadm, F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨hfin, hcard⟩ := finite_and_card_hopf hGA hmm
  have hga : (genericOrders .PSU 3 p f).1 = Nat.gcd 3 (p ^ f + 1) := rfl
  have h3g : 3 ∣ (genericOrders .PSU 3 p f).1 := by rw [hga]; exact Nat.dvd_gcd dvd_rfl h3
  have hdv : (genericOrders .PSU 3 p f).1 ∣
      Nat.card ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (p ^ f) F)) :=
    dvd_card_scalars (q := p ^ f) (by norm_num) hq0
      (Or.inr ⟨hF, rfl, hga ▸ Nat.gcd_dvd_left _ _, hga ▸ Nat.gcd_dvd_right _ _⟩)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hfin
  have hM : (Nat.card (hopfMultiplier (StatedProj (StatedSU 3 (p ^ f) F)))).factorization 3 ≤
      (Nat.card ((StatedScalars (Fin 3) F).subgroupOf
        (StatedSU 3 (p ^ f) F))).factorization 3 := by
    rw [hcard]
    refine (factorization_card_table Nat.prime_three (by norm_num) hadm (Or.inr rfl) h3g).trans ?_
    exact (Nat.factorization_le_iff_dvd (genericOrders_fst_pos hadm).ne'
      Nat.card_pos.ne').2 hdv 3
  have hHperf : Group.IsPerfect (StatedSU 3 (p ^ f) F) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF le_rfl hadm.2.2.2
  obtain ⟨eq⟩ := equiv_of_cover_three hperf (H := StatedSU 3 (p ^ f) F)
    (Or.inr ⟨hF, rfl, h3⟩) hHperf hq0 (e.trans e') hZ hM
  exact ⟨F, inferInstance, inferInstance, p ^ f, hF, by omega, ⟨eq⟩⟩

end Three

section High

theorem blueprintLieModel_of_models_lin {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (hm : CFSG.Models.LieModel X t n p f) (ht : t = .PSL ∨ t = .PSU) (hn : n ≠ 0) :
    CFSG.Blueprint.LieModel X t n p f := by
  obtain ⟨-, hcl | ⟨h0, -⟩⟩ := hm
  · exact Or.inl ⟨by rcases ht with rfl | rfl <;> decide, hcl⟩
  · exact absurd h0 hn

theorem five_le_pRank_of_lin (hGA : CFSG.Open.GriessAllModelsStatement) {L : Type} [Group L]
    [Finite L] (hperf : Group.IsPerfect L) (hZ : Nat.card (Subgroup.center L) = 3)
    {t : StatedLieTag} {n r f : ℕ} (hm : CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) t n r f)
    (ht : t = .PSL ∨ t = .PSU) (hg : 3 ∣ diagGcd t n r f) (h6 : 6 ≤ n) :
    5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  have hcl := classical_of_lieModel hm ht
  have hlow := n_sub_two_le_pRank_of_model hcl ht (by omega) Nat.prime_three (by norm_num) hg
  have ha : 3 ∣ (genericOrders t n r f).1 := by
    rcases ht with rfl | rfl <;> exact hg
  obtain ⟨-, h⟩ := lieCoverRankHighLin_aux hGA hperf Nat.prime_three (by norm_num)
    (hZ ▸ dvd_rfl) (by omega) hm ht ha
  omega

end High

end CFSG.HardMathSupport.Solomon.Coordinator
