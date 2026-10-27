module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.LinearCover
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models

public section

namespace CFSG.HardMathSupport.Timmesfeld.FieldBonus

open Matrix CFSG.Assembly.LowTwoRank CFSG.Models CFSG.Blueprint.Multiplier
open CFSG.RankThree.PerfectCover (hopfMultiplier)
open CFSG.Open (GriessAllModelsStatement)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

theorem mulEquiv_of_three_cover_core {K : Type} [Field K] [Finite K]
    {H : Subgroup (GL (Fin 3) K)}
    (hdet : ∀ A ∈ H, (A : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hHperf : Group.IsPerfect H)
    (h3D : 3 ∣ Nat.card ((StatedScalars (Fin 3) K).subgroupOf H))
    {L : Type} [Group L] [Finite L] (hLperf : Group.IsPerfect L)
    (hZ : Nat.card (Subgroup.center L) = 3)
    (θ : L ⧸ Subgroup.center L ≃* StatedProj H)
    [Finite (hopfMultiplier (StatedProj H))]
    (hM : (Nat.card (hopfMultiplier (StatedProj H))).factorization 3 ≤ 1) :
    Nonempty (L ≃* ↥H) := by
  set D := (StatedScalars (Fin 3) K).subgroupOf H with hD
  have hDc : D ≤ Subgroup.center H := scalars_le_center H
  have hD3 : Nat.card D = 3 := by
    refine Nat.dvd_antisymm ?_ h3D
    refine CFSG.SectionRank.OddCover.card_scalars_dvd (by norm_num) H fun x c hc => ?_
    have h1 := hdet _ (x : H).2
    rw [hc] at h1
    apply Units.ext
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal] using h1
  let α : H →* StatedProj H := QuotientGroup.mk' D
  have hα : Function.Surjective α := QuotientGroup.mk'_surjective D
  have hαk : α.ker = D := QuotientGroup.ker_mk' D
  let β : L →* StatedProj H := CFSG.GH74.Generic.centralQuotientMap θ
  have hβ : Function.Surjective β := CFSG.GH74.Generic.centralQuotientMap_surjective θ
  have hβk : β.ker = Subgroup.center L := CFSG.GH74.Generic.centralQuotientMap_ker θ
  have hZp : IsPGroup 3 (Subgroup.center L) :=
    IsPGroup.of_card (n := 1) (by rw [hZ]; norm_num)
  have hM' : (Nat.card (hopfMultiplier (StatedProj H))).factorization 3 ≤
      (Nat.card α.ker).factorization 3 := by
    rw [hαk, hD3, Nat.Prime.factorization_self Nat.prime_three]
    exact hM
  obtain ⟨φ, hφs, hβφ⟩ := exists_hom_of_cover hHperf hLperf α hα (hαk ▸ hDc) β hβ hβk.le
    Nat.prime_three (by rw [hβk]; exact hZp) hM'
  have hcardH : Nat.card H = Nat.card (StatedProj H) * 3 := by
    rw [CFSG.GH74.Generic.card_eq_card_mul_card_ker α hα, hαk, hD3]
  have hcardL : Nat.card L = Nat.card (StatedProj H) * 3 := by
    rw [CFSG.GH74.Generic.card_eq_card_mul_card_ker β hβ, hβk, hZ]
  have hbij : Function.Bijective φ :=
    (Nat.bijective_iff_surjective_and_card φ).2 ⟨hφs, hcardH.trans hcardL.symm⟩
  exact ⟨(MulEquiv.ofBijective φ hbij).symm⟩

theorem det_eq_one_of_mem_statedSL {n : ℕ} {K : Type} [Field K] {A : GL (Fin n) K}
    (hA : A ∈ StatedSL n K) : (A : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hA

theorem statedSU_le_statedSL {n q : ℕ} {K : Type} [Field K] : StatedSU n q K ≤ StatedSL n K :=
  CFSG.Open.StatedAPI.statedSU_le_statedSL n q K

theorem factorization_three_hopf_le {t : StatedLieTag} {n p f M : ℕ}
    (hadm : StatedLieAdmissible t n p f) (ha : (genericOrders t n p f).1 = 3)
    (hM : M = (genericOrders t n p f).1 * (genericOrders t n p f).2 *
      ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2)) :
    M.factorization 3 ≤ 1 := by
  have hex := not_three_dvd_exceptional_of_dvd_generic (t := t) (n := n) (p := p) (f := f)
    (by rw [ha])
  have hb : ¬ 3 ∣ (genericOrders t n p f).2 := fun hd => by
    have := Nat.le_of_dvd (genericOrders_snd_le t n p f).1 hd
    have := (genericOrders_snd_le t n p f).2
    omega
  have h1 : (genericOrders t n p f).1 ≠ 0 := (genericOrders_fst_pos hadm).ne'
  have h2 : (genericOrders t n p f).2 ≠ 0 := (genericOrders_snd_le t n p f).1.ne'
  have h3 : (exceptionalOrders t n p f).1 ≠ 0 := (exceptionalOrders_le t n p f).1.1.ne'
  have h4 : (exceptionalOrders t n p f).2 ≠ 0 := (exceptionalOrders_le t n p f).2.1.ne'
  rw [hM, Nat.factorization_mul (mul_ne_zero h1 h2) (mul_ne_zero h3 h4),
    Nat.factorization_mul h1 h2, Nat.factorization_mul h3 h4]
  simp [Nat.factorization_eq_zero_of_not_dvd hb, Nat.factorization_eq_zero_of_not_dvd hex.1,
    Nat.factorization_eq_zero_of_not_dvd hex.2, ha, Nat.Prime.factorization_self Nat.prime_three]

theorem mulEquiv_statedSL_of_three_cover (hGA : GriessAllModelsStatement)
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (h3 : 3 ∣ p ^ f - 1)
    {L : Type} [Group L] [Finite L] (hLperf : Group.IsPerfect L)
    (hZ : Nat.card (Subgroup.center L) = 3)
    (θ : L ⧸ Subgroup.center L ≃* StatedProj (StatedSL 3 K)) :
    Nonempty (L ≃* ↥(StatedSL 3 K)) := by
  have hq0 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have hq2 : p ^ f ≠ 2 := fun h => by omega
  have hadm : StatedLieAdmissible .PSL 3 p f :=
    ⟨hp, hf, by norm_num, by simp [hq2], by simp⟩
  have hm : LieModel (StatedProj (StatedSL 3 K)) .PSL 3 p f :=
    lieModel_of_classical ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨hfin, hcard⟩ := finite_and_card_hopf hGA hm
  have h3a : 3 ∣ (genericOrders .PSL 3 p f).1 := Nat.dvd_gcd dvd_rfl h3
  have ha : (genericOrders .PSL 3 p f).1 = 3 :=
    Nat.dvd_antisymm (Nat.gcd_dvd_left _ _) h3a
  have := hfin
  have hHperf : Group.IsPerfect (StatedSL 3 K) := by
    have := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := K) (n := 3)
      (by norm_num)
    exact Group.IsPerfect.ofSurjective
      (f := (specialLinearGroupEquivStatedSL 3 K).toMonoidHom)
      (specialLinearGroupEquivStatedSL 3 K).surjective
  refine mulEquiv_of_three_cover_core (fun A hA => det_eq_one_of_mem_statedSL hA) hHperf ?_
    hLperf hZ θ (factorization_three_hopf_le hadm ha hcard)
  exact dvd_card_scalars (q := p ^ f) (by norm_num) hq0 (Or.inl ⟨hK, rfl, dvd_rfl, h3⟩)

theorem mulEquiv_statedSU_of_three_cover (hGA : GriessAllModelsStatement)
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (h3 : 3 ∣ p ^ f + 1) (hq2 : p ^ f ≠ 2)
    {L : Type} [Group L] [Finite L] (hLperf : Group.IsPerfect L)
    (hZ : Nat.card (Subgroup.center L) = 3)
    (θ : L ⧸ Subgroup.center L ≃* StatedProj (StatedSU 3 (p ^ f) K)) :
    Nonempty (L ≃* ↥(StatedSU 3 (p ^ f) K)) := by
  have hq0 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have hadm : StatedLieAdmissible .PSU 3 p f :=
    ⟨hp, hf, le_rfl, by simp [hq2]⟩
  have hm : LieModel (StatedProj (StatedSU 3 (p ^ f) K)) .PSU 3 p f :=
    lieModel_of_classical ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨hfin, hcard⟩ := finite_and_card_hopf hGA hm
  have h3a : 3 ∣ (genericOrders .PSU 3 p f).1 := Nat.dvd_gcd dvd_rfl h3
  have ha : (genericOrders .PSU 3 p f).1 = 3 :=
    Nat.dvd_antisymm (Nat.gcd_dvd_left _ _) h3a
  have := hfin
  have : Fact p.Prime := ⟨hp⟩
  have hHperf : Group.IsPerfect (StatedSU 3 (p ^ f) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK (by norm_num) (fun h => hq2 (congrArg Prod.snd h))
  refine mulEquiv_of_three_cover_core
    (fun A hA => det_eq_one_of_mem_statedSL (statedSU_le_statedSL hA)) hHperf ?_
    hLperf hZ θ (factorization_three_hopf_le hadm ha hcard)
  exact dvd_card_scalars (q := p ^ f) (by norm_num) hq0 (Or.inr ⟨hK, rfl, dvd_rfl, h3⟩)

end CFSG.HardMathSupport.Timmesfeld.FieldBonus
