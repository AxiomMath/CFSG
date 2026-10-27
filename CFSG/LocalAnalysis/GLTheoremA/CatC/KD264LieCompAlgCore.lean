module

public import CFSG.RankThree.PartOne.KF.ClsSUUpper
public import CFSG.RankThree.PartOne.KC.LinearSubfieldInclusion
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofCoverSU
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterUnitary

public section

namespace CFSG.ComponentClassification.PerfectCentralQuotient

open CFSG.ComponentClassification.PerfectAutomorphisms
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectCentralQuotient

variable {G T : Type*} [Group G] [Group T]

theorem equivalence_mk [Group.IsPerfect G] (φ : G →* T) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center G) (g : G) :
    equivalence φ hφ hker (g : G ⧸ Subgroup.center G) = (φ g : T ⧸ Subgroup.center T) :=
  rfl

theorem congr_centerQuotientHom_of_surjective [Group.IsPerfect G] (π : G →* T)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    {α : MulAut G} {γ : MulAut T} (hαγ : ∀ g, γ (π g) = π (α g)) :
    MulAut.congr (equivalence π hπ hker) (centerQuotientHom G α) = centerQuotientHom T γ := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center T) x
  obtain ⟨g, rfl⟩ := hπ t
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have hesymm : (equivalence π hπ hker).symm
      ((QuotientGroup.mk' (Subgroup.center T)) (π g)) = (g : G ⧸ Subgroup.center G) := by
    rw [QuotientGroup.mk'_apply, ← equivalence_mk π hπ hker g, MulEquiv.symm_apply_apply]
  have hG : (centerQuotientHom G α) (g : G ⧸ Subgroup.center G) =
      ((α g : G) : G ⧸ Subgroup.center G) :=
    onCenterQuotient_apply_mk α g
  have hT : (centerQuotientHom T γ) ((QuotientGroup.mk' (Subgroup.center T)) (π g)) =
      ((γ (π g) : T) : T ⧸ Subgroup.center T) :=
    onCenterQuotient_apply_mk γ (π g)
  rw [hesymm, hG, equivalence_mk, hT, hαγ]

theorem centerQuotientHom_mem_innAutDerived_iff_of_surjective [Group.IsPerfect G]
    (π : G →* T) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    {α : MulAut G} {γ : MulAut T} (hαγ : ∀ g, γ (π g) = π (α g)) :
    centerQuotientHom T γ ∈ innAutDerived (T ⧸ Subgroup.center T) ↔
      centerQuotientHom G α ∈ innAutDerived (G ⧸ Subgroup.center G) := by
  rw [← congr_centerQuotientHom_of_surjective π hπ hker hαγ]
  exact mem_innAutDerived_congr (equivalence π hπ hker)

theorem centerQuotientHom_pow_eq_one_iff_of_surjective [Group.IsPerfect G] (π : G →* T)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    {α : MulAut G} {γ : MulAut T} (hαγ : ∀ g, γ (π g) = π (α g)) (n : ℕ) :
    centerQuotientHom T γ ^ n = 1 ↔ centerQuotientHom G α ^ n = 1 := by
  rw [← congr_centerQuotientHom_of_surjective π hπ hker hαγ, ← map_pow,
    MulEquiv.map_eq_one_iff]

theorem centerQuotientHom_mem_innAutDerived {G : Type*} [Group G] {α : MulAut G}
    (hα : α ∈ innAutDerived G) :
    centerQuotientHom G α ∈ innAutDerived (G ⧸ Subgroup.center G) := by
  have hinner : inner G ≤ (innAutDerived (G ⧸ Subgroup.center G)).comap (centerQuotientHom G) := by
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    rw [Subgroup.mem_comap, CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_conj]
    exact inner_le_innAutDerived _ ⟨z, rfl⟩
  have hcomm : commutator (MulAut G) ≤
      (innAutDerived (G ⧸ Subgroup.center G)).comap (centerQuotientHom G) := by
    intro x hx
    rw [Subgroup.mem_comap]
    exact commutator_le_innAutDerived _ (map_mem_commutator_mulAut (centerQuotientHom G) hx)
  have hle : innAutDerived G ≤
      (innAutDerived (G ⧸ Subgroup.center G)).comap (centerQuotientHom G) :=
    sup_le hinner hcomm
  exact hle hα

end CFSG.ComponentClassification.PerfectCentralQuotient

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Matrix CFSG.Open

theorem card_statedSU_eq_nat {f : ℕ} {K : Type} [Field K] [CharP K 2]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K) {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (StatedSU n (2 ^ f) K) =
      (2 ^ f) ^ (n * (n - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 n, ((((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) := by
  have hEq := CFSG.RankThree.PartOne.KFU.card_statedSU_eq (K := K) (f := f) h (n := n) hn
  have hnonneg : ∀ i ∈ Finset.Icc 2 n,
      (0 : ℤ) ≤ (((2 ^ f : ℕ)) : ℤ) ^ i - (-1) ^ i := by
    intro i hi
    have h1 : (1 : ℤ) ≤ (((2 ^ f : ℕ)) : ℤ) := by
      have := Nat.one_le_pow f 2 (by norm_num)
      exact_mod_cast this
    have h2 : (1 : ℤ) ≤ (((2 ^ f : ℕ)) : ℤ) ^ i := one_le_pow₀ h1
    rcases neg_one_pow_eq_or ℤ i with hneg | hneg <;> rw [hneg] <;> linarith
  refine Nat.cast_injective (R := ℤ) ?_
  push_cast
  rw [hEq]
  congr 1
  exact Finset.prod_congr rfl fun i hi => (Int.toNat_of_nonneg (hnonneg i hi)).symm

theorem odd_card_scalars_of_even {E : Type} [Field E] [Finite E] {m : ℕ} (hm : 1 ≤ m)
    (heven : Even (Nat.card E)) :
    Odd (Nat.card (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars m E)) := by
  refine Odd.of_dvd_nat ?_ (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_scalars_dvd
    (K := E) (n := m) hm)
  obtain ⟨t, ht⟩ := heven
  have h2 : 2 ≤ Nat.card E := by
    have := Finite.one_lt_card (α := E)
    omega
  exact ⟨t - 1, by omega⟩

theorem card_eq_card_centerQuotient_mul_card_center_of_surjective {G K : Type*} [Group G]
    [Group K] (hperf : commutator G = ⊤) (f : G →* K) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center G) :
    Nat.card G = Nat.card (K ⧸ Subgroup.center K) * Nat.card (Subgroup.center G) := by
  haveI : Group.IsPerfect G := Group.isPerfect_def.mpr hperf
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G),
    Nat.card_congr
      (CFSG.ComponentClassification.PerfectCentralQuotient.equivalence f hf hker).toEquiv]

theorem pow_dvd_card_centerQuotient_of_surjective_specialLinear {E : Type} [Field E] [Finite E]
    {m e : ℕ} (hm : 1 ≤ m) (he : 1 ≤ e) (hE : Nat.card E = 2 ^ e) {K : Type*} [Group K]
    (f : SpecialLinearGroup (Fin m) E →* K) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center (SpecialLinearGroup (Fin m) E))
    (hperf : commutator (SpecialLinearGroup (Fin m) E) = ⊤) :
    2 ^ (e * (m * (m - 1) / 2)) ∣ Nat.card (K ⧸ Subgroup.center K) := by
  classical
  let G := SpecialLinearGroup (Fin m) E
  haveI : Group.IsPerfect G := Group.isPerfect_def.mpr hperf
  have heven : Even (Nat.card E) := by
    rw [hE]
    exact (Nat.even_pow' (by omega : e ≠ 0)).mpr even_two
  have hZodd : Odd (Nat.card (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars m E)) :=
    odd_card_scalars_of_even hm heven
  have hSL : Nat.card G = Nat.card E ^ (m * (m - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 m, (Nat.card E ^ i - 1) :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := E) (n := m) hm
  have hsplit : Nat.card G = Nat.card (K ⧸ Subgroup.center K) *
      Nat.card (Subgroup.center G) :=
    card_eq_card_centerQuotient_mul_card_center_of_surjective hperf f hf hker
  have hdvd : 2 ^ (e * (m * (m - 1) / 2)) ∣
      Nat.card (K ⧸ Subgroup.center K) * Nat.card (Subgroup.center G) := by
    rw [← hsplit, hSL, hE, ← pow_mul]
    exact dvd_mul_right _ _
  have hcop : Nat.Coprime (2 ^ (e * (m * (m - 1) / 2))) (Nat.card (Subgroup.center G)) := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hZodd)
  exact Nat.Coprime.dvd_of_dvd_mul_right hcop hdvd

theorem pow_dvd_card_centerQuotient_of_surjective_statedSU {E : Type} [Field E] [Finite E]
    {m f : ℕ} (hm : 3 ≤ m) (hf : 3 ≤ f) (hE : Nat.card E = (2 ^ f) ^ 2) {T : Type*} [Group T]
    (g : ↥(StatedSU m (2 ^ f) E) →* T) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center ↥(StatedSU m (2 ^ f) E))
    (hperf : commutator ↥(StatedSU m (2 ^ f) E) = ⊤) :
    2 ^ (f * (m * (m - 1) / 2)) ∣ Nat.card (T ⧸ Subgroup.center T) := by
  classical
  let G := ↥(StatedSU m (2 ^ f) E)
  haveI : Group.IsPerfect G := Group.isPerfect_def.mpr hperf
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP E 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := f) hE
  haveI := hchar
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f E :=
    CFSG.RankThree.PartOne.KFU.unitaryFieldData_two hE (by omega)
  have hq8 : 8 ≤ 2 ^ f := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hne : (m, 2 ^ f) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ f = 2 := by simpa using congrArg Prod.snd h
    omega
  have hQ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := E) (p := 2)
    (f := f) hE hm hne
  have hZ : Nat.card (Subgroup.center G) = Nat.gcd m (2 ^ f + 1) := by
    rw [hQ.2]
    exact CFSG.LocalAnalysis.RankFourTheoremC.card_scalars_statedSU (K := E) (r := 2)
      (f := f) hE (by omega)
  have hZodd : Odd (Nat.card (Subgroup.center G)) := by
    rw [hZ]
    refine Odd.of_dvd_nat ?_ (Nat.gcd_dvd_right _ _)
    obtain ⟨k, hk⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
    rw [hk, pow_succ]
    exact ⟨2 ^ k, by ring⟩
  have hsplit : Nat.card G = Nat.card (T ⧸ Subgroup.center T) *
      Nat.card (Subgroup.center G) :=
    card_eq_card_centerQuotient_mul_card_center_of_surjective hperf g hg hker
  have hSU : Nat.card G = (2 ^ f) ^ (m * (m - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 m, ((((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) :=
    card_statedSU_eq_nat hUF (by omega)
  have hdvd : 2 ^ (f * (m * (m - 1) / 2)) ∣
      Nat.card (T ⧸ Subgroup.center T) * Nat.card (Subgroup.center G) := by
    rw [← hsplit, hSU, ← pow_mul]
    exact dvd_mul_right _ _
  have hcop : Nat.Coprime (2 ^ (f * (m * (m - 1) / 2))) (Nat.card (Subgroup.center G)) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hZodd)
  exact Nat.Coprime.dvd_of_dvd_mul_right hcop hdvd

private theorem le_three_of_pow_two_dvd_504 {k : ℕ} (h : 2 ^ k ∣ 504) : k ≤ 3 := by
  rw [show (504 : ℕ) = 8 * 63 by norm_num] at h
  have h8 : 2 ^ k ∣ 8 :=
    Nat.Coprime.dvd_of_dvd_mul_right
      (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (by norm_num : Odd 63))) h
  rw [show (8 : ℕ) = 2 ^ 3 by norm_num] at h8
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h8

private theorem le_nine_of_pow_two_dvd_5515776 {k : ℕ} (h : 2 ^ k ∣ 5515776) : k ≤ 9 := by
  rw [show (5515776 : ℕ) = 512 * 10773 by norm_num] at h
  have h512 : 2 ^ k ∣ 512 :=
    Nat.Coprime.dvd_of_dvd_mul_right
      (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (by norm_num : Odd 10773))) h
  rw [show (512 : ℕ) = 2 ^ 9 by norm_num] at h512
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h512

theorem card_centerQuotient_eq_504_of_surjective_SL_two {F : Type} [Field F] [Finite F] {j : ℕ}
    (hj : 1 ≤ j) (hF : Nat.card F = 2 ^ (3 * j)) {T : Type*} [Group T]
    (g : SpecialLinearGroup (Fin 2) F →* T) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 2) F))
    (hperf : commutator (SpecialLinearGroup (Fin 2) F) = ⊤)
    (hN : Nat.card (T ⧸ Subgroup.center T) = 504 ∨
      Nat.card (T ⧸ Subgroup.center T) = 5515776) :
    j = 1 ∧ Nat.card (T ⧸ Subgroup.center T) = 504 := by
  classical
  let G := SpecialLinearGroup (Fin 2) F
  haveI : Group.IsPerfect G := Group.isPerfect_def.mpr hperf
  have hdvd : 2 ^ (3 * j) ∣ Nat.card (T ⧸ Subgroup.center T) := by
    simpa using pow_dvd_card_centerQuotient_of_surjective_specialLinear (E := F) (m := 2)
      (e := 3 * j) (by norm_num) (by omega) hF g hg hker hperf
  have hZ : Nat.card (Subgroup.center G) = 1 := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center,
      CFSG.RankThree.PartOne.card_scalars (K := F) (n := 2) (by norm_num)]
    have hodd : Odd (Nat.card F - 1) := by
      rw [hF, show 3 * j = (3 * j - 1) + 1 by omega, pow_succ]
      refine ⟨2 ^ (3 * j - 1) - 1, ?_⟩
      have : 1 ≤ 2 ^ (3 * j - 1) := Nat.one_le_pow _ _ (by norm_num)
      omega
    exact Nat.coprime_iff_gcd_eq_one.mp (Nat.coprime_two_left.mpr hodd)
  have hSL : Nat.card (SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := F) (n := 2)
      (by norm_num)]
    norm_num
  have hpow : (2 ^ (3 * j)) ^ 2 = 2 ^ (6 * j) := by
    rw [← pow_mul, show 3 * j * 2 = 6 * j by ring]
  have horder : Nat.card (T ⧸ Subgroup.center T) = 2 ^ (3 * j) * (2 ^ (6 * j) - 1) := by
    have hcard := card_eq_card_centerQuotient_mul_card_center_of_surjective hperf g hg hker
    rw [hZ, mul_one] at hcard
    rw [← hcard, hSL, hF, hpow]
  rcases hN with hN | hN
  · have hle : 3 * j ≤ 3 := le_three_of_pow_two_dvd_504 (by rwa [hN] at hdvd)
    have hj1 : j = 1 := by omega
    subst hj1
    exact ⟨rfl, hN⟩
  · have hle : 3 * j ≤ 9 := le_nine_of_pow_two_dvd_5515776 (by rwa [hN] at hdvd)
    have hjle : j ≤ 3 := by omega
    rw [hN] at horder
    interval_cases j <;> norm_num at horder

theorem card_centerQuotient_statedSU_three_eight {E : Type} [Field E] [Finite E]
    (hE : Nat.card E = 64) {T : Type*} [Group T]
    (g : ↥(StatedSU 3 8 E) →* T) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center ↥(StatedSU 3 8 E))
    (hperf : commutator ↥(StatedSU 3 8 E) = ⊤) :
    Nat.card (T ⧸ Subgroup.center T) = 5515776 := by
  classical
  let G := ↥(StatedSU 3 8 E)
  haveI : Group.IsPerfect G := Group.isPerfect_def.mpr hperf
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h8 : (2 : ℕ) ^ 3 = 8 := by norm_num
  have hE8 : Nat.card E = (2 ^ 3) ^ 2 := by rw [hE]; norm_num
  have hchar : CharP E 2 :=
    CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := 3) hE8
  haveI := hchar
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 3 E :=
    CFSG.RankThree.PartOne.KFU.unitaryFieldData_two hE8 (by norm_num)
  have hne : (3, 2 ^ 3) ≠ (3, 2) := by norm_num
  have hQ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := E) (p := 2)
    (f := 3) hE8 (by norm_num) hne
  have hQ8 : CFSG.IsQuasisimple G ∧ Subgroup.center G =
      (StatedScalars (Fin 3) E).subgroupOf (StatedSU 3 8 E) := by
    have h := hQ
    rw [h8] at h
    exact h
  have hZ : Nat.card (Subgroup.center G) = 3 := by
    rw [hQ8.2]
    have hc := CFSG.LocalAnalysis.RankFourTheoremC.card_scalars_statedSU (K := E) (r := 2)
      (f := 3) (n := 3) hE8 (by norm_num)
    rw [h8] at hc
    rw [hc]
    norm_num
  have hprod : ∏ i ∈ Finset.Icc 2 3, ((((8 : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) = 63 * 513 := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num,
      Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 2 + 1), Finset.Icc_self,
      Finset.prod_singleton]
    norm_num
  have hSU : Nat.card G = 512 * (63 * 513) := by
    have hc := card_statedSU_eq_nat (n := 3) hUF (by norm_num)
    rw [h8] at hc
    rw [hc, hprod]
    norm_num
  have hcard := card_eq_card_centerQuotient_mul_card_center_of_surjective hperf g hg hker
  rw [hSU, hZ] at hcard
  omega

theorem card_centerQuotient_eq_5515776_of_surjective_statedSU {E : Type} [Field E] [Finite E]
    {m j : ℕ} (hm : 3 ≤ m) (hj : 1 ≤ j) (hE : Nat.card E = (2 ^ (3 * j)) ^ 2)
    {T : Type*} [Group T] (g : ↥(StatedSU m (2 ^ (3 * j)) E) →* T)
    (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center ↥(StatedSU m (2 ^ (3 * j)) E))
    (hperf : commutator ↥(StatedSU m (2 ^ (3 * j)) E) = ⊤)
    (hN : Nat.card (T ⧸ Subgroup.center T) = 504 ∨
      Nat.card (T ⧸ Subgroup.center T) = 5515776) :
    m = 3 ∧ j = 1 ∧ Nat.card (T ⧸ Subgroup.center T) = 5515776 := by
  classical
  let G := ↥(StatedSU m (2 ^ (3 * j)) E)
  haveI : Group.IsPerfect G := Group.isPerfect_def.mpr hperf
  have hdvd : 2 ^ (3 * j * (m * (m - 1) / 2)) ∣ Nat.card (T ⧸ Subgroup.center T) :=
    pow_dvd_card_centerQuotient_of_surjective_statedSU (f := 3 * j) hm (by omega) hE g hg hker
      hperf
  have hk9 : 9 ≤ 3 * j * (m * (m - 1) / 2) := by
    have h3 : 3 ≤ m * (m - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      have h2 : 2 ≤ m - 1 := by omega
      calc 3 * 2 = 3 * 2 := rfl
        _ ≤ m * (m - 1) := Nat.mul_le_mul hm h2
    have h3' : 3 ≤ j * (m * (m - 1) / 2) := by
      calc 3 = 1 * 3 := by norm_num
        _ ≤ j * (m * (m - 1) / 2) := Nat.mul_le_mul hj h3
    calc 9 = 3 * 3 := by norm_num
      _ ≤ 3 * (j * (m * (m - 1) / 2)) := Nat.mul_le_mul_left 3 h3'
      _ = 3 * j * (m * (m - 1) / 2) := by ring
  have hle : 3 * j * (m * (m - 1) / 2) ≤ 9 := by
    rcases hN with hN | hN
    · have h3 := le_three_of_pow_two_dvd_504 (by rwa [hN] at hdvd)
      omega
    · exact le_nine_of_pow_two_dvd_5515776 (by rwa [hN] at hdvd)
  have hk : 3 * j * (m * (m - 1) / 2) = 9 := le_antisymm hle hk9
  have h3 : 3 ≤ m * (m - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    have h2 : 2 ≤ m - 1 := by omega
    calc 3 * 2 = 3 * 2 := rfl
      _ ≤ m * (m - 1) := Nat.mul_le_mul hm h2
  set K := j * (m * (m - 1) / 2) with hK
  have hK3 : K = 3 := by
    have h9 : 3 * K = 9 := by
      calc 3 * K = 3 * j * (m * (m - 1) / 2) := by rw [hK]; ring
        _ = 9 := hk
    omega
  have ht : m * (m - 1) / 2 = 3 := by
    have hdvd3 : m * (m - 1) / 2 ∣ 3 := ⟨j, by rw [← hK3, hK, mul_comm]⟩
    rcases (show Nat.Prime 3 by norm_num).eq_one_or_self_of_dvd _ hdvd3 with h | h
    · omega
    · exact h
  have hj1 : j = 1 := by rw [ht] at hK; omega
  have hm3 : m = 3 := by
    rcases Nat.lt_or_ge m 4 with h | h
    · omega
    · have h6 : 6 ≤ m * (m - 1) / 2 := by
        rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
        have h2 : 3 ≤ m - 1 := by omega
        calc 6 * 2 = 4 * 3 := by norm_num
          _ ≤ m * (m - 1) := Nat.mul_le_mul h h2
      omega
  subst hm3
  subst hj1
  have hE64 : Nat.card E = 64 := by rw [hE]; norm_num
  exact ⟨rfl, rfl, card_centerQuotient_statedSU_three_eight hE64 g hg hker hperf⟩

theorem card_centerQuotient_SL_two_six {E : Type} [Field E] [Finite E]
    (hE : Nat.card E = 64) {T : Type*} [Group T]
    (g : SpecialLinearGroup (Fin 2) E →* T) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 2) E))
    (hperf : commutator (SpecialLinearGroup (Fin 2) E) = ⊤) :
    Nat.card (T ⧸ Subgroup.center T) = 262080 := by
  classical
  let G := SpecialLinearGroup (Fin 2) E
  haveI : Group.IsPerfect G := Group.isPerfect_def.mpr hperf
  have hprod : ∏ i ∈ Finset.Icc 2 2, (64 ^ i - 1) = 4095 := by
    rw [Finset.Icc_self, Finset.prod_singleton]
    norm_num
  have hgcd1 : Nat.gcd 2 (Nat.card E - 1) = 1 := by
    rw [hE]
    exact Nat.coprime_iff_gcd_eq_one.mp
      (Nat.coprime_two_left.mpr (by norm_num : Odd 63))
  have hZ : Nat.card (Subgroup.center G) = Nat.gcd 2 (Nat.card E - 1) := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]
    exact CFSG.RankThree.PartOne.card_scalars (K := E) (n := 2) (by norm_num)
  have hSL : Nat.card G = Nat.card E ^ (2 * (2 - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 2, (Nat.card E ^ i - 1) :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := E) (n := 2) (by norm_num)
  have hcard := card_eq_card_centerQuotient_mul_card_center_of_surjective hperf g hg hker
  rw [hSL, hE, hZ, hgcd1, hprod] at hcard
  norm_num at hcard ⊢
  omega

theorem false_of_surjective_SL_of_card_eq_two_pow_six_mul {E : Type} [Field E] [Finite E]
    {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hE : Nat.card E = 2 ^ (2 * (3 * j)))
    {T : Type*} [Group T] (g : SpecialLinearGroup (Fin m) E →* T)
    (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center (SpecialLinearGroup (Fin m) E))
    (hperf : commutator (SpecialLinearGroup (Fin m) E) = ⊤)
    (hN : Nat.card (T ⧸ Subgroup.center T) = 504 ∨
      Nat.card (T ⧸ Subgroup.center T) = 5515776) : False := by
  classical
  let G := SpecialLinearGroup (Fin m) E
  haveI : Group.IsPerfect G := Group.isPerfect_def.mpr hperf
  have hE6 : Nat.card E = 2 ^ (6 * j) := by
    rw [hE, show 2 * (3 * j) = 6 * j by ring]
  have hdvd : 2 ^ (6 * j * (m * (m - 1) / 2)) ∣ Nat.card (T ⧸ Subgroup.center T) :=
    pow_dvd_card_centerQuotient_of_surjective_specialLinear (E := E) (m := m) (e := 6 * j)
      (by omega) (by omega) hE6 g hg hker hperf
  have hk6 : 6 ≤ 6 * j * (m * (m - 1) / 2) := by
    have h1 : 1 ≤ m * (m - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      have h1m : 2 ≤ m := hm
      have h2 : 1 ≤ m - 1 := by omega
      calc 1 * 2 = 2 * 1 := by norm_num
        _ ≤ m * (m - 1) := Nat.mul_le_mul h1m h2
    have h61 : 6 * 1 ≤ 6 * j := Nat.mul_le_mul_left 6 hj
    calc 6 = 6 * 1 * 1 := by norm_num
      _ ≤ 6 * j * (m * (m - 1) / 2) := Nat.mul_le_mul h61 h1
  rcases hN with hN | hN
  · have hle : 6 * j * (m * (m - 1) / 2) ≤ 3 :=
      le_three_of_pow_two_dvd_504 (by rwa [hN] at hdvd)
    omega
  · have hle : 6 * j * (m * (m - 1) / 2) ≤ 9 :=
      le_nine_of_pow_two_dvd_5515776 (by rwa [hN] at hdvd)
    have h1 : 1 ≤ m * (m - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      have h1m : 2 ≤ m := hm
      have h2 : 1 ≤ m - 1 := by omega
      calc 1 * 2 = 2 * 1 := by norm_num
        _ ≤ m * (m - 1) := Nat.mul_le_mul h1m h2
    set K := j * (m * (m - 1) / 2) with hK
    have hK1 : K ≤ 1 := by
      have h9 : 6 * K ≤ 9 := by
        calc 6 * K = 6 * j * (m * (m - 1) / 2) := by rw [hK]; ring
          _ ≤ 9 := hle
      omega
    have ht : m * (m - 1) / 2 = 1 := by
      have hKt : m * (m - 1) / 2 ≤ K := by
        rw [hK]
        exact Nat.le_mul_of_pos_left _ (by omega : 0 < j)
      omega
    have hj1 : j = 1 := by
      rw [ht, mul_one] at hK
      omega
    have hm2 : m = 2 := by
      rcases Nat.lt_or_ge m 3 with h | h
      · omega
      · have h6 : 3 ≤ m * (m - 1) / 2 := by
          rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
          have h2 : 2 ≤ m - 1 := by omega
          calc 3 * 2 = 3 * 2 := rfl
            _ ≤ m * (m - 1) := Nat.mul_le_mul h h2
        omega
    subst hm2
    subst hj1
    have hE64 : Nat.card E = 64 := by rw [hE6]; norm_num
    have hval := card_centerQuotient_SL_two_six hE64 g hg hker hperf
    rw [hN] at hval
    norm_num at hval

section UnitaryBlock

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.PerfectAutomorphisms
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectCentralQuotient
open CFSG.RankThree.CentralLift
open CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {K : Type} [Field K]

theorem toLin'_mem_sesqUnitaryGroup_iff_primeFormUnitary {V : Type*} [AddCommGroup V]
    [Module K V] {n : ℕ} (h : UnitaryFieldData p f K) {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    (e : Module.Basis (Fin n) K V) {G : Matrix (Fin n) (Fin n) K}
    (he : ∀ i j, B (e i) (e j) = G i j) (M : GL (Fin n) K) :
    Matrix.GeneralLinearGroup.toLin' e M ∈ sesqUnitaryGroup B ↔ M ∈ primeFormUnitary h G := by
  rw [mem_sesqUnitaryGroup, mem_primeFormUnitary, ← gramForm_isometry_iff h]
  constructor
  · intro hiso x y
    have huv := hiso (e.equivFun.symm x) (e.equivFun.symm y)
    simpa only [form_eq_gramForm h e he, equivFun_toLin'_basis_apply,
      LinearEquiv.apply_symm_apply] using huv
  · intro hM x y
    have huv := hM (e.equivFun x) (e.equivFun y)
    simpa only [form_eq_gramForm h e he, equivFun_toLin'_basis_apply,
      LinearEquiv.apply_symm_apply] using huv

@[expose] noncomputable def gramSUEquivSesqSpecialUnitaryGroup {V : Type*} [AddCommGroup V]
    [Module K V] {ι : Type*} [Fintype ι] [DecidableEq ι] (h : UnitaryFieldData p f K)
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (e : Module.Basis ι K V) {G : Matrix ι ι K}
    (he : ∀ i j, B (e i) (e j) = G i j) :
    ↥(gramSU h G) ≃* ↥(sesqSpecialUnitaryGroup B) :=
  (Matrix.GeneralLinearGroup.toLin' e).subgroupMap (gramSU h G) |>.trans
    (MulEquiv.subgroupCongr (by
      ext g
      constructor
      · rintro ⟨M, hM, rfl⟩
        exact (toLin'_mem_sesqSpecialUnitaryGroup_iff_gramSU h e he M).2 hM
      · intro hg
        refine ⟨(Matrix.GeneralLinearGroup.toLin' e).symm g, ?_,
          MulEquiv.apply_symm_apply _ _⟩
        exact (toLin'_mem_sesqSpecialUnitaryGroup_iff_gramSU h e he _).1 (by
          rw [MulEquiv.apply_symm_apply]
          exact hg)))

@[simp]
theorem gramSUEquivSesqSpecialUnitaryGroup_apply {V : Type*} [AddCommGroup V] [Module K V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (h : UnitaryFieldData p f K)
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (e : Module.Basis ι K V) {G : Matrix ι ι K}
    (he : ∀ i j, B (e i) (e j) = G i j) (s : ↥(gramSU h G)) :
    ((gramSUEquivSesqSpecialUnitaryGroup h e he s : ↥(sesqSpecialUnitaryGroup B)) :
      LinearMap.GeneralLinearGroup K V) = Matrix.GeneralLinearGroup.toLin' e (s : GL ι K) := by
  simp [gramSUEquivSesqSpecialUnitaryGroup]

theorem conj_mem_sesqSpecialUnitaryGroup {k M : Type*} [Field k] {σ : k →+* k}
    [AddCommGroup M] [Module k M] {B : M →ₛₗ[σ] M →ₗ[k] k}
    (g : ↥(sesqUnitaryGroup B)) {s : LinearMap.GeneralLinearGroup k M}
    (hs : s ∈ sesqSpecialUnitaryGroup B) :
    (g : LinearMap.GeneralLinearGroup k M) * s *
      (↑(g⁻¹) : LinearMap.GeneralLinearGroup k M) ∈ sesqSpecialUnitaryGroup B := by
  rw [mem_sesqSpecialUnitaryGroup] at hs ⊢
  obtain ⟨hsu, hsd⟩ := hs
  have hgU : ∀ x y, B (((g : LinearMap.GeneralLinearGroup k M) : M →ₗ[k] M) x)
      (((g : LinearMap.GeneralLinearGroup k M) : M →ₗ[k] M) y) = B x y := g.2
  have hgiU : ∀ x y, B (((↑(g⁻¹) : LinearMap.GeneralLinearGroup k M) : M →ₗ[k] M) x)
      (((↑(g⁻¹) : LinearMap.GeneralLinearGroup k M) : M →ₗ[k] M) y) = B x y :=
    (sesqUnitaryGroup B).inv_mem g.2
  refine ⟨?_, ?_⟩
  · rw [mem_sesqUnitaryGroup]
    intro x y
    rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply]
    exact (hgU _ _).trans (((mem_sesqUnitaryGroup.mp hsu) _ _).trans (hgiU _ _))
  · have hgg : (((g : LinearMap.GeneralLinearGroup k M) : M →ₗ[k] M) *
        ((↑(g⁻¹) : LinearMap.GeneralLinearGroup k M) : M →ₗ[k] M)) = 1 := by
      rw [← Units.val_mul, Subgroup.coe_inv, mul_inv_cancel, Units.val_one]
    have hprod : LinearMap.det ((g : LinearMap.GeneralLinearGroup k M) : M →ₗ[k] M) *
        LinearMap.det ((↑(g⁻¹) : LinearMap.GeneralLinearGroup k M) : M →ₗ[k] M) = 1 := by
      rw [← map_mul, hgg, map_one]
    calc LinearMap.det ((↑((g : LinearMap.GeneralLinearGroup k M) * s *
          (↑(g⁻¹) : LinearMap.GeneralLinearGroup k M))) : M →ₗ[k] M)
        = LinearMap.det ((g : LinearMap.GeneralLinearGroup k M) : M →ₗ[k] M) *
            LinearMap.det (s : M →ₗ[k] M) *
            LinearMap.det ((↑(g⁻¹) : LinearMap.GeneralLinearGroup k M) : M →ₗ[k] M) := by
          rw [Units.val_mul, Units.val_mul, map_mul, map_mul]
      _ = 1 := by rw [hsd, mul_one]; exact hprod

@[expose] noncomputable def sesqSUConj {k M : Type*} [Field k] {σ : k →+* k}
    [AddCommGroup M] [Module k M] {B : M →ₛₗ[σ] M →ₗ[k] k}
    (g : ↥(sesqUnitaryGroup B)) : MulAut ↥(sesqSpecialUnitaryGroup B) where
  toFun s := ⟨(g : LinearMap.GeneralLinearGroup k M) * (s : LinearMap.GeneralLinearGroup k M) *
    (↑(g⁻¹) : LinearMap.GeneralLinearGroup k M), conj_mem_sesqSpecialUnitaryGroup g s.2⟩
  invFun s := ⟨(↑(g⁻¹) : LinearMap.GeneralLinearGroup k M) *
    (s : LinearMap.GeneralLinearGroup k M) * (g : LinearMap.GeneralLinearGroup k M), by
      have h := conj_mem_sesqSpecialUnitaryGroup
        (g := (⟨(↑(g⁻¹) : LinearMap.GeneralLinearGroup k M), (sesqUnitaryGroup B).inv_mem g.2⟩ :
          ↥(sesqUnitaryGroup B))) s.2
      simpa using h⟩
  left_inv s := Subtype.ext (by simp only [Subgroup.coe_inv]; group)
  right_inv s := Subtype.ext (by simp only [Subgroup.coe_inv]; group)
  map_mul' s t := Subtype.ext (by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group)

@[simp]
theorem sesqSUConj_apply {k M : Type*} [Field k] {σ : k →+* k} [AddCommGroup M] [Module k M]
    {B : M →ₛₗ[σ] M →ₗ[k] k} (g : ↥(sesqUnitaryGroup B))
    (s : ↥(sesqSpecialUnitaryGroup B)) :
    ((sesqSUConj g s : ↥(sesqSpecialUnitaryGroup B)) : LinearMap.GeneralLinearGroup k M) =
      (g : LinearMap.GeneralLinearGroup k M) * (s : LinearMap.GeneralLinearGroup k M) *
        (g : LinearMap.GeneralLinearGroup k M)⁻¹ := by
  show (↑g : LinearMap.GeneralLinearGroup k M) * (↑s : LinearMap.GeneralLinearGroup k M) *
    (↑(g⁻¹) : LinearMap.GeneralLinearGroup k M) = _
  rw [Subgroup.coe_inv]

theorem primeFormConjSU_coe {p f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    {C : Matrix (Fin n) (Fin n) K} (A : primeFormUnitary h C) (s : gramSU h C) :
    ((primeFormConjSU h C A s : gramSU h C) : GL (Fin n) K) =
      (A : GL (Fin n) K) * (s : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ :=
  rfl

theorem centerQuotientHom_mem_innAutDerived_of_primeFormConjSU {ℓ f N p : ℕ} {E : Type}
    [Field E] (hE : UnitaryFieldData ℓ f E) (hp : p.Prime) (hp2 : p ≠ 2)
    (hperf : commutator ↥(gramSU hE ((1 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)) = ⊤)
    (M : primeFormUnitary hE ((1 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E))
    {T : Type*} [Group T]
    (π : ↥(gramSU hE ((1 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)) →* T)
    (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥(gramSU hE ((1 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)))
    {γ : MulAut T}
    (hγ : ∀ s : ↥(gramSU hE ((1 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)),
      γ (π s) = π (primeFormConjSU hE ((1 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) M s))
    (hγp : centerQuotientHom T γ ^ p = 1) :
    centerQuotientHom T γ ∈ innAutDerived (T ⧸ Subgroup.center T) := by
  classical
  let C : Matrix (Fin N) (Fin N) E := ((1 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)
  let G := ↥(gramSU hE C)
  let Q := primeFormP hE C
  let ρ : G →* Q := QuotientGroup.mk' (normOneScalars hE (gramSU hE C) N)
  haveI : Group.IsPerfect G := Group.isPerfect_def.mpr hperf
  have hρsurj : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  have hρker : ρ.ker ≤ Subgroup.center G := by
    have hker_eq : ρ.ker = normOneScalars hE (gramSU hE C) N :=
      QuotientGroup.ker_mk' (normOneScalars hE (gramSU hE C) N)
    rw [hker_eq]
    exact normOneScalars_le_center hE _ N
  have hρ : ∀ s : G, primeFormConjHom hE C M (ρ s) = ρ (primeFormConjSU hE C M s) :=
    fun s => primeFormConjAut_mk hE C M s
  have hαγ : ∀ s : ↥(gramSU hE C), γ (π s) = π (primeFormConjSU hE C M s) := hγ
  have hpowG : centerQuotientHom G (primeFormConjSU hE C M) ^ p = 1 :=
    (centerQuotientHom_pow_eq_one_iff_of_surjective (G := ↥(gramSU hE C)) (T := T)
      (π := π) hπ hker (α := primeFormConjSU hE C M) (γ := γ) hαγ p).mp hγp
  have hpowQ : centerQuotientHom Q (primeFormConjHom hE C M) ^ p = 1 :=
    (centerQuotientHom_pow_eq_one_iff_of_surjective (G := G) (T := Q)
      (π := ρ) hρsurj hρker (α := primeFormConjSU hE C M) (γ := primeFormConjHom hE C M)
      hρ p).mpr hpowG
  have hQperf : commutator Q = ⊤ := by
    have h := Subgroup.map_commutator (H₁ := (⊤ : Subgroup G)) (H₂ := (⊤ : Subgroup G))
      (ρ : G →* Q)
    rw [show (⁅(⊤ : Subgroup G), ⊤⁆ : Subgroup G) = ⊤ from hperf,
      Subgroup.map_top_of_surjective ρ hρsurj] at h
    exact h.symm
  haveI : Group.IsPerfect Q := Group.isPerfect_def.mpr hQperf
  have hcMp : (primeFormConjHom hE C M) ^ p = 1 := by
    apply CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective Q
    rw [map_pow, map_one]
    exact hpowQ
  have hcM : primeFormConjHom hE C M ∈ innAutDerived Q :=
    mem_innAutDerived_of_mem_primeFormD hE hp hp2 (x := primeFormConjHom hE C M) ⟨M, rfl⟩ hcMp
  have hQmem : centerQuotientHom Q (primeFormConjHom hE C M) ∈
      innAutDerived (Q ⧸ Subgroup.center Q) :=
    centerQuotientHom_mem_innAutDerived hcM
  exact (centerQuotientHom_mem_innAutDerived_iff_of_surjective (G := ↥(gramSU hE C)) (T := T)
    (π := π) hπ hker (α := primeFormConjSU hE C M) (γ := γ) hαγ).mpr
    ((centerQuotientHom_mem_innAutDerived_iff_of_surjective (G := G) (T := Q)
      (π := ρ) hρsurj hρker (α := primeFormConjSU hE C M) (γ := primeFormConjHom hE C M)
      hρ).mp hQmem)

theorem centerQuotientHom_mem_innAutDerived_of_sesqSUConj {ℓ f p : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ f E) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {H : W →ₛₗ[hE.bar] W →ₗ[E] E} (hH : H.IsSymm)
    (hHl : H.SeparatingLeft) (hperf : commutator ↥(sesqSpecialUnitaryGroup H) = ⊤)
    (hp : p.Prime) (hp2 : p ≠ 2) (g : ↥(sesqUnitaryGroup H)) {T : Type*} [Group T]
    (π : ↥(sesqSpecialUnitaryGroup H) →* T) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥(sesqSpecialUnitaryGroup H)) {γ : MulAut T}
    (hγ : ∀ s, γ (π s) = π (sesqSUConj (B := H) g s))
    (hγp : centerQuotientHom T γ ^ p = 1) :
    centerQuotientHom T γ ∈ innAutDerived (T ⧸ Subgroup.center T) := by
  classical
  obtain ⟨e, he⟩ := hE.exists_orthonormal_basis (M := W) hH hHl
  let N := Module.finrank E W
  let C : Matrix (Fin N) (Fin N) E := ((1 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)
  have he' : ∀ i j, H (e i) (e j) = C i j := by
    intro i j
    rw [show C i j = if i = j then 1 else 0 by simp [C, Units.val_one, Matrix.one_apply]]
    exact he i j
  let Ψ : ↥(gramSU hE C) ≃* ↥(sesqSpecialUnitaryGroup H) :=
    gramSUEquivSesqSpecialUnitaryGroup (h := hE) (B := H) e he'
  let M : GL (Fin N) E :=
    (Matrix.GeneralLinearGroup.toLin' e).symm (g : LinearMap.GeneralLinearGroup E W)
  have htoLinM : Matrix.GeneralLinearGroup.toLin' e M =
      (g : LinearMap.GeneralLinearGroup E W) :=
    MulEquiv.apply_symm_apply _ _
  have hM : M ∈ primeFormUnitary hE C := by
    rw [← toLin'_mem_sesqUnitaryGroup_iff_primeFormUnitary (h := hE) (B := H) e he' M]
    rw [htoLinM]
    exact g.2
  have hperf' : commutator ↥(gramSU hE C) = ⊤ := by
    have htop : (commutator ↥(gramSU hE C)).map Ψ.toMonoidHom = ⊤ := by
      rw [commutator_def, Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥(gramSU hE C)))
        (H₂ := (⊤ : Subgroup ↥(gramSU hE C))) Ψ.toMonoidHom,
        Subgroup.map_top_of_surjective Ψ.toMonoidHom Ψ.surjective, ← commutator_def, hperf]
    rw [eq_top_iff]
    intro x _
    have hx : Ψ x ∈ (commutator ↥(gramSU hE C)).map Ψ.toMonoidHom := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [Ψ.injective hyx] at hy
  have hcenter : (Subgroup.center ↥(sesqSpecialUnitaryGroup H)).comap Ψ.toMonoidHom =
      Subgroup.center ↥(gramSU hE C) := by
    ext x
    rw [Subgroup.mem_comap, ← Subgroup.map_center_eq Ψ]
    exact Subgroup.mem_map_iff_mem
      (f := (Ψ : ↥(gramSU hE C) →* ↥(sesqSpecialUnitaryGroup H))) Ψ.injective
  have hker' : (π.comp Ψ.toMonoidHom).ker ≤ Subgroup.center ↥(gramSU hE C) := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
    rw [← hcenter]
    exact hker hx
  have hΨ : ∀ s : ↥(gramSU hE C),
      Ψ (primeFormConjSU hE C ⟨M, hM⟩ s) = sesqSUConj (B := H) g (Ψ s) := by
    intro s
    apply Subtype.ext
    rw [gramSUEquivSesqSpecialUnitaryGroup_apply, primeFormConjSU_coe, map_mul, map_mul, map_inv,
      htoLinM, sesqSUConj_apply, gramSUEquivSesqSpecialUnitaryGroup_apply]
  refine centerQuotientHom_mem_innAutDerived_of_primeFormConjSU (hE := hE) (hp := hp)
    (hp2 := hp2) (hperf := hperf') (M := ⟨M, hM⟩) (π := π.comp Ψ.toMonoidHom) ?_ ?_ ?_ hγp
  · exact hπ.comp Ψ.surjective
  · exact hker'
  · intro s
    change γ (π (Ψ s)) = π (Ψ (primeFormConjSU hE C ⟨M, hM⟩ s))
    rw [hΨ]
    exact hγ (Ψ s)

end UnitaryBlock
end CFSG.LocalAnalysis.GLTheoremA.KD264Lie
