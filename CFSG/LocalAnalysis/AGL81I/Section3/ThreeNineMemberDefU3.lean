module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberDefLocal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAutCore
public import CFSG.Quasithin.Background.A318PL3Inst
public import CFSG.Quasithin.EmptyFaithful.S146zMListCl

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open
open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.BenderSuzuki.MatrixGroups
open CFSG.UnitaryThreeRecognition.Model
open CFSG.AGLEmbedding.UnitaryModel

private theorem normalizer_rootGroup_le_stabilizer_pinf {K : Type} [Field K] [Finite K]
    (J : HermitianForm 3 K) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (q : ℕ)
    (hK : Nat.card K = q ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = q) (hq : 1 < q) :
    Subgroup.normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) := by
  have hcardR : Nat.card (rootGroup J hJ) = q ^ 3 := card_rootGroup J hJ q hK hfix
  have hq3 : 1 < q ^ 3 := one_lt_pow₀ hq (by norm_num)
  haveI : Nontrivial (rootGroup J hJ) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcardR]; exact hq3)
  intro x hx
  rw [MulAction.mem_stabilizer_iff]
  by_cases hx1 : x⁻¹ • pinf J hJ = pinf J hJ
  · have h := smul_inv_smul x (pinf J hJ)
    simpa [hx1] using h
  · obtain ⟨r, hr1⟩ := exists_ne (1 : rootGroup J hJ)
    have hxr : x * (r : ProjectiveSpecialUnitaryMatrixGroup J) * x⁻¹ ∈ rootGroup J hJ :=
      ((Subgroup.mem_normalizer_iff.mp hx) (r : ProjectiveSpecialUnitaryMatrixGroup J)).mp
        r.2
    have hfixx : (x * (r : ProjectiveSpecialUnitaryMatrixGroup J) * x⁻¹) • pinf J hJ =
        pinf J hJ :=
      MulAction.mem_stabilizer_iff.mp (rootGroup_le_stabilizer J hJ hxr)
    have hrx : (r : ProjectiveSpecialUnitaryMatrixGroup J) • (x⁻¹ • pinf J hJ) =
        x⁻¹ • pinf J hJ := by
      have h := congrArg (fun y => x⁻¹ • y) hfixx
      simpa [mul_smul] using h
    obtain ⟨r₀, -, huniq⟩ :=
      rootGroup_regular J hJ (x⁻¹ • pinf J hJ) (x⁻¹ • pinf J hJ) hx1 hx1
    have hr_eq : r = r₀ := huniq r hrx
    have h1_eq : (1 : rootGroup J hJ) = r₀ := huniq 1 (by simp)
    exfalso
    exact hr1 (hr_eq.trans h1_eq.symm)

theorem threeNineOut_psu_three {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hG : StatedClassicalModel G .PSU 3 p 1) :
    Subgroup.center G = ⊥ ∧ ¬ p ∣ Nat.card (Outer G) ∧
      (∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ Nat.card (Outer G) → q = 3) ∧ 3 ∣ Nat.card G := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, hq, K, hField, hFinite, J, hJ, hK, hfix, ⟨e⟩⟩ := exists_equiv_psu hG
  letI : Field K := hField
  letI : Finite K := hFinite
  have hOut : Nat.card (Outer G) ∣ 2 * Nat.gcd 3 (p + 1) := by
    simpa using CFSG.Quasithin.A318P.outer_dvd_unitary (p₀ := p) (e₀ := 1) hG
  have hcenter : Subgroup.center G = ⊥ := by
    have hcM : Subgroup.center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ :=
      CFSG.AGLEmbedding.UnitaryModel.center_eq_bot J hJ hK hfix hq
    rw [← Subgroup.map_center_eq e] at hcM
    exact (Subgroup.map_eq_bot_iff_of_injective (H := Subgroup.center G)
      (f := e.toMonoidHom) e.injective).mp hcM
  refine ⟨hcenter, ?_, ?_, ?_⟩
  · intro hpdvd
    have hp2 : p ∣ 2 * Nat.gcd 3 (p + 1) := hpdvd.trans hOut
    rcases (Nat.Prime.dvd_mul hp).1 hp2 with h2 | hg
    · have hp_eq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
      omega
    · have hp3 : p ∣ 3 := hg.trans (Nat.gcd_dvd_left 3 (p + 1))
      have hp_eq : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hp3
      omega
  · intro q hqprime hq2 hqout
    have hqdvd : q ∣ 2 * Nat.gcd 3 (p + 1) := hqout.trans hOut
    rcases (Nat.Prime.dvd_mul hqprime).1 hqdvd with h2 | hg
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hqprime Nat.prime_two).1 h2) hq2
    · exact (Nat.prime_dvd_prime_iff_eq hqprime Nat.prime_three).1
        (hg.trans (Nat.gcd_dvd_left 3 (p + 1)))
  · exact CFSG.Quasithin.three_dvd_card_psu_three_model hG

theorem not_isBorelDLocal_psu_three {G : Type} [Group G] [Finite G] {p d f : ℕ}
    {Y : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2) (hd : d.Prime) (hdp : d ≠ p)
    (hdG : d ∣ Nat.card G) (hG : StatedClassicalModel G .PSU 3 p f) :
    ¬ IsBorelDLocal p d Y := by
  intro hY
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hf, hq, K, hField, hFinite, J, hJ, hK, hfix, ⟨e⟩⟩ := exists_equiv_psu hG
  letI : Field K := hField
  letI : Finite K := hFinite
  let M := ProjectiveSpecialUnitaryMatrixGroup J
  let Y' : Subgroup M := Y.map e.toMonoidHom
  have hY' : IsBorelDLocal p d Y' := hY.map_equiv e
  have hdM : d ∣ Nat.card M := by
    rw [← Nat.card_congr e.toEquiv]
    exact hdG
  obtain ⟨S, hS⟩ := exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨g, hYg, hNg⟩ := hY'.exists_conj hp S
  rw [hS] at hNg
  have hN_eq : Subgroup.normalizer (rootGroup J hJ : Set M) =
      MulAction.stabilizer M (pinf J hJ) :=
    le_antisymm (normalizer_rootGroup_le_stabilizer_pinf J hJ (p ^ f) hK hfix (by omega))
      (stabilizer_pinf_le_normalizer_rootGroup J hJ (p ^ f) hK hfix)
  have hco : IsCoatom (Subgroup.normalizer (rootGroup J hJ : Set M)) :=
    isCoatom_normalizer_rootGroup J hJ hK hfix hq
  have hYeq : Y'.map (MulAut.conj g).toMonoidHom =
      Subgroup.normalizer (rootGroup J hJ : Set M) :=
    (hco.le_iff_eq hYg.lt_top.ne).mp hNg
  haveI : MulAction.IsMultiplyPretransitive M (IsoPoint J) 2 :=
    isMultiplyPretransitive_two J hJ (p ^ f) hK hfix
  haveI : MulAction.IsPretransitive M (IsoPoint J) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have hindex : (Y'.map (MulAut.conj g).toMonoidHom).index = (p ^ f) ^ 3 + 1 := by
    rw [hYeq, hN_eq, MulAction.index_stabilizer_of_transitive]
    exact card_isoPoint J hJ (p ^ f) hK hfix
  have hmod := hYg.index_modEq_one_of_dvd hd hdM
  rw [hindex] at hmod
  have hdvd3 : d ∣ (p ^ f) ^ 3 := by
    have h := hmod.symm.dvd'
    simpa using h
  have hdpf : d ∣ p ^ f := hd.dvd_of_dvd_pow hdvd3
  have hpdvd : d ∣ p := hd.dvd_of_dvd_pow hdpf
  exact hdp ((Nat.prime_dvd_prime_iff_eq hd hp).mp hpdvd)

end CFSG.LocalAnalysis.AGL81I.Section3
