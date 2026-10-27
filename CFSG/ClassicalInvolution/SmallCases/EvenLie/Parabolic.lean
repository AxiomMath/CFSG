module

public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Basic
public import CFSG.Blueprint.Catalog
import CFSG.LieType.BorelTits.AllModels

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem centralizer_eq_normalizer_zpowers_of_orderOf_eq_two {F : Type*} [Group F] {z : F}
    (hz : orderOf z = 2) :
    Subgroup.centralizer ({z} : Set F) =
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup F) : Set F) := by
  apply le_antisymm
  · rw [← centralizer_zpowers_eq z]
    exact Subgroup.centralizer_le_normalizer _
  · intro g hg
    rw [Subgroup.mem_normalizer_iff] at hg
    have h1 : g * z * g⁻¹ ∈ Subgroup.zpowers z := (hg z).mp (Subgroup.mem_zpowers z)
    have hne : g * z * g⁻¹ ≠ 1 := by
      intro h
      have : z = 1 := by
        have h2 := congrArg (fun x => g⁻¹ * x * g) h
        simpa [mul_assoc] using h2
      rw [this, orderOf_one] at hz
      exact absurd hz (by norm_num)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h1
    have hmod : z ^ (n % 2) = z ^ n := by
      have := zpow_mod_orderOf z n
      rwa [hz, Nat.cast_ofNat] at this
    have hcase : g * z * g⁻¹ = z := by
      rcases Int.emod_two_eq_zero_or_one n with h0 | h0
      · exfalso
        apply hne
        rw [← hn, ← hmod, h0, zpow_zero]
      · rw [← hn, ← hmod, h0, zpow_one]
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (mul_inv_eq_iff_eq_mul.mp hcase).symm

theorem isTwoLocal_centralizer_of_orderOf_eq_two {F : Type*} [Group F] {z : F}
    (hz : orderOf z = 2) : IsTwoLocal (Subgroup.centralizer ({z} : Set F)) :=
  ⟨Subgroup.zpowers z, (isPGroup_zpowers_of_orderOf_eq_two hz).2,
    (isPGroup_zpowers_of_orderOf_eq_two hz).1,
    centralizer_eq_normalizer_zpowers_of_orderOf_eq_two hz⟩

theorem NoNonsolvableClassical.of_isCharTwoType {F : Type*} [Group F] [Finite F]
    (h : IsCharTwoType F) : NoNonsolvableClassical F :=
  fun _ hz => NoNonsolvableClassicalAt.of_twoConstrained
    (h _ (isTwoLocal_centralizer_of_orderOf_eq_two hz)) hz

theorem NoNonsolvableClassicalAt.of_borelTits_of_isEvenCharacteristic {X : Type*} [Group X]
    [Finite X] {z : X} (hz : orderOf z = 2) (hE : IsEvenCharacteristic X) (S : Sylow 2 X)
    (P : Subgroup X)
    (hNP : Subgroup.normalizer ((Subgroup.zpowers z : Subgroup X) : Set X) ≤ P)
    (hzP : z ∈ pCoreOf 2 P) (hSP : (S : Subgroup X) ≤ P) : NoNonsolvableClassicalAt z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVne : pCoreOf 2 P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hzP
    rw [hzP, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hPH : P ≤ Subgroup.normalizer (pCoreOf 2 P : Set X) := le_normalizer_pCoreOf 2 P
  have hloc : IsPLocal 2 (Subgroup.normalizer (pCoreOf 2 P : Set X)) :=
    ⟨pCoreOf 2 P, hVne, pCoreOf_isPGroup 2 P, rfl⟩
  have hchar := hE _ hloc ⟨S, hSP.trans hPH⟩
  refine NoNonsolvableClassicalAt.of_hasParabolicOvergroup
    ⟨Subgroup.normalizer (pCoreOf 2 P : Set X),
      pCoreOf 2 (Subgroup.normalizer (pCoreOf 2 P : Set X)), ?_, pCoreOf_le 2 _,
      (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 _)).2
        (le_normalizer_pCoreOf 2 _), pCoreOf_isPGroup 2 _, ?_⟩
  · rw [centralizer_eq_normalizer_zpowers_of_orderOf_eq_two hz]
    exact hNP.trans hPH
  · rw [inf_comm]
    exact inf_centralizer_pCoreOf_le_of_isCharacteristicP hchar

theorem noNonsolvableClassical_of_lieModel_of_isEvenCharacteristic {X : Type} [Group X] [Finite X]
    {t : StatedLieTag} {n f : ℕ} (h : LieModel X t n 2 f) (hE : IsEvenCharacteristic X) :
    NoNonsolvableClassical X := by
  intro z hz
  have hp := isPGroup_zpowers_of_orderOf_eq_two hz
  obtain ⟨S, P, -, hN, -, hUP, hS1, hS2⟩ := lieModel_conclusion X t n 2 f h _ hp.2 hp.1
  have hSP : (S : Subgroup X) ≤ P := by
    by_cases ht : t = .Tits
    · exact hS2 ht
    · exact Subgroup.le_normalizer.trans (hS1 ht)
  exact NoNonsolvableClassicalAt.of_borelTits_of_isEvenCharacteristic hz hE S P hN
    (hUP (Subgroup.mem_zpowers z)) hSP hz

end CFSG.ClassicalInvolution
