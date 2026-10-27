module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55CentExt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgAct
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.ABGLocalTools
open scoped commutatorElement

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem not_sylow_two_le_center {K : Type*} [Group K] [Finite K] (hK : IsQuasisimple K)
    {S : Subgroup K} (hS : IsSylowOf 2 S ⊤) (hSZ : S ≤ center K) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := (isSylowOf_iff).1 hS
  have hodd : ¬ 2 ∣ S.index := by
    have := h1.2.2
    rwa [Subgroup.relIndex_top_right] at this
  have hdvd : (center K).index ∣ S.index := Subgroup.index_dvd_of_le hSZ
  have hodd' : ¬ 2 ∣ (center K).index := fun h => hodd (h.trans hdvd)
  have hcard : Odd (Nat.card (K ⧸ center K)) := by
    have : Nat.card (K ⧸ center K) = (center K).index := rfl
    rw [this]
    exact Nat.odd_iff.mpr (by omega)
  have hsol : Group.IsSolvable (K ⧸ center K) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hcard
  have := hK.2.1
  obtain ⟨a, b, hab⟩ := hK.2.2
  exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsol) a b)

theorem mem_normalizer_component (T : Sylow 2 Γ) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P : Subgroup Γ} (hP : IsPGroup p ↥P) (hTP : (T : Subgroup Γ) ≤ normalizer (P : Set Γ))
    {a : Γ} (ha : a ∈ P) {K : Subgroup Γ} (hK : IsComponent K) :
    a ∈ normalizer (K : Set Γ) := by
  by_contra hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K1 : Subgroup Γ := K.map (MulAut.conj a).toMonoidHom with hK1
  have hK1c : IsComponent K1 := LocalCores.isComponent_map_mulEquiv (MulAut.conj a) hK
  have hmem1 : ∀ x ∈ K, a * x * a⁻¹ ∈ K1 := fun x hx => ⟨x, hx, rfl⟩
  have hne : K ≠ K1 := by
    intro heq
    apply hn
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [heq]
      exact hmem1 x hx
    · intro hx
      rw [heq] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := by
        have h2 : a * y * a⁻¹ = a * x * a⁻¹ := hyx
        simpa using h2
      rw [← this]
      exact hy
  have hcomm : ∀ x ∈ K, ∀ y ∈ K1, x * y = y * x := by
    intro x hx y hy
    rcases LocalCores.distinct_components_commute hK hK1c with h | h
    · exact absurd h hne
    · have : ⁅x, y⁆ ∈ (⊥ : Subgroup Γ) := h ▸ Subgroup.commutator_mem_commutator hx hy
      exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp this)
  have hTtop : IsSylowOf 2 (T : Subgroup Γ) ⊤ := by
    rw [isSylowOf_iff]
    exact ⟨le_top, T.isPGroup', by rw [Subgroup.relIndex_top_right]; exact T.not_dvd_index⟩
  have hTK : IsSylowOf 2 ((T : Subgroup Γ) ⊓ K) K := YCfg.isSylowOf_inf_isSubnormal_top hTtop hK.2
  have hcen : ((T : Subgroup Γ) ⊓ K).subgroupOf K ≤ center ↥K := by
    intro t ht
    have htT : (t : Γ) ∈ (T : Subgroup Γ) := (Subgroup.mem_inf.mp ht).1
    have htK : (t : Γ) ∈ K := t.2
    have hca : ((t : Γ) * a * (t : Γ)⁻¹) ∈ P := (mem_normalizer_iff.mp (hTP htT) a).mp ha
    have hcP : (t : Γ) * (a * (t : Γ) * a⁻¹)⁻¹ ∈ P := by
      have : (t : Γ) * (a * (t : Γ) * a⁻¹)⁻¹ = (t : Γ) * a * (t : Γ)⁻¹ * a⁻¹ := by group
      rw [this]
      exact P.mul_mem hca (P.inv_mem ha)
    obtain ⟨k, hk⟩ := T.isPGroup' ⟨(t : Γ), htT⟩
    have hk' : (t : Γ) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨m, hm⟩ := hP ⟨_, hcP⟩
    have hm' : ((t : Γ) * (a * (t : Γ) * a⁻¹)⁻¹) ^ p ^ m = 1 := by
      simpa using congrArg Subtype.val hm
    have h1k : (a * (t : Γ) * a⁻¹) ^ 2 ^ k = 1 := by rw [conj_pow, hk']; group
    have hcm0 : Commute (t : Γ) (a * (t : Γ) * a⁻¹) := hcomm _ htK _ (hmem1 _ htK)
    have hcm : Commute (t : Γ) (a * (t : Γ) * a⁻¹)⁻¹ := hcm0.inv_right
    have hck : ((t : Γ) * (a * (t : Γ) * a⁻¹)⁻¹) ^ 2 ^ k = 1 := by
      rw [hcm.mul_pow, hk', inv_pow, h1k, inv_one, one_mul]
    have hcop : Nat.Coprime 2 (p ^ m) :=
      Nat.Coprime.pow_right m ((Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).mpr
        (Ne.symm hp2))
    have hc1 := eq_one_of_pow_pow_of_pow hcop hck hm'
    have htt : (t : Γ) = a * (t : Γ) * a⁻¹ := mul_inv_eq_one.mp hc1
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    have htK1 : (t : Γ) ∈ K1 := by rw [htt]; exact hmem1 _ htK
    exact hcomm (x : Γ) x.2 (t : Γ) htK1
  have hS' : IsSylowOf 2 (((T : Subgroup Γ) ⊓ K).subgroupOf K) ⊤ := by
    rw [← isSylowOf_map_subtype_iff K, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left inf_le_right, Subgroup.map_top, Subgroup.range_subtype]
    exact hTK
  exact not_sylow_two_le_center hK.1 hS' hcen

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
