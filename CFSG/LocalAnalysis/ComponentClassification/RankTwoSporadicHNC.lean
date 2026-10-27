module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHNLocal
public import CFSG.Sporadic.HNOddCore.InvRow1b
public import Certificates.Certificate2083
public import Certificates.Certificate2084
public import Certificates.Certificate2087
public import Certificates.Certificate2091
public import Certificates.Certificate2094
public import Certificates.Certificate2096
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.HN

open Subgroup Equiv CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore
open scoped commutatorElement

@[expose] def sigK : ℕ → Perm (Fin 10)
  | 0 => 1
  | k + 1 => sigK k * swap (Fin.ofNat 10 (2 * k)) (Fin.ofNat 10 (2 * k + 1))

@[expose] def perm1a0 : Perm (Fin 10) where
  toFun := ![5, 2, 6, 0, 1, 9, 3, 8, 7, 4]
  invFun := ![3, 4, 1, 6, 9, 0, 2, 8, 7, 5]
  left_inv := by decide
  right_inv := by decide

@[expose] def perm1b0 : Perm (Fin 10) where
  toFun := ![0, 9, 2, 1, 7, 8, 3, 4, 6, 5]
  invFun := ![0, 3, 2, 6, 7, 9, 8, 4, 5, 1]
  left_inv := by decide
  right_inv := by decide

@[expose] def perm1a1 : Perm (Fin 10) where
  toFun := ![3, 9, 2, 8, 1, 4, 0, 7, 5, 6]
  invFun := ![6, 4, 2, 0, 5, 8, 9, 7, 3, 1]
  left_inv := by decide
  right_inv := by decide

@[expose] def perm1b1 : Perm (Fin 10) where
  toFun := ![8, 2, 3, 0, 6, 5, 4, 9, 1, 7]
  invFun := ![3, 8, 1, 2, 6, 5, 4, 9, 0, 7]
  left_inv := by decide
  right_inv := by decide

@[expose] def perm1a2 : Perm (Fin 10) where
  toFun := ![1, 5, 8, 9, 6, 3, 0, 4, 7, 2]
  invFun := ![6, 0, 9, 5, 7, 1, 4, 8, 2, 3]
  left_inv := by decide
  right_inv := by decide

@[expose] def perm1b2 : Perm (Fin 10) where
  toFun := ![2, 8, 4, 0, 7, 6, 5, 1, 3, 9]
  invFun := ![3, 7, 0, 8, 2, 6, 5, 4, 1, 9]
  left_inv := by decide
  right_inv := by decide

@[expose] def perm2a0 : Perm (Fin 10) where
  toFun := ![9, 2, 7, 4, 1, 5, 6, 3, 0, 8]
  invFun := ![8, 4, 1, 7, 3, 5, 6, 2, 9, 0]
  left_inv := by decide
  right_inv := by decide

@[expose] def perm2b0 : Perm (Fin 10) where
  toFun := ![0, 1, 2, 3, 9, 4, 7, 8, 6, 5]
  invFun := ![0, 1, 2, 3, 5, 9, 8, 6, 7, 4]
  left_inv := by decide
  right_inv := by decide

@[expose] def perm3a0 : Perm (Fin 10) where
  toFun := ![7, 6, 9, 2, 5, 4, 0, 8, 3, 1]
  invFun := ![6, 9, 3, 8, 5, 4, 1, 0, 7, 2]
  left_inv := by decide
  right_inv := by decide

@[expose] def perm3b0 : Perm (Fin 10) where
  toFun := ![0, 3, 4, 5, 2, 7, 1, 6, 9, 8]
  invFun := ![0, 6, 4, 1, 2, 3, 7, 5, 9, 8]
  left_inv := by decide
  right_inv := by decide

@[expose] def perm4a0 : Perm (Fin 10) where
  toFun := ![0, 3, 5, 7, 8, 4, 2, 6, 9, 1]
  invFun := ![0, 9, 6, 1, 5, 2, 7, 3, 4, 8]
  left_inv := by decide
  right_inv := by decide

@[expose] def perm4b0 : Perm (Fin 10) where
  toFun := ![4, 8, 7, 1, 5, 6, 9, 0, 3, 2]
  invFun := ![7, 3, 9, 8, 0, 4, 5, 2, 1, 6]
  left_inv := by decide
  right_inv := by decide

@[expose] def perm5a0 : Perm (Fin 10) where
  toFun := ![2, 8, 1, 7, 5, 4, 6, 0, 9, 3]
  invFun := ![7, 2, 0, 9, 5, 4, 6, 3, 1, 8]
  left_inv := by decide
  right_inv := by decide

@[expose] def perm5b0 : Perm (Fin 10) where
  toFun := ![9, 3, 8, 6, 0, 2, 1, 5, 4, 7]
  invFun := ![4, 6, 5, 1, 8, 7, 3, 9, 2, 0]
  left_inv := by decide
  right_inv := by decide

@[expose] def witK : ℕ → Perm (Fin 10)
  | 1 => ⁅sigK 1, ⁅perm1a0, perm1b0⁆⁆ * ⁅sigK 1, ⁅perm1a1, perm1b1⁆⁆ * ⁅sigK 1, ⁅perm1a2, perm1b2⁆⁆
  | 2 => ⁅sigK 2, ⁅perm2a0, perm2b0⁆⁆
  | 3 => ⁅sigK 3, ⁅perm3a0, perm3b0⁆⁆
  | 4 => ⁅sigK 4, ⁅perm4a0, perm4b0⁆⁆
  | 5 => ⁅sigK 5, ⁅perm5a0, perm5b0⁆⁆
  | _ => 1

theorem four_dvd_orderOf_of_apply {x : Perm (Fin 10)} (m : ℕ) (h2 : ∃ i, (x ^ (m * 2)) i ≠ i)
    (h4 : ∀ i, (x ^ (m * 4)) i = i) : 4 ∣ orderOf x := by
  have h2' : (x ^ m) ^ 2 ≠ 1 := fun h => by
    obtain ⟨i, hi⟩ := h2
    rw [pow_mul, h, Perm.one_apply] at hi
    exact hi rfl
  have h4' : (x ^ m) ^ 4 = 1 := Equiv.ext fun i => by rw [← pow_mul, h4 i, Perm.one_apply]
  rw [← orderOf_eq_four h2' h4']
  exact orderOf_pow_dvd m

theorem four_dvd_orderOf_witK : ∀ k, 1 ≤ k → k ≤ 5 → 4 ∣ orderOf (witK k)
  | 1, _, _ => four_dvd_orderOf_of_apply 1 (by decide +kernel) (by decide +kernel)
  | 2, _, _ => four_dvd_orderOf_of_apply 1 (by decide +kernel) (by decide +kernel)
  | 3, _, _ => four_dvd_orderOf_of_apply 1 (by decide +kernel) (by decide +kernel)
  | 4, _, _ => four_dvd_orderOf_of_apply 3 (by decide +kernel) (by decide +kernel)
  | 5, _, _ => four_dvd_orderOf_of_apply 1 (by decide +kernel) (by decide +kernel)
  | 0, h, _ => absurd h (by norm_num)
  | k + 6, _, h => absurd h (by omega)

theorem witK_mem (k : ℕ) (hk1 : 1 ≤ k) (hk5 : k ≤ 5) :
    witK k ∈ closure {y | ∃ a b : Perm (Fin 10), y = ⁅sigK k, ⁅a, b⁆⁆} := by
  have hm : ∀ a b : Perm (Fin 10), ⁅sigK k, ⁅a, b⁆⁆ ∈
      closure {y | ∃ a b : Perm (Fin 10), y = ⁅sigK k, ⁅a, b⁆⁆} :=
    fun a b => subset_closure ⟨a, b, rfl⟩
  interval_cases k
  · exact mul_mem (mul_mem (hm _ _) (hm _ _)) (hm _ _)
  · exact hm _ _
  · exact hm _ _
  · exact hm _ _
  · exact hm _ _

theorem sigK_sq (k : ℕ) (hk : k ≤ 5) : sigK k ^ 2 = 1 := by
  interval_cases k <;> decide

theorem card_support_sigK (k : ℕ) (hk : k ≤ 5) : (sigK k).support.card = 2 * k := by
  interval_cases k <;> decide

theorem cycleType_sigK (k : ℕ) (hk : k ≤ 5) : (sigK k).cycleType = Multiset.replicate k 2 := by
  have h1 := CFSG.Sporadic.HN.Local.involution_cycleType (sigK_sq k hk)
  have h2 : (sigK k).cycleType.sum = (sigK k).support.card := Perm.sum_cycleType _
  rw [h1, Multiset.sum_replicate, smul_eq_mul, card_support_sigK k hk] at h2
  rw [h1]
  congr 1
  omega

theorem exists_cycleType_of_sq10 {σ : Perm (Fin 10)} (h2 : σ ^ 2 = 1) (h1 : σ ≠ 1) :
    ∃ k, 1 ≤ k ∧ k ≤ 5 ∧ σ.cycleType = Multiset.replicate k 2 := by
  have hord : orderOf σ = 2 := orderOf_eq_prime h2 h1
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (hord ▸ Nat.prime_two)
  rw [hord] at hn
  refine ⟨n + 1, by omega, ?_, hn⟩
  have hs := σ.sum_cycleType_le
  rw [hn, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hs
  omega

theorem exists_conj_sigK {σ : Perm (Fin 10)} (h2 : σ ^ 2 = 1) (h1 : σ ≠ 1) :
    ∃ k, 1 ≤ k ∧ k ≤ 5 ∧ ∃ τ : Perm (Fin 10), τ * sigK k * τ⁻¹ = σ := by
  obtain ⟨k, hk1, hk5, hk⟩ := exists_cycleType_of_sq10 h2 h1
  have hc : IsConj (sigK k) σ := by
    rw [Perm.isConj_iff_cycleType_eq, cycleType_sigK k hk5, hk]
  obtain ⟨τ, hτ⟩ := isConj_iff.mp hc
  exact ⟨k, hk1, hk5, τ, hτ⟩

section Generic

variable {G : Type*} [Group G] {H : Subgroup G}

theorem yWitness_of_s10 [Finite G] {X E : Subgroup ↥H} (hX : X.Normal) {c : ↥H}
    (hc2 : orderOf c = 2) (ι : Perm (Fin 10) →* ↥H) (hι : Function.Injective ι)
    (hιX : ∀ σ, ι σ ∈ X ⊓ centralizer {c})
    (hC : ∀ b ∈ centralizer {c}, ∃ σ, b = ι σ ∨ b = ι σ * c)
    (hE : IsElemAbelian 2 E) (hE4 : 4 ≤ Nat.card E) (hcE : c ∈ E) : YWitness X E := by
  have hc1 : c ≠ 1 := fun h => by rw [h, orderOf_one] at hc2; exact absurd hc2 (by norm_num)
  obtain ⟨b, hbE, hbz⟩ := exists_mem_not_mem_zpowers hc2 hE4
  have hbc : b ∈ centralizer {c} := by
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨b, hbE⟩ ⟨c, hcE⟩)
  obtain ⟨σ, hσb⟩ := hC b hbc
  have hcc : c * c = 1 := by rw [← pow_two, ← hc2, pow_orderOf_eq_one]
  have hσE : ι σ ∈ E := by
    rcases hσb with rfl | rfl
    · exact hbE
    · have e : ι σ = ι σ * c * c := by rw [mul_assoc, hcc, mul_one]
      rw [e]
      exact mul_mem hbE hcE
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [map_one, one_mul] at hσb
    rcases hσb with h | h
    · exact hbz (h ▸ one_mem _)
    · exact hbz (h ▸ mem_zpowers c)
  have hσ2 : σ ^ 2 = 1 := hι (by rw [map_pow, map_one]; exact hE.2 _ hσE)
  obtain ⟨k, hk1, hk5, τ, hτ⟩ := exists_conj_sigK hσ2 hσ1
  have huc : ι τ * c = c * ι τ := mem_centralizer_singleton_iff.mp (mem_inf.mp (hιX τ)).2
  have hcE' : c ∈ E.map (MulAut.conj (ι τ)⁻¹).toMonoidHom := by
    refine ⟨c, hcE, ?_⟩
    show (ι τ)⁻¹ * c * (ι τ)⁻¹⁻¹ = c
    rw [inv_inv, mul_assoc, ← huc, ← mul_assoc, inv_mul_cancel, one_mul]
  have hkE : ι (sigK k) ∈ E.map (MulAut.conj (ι τ)⁻¹).toMonoidHom := by
    refine ⟨ι σ, hσE, ?_⟩
    show (ι τ)⁻¹ * ι σ * (ι τ)⁻¹⁻¹ = ι (sigK k)
    rw [← hτ, map_mul, map_mul, map_inv, inv_inv]
    group
  refine yWitness_of_map_conj hX (ι τ)⁻¹ ?_
  refine yWitness_of_root hcE' hc1 hkE (w := ι (witK k)) ?_ ?_
  · have h := mem_map_of_mem ι (witK_mem k hk1 hk5)
    rw [MonoidHom.map_closure] at h
    refine (closure_le _).mpr ?_ h
    rintro _ ⟨y, ⟨a, b, rfl⟩, rfl⟩
    refine subset_closure ⟨⁅ι a, ι b⁆, ?_, ?_⟩
    · exact commutator_mem_commutator (hιX a) (hιX b)
    · rw [map_commutatorElement, map_commutatorElement]
  · rw [orderOf_injective _ hι]
    exact four_dvd_orderOf_witK k hk1 hk5

end Generic

@[expose] noncomputable def s10Fun
    (x : Perm (Fin 10)) : ↥JH :=
  ((cjcEquiv.symm x : CJ cR) : JH)

theorem s10Fun_one :
    s10Fun 1 = 1 := by
  have h := map_one cjcEquiv.symm
  have h2 := congrArg (fun z : CJ cR => (z : JH)) h
  exact h2

theorem s10Fun_mul
    (x y : Perm (Fin 10)) : s10Fun (x * y) = s10Fun x * s10Fun y := by
  have h := map_mul cjcEquiv.symm x y
  have h2 := congrArg (fun z : CJ cR => (z : JH)) h
  exact h2

@[expose] noncomputable def s10J :
    Perm (Fin 10) →* ↥JH where
  toFun := s10Fun
  map_one' := s10Fun_one
  map_mul' := s10Fun_mul

theorem s10J_apply
    (x : Perm (Fin 10)) : s10J x = ((cjcEquiv.symm x : CJ cR) : JH) := rfl

@[expose] noncomputable def iota10 :=
  jR.comp s10J

theorem iota10_apply
    (x : Perm (Fin 10)) : iota10 x = jR (s10J x) := rfl

theorem iota10_injective :
    Function.Injective iota10 := by
  intro x y h
  rw [iota10_apply, iota10_apply] at h
  have h1 := jR_injective h
  rw [s10J_apply, s10J_apply] at h1
  exact cjcEquiv.symm.injective (Subtype.ext h1)

theorem iota10_mem
    (x : Perm (Fin 10)) : iota10 x ∈ JH.subgroupOf RH ⊓ centralizer {cR} := by
  refine mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_subgroupOf, iota10_apply, jR_val]
    exact (s10J x).2
  · rw [mem_centralizer_singleton_iff, iota10_apply, s10J_apply]
    exact mem_CJ.mp (cjcEquiv.symm x).2

theorem exists_iota10_of_mem_centralizer
    (b : ↥RH) (hb : b ∈ centralizer {cR}) :
    ∃ σ, b = iota10 σ ∨ b = iota10 σ * cR := by
  have e : ∀ g (hg : g ∈ CJ cR), iota10 (cjcEquiv ⟨g, hg⟩) = jR g := fun g hg => by
    rw [iota10_apply, s10J_apply, MulEquiv.symm_apply_apply]
  rcases (mem_centralizer_cR_iff b).1 hb with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
  · exact ⟨_, Or.inl (e g hg).symm⟩
  · exact ⟨_, Or.inr (by rw [e g hg])⟩

theorem normal_X :
    (JH.subgroupOf RH).Normal := ⟨fun n hn g => by
  rw [mem_subgroupOf] at hn ⊢
  simpa using JH_normal_RH g.2 hn⟩

theorem yWitness_of_mem_cR
    {E : Subgroup ↥RH} (hE : IsElemAbelian 2 E) (hE4 : 4 ≤ Nat.card E)
    (hc : cR ∈ E) : YWitness (JH.subgroupOf RH) E :=
  yWitness_of_s10 normal_X orderOf_cR iota10 iota10_injective iota10_mem
    exists_iota10_of_mem_centralizer hE hE4 hc

end CFSG.ComponentClassification.RankTwoSporadic.HN
