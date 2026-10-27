module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem commutator_eq_bot_of_le_centralizer {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hcore : primeComplementCore (G := X) p = ⊥)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hZ : center K = ⊥)
    (huniq : ∀ L : Subgroup X, IsComponentOf L ⊤ → L = K)
    (hQcyc : IsCyclic (CFSG.pCore p X))
    {B T : Subgroup X} (hB : ∀ b ∈ B, b ^ p = 1) (hT : IsPGroup 2 T)
    (hBT : B ≤ normalizer (T : Set X)) (hle : ⁅B, T⁆ ≤ centralizer (K : Set X)) :
    ⁅B, T⁆ = ⊥ := by
  classical
  have hp : p.Prime := Fact.out
  set Q : Subgroup X := CFSG.pCore p X with hQ
  have hQn : Q.Normal := CFSG.pCore_normal
  have hQp : IsPGroup p Q := CFSG.pCore_isPGroup
  have hcommAut : ∀ a b : MulAut Q, a * b = b * a := by
    intro a b
    apply (IsCyclic.mulAutMulEquiv Q).injective
    rw [map_mul, map_mul, mul_comm]
  have hQK : ⁅K, Q⁆ = ⊥ := by
    have : Group.IsNilpotent Q := hQp.isNilpotent
    have : Group.IsSolvable Q := inferInstance
    exact ComponentClassification.LocalComponents.commutes_with_solvable_subnormal K Q hK
      (ComponentClassification.Components.chain_of_mathlib_subnormal hQn.isSubnormal)
  have hQC : Q ≤ centralizer (K : Set X) := by
    rw [Subgroup.le_centralizer_iff]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQK
  have hset : {L : Subgroup X | CFSG.IsComponent L} = {K} := by
    ext L
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hL
      exact huniq L ((CFSG.isComponent_iff_open L).mp hL)
    · rintro rfl
      exact (CFSG.isComponent_iff_open _).mpr hK
  have hlayer : CFSG.layer X = K := by
    simp only [CFSG.layer.eq_sSup]
    rw [hset, sSup_singleton]
  have hF : CFSG.generalizedFitting X = Q ⊔ K := by
    rw [CFSG.generalizedFitting, hlayer, CFSG.Fitting_eq_pcore X p hcore]
  have hodd2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  refine le_bot_iff.mp ?_
  rw [Subgroup.commutator_le]
  intro b hb t ht
  have hbp := hB b hb
  have htb : b * t * b⁻¹ ∈ T := (mem_normalizer_iff.mp (hBT hb) t).mp ht
  set c : X := b * t * b⁻¹ * t⁻¹ with hcdef
  have hcT : c ∈ T := T.mul_mem htb (T.inv_mem ht)
  have hcK : c ∈ centralizer (K : Set X) := hle (Subgroup.commutator_mem_commutator hb ht)
  have hbcb : b * c * b⁻¹ ∈ T := (mem_normalizer_iff.mp (hBT hb) c).mp hcT
  set c' : X := b * c * b⁻¹ * c⁻¹ with hc'def
  have hc'T : c' ∈ T := T.mul_mem hbcb (T.inv_mem hcT)
  have hbcbK : b * c * b⁻¹ ∈ centralizer (K : Set X) := by
    refine mem_centralizer_iff.mpr fun k hk => ?_
    have hk' : b⁻¹ * k * b ∈ K := by
      have := hKn.conj_mem k hk b⁻¹
      simpa using this
    have h1 : c * (b⁻¹ * k * b) = (b⁻¹ * k * b) * c := (mem_centralizer_iff.mp hcK _ hk').symm
    calc k * (b * c * b⁻¹) = b * ((b⁻¹ * k * b) * c) * b⁻¹ := by group
      _ = b * (c * (b⁻¹ * k * b)) * b⁻¹ := by rw [h1]
      _ = b * c * b⁻¹ * k := by group
  have hc'K : c' ∈ centralizer (K : Set X) :=
    (centralizer (K : Set X)).mul_mem hbcbK ((centralizer (K : Set X)).inv_mem hcK)
  have hc'Q : ∀ q ∈ Q, q * c' = c' * q := by
    intro q hq
    let β : MulAut Q := MulAut.conjNormal b
    let γ : MulAut Q := MulAut.conjNormal c
    have hone : (MulAut.conjNormal c' : MulAut Q) = 1 := by
      have : (MulAut.conjNormal c' : MulAut Q) = β * γ * β⁻¹ * γ⁻¹ := by
        rw [hc'def]
        simp only [map_mul, map_inv]
        rfl
      rw [this, hcommAut β γ]
      group
    have h2 := congrArg (fun f : MulAut Q => ((f ⟨q, hq⟩ : Q) : X)) hone
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
    calc q * c' = (c' * q * c'⁻¹) * c' := by rw [h2]
      _ = c' * q := by group
  have hc'F : c' ∈ CFSG.generalizedFitting X := by
    refine CFSG.centralizer_generalizedFitting_le X ?_
    rw [hF]
    refine mem_centralizer_iff.mpr fun x hx => ?_
    have hsup : Q ⊔ K ≤ centralizer ({c'} : Set X) := by
      refine sup_le (fun q hq => mem_centralizer_singleton_iff.mpr (hc'Q q hq)) (fun k hk => ?_)
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hc'K k hk)
    exact mem_centralizer_singleton_iff.mp (hsup hx)
  rw [hF] at hc'F
  have hc'Q' : c' ∈ Q := by
    have hmem : c' ∈ (↑(Q ⊔ K) : Set X) := hc'F
    rw [Subgroup.mul_normal Q K] at hmem
    obtain ⟨q, hq, k, hk, hqk⟩ := Set.mem_mul.1 hmem
    have hkC : k ∈ centralizer (K : Set X) := by
      have : k = q⁻¹ * c' := by rw [← hqk]; group
      rw [this]
      exact (centralizer (K : Set X)).mul_mem ((centralizer (K : Set X)).inv_mem (hQC hq)) hc'K
    have hk1 : k = 1 := by
      have hkZ : (⟨k, hk⟩ : K) ∈ center K := by
        rw [mem_center_iff]
        intro g
        exact Subtype.ext (mem_centralizer_iff.mp hkC g g.2)
      rw [hZ, mem_bot] at hkZ
      exact congrArg Subtype.val hkZ
    rw [← hqk, hk1, mul_one]
    exact hq
  have key : ∀ (x : X) (m : ℕ), x ∈ T → x ^ p ^ m = 1 → x = 1 := by
    intro x m hxT hxm
    obtain ⟨n, hn⟩ := hT ⟨x, hxT⟩
    have hn' : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have h1 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
    have h2 : orderOf x ∣ p ^ m := orderOf_dvd_of_pow_eq_one hxm
    have h3 : orderOf x ∣ Nat.gcd (2 ^ n) (p ^ m) := Nat.dvd_gcd h1 h2
    rw [(hodd2.pow n m).gcd_eq_one] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have hc'1 : c' = 1 := by
    obtain ⟨m, hm⟩ := hQp ⟨c', hc'Q'⟩
    exact key c' m hc'T (by simpa using congrArg Subtype.val hm)
  have hbc : b * c * b⁻¹ = c := by
    have : b * c * b⁻¹ * c⁻¹ = 1 := hc'1
    exact mul_inv_eq_one.mp this
  have hpow : ∀ k : ℕ, b ^ k * t * (b ^ k)⁻¹ = c ^ k * t := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e1 : b * c ^ k * b⁻¹ = c ^ k := by
        have := conj_pow (α := X) (i := k) (a := b) (b := c)
        rw [hbc] at this
        exact this.symm
      calc b ^ (k + 1) * t * (b ^ (k + 1))⁻¹
          = b * (b ^ k * t * (b ^ k)⁻¹) * b⁻¹ := by group
        _ = b * (c ^ k * t) * b⁻¹ := by rw [ih]
        _ = (b * c ^ k * b⁻¹) * (b * t * b⁻¹) := by group
        _ = c ^ k * (c * t) := by rw [e1, show b * t * b⁻¹ = c * t by rw [hcdef]; group]
        _ = c ^ (k + 1) * t := by group
  have hcp : c ^ p = 1 := by
    have h := hpow p
    rw [hbp] at h
    have h' : c ^ p * t = 1 * t := by rw [← h]; group
    exact mul_right_cancel h'
  have hc1 : c = 1 := by simpa using key c 1 hcT (by simpa using hcp)
  rw [mem_bot, commutatorElement_def]
  exact hc1

end CFSG.LocalAnalysis.RankThreeTheoremC
