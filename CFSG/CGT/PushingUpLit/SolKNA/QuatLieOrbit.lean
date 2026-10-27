module

import CFSG.ClassicalInvolution.Basic
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.ComponentClassification.AschbacherTheorem3 (IsQuaternionTwoGroup)

section MovedPoints

variable {P : Type*} [Group P]

theorem mul_mul_inv_eq_of_unique_involution {u : P} (hu2 : orderOf u = 2)
    (hH : ∀ H : Subgroup P, H ≠ ⊥ → u ∈ H) (p : P) : p * u * p⁻¹ = u := by
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu2
    omega
  have hu2' : u ^ 2 = 1 := by rw [← hu2]; exact pow_orderOf_eq_one u
  have hv2 : (p * u * p⁻¹) ^ 2 = 1 := by rw [conj_pow, hu2']; group
  have hv1 : p * u * p⁻¹ ≠ 1 := by
    intro h
    apply hu1
    calc u = p⁻¹ * (p * u * p⁻¹) * p := by group
      _ = 1 := by rw [h]; group
  have hvo : orderOf (p * u * p⁻¹) = 2 := orderOf_eq_prime hv2 hv1
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp
    (hH (Subgroup.zpowers (p * u * p⁻¹)) (by rwa [Ne, Subgroup.zpowers_eq_bot]))
  have hj' : (p * u * p⁻¹) ^ (j % 2) = u := by
    have := zpow_mod_orderOf (p * u * p⁻¹) j
    rw [hvo] at this
    simpa using this.trans hj
  rcases Int.emod_two_eq_zero_or_one j with h | h
  · rw [h, zpow_zero] at hj'
    exact absurd hj'.symm hu1
  · rw [h, zpow_one] at hj'
    exact hj'

theorem card_dvd_card_moved {u : P} (hu2 : orderOf u = 2)
    (hH : ∀ H : Subgroup P, H ≠ ⊥ → u ∈ H) {Ω : Type*} [Finite Ω]
    (φ : P →* Equiv.Perm Ω) (hφ : Function.Injective φ) :
    Nat.card P ∣ Nat.card {ω : Ω // φ u ω ≠ ω} := by
  classical
  have hcomm : ∀ (p : P) (ω : Ω), φ u (φ p ω) = φ p (φ u ω) := fun p ω => by
    have h := mul_mul_inv_eq_of_unique_involution hu2 hH p
    have h' : p * u = u * p := by
      calc p * u = p * u * p⁻¹ * p := by group
        _ = u * p := by rw [h]
    rw [← Equiv.Perm.mul_apply, ← map_mul, ← h', map_mul, Equiv.Perm.mul_apply]
  have hinv : ∀ (p : P) (ω : Ω), φ u (φ p ω) ≠ φ p ω ↔ φ u ω ≠ ω := fun p ω => by
    rw [hcomm p ω]
    exact (φ p).injective.ne_iff
  have hfix : ∀ (g : P) (ω : Ω), g ≠ 1 → φ g ω = ω → φ u ω = ω := by
    intro g ω hg1 hgω
    have hne : Subgroup.zpowers g ≠ ⊥ := by rwa [Ne, Subgroup.zpowers_eq_bot]
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hH _ hne)
    rw [← hj, map_zpow]
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hgω j
  let ψ : P →* Equiv.Perm {ω : Ω // φ u ω ≠ ω} :=
    { toFun := fun p => Equiv.Perm.subtypePerm (φ p) (hinv p)
      map_one' := by
        ext ω
        simp
      map_mul' := fun p q => by
        ext ω
        show φ (p * q) ω.1 = φ p (φ q ω.1)
        rw [map_mul, Equiv.Perm.mul_apply] }
  let _ : MulAction P {ω : Ω // φ u ω ≠ ω} := MulAction.compHom _ ψ
  have hstab : ∀ ω : {ω : Ω // φ u ω ≠ ω}, MulAction.stabilizer P ω = ⊥ := by
    intro ω
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have hg' : φ g ω.1 = ω.1 := congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hg)
    by_contra hg1
    exact ω.2 (hfix g ω.1 hg1 hg')
  have : Finite P := Finite.of_injective φ hφ
  let Q := Quotient (MulAction.orbitRel P {ω : Ω // φ u ω ≠ ω})
  have : Fintype Q := Fintype.ofFinite Q
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbitsQuotientStabilizer P
    {ω : Ω // φ u ω ≠ ω}), Nat.card_sigma]
  have hterm : ∀ q : Q, Nat.card (P ⧸ MulAction.stabilizer P q.out) = Nat.card P := fun q => by
    rw [hstab q.out]
    exact Subgroup.index_bot
  exact Finset.dvd_sum fun q _ => dvd_of_eq (hterm q).symm

end MovedPoints

theorem no_big_quaternion_of_moved {G : Type} [Group G] {Ω : Type} [Finite Ω]
    (ψ : G →* Equiv.Perm Ω) (hψ : Function.Injective ψ) (m : ℕ) (hm : ¬ 16 ∣ m)
    (h : ∀ g : G, orderOf g = 2 → Nat.card {ω // ψ g ω ≠ ω} = m) {P : Subgroup G}
    (hP : IsQuaternionTwoGroup P) : Nonempty (↥P ≃* QuaternionGroup 2) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hP
  obtain ⟨u, hu2, -, hH⟩ :=
    CFSG.ClassicalInvolution.exists_unique_involution_of_mulEquiv_quaternionGroup e
  have hdvd := card_dvd_card_moved hu2 hH (ψ.comp P.subtype) (hψ.comp P.subtype_injective)
  have hcard : Nat.card P = 2 ^ n := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have h4 : (4 : ℕ) * 2 ^ (n - 2) = 2 ^ n := by
      calc (4 : ℕ) * 2 ^ (n - 2) = 2 ^ 2 * 2 ^ (n - 2) := by norm_num
        _ = 2 ^ (2 + (n - 2)) := (pow_add 2 2 (n - 2)).symm
        _ = 2 ^ n := by congr 1; omega
    exact h4
  have hum : Nat.card {ω // (ψ.comp P.subtype) u ω ≠ ω} = m :=
    h (u : G) (by rw [Subgroup.orderOf_coe]; exact hu2)
  rw [hum, hcard] at hdvd
  have hn3 : n = 3 := by
    by_contra hne
    apply hm
    have h4 : 2 ^ 4 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    exact dvd_trans (by simpa using h4) hdvd
  subst hn3
  exact ⟨e⟩

end CFSG.CGT.PushingUpLit.SolKNA
