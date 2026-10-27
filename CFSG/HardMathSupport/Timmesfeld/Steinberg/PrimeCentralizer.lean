module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.FiveCharE8

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Steinberg

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

set_option linter.unusedSectionVars false

theorem exists_pow_eq_self_of_prime {G : Type*} [Group G] {ℓ : ℕ} (hℓ : ℓ.Prime) {d : G}
    (hd : d ^ ℓ = 1) {t : ℕ} (ht : ¬ ℓ ∣ t) : ∃ u : ℕ, (d ^ t) ^ u = d :=
  exists_pow_eq_self_of_coprime
    (Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hd)
      ((Nat.Prime.coprime_iff_not_dvd hℓ).2 ht).symm)

section Lang

variable {τ : Tag} {k : Type} [Field k]
variable (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]

theorem toral_centralizer_Lang_of_prime {ℓ : ℕ} (hℓ : ℓ.Prime) (hpℓ : p ≠ ℓ)
    (a : Fin τ.rank → kˣ) (haℓ : ∀ i, a i ^ ℓ = 1)
    (hW : rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a)
    (e : ℕ) (he : 1 ≤ e) {Q : ModGL τ k} (hQG : Q ∈ adjointGroup τ k) {s : ℕ} (hs : ¬ ℓ ∣ s)
    (hQ : Q * rootDiagUnit τ a * Q⁻¹ = rootDiagUnit τ a ^ s) :
    ∀ c ∈ toralCentralizer τ k a, ∃ z ∈ toralCentralizer τ k a,
      z⁻¹ * frobTwistGL τ k p e Q z = c := by
  obtain ⟨-, hZ⟩ := toral_centralizer_connected_of_stabilizer_le a hW
  have hdℓ : rootDiagUnit τ a ^ ℓ = 1 := by
    have h1 : a ^ ℓ = 1 := funext fun i => by simpa using haℓ i
    have := (rootDiagUnitHom τ k).map_pow a ℓ
    rw [h1, map_one] at this
    exact this.symm
  have hQ' : ∀ g ∈ toralCentralizer τ k a, frobTwistGL τ k p e Q g ∈ toralCentralizer τ k a := by
    intro g hg
    obtain ⟨hgG, hgc⟩ := mem_toralCentralizer.1 hg
    refine mem_toralCentralizer.2 ⟨?_, ?_⟩
    · rw [frobTwistGL_apply]
      exact mul_mem (mul_mem hQG (entrywiseFrobGL_mem p e hgG)) (inv_mem hQG)
    · set d := rootDiagUnit τ a with hd
      have hcg : Commute g d := by
        have := hgc
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this.symm
      have h1 : Commute (entrywiseFrobGL τ k p e g) (d ^ p ^ e) := by
        rw [← entrywiseFrobGL_rootDiagUnit_pow p e a]
        exact hcg.map _
      have h2 : Commute (Q * entrywiseFrobGL τ k p e g * Q⁻¹) (Q * d ^ p ^ e * Q⁻¹) :=
        h1.map (MulAut.conj Q).toMonoidHom
      have h3 : Q * d ^ p ^ e * Q⁻¹ = d ^ (s * p ^ e) := by
        rw [← conj_pow, hQ, ← pow_mul]
      rw [h3] at h2
      have hnd : ¬ ℓ ∣ s * p ^ e := by
        intro h
        rcases (Nat.Prime.dvd_mul hℓ).1 h with h | h
        · exact hs h
        · exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ (Fact.out)).1 (hℓ.dvd_of_dvd_pow h)).symm
      obtain ⟨u, hu⟩ := exists_pow_eq_self_of_prime hℓ hdℓ hnd
      have h4 : Commute (Q * entrywiseFrobGL τ k p e g * Q⁻¹) d := by
        rw [← hu]
        exact h2.pow_right u
      rw [frobTwistGL_apply, mul_inv_eq_iff_eq_mul]
      exact h4.symm.eq
  obtain ⟨-, -, -, hlang⟩ := exists_frobTwist_restriction p hZ he Q hQ'
  exact hlang

end Lang

section E8Five

theorem toralCentralizer_eq_toralRootGroup_E8_five (K : Type) [Field K]
    (a : Fin Tag.E8.rank → Kˣ) (h5 : ∀ i, a i ^ 5 = 1) :
    toralCentralizer Tag.E8 K a = toralRootGroup Tag.E8 K a :=
  toralCentralizer_eq_toralRootGroup_of_stabilizer_le _ K a
    (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_five a h5).le

theorem toral_centralizer_Lang_E8_five (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] [IsAlgClosed k] (hp5 : p ≠ 5) (a : Fin Tag.E8.rank → kˣ)
    (h5 : ∀ i, a i ^ 5 = 1) (e : ℕ) (he : 1 ≤ e) {Q : ModGL Tag.E8 k}
    (hQG : Q ∈ adjointGroup Tag.E8 k) {s : ℕ} (hs : ¬ 5 ∣ s)
    (hQ : Q * rootDiagUnit Tag.E8 a * Q⁻¹ = rootDiagUnit Tag.E8 a ^ s) :
    ∀ c ∈ toralCentralizer Tag.E8 k a, ∃ z ∈ toralCentralizer Tag.E8 k a,
      z⁻¹ * frobTwistGL Tag.E8 k p e Q z = c :=
  toral_centralizer_Lang_of_prime p Nat.prime_five hp5 a h5
    (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_five a h5).le e he hQG hs hQ

end E8Five

end CFSG.HardMathSupport.Timmesfeld.Steinberg
