module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Ineq

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem exists_zpow_of_normalizes {p : ℕ} [hp : Fact p.Prime] {A : Subgroup G}
    (hA : Nat.card A = p) {x : G} (hx : A.map (MulAut.conj x).toMonoidHom = A) :
    ∃ m : ℤ, ∀ a ∈ A, x * a * x⁻¹ = a ^ m := by
  haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; exact hp.out.ne_zero)
  haveI : IsCyclic A := isCyclic_of_prime_card hA
  have hmem : ∀ a ∈ A, x * a * x⁻¹ ∈ A := fun a ha => by
    rw [← hx]; exact ⟨a, ha, rfl⟩
  let σ : A →* A :=
    { toFun := fun a => ⟨x * a * x⁻¹, hmem a a.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic σ
  exact ⟨m, fun a ha => by simpa [σ] using congrArg Subtype.val (hm ⟨a, ha⟩)⟩

theorem map_conj_inv_eq {A : Subgroup G} {x : G} (hx : A.map (MulAut.conj x).toMonoidHom = A) :
    A.map (MulAut.conj x⁻¹).toMonoidHom = A := by
  conv_lhs => rw [← hx]
  rw [Subgroup.map_map]
  convert Subgroup.map_id A using 2
  ext a
  simp [mul_assoc]

theorem commutatorElement_centralizes_of_normalizes_line {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : Nat.card A = p) {x y : G}
    (hx : A.map (MulAut.conj x).toMonoidHom = A) (hy : A.map (MulAut.conj y).toMonoidHom = A) :
    ∀ a ∈ A, ⁅x, y⁆ * a * ⁅x, y⁆⁻¹ = a := by
  obtain ⟨m, hm⟩ := exists_zpow_of_normalizes hA hx
  obtain ⟨n, hn⟩ := exists_zpow_of_normalizes hA hy
  obtain ⟨m', hm'⟩ := exists_zpow_of_normalizes hA (map_conj_inv_eq hx)
  obtain ⟨n', hn'⟩ := exists_zpow_of_normalizes hA (map_conj_inv_eq hy)
  have hmm : ∀ b ∈ A, b ^ (m' * m) = b := fun b hb => by
    have h1 : x * b ^ m' * x⁻¹ = (b ^ m') ^ m := hm (b ^ m') (A.zpow_mem hb m')
    have h2 : b ^ m' = x⁻¹ * b * x := by simpa using (hm' b hb).symm
    rw [zpow_mul, ← h1, h2]; group
  have hnn : ∀ b ∈ A, b ^ (n' * n) = b := fun b hb => by
    have h1 : y * b ^ n' * y⁻¹ = (b ^ n') ^ n := hn (b ^ n') (A.zpow_mem hb n')
    have h2 : b ^ n' = y⁻¹ * b * y := by simpa using (hn' b hb).symm
    rw [zpow_mul, ← h1, h2]; group
  intro a ha
  have e1 : y⁻¹ * a * y = a ^ n' := by simpa using hn' a ha
  have e2 : x⁻¹ * a ^ n' * x = (a ^ n') ^ m' := by
    simpa using hm' (a ^ n') (A.zpow_mem ha n')
  have e3 : y * (a ^ n') ^ m' * y⁻¹ = ((a ^ n') ^ m') ^ n :=
    hn _ (A.zpow_mem (A.zpow_mem ha n') m')
  have e4 : x * ((a ^ n') ^ m') ^ n * x⁻¹ = (((a ^ n') ^ m') ^ n) ^ m :=
    hm _ (A.zpow_mem (A.zpow_mem (A.zpow_mem ha n') m') n)
  have hc : ⁅x, y⁆ * a * ⁅x, y⁆⁻¹ = x * (y * (x⁻¹ * (y⁻¹ * a * y) * x) * y⁻¹) * x⁻¹ := by
    rw [commutatorElement_def]; group
  rw [hc, e1, e2, e3, e4, ← zpow_mul, ← zpow_mul, ← zpow_mul]
  calc a ^ (n' * (m' * (n * m))) = (a ^ (n' * n)) ^ (m' * m) := by rw [← zpow_mul]; ring_nf
    _ = a ^ (m' * m) := by rw [hnn a ha]
    _ = a := hmm a ha

theorem exists_not_normalizes_of_commutator_fpf {p : ℕ} [hp : Fact p.Prime] {E A : Subgroup G}
    (hAE : A ≤ E) (hA : Nat.card A = p) {c₁ c₂ : G}
    (hfpf : ∀ x ∈ E, ⁅c₁, c₂⁆ * x * ⁅c₁, c₂⁆⁻¹ = x → x = 1) :
    A.map (MulAut.conj c₁).toMonoidHom ≠ A ∨ A.map (MulAut.conj c₂).toMonoidHom ≠ A := by
  by_contra h
  push Not at h
  have hcen := commutatorElement_centralizes_of_normalizes_line hA h.1 h.2
  have hbot : A = ⊥ := (Subgroup.eq_bot_iff_forall A).2 fun a ha => hfpf a (hAE ha) (hcen a ha)
  rw [hbot, Subgroup.card_bot] at hA
  exact hp.out.one_lt.ne hA

theorem exists_not_normalizes_of_doubleCommutator_fpf {p : ℕ} [Fact p.Prime] {E A : Subgroup G}
    (hAE : A ≤ E) (hA : Nat.card A = p) {c₁ c₂ c₃ c₄ : G}
    (hfpf : ∀ x ∈ E, ⁅⁅c₁, c₂⁆, ⁅c₃, c₄⁆⁆ * x * ⁅⁅c₁, c₂⁆, ⁅c₃, c₄⁆⁆⁻¹ = x → x = 1) :
    A.map (MulAut.conj ⁅c₁, c₂⁆).toMonoidHom ≠ A ∨ A.map (MulAut.conj ⁅c₃, c₄⁆).toMonoidHom ≠ A :=
  exists_not_normalizes_of_commutator_fpf hAE hA hfpf

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
