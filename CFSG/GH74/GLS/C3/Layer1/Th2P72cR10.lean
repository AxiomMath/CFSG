module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GH74.GLS.C3.Layer1.Th2L83GenCore

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS
open scoped commutatorElement

theorem exists_fixedPoint_of_involutive_of_odd {S : Type*} [Finite S] (τ : S → S)
    (hτ : ∀ s, τ (τ s) = s) (hodd : ¬ 2 ∣ Nat.card S) : ∃ s, τ s = s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let σ : Equiv.Perm S := ⟨τ, τ, hτ, hτ⟩
  have hσ : σ * σ = 1 := by ext s; exact hτ s
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  have hF : IsPGroup 2 ↥(Subgroup.zpowers σ) := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨g, hg⟩ := g
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    have h2 : σ ^ (2 : ℤ) = 1 := by rw [zpow_two, hσ]
    calc (σ ^ n) ^ 2 = σ ^ (n * 2) := by rw [← zpow_natCast, ← zpow_mul]; norm_num
      _ = (σ ^ (2 : ℤ)) ^ n := by rw [mul_comm, zpow_mul]
      _ = 1 := by rw [h2, one_zpow]
  obtain ⟨s, hs⟩ := hF.nonempty_fixed_point_of_prime_not_dvd_card S hodd
  refine ⟨s, ?_⟩
  have := hs ⟨σ, Subgroup.mem_zpowers σ⟩
  exact this


theorem exists_fixed_inv_mem_coset {X : Type} [Group X] [Finite X] {O V : Subgroup X}
    (hOodd : ¬ 2 ∣ Nat.card O) (hV : IsPGroup 2 ↥V)
    (hVO : ∀ v ∈ V, ∀ o ∈ O, v * o * v⁻¹ ∈ O) {b : X} (hb2 : b * b = 1)
    (hbN : b ∈ normalizer (O : Set X)) (hbV : ∀ v ∈ V, b * v = v * b) {k : X}
    (hkN : k ∈ normalizer (O : Set X)) (hk : ∀ v ∈ V, k⁻¹ * (v * k * v⁻¹) ∈ O)
    (hkb : k * (b * k * b⁻¹) ∈ O) :
    ∃ o ∈ O, (∀ v ∈ V, v * (k * o) * v⁻¹ = k * o) ∧ b * (k * o) * b⁻¹ = (k * o)⁻¹ := by
  classical
  obtain ⟨o₀, ho₀, hfix₀⟩ := Th2.L83.exists_fixed_mem_coset hOodd hV hVO hk
  set g₀ : X := k * o₀ with hg₀
  let D : Subgroup X := O ⊓ centralizer (V : Set X)
  have hbO : ∀ o ∈ O, b * o * b⁻¹ ∈ O := fun o ho => (Subgroup.mem_normalizer_iff.1 hbN o).1 ho
  have hkO' : ∀ o ∈ O, k⁻¹ * o * k ∈ O := by
    intro o ho
    have := (Subgroup.mem_normalizer_iff.1 ((normalizer (O : Set X)).inv_mem hkN) o).1 ho
    simpa using this
  let S : Type _ := {g : X // k⁻¹ * g ∈ O ∧ ∀ v ∈ V, v * g * v⁻¹ = g}
  have hSD : Nat.card S = Nat.card D := by
    refine Nat.card_congr
      { toFun := fun g => ⟨g₀⁻¹ * g.1, ?_, ?_⟩
        invFun := fun c => ⟨g₀ * c.1, ?_, ?_⟩
        left_inv := fun g => Subtype.ext (by simp)
        right_inv := fun c => Subtype.ext (by simp) }
    · have h1 : g₀⁻¹ * g.1 = o₀⁻¹ * (k⁻¹ * g.1) := by simp [hg₀, mul_assoc]
      rw [h1]
      exact O.mul_mem (O.inv_mem ho₀) g.2.1
    · show g₀⁻¹ * g.1 ∈ centralizer (V : Set X)
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h1 := g.2.2 v hv
      have h2 := hfix₀ v hv
      have h3 : v * (g₀⁻¹ * g.1) * v⁻¹ = g₀⁻¹ * g.1 := by
        have : v * (g₀⁻¹ * g.1) * v⁻¹ = (v * g₀ * v⁻¹)⁻¹ * (v * g.1 * v⁻¹) := by group
        rw [this, show v * g₀ * v⁻¹ = g₀ from h2, h1]
      exact mul_inv_eq_iff_eq_mul.1 h3
    · have h1 : k⁻¹ * (g₀ * c.1) = o₀ * c.1 := by simp [hg₀, mul_assoc]
      rw [h1]
      exact O.mul_mem ho₀ c.2.1
    · intro v hv
      have h1 := hfix₀ v hv
      have h2 : v * c.1 = c.1 * v := Subgroup.mem_centralizer_iff.1 c.2.2 v hv
      have : v * (g₀ * c.1) * v⁻¹ = (v * g₀ * v⁻¹) * (v * c.1 * v⁻¹) := by group
      rw [this, show v * g₀ * v⁻¹ = g₀ from h1, h2]
      group
  have hSodd : ¬ 2 ∣ Nat.card S := by
    rw [hSD]
    intro h
    exact hOodd (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hτS : ∀ g : S, k⁻¹ * (b * g.1⁻¹ * b⁻¹) ∈ O ∧ ∀ v ∈ V, v * (b * g.1⁻¹ * b⁻¹) * v⁻¹ = b * g.1⁻¹ * b⁻¹ := by
    intro g
    refine ⟨?_, ?_⟩
    · have hid : b * g.1⁻¹ * b⁻¹ =
          (b * (k⁻¹ * g.1)⁻¹ * b⁻¹) * (k * (b * k * b⁻¹))⁻¹ * k := by group
      rw [hid]
      have h1 : (b * (k⁻¹ * g.1)⁻¹ * b⁻¹) * (k * (b * k * b⁻¹))⁻¹ ∈ O :=
        O.mul_mem (hbO _ (O.inv_mem g.2.1)) (O.inv_mem hkb)
      have := hkO' _ h1
      simpa [mul_assoc] using this
    · intro v hv
      have h1 := g.2.2 v hv
      have h2 : v * g.1⁻¹ * v⁻¹ = g.1⁻¹ := by
        have : v * g.1⁻¹ * v⁻¹ = (v * g.1 * v⁻¹)⁻¹ := by group
        rw [this, h1]
      have h3 : v * b = b * v := (hbV v hv).symm
      calc v * (b * g.1⁻¹ * b⁻¹) * v⁻¹ = (v * b) * g.1⁻¹ * (b⁻¹ * v⁻¹) := by group
        _ = (b * v) * g.1⁻¹ * (b⁻¹ * v⁻¹) := by rw [h3]
        _ = b * (v * g.1⁻¹ * v⁻¹) * b⁻¹ := by
            have hb' : b⁻¹ * v⁻¹ = v⁻¹ * b⁻¹ := by
              rw [← mul_inv_rev, ← mul_inv_rev, h3]
            rw [hb']; group
        _ = b * g.1⁻¹ * b⁻¹ := by rw [h2]
  let τ : S → S := fun g => ⟨b * g.1⁻¹ * b⁻¹, hτS g⟩
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hττ : ∀ g, τ (τ g) = g := by
    intro g
    apply Subtype.ext
    simp only [τ]
    rw [hbinv]
    group
  obtain ⟨g, hg⟩ := exists_fixedPoint_of_involutive_of_odd τ hττ hSodd
  have hg' : b * g.1⁻¹ * b⁻¹ = g.1 := congrArg Subtype.val hg
  refine ⟨k⁻¹ * g.1, g.2.1, ?_, ?_⟩
  · intro v hv
    simpa using g.2.2 v hv
  · have : b * g.1 * b⁻¹ = g.1⁻¹ := by
      have := congrArg (fun z => z⁻¹) hg'
      simpa [mul_assoc] using this
    simpa [mul_assoc] using this


theorem exists_pow_pPart {X : Type*} [Group X] (g : X) (hn : orderOf g ≠ 0) {p : ℕ} (hp : p.Prime) :
    ∃ n : ℕ, n % p = 1 % p ∧ ∃ k : ℕ, (g ^ n) ^ (p ^ k) = 1 := by
  obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.one_lt.ne'
  have hcop : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm
  obtain ⟨m', -, hm'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  refine ⟨m * m', ?_, e, ?_⟩
  · rw [hm', Nat.mod_eq_of_lt hp.one_lt]
  · rw [← pow_mul, show m * m' * p ^ e = orderOf g * m' by rw [he]; ring, pow_mul,
      pow_orderOf_eq_one, one_pow]

end CFSG.GH74.GLS.Th2.Obs
