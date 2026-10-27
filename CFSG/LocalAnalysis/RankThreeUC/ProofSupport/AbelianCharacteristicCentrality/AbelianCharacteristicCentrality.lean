module

public import CFSG.LocalAnalysis.RankThreeUC.FaithfulPrimeFieldKGroupModule
public import CFSG.GroupTheory.CoprimeActionSupport.FixedFreeNormalizerScalarExtension
public import CFSG.LocalAnalysis.RankThreeUC.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.AbelianCharacteristicCentrality

open CFSG.LocalAnalysis.RankThreeUC

theorem nonabelian {G : Type} [Group G] [Finite G] {p : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ρ : Representation (ZMod p) G V}
    (hS : FaithfulPrimeFieldKGroupModule G p V ρ) {q r : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hqp : q ≠ p) (hrp : r ≠ p) (hqr : q ≠ r)
    (D : Subgroup G) (hD : Nat.card D = r)
    (hCV : (⨅ d ∈ D, LinearMap.ker (ρ d - LinearMap.id)) = (⊥ : Submodule (ZMod p) V))
    (Q : Subgroup G) (hQD : ⁅D, Q⁆ = Q) (hQ1 : Q ≠ ⊥) (hQq : IsPGroup q Q) :
    ¬ IsMulCommutative Q := by
  have card_ne_zero {G : Type} [Group G] [Finite G] {p q : ℕ} (hp : p.Prime)
      (hq : q.Prime) (hqp : q ≠ p) (U : Subgroup G) (hU : IsPGroup q U) :
      ((Nat.card U : ℕ) : ZMod p) ≠ 0 := by
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨n, hn⟩ := hU.exists_card_eq
    rw [hn, Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h)
    exact hqp this.symm
  have normalizes {G : Type} [Group G] (D Q : Subgroup G) (hQD : ⁅D, Q⁆ = Q) :
      D ≤ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right, hQD]
  have normalizes_char {G : Type} [Group G] (D Q U : Subgroup G) (hQD : ⁅D, Q⁆ = Q)
      (hUQ : U ≤ Q) (hchar : (U.subgroupOf Q).Characteristic) :
      D ≤ Subgroup.normalizer (U : Set G) := by
    intro d hd
    have hdQ : ∀ x ∈ Q, d * x * d⁻¹ ∈ Q := by
      intro x hx
      have := normalizes D Q hQD hd
      exact (Subgroup.mem_normalizer_iff.mp this x).mp hx
    have hdQ' : ∀ x ∈ Q, d⁻¹ * x * d ∈ Q := by
      intro x hx
      have := normalizes D Q hQD (D.inv_mem hd)
      simpa using (Subgroup.mem_normalizer_iff.mp this x).mp hx
    let φ : Q ≃* Q :=
      { toFun := fun x => ⟨d * x * d⁻¹, hdQ x x.2⟩
        invFun := fun x => ⟨d⁻¹ * x * d, hdQ' x x.2⟩
        left_inv := fun x => by ext; simp [mul_assoc]
        right_inv := fun x => by ext; simp [mul_assoc]
        map_mul' := fun x y => by ext; simp [mul_assoc] }
    have hfix := hchar.fixed φ
    have key : ∀ x ∈ U, d * x * d⁻¹ ∈ U := by
      intro x hx
      have hmem : (⟨x, hUQ hx⟩ : Q) ∈ U.subgroupOf Q := hx
      rw [← hfix] at hmem
      exact hmem
    have hfix' := hchar.fixed φ.symm
    have key' : ∀ x ∈ U, d⁻¹ * x * d ∈ U := by
      intro x hx
      have hmem : (⟨x, hUQ hx⟩ : Q) ∈ U.subgroupOf Q := hx
      rw [← hfix'] at hmem
      exact hmem
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key x hx, fun hx => ?_⟩
    have := key' _ hx
    simpa [mul_assoc] using this
  have centralizes_abelian_characteristic {G : Type} [Group G] [Finite G] {p : ℕ}
      {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ρ : Representation (ZMod p) G V}
      (hS : FaithfulPrimeFieldKGroupModule G p V ρ) {q r : ℕ} (hq : q.Prime) (hr : r.Prime)
      (hqp : q ≠ p) (hrp : r ≠ p) (hqr : q ≠ r)
      (D : Subgroup G) (hD : Nat.card D = r)
      (hCV : (⨅ d ∈ D, LinearMap.ker (ρ d - LinearMap.id)) = (⊥ : Submodule (ZMod p) V))
      (Q : Subgroup G) (hQD : ⁅D, Q⁆ = Q) (hQ1 : Q ≠ ⊥) (hQq : IsPGroup q Q) :
      ∀ U : Subgroup G, U ≤ Q → (U.subgroupOf Q).Characteristic → IsMulCommutative U →
        D ≤ Subgroup.centralizer (U : Set G) := by
    intro U hUQ hchar hUc
    haveI : Fact p.Prime := ⟨hS.prime⟩
    haveI : Fact r.Prime := ⟨hr⟩
    have hUq : IsPGroup q U := hQq.of_injective (Subgroup.inclusion hUQ) (Subgroup.inclusion_injective hUQ)
    exact CFSG.GroupTheory.CoprimeActionSupport.FixedFreeNormalizerScalarExtension.centralizes
      ρ hS.faithful r D hD hCV U (normalizes_char D Q U hQD hUQ hchar)
      (card_ne_zero hS.prime hq hqp U hUq)
      (by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro h
        exact hrp ((Nat.prime_dvd_prime_iff_eq hS.prime hr).mp h).symm)
  intro hcomm
  apply hQ1
  have := centralizes_abelian_characteristic hS hq hr hqp hrp hqr D hD hCV Q hQD hQ1 hQq Q le_rfl
    (by
      have : Q.subgroupOf Q = ⊤ := Subgroup.subgroupOf_self Q
      rw [this]; infer_instance) hcomm
  rw [← hQD, eq_bot_iff, Subgroup.commutator_le]
  intro d hd x hx
  have := (Subgroup.mem_centralizer_iff.mp (this hd)) x hx
  rw [Subgroup.mem_bot, commutatorElement_def]
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  simpa [mul_assoc] using this.symm

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.AbelianCharacteristicCentrality
