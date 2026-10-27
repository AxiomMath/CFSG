module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

namespace SylowCommute

open scoped Pointwise

variable {G : Type*} [Group G]

theorem card_sup_mul_card_inf (L R : Subgroup G) (hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) :
    Nat.card ↥(L ⊔ R) * Nat.card ↥(L ⊓ R) = Nat.card L * Nat.card R ∧
      ∀ x, x ∈ L ⊔ R ↔ ∃ a ∈ L, ∃ b ∈ R, x = a * b := by
  let μ : L × R →* G := MonoidHom.noncommCoprod L.subtype R.subtype fun x y => hc x x.2 y y.2
  have hμ : ∀ x : L × R, μ x = (x.1 : G) * x.2 := fun _ => rfl
  have hrange : μ.range = L ⊔ R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hμ]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le (fun l hl => ⟨(⟨l, hl⟩, 1), by rw [hμ]; simp⟩)
        (fun r hr => ⟨(1, ⟨r, hr⟩), by rw [hμ]; simp⟩)
  have hmem : ∀ x, x ∈ L ⊔ R ↔ ∃ a ∈ L, ∃ b ∈ R, x = a * b := by
    intro x
    rw [← hrange]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.1.2, y.2, y.2.2, rfl⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have hker : Nat.card μ.ker = Nat.card (L ⊓ R : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : G), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : G)⁻¹, inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact R.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · apply Subtype.ext
      have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Prod.ext rfl (Subtype.ext h)
  have := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at this
  exact ⟨by rw [mul_comm]; exact this, hmem⟩

theorem exists_conj_of_card_eq [Finite G] {p : ℕ} [Fact p.Prime] {K T X : Subgroup G}
    (hTK : T ≤ K) (hXK : X ≤ K) (hT : Nat.card T = p ^ (Nat.card K).factorization p)
    (hX : Nat.card X = p ^ (Nat.card K).factorization p) :
    ∃ g ∈ K, ∀ x : G, x ∈ X ↔ ∃ t ∈ T, g * t * g⁻¹ = x := by
  have hcT : Nat.card (T.subgroupOf K) = p ^ (Nat.card K).factorization p := by
    rw [← hT]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv
  have hcX : Nat.card (X.subgroupOf K) = p ^ (Nat.card K).factorization p := by
    rw [← hX]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv
  let P : Sylow p K := Sylow.ofCard (T.subgroupOf K) hcT
  let Q : Sylow p K := Sylow.ofCard (X.subgroupOf K) hcX
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P Q
  refine ⟨g, g.2, fun x => ?_⟩
  have hQ : (Q : Subgroup K) = MulAut.conj g • (P : Subgroup K) := by
    rw [← Sylow.coe_subgroup_smul, hg]
  constructor
  · intro hx
    have hxQ : (⟨x, hXK hx⟩ : K) ∈ (Q : Subgroup K) := hx
    rw [hQ, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
    obtain ⟨s, hs, hsx⟩ := hxQ
    refine ⟨(s : G), hs, ?_⟩
    have := congrArg Subtype.val hsx
    simpa using this
  · rintro ⟨t, ht, rfl⟩
    have htP : (⟨t, hTK ht⟩ : K) ∈ (P : Subgroup K) := ht
    have : MulAut.conj g • (⟨t, hTK ht⟩ : K) ∈ (Q : Subgroup K) := by
      rw [hQ]; exact Subgroup.smul_mem_pointwise_smul _ _ _ htP
    exact this

theorem exists_le_card_eq [Finite G] {p : ℕ} [Fact p.Prime] (A : Subgroup G) :
    ∃ S : Subgroup G, S ≤ A ∧ Nat.card S = p ^ (Nat.card A).factorization p := by
  let P : Sylow p A := default
  refine ⟨(P : Subgroup A).map A.subtype, Subgroup.map_subtype_le _, ?_⟩
  rw [Subgroup.card_map_of_injective A.subtype_injective]
  exact P.card_eq_multiplicity

theorem card_inf_eq [Finite G] {p : ℕ} (hp : p.Prime) {X A S : Subgroup G} {m : ℕ}
    (hX : Nat.card X = p ^ m) (hS : S ≤ X ⊓ A)
    (hSc : Nat.card S = p ^ (Nat.card A).factorization p) :
    Nat.card ↥(X ⊓ A) = p ^ (Nat.card A).factorization p := by
  have h1 : Nat.card ↥(X ⊓ A) ∣ p ^ m := by
    rw [← hX]; exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 h1
  have h2 : p ^ k ∣ Nat.card A := by
    rw [← hk]; exact Subgroup.card_dvd_of_le inf_le_right
  have h3 : k ≤ (Nat.card A).factorization p :=
    (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 h2
  have h4 : p ^ (Nat.card A).factorization p ∣ p ^ k := by
    rw [← hk, ← hSc]; exact Subgroup.card_dvd_of_le hS
  have h5 : (Nat.card A).factorization p ≤ k := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h4
  rw [hk, le_antisymm h3 h5]

end SylowCommute

end CFSG.GH74.GLS.IVK.Proofs2
