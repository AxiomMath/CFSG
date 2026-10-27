module

public import CFSG.GH74.GLS.Stage4.RestCases
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage4.T2Cent

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4

section Bad3

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem t2_card_fact_of_sylow {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G) {C : Subgroup G}
    (hPC : (P : Subgroup G) ≤ C) :
    (Nat.card G).factorization p = (Nat.card C).factorization p := by
  have h1 : Nat.card ↥(P : Subgroup G) = p ^ (Nat.card G).factorization p :=
    Sylow.card_eq_multiplicity P
  have h2 : Nat.card ↥(P : Subgroup G) ∣ Nat.card C := Subgroup.card_dvd_of_le hPC
  have h3 : Nat.card C ∣ Nat.card G := Subgroup.card_subgroup_dvd_card C
  have hC0 : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  apply le_antisymm
  · rw [h1] at h2
    have := (hp.out.pow_dvd_iff_le_factorization hC0).1 h2
    exact this
  · exact (Nat.factorization_le_iff_dvd hC0 hG0).2 h3 p

theorem t2_card2 (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) :
    (Nat.card G).factorization 2 = (Nat.card (centralizer ({z} : Set G))).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, S, hzS, hcent⟩ := hSet.central
  refine t2_card_fact_of_sylow S ?_
  intro s hs
  exact Subgroup.mem_centralizer_singleton_iff.2 (hcent s hs)

theorem t2_bad3 (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hBad : Ch6Bad3 G) : ∃ P : Sylow 3 G, (P : Subgroup G) ≤ K₁ ⊔ K₂ := by
  obtain ⟨z', hz'2, P, hP⟩ := hBad
  obtain ⟨c, hc⟩ := isConj_iff.1 (hSet.one_class z' hz'2)
  let f : G →* G := (MulAut.conj c⁻¹).toMonoidHom
  have hfs : Function.Surjective f := (MulAut.conj c⁻¹).surjective
  refine ⟨P.mapSurjective hfs, ?_⟩
  rw [Sylow.coe_mapSurjective]
  have hP' : (P : Subgroup G).map f ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hP hx
    rw [t2C_oPrimeResidualOf_eq_closure] at hx' ⊢
    have hmap : (Subgroup.closure {y | y ∈ centralizer ({z'} : Set G) ∧ ∃ k : ℕ, y ^ 2 ^ k = 1}).map f ≤
        Subgroup.closure {y | y ∈ centralizer ({z} : Set G) ∧ ∃ k : ℕ, y ^ 2 ^ k = 1} := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨y, ⟨hyC, k, hk⟩, rfl⟩
      refine Subgroup.subset_closure ⟨?_, k, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
        have h1 : y * z' = z' * y := hyC
        show c⁻¹ * y * c⁻¹⁻¹ * z = z * (c⁻¹ * y * c⁻¹⁻¹)
        have hz : z = c⁻¹ * z' * c := by rw [← hc]; group
        rw [hz]
        calc c⁻¹ * y * c⁻¹⁻¹ * (c⁻¹ * z' * c) = c⁻¹ * (y * z') * c := by group
          _ = c⁻¹ * (z' * y) * c := by rw [h1]
          _ = c⁻¹ * z' * c * (c⁻¹ * y * c⁻¹⁻¹) := by group
      · show (c⁻¹ * y * c⁻¹⁻¹) ^ 2 ^ k = 1
        rw [conj_pow, hk]; group
    exact hmap ⟨x, hx', rfl⟩
  intro x hx
  have hxC₁ := hP' hx
  have hxodd : Odd (orderOf x) := by
    obtain ⟨y, hy, rfl⟩ := hx
    have hy3 : ∃ k : ℕ, y ^ 3 ^ k = 1 := by
      obtain ⟨k, hk⟩ := (P.isPGroup') ⟨y, hy⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    obtain ⟨k, hk⟩ := hy3
    have hdvd : orderOf (f y) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one (by
      rw [← map_pow, hk, map_one])
    exact Odd.of_dvd_nat (Odd.pow (by decide)) hdvd
  exact t2C_odd_mem_of_index_two hSet.index_two hxC₁ hxodd

theorem t2_card3 (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hBad : Ch6Bad3 G) :
    (Nat.card G).factorization 3 = (Nat.card (centralizer ({z} : Set G))).factorization 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := t2_bad3 hSet hBad
  exact t2_card_fact_of_sylow P (hP.trans hSet.le_centralizer)

end Bad3

end CFSG.GH74.GLS.Stage4.Rest
