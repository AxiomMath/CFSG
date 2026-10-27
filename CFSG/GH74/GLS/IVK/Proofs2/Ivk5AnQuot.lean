module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk5An

open Subgroup

theorem exists_hom_alternating_three {G : Type*} [Group G] (N : Subgroup G) [N.Normal] [Finite G]
    (hcard : Nat.card (G ⧸ N) = 3) :
    ∃ φ : G →* alternatingGroup (Fin 3), Function.Surjective φ ∧ φ.ker = N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic (G ⧸ N) := isCyclic_of_prime_card hcard
  have hA : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have : IsCyclic (alternatingGroup (Fin 3)) := isCyclic_of_prime_card hA
  let e : G ⧸ N ≃* alternatingGroup (Fin 3) := mulEquivOfCyclicCardEq (by rw [hcard, hA])
  refine ⟨(e : G ⧸ N →* alternatingGroup (Fin 3)).comp (QuotientGroup.mk' N), ?_, ?_⟩
  · exact e.surjective.comp (QuotientGroup.mk'_surjective N)
  · ext g
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
      map_eq_one_iff (e : G ⧸ N →* alternatingGroup (Fin 3)) e.injective]
    exact QuotientGroup.eq_one_iff g

namespace S3Quot

variable {Q : Type*} [Group Q]

theorem eq_one_or_eq_of_mem_zpowers {b q : Q} (hb2 : b ^ 2 = 1) (hq : q ∈ zpowers b) :
    q = 1 ∨ q = b := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hq
  have hb2' : b ^ (2 : ℤ) = 1 := by exact_mod_cast hb2
  obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
  · left; rw [zpow_mul, hb2', one_zpow]
  · right; rw [zpow_add_one, zpow_mul, hb2', one_zpow, one_mul]

theorem card_eq_six (a b : Q) (ha3 : a ^ 3 = 1) (ha : a ≠ 1) (hb2 : b ^ 2 = 1) (hb : b ≠ 1)
    (hgen : ∀ q : Q, ∃ i j : ℕ, q = a ^ i * b ^ j) : Nat.card Q = 6 := by
  have hoa : orderOf a = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime ha3 ha
  have hob : orderOf b = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hb2 hb
  let f : Fin 3 × Fin 2 → Q := fun p => a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨i, j, rfl⟩ := hgen q
    refine ⟨(⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 2, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    simp only [f]
    rw [← hoa, ← hob, pow_mod_orderOf, pow_mod_orderOf]
  have hfin : Finite Q := Finite.of_surjective f hf
  have hle : Nat.card Q ≤ 6 := by
    have := Nat.card_le_card_of_surjective f hf
    simpa using this
  have hd : 6 ∣ Nat.card Q := by
    have h3 : 3 ∣ Nat.card Q := hoa ▸ orderOf_dvd_natCard a
    have h2 : 2 ∣ Nat.card Q := hob ▸ orderOf_dvd_natCard b
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 2) h3 h2
  have hpos : 0 < Nat.card Q := Nat.card_pos
  omega

theorem injective_toPermHom (a b : Q) (ha3 : a ^ 3 = 1) (ha : a ≠ 1) (hb2 : b ^ 2 = 1)
    (hb : b ≠ 1) (hab : b * a * b⁻¹ = a⁻¹) :
    Function.Injective (MulAction.toPermHom Q (Q ⧸ zpowers b)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff_forall]
  intro q hq
  have hq' : ∀ g : Q, q • (g : Q ⧸ zpowers b) = g := fun g => by
    have := DFunLike.congr_fun (MonoidHom.mem_ker.mp hq) (g : Q ⧸ zpowers b)
    simpa using this
  have hbinv : b⁻¹ = b := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hb2]
  have h1 : q ∈ zpowers b := by
    have := hq' 1
    rw [MulAction.Quotient.smul_coe, QuotientGroup.eq] at this
    simpa using this
  rcases eq_one_or_eq_of_mem_zpowers hb2 h1 with h | h
  · exact h
  · exfalso
    subst h
    have h2 := hq' a
    rw [MulAction.Quotient.smul_coe, QuotientGroup.eq] at h2
    simp only [smul_eq_mul, mul_inv_rev] at h2
    rcases eq_one_or_eq_of_mem_zpowers hb2 h2 with h3 | h3
    · apply hb
      rw [← hbinv]
      calc q⁻¹ = a * (a⁻¹ * q⁻¹ * a) * a⁻¹ := by group
        _ = 1 := by rw [h3]; group
    · have hcomm : q * a = a * q := by
        rw [hbinv] at h3
        calc q * a = a * (a⁻¹ * q * a) := by group
          _ = a * q := by rw [h3]
      rw [hcomm, mul_inv_cancel_right] at hab
      have ha2 : a ^ 2 = 1 := by
        rw [pow_two]
        exact mul_eq_one_iff_eq_inv.mpr hab
      apply ha
      calc a = a ^ 3 * (a ^ 2)⁻¹ := by group
        _ = 1 := by rw [ha3, ha2, inv_one, one_mul]

theorem exists_bijective_hom_perm_three (a b : Q) (ha3 : a ^ 3 = 1) (ha : a ≠ 1)
    (hb2 : b ^ 2 = 1) (hb : b ≠ 1) (hab : b * a * b⁻¹ = a⁻¹)
    (hgen : ∀ q : Q, ∃ i j : ℕ, q = a ^ i * b ^ j) :
    ∃ ψ : Q →* Equiv.Perm (Fin 3), Function.Bijective ψ := by
  have hcard := card_eq_six a b ha3 ha hb2 hb hgen
  have hfin : Finite Q := Nat.finite_of_card_ne_zero (by omega)
  have hob : orderOf b = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hb2 hb
  have hidx : (zpowers b).index = 3 := by
    have h := (zpowers b).index_mul_card
    rw [Nat.card_zpowers, hob, hcard] at h
    omega
  have hq : Nat.card (Q ⧸ zpowers b) = 3 := hidx
  let e : (Q ⧸ zpowers b) ≃ Fin 3 := (Finite.equivFin (Q ⧸ zpowers b)).trans (finCongr hq)
  refine ⟨(Equiv.permCongrHom e : Equiv.Perm (Q ⧸ zpowers b) ≃* Equiv.Perm (Fin 3)).toMonoidHom.comp
    (MulAction.toPermHom Q (Q ⧸ zpowers b)), ?_⟩
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨(Equiv.permCongrHom e).injective.comp (injective_toPermHom a b ha3 ha hb2 hb hab), ?_⟩
  rw [hcard, Nat.card_perm, Nat.card_fin]
  rfl

end S3Quot

theorem exists_hom_perm_three {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (x y : G)
    (hx3 : x ^ 3 ∈ N) (hx : x ∉ N) (hy2 : y ^ 2 ∈ N) (hy : y ∉ N) (hxy : y * x * y⁻¹ * x ∈ N)
    (hgen : ∀ g : G, ∃ n ∈ N, ∃ i j : ℕ, g = n * x ^ i * y ^ j) :
    ∃ φ : G →* Equiv.Perm (Fin 3), Function.Surjective φ ∧ φ.ker = N := by
  have ha3 : ((x : G ⧸ N)) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hx3
  have ha : (x : G ⧸ N) ≠ 1 := fun h => hx ((QuotientGroup.eq_one_iff x).1 h)
  have hb2 : ((y : G ⧸ N)) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hy2
  have hb : (y : G ⧸ N) ≠ 1 := fun h => hy ((QuotientGroup.eq_one_iff y).1 h)
  have hab : (y : G ⧸ N) * x * (y : G ⧸ N)⁻¹ = (x : G ⧸ N)⁻¹ := by
    have := (QuotientGroup.eq_one_iff _).2 hxy
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv] at this
    exact eq_inv_of_mul_eq_one_left this
  have hgen' : ∀ q : G ⧸ N, ∃ i j : ℕ, q = (x : G ⧸ N) ^ i * (y : G ⧸ N) ^ j := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨n, hn, i, j, rfl⟩ := hgen g
    refine ⟨i, j, ?_⟩
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_pow,
      (QuotientGroup.eq_one_iff n).2 hn, one_mul]
  obtain ⟨ψ, hψ⟩ := S3Quot.exists_bijective_hom_perm_three _ _ ha3 ha hb2 hb hab hgen'
  refine ⟨ψ.comp (QuotientGroup.mk' N), hψ.2.comp (QuotientGroup.mk'_surjective N), ?_⟩
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, map_eq_one_iff ψ hψ.1]
  exact QuotientGroup.eq_one_iff g

end CFSG.GH74.GLS.IVK.Proofs2.Ivk5An
