module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerCase
public import CFSG.Quasithin.SteinbergCBAlternatingAut
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8Sp4

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace AZ

open CFSG Subgroup CFSG.ComponentClassification.GSThmB
open scoped commutatorElement

theorem commutator_le_of_out_comm {H : Type*} [Group H] (L : Subgroup H) [L.Normal]
    (hC : centralizer (L : Set H) = ⊥)
    (hout : ∀ u v : MulAut L, ⁅u, v⁆ ∈ (MulAut.conj : L →* MulAut L).range) :
    commutator H ≤ L := by
  rw [_root_.commutator_def, commutator_le]
  intro a _ b _
  obtain ⟨l, hl⟩ := hout (MulAut.conjNormal a) (MulAut.conjNormal b)
  have h1 : MulAut.conjNormal ⁅a, b⁆ = (MulAut.conjNormal (l : H) : MulAut L) := by
    rw [map_commutatorElement, ← hl, MulAut.conjNormal_val]
  have h2 : (l : H)⁻¹ * ⁅a, b⁆ ∈ centralizer (L : Set H) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h3 := congrArg (fun ψ : MulAut L => ((ψ ⟨x, hx⟩ : L) : H)) h1
    simp only [MulAut.conjNormal_apply] at h3
    calc x * ((l : H)⁻¹ * ⁅a, b⁆) = (l : H)⁻¹ * ((l : H) * x * (l : H)⁻¹) * ⁅a, b⁆ := by group
      _ = (l : H)⁻¹ * (⁅a, b⁆ * x * ⁅a, b⁆⁻¹) * ⁅a, b⁆ := by rw [h3]
      _ = (l : H)⁻¹ * ⁅a, b⁆ * x := by group
  rw [hC, mem_bot, inv_mul_eq_one] at h2
  rw [← h2]
  exact l.2

theorem le_of_perfect {H : Type*} [Group H] (L : Subgroup H) [L.Normal]
    (hC : centralizer (L : Set H) = ⊥)
    (hout : ∀ u v : MulAut L, ⁅u, v⁆ ∈ (MulAut.conj : L →* MulAut L).range) {J : Subgroup H}
    (hJ : ⁅J, J⁆ = J) : J ≤ L := by
  rw [← hJ]
  exact (commutator_mono le_top le_top).trans
    ((_root_.commutator_def H).symm ▸ commutator_le_of_out_comm L hC hout)

theorem out_comm_alternatingGroup_ten (u v : MulAut (alternatingGroup (Fin 10))) :
    ⁅u, v⁆ ∈ (MulAut.conj : alternatingGroup (Fin 10) →* MulAut (alternatingGroup (Fin 10))).range
    := by
  have hc := (Quasithin.SteinbergCB.isSolvable_outer_alternatingGroup (n := 10)
    (Or.inr (by norm_num))).2
  have hcomm : ∀ a b : OuterAutomorphisms.Outer (alternatingGroup (Fin 10)), a * b = b * a := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hc with h1 | h2
    · have := (Nat.card_eq_one_iff_unique.1 h1).1
      exact fun a b => Subsingleton.elim _ _
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := isCyclic_of_prime_card h2
      exact fun a b => (IsCyclic.isMulCommutative
        (α := OuterAutomorphisms.Outer (alternatingGroup (Fin 10)))).is_comm.comm a b
  change ⁅u, v⁆ ∈ OuterAutomorphisms.inner (alternatingGroup (Fin 10))
  rw [← QuotientGroup.eq_one_iff]
  change QuotientGroup.mk' (OuterAutomorphisms.inner (alternatingGroup (Fin 10))) ⁅u, v⁆ = 1
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact hcomm _ _

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem two_mul_card_of_isSec8JType {Y : Type} [Group Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hY : IsSec8JType Y p f) : 2 * Nat.card Y = (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) := by
  rcases hY with hL | ⟨rfl, rfl, ⟨e⟩⟩
  · have hQ : Odd (p ^ (2 * f)) := (hp.odd_of_ne_two hp2).pow
    rw [card_of_lieModel_psl_two hp2 hL, two_mul_ordA_one hQ, ← pow_mul, ← pow_mul,
      ← pow_mul, show f * 2 = 2 * f by ring, show 2 * f * 2 = f * 4 by ring]
  · rw [Nat.card_congr e.toEquiv, card_alternatingGroup_six]
    norm_num

theorem five_dvd_sq_mul (q : ℕ) : 5 ∣ q ^ 2 * (q ^ 4 - 1) := by
  have h1 : 1 ≤ q ^ 4 ∨ q = 0 := by
    rcases Nat.eq_zero_or_pos q with h | h
    · exact Or.inr h
    · exact Or.inl (Nat.one_le_pow _ _ h)
  rcases h1 with h1 | rfl
  · rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, Nat.cast_sub h1, Nat.cast_pow, Nat.cast_pow,
      Nat.cast_one]
    have key : ∀ x : ZMod 5, x ^ 2 * (x ^ 4 - 1) = 0 := by decide
    exact key _
  · simp

theorem five_dvd_card_of_isSec8JType {Y : Type} [Group Y] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hY : IsSec8JType Y p f) : 5 ∣ Nat.card Y := by
  have h := two_mul_card_of_isSec8JType hp hp2 hY
  have h5 : 5 ∣ 2 * Nat.card Y := h ▸ five_dvd_sq_mul (p ^ f)
  exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h5)

theorem exists_prime_dvd_card_of_isSec8JType {Y : Type} [Group Y] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hY : IsSec8JType Y p f) :
    ∃ s : ℕ, s.Prime ∧ s ≠ 2 ∧ s ∣ (p ^ f) ^ 2 + 1 ∧ s ∣ Nat.card Y := by
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h3 : 3 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    calc 3 ≤ p := hp3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  obtain ⟨s, hs, hs2, hsq⟩ := exists_odd_prime_dvd_sq_add_one hq h3
  refine ⟨s, hs, hs2, hsq, ?_⟩
  have h4 : s ∣ 2 * Nat.card Y := by
    rw [two_mul_card_of_isSec8JType hp hp2 hY]
    apply Dvd.dvd.mul_left
    obtain ⟨Q, hQ1⟩ : ∃ Q, (p ^ f) ^ 2 = Q + 1 :=
      ⟨(p ^ f) ^ 2 - 1, by have : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
    have h5 : (p ^ f) ^ 4 - 1 = ((p ^ f) ^ 2 + 1) * ((p ^ f) ^ 2 - 1) := by
      rw [show (p ^ f) ^ 4 = ((p ^ f) ^ 2) ^ 2 by ring, hQ1,
        show (Q + 1) ^ 2 = (Q ^ 2 + 2 * Q) + 1 by ring, Nat.add_sub_cancel, Nat.add_sub_cancel]
      ring
    rw [h5]
    exact Dvd.dvd.mul_right hsq _
  exact Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hs Nat.prime_two).2 hs2) h4

end AZ

end CFSG.ComponentClassification.CatFactsL4U4
