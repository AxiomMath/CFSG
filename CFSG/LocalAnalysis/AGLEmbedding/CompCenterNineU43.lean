module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder

public section

namespace CFSG.AGLEmbedding.CompCenterNine

open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU unitaryPSUEquiv)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSU)

theorem outer_facts_of_mulEquiv {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    (h : Nat.card (Outer T) = 8 ∧
      ∃ a b : Outer T, a ≠ 1 ∧ b ≠ 1 ∧ a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a ≠ b) :
    Nat.card (Outer S) = 8 ∧
      ∃ a b : Outer S, a ≠ 1 ∧ b ≠ 1 ∧ a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a ≠ b := by
  obtain ⟨h8, a, b, ha, hb, ha2, hb2, hab⟩ := h
  let ψ : Outer T ≃* Outer S := (equivalence e).symm
  refine ⟨(Nat.card_congr ψ.toEquiv).symm.trans h8, ψ a, ψ b, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h1 => ha (ψ.injective (h1.trans (map_one ψ).symm))
  · exact fun h1 => hb (ψ.injective (h1.trans (map_one ψ).symm))
  · rw [← map_pow, ha2, map_one]
  · rw [← map_pow, hb2, map_one]
  · exact fun h1 => hab (ψ.injective h1)

theorem exponent_eq_one_of_pow_eq_three {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hq : p ^ f = 3) :
    f = 1 := by
  rcases f with _ | _ | f
  · omega
  · rfl
  · have h3 : p ^ (f + 2) = 3 := hq
    have h4 : 2 ^ (f + 2) ≤ p ^ (f + 2) := Nat.pow_le_pow_left hp.two_le _
    have h5 : 2 ^ 2 ≤ 2 ^ (f + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem outer_primeFormP_four {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)
    (hq : p ^ f = 3) :
    Nat.card (Outer (primeFormP h ((1 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))) = 8 ∧
      ∃ a b : Outer (primeFormP h ((1 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)),
        a ≠ 1 ∧ b ≠ 1 ∧ a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a ≠ b := by
  classical
  have hf : f = 1 := exponent_eq_one_of_pow_eq_three h.prime h.one_le hq
  have hC : IsPrimeFormGram (1 : GL (Fin 4) F) := isPrimeFormGram_one
  have hn : 3 ≤ 4 := by norm_num
  have hq2 : ¬(4 = 3 ∧ p ^ f = 2) := by omega
  obtain ⟨-, -, hcardDI, hout, -, -⟩ := unitary_full_diagonal_outer_order h hn hq2
  obtain ⟨-, -, -, -, -, hFapp, -, hFker, -, hinn, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq2
  set T := primeFormP h ((1 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
  set D := primeFormD h ((1 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
  set I := inner T
  have hID : I ≤ D := fun α hα => by
    obtain ⟨s, rfl⟩ := (hinn α).1 hα
    exact ⟨_, rfl⟩
  let τ : F ≃+* F :=
    { toFun := h.bar
      invFun := h.bar
      left_inv := h.bar_bar
      right_inv := h.bar_bar
      map_mul' := map_mul h.bar
      map_add' := map_add h.bar }
  have hτ2 : τ ^ 2 = 1 := RingEquiv.ext fun c => h.bar_bar c
  have hτ1 : τ ≠ 1 := fun h1 => by
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    exact hc (congrArg (fun φ : F ≃+* F => φ c) h1)
  set σ := primeFormFieldHom h hC τ
  have hσ2 : σ ^ 2 = 1 := by rw [← map_pow, hτ2, map_one]
  have hσD : σ ∉ D := by
    rw [← hFker, MonoidHom.mem_ker]
    have h1 := hFapp 1 τ
    rw [map_one, one_mul] at h1
    rwa [h1]
  have hσI : σ ∉ I := fun h1 => hσD (hID h1)
  have h4 : Nat.card (D ⧸ I.subgroupOf D) = 4 := by
    rw [hcardDI, hq]
    norm_num
  have : Finite (D ⧸ I.subgroupOf D) := Nat.finite_of_card_ne_zero (by rw [h4]; norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨δ, hδ⟩ := exists_prime_orderOf_dvd_card' (G := D ⧸ I.subgroupOf D) 2
    (by rw [h4]; norm_num)
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective δ
  have hdI : (d : MulAut T) ∉ I := by
    intro h1
    have h2 : ((d : D ⧸ I.subgroupOf D)) = 1 :=
      (QuotientGroup.eq_one_iff d).mpr (Subgroup.mem_subgroupOf.mpr h1)
    rw [h2, orderOf_one] at hδ
    omega
  have hd2 : (d : MulAut T) ^ 2 ∈ I := by
    have h1 : ((d : D ⧸ I.subgroupOf D)) ^ 2 = 1 := by rw [← hδ]; exact pow_orderOf_eq_one _
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  refine ⟨by rw [hout, hq, hf]; norm_num, (σ : Outer T), ((d : MulAut T) : Outer T), ?_, ?_, ?_,
    ?_, ?_⟩
  · exact fun h1 => hσI ((QuotientGroup.eq_one_iff σ).mp h1)
  · exact fun h1 => hdI ((QuotientGroup.eq_one_iff _).mp h1)
  · rw [← QuotientGroup.mk_pow, hσ2, QuotientGroup.mk_one]
  · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hd2
  · intro h1
    have h2 := QuotientGroup.eq.mp h1
    apply hσD
    have h3 : σ = (d : MulAut T) * ((σ⁻¹ * (d : MulAut T))⁻¹) := by group
    rw [h3]
    exact D.mul_mem d.2 (D.inv_mem (hID h2))

theorem outer_facts_of_psu43 {S : Type*} [Group S] {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) (hq : p ^ f = 3) (e : S ≃* StatedProj (StatedSU 4 (p ^ f) F)) :
    Nat.card (Outer S) = 8 ∧
      ∃ a b : Outer S, a ≠ 1 ∧ b ≠ 1 ∧ a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a ≠ b := by
  have hq2 : ¬(4 = 3 ∧ p ^ f = 2) := by omega
  obtain ⟨⟨eT⟩, -⟩ := unitary_full_diagonal_outer_order h (n := 4) (by norm_num) hq2
  exact outer_facts_of_mulEquiv
    ((e.trans (unitaryPSUEquiv h (by norm_num : 1 ≤ 4)).symm).trans eT.symm)
    (outer_primeFormP_four h hq)

end CFSG.AGLEmbedding.CompCenterNine
