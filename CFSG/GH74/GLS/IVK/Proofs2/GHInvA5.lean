module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4PerfApply

public section

namespace CFSG.GH74.GLS.IVK.GHInv

open Subgroup CFSG CFSG.ABGLocalTools Blueprint

theorem u2_card_data' {B : Type} [Group B] [Finite B] (hq : IsQuasisimple B)
    (hU : HasL2Model (B ⧸ pPrimeCore 2 B) Odd ∨
      Nonempty ((B ⧸ pPrimeCore 2 B) ≃* alternatingGroup (Fin 7)))
    (hodd : Odd (Nat.card (center B))) :
    pPrimeCore 2 B = center B ∧ ∃ n : ℕ,
      (n = 2520 ∨ ∃ q : ℕ, 5 ≤ q ∧ Odd q ∧ 2 * n = q * (q ^ 2 - 1)) ∧
      Nat.card (B ⧸ pPrimeCore 2 B) = n ∧ Nat.card B = n * Nat.card (center B) := by
  have hnt : Nontrivial (B ⧸ pPrimeCore 2 B) := by
    rcases hU with hL | he
    · obtain ⟨hs, -⟩ := Generic.S45.LAlt.hasL2Model_data hL
      infer_instance
    · obtain ⟨e⟩ := he
      have hA : Nontrivial (alternatingGroup (Fin 7)) := by
        rw [← Finite.one_lt_card_iff_nontrivial, Nat.card_eq_fintype_card, card_alternatingGroup,
          Fintype.card_fin]
        decide
      exact e.symm.injective.nontrivial
  have hNZ : pPrimeCore 2 B = center B := by
    apply le_antisymm
    · rcases LocalCores.quasisimple_normal_subgroups hq (inferInstance : (pPrimeCore 2 B).Normal) with h | h
      · exfalso
        have : Subsingleton (B ⧸ pPrimeCore 2 B) := by
          rw [h]
          exact (QuotientGroup.subsingleton_quotient_top)
        exact not_subsingleton _ this
      · exact h
    · exact le_sSup ⟨inferInstance, Nat.coprime_two_left.2 hodd⟩
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 B)
  have hcardN : Nat.card ↥(pPrimeCore 2 B) = Nat.card ↥(center B) := by rw [hNZ]
  rw [hcardN] at hcard
  refine ⟨hNZ, Nat.card (B ⧸ pPrimeCore 2 B), ?_, rfl, hcard⟩
  rcases hU with hL | he
  · obtain ⟨-, -, -, q, hq5, hqo, hc, -⟩ := Generic.S45.LAlt.hasL2Model_data hL
    exact Or.inr ⟨q, hq5, hqo, by omega⟩
  · obtain ⟨e⟩ := he
    left
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide

theorem u2_arith_240 {n z : ℕ}
    (hn : n = 2520 ∨ ∃ q : ℕ, 5 ≤ q ∧ Odd q ∧ 2 * n = q * (q ^ 2 - 1)) (hz : Odd z)
    (hd : n * z ∣ 240) : n = 60 ∧ z = 1 := by
  have hz0 : 0 < z := hz.pos
  have hnN : n ∣ 240 := Dvd.dvd.trans (Dvd.intro z rfl) hd
  have hnle : n ≤ 240 := Nat.le_of_dvd (by norm_num) hnN
  rcases hn with rfl | ⟨q, hq5, hqo, hqn⟩
  · exfalso
    omega
  · have hq8 : q ≤ 8 := by
      by_contra hc
      push Not at hc
      have h1 : 9 * (9 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
        Nat.mul_le_mul hc (Nat.sub_le_sub_right (Nat.pow_le_pow_left hc 2) 1)
      norm_num at h1
      omega
    obtain ⟨k, rfl⟩ := hqo
    have hk : k ≤ 3 := by omega
    have hk2 : 2 ≤ k := by omega
    interval_cases k <;> simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] at hqn
    · have hn60 : n = 60 := by omega
      subst hn60
      have hz4 : z ∣ 4 := by
        have h1 : 60 * z ∣ 60 * 4 := by simpa using hd
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
      have hzle : z ≤ 4 := Nat.le_of_dvd (by norm_num) hz4
      refine ⟨rfl, ?_⟩
      interval_cases z
      · rfl
      · exact absurd hz (by decide)
      · exact absurd hz4 (by decide)
      · exact absurd hz (by decide)
    · exfalso
      have hn168 : n = 168 := by omega
      subst hn168
      omega

theorem hasL2Model_card_sixty {X : Type} [Group X]
    (h : HasL2Model X Odd) (hc : Nat.card X = 60) :
    Nonempty (X ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨-, -, -, q, hq5, hqo, hcq, hP⟩ := Generic.S45.LAlt.hasL2Model_data h
  have hq : q = 5 := by
    rw [hc] at hcq
    have hq8 : q ≤ 5 := by
      by_contra hcon
      push Not at hcon
      have h1 : 6 * (6 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
        Nat.mul_le_mul hcon (Nat.sub_le_sub_right (Nat.pow_le_pow_left hcon 2) 1)
      norm_num at h1
      omega
    omega
  subst hq
  obtain ⟨p, f, hp, hf, h5, hL⟩ := hP (fun m => m = 5) rfl
  obtain ⟨-, F, hFfield, hFfin, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSL hL
  have hF5 : Nat.card F = 5 := by rw [hF, ← h5]
  obtain ⟨e5⟩ := (CFSG.LinearGroups.five_field_linear_two_alternating_five_model F hF5).1
  exact ⟨(e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm).trans e5⟩

theorem u2_a5_of_dvd_240 {B : Type} [Group B] [Finite B]
    (hq : IsQuasisimple B)
    (hU : HasL2Model (B ⧸ pPrimeCore 2 B) Odd ∨
      Nonempty ((B ⧸ pPrimeCore 2 B) ≃* alternatingGroup (Fin 7)))
    (hodd : Odd (Nat.card (center B))) (hd : Nat.card B ∣ 240) :
    Nat.card B = 60 ∧ center B = ⊥ ∧ Nonempty ((B ⧸ pPrimeCore 2 B) ≃* alternatingGroup (Fin 5)) ∧
      Nonempty (B ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨hNZ, n, hn, hnB, hB⟩ := u2_card_data' hq hU hodd
  rw [hB] at hd
  obtain ⟨hn60, hz1⟩ := u2_arith_240 hn hodd hd
  have hZ : center B = ⊥ := Subgroup.card_eq_one.1 hz1
  have hcB : Nat.card B = 60 := by rw [hB, hn60, hz1]
  have hbar : Nat.card (B ⧸ pPrimeCore 2 B) = 60 := by rw [hnB, hn60]
  have hA5 : Nonempty ((B ⧸ pPrimeCore 2 B) ≃* alternatingGroup (Fin 5)) := by
    rcases hU with hL | he
    · exact hasL2Model_card_sixty hL hbar
    · exfalso
      obtain ⟨e⟩ := he
      have h7 : Nat.card (B ⧸ pPrimeCore 2 B) = 2520 := by
        rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
          Fintype.card_fin]
        decide
      omega
  refine ⟨hcB, hZ, hA5, ?_⟩
  obtain ⟨e5⟩ := hA5
  have hbot : pPrimeCore 2 B = ⊥ := by rw [hNZ, hZ]
  have e1 : B ≃* (B ⧸ pPrimeCore 2 B) :=
    (QuotientGroup.quotientBot (G := B)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hbot.symm)
  exact ⟨e1.trans e5⟩

@[expose] def NoU2Comp (C : Type) [Group C] : Prop :=
  ∀ B : Subgroup C, IsComponent B →
    (HasL2Model (↥B ⧸ pPrimeCore 2 ↥B) Odd ∨
      Nonempty ((↥B ⧸ pPrimeCore 2 ↥B) ≃* alternatingGroup (Fin 7))) →
    Odd (Nat.card (center ↥B)) → False

theorem NoU2Comp.of_solvable {C : Type} [Group C] (hs : Group.IsSolvable C) : NoU2Comp C := by
  intro B hB _ _
  have hsB : Group.IsSolvable B :=
    Group.isSolvable_of_isSolvable_injective (f := B.subtype) B.subtype_injective
  exact not_isSolvable_of_isQuasisimple hB.1 hsB

theorem NoU2Comp.of_perfect {C : Type} [Group C] [Finite C] (hC : Group.IsPerfect C)
    (hN : Nat.card C = 1920 ∨ Nat.card C = 2688) : NoU2Comp C :=
  fun _ hB hU hodd => false_of_perfect_u2_component hC hN hB hU hodd

theorem NoU2Comp.of_equiv {C C' : Type} [Group C] [Group C'] (e : C ≃* C') (h : NoU2Comp C') :
    NoU2Comp C := by
  intro B hB hU hodd
  let B' : Subgroup C' := B.map e.toMonoidHom
  let f : ↥B ≃* ↥B' := Subgroup.equivMapOfInjective B e.toMonoidHom e.injective
  have hB' : IsComponent B' := LocalCores.isComponent_map_mulEquiv e hB
  obtain ⟨hU', hodd'⟩ := u2_data_of_mulEquiv f ⟨hU, hodd⟩
  exact h B' hB' hU' hodd'

end CFSG.GH74.GLS.IVK.GHInv
