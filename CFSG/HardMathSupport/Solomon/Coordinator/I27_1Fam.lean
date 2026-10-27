module

public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Gen
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullCore

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance

@[expose] def I271AltType {X : Type} [Group X] (K : Subgroup X) (n : ℕ) (hn : 5 ≤ n) : Prop :=
  Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.alternating n hn).Group)

@[expose] def I271LieType (P : ℕ → Prop) {X : Type} [Group X] (K : Subgroup X) : Prop :=
  ∃ idx : TauCeti.ValidLieTypeIndex,
    Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie idx).Group) ∧
      P idx.1.characteristic

@[expose] def I271SporType {X : Type} [Group X] (K : Subgroup X) (name : TauCeti.SporadicName) :
    Prop :=
  Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.sporadic name).Group)

@[expose] def I271NotAlt {X : Type} [Group X] (K : Subgroup X) : Prop :=
  ¬ ∃ (n : ℕ) (hn : 5 ≤ n), I271AltType K n hn

@[expose] def I271Norm (p : ℕ) {X : Type} [Group X] [Finite X] (K B : Subgroup X) : Prop :=
  B ≤ Subgroup.normalizer (K : Set X) ∧ p ^ 2 ≤ autOrderIn B K

@[expose] def I271NNHatSixRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ K B : Subgroup X,
    I271Hyp 3 K B → ¬ B ≤ Subgroup.normalizer (K : Set X) → IsHatSix ↥K →
      3 ^ 2 ≤ autOrderIn B K

@[expose] def I271AutBalanceAltSix : Prop :=
  ∀ A : Subgroup (MulAut ↥(alternatingGroup (Fin 6))), IsElemAbelian 3 A → 3 ^ 2 ≤ Nat.card A →
    ∀ T : Subgroup (MulAut ↥(alternatingGroup (Fin 6))), Nat.Coprime 3 (Nat.card T) →
      A ≤ Subgroup.normalizer (T : Set (MulAut ↥(alternatingGroup (Fin 6)))) → T = ⊥

@[expose] def I271NNOther : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ K B : Subgroup X,
    I271Hyp 3 K B → ¬ B ≤ Subgroup.normalizer (K : Set X) →
      (IsLTwoOddPow ↥K ∨ IsHatSeven ↥K ∨ IsHatMTwentyTwo ↥K ∨ IsSLThreeExc ↥K ∨
        IsSUThreeExc ↥K) → I271CaseA 3 K B ∨ IsStronglyBalancedIn 3 B K ∨ I271CaseC K B

@[expose] def I271AltDiv : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (p : ℕ) (K B : Subgroup X),
    I271Hyp p K B → I271Norm p K B → ∀ (n : ℕ) (hn : 5 ≤ n), I271AltType K n hn → p ∣ n →
      IsStronglyBalancedIn p B K

@[expose] def I271AltNdiv : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (p : ℕ) (K B : Subgroup X),
    I271Hyp p K B → I271Norm p K B → ∀ (n : ℕ) (hn : 5 ≤ n), I271AltType K n hn → ¬ p ∣ n →
      I271CaseA p K B

@[expose] def I271ChevPBal : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (p : ℕ) (K B : Subgroup X),
    I271Hyp p K B → I271Norm p K B → I271NotAlt K → I271LieType (· = p) K →
      ¬ (p = 3 ∧ IsLTwoTwentySeven (↥K ⧸ Subgroup.center ↥K) ∧ ¬ InducesInnerIn B K) →
        IsStronglyBalancedIn p B K

@[expose] def I271ChevPExc : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ K B : Subgroup X,
    I271Hyp 3 K B → I271Norm 3 K B → IsLTwoTwentySeven (↥K ⧸ Subgroup.center ↥K) →
      ¬ InducesInnerIn B K → I271CaseA 3 K B

@[expose] def I271SporGen : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (p : ℕ) (K B : Subgroup X),
    I271Hyp p K B → I271Norm p K B → ∀ name, I271SporType K name →
      ¬ (IsFiTwentyTwo ↥K ∧ p = 5) → ¬ (IsHatON ↥K ∧ p = 3) →
        I271CaseA p K B ∨ IsStronglyBalancedIn p B K

@[expose] def I271Fi22Aut : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsFiTwentyTwo Y →
    CFSG.Open.pRank 5 (⊤ : Subgroup (MulAut Y)) ≤ 2

@[expose] def I271AutBalanceON : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group) →
      ∀ A : Subgroup (MulAut S), IsElemAbelian 3 A → 3 ^ 4 ≤ Nat.card A →
        ∀ T : Subgroup (MulAut S), Nat.Coprime 3 (Nat.card T) →
          A ≤ Subgroup.normalizer (T : Set (MulAut S)) → T = ⊥

@[expose] def I271ONLow : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ K B : Subgroup X,
    I271Hyp 3 K B → I271Norm 3 K B → IsHatON ↥K → autOrderIn B K ≤ 3 ^ 3 →
      I271CaseA 3 K B ∨ I271CaseD K B

@[expose] def I271ChevQLThreeFour : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ K B : Subgroup X,
    I271Hyp 3 K B → I271Norm 3 K B → IsLThreeFour (↥K ⧸ Subgroup.center ↥K) →
      I271CaseA 3 K B ∨ I271CaseC K B

@[expose] def I271ChevQ : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (p : ℕ) (K B : Subgroup X),
    I271Hyp p K B → I271Norm p K B → I271NotAlt K → I271LieType (· ≠ p) K →
      ¬ (p = 3 ∧ IsLThreeFour (↥K ⧸ Subgroup.center ↥K)) →
        I271CaseA p K B ∨ IsStronglyBalancedIn p B K

structure I271Families : Prop where
  nnHatSixRank : I271NNHatSixRank
  autBalanceSix : I271AutBalanceAltSix
  nnOther : I271NNOther
  altDiv : I271AltDiv
  altNdiv : I271AltNdiv
  chevPBal : I271ChevPBal
  chevPExc : I271ChevPExc
  sporGen : I271SporGen
  fi22Aut : I271Fi22Aut
  autBalanceON : I271AutBalanceON
  onLow : I271ONLow
  chevQL34 : I271ChevQLThreeFour
  chevQ : I271ChevQ

section Cases

variable {X : Type} [Group X] [Finite X]

private theorem concl_of_a {p : ℕ} {K B : Subgroup X} (h : I271CaseA p K B) : I271Concl p K B :=
  Or.inl h

private theorem concl_of_b {p : ℕ} {K B : Subgroup X} (h : IsStronglyBalancedIn p B K) :
    I271Concl p K B :=
  Or.inr (Or.inl h)

private theorem concl_of_c {K B : Subgroup X} (h : I271CaseC K B) : I271Concl 3 K B :=
  Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))

private theorem concl_of_d {K B : Subgroup X} (h : I271CaseD K B) : I271Concl 3 K B :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h⟩)))

private theorem concl_of_e {K B : Subgroup X} (h : I271CaseE K B) : I271Concl 5 K B :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h⟩)))

theorem i271_normalizing (hXK : CFSG.Open.IsKGroup X) (hF : I271Families) {p : ℕ}
    {K B : Subgroup X} (hH : I271Hyp p K B) (hN : B ≤ Subgroup.normalizer (K : Set X)) :
    I271Concl p K B := by
  have hp := hH.prime
  have hBel : IsElemAbelian p B := hH.scp.2.1
  obtain ⟨r, hr⟩ := exists_pow_autOrderIn hp hBel hN
  by_cases hr1 : r ≤ 1
  ·
    refine concl_of_a ⟨hH.rank_four, isInGOne_of_autOrderIn_le (r := 1) hp hBel hN ?_ ?_⟩
    · rw [hr]
      exact Nat.pow_le_pow_right hp.pos hr1
    · have := hH.rank_four
      omega
  have h2 : p ^ 2 ≤ autOrderIn B K := by
    rw [hr]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  have hNorm : I271Norm p K B := ⟨hN, h2⟩
  by_cases hAlt : ∃ (n : ℕ) (hn : 5 ≤ n), I271AltType K n hn
  · obtain ⟨n, hn, he⟩ := hAlt
    by_cases hdiv : p ∣ n
    · exact concl_of_b (hF.altDiv X hXK p K B hH hNorm n hn he hdiv)
    · exact concl_of_a (hF.altNdiv X hXK p K B hH hNorm n hn he hdiv)
  obtain ⟨i, ⟨e⟩⟩ := hH.catalog
  cases i with
  | cyclic q hq =>
    exfalso
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_isQuasisimple
      (i116e_isQuasisimple hH.core hH.comp)
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn => exact absurd ⟨n, hn, ⟨e⟩⟩ hAlt
  | lie idx =>
    by_cases hc : idx.1.characteristic = p
    · by_cases hx : p = 3 ∧ IsLTwoTwentySeven (↥K ⧸ Subgroup.center ↥K) ∧ ¬ InducesInnerIn B K
      · obtain ⟨rfl, h27, hinn⟩ := hx
        exact concl_of_a (hF.chevPExc X hXK K B hH hNorm h27 hinn)
      · exact concl_of_b (hF.chevPBal X hXK p K B hH hNorm hAlt ⟨idx, ⟨e⟩, hc⟩ hx)
    · by_cases hx : p = 3 ∧ IsLThreeFour (↥K ⧸ Subgroup.center ↥K)
      · obtain ⟨rfl, hL⟩ := hx
        rcases hF.chevQL34 X hXK K B hH hNorm hL with h | h
        · exact concl_of_a h
        · exact concl_of_c h
      · rcases hF.chevQ X hXK p K B hH hNorm hAlt ⟨idx, ⟨e⟩, hc⟩ hx with h | h
        · exact concl_of_a h
        · exact concl_of_b h
  | sporadic name =>
    by_cases hFi : IsFiTwentyTwo ↥K ∧ p = 5
    ·
      obtain ⟨hFi, rfl⟩ := hFi
      have hle : autOrderIn B K ≤ 5 ^ 2 :=
        autOrderIn_le_pow_of_pRank hp hBel hN (hF.fi22Aut ↥K hFi)
      by_cases h5 : 5 ≤ CFSG.Open.pRank 5 B
      · exact concl_of_a ⟨hH.rank_four, isInGOne_of_autOrderIn_le (r := 2) hp hBel hN hle (by omega)⟩
      · have h4 := hH.rank_four
        exact concl_of_e ⟨hFi, by omega⟩
    · by_cases hON : IsHatON ↥K ∧ p = 3
      · obtain ⟨hON, rfl⟩ := hON
        by_cases h4 : 3 ^ 4 ≤ autOrderIn B K
        · obtain ⟨hperf, -, ⟨e'⟩⟩ := id hON
          exact concl_of_b (isStronglyBalancedIn_of_autBalanced hBel hperf (S := ↥K ⧸ Subgroup.center ↥K)
            (MulEquiv.refl _) h4 (hF.autBalanceON (↥K ⧸ Subgroup.center ↥K) ⟨e'⟩))
        · rcases hF.onLow X hXK K B hH hNorm hON (by
            have hlt : autOrderIn B K < 3 ^ 4 := not_le.1 h4
            rw [hr] at hlt ⊢
            have : r < 4 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
            exact Nat.pow_le_pow_right (by norm_num) (by omega)) with h | h
          · exact concl_of_a h
          · exact concl_of_d h
      · rcases hF.sporGen X hXK p K B hH hNorm name ⟨e⟩ hFi hON with h | h
        · exact concl_of_a h
        · exact concl_of_b h

end Cases

theorem input27_1K_of_families (T : Tables112) (TL : TableL2) (TT : Tables112Types)
    (hF : I271Families) : Input27_1K := by
  intro X _ _ hXK
  refine input27_1At_of_concl fun p K B hH => ?_
  by_cases hN : B ≤ Subgroup.normalizer (K : Set X)
  · exact i271_normalizing hXK hF hH hN
  ·
    obtain ⟨h3, -, -, -, htype⟩ := i112f_core T TL TT hXK hH.prime hH.odd hH.core hH.scp.2.1
      hH.rank_local hH.comp hN
    subst h3
    rcases htype with h | h | h | h | h | h
    · rcases hF.nnOther X hXK K B hH hN (Or.inl h) with h' | h' | h'
      · exact concl_of_a h'
      · exact concl_of_b h'
      · exact concl_of_c h'
    · obtain ⟨hperf, -, ⟨e'⟩⟩ := id h
      exact Or.inr (Or.inl (isStronglyBalancedIn_of_autBalanced hH.scp.2.1 hperf e'
        (hF.nnHatSixRank X hXK K B hH hN h) hF.autBalanceSix))
    · rcases hF.nnOther X hXK K B hH hN (Or.inr (Or.inl h)) with h' | h' | h'
      · exact concl_of_a h'
      · exact concl_of_b h'
      · exact concl_of_c h'
    · rcases hF.nnOther X hXK K B hH hN (Or.inr (Or.inr (Or.inl h))) with h' | h' | h'
      · exact concl_of_a h'
      · exact concl_of_b h'
      · exact concl_of_c h'
    · rcases hF.nnOther X hXK K B hH hN (Or.inr (Or.inr (Or.inr (Or.inl h)))) with h' | h' | h'
      · exact concl_of_a h'
      · exact concl_of_b h'
      · exact concl_of_c h'
    · rcases hF.nnOther X hXK K B hH hN (Or.inr (Or.inr (Or.inr (Or.inr h)))) with h' | h' | h'
      · exact concl_of_a h'
      · exact concl_of_b h'
      · exact concl_of_c h'

end CFSG.HardMathSupport.Solomon.Coordinator
