module

public import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSL
public import CFSG.LieType.SemisimpleCentralizers.HeldUnitaryComponents
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
public import CFSG.RankThree.PartTwo.Sec8.Item87ProofOrders

public section

namespace CFSG.LieType.SemisimpleCentralizers.Held

open CFSG.Open CFSG.Open.StatedAPI Matrix

theorem hct_exists_char_pow {M : Type} [Field M] [Finite M] {Q : ℕ} (hK : Nat.card M = Q ^ 2) :
    ∃ p : ℕ, CharP M p ∧ ∃ k : ℕ, p.Prime ∧ Q = p ^ k := by
  have := Fintype.ofFinite M
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' M
  rw [← Nat.card_eq_fintype_card, hK] at hcard
  have hdvd : Q ∣ p ^ (n : ℕ) := ⟨Q, by rw [← hcard]; ring⟩
  obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  exact ⟨p, hchar, k, hp, rfl⟩

theorem hct_heldSU_eq_statedSU {a Q : ℕ} {M : Type} [Field M] {τ : M ≃+* M}
    {hτ : ∀ x, τ (τ x) = x} (hτQ : ∀ x, τ x = x ^ Q) :
    heldSU a M τ hτ = StatedSU a Q M := by
  have hτf : (⇑τ) = fun x => x ^ Q := funext hτQ
  have hset : ((heldSU a M τ hτ : Subgroup (GL (Fin a) M)) : Set (GL (Fin a) M)) =
      {A : GL (Fin a) M | Matrix.GeneralLinearGroup.det A = 1 ∧
        ((A : Matrix (Fin a) (Fin a) M).map (· ^ Q))ᵀ * (A : Matrix (Fin a) (Fin a) M) = 1} := by
    ext A
    simp only [SetLike.mem_coe, heldSU, Subgroup.mem_inf, mem_heldGU, Set.mem_setOf_eq, hτf,
      mem_statedSL_iff, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
      and_comm]
  rw [CFSG.PGLModel.statedSU_eq_closure_det, ← hset, Subgroup.closure_eq]

theorem hct_comp_top_statedSU {a Q : ℕ} {M : Type} [Field M] [Finite M]
    (hK : Nat.card M = Q ^ 2) (H : Subgroup (GL (Fin a) M)) (hH : H = StatedSU a Q M)
    {X : Subgroup H} (hX : IsComponentOf X ⊤) : X = ⊤ := by
  subst hH
  obtain ⟨p, hchar, k, hp, rfl⟩ := hct_exists_char_pow hK
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hchar
  have h1 : 1 < Nat.card M := Finite.one_lt_card
  have hQ2 : 2 ≤ p ^ k := by
    by_contra hlt
    have hle1 : p ^ k ≤ 1 := by omega
    have hsq : (p ^ k) ^ 2 ≤ 1 := by
      have := Nat.pow_le_pow_left hle1 2
      simpa using this
    omega
  rcases Nat.lt_or_ge a 2 with ha | ha
  ·
    haveI : Subsingleton ↥(StatedSU a (p ^ k) M) := by
      haveI := hct_subsingleton_statedSL_of_le_one (K := M) (d := a) (by omega)
      refine ⟨fun x y => ?_⟩
      have h := Subsingleton.elim (α := ↥(StatedSL a M))
        ⟨x.1, statedSU_le_statedSL a (p ^ k) M x.2⟩ ⟨y.1, statedSU_le_statedSL a (p ^ k) M y.2⟩
      exact Subtype.ext (Subtype.mk.inj h)
    exact (hct_not_component_top_of_subsingleton hX).elim
  rcases Nat.lt_or_ge a 3 with ha3 | ha3
  ·
    have ha2 : a = 2 := by omega
    subst ha2
    rcases Nat.lt_or_ge (p ^ k) 4 with hsmall | hbig
    ·
      have hcard : Nat.card (StatedSU 2 (p ^ k) M) = p ^ k * ((p ^ k) ^ 2 - 1) :=
        CFSG.RankThree.SubgroupLists.card_statedSU_two (K := M) (r := p) (f := k) hK
      have hQ : p ^ k = 2 ∨ p ^ k = 3 := by omega
      rcases hQ with h | h
      · have hs : Group.IsSolvable ↥(StatedSU 2 (p ^ k) M) :=
          hct_isSolvable_of_natCard_eq (p := 2) (q := 3) (a := 1) (b := 1) Nat.prime_two
            Nat.prime_three (by norm_num) (by rw [hcard, h] <;> norm_num)
        exact (hct_not_component_top_of_isSolvable hs hX).elim
      · have hs : Group.IsSolvable ↥(StatedSU 2 (p ^ k) M) :=
          hct_isSolvable_of_natCard_eq (p := 2) (q := 3) (a := 3) (b := 1) Nat.prime_two
            Nat.prime_three (by norm_num) (by rw [hcard, h] <;> norm_num)
        exact (hct_not_component_top_of_isSolvable hs hX).elim
    ·
      have hF : Nat.card (CFSG.LieType.Steinberg.fixedSubfield M p k) = p ^ k :=
        CFSG.LieType.Steinberg.card_fixedSubfield hK
      obtain ⟨e⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two
        (K := M) (r := p) (f := k) hK
      have hSL : CFSG.Open.IsQuasisimple (StatedSL 2 (CFSG.LieType.Steinberg.fixedSubfield M p k)) :=
        hct_isQuasisimple_statedSL _ (by norm_num) (Or.inr (by rw [hF]; omega))
          (Or.inr (by rw [hF]; omega))
      let e' : ↥(StatedSU 2 (p ^ k) M) ≃*
          ↥(StatedSL 2 (CFSG.LieType.Steinberg.fixedSubfield M p k)) :=
        e.symm.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 _)
      exact hct_comp_eq_top_of_isQuasisimple (CFSG.Open.IsQuasisimple.of_mulEquiv e' hSL) hX
  ·
    by_cases h32 : a = 3 ∧ p ^ k = 2
    ·
      exfalso
      obtain ⟨rfl, h2⟩ := h32
      have hF : Nat.card M = (2 ^ 1) ^ 2 := by rw [hK, h2] <;> norm_num
      have hcard : Nat.card (StatedSU 3 (2 ^ 1) M) = 216 := by
        rw [CFSG.RankThree.PartTwo.Sec8.Item87Proof.card_statedSU_three_two hF]
        norm_num
      have hcard' : Nat.card (StatedSU 3 (p ^ k) M) = 216 := by
        rw [h2]
        simpa using hcard
      have hs : Group.IsSolvable ↥(StatedSU 3 (p ^ k) M) :=
        hct_isSolvable_of_natCard_eq (p := 2) (q := 3) (a := 3) (b := 3) Nat.prime_two
          Nat.prime_three (by norm_num) (by rw [hcard'] <;> norm_num)
      exact (hct_not_component_top_of_isSolvable hs hX).elim
    · have hnq : (a, p ^ k) ≠ (3, 2) := fun h => h32 ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2⟩
      have hperf : Group.IsPerfect (StatedSU a (p ^ k) M) :=
        CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK ha3 hnq
      have hsimp : IsSimpleGroup (StatedProj (StatedSU a (p ^ k) M)) :=
        CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU M p k hK a ha3 hnq
      exact hct_comp_eq_top_of_perfect_statedProj (StatedSU a (p ^ k) M) hperf hsimp hX

theorem SUComponentsTrivial_holds : SUComponentsTrivial := by
  unfold SUComponentsTrivial
  intro a Q M _ _ τ hτ hK hτQ X hX
  exact hct_comp_top_statedSU hK (heldSU a M τ hτ) (hct_heldSU_eq_statedSU hτQ) hX

end CFSG.LieType.SemisimpleCentralizers.Held

end
