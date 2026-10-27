module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYLeviBasic

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint

local instance e6CentralizerYLeviWeylNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

theorem yReflect_check :
    (∀ i : Fin Tag.E6.rank, (i = 1 ∨ i = 3) →
      reflect .E6 i yAlphaAS = yAlphaAS ∧ reflect .E6 i yBetaAS = yBetaAS) ∧
    reflect .E6 2 (reflect .E6 4 yAlphaAS) = yBetaAS ∧
    reflect .E6 2 (reflect .E6 4 yBetaAS) = yAlphaAS ∧
    reflect .E6 4 (reflect .E6 2 yAlphaAS) = yBetaAS ∧
    reflect .E6 4 (reflect .E6 2 yBetaAS) = yAlphaAS ∧
    reflect .E6 2 (Pi.single 4 1) = Pi.single 4 1 ∧ reflect .E6 4 (Pi.single 2 1) = Pi.single 2 1 ∧
    yAlphaAS - yBetaAS = Pi.single 2 1 - Pi.single 4 1 := by
  decide +kernel

section CharTwo

variable {τ : Tag} {K : Type} [Field K] [CharP K 2]

theorem weylElt_mul_canonicalRep_charTwo' (i : Fin τ.rank) (w : WeylGroup τ) :
    weylElt τ K i 1 * canonicalRep (coxeterSystem τ) K w =
      canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).simple i * w) := by
  rw [weylElt_mul_canonicalRep]
  split_ifs
  · rfl
  · rw [show (-1 : Kˣ) = 1 from Units.ext (CharTwo.neg_eq (1 : K)), torusElt_one, one_mul]

theorem canonicalRep_wordProd_mul_charTwo' (ω : List (Fin τ.rank)) (v : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).wordProd ω * v) =
      (ω.map fun i => weylElt τ K i 1).prod * canonicalRep (coxeterSystem τ) K v := by
  induction ω with
  | nil => rw [CoxeterSystem.wordProd_nil, one_mul, List.map_nil, List.prod_nil, one_mul]
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_assoc, ← weylElt_mul_canonicalRep_charTwo', ih,
      List.map_cons, List.prod_cons, mul_assoc]

theorem canonicalRep_mul_charTwo' (w v : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) K (w * v) =
      canonicalRep (coxeterSystem τ) K w * canonicalRep (coxeterSystem τ) K v := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [canonicalRep_wordProd_mul_charTwo', canonicalRep_wordProd hω]

end CharTwo

section Stab

variable {K : Type} [Field K] [CharP K 2]

theorem height_neg_of_coord_neg {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ)
    {k : Fin Tag.E6.rank} (hk : γ k < 0) : height γ < 0 := by
  rcases IsRoot.height_pos_or_neg hγ with h | h
  · have := (IsRoot.height_pos_iff hγ).1 h k
    omega
  · exact h

theorem smul_single_neg_partner {w : WeylGroup .E6}
    (hab : (w • yAlphaAS = yAlphaAS ∧ w • yBetaAS = yBetaAS) ∨
      (w • yAlphaAS = yBetaAS ∧ w • yBetaAS = yAlphaAS)) {i j : Fin Tag.E6.rank}
    (hij : (i = 2 ∧ j = 4) ∨ (i = 4 ∧ j = 2))
    (hi : height (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) < 0) :
    height (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) < 0 := by
  have hd := yReflect_check.2.2.2.2.2.2.2
  set d : Fin Tag.E6.rank → ℤ := Pi.single 2 1 - Pi.single 4 1 with hddef
  have hwd : w • d = d ∨ w • d = -d := by
    rw [← hd]
    rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [smul_sub, h1, h2]
    · right; rw [smul_sub, h1, h2, neg_sub]
  have hjr : IsRoot .E6 (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) :=
    IsRoot.smul (isRoot_single _ j) w
  have hγr : IsRoot .E6 (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) :=
    IsRoot.smul (isRoot_single _ i) w
  have hneg := (IsRoot.height_neg_iff hγr).1 hi
  have d2 : d 2 = 1 := by decide
  have d4 : d 4 = -1 := by decide
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have e : w • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) =
        w • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) - w • d := by
      rw [← smul_sub, hddef, sub_sub_cancel]
    rcases hwd with h | h
    · refine height_neg_of_coord_neg hjr (k := 2) ?_
      rw [e, h, Pi.sub_apply, d2]
      have := hneg 2
      omega
    · refine height_neg_of_coord_neg hjr (k := 4) ?_
      rw [e, h, Pi.sub_apply, Pi.neg_apply, d4]
      have := hneg 4
      omega
  · have e : w • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) =
        w • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) + w • d := by
      rw [← smul_add, hddef, add_sub_cancel]
    rcases hwd with h | h
    · refine height_neg_of_coord_neg hjr (k := 4) ?_
      rw [e, h, Pi.add_apply, d4]
      have := hneg 4
      omega
    · refine height_neg_of_coord_neg hjr (k := 2) ?_
      rw [e, h, Pi.add_apply, Pi.neg_apply, d2]
      have := hneg 2
      omega

theorem weylElt_one_mul_self_charTwo (i : Fin Tag.E6.rank) :
    weylElt .E6 K i 1 * weylElt .E6 K i 1 = 1 := by
  rw [← canonicalRep_simple (coxeterSystem .E6) K i, ← canonicalRep_mul_charTwo',
    CoxeterSystem.simple_mul_simple_self, canonicalRep_one]

theorem canonicalRep_mem_yLeviF4_of_length :
    ∀ (n : ℕ) (w : WeylGroup .E6), (coxeterSystem .E6).length w = n →
      w ∈ parabolicWeylGroup .E6 nodes16 →
      ((w • yAlphaAS = yAlphaAS ∧ w • yBetaAS = yBetaAS) ∨
        (w • yAlphaAS = yBetaAS ∧ w • yBetaAS = yAlphaAS)) →
      canonicalRep (coxeterSystem .E6) K w ∈ yLeviF4 K := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hw hwJ hab
  by_cases hw1 : w = 1
  · subst hw1
    rw [canonicalRep_one]
    exact one_mem _
  obtain ⟨i, hroot, hneg⟩ := (weyl_exchange_condition .E6).2.2.2 w hw1
  have hiJ : i ∈ nodes16 := by
    by_contra hi
    have h1 := smul_apply_of_mem_parabolicWeylGroup hwJ (Pi.single i 1) hi
    have h2 := (IsRoot.height_neg_iff hroot).1 hneg i
    rw [h1, Pi.single_eq_same] at h2
    omega
  have hlen1 : (coxeterSystem .E6).length (w * simple .E6 i) = n - 1 := by
    have := ((weyl_exchange_condition .E6).2.1 w i).1.2 ⟨hroot, hneg⟩
    omega
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, CoxeterSystem.length_eq_zero_iff] at hw
      exact absurd hw hw1
    · exact h0
  have hsi : simple .E6 i ∈ parabolicWeylGroup .E6 nodes16 := subset_closure ⟨i, hiJ, rfl⟩
  have hi4 : i = 1 ∨ i = 3 ∨ i = 2 ∨ i = 4 := by
    have key : ∀ i : Fin Tag.E6.rank, (i ≠ 0 ∧ i ≠ 5) → i = 1 ∨ i = 3 ∨ i = 2 ∨ i = 4 := by
      decide
    exact key i hiJ
  rcases hi4 with h | h | h | h
  · subst h
    have hab' : ((w * simple .E6 1) • yAlphaAS = yAlphaAS ∧ (w * simple .E6 1) • yBetaAS = yBetaAS) ∨
        ((w * simple .E6 1) • yAlphaAS = yBetaAS ∧ (w * simple .E6 1) • yBetaAS = yAlphaAS) := by
      rw [mul_smul, mul_smul, simple_smul, simple_smul, (yReflect_check.1 1 (Or.inl rfl)).1,
        (yReflect_check.1 1 (Or.inl rfl)).2]
      exact hab
    have hmem := ih (n - 1) (by omega) _ hlen1 (mul_mem hwJ hsi) hab'
    have e : w = w * simple .E6 1 * simple .E6 1 := by
      rw [mul_assoc, CoxeterSystem.simple_mul_simple_self, mul_one]
    rw [e, canonicalRep_mul_charTwo', canonicalRep_simple]
    exact mul_mem hmem (weylElt_mem_yLeviF4 (Or.inl rfl))
  · subst h
    have hab' : ((w * simple .E6 3) • yAlphaAS = yAlphaAS ∧ (w * simple .E6 3) • yBetaAS = yBetaAS) ∨
        ((w * simple .E6 3) • yAlphaAS = yBetaAS ∧ (w * simple .E6 3) • yBetaAS = yAlphaAS) := by
      rw [mul_smul, mul_smul, simple_smul, simple_smul, (yReflect_check.1 3 (Or.inr rfl)).1,
        (yReflect_check.1 3 (Or.inr rfl)).2]
      exact hab
    have hmem := ih (n - 1) (by omega) _ hlen1 (mul_mem hwJ hsi) hab'
    have e : w = w * simple .E6 3 * simple .E6 3 := by
      rw [mul_assoc, CoxeterSystem.simple_mul_simple_self, mul_one]
    rw [e, canonicalRep_mul_charTwo', canonicalRep_simple]
    exact mul_mem hmem (weylElt_mem_yLeviF4 (Or.inr rfl))
  all_goals
    obtain ⟨j, hij, hjJ, hsij⟩ : ∃ j : Fin Tag.E6.rank, ((i = 2 ∧ j = 4) ∨ (i = 4 ∧ j = 2)) ∧
        j ∈ nodes16 ∧ reflect .E6 i (Pi.single j 1) = Pi.single j 1 := by
      subst h
      first
      | exact ⟨4, Or.inl ⟨rfl, rfl⟩, ⟨by decide, by decide⟩, yReflect_check.2.2.2.2.2.1⟩
      | exact ⟨2, Or.inr ⟨rfl, rfl⟩, ⟨by decide, by decide⟩, yReflect_check.2.2.2.2.2.2.1⟩
    have hnegj := smul_single_neg_partner hab hij hneg
    have hjroot : IsRoot .E6 ((w * simple .E6 i) • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) :=
      IsRoot.smul (isRoot_single _ j) _
    have hw1j : (w * simple .E6 i) • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) =
        w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) := by
      rw [mul_smul, simple_smul, hsij]
    have hlen2 : (coxeterSystem .E6).length (w * simple .E6 i * simple .E6 j) = n - 2 := by
      have := ((weyl_exchange_condition .E6).2.1 (w * simple .E6 i) j).1.2
        ⟨hjroot, by rw [hw1j]; exact hnegj⟩
      omega
    have hsj : simple .E6 j ∈ parabolicWeylGroup .E6 nodes16 := subset_closure ⟨j, hjJ, rfl⟩
    have hswap : reflect .E6 i (reflect .E6 j yAlphaAS) = yBetaAS ∧
        reflect .E6 i (reflect .E6 j yBetaAS) = yAlphaAS := by
      rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨yReflect_check.2.1, yReflect_check.2.2.1⟩
      · exact ⟨yReflect_check.2.2.2.1, yReflect_check.2.2.2.2.1⟩
    have hab' : ((w * simple .E6 i * simple .E6 j) • yAlphaAS = yAlphaAS ∧
          (w * simple .E6 i * simple .E6 j) • yBetaAS = yBetaAS) ∨
        ((w * simple .E6 i * simple .E6 j) • yAlphaAS = yBetaAS ∧
          (w * simple .E6 i * simple .E6 j) • yBetaAS = yAlphaAS) := by
      rw [mul_smul, mul_smul, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul,
        simple_smul, hswap.1, hswap.2]
      rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨h2, h1⟩
      · exact Or.inl ⟨h2, h1⟩
    have hmem := ih (n - 2) (by omega) _ hlen2 (mul_mem (mul_mem hwJ hsi) hsj) hab'
    have e : w = w * simple .E6 i * simple .E6 j * simple .E6 j * simple .E6 i := by
      rw [mul_assoc (w * simple .E6 i) (simple .E6 j) (simple .E6 j),
        CoxeterSystem.simple_mul_simple_self, mul_one, mul_assoc w (simple .E6 i) (simple .E6 i),
        CoxeterSystem.simple_mul_simple_self, mul_one]
    have hji : weylElt .E6 K j 1 * weylElt .E6 K i 1 ∈ yLeviF4 K := by
      have h24 := weylElt_two_mul_weylElt_four_mem_yLeviF4 (K := K)
      rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have e' : weylElt .E6 K 4 1 * weylElt .E6 K 2 1 =
            (weylElt .E6 K 2 1 * weylElt .E6 K 4 1)⁻¹ := by
          rw [mul_inv_rev, inv_eq_of_mul_eq_one_left (weylElt_one_mul_self_charTwo 4),
            inv_eq_of_mul_eq_one_left (weylElt_one_mul_self_charTwo 2)]
        rw [e']
        exact inv_mem h24
      · exact h24
    rw [e, canonicalRep_mul_charTwo', canonicalRep_mul_charTwo', canonicalRep_simple,
      canonicalRep_simple, mul_assoc]
    exact mul_mem hmem hji

theorem canonicalRep_mem_yLeviF4 {w : WeylGroup .E6} (hwJ : w ∈ parabolicWeylGroup .E6 nodes16)
    (hab : (w • yAlphaAS = yAlphaAS ∧ w • yBetaAS = yBetaAS) ∨
      (w • yAlphaAS = yBetaAS ∧ w • yBetaAS = yAlphaAS)) :
    canonicalRep (coxeterSystem .E6) K w ∈ yLeviF4 K :=
  canonicalRep_mem_yLeviF4_of_length _ w rfl hwJ hab

end Stab

end CFSG.SeitzReduction.E6Pilot
