module

public import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
public import CFSG.Open.GLADefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2
public import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeHypSix
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTriDiag
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4Diag
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestInner
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Assembly CFSG.Open CFSG.StandardType

private theorem recipeLinear_inndiag {d N : ℕ} {Q : LargeEvenRawCont}
    (hd : (N - 1).Coprime d) (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧ I ⊆ LargeEvenInnSet R := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have hcard : Nat.card Kˣ = N - 1 := by rw [Nat.card_units, hK]
  exact matConjImage_gl_subset_inn (by rw [hcard]; exact hd)

private theorem recipeUnitary_inndiag {n d : ℕ} {Q : LargeEvenRawCont}
    (hd : (2 ^ n + 1).Coprime d) (h : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F => Q R I F ∧ I ⊆ LargeEvenInnSet R := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, TableB.matConjImage_gu_subset_inn hK hd⟩

private theorem recipeSymplectic_inndiag {m n : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic m (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic m (2 ^ n) false fun R _ I F =>
      Q R I F ∧ I ⊆ LargeEvenInnSet R := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  haveI : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ, matConjImage_gsp_subset_inn m⟩

private theorem recipeOmegaPlus_inndiag {m q : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaPlus m q Q) :
    LargeEvenRecipeOmegaPlus m q fun R _ I F => Q R I F ∧ I ⊆ LargeEvenInnSet R := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun _ hx => hx⟩

private theorem recipeOmegaMinus_inndiag {m q : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaMinus m q Q) :
    LargeEvenRecipeOmegaMinus m q fun R _ I F => Q R I F ∧ I ⊆ LargeEvenInnSet R := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ, fun _ hx => hx⟩

private theorem recipeSuzuki_inndiag {a : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSuzuki a Q) :
    LargeEvenRecipeSuzuki a fun R _ I F => Q R I F ∧ I ⊆ LargeEvenInnSet R := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun _ hx => hx⟩

private theorem recipeChevalley_inndiag {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {q : ℕ}
    {derived : Bool} {Q : LargeEvenRawCont}
    (hA : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q →
      LargeEvenChevIDImage A K (LargeEvenChevH A K derived) ⊆
        LargeEvenInnSet (LargeEvenCenterQuot (LargeEvenChevH A K derived)))
    (h : LargeEvenRecipeChevalley A q derived Q) :
    LargeEvenRecipeChevalley A q derived fun R _ I F =>
      Q R I F ∧ I ⊆ LargeEvenInnSet R := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, hA K hK⟩

@[expose] def rk2DiagIndex (lab : GLALabel) : ℕ :=
  match lab.tag with
  | .A => Nat.gcd (lab.rank + 1) (2 ^ lab.n - 1)
  | .twA => Nat.gcd (lab.rank + 1) (2 ^ lab.n + 1)
  | .E6 => Nat.gcd 3 (2 ^ lab.n - 1)
  | .twE6 => Nat.gcd 3 (2 ^ lab.n + 1)
  | _ => 1

@[expose] def Rk2DiagIndexInput : Prop :=
  ∀ (lab : GLALabel), GLAInLambda2 lab →
    (lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .E6 ∨ lab.tag = .twE6 ∨
      lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ rk2DiagIndex lab →
      Rk2LabelAll lab fun R _ I _ => ∀ E : Subgroup (MulAut R),
        E ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) → IsPGroup p E →
          E ≤ (MulAut.conj : R →* MulAut R).range

section Certificates


private theorem recipeTwF4Inherited_inndiag {a : ℕ} {Q : LargeEvenRawCont} (ha : 1 ≤ a)
    (h : LargeEvenRecipeTwF4Inherited a Q) :
    LargeEvenRecipeTwF4Inherited a fun R _ I F => Q R I F ∧ I ⊆ LargeEvenInnSet R := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have ha0 : a ≠ 0 := by omega
  refine ⟨K, inferInstance, inferInstance, hK, ?_⟩
  simp only [if_neg ha0] at hQ ⊢
  exact ⟨hQ, chevIDImage_subset_inn_twF4 ha K hK⟩

theorem rk2_inndiag_subset_inn_of_notDerived {lab : GLALabel} (hlab : GLAInLambda2 lab)
    (htag : lab.tag ≠ .A ∧ lab.tag ≠ .twA ∧ lab.tag ≠ .E6 ∧ lab.tag ≠ .twE6)
    (hB2der : lab.tag ≠ .B2der) (hG2der : lab.tag ≠ .G2der)
    (htwF4der : lab.tag ≠ .twF4der) :
    Rk2LabelAll lab fun R _ I _ => I ⊆ Set.range (MulAut.conj : R →* MulAut R) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only [GLAInLambda2] at hlab
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  cases t
  · exact (htag.1 rfl).elim
  · exact (htag.2.1 rfl).elim
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    exact recipeSymplectic_inndiag hQ
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    exact recipeSymplectic_inndiag hQ
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    by_cases hl : l = 3
    · rw [if_pos hl] at hQ ⊢
      have hodd : Odd (2 ^ n - 1) := ggOdd_two_pow_sub_one hn
      exact recipeLinear_inndiag (by
        simpa using Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hodd)) hQ
    · rw [if_neg hl] at hQ ⊢
      exact recipeOmegaPlus_inndiag hQ
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    by_cases hl2 : l = 2
    · rw [if_pos hl2] at hQ ⊢
      have hn2 : 1 ≤ n * 2 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by norm_num))
      exact recipeLinear_inndiag (Nat.coprime_two_right.mpr (by
        rw [← pow_mul]
        exact ggOdd_two_pow_sub_one hn2)) hQ
    · rw [if_neg hl2] at hQ ⊢
      by_cases hl3 : l = 3
      · rw [if_pos hl3] at hQ ⊢
        have hodd : Odd (2 ^ n + 1) := CFSG.RankThree.PartTwo.Census.odd_two_pow_add_one hn
        exact recipeUnitary_inndiag (by
          simpa using Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hodd)) hQ
      · rw [if_neg hl3] at hQ ⊢
        exact recipeOmegaMinus_inndiag hQ
  · exact (htag.2.2.1 rfl).elim
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    exact recipeChevalley_inndiag (fun K _ _ hK => by
      haveI : CharP K 2 := charP_two_of_card hK
      exact chevIDImage_subset_inn_of_top (τ := .E7)
        (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanE7_adj
          (TableB.exists_sq_eq_of_charTwo K))) hQ
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    exact recipeChevalley_inndiag (fun K _ _ _ =>
      chevIDImage_subset_inn_of_top (τ := .E8)
        (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanE8_inv
          fun s => ⟨s, pow_one s⟩)) hQ
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    exact recipeChevalley_inndiag (fun K _ _ _ =>
      chevIDImage_subset_inn_of_top (τ := .F4)
        (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanF4_inv
          fun s => ⟨s, pow_one s⟩)) hQ
  · exact (htag.2.2.2 rfl).elim
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    exact recipeTwisted_and (P := fun R _ I _ => I ⊆ LargeEvenInnSet R)
      (fun K _ _ hK => TableBExcSmallRest.chevIDImage_subset_inn_triD4 hlab.1 K hK) hQ
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    exact recipeChevalley_inndiag (fun K _ _ _ =>
      chevIDImage_subset_inn_of_top (τ := .G2)
        (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanG2_inv
          fun s => ⟨s, pow_one s⟩)) hQ
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    exact recipeSuzuki_inndiag hQ
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨-, -, hn3⟩ := hlab.2
    have hn3' : 3 ≤ n := by simpa using hn3
    have ha : 1 ≤ (n - 1) / 2 := by
      have h2 : 2 ≤ n - 1 := Nat.le_sub_one_of_lt (by omega : 2 < n)
      exact Nat.succ_le_of_lt (Nat.div_pos h2 (by norm_num))
    exact recipeTwF4Inherited_inndiag ha hQ
  · exact (hB2der rfl).elim
  · exact (hG2der rfl).elim
  · exact (htwF4der rfl).elim

theorem rk2_closure_inndiag_eq_inn {lab : GLALabel} (hlab : GLAInLambda2 lab)
    (htag : lab.tag ≠ .A ∧ lab.tag ≠ .twA ∧ lab.tag ≠ .E6 ∧ lab.tag ≠ .twE6)
    (hB2der : lab.tag ≠ .B2der) (hG2der : lab.tag ≠ .G2der)
    (htwF4der : lab.tag ≠ .twF4der) :
    Rk2LabelAll lab fun R _ I _ =>
      Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) =
        (MulAut.conj : R →* MulAut R).range := by
  intro Q hQ
  refine Canonical.largeEvenRawDatum_mono (fun R _ I F hq => ?_)
    (rk2_inndiag_subset_inn_of_notDerived hlab htag hB2der hG2der htwF4der Q hQ)
  obtain ⟨hq, hI⟩ := hq
  refine ⟨hq, ?_⟩
  apply le_antisymm
  · rw [Subgroup.closure_le]
    exact Set.union_subset hI (fun x hx => hx)
  · intro x hx
    exact Subgroup.subset_closure (Set.mem_union_right _ hx)

theorem rk2_pSubgroup_le_inn (hinput : Rk2DiagIndexInput) {lab : GLALabel}
    (hlab : GLAInLambda2 lab) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : ¬ p ∣ rk2DiagIndex lab) :
    Rk2LabelAll lab fun R _ I _ => ∀ E : Subgroup (MulAut R),
      E ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) → IsPGroup p E →
        E ≤ (MulAut.conj : R →* MulAut R).range := by
  by_cases hhard : (lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .E6 ∨ lab.tag = .twE6 ∨
      lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der)
  · exact hinput lab hlab hhard p hp hp2 hpd
  · have htag : lab.tag ≠ .A ∧ lab.tag ≠ .twA ∧ lab.tag ≠ .E6 ∧ lab.tag ≠ .twE6 := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro h; exact hhard (Or.inl h)
      · intro h; exact hhard (Or.inr (Or.inl h))
      · intro h; exact hhard (Or.inr (Or.inr (Or.inl h)))
      · intro h; exact hhard (Or.inr (Or.inr (Or.inr (Or.inl h))))
    have hB2der : lab.tag ≠ .B2der := fun h => hhard (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    have hG2der : lab.tag ≠ .G2der :=
      fun h => hhard (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    have htwF4der : lab.tag ≠ .twF4der :=
      fun h => hhard (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
    intro Q hQ
    refine Canonical.largeEvenRawDatum_mono (fun R _ I F hq => ?_)
      (rk2_closure_inndiag_eq_inn hlab htag hB2der hG2der htwF4der Q hQ)
    obtain ⟨hq, hI⟩ := hq
    exact ⟨hq, fun E hE _ => by rw [hI] at hE; exact hE⟩

theorem rk2_card_le_of_le_inndiag (hinput : Rk2DiagIndexInput) {lab : GLALabel}
    (hlab : GLAInLambda2 lab) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : ¬ p ∣ rk2DiagIndex lab) :
    Rk2LabelAll lab fun R _ I _ => ∀ (hfin : Finite R), IsSimpleGroup R →
      ∀ E : Subgroup (MulAut R),
        E ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) →
          IsElemAbelian p E →
            Nat.card E ≤ p ^ @CFSG.Open.pRank p R _ hfin (⊤ : Subgroup R) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro Q hQ
  refine Canonical.largeEvenRawDatum_mono (fun R _ I F hq => ?_)
    (rk2_pSubgroup_le_inn hinput hlab hp hp2 hpd Q hQ)
  obtain ⟨hq, hEinn⟩ := hq
  refine ⟨hq, fun hfin hs E hE hEel => ?_⟩
  haveI : Finite R := hfin
  have hInn : E ≤ (MulAut.conj : R →* MulAut R).range := hEinn E hE hEel.isPGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R) with hZ | hZ
  · have hconj : Function.Injective (MulAut.conj : R →* MulAut R) :=
      mulAut_conj_injective hZ
    let E' : Subgroup R := E.comap (MulAut.conj : R →* MulAut R)
    have hE'el : IsElemAbelian p E' := by
      constructor
      · refine ⟨⟨fun x y => ?_⟩⟩
        apply Subtype.ext
        apply hconj
        rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
        exact congrArg (fun z : E => (z : MulAut R)) (hEel.1.is_comm.comm
          ⟨MulAut.conj (x : R), x.2⟩ ⟨MulAut.conj (y : R), y.2⟩)
      · intro x hx
        apply hconj
        rw [map_pow]
        rw [hEel.2 (MulAut.conj x) hx, map_one]
    have hmap : E'.map (MulAut.conj : R →* MulAut R) = E := Subgroup.map_comap_eq_self hInn
    have hcard : Nat.card E' = Nat.card E := by
      rw [← hmap, Subgroup.card_map_of_injective hconj]
    have hE'p : IsPGroup p E' := hE'el.isPGroup
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE'p
    have hk' : Nat.card E = p ^ k := by rw [← hcard, hk]
    have hle : k ≤ CFSG.Open.pRank p (⊤ : Subgroup R) :=
      CFSG.SectionRank.le_pRank hp.one_lt le_top hE'el hk
    rw [hk']
    exact Nat.pow_le_pow_right hp.pos hle
  · have hcenter : Subgroup.center R = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
      · exfalso
        exact (bot_ne_top : (⊥ : Subgroup R) ≠ ⊤) (h.symm.trans hZ)
      · exact h
    have hInnBot : (MulAut.conj : R →* MulAut R).range = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨r, rfl⟩
      ext s
      rw [MulAut.conj_apply, MulAut.one_apply]
      have hr : r ∈ Subgroup.center R := by rw [hcenter]; exact Subgroup.mem_top r
      have hcomm := Subgroup.mem_center_iff.mp hr s
      rw [show r * s = s * r from hcomm.symm]
      group
    have hEbot : E = ⊥ := by
      rw [eq_bot_iff]
      intro e he
      have : e ∈ (⊥ : Subgroup (MulAut R)) := by rw [← hInnBot]; exact hInn he
      exact this
    rw [hEbot, Subgroup.card_bot]
    exact Nat.one_le_pow _ _ hp.pos

end Certificates

end CFSG.LocalAnalysis.GLTheoremA
