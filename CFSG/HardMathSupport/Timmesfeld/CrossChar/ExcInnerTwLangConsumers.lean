module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidSetup
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSevenClasses
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Timmesfeld.ExceptionalOrders
open scoped Matrix

theorem eval_charpoly_neg_one {r : ℕ} (t : ℤ) :
    (-1 : Matrix (Fin r) (Fin r) ℤ).charpoly.eval t = (t + 1) ^ r := by
  rw [Matrix.eval_charpoly, sub_neg_eq_add,
    show Matrix.scalar (Fin r) t + 1 = Matrix.scalar (Fin r) (t + 1) by rw [map_add, map_one],
    Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

theorem natAbs_eval_charpoly_neg_one {r : ℕ} (q : ℕ) :
    ((-1 : Matrix (Fin r) (Fin r) ℤ).charpoly.eval (q : ℤ)).natAbs = (q + 1) ^ r := by
  rw [eval_charpoly_neg_one, Int.natAbs_pow,
    show (q : ℤ) + 1 = ((q + 1 : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast]

theorem dvd_add_one_regime {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (q : ℕ) (hpq : p ∣ q + 1) :
    ¬ p ∣ q ∧ p ∣ q + 1 ∧ 4 ≤ q := by
  refine ⟨fun h => hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 hpq)), hpq, ?_⟩
  have := Nat.le_of_dvd (Nat.succ_pos q) hpq
  omega

section Forall

theorem langTorusPlaneBalance_forall_of_ne {τ : Tag} {w₀ : WeylGroup τ} {p : ℕ} {Q : ℕ → Prop}
    (hNeg : ∀ w : WeylGroup τ, w ≠ w₀ → LangTorusPlaneBalance τ w p Q)
    (h0 : LangTorusPlaneBalance τ w₀ p Q) (w : WeylGroup τ) : LangTorusPlaneBalance τ w p Q := by
  by_cases hw : w = w₀
  · subst hw
    exact h0
  · exact hNeg w hw

end Forall

section Lang

theorem isInnerLocallyBalanced_adjoint_of_negBalance {τ : Tag} (d : ℕ)
    (hτ : (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1)) {w : WeylGroup τ}
    (hw : ∀ u : Fin τ.rank → ℤ, w • u = -u) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {Q : ℕ → Prop} (hL : LangTorusPlaneBalance τ w p Q) (K : Type) [Field K] [Finite K]
    (hQ : Q (Nat.card K))
    (hord : (Nat.card (adjointGroup τ K)).factorization p ≤
      τ.rank * (Nat.card K + 1).factorization p + 1) :
    IsInnerLocallyBalanced p (adjointGroup τ K) := by
  refine isInnerLocallyBalanced_adjoint_of_langTorus d (Or.inr hτ) (M := -1)
    (fun u => by rw [hw u, Matrix.neg_mulVec, Matrix.one_mulVec]) (n := 2) two_ne_zero
    (by rw [neg_one_sq]) hp hp3 hL K hQ ?_ ?_
  · rw [eval_charpoly_neg_one]
    positivity
  · rw [natAbs_eval_charpoly_neg_one, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    exact hord

theorem isInnerLocallyBalanced_adjointE8_of_dvd_add_one_of_negBalance {p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hL : LangTorusPlaneBalance Tag.E8 e8Neg p fun q => p ∣ q + 1) (K : Type)
    [Field K] [Finite K] (hpq : p ∣ Nat.card K + 1) :
    IsInnerLocallyBalanced p (adjointGroup Tag.E8 K) :=
  isInnerLocallyBalanced_adjoint_of_negBalance 1 (Or.inr ⟨rfl, rfl⟩) e8Neg_smul hp (by omega) hL
    K hpq (factorization_card_adjointGroup_E8_le_of_dvd_add_one K hp hp7 hpq)

theorem factorization_card_adjointGroup_E7_le_of_dvd_add_one (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hpq : p ∣ Nat.card K + 1) :
    (Nat.card (adjointGroup Tag.E7 K)).factorization p ≤
      7 * (Nat.card K + 1).factorization p + 1 := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hp2 : p ≠ 2 := by omega
  have hpK : ¬ p ∣ Nat.card K := (dvd_add_one_regime hp (by omega) _ hpq).1
  have hpK1 : ¬ p ∣ Nat.card K - 1 := fun h => by
    have h1 : p ∣ Nat.card K + 1 - (Nat.card K - 1) := Nat.dvd_sub hpq h
    rw [show Nat.card K + 1 - (Nat.card K - 1) = 2 by omega] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1)
  have hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 2 := by
    have : Fact p.Prime := ⟨hp⟩
    have h0 : ((Nat.card K + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpq
    rw [Nat.cast_add, Nat.cast_one] at h0
    have h1 := orderOf_neg_one (R := ZMod p)
    simp only [ZMod.ringChar_zmod_n, hp2, ite_false] at h1
    rw [eq_neg_of_add_eq_zero_left h0]
    exact h1
  have hsq : (Nat.card K ^ 2 - 1).factorization p = (Nat.card K + 1).factorization p := by
    have h1 : Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
      have : 1 ≤ Nat.card K := by omega
      zify [this, Nat.one_le_pow 2 _ (by omega : 0 < Nat.card K)]
      ring
    rw [h1, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpK1, zero_add]
  have hlte : ∀ k : ℕ, k ≠ 0 → p ^ (Nat.card K ^ (2 * k) - 1).factorization p =
      p ^ (Nat.card K + 1).factorization p * p ^ k.factorization p := fun k hk => by
    rw [ordProj_pow_sub_one_of_dvd hp hp2 hpK hq2 hord hk, hsq]
  have h := ordProj_card_adjointGroup_E (τ := Tag.E7) (K := K) (by simp) hp (by omega) hpK
  simp only [degreesE, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  rw [hlte 1 one_ne_zero, hlte 3 (by norm_num), hlte 4 (by norm_num), hlte 5 (by norm_num),
    hlte 6 (by norm_num), hlte 7 (by norm_num), hlte 9 (by norm_num)] at h
  have hnd : ∀ k ∈ ([1, 3, 4, 5, 6, 9] : List ℕ), ¬ p ∣ k := by
    intro k hk hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    have hle : p ≤ k := Nat.le_of_dvd (by rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num) hdvd
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals interval_cases p <;> first | omega | (norm_num at hp)
  rw [ordProj_eq_one_of_not_dvd' (hnd 1 (by simp)), ordProj_eq_one_of_not_dvd' (hnd 3 (by simp)),
    ordProj_eq_one_of_not_dvd' (hnd 4 (by simp)), ordProj_eq_one_of_not_dvd' (hnd 5 (by simp)),
    ordProj_eq_one_of_not_dvd' (hnd 6 (by simp)), ordProj_eq_one_of_not_dvd' (hnd 9 (by simp))] at h
  have h7 : (7 : ℕ).factorization p ≤ 1 := by
    rcases eq_or_ne p 7 with rfl | hne
    · rw [Nat.Prime.factorization_self (by norm_num)]
    · rw [Nat.factorization_eq_zero_of_not_dvd fun hd =>
        hne ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hd)]
      norm_num
  have h' : (Nat.card (adjointGroup Tag.E7 K)).factorization p =
      7 * (Nat.card K + 1).factorization p + (7 : ℕ).factorization p := by
    refine Nat.pow_right_injective hp.two_le ?_
    change p ^ _ = p ^ _
    rw [h]
    ring
  omega

theorem isInnerLocallyBalanced_adjointE7_of_dvd_add_one_of_negBalance {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hL : LangTorusPlaneBalance Tag.E7 e7Neg p fun q => p ∣ q + 1) (K : Type)
    [Field K] [Finite K] (hpq : p ∣ Nat.card K + 1) :
    IsInnerLocallyBalanced p (adjointGroup Tag.E7 K) := by
  refine isInnerLocallyBalanced_adjoint_of_negBalance 2 (Or.inl ⟨rfl, rfl⟩) e7Neg_smul hp
    (by omega) hL K hpq ?_
  rcases eq_or_lt_of_le hp5 with rfl | h6
  · exact (Proving.factorization_five_card_adjointGroup_E7_of_dvd_add_one K hpq).le
  · refine factorization_card_adjointGroup_E7_le_of_dvd_add_one K hp ?_ hpq
    rcases (show p = 6 ∨ 7 ≤ p by omega) with rfl | h7
    · norm_num at hp
    · exact h7

theorem isInnerLocallyBalanced_adjointF4_of_dvd_add_one_of_negBalance {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hL : LangTorusPlaneBalance Tag.F4 f4Neg p fun q => p ∣ q + 1) (K : Type)
    [Field K] [Finite K] (hpq : p ∣ Nat.card K + 1) :
    IsInnerLocallyBalanced p (adjointGroup Tag.F4 K) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL Tag.F4 K) := finite_modGL
  obtain ⟨Fr, hFr, g0, hg0C, hg0⟩ := exists_lang_data_F4 K
  set L := AlgebraicClosure K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set n := canonicalRep (coxeterSystem Tag.F4) L f4Neg with hn
  set ι : adjointGroup Tag.F4 K →* ModGL Tag.F4 L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup Tag.F4 K).subtype with hι
  have hιinj : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hK0 : ((Nat.card K : ℕ) : L) = 0 := by
    have : Fintype K := Fintype.ofFinite K
    rw [← map_natCast (algebraMap K L), Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero K,
      map_zero]
  have : NeZero (((Nat.card K + 1 : ℕ)) : L) := ⟨by
    rw [Nat.cast_add, hK0, zero_add, Nat.cast_one]
    exact one_ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L (Nat.card K + 1)
  set ζu : Lˣ := (hζ.isUnit (by omega)).unit with hζu
  have hζu' : IsPrimitiveRoot ζu (Nat.card K + 1) :=
    IsPrimitiveRoot.coe_units_iff.1 (by simpa [hζu] using hζ)
  have hord : orderOf ζu = Nat.card K + 1 := hζu'.eq_orderOf.symm
  obtain ⟨H₀, hH₀T, hH₀card⟩ := exists_le_twistedTorus_card (L := L)
    (rootDiagUnit_mem_torusGroup_of_unimodular exists_mul_cartan_F4.choose_spec) f4Neg_smul hFr
    hζu'.pow_eq_one
  rw [hord] at hH₀card
  set X := H₀.map (MulAut.conj g0).toMonoidHom with hX
  have hXι : X ≤ ι.range := by
    rw [hι, MonoidHom.range_comp, Subgroup.range_subtype,
      ← (CFSG.RankThree.Chevalley.G2_F4_exact_finite_field_fixed_root_matrices Tag.F4 (Or.inr rfl)
        K L Fr hFr).1,
      ← map_conj_twModel hg0C hg0]
    exact Subgroup.map_mono (hH₀T.trans (twistedTorus_le_twModel n Fr))
  set S : Subgroup (adjointGroup Tag.F4 K) := X.comap ι with hS
  have hScard : Nat.card S = (Nat.card K + 1) ^ Tag.F4.rank := by
    have hmap : S.map ι = X := by
      rw [hS, Subgroup.map_comap_eq, inf_eq_right.2 hXι]
    rw [← Subgroup.card_map_of_injective hιinj, hmap, hX,
      Subgroup.card_map_of_injective (MulAut.conj g0).injective, hH₀card]
  have hfac : (Nat.card (⊤ : Subgroup (adjointGroup Tag.F4 K))).factorization p ≤
      (Nat.card S).factorization p + 1 := by
    rw [Subgroup.card_top, card_adjointGroup_F4, factorization_ordF4_of_dvd_add_one hp hp5 hq2 hpq,
      hScard, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      show Tag.F4.rank = 4 from rfl]
    omega
  refine isInnerLocallyBalanced_of_large_conj hp
    (mulAut_conj_injective_adjointGroup (τ := Tag.F4) (K := K))
    (fun x => baseChangeGL (algebraMap K L) (x : ModGL Tag.F4 K) ∈
      (twistedTorusOf n (Units.map (entrywiseHom Fr))).map (MulAut.conj g0).toMonoidHom)
    (fun A hA => ?_) (fun D₁ hpow₁ hcard₁ hP₁ H hH =>
      hL K hpq Fr hFr g0 hg0C hg0 D₁ hpow₁ hcard₁ hP₁ H hH)
  obtain ⟨c, -, E, hEA, hEcard, hEH⟩ := exists_large_conj_le_of_sylow (le_top : S ≤ ⊤)
    (le_top : A ≤ ⊤) hA hfac
  exact ⟨c, E, hEA, hEcard, fun x hx => Subgroup.map_mono hH₀T (hEH x hx)⟩

theorem f4InnerResidual_of_negBalance
    (hL : ∀ p : ℕ, p.Prime → 5 ≤ p → LangTorusPlaneBalance Tag.F4 f4Neg p fun q => p ∣ q + 1)
    (h3 : F4InnerResidualThree) : F4InnerResidual := by
  intro K _ _ p hp hp2 hpK D hD hcard hDin hcase H hH hDH
  rcases eq_three_or_five_le hp hp2 with rfl | h5
  · exact h3 K hpK D hD hcard hDin (hcase.imp id fun h => h.2) H hH hDH
  · rcases hcase with h1 | ⟨rfl, -⟩
    · exact isInnerLocallyBalanced_adjointF4_of_dvd_add_one_of_negBalance hp h5 (hL p hp h5) K h1
        D hD hcard hDin H hH hDH
    · omega

end Lang

section Components

theorem langTorusPlaneBalance_neg_dvd_add_one {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8)
    {w : WeylGroup τ} (hw : ∀ u : Fin τ.rank → ℤ, w • u = -u) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hsub : LangSubnormal) (hin : LangComponentsQuasisimple .inner)
    (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
    (hex : LangComponentsQuasisimple .exc) :
    LangTorusPlaneBalance τ w p fun q => p ∣ q + 1 :=
  langTorusPlaneBalance_neg_of_components hτ hw hp (by omega)
    (fun q _ hq => dvd_add_one_regime hp hp5 q hq) hsub hin hsu htw hex

end Components

section Families

theorem crossCharInnerAt_E8_dvd_add_one_of_negBalance
    (hL : ∀ p : ℕ, p.Prime → 7 ≤ p → LangTorusPlaneBalance Tag.E8 e8Neg p fun q => p ∣ q + 1) :
    CrossCharInnerAt .E8 fun idx p =>
      (∃ q : TauCeti.PrimePower, idx.1 = .E8 q ∧ p ∣ q.card + 1) ∧ 7 ≤ p := by
  rintro ⟨d, hv⟩ _ p hp _ _ ⟨⟨q, hd, hpq⟩, hp7⟩
  change d = _ at hd
  subst hd
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  rw [← hK] at hpq
  exact (isInnerLocallyBalanced_adjointE8_of_dvd_add_one_of_negBalance hp hp7 (hL p hp hp7) K
    hpq).of_mulEquiv e

theorem crossCharInnerAt_E8_seven_of_classes_negBalance
    (hL : ∀ p : ℕ, p.Prime → 7 ≤ p → LangTorusPlaneBalance Tag.E8 e8Neg p fun q => p ∣ q + 1)
    (h1 : InnerPlaneBalanceAtP .E8 1 fun p => p = 7) (h3 : InnerPlaneBalanceAt .E8 3)
    (h4 : InnerPlaneBalanceAt .E8 4) (h6 : InnerPlaneBalanceAt .E8 6) :
    CrossCharInnerAt .E8 fun idx p => (∃ q : TauCeti.PrimePower, idx.1 = .E8 q ∧
      3 ≤ degCount Tag.E8 (orderOf ((q.card : ℕ) : ZMod p))) ∧ 7 ≤ p := by
  rintro ⟨d, hv⟩ hk p hp hp2 hc ⟨⟨q, hq, hdeg⟩, hp7⟩
  change d = _ at hq
  subst hq
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hq1 : 1 ≤ q.card := Nat.one_le_iff_ne_zero.2 (TauCeti.PrimePower.card_def q ▸
    pow_ne_zero _ q.prime_p.ne_zero)
  rcases degCount_E8_ge_three hdeg with he | he | he | he | he
  · by_cases h7 : p = 7
    · exact isInnerLocallyBalanced_of_innerPlaneBalanceAtP (k := .E8) h1 q hv hp hp7 h7 hpq he
    · exact crossCharInnerAt_E8_dvd_sub_one _ ⟨q, rfl⟩ p hp hp2 hc
        ⟨q, rfl, eleven_le_of_prime_seven_le_ne hp hp7 h7, dvd_sub_one_of_orderOf_eq_one hq1 he⟩
  · exact crossCharInnerAt_E8_dvd_add_one_of_negBalance hL _ ⟨q, rfl⟩ p hp hp2 hc
      ⟨⟨q, rfl, dvd_add_one_of_orderOf_eq_two hp he⟩, hp7⟩
  · exact isInnerLocallyBalanced_of_innerPlaneBalanceAtP (k := .E8)
      (h3.atP fun _ => True) q hv hp hp7 trivial hpq he
  · exact isInnerLocallyBalanced_of_innerPlaneBalanceAtP (k := .E8)
      (h4.atP fun _ => True) q hv hp hp7 trivial hpq he
  · exact isInnerLocallyBalanced_of_innerPlaneBalanceAtP (k := .E8)
      (h6.atP fun _ => True) q hv hp hp7 trivial hpq he

theorem crossCharInnerAt_E8_five_of_toral_negBalance (htor : E8FiveToralPlane)
    (hSplit : ∀ w : WeylGroup Tag.E8, LangTorusPlaneBalance Tag.E8 w 5 fun q => 5 ∣ q - 1)
    (hNeg : ∀ w : WeylGroup Tag.E8, LangTorusPlaneBalance Tag.E8 w 5 fun q => 5 ∣ q + 1)
    (hFour : LangTorusPlaneBalance Tag.E8 e8PhiFourWeyl 5 fun q => 5 ∣ q ^ 2 + 1) :
    CrossCharInnerAt .E8 fun _ p => p = 5 := by
  rintro ⟨d, hv⟩ hk p hp hp2 hc rfl
  obtain ⟨q, hq⟩ : ∃ q, d = TauCeti.LieTypeIndex.E8 q := hk
  subst hq
  have hpq : 5 ≠ q.p := fun h => hc (by simp [h])
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have h5 : ¬ 5 ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  refine IsInnerLocallyBalanced.of_mulEquiv e ?_
  rcases five_dvd_sq_sub_one_or_sq_add_one h5 with h | h
  · rcases five_dvd_sq_sub_one_iff_or.1 h with h1 | h1
    · exact isInnerLocallyBalanced_adjointE8_five_of_toral htor hSplit K h5 h1
    · exact isInnerLocallyBalanced_adjointE8_five_of_toral htor hNeg K h5 h1
  · exact isInnerLocallyBalanced_adjointE8_five_of_dvd_sq_add_one hFour K h

theorem crossCharInnerAt_E8_five_of_parts_negBalance (htor : E8FiveToralPlane)
    (hSplit : ∀ w : WeylGroup Tag.E8, LangTorusPlaneBalance Tag.E8 w 5 fun q => 5 ∣ q - 1)
    (hNeg : ∀ w : WeylGroup Tag.E8, w ≠ e8Neg →
      LangTorusPlaneBalance Tag.E8 w 5 fun q => 5 ∣ q + 1)
    (h0 : LangTorusPlaneBalance Tag.E8 e8Neg 5 fun q => 5 ∣ q + 1)
    (hFour : LangTorusPlaneBalance Tag.E8 e8PhiFourWeyl 5 fun q => 5 ∣ q ^ 2 + 1) :
    CrossCharInnerAt .E8 fun _ p => p = 5 :=
  crossCharInnerAt_E8_five_of_toral_negBalance htor hSplit
    (langTorusPlaneBalance_forall_of_ne hNeg h0) hFour

theorem crossCharInnerAt_E7_five_of_negBalance
    (hL : LangTorusPlaneBalance Tag.E7 e7Neg 5 fun q => 5 ∣ q + 1) :
    CrossCharInnerAt .E7 fun idx p =>
      (∃ q : TauCeti.PrimePower, idx.1 = .E7 q ∧ 5 ∣ q.card + 1) ∧ p = 5 := by
  rintro ⟨d, hv⟩ _ p _ _ _ ⟨⟨q, hd, h5⟩, rfl⟩
  change d = _ at hd
  subst hd
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  rw [← hK] at h5
  exact (isInnerLocallyBalanced_adjointE7_of_dvd_add_one_of_negBalance Nat.prime_five le_rfl hL K
    h5).of_mulEquiv e

theorem crossCharInnerAt_E7_dvd_add_one_of_negBalance
    (hL : ∀ p : ℕ, p.Prime → 7 ≤ p → LangTorusPlaneBalance Tag.E7 e7Neg p fun q => p ∣ q + 1) :
    CrossCharInnerAt .E7 fun idx p =>
      (∃ q : TauCeti.PrimePower, idx.1 = .E7 q ∧ p ∣ q.card + 1) ∧ 7 ≤ p := by
  rintro ⟨d, hv⟩ _ p hp _ _ ⟨⟨q, hd, hpq⟩, hp7⟩
  change d = _ at hd
  subst hd
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  rw [← hK] at hpq
  exact (isInnerLocallyBalanced_adjointE7_of_dvd_add_one_of_negBalance hp (by omega) (hL p hp hp7) K
    hpq).of_mulEquiv e

theorem crossCharInnerAt_E7_seven_of_classes_negBalance
    (hL : ∀ p : ℕ, p.Prime → 7 ≤ p → LangTorusPlaneBalance Tag.E7 e7Neg p fun q => p ∣ q + 1)
    (h1 : InnerPlaneBalanceAtP .E7 1 fun p => p = 7) (h3 : InnerPlaneBalanceAt .E7 3)
    (h6 : InnerPlaneBalanceAt .E7 6) :
    CrossCharInnerAt .E7 fun idx p => (∃ q : TauCeti.PrimePower, idx.1 = .E7 q ∧
      3 ≤ degCount Tag.E7 (orderOf ((q.card : ℕ) : ZMod p))) ∧ 7 ≤ p := by
  rintro ⟨d, hv⟩ hk p hp hp2 hc ⟨⟨q, hq, hdeg⟩, hp7⟩
  change d = _ at hq
  subst hq
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hq1 : 1 ≤ q.card := Nat.one_le_iff_ne_zero.2 (TauCeti.PrimePower.card_def q ▸
    pow_ne_zero _ q.prime_p.ne_zero)
  rcases degCount_E7_ge_three hdeg with he | he | he | he
  · by_cases h7 : p = 7
    · exact isInnerLocallyBalanced_of_innerPlaneBalanceAtP (k := .E7) h1 q hv hp hp7 h7 hpq he
    · exact crossCharInnerAt_E7_dvd_sub_one _ ⟨q, rfl⟩ p hp hp2 hc
        ⟨q, rfl, eleven_le_of_prime_seven_le_ne hp hp7 h7, dvd_sub_one_of_orderOf_eq_one hq1 he⟩
  · exact crossCharInnerAt_E7_dvd_add_one_of_negBalance hL _ ⟨q, rfl⟩ p hp hp2 hc
      ⟨⟨q, rfl, dvd_add_one_of_orderOf_eq_two hp he⟩, hp7⟩
  · exact isInnerLocallyBalanced_of_innerPlaneBalanceAtP (k := .E7)
      (h3.atP fun _ => True) q hv hp hp7 trivial hpq he
  · exact isInnerLocallyBalanced_of_innerPlaneBalanceAtP (k := .E7)
      (h6.atP fun _ => True) q hv hp hp7 trivial hpq he

theorem crossCharInnerAt_F4_ge_three_of_negBalance
    (hL : ∀ p : ℕ, p.Prime → 5 ≤ p → LangTorusPlaneBalance Tag.F4 f4Neg p fun q => p ∣ q + 1)
    (h3 : F4InnerResidualThree) :
    CrossCharInnerAt .F4 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .F4 q ∧
      3 ≤ degCount Tag.F4 (orderOf ((q.card : ℕ) : ZMod p)) :=
  crossCharInnerAt_F4_ge_three_of_residual (f4InnerResidual_of_negBalance hL h3)

theorem crossCharInnerAt_E8_seven_of_classes_lang
    (hsub : LangSubnormal) (hin : LangComponentsQuasisimple .inner)
    (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
    (hex : LangComponentsQuasisimple .exc)
    (h1 : InnerPlaneBalanceAtP .E8 1 fun p => p = 7) (h3 : InnerPlaneBalanceAt .E8 3)
    (h4 : InnerPlaneBalanceAt .E8 4) (h6 : InnerPlaneBalanceAt .E8 6) :
    CrossCharInnerAt .E8 fun idx p => (∃ q : TauCeti.PrimePower, idx.1 = .E8 q ∧
      3 ≤ degCount Tag.E8 (orderOf ((q.card : ℕ) : ZMod p))) ∧ 7 ≤ p :=
  crossCharInnerAt_E8_seven_of_classes_negBalance (fun _ hp hp7 =>
    langTorusPlaneBalance_neg_dvd_add_one (Or.inr (Or.inr rfl)) e8Neg_smul hp (by omega) hsub hin
      hsu htw hex) h1 h3 h4 h6

theorem crossCharInnerAt_E8_five_of_parts_lang (htor : E8FiveToralPlane)
    (hSplit : ∀ w : WeylGroup Tag.E8, LangTorusPlaneBalance Tag.E8 w 5 fun q => 5 ∣ q - 1)
    (hNeg : ∀ w : WeylGroup Tag.E8, w ≠ e8Neg →
      LangTorusPlaneBalance Tag.E8 w 5 fun q => 5 ∣ q + 1)
    (hsub : LangSubnormal) (hin : LangComponentsQuasisimple .inner)
    (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
    (hex : LangComponentsQuasisimple .exc)
    (hFour : LangTorusPlaneBalance Tag.E8 e8PhiFourWeyl 5 fun q => 5 ∣ q ^ 2 + 1) :
    CrossCharInnerAt .E8 fun _ p => p = 5 :=
  crossCharInnerAt_E8_five_of_parts_negBalance htor hSplit hNeg
    (langTorusPlaneBalance_neg_dvd_add_one (Or.inr (Or.inr rfl)) e8Neg_smul Nat.prime_five le_rfl
      hsub hin hsu htw hex) hFour

theorem crossCharInnerAt_E7_five_of_lang
    (hsub : LangSubnormal) (hin : LangComponentsQuasisimple .inner)
    (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
    (hex : LangComponentsQuasisimple .exc) :
    CrossCharInnerAt .E7 fun idx p =>
      (∃ q : TauCeti.PrimePower, idx.1 = .E7 q ∧ 5 ∣ q.card + 1) ∧ p = 5 :=
  crossCharInnerAt_E7_five_of_negBalance (langTorusPlaneBalance_neg_dvd_add_one
    (Or.inr (Or.inl rfl)) e7Neg_smul Nat.prime_five le_rfl hsub hin hsu htw hex)

theorem crossCharInnerAt_E7_five_sq_of_lang
    (hsub : LangSubnormal) (hin : LangComponentsQuasisimple .inner)
    (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
    (hex : LangComponentsQuasisimple .exc) :
    CrossCharInnerAt .E7 fun idx p =>
      (∃ q : TauCeti.PrimePower, idx.1 = .E7 q ∧ 5 ∣ q.card ^ 2 - 1) ∧ p = 5 :=
  crossCharInnerAt_E7_five_of_add_one (crossCharInnerAt_E7_five_of_lang hsub hin hsu htw hex)

theorem crossCharInnerAt_E7_seven_of_classes_lang
    (hsub : LangSubnormal) (hin : LangComponentsQuasisimple .inner)
    (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
    (hex : LangComponentsQuasisimple .exc)
    (h1 : InnerPlaneBalanceAtP .E7 1 fun p => p = 7) (h3 : InnerPlaneBalanceAt .E7 3)
    (h6 : InnerPlaneBalanceAt .E7 6) :
    CrossCharInnerAt .E7 fun idx p => (∃ q : TauCeti.PrimePower, idx.1 = .E7 q ∧
      3 ≤ degCount Tag.E7 (orderOf ((q.card : ℕ) : ZMod p))) ∧ 7 ≤ p :=
  crossCharInnerAt_E7_seven_of_classes_negBalance (fun _ hp hp7 =>
    langTorusPlaneBalance_neg_dvd_add_one (Or.inr (Or.inl rfl)) e7Neg_smul hp (by omega) hsub hin
      hsu htw hex) h1 h3 h6

theorem crossCharInnerAt_F4_ge_three_of_lang
    (hsub : LangSubnormal) (hin : LangComponentsQuasisimple .inner)
    (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
    (hex : LangComponentsQuasisimple .exc)
    (h3 : F4InnerResidualThree) :
    CrossCharInnerAt .F4 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .F4 q ∧
      3 ≤ degCount Tag.F4 (orderOf ((q.card : ℕ) : ZMod p)) :=
  crossCharInnerAt_F4_ge_three_of_negBalance (fun _ hp hp5 =>
    langTorusPlaneBalance_neg_dvd_add_one (Or.inl rfl) f4Neg_smul hp hp5 hsub hin hsu htw hex) h3

end Families

end CFSG.HardMathSupport.Timmesfeld.CrossChar
