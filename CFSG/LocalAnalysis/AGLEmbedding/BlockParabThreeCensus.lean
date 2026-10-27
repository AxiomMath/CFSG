module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSU
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSpin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSpinMinus
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeG2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThree
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2

public section

namespace CFSG.AGLEmbedding.ParabHub

open CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank

section Quotient

variable {K Y : Type*} [Group K] [Finite K] [Group Y] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem BorelQuotient.exists_perfect_three_dvd (h : BorelQuotient D n H π M) {q : ℕ}
    (hq4 : 4 ≤ q) (hrank : ∀ i, RankOneNode D i q) (h3 : ∀ i, HasOrderThree D i)
    (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) :
    ∃ V : Subgroup Y, V ≤ J ∧ ⁅V, V⁆ = V ∧ 3 ∣ Nat.card V := by
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq T
  have hQ : BorelQuotient D n H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : borel D H ≤ J.comap π' := fun b hb => by
    rw [Subgroup.mem_comap]
    exact hNJ (by rw [hNπ]; exact ⟨b, hb, rfl⟩)
  have hne : J.comap π' ≠ borel D H := by
    intro he
    apply hJ
    rw [hNπ, ← he, Subgroup.map_comap_eq_self_of_surjective hπ']
  obtain ⟨i, hi⟩ := exists_negRoot_le_of_borel_lt h.ct h.extras hBJ hne
  have hLi : rankOne D.rootGroup i ≤ J.comap π' :=
    sup_le ((rootGroup_le_borel ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)
      (ht_single_pos i)).trans hBJ) hi
  obtain ⟨x, hx, y, hy, h3', c, hc⟩ := h3 i
  have hVJ : (rankOne D.rootGroup i).map π' ≤ J := Subgroup.map_le_iff_le_comap.2 hLi
  have hperf : ⁅(rankOne D.rootGroup i).map π', (rankOne D.rootGroup i).map π'⁆ =
      (rankOne D.rootGroup i).map π' := by
    rw [← Subgroup.map_commutator, (hrank i).perfect hq4]
  have hxy : x * y ∈ rankOne D.rootGroup i :=
    mul_mem (le_sup_left (b := D.rootGroup (-Pi.single i 1)) hx)
      (le_sup_right (a := D.rootGroup (Pi.single i 1)) hy)
  have hne1 : π' (x * y) ≠ 1 := by
    intro h1
    exact hc (Subgroup.mem_center_iff.1 (hQ.ker_central _ h1) c).symm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf (π' (x * y)) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, h3', map_one]) hne1
  have hmem : π' (x * y) ∈ (rankOne D.rootGroup i).map π' := ⟨x * y, hxy, rfl⟩
  have hdvd := Subgroup.orderOf_dvd_natCard ((rankOne D.rootGroup i).map π') hmem
  rw [hord] at hdvd
  exact ⟨_, hVJ, hperf, hdvd⟩

end Quotient

theorem four_le_two_pow_of_le {f : ℕ} (hf : 2 ≤ f) : 4 ≤ 2 ^ f :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

theorem four_le_card_of_card_eq_two_pow {F : Type} {f : ℕ} (hcard : Nat.card F = 2 ^ f)
    (hf : 2 ≤ f) : 4 ≤ Nat.card F :=
  hcard ▸ four_le_two_pow_of_le hf

theorem exists_perfect_three_dvd_of_model_psl {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSL n 2 f) (hf : 2 ≤ f) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) :
    ∃ V : Subgroup Y, V ≤ J ∧ ⁅V, V⁆ = V ∧ 3 ∣ Nat.card V := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (borelQuotient_sl ((projectiveSpecialLinearGroupEquivStatedProj (m + 1) F).trans
    e.symm)).exists_perfect_three_dvd (four_le_card_of_card_eq_two_pow hcard hf) rankOneNode_sl
    (fun i => (hasSL2Node_sl i).hasOrderThree) T J hNJ hJ

theorem exists_perfect_three_dvd_of_model_psp {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSp n 2 f) (hf : 2 ≤ f) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) :
    ∃ V : Subgroup Y, V ≤ J ∧ ⁅V, V⁆ = V ∧ 3 ∣ Nat.card V := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact (borelQuotient_sp e).exists_perfect_three_dvd (four_le_card_of_card_eq_two_pow hcard hf)
    rankOneNode_sp (fun i => (hasSL2Node_sp i).hasOrderThree) T J hNJ hJ

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits in
theorem exists_perfect_three_dvd_of_model_psu {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSU n 2 f) (hf : 2 ≤ f) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) :
    ∃ V : Subgroup Y, V ≤ J ∧ ⁅V, V⁆ = V ∧ 3 ∣ Nat.card V := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
  have : Finite (SU (unitaryInvolution F 2 f) n) := Finite.of_injective _ Subtype.val_injective
  exact (borelQuotient_su hcard (by omega) ζ hζ e).exists_perfect_three_dvd
    (four_le_two_pow_of_le hf) (rankOneNode_su hcard) (fun i => hasOrderThree_su hcard i) T J
    hNJ hJ

open CFSG.LieType.Universal.Spin in
theorem exists_perfect_three_dvd_of_model_pomegaPlus {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaPlus n 2 f) (hf : 2 ≤ f) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) :
    ∃ V : Subgroup Y, V ≤ J ∧ ⁅V, V⁆ = V ∧ 3 ∣ Nat.card V := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  exact (borelQuotient_spinPlus hn3 e).exists_perfect_three_dvd
    (four_le_card_of_card_eq_two_pow hcard hf) (rankOneNode_spinPlus hn3)
    (fun i => (hasSL2Node_spinPlus hn3 i).hasOrderThree) T J hNJ hJ

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted in
theorem exists_perfect_three_dvd_of_model_pomegaMinus {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaMinus n 2 f) (hf : 2 ≤ f) (T : Sylow 2 Y)
    (J : Subgroup Y) (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) :
    ∃ V : Subgroup Y, V ≤ J ∧ ⁅V, V⁆ = V ∧ 3 ∣ Nat.card V := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  refine (borelQuotient_spinMinus hirr hn e).exists_perfect_three_dvd
    (four_le_card_of_card_eq_two_pow hcard hf) (fun i => ?_)
    (fun i => hasOrderThree_spinMinus hirr i) T J hNJ hJ
  by_cases hk : i.val + 1 < n - 1
  · exact rankOneNode_spinMinus_long hirr hk
  · exact rankOneNode_spinMinus_short hirr hk

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem exists_perfect_three_dvd_g2 {K : Type} [Field K] [Finite K] [CharP K 2] {Y : Type}
    [Group Y] [Finite Y] (e : Y ≃* AdjointQuotient .G2 K) (hq4 : 4 ≤ Nat.card K) (T : Sylow 2 Y)
    (J : Subgroup Y) (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) :
    ∃ V : Subgroup Y, V ≤ J ∧ ⁅V, V⁆ = V ∧ 3 ∣ Nat.card V := by
  have : Finite ↥(adjointGroup .G2 K) := generated_group_finite .G2 K
  exact (borelQuotient_g2 e).exists_perfect_three_dvd hq4 rankOneNode_g2
    (fun i => (hasSL2Node_g2 i).hasOrderThree) T J hNJ hJ

end CFSG.AGLEmbedding.ParabHub

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding.ParabHub

@[expose] def IsClassicalOrG2IndexTwo : TauCeti.LieTypeIndex → Prop
  | .A _ q | .twistedA _ q | .B _ q | .D _ q | .twistedD _ q | .G2 q => q.card = 2
  | _ => False

theorem card_eq_two_of_not_two_le_exponent {q : TauCeti.PrimePower} (hq : q.p = 2)
    (h : ¬ 2 ≤ q.exponent) : q.card = 2 := by
  have := q.exponent_pos
  rw [TauCeti.PrimePower.card_def, hq, show q.exponent = 1 by omega, pow_one]

section Catalog


theorem isClassicalOrG2IndexTwo_of_perfect_coprime {Y : Type} [Group Y] [Finite Y]
    (d : TauCeti.ValidLieTypeIndex) (hd : IsClassicalOrG2Index d.1)
    (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y))
    (hperf : ∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) :
    IsClassicalOrG2IndexTwo d.1 := by
  have hno : ¬ ∃ V : Subgroup Y, V ≤ J ∧ ⁅V, V⁆ = V ∧ 3 ∣ Nat.card V := by
    rintro ⟨V, hVJ, hV, h3⟩
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (hperf V hVJ hV) h3
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q =>
    change q.p = 2 at hd
    refine card_eq_two_of_not_two_le_exponent hd fun hf => hno ?_
    have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    rw [hd] at h
    exact exists_perfect_three_dvd_of_model_psl h hf T J hNJ hJ
  | twistedA r q =>
    change q.p = 2 at hd
    refine card_eq_two_of_not_two_le_exponent hd fun hf => hno ?_
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    rw [hd] at h
    exact exists_perfect_three_dvd_of_model_psu h hf T J hNJ hJ
  | B r q =>
    change q.p = 2 at hd
    refine card_eq_two_of_not_two_le_exponent hd fun hf => hno ?_
    have hr := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    by_cases h2 : r = 2
    · subst h2
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      rw [hd] at h
      exact exists_perfect_three_dvd_of_model_psp h hf T J hNJ hJ
    · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hd
        (by omega) e
      rw [hd] at h
      exact exists_perfect_three_dvd_of_model_psp h hf T J hNJ hJ
  | C r q => exact hd.elim
  | D r q =>
    change q.p = 2 at hd
    refine card_eq_two_of_not_two_le_exponent hd fun hf => hno ?_
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hd e
    rw [hd] at h
    exact exists_perfect_three_dvd_of_model_pomegaPlus h hf T J hNJ hJ
  | twistedD r q =>
    change q.p = 2 at hd
    refine card_eq_two_of_not_two_le_exponent hd fun hf => hno ?_
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hd e
    rw [hd] at h
    exact exists_perfect_three_dvd_of_model_pomegaMinus h hf T J hNJ hJ
  | G2 q =>
    change q.p = 2 at hd
    refine absurd ?_ hno
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hd
    have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
      rw [TauCeti.PrimePower.card_def, GaloisField.card q.p q.exponent q.exponent_pos.ne']
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hd
      (GaloisField q.p q.exponent) hK
    have hq3 : 3 ≤ q.card :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hd]
    have hm : 2 ≤ q.exponent := by
      by_contra hm
      have h1 : 2 ^ q.exponent ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact exists_perfect_three_dvd_g2 (e.trans b.symm)
      (by rw [hK, hcard]; exact four_le_two_pow_of_le hm) T J hNJ hJ
  | _ => exact hd.elim

theorem kFactParabolicThreeCensus :
    ∀ (Y : Type) [Group Y] [Finite Y], IsClassicalTwoOrG2 Y → ∀ T J : Subgroup Y,
      IsSylowTwoOf T ⊤ → Subgroup.normalizer (T : Set Y) ≤ J →
      J ≠ Subgroup.normalizer (T : Set Y) →
      (∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) →
      (∃ d : TauCeti.ValidLieTypeIndex, IsClassicalOrG2IndexTwo d.1 ∧
          Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
        (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 8) ∧ Nonempty (Y ≃* alternatingGroup (Fin n))) ∨
        ∃ d : TauCeti.ValidLieTypeIndex, ((∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
          (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) ∧
          Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  intro Y _ _ hY T J hT hNJ hJ hperf
  obtain ⟨T', rfl⟩ := exists_sylow_of_isSylowTwoOf_top hT
  rcases hY with ⟨d, hd, ⟨e⟩⟩ | h2 | h3
  · exact Or.inl ⟨d, isClassicalOrG2IndexTwo_of_perfect_coprime d hd e T' J hNJ hJ hperf, ⟨e⟩⟩
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

end Catalog

end CFSG.AGLEmbedding
