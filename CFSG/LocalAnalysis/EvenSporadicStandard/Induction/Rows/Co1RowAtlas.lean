module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1Stage3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RankE8
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.PinnedPair
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0ClsK
public import CFSG.RankThree.PartOne.N143.Co1TwoRank
public import Certificates.Certificate26991
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1KFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1Lemma36

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Co1Block CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native Cover

private theorem rep_two_getElem! {n : ℕ} {a b : Array ℕ} {f : ℕ → Equiv.Perm (Fin n)}
    (ha : Rep n a (f 0)) (hb : Rep n b (f 1)) :
    ∀ h < 2, Rep n (#[a, b] : Array (Array ℕ))[h]! (f h) := by
  intro h hh
  interval_cases h
  · exact ha
  · exact hb

section Co1


@[expose] def IsKCo1O : GroupClass := fun X _ => Nonempty (X ≃* ↥twoBD)

theorem isKCo1O_inv : GroupClass.IsoInv IsKCo1O := fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩

theorem co1_E8 : 3 ≤ CFSG.pRank 2 ↥twoBD := by
  have h := Certificates.certificate26991
  simp only [co1E8Check, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hi0, hi1⟩, hl1⟩, hl2⟩, hl3⟩, e1⟩, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, n1⟩, n2⟩,
    n3⟩, n4⟩, n5⟩, n6⟩, n7⟩ := h
  have hRx : Rep 1365 twoBStrong[0]! xBar := by
    have := strong_rep (j := 0) (by norm_num)
    rwa [strong0_eq] at this
  have hRy : Rep 1365 twoBStrong[1]! yBar := by
    have := strong_rep (j := 1) (by norm_num)
    rwa [strong1_eq] at this
  have hRxi := rep_inv_of_isInvA hRx hi0
  have hRyi := rep_inv_of_isInvA hRy hi1
  let gs2 : ℕ → Equiv.Perm (Fin 1365) := fun h => if h = 0 then xBar else yBar
  have hS2 : ∀ h < 2, Rep 1365 co1GenArr[h]! (gs2 h) := rep_two_getElem! (f := gs2) hRx hRy
  have hS2i : ∀ h < 2, Rep 1365 co1GenInv[h]! (gs2 h)⁻¹ :=
    rep_two_getElem! (f := fun h => (gs2 h)⁻¹) hRxi hRyi
  obtain ⟨ev, hev, hevK⟩ : ∃ ev : List ℤ → Equiv.Perm (Fin 1365),
      (∀ w, lettersOK 2 w = true → Rep 1365 (co1ArrWord w) (ev w)) ∧
        ∀ w, ev w ∈ Subgroup.closure {xBar, yBar} := by
    refine ⟨fun w => Quiver.SchreierGraph.evalWord (fun h : Fin 2 => gs2 h) (toLetters 2 w),
      fun w hw => rep_wordA hS2 hS2i w hw, fun w => ?_⟩
    have := Quiver.SchreierGraph.evalWord_mem_closure (fun h : Fin 2 => gs2 h) (toLetters 2 w)
    have e : Set.range (fun h : Fin 2 => gs2 h) = {xBar, yBar} := by
      ext x
      constructor
      · rintro ⟨h, rfl⟩
        fin_cases h <;> simp [gs2]
      · rintro (rfl | rfl)
        · exact ⟨0, by simp [gs2]⟩
        · exact ⟨1, by simp [gs2]⟩
    rwa [e] at this
  have ra := hev co1WordE1 hl1
  have rb := hev co1WordE2 hl2
  have rc := hev co1WordE3 hl3
  have ha2 := (eqA_iff (rep_compA ra ra) rep_idA).1 e1
  have hb2 := (eqA_iff (rep_compA rb rb) rep_idA).1 e2
  have hc2 := (eqA_iff (rep_compA rc rc) rep_idA).1 e3
  have hab := (eqA_iff (rep_compA ra rb) (rep_compA rb ra)).1 e4
  have hac := (eqA_iff (rep_compA ra rc) (rep_compA rc ra)).1 e5
  have hbc := (eqA_iff (rep_compA rb rc) (rep_compA rc rb)).1 e6
  have ne : ∀ {t u : Array ℕ} {g h : Equiv.Perm (Fin 1365)}, Rep 1365 t g → Rep 1365 u h →
      eqA 1365 t u = false → g ≠ h := fun ht hu he hgh => by
    rw [(eqA_iff ht hu).2 hgh] at he
    exact Bool.noConfusion he
  have m1 := ne ra rep_idA n1
  have m2 := ne rb rep_idA n2
  have m3 := ne rb ra n3
  have m4 := ne rc rep_idA n4
  have m5 := ne rc ra n5
  have m6 := ne rc rb n6
  have m7 := ne rc (rep_compA ra rb) n7
  exact three_le_pRank_of_three_involutions
    (a := (⟨ev co1WordE1, hevK _⟩ : ↥twoBD)) (b := (⟨ev co1WordE2, hevK _⟩ : ↥twoBD))
    (c := (⟨ev co1WordE3, hevK _⟩ : ↥twoBD))
    (Subtype.ext ha2) (Subtype.ext hb2) (Subtype.ext hc2) (Subtype.ext hab) (Subtype.ext hac)
    (Subtype.ext hbc) (fun h => m1 (congrArg Subtype.val h)) (fun h => m2 (congrArg Subtype.val h))
    (fun h => m3 (congrArg Subtype.val h)) (fun h => m4 (congrArg Subtype.val h))
    (fun h => m5 (congrArg Subtype.val h)) (fun h => m6 (congrArg Subtype.val h))
    (fun h => m7 (congrArg Subtype.val h))

theorem co1_pRank_K (X : Type) [Group X] (hX : IsKCo1O X) : 3 ≤ CFSG.pRank 2 X := by
  obtain ⟨e⟩ := hX
  rw [pRank_two_eq_of_mulEquiv' e]
  exact co1_E8

theorem co1_pRank_L (X : Type) [Group X] (hX : IsLS [.Co1] X) : 3 ≤ CFSG.pRank 2 X := by
  refine three_le_pRank_of_isLS co1_pinned.1 (fun Y _ h => ?_) hX
  have hf : Finite (Carrier .Co1) := co1_pinned.1
  have : Finite Y := Finite.of_equiv _ h.some.symm.toEquiv
  exact ((CFSG.RankThree.PartOne.N143.co1_two_rank_at_least_five Y h).2).trans' (by norm_num)

theorem co1_pair_of_involution (hmult : OddMultTrivial .Co1) (H : Type) [Group H] [Finite H]
    (L K : Subgroup H) (hcov : OddCover .Co1 L) (hKL : K ≤ L) (hKq : CFSG.IsQuasisimple ↥K)
    {j : ℕ} (hj : Odd j) (hq : Nat.card (↥K ⧸ CFSG.oddCore ↥K) = 251596800 * j) (t : ↥L)
    (ht2 : orderOf t = 2) (hKt : ∀ k ∈ K, k * (t : H) = (t : H) * k) :
    Co1Pair H L K (t : H) := by
  have : Finite ↥L := hcov.finite (by decide : TauCeti.SporadicName.Co1 ≠ .M)
  have : Finite ↥K := Finite.of_injective _ (Subgroup.inclusion_injective hKL)
  have hL : IsSporadic ↥L .Co1 := hcov.isSporadic_of_mult hmult
  have ht2' : orderOf (t : H) = 2 := by rw [Subgroup.orderOf_coe]; exact ht2
  have hle : K.subgroupOf L ≤ centralizer ({t} : Set ↥L) := fun k hk => by
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (hKt k (mem_subgroupOf.1 hk))
  have hdvd : Nat.card ↥K ∣ Nat.card ↥(centralizer ({t} : Set ↥L)) := by
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv] at this
  have hKcard : Nat.card ↥K = 251596800 * (j * Nat.card (CFSG.oddCore ↥K)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore ↥K), hq, mul_assoc]
  have hodd : Odd (j * Nat.card (CFSG.oddCore ↥K)) :=
    hj.mul (RuStd.S2.Glue.odd_card_oddCore ↥K)
  have h13 : 251596800 ∣ Nat.card ↥(centralizer ({t} : Set ↥L)) := by
    refine Dvd.dvd.trans ?_ hdvd
    rw [hKcard]
    exact dvd_mul_right _ _
  have hcc : Nat.card ↥(centralizer ({t} : Set ↥L)) = 2012774400 := by
    rcases TwoCo1.card_centralizer_involution_of_isSporadic_co1 hL ht2 with h | h | h
    · rw [h] at h13
      exact absurd h13 (by norm_num)
    · rw [h] at h13
      exact absurd h13 (by norm_num)
    · exact h
  rw [hcc, hKcard] at hdvd
  have hm : j * Nat.card (CFSG.oddCore ↥K) ∣ 8 := by
    have : 251596800 * (j * Nat.card (CFSG.oddCore ↥K)) ∣ 251596800 * 8 := by
      simpa using hdvd
    exact (Nat.mul_dvd_mul_iff_left (by norm_num)).1 this
  have hm1 : j * Nat.card (CFSG.oddCore ↥K) = 1 :=
    Nat.Coprime.eq_one_of_dvd (by
      have : Nat.Coprime (j * Nat.card (CFSG.oddCore ↥K)) (2 ^ 3) :=
        Nat.Coprime.pow_right 3 (Nat.coprime_two_right.2 hodd)
      simpa using this) hm
  exact ⟨t.2, ht2', hKL, hKt, hKq.1, by rw [hKcard, hm1, mul_one]⟩

theorem co1_rowFit (hmult : OddMultTrivial .Co1) (H : Type) [Group H] [Finite H] (L K : Subgroup H)
    (hcov : OddCover .Co1 L) (hKL : K ≤ L) (hKq : CFSG.IsQuasisimple ↥K) {j : ℕ} (hj : Odd j)
    (hq : Nat.card (↥K ⧸ CFSG.oddCore ↥K) = 251596800 * j) (hstd : SolStd (K.subgroupOf L)) :
    ∃ u : H, Co1Pair H L K u := by
  obtain ⟨t, ht2, hcomp⟩ := hstd.exists_involution
  have hKt : ∀ k ∈ K, k * (t : H) = (t : H) * k := fun k hk => by
    have h1 : (⟨k, hKL hk⟩ : ↥L) ∈ centralizer ({t} : Set ↥L) := hcomp.1 (mem_subgroupOf.2 hk)
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 h1)
  exact ⟨(t : H), co1_pair_of_involution hmult H L K hcov hKL hKq hj hq t ht2 hKt⟩

@[expose] def Co1PinnedPair : Prop :=
  ∃ (u : Carrier .Co1) (K : Subgroup (Carrier .Co1)), u * u = 1 ∧ u ≠ 1 ∧
    (∀ k ∈ K, k * u = u * k) ∧ ⁅K, K⁆ = K ∧ Nat.card K = 251596800

theorem co1_rowExists (hmult : OddMultTrivial .Co1) (hpair : Co1PinnedPair) (H : Type) [Group H]
    [Finite H] (L : Subgroup H) (hcov : OddCover .Co1 L) :
    ∃ (K : Subgroup H) (u : H), Co1Pair H L K u := by
  have : Finite ↥L := hcov.finite (by decide : TauCeti.SporadicName.Co1 ≠ .M)
  obtain ⟨e⟩ := hcov.2.2
  obtain ⟨ut, Kt, hut, hut1, hKtu, hKt, hcard⟩ := hpair
  obtain ⟨K, u, hu, hu2, hKL, hKu, hKperf, hmap⟩ :=
    exists_pair_of_pinned_pair hcov.2.1 e hut hut1 hKtu hKt
  have hZ : center ↥L = ⊥ := hcov.center_eq_bot hmult
  have hinj : Function.Injective (q ↥L) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    show (QuotientGroup.mk' (center ↥L)).ker = ⊥
    rw [QuotientGroup.ker_mk', hZ]
  refine ⟨K, u, hu, hu2, hKL, hKu, hKperf, ?_⟩
  have h1 : Nat.card ↥K = Nat.card ↥(K.subgroupOf L) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv).symm
  have h2 := Subgroup.card_map_of_injective (K := K.subgroupOf L) hinj
  rw [h1, ← h2, hmap, Subgroup.card_map_of_injective e.symm.injective, hcard]

theorem isOddCentralExt_of_isKCo1O {X : Type} [Group X] (hX : IsKCo1O X) :
    IsOddCentralExt ↥twoBD X := by
  obtain ⟨e⟩ := hX
  have hqK : CFSG.Open.IsQuasisimple ↥twoBD :=
    isQuasisimple_of_simple isSimpleGroup_twoBD ⟨xD, yD, xD_yD_ne⟩
  have hqX : CFSG.Open.IsQuasisimple X := isQuasisimple_of_mulEquiv' e.symm hqK
  have hker : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 e.injective
  exact ⟨((CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1).2 hqX, e.toMonoidHom,
    e.surjective, by rw [hker]; exact bot_le, by rw [hker, Subgroup.card_bot]; exact odd_one⟩

theorem co1_rowIsKO (hmult : OddMultTrivial .Co1) : ∀ s ∈ [TauCeti.SporadicName.Co1],
    ∀ (H : Type) [Group H] (L K : Subgroup H) (u : H), OddCover s L → Co1Pair H L K u →
      IsKCo1O ↥K := by
  intro s hs H _ L K u hcov hQ
  rcases List.mem_singleton.1 hs with rfl
  have := hcov.finite (by decide : TauCeti.SporadicName.Co1 ≠ .M)
  have hL : IsSporadic ↥L .Co1 :=
    isSporadic_of_center_eq_bot (hmult ↥L hcov.1 hcov.2.1 hcov.2.2) hcov.2.2
  have hP : Co1Pair H L K u := hQ
  obtain ⟨huL, hu2, hKL, hKu, hperf, hcard⟩ := hQ
  obtain ⟨Ψ, hΨ, hΨL, hΨR, hΨu⟩ := co1_model hL hP
  obtain ⟨M⟩ := co1_outModel
  exact M.equiv_D huL hKL hKu Ψ hΨ hΨL hΨu hperf (hcard.trans card_twoBD.symm)

def stage3Row_co1_proved (hmult : OddMultTrivial .Co1) (hpair : Co1PinnedPair)
    (hsol : Co1AutCentralizerA4) (hfix : G24FixedNonsolvable) (h25 : Finkelstein77.Asc76Lemma25) :
    Stage3Row [.Co1] (fun _ => Co1Pair) :=
  stage3Row_of_parts (m := fun _ => 2) (IsK := IsKCo1O)
    { pRank_K := fun X _ hX => co1_pRank_K X hX
      pRank_L := fun X _ hX => co1_pRank_L X hX
      rowExists := fun s hs H _ _ L hcov => by
        rcases List.mem_singleton.1 hs with rfl
        exact co1_rowExists hmult hpair H L hcov
      rowFit := fun s hs H _ _ L K hcov hKL hKq hK hstd _ => by
        rcases List.mem_singleton.1 hs with rfl
        obtain ⟨e⟩ := hK
        exact co1_rowFit hmult H L K hcov hKL hKq (j := 1) odd_one
          (by rw [Nat.card_congr e.toEquiv, card_twoBD, mul_one]) hstd }
    (fun X _ hX => co1_kNotExc X (isOddCentralExt_of_isKCo1O hX))
    (fun _ _ _ _ hX hY => co1_kNeL hX (isOddCentralExt_of_isKCo1O hY)) isKCo1O_inv
    (fun X _ hX => (isOddCentralExt_of_isKCo1O hX).1) co1_finite_even
    (fun s hs => by
      rcases List.mem_singleton.1 hs with rfl
      exact Rec36.new 4 (lemma36eDataQ_co1 hmult hsol hfix))
    (outTwoCovers_co1 hmult) (co1_rowIsKO hmult) (Or.inr (twoSylowStd_co1 h25 co1_pRank_L))

end Co1

end CFSG.EvenSporadicStandard.Induction
