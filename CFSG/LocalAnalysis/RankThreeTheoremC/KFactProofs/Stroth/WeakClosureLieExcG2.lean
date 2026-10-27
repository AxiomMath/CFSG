module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcAssembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTori
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcNum
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcWitness
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcModel
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcFpf

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.Lattice
  CFSG.Timmesfeld.ExceptionalOrders CFSG.RankThree.PartOne.K128
open scoped commutatorElement Matrix

variable {F : Type} [Field F] [Finite F] {p : ℕ}

namespace G2

theorem commutator_eq_top (hq3 : 3 ≤ Nat.card F) :
    commutator ↥(adjointGroup Tag.G2 F) = ⊤ :=
  (CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card F hq3).commutator_eq_top

theorem hord_one (hp : p.Prime) (hp5 : 5 ≤ p) (hd : p ∣ Nat.card F - 1) {L : Type} [Field L]
    [Algebra F L] [IsAlgClosure F L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card F) :
    ∃ H : Subgroup (ModGL Tag.G2 L), H ≤
        twistedTorusOf (canonicalRep (coxeterSystem Tag.G2) L (1 : WeylGroup Tag.G2))
          (Units.map (entrywiseHom Fr)) ∧
      (Nat.card (adjointGroup Tag.G2 F)).factorization p ≤ (Nat.card H).factorization p := by
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  have hQ : 2 ≤ Nat.card F := Finite.one_lt_card
  have hpK : ¬ p ∣ Nat.card F := by
    intro h
    have h1 : p ∣ Nat.card F - (Nat.card F - 1) := Nat.dvd_sub h hd
    rw [show Nat.card F - (Nat.card F - 1) = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hdQ : p ∣ Nat.card F ^ 2 - 1 := by
    rw [sq_sub_one_eq _ (by omega)]
    exact Dvd.dvd.mul_right hd _
  have hnQ1 : ¬ p ∣ Nat.card F + 1 := by
    intro h
    have h1 : p ∣ (Nat.card F + 1) - (Nat.card F - 1) := Nat.dvd_sub h hd
    rw [show (Nat.card F + 1) - (Nat.card F - 1) = 2 by omega] at h1
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  have hvp : (Nat.card F ^ 2 - 1).factorization p = (Nat.card F - 1).factorization p := by
    rw [sq_sub_one_eq _ (by omega), Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnQ1, add_zero]
  obtain ⟨ζ, hζord, hζpow⟩ := exists_unit_orderOf_card_sub_one_alg F L
  obtain ⟨H₀, hH₀T, hH₀card⟩ := exists_le_twistedTorus_card_one (τ := Tag.G2) hFr (by omega) hζpow
  refine ⟨H₀, hH₀T, le_of_eq ?_⟩
  rw [card_adjointGroup_G2, factorization_ordG2 hp hp5 hQ hpK hdQ, hvp, hH₀card, hζord,
    Nat.factorization_pow]
  rfl

theorem hord_two (hp : p.Prime) (hp5 : 5 ≤ p) (hd : p ∣ Nat.card F + 1) {L : Type} [Field L]
    [Algebra F L] [IsAlgClosure F L] {w : WeylGroup Tag.G2}
    (hw : ∀ u : Fin Tag.G2.rank → ℤ, w • u = -u) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card F) :
    ∃ H : Subgroup (ModGL Tag.G2 L), H ≤
        twistedTorusOf (canonicalRep (coxeterSystem Tag.G2) L w) (Units.map (entrywiseHom Fr)) ∧
      (Nat.card (adjointGroup Tag.G2 F)).factorization p ≤ (Nat.card H).factorization p := by
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hpK : ¬ p ∣ Nat.card F := by
    intro h
    have h1 : p ∣ (Nat.card F + 1) - Nat.card F := Nat.dvd_sub hd h
    rw [show (Nat.card F + 1) - Nat.card F = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  obtain ⟨ζ, hζord, hζpow⟩ : ∃ ζ : Lˣ, orderOf ζ = Nat.card F + 1 ∧ ζ ^ (Nat.card F + 1) = 1 := by
    have hK0 : ((Nat.card F : ℕ) : L) = 0 := by
      haveI : Fintype F := Fintype.ofFinite F
      rw [← map_natCast (algebraMap F L), Nat.card_eq_fintype_card,
        FiniteField.cast_card_eq_zero F, map_zero]
    haveI : NeZero (((Nat.card F + 1 : ℕ)) : L) := ⟨by
      rw [Nat.cast_add, hK0, zero_add, Nat.cast_one]
      exact one_ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L (Nat.card F + 1)
    set ζu : Lˣ := (hζ.isUnit (by omega)).unit with hζu
    have hζu' : IsPrimitiveRoot ζu (Nat.card F + 1) :=
      IsPrimitiveRoot.coe_units_iff.1 (by simpa [hζu] using hζ)
    exact ⟨ζu, hζu'.eq_orderOf.symm, hζu'.pow_eq_one⟩
  obtain ⟨H₀, hH₀T, hH₀card⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_le_twistedTorus_card
    (L := L) (fun a => rootDiagUnit_mem_torusGroup a) hw hFr hζpow
  refine ⟨H₀, hH₀T, le_of_eq ?_⟩
  have hd2 : p ∣ Nat.card F ^ 2 - 1 := by
    rw [sq_sub_one_eq _ (by omega)]
    exact Dvd.dvd.mul_left hd _
  have hq1 : ¬ p ∣ Nat.card F - 1 := by
    intro h1
    have h2 : p ∣ (Nat.card F + 1) - (Nat.card F - 1) := Nat.dvd_sub hd h1
    rw [show (Nat.card F + 1) - (Nat.card F - 1) = 2 by omega] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hvp : (Nat.card F ^ 2 - 1).factorization p = (Nat.card F + 1).factorization p := by
    rw [sq_sub_one_eq _ (by omega), Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hq1, zero_add]
  rw [hH₀card, hζord, card_adjointGroup_G2, factorization_ordG2 hp hp5 hq2 hpK hd2, hvp,
    Nat.factorization_pow]
  rfl

@[expose] def negWord : List (Fin Tag.G2.rank) := (List.replicate 3 [0, 1]).flatten

theorem wordMat_negWord : wordMat Tag.G2 negWord = -1 := by decide +kernel

theorem wp_negWord_smul (u : Fin Tag.G2.rank → ℤ) : wp Tag.G2 negWord • u = -u := by
  rw [wp, wordProd_smul_eq_wordMat_mulVec, wordMat_negWord, Matrix.neg_mulVec, Matrix.one_mulVec]

theorem sylowFrameM_one (hp : p.Prime) (hp5 : 5 ≤ p) (hd : p ∣ Nat.card F - 1) :
    SylowFrameM Tag.G2 F p 1 := by
  have hq3 : 3 ≤ Nat.card F := by
    have := Nat.le_of_dvd (by have : 2 ≤ Nat.card F := Finite.one_lt_card; omega) hd
    omega
  exact exists_exact_frame_sylow (Or.inl rfl) F hp 1 (commutator_eq_top hq3)
    fun {L} _ _ _ Fr hFr => hord_one hp hp5 hd Fr hFr

theorem sylowFrameM_neg (hp : p.Prime) (hp5 : 5 ≤ p) (hd : p ∣ Nat.card F + 1) :
    SylowFrameM Tag.G2 F p (wp Tag.G2 negWord) := by
  have hq3 : 3 ≤ Nat.card F := by
    have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
    have := Nat.le_of_dvd (by omega) hd
    omega
  exact exists_exact_frame_sylow (Or.inl rfl) F hp (wp Tag.G2 negWord) (commutator_eq_top hq3)
    fun {L} _ _ _ Fr hFr => hord_two hp hp5 hd (wp_negWord_smul) Fr hFr

@[expose] def certY : Matrix (Fin Tag.G2.rank) (Fin Tag.G2.rank) ℤ := !![0, -1; 3, -3]

theorem weylMat_cw_cert :
    (weylMat (⁅wp Tag.G2 [0], wp Tag.G2 [1]⁆)⁻¹ - 1) * certY =
      (3 : ℤ) • (1 : Matrix (Fin Tag.G2.rank) (Fin Tag.G2.rank) ℤ) := by
  rw [← wp_cw, ← wp_reverse, weylMat_wp]
  unfold certY
  decide +kernel

theorem torusFpf_cw (hp : p.Prime) (hp5 : 5 ≤ p) (q : ℕ) (w : WeylGroup Tag.G2) :
    TorusFpf Tag.G2 q p w ⁅wp Tag.G2 [0], wp Tag.G2 [1]⁆ := by
  intro L _ _ Fr _ β _ hβp hfix
  refine fpf_of_matrix_cert weylMat_cw_cert hp ?_ hβp hfix
  intro h
  have h' : p ∣ 3 := by exact_mod_cast h
  have := Nat.le_of_dvd (by norm_num) h'
  omega

theorem mem_centralizer_one {G : Type*} [Group G] (a : G) :
    a ∈ Subgroup.centralizer ({1} : Set G) :=
  Subgroup.mem_centralizer_iff.2 fun g hg => by
    rw [Set.mem_singleton_iff.1 hg]
    simp

theorem wp_mem_centralizer_negWord (a : List (Fin Tag.G2.rank)) :
    wp Tag.G2 a ∈ Subgroup.centralizer ({wp Tag.G2 negWord} : Set (WeylGroup Tag.G2)) :=
  wp_mem_centralizer (by rw [wordMat_negWord]; simp)

theorem wcOn_toral [Fact p.Prime] (hp5 : 5 ≤ p)
    (he : orderOf ((Nat.card F : ℕ) : ZMod p) = 1 ∨ orderOf ((Nat.card F : ℕ) : ZMod p) = 2) :
    WCOn p (adjointGroup Tag.G2 F) := by
  have hp : p.Prime := Fact.out
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  rcases he with he | he
  · have hd := dvd_sub_one_of_orderOf_eq_one' (by omega) he
    exact (sylowFrameM_one hp hp5 hd).wcOn_c (a := wp Tag.G2 [0]) (b := wp Tag.G2 [1])
      (mem_centralizer_one _) (mem_centralizer_one _) (torusFpf_cw hp hp5 _ _)
  · have hd := dvd_add_one_of_orderOf_eq_two' hp he
    exact (sylowFrameM_neg hp hp5 hd).wcOn_c (a := wp Tag.G2 [0]) (b := wp Tag.G2 [1])
      (wp_mem_centralizer_negWord _) (wp_mem_centralizer_negWord _) (torusFpf_cw hp hp5 _ _)

theorem wcOn_three [Fact p.Prime] (hp3 : p = 3) (hpq : ¬ p ∣ Nat.card F) (hq3 : 3 ≤ Nat.card F)
    (he : orderOf ((Nat.card F : ℕ) : ZMod p) = 1 ∨ orderOf ((Nat.card F : ℕ) : ZMod p) = 2) :
    WCOn p (adjointGroup Tag.G2 F) := by
  have hp : p.Prime := Fact.out
  have hv : ⁅wp Tag.G2 [0], wp Tag.G2 [1]⁆ ^ p = 1 := by
    subst hp3
    exact wp_cw_pow_eq_one (by decide +kernel)
  have hj : ¬ (p : ℤ) ∣ ∑ i, (fun i : Fin Tag.G2.rank => if i = 0 then (1 : ℤ) else 0) i *
      ((weylMat (wp Tag.G2 [0])⁻¹ - 1) * (weylMat ⁅wp Tag.G2 [0], wp Tag.G2 [1]⁆⁻¹ - 1)) i 1 := by
    subst hp3
    rw [weylMat_wp_inv, weylMat_cw_inv]
    decide +kernel
  rcases he with he | he
  · have hd := dvd_sub_one_of_orderOf_eq_one' (by omega) he
    exact (weakFrame_exact (Or.inl rfl) F 1 (commutator_eq_top hq3)).wcOn_noncomm_one hpq hd hv
      _ 1 hj
  · have hd := dvd_add_one_of_orderOf_eq_two' hp he
    exact (weakFrame_exact (Or.inl rfl) F (wp Tag.G2 negWord) (commutator_eq_top hq3)).wcOn_noncomm_neg
      wp_negWord_smul hpq hd hv _ 1 hj

theorem wcOn_adjoint [Fact p.Prime] (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card F)
    (hq3 : 3 ≤ Nat.card F) : WCOn p (adjointGroup Tag.G2 F) := by
  have hp : p.Prime := Fact.out
  have hq1 : 1 ≤ Nat.card F := by omega
  rcases eq_three_or_five_le' hp hp2 with hp3 | hp5
  ·
    refine wcOn_three hp3 hpq hq3 ?_
    subst hp3
    exact CFSG.HardMathSupport.Timmesfeld.CrossChar.orderOf_natCast_zmod_three hpq
  · by_cases hd : p ∣ Nat.card F ^ 2 - 1
    · refine wcOn_toral hp5 ?_
      rcases dvd_pred_or_succ_of_dvd_sq_sub_one hp hp2 hq1 hd with ⟨h1, -⟩ | ⟨h2, -⟩
      · exact Or.inl (orderOf_eq_one_of_dvd_sub_one' hq1 h1)
      · exact Or.inr (orderOf_eq_two_of_dvd_add_one' hp hp2 h2)
    · exact WCOn.of_rankLE1 (rankLE1_G2 hp hp5 hpq hd)

end G2

theorem wcOn_g2_model {K : Type} [Group K] [Finite K] {ℓ f p : ℕ} [Fact p.Prime] (hℓ : ℓ.Prime)
    (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hq3 : 3 ≤ ℓ ^ f)
    (h : UntwistedChevalleyModel K Tag.G2 (ℓ ^ f)) : WCOn p K :=
  wcOn_of_untwisted_model hℓ hpℓ h fun F _ _ hcard hpq => G2.wcOn_adjoint hp2 hpq (hcard ▸ hq3)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw
