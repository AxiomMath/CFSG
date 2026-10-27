module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcDC
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTori
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcWitness
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcModel
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcF4Data
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwModel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.Lattice
  CFSG.Timmesfeld.ExceptionalOrders CFSG.RankThree.PartOne.K133H CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.F4Weyl CFSG.LieType.SeitzGeneration
open scoped commutatorElement Matrix

variable {F : Type} [Field F] [Finite F] {p : ℕ}

namespace F4

open F4Data

theorem commutator_eq_top : commutator ↥(adjointGroup Tag.F4 F) = ⊤ :=
  (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 F).1.commutator_eq_top

theorem wp_coxPow (k : ℕ) : wp Tag.F4 (coxPow k) = f4Coxeter ^ k := by
  induction k with
  | zero => simp [coxPow, wp_nil]
  | succ k ih =>
    have : coxPow (k + 1) = [0, 1, 2, 3] ++ coxPow k := by simp [coxPow, List.replicate_succ]
    rw [this, wp_append, ih, pow_succ']
    rfl

theorem hord_one (hp : p.Prime) (hp5 : 5 ≤ p) (hd : p ∣ Nat.card F - 1) {L : Type} [Field L]
    [Algebra F L] [IsAlgClosure F L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card F) :
    ∃ H : Subgroup (ModGL Tag.F4 L), H ≤
        twistedTorusOf (canonicalRep (coxeterSystem Tag.F4) L (1 : WeylGroup Tag.F4))
          (Units.map (entrywiseHom Fr)) ∧
      (Nat.card (adjointGroup Tag.F4 F)).factorization p ≤ (Nat.card H).factorization p := by
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  have hQ : 2 ≤ Nat.card F := Finite.one_lt_card
  obtain ⟨ζ, hζord, hζpow⟩ := exists_unit_orderOf_card_sub_one_alg F L
  obtain ⟨H₀, hH₀T, hH₀card⟩ := exists_le_twistedTorus_card_one (τ := Tag.F4) hFr (by omega) hζpow
  refine ⟨H₀, hH₀T, le_of_eq ?_⟩
  rw [card_adjointGroup_F4, factorization_ordF4 hp hp5 hQ hd, hH₀card, hζord, Nat.factorization_pow]
  rfl

@[expose] def negWord : List (Fin Tag.F4.rank) := coxPow 6

theorem wordMat_negWord : wordMat Tag.F4 negWord = -1 := by
  unfold negWord coxPow
  decide +kernel

theorem weylMat_wp_negWord :
    weylMat (wp Tag.F4 negWord) = (-1 : ℤ) • (1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) := by
  rw [weylMat_wp, wordMat_negWord]
  simp

theorem wp_negWord_smul (u : Fin Tag.F4.rank → ℤ) : wp Tag.F4 negWord • u = -u := by
  rw [wp, wordProd_smul_eq_wordMat_mulVec, wordMat_negWord, Matrix.neg_mulVec, Matrix.one_mulVec]

theorem hord_two (hp : p.Prime) (hp5 : 5 ≤ p) (hd : p ∣ Nat.card F + 1) {L : Type} [Field L]
    [Algebra F L] [IsAlgClosure F L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card F) :
    ∃ H : Subgroup (ModGL Tag.F4 L), H ≤
        twistedTorusOf (canonicalRep (coxeterSystem Tag.F4) L (wp Tag.F4 negWord))
          (Units.map (entrywiseHom Fr)) ∧
      (Nat.card (adjointGroup Tag.F4 F)).factorization p ≤ (Nat.card H).factorization p := by
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  obtain ⟨ζ, hζord, hζpow⟩ := exists_unit_orderOf_card_add_one_alg F L
  obtain ⟨H₀, hH₀T, hH₀card⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_le_twistedTorus_card (L := L)
      (fun a => rootDiagUnit_mem_torusGroup a) wp_negWord_smul hFr hζpow
  refine ⟨H₀, hH₀T, le_of_eq ?_⟩
  rw [hH₀card, hζord, card_adjointGroup_F4,
    CFSG.HardMathSupport.Timmesfeld.CrossChar.factorization_ordF4_of_dvd_add_one hp hp5 hq2 hd,
    Nat.factorization_pow]
  rfl

theorem mem_twistedTorus_of_steinberg' {L : Type} [Field L] {Fr : L →+* L} {n g : ModGL Tag.F4 L}
    {Γ T₀ T : Subgroup (ModGL Tag.F4 L)}
    (hΓ : Γ = adjointGroup Tag.F4 L ⊓ (twistedEntrywise n Fr).eqLocus (MonoidHom.id _))
    (hT₀ : T₀ = torusGroup Tag.F4 L ⊓ Γ) (hT : T = T₀.map (MulAut.conj g).toMonoidHom)
    {y : ModGL Tag.F4 L} (hy : y ∈ T) :
    g⁻¹ * y * g ∈ twistedTorus n Fr := by
  rw [hT] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  rw [hT₀] at ht
  obtain ⟨ht1, ht2⟩ := Subgroup.mem_inf.1 ht
  rw [hΓ] at ht2
  have hfix : n * Units.map (entrywiseHom Fr) t * n⁻¹ = t := (Subgroup.mem_inf.1 ht2).2
  have : g⁻¹ * (MulAut.conj g).toMonoidHom t * g = t := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [this]
  exact mem_twistedTorus.2 ⟨ht1, hfix⟩

theorem sylowFrameM_one (hp : p.Prime) (hp5 : 5 ≤ p) (hd : p ∣ Nat.card F - 1) :
    SylowFrameM Tag.F4 F p 1 :=
  exists_exact_frame_sylow (Or.inr rfl) F hp 1 commutator_eq_top
    fun {L} _ _ _ Fr hFr => hord_one hp hp5 hd Fr hFr

theorem sylowFrameM_neg (hp : p.Prime) (hp5 : 5 ≤ p) (hd : p ∣ Nat.card F + 1) :
    SylowFrameM Tag.F4 F p (wp Tag.F4 negWord) :=
  exists_exact_frame_sylow (Or.inr rfl) F hp _ commutator_eq_top
    fun {L} _ _ _ Fr hFr => hord_two hp hp5 hd Fr hFr

theorem sylowFrameM_three (hp : p.Prime) (hp3 : 3 < p)
    (hd : p ∣ Nat.card F ^ 2 + Nat.card F + 1) : SylowFrameM Tag.F4 F p (f4Coxeter ^ 4) :=
  exists_exact_frame_sylow_of_S (Or.inr rfl) F hp _ commutator_eq_top
    fun {L} _ _ _ Fr hFr g0 hg0C hg0 => by
      have hgn : g0⁻¹ * Units.map (entrywiseHom Fr) g0 =
          canonicalRep (coxeterSystem .F4) L (f4Coxeter ^ 4) := by
        rw [hg0]
        group
      obtain ⟨-, hmain⟩ := F4_cyclotomic_three_torus_and_regular_prime_centralizers F L Fr hFr _ rfl
      obtain ⟨hΓ, -, -, -, hp', -⟩ := hmain g0 hg0C hgn _ _ _ rfl rfl rfl
      obtain ⟨⟨S, hS⟩, -⟩ := hp' p hp hp3 hd
      exact ⟨S, fun x hx => mem_twistedTorus_of_steinberg' hΓ rfl rfl (hS ⟨x, hx, rfl⟩)⟩

theorem sylowFrameM_four (hp : p.Prime) (hp3 : 3 < p) (hd : p ∣ Nat.card F ^ 2 + 1) :
    SylowFrameM Tag.F4 F p (f4Coxeter ^ 3) :=
  exists_exact_frame_sylow_of_S (Or.inr rfl) F hp _ commutator_eq_top
    fun {L} _ _ _ Fr hFr g0 hg0C hg0 => by
      have hgn : g0⁻¹ * Units.map (entrywiseHom Fr) g0 =
          canonicalRep (coxeterSystem .F4) L (f4Coxeter ^ 3) := by
        rw [hg0]
        group
      obtain ⟨-, hmain⟩ := F4_cyclotomic_four_torus_and_regular_prime_centralizers F L Fr hFr _ rfl
      obtain ⟨hΓ, -, -, hp', -⟩ := hmain g0 hg0C hgn _ _ _ rfl rfl rfl
      obtain ⟨⟨S, hS⟩, -⟩ := hp' p hp hp3 hd
      exact ⟨S, fun x hx => mem_twistedTorus_of_steinberg' hΓ rfl rfl (hS ⟨x, hx, rfl⟩)⟩

theorem sylowFrameM_six (hp : p.Prime) (hp3 : 3 < p) (hd : p ∣ Nat.card F ^ 2 - Nat.card F + 1) :
    SylowFrameM Tag.F4 F p f4PhiSix :=
  exists_exact_frame_sylow_of_S (Or.inr rfl) F hp _ commutator_eq_top
    fun {L} _ _ _ Fr hFr g0 hg0C hg0 => by
      have hgn : g0⁻¹ * Units.map (entrywiseHom Fr) g0 =
          canonicalRep (coxeterSystem .F4) L f4PhiSix := by
        rw [hg0]
        group
      obtain ⟨-, -, -, -, hmain⟩ := F4_cyclotomic_six_torus_and_surviving_A2_kernels F L Fr hFr _ rfl
      obtain ⟨hΓ, -, -, -, hp', -⟩ := hmain g0 hg0C hgn _ _ _ rfl rfl rfl
      obtain ⟨⟨S, hS⟩, -⟩ := hp' p hp hp3 hd
      exact ⟨S, fun x hx => mem_twistedTorus_of_steinberg' hΓ rfl rfl (hS ⟨x, hx, rfl⟩)⟩

theorem wordMat_nil' : wordMat Tag.F4 ([] : List (Fin Tag.F4.rank)) = 1 := rfl

theorem wcOn_toral [Fact p.Prime] (hp5 : 5 ≤ p) (hpq : ¬ p ∣ Nat.card F) {e : ℕ}
    (he : orderOf ((Nat.card F : ℕ) : ZMod p) = e)
    (hecases : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6) : WCOn p (adjointGroup Tag.F4 F) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hp3 : 3 < p := by omega
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hz1 : weylMat (1 : WeylGroup Tag.F4) =
      (1 : ℤ) • (1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) := by
    rw [weylMat_one, one_smul]
  rcases hecases with rfl | rfl | rfl | rfl | rfl
  ·
    have hd := dvd_sub_one_of_orderOf_eq_one' (by omega) he
    have hF : SylowFrame Tag.F4 F p (wp Tag.F4 ([] : List (Fin Tag.F4.rank))) := by
      rw [wp_nil]
      exact (sylowFrameM_one hp hp5 hd).toSylowFrame
    refine hF.wcOn_dcw (a := r12a) (b := r12b) (c := r12c) (d := r12d) (z := wp Tag.F4 negWord)
      (s := -1) (k := 0) hp2 hpq he weylMat_wp_negWord (Or.inr rfl)
      (by rw [wordMat_nil']; simp) (by rw [wordMat_nil']; simp) (by rw [wordMat_nil']; simp)
      (by rw [wordMat_nil']; simp) (by rw [wordMat_nil', pow_zero, r12_dc]; simp)
      (Or.inr ⟨rfl, dvd_zero _⟩)
  ·
    have hd := dvd_add_one_of_orderOf_eq_two' hp he
    refine (sylowFrameM_neg hp hp5 hd).toSylowFrame.wcOn_dcw (a := r12a) (b := r12b) (c := r12c)
      (d := r12d) (z := wp Tag.F4 negWord) (s := -1) (k := 0) hp2 hpq he weylMat_wp_negWord
      (Or.inr rfl) (by rw [wordMat_negWord]; simp) (by rw [wordMat_negWord]; simp)
      (by rw [wordMat_negWord]; simp) (by rw [wordMat_negWord]; simp)
      (by rw [wordMat_negWord, pow_zero, r12_dc]; simp) (Or.inr ⟨rfl, dvd_zero _⟩)
  ·
    have hd := dvd_phi3_of_orderOf' hp he
    have hF : SylowFrame Tag.F4 F p (wp Tag.F4 (coxPow 4)) := by
      rw [wp_coxPow]
      exact (sylowFrameM_three hp hp3 hd).toSylowFrame
    exact hF.wcOn_dcw (a := r3a) (b := r3b) (c := r3c) (d := r3d) (z := wp Tag.F4 negWord)
      (s := -1) (k := 0) hp2 hpq he weylMat_wp_negWord (Or.inr rfl) r3_comm_a r3_comm_b r3_comm_c
      r3_comm_d r3_dc (Or.inr ⟨rfl, dvd_zero _⟩)
  ·
    have hd := dvd_phi4_of_orderOf' hp he
    have hF : SylowFrame Tag.F4 F p (wp Tag.F4 (coxPow 3)) := by
      rw [wp_coxPow]
      exact (sylowFrameM_four hp hp3 hd).toSylowFrame
    exact hF.wcOn_dcw (a := r4a) (b := r4b) (c := r4c) (d := r4d) (z := 1) (s := 1) (k := 2)
      hp2 hpq he hz1 (Or.inl rfl) r4_comm_a r4_comm_b r4_comm_c r4_comm_d r4_dc
      (Or.inl ⟨rfl, by omega⟩)
  ·
    have hd := dvd_phi6_of_orderOf' hp he
    have hF : SylowFrame Tag.F4 F p (wp Tag.F4 (coxPow 10)) := by
      rw [wp_coxPow]
      exact (sylowFrameM_six hp hp3 hd).toSylowFrame
    exact hF.wcOn_dcw (a := r6a) (b := r6b) (c := r6c) (d := r6d) (z := 1) (s := 1) (k := 3)
      hp2 hpq he hz1 (Or.inl rfl) r6_comm_a r6_comm_b r6_comm_c r6_comm_d r6_dc
      (Or.inl ⟨rfl, by omega⟩)

theorem wcOn_three [Fact p.Prime] (hp3 : p = 3) (hpq : ¬ p ∣ Nat.card F)
    (he : orderOf ((Nat.card F : ℕ) : ZMod p) = 1 ∨ orderOf ((Nat.card F : ℕ) : ZMod p) = 2) :
    WCOn p (adjointGroup Tag.F4 F) := by
  have hp : p.Prime := Fact.out
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hv : ⁅wp Tag.F4 [0], wp Tag.F4 [1]⁆ ^ p = 1 := by
    subst hp3
    exact wp_cw_pow_eq_one (by decide +kernel)
  have hj : ¬ (p : ℤ) ∣ ∑ i, (fun i : Fin Tag.F4.rank => if i = 0 then (1 : ℤ) else 0) i *
      ((weylMat (wp Tag.F4 [0])⁻¹ - 1) * (weylMat ⁅wp Tag.F4 [0], wp Tag.F4 [1]⁆⁻¹ - 1)) i 2 := by
    subst hp3
    rw [weylMat_wp_inv, weylMat_cw_inv]
    decide +kernel
  rcases he with he | he
  · have hd := dvd_sub_one_of_orderOf_eq_one' (by omega) he
    exact (weakFrame_exact (Or.inr rfl) F 1 commutator_eq_top).wcOn_noncomm_one hpq hd hv _ 2 hj
  · have hd := dvd_add_one_of_orderOf_eq_two' hp he
    exact (weakFrame_exact (Or.inr rfl) F (wp Tag.F4 negWord) commutator_eq_top).wcOn_noncomm_neg
      wp_negWord_smul hpq hd hv _ 2 hj

theorem wcOn_adjoint [Fact p.Prime] (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card F) :
    WCOn p (adjointGroup Tag.F4 F) := by
  have hp : p.Prime := Fact.out
  by_cases hcnt : degCount Tag.F4 (orderOf ((Nat.card F : ℕ) : ZMod p)) ≤ 1
  · exact WCOn.of_rankLE1 (rankLE1_F4 F hp hpq hcnt)
  · push Not at hcnt
    obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card F : ℕ) : ZMod p) = e := ⟨_, rfl⟩
    rw [he] at hcnt
    have hlt : e < p := CFSG.LieType.SeitzGeneration.orderOf_lt_prime hp hpq he
    have he30 : e ≤ 30 := le_thirty_of_degCount_pos (τ := Tag.F4) (Or.inl rfl) (by omega)
    have hecases : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6 := by
      interval_cases e <;> first | omega | exact absurd hcnt (by decide)
    rcases eq_three_or_five_le' hp hp2 with hp3 | hp5
    · refine wcOn_three hp3 hpq ?_
      rw [he]
      omega
    · exact wcOn_toral hp5 hpq he hecases

end F4

theorem wcOn_f4_model {K : Type} [Group K] [Finite K] {ℓ f p : ℕ} [Fact p.Prime] (hℓ : ℓ.Prime)
    (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (h : UntwistedChevalleyModel K Tag.F4 (ℓ ^ f)) : WCOn p K :=
  wcOn_of_untwisted_model hℓ hpℓ h fun F _ _ _ hpq => F4.wcOn_adjoint hp2 hpq

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw
