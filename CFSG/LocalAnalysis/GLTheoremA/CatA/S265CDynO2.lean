module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynClassical

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265C.DynO

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU heldGU)
open CFSG.Assembly (LargeEvenProjMk LargeEvenProj)

@[expose] def ClassicalOr360 (X : Type) [Group X] : Prop :=
  (∃ (t : StatedLieTag) (r e : ℕ),
      (t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus) ∧
      CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) t r 2 e) ∨
    Nonempty (X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6))

theorem classicalOr360_of_model {X : Type} [Group X] {t : StatedLieTag} {r e : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (h : StatedClassicalModel (X ⧸ Subgroup.center X) t r 2 e) : ClassicalOr360 X := by
  refine Or.inl ⟨t, r, e, ht, Or.inl ⟨?_, h⟩⟩
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide

theorem ClassicalOr360.of_mulEquiv {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y)
    (h : ClassicalOr360 Y) : ClassicalOr360 X := by
  rcases h with ⟨t, r, k, ht, hm⟩ | h
  · exact Or.inl ⟨t, r, k, ht, CFSG.Blueprint.LieModel.quotient_center_of_mulEquiv φ.symm hm⟩
  · obtain ⟨e⟩ := h
    exact Or.inr ⟨(QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) φ
      (Subgroup.map_center_eq φ)).trans e⟩

theorem classicalOr360_of_quot_statedSL {X : Type} [Group X] [Finite X] {a k : ℕ} {E : Type}
    [Field E] [Finite E] (hJ : CFSG.Open.IsQuasisimple X) (ha : 2 ≤ a)
    (hE : Nat.card E = 2 ^ k)
    (hφ : Nonempty (X ⧸ Subgroup.center X ≃* StatedProj (StatedSL a E))) :
    ClassicalOr360 X := by
  by_cases h22 : a = 2 ∧ k = 1
  ·
    obtain ⟨rfl, rfl⟩ := h22
    have hE2 : Nat.card E = 2 := by simpa using hE
    obtain ⟨φ⟩ := hφ
    have hcard : Nat.card (X ⧸ Subgroup.center X) < 60 := by
      rw [Nat.card_congr φ.toEquiv]
      have hdvd : Nat.card (StatedProj (StatedSL 2 E)) ∣ Nat.card ↥(StatedSL 2 E) :=
        Subgroup.index_dvd_card _
      rw [CFSG.Open.StatedAPI.card_statedSL_two E, hE2] at hdvd
      norm_num at hdvd
      exact lt_of_le_of_lt (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num)
    haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hJ.2
    haveI : Group.IsSolvable (X ⧸ Subgroup.center X) :=
      CFSG.GroupTheory.groups_order_below_sixty_solvable hcard
    exact (CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.not_isSolvable_quot_center
      (J := X) inferInstance).elim
  · have hk : 1 ≤ k := by
      have h2 : 1 < Nat.card E := Finite.one_lt_card
      rw [hE] at h2
      by_contra hk0
      rw [show k = 0 by omega, pow_zero] at h2
      omega
    have hadm : StatedLieAdmissible .PSL a 2 k := by
      refine ⟨Nat.prime_two, hk, ha, ?_, ?_⟩
      · intro h
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        exact h22 ⟨h1, Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm)⟩
      · intro h
        obtain ⟨-, h3⟩ := Prod.mk.inj h
        have hdvd : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
        rw [h3] at hdvd
        norm_num at hdvd
    exact classicalOr360_of_model (Or.inl rfl) ⟨hadm, E, inferInstance, inferInstance, hE, hφ⟩

theorem classicalOr360_of_quot_heldSU {X : Type} [Group X] [Finite X] {a k : ℕ} {E : Type}
    [Field E] [Finite E] (hJ : CFSG.Open.IsQuasisimple X) (τ' : E ≃+* E)
    (hτ' : ∀ x, τ' (τ' x) = x) (ha : 2 ≤ a)
    (hτ'k : ∀ x, τ' x = x ^ (2 ^ k)) (hE : Nat.card E = (2 ^ k) ^ 2)
    (hφ : Nonempty (X ⧸ Subgroup.center X ≃*
      ↥(heldSU a E τ' hτ') ⧸ Subgroup.center ↥(heldSU a E τ' hτ'))) :
    ClassicalOr360 X := by
  obtain ⟨φ⟩ := hφ
  have hk : 1 ≤ k := by
    by_contra hk0
    have h2 : 2 ≤ Nat.card E := Finite.one_lt_card
    rw [hE, show k = 0 by omega] at h2
    norm_num at h2
  rcases Nat.lt_or_ge a 3 with ha3 | ha3
  · obtain rfl : a = 2 := by omega
    obtain ⟨K, hKf, hKfin, hk', ⟨ψ⟩⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_quot_heldSU_two_equiv_psl
        τ' hτ' hτ'k hE
    exact classicalOr360_of_quot_statedSL hJ le_rfl hk' ⟨φ.trans ψ⟩
  · by_cases h31 : a = 3 ∧ k = 1
    ·
      obtain ⟨rfl, rfl⟩ := h31
      haveI := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.isSolvable_quot_heldSU_three_two
        τ' hτ' (fun x => by simpa using hτ'k x) (by simpa using hE)
      haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hJ.2
      exact (CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.not_isSolvable_quot_center
        (J := X) (solvable_of_surjective (f := φ.symm.toMonoidHom)
          φ.symm.surjective)).elim
    · have hak : (a, 2 ^ k) ≠ (3, 2) := by
        intro h
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        exact h31 ⟨h1, Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm)⟩
      obtain ⟨ψ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.nonempty_quot_heldSU_equiv_statedProj
        CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.uniScalar_holds τ' hτ' hτ'k hE ha3 hak
      exact classicalOr360_of_model (Or.inr (Or.inl rfl))
        ⟨⟨Nat.prime_two, hk, ha3, hak⟩, E, inferInstance, inferInstance, hE, ⟨φ.trans ψ⟩⟩

theorem classicalOr360_of_quot_statedSp {X : Type} [Group X] {s k : ℕ} {E : Type}
    [Field E] [Finite E] (hs : 2 ≤ s) (hE : Nat.card E = 2 ^ k)
    (hne : ¬(s = 2 ∧ Nat.card E = 2))
    (φ : X ⧸ Subgroup.center X ≃* StatedProj (StatedSp s E)) : ClassicalOr360 X := by
  have hk : 1 ≤ k := by
    by_contra hk0
    have h2 : 2 ≤ Nat.card E := Finite.one_lt_card
    rw [hE, show k = 0 by omega] at h2
    norm_num at h2
  have hne' : (s, 2 ^ k) ≠ (2, 2) := by
    intro h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact hne ⟨h1, by rw [hE, h2]⟩
  exact classicalOr360_of_model (Or.inr (Or.inr (Or.inl rfl)))
    ⟨⟨Nat.prime_two, hk, hs, hne'⟩, E, inferInstance, inferInstance, hE, ⟨φ⟩⟩

theorem classicalOr360_of_quot_sp42 {X Y : Type} [Group X] [Group Y] {F : Type} [Field F]
    [Finite F] (hK2 : Nat.card F = 2) (eX : X ≃* ↥(commutator (StatedSp 2 F)))
    (eY : Y ⧸ Subgroup.center Y ≃* X ⧸ Subgroup.center X) : ClassicalOr360 Y := by
  have hZA : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; decide)
  have hA : X ≃* alternatingGroup (Fin 6) :=
    eX.trans (CFSG.SignalizerFunctorTheorem.NonLocal.commutatorSpTwoEquiv hK2)
  have hZ : Subgroup.center X = ⊥ := by
    have h : (Subgroup.center X).map (hA : X →* alternatingGroup (Fin 6)) = ⊥ := by
      rw [Subgroup.map_center_eq hA, hZA]
    exact Subgroup.map_injective hA.injective (h.trans (Subgroup.map_bot _).symm)
  exact Or.inr ⟨eY.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    (QuotientGroup.quotientBot.trans hA))⟩

theorem classicalOr360_of_spCover {X : Type} [Group X] {m k : ℕ} {K : Type} [Field K]
    [Finite K] (hm : 2 ≤ m) (hne : ¬(m = 2 ∧ Nat.card K = 2)) (hK : Nat.card K = 2 ^ k)
    (g : StatedSp m K →* X) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center (StatedSp m K)) : ClassicalOr360 X := by
  haveI : Fintype K := Fintype.ofFinite K
  have hne' : (m, Fintype.card K) ≠ (2, 2) := fun h =>
    hne ⟨(Prod.mk.inj h).1, by rw [Nat.card_eq_fintype_card]; exact (Prod.mk.inj h).2⟩
  have hSpPerf : commutator (StatedSp m K) = ⊤ :=
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFactorFacts_holds K m hm hne').perfect
  obtain ⟨e₁⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.center_quot_equiv_of_surjective
    hSpPerf g hg hker
  have hchar : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  obtain ⟨e₂⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sp
    (s := m) hm hne hchar (MulEquiv.refl _)
  exact classicalOr360_of_quot_statedSp hm hK hne (e₁.trans e₂)

section Families


theorem classicalOr360_lin {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥) (hF : FamLin labL)
    (hin : InnDiagKind S labL β) (hβp : β ^ p = 1) {J : Subgroup S}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) : ClassicalOr360 ↥J := by
  classical
  obtain ⟨F, hF', hFf, d, hd, hcard, A, u, e, hαu, hu⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.innDiag_linear_data hcen hF hin
  have h2 : (2 : F) = 0 := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.two_eq_zero_of_card hcard
  have hue : MulAut.congr e β = u := by
    ext z
    obtain ⟨l, rfl⟩ := e.surjective z
    show e (β (e.symm (e l))) = u (e l)
    rw [MulEquiv.symm_apply_apply]
    exact hαu l
  have hupow : u ^ p = 1 := by rw [← hue, ← map_pow, hβp, map_one]
  obtain ⟨c, hc⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.isScalar_of_pow_trivial
    h2 A p u hu hupow
  have hodd := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.odd_orderOf_of_pow_scalar h2 hd A
    (hp.odd_of_ne_two hp2) hc
  have hord := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.cast_orderOf_ne_zero_of_odd h2 A hodd
  have hJ' := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.isComponentOf_transport e β hJ
  rw [hue] at hJ'
  obtain ⟨M, hM, hMJ⟩ := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.exists_isComponentOf_lift
    (LargeEvenProjMk (StatedSL d F)) (QuotientGroup.mk'_surjective _)
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.ker_projMk_le_center
    (CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.conjSL A) u
    (fun k => (hu k (CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.conjSL A k) rfl).symm) hJ'
  have hMinj : Function.Injective (StatedSL d F).subtype := Subtype.val_injective
  have hM' : IsComponentOf (M.map (StatedSL d F).subtype)
      (Subgroup.centralizer ({A} : Set (GL (Fin d) F)) ⊓ StatedSL d F) := by
    rw [← CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.map_fixSubgroup_conjSL A]
    refine CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_map _ (fun g hg => ?_) hM
    rw [show g = 1 from hMinj (by simpa using hg)]
    exact one_mem _
  obtain ⟨a, E, hEf, hEalg, hEfin, ha, ⟨eM⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.held_linear_components_gl
      CFSG.LieType.SemisimpleCentralizers.Held.SLComponentsTrivial_holds A hord _ hM'
  obtain ⟨eJM⟩ := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.nonempty_centerQuot_of_map_eq
    (LargeEvenProjMk (StatedSL d F))
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.ker_projMk_le_center hM.2.2.1 hMJ
  obtain ⟨eMZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv
    (Subgroup.equivMapOfInjective M _ hMinj)
  letI := hEf
  letI := hEalg
  obtain ⟨k, hk⟩ := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.exists_card_eq_two_pow
    (F := F) (E := E) h2
  exact ClassicalOr360.of_mulEquiv (J.equivMapOfInjective e.toMonoidHom e.injective)
    (classicalOr360_of_quot_statedSL hJ'.2.2 ha hk ⟨(eJM.trans eMZ).trans eM⟩)

theorem classicalOr360_uni {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥) (hFam : FamUni labL)
    (hin : InnDiagKind S labL β) (hβp : β ^ p = 1) {J : Subgroup S}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) : ClassicalOr360 ↥J := by
  classical
  obtain ⟨F, hF', hFf, d, τ, hτ, hτQ, hcardF, hd, hd3, A, u, e, hA, hαu, hu⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.innDiag_unitary_data hcen hFam hin
  have h2 : (2 : F) = 0 := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.two_eq_zero_of_card
    (n := 2 * labL.n) (by rw [hcardF, ← pow_mul, Nat.mul_comm])
  generalize hQdef : 2 ^ labL.n = Q at *
  have hdQ : (d, Q) ≠ (3, 2) := by
    intro h
    obtain ⟨h1, h2'⟩ := Prod.mk.inj h
    have hn2 := hd3 h1
    have : 4 ≤ Q := by
      rw [← hQdef]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ labL.n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have hue : MulAut.congr e β = u := by
    ext z
    obtain ⟨l, rfl⟩ := e.surjective z
    show e (β (e.symm (e l))) = u (e l)
    rw [MulEquiv.symm_apply_apply]
    exact hαu l
  have hpow : u ^ p = 1 := by rw [← hue, ← map_pow, hβp, map_one]
  have hord := CFSG.LocalAnalysis.GLTheoremA.I141F.Cls.compType_uni_scalar h2 hτ hτQ A hA hp hp2
    hcardF hd hdQ u hu hpow
  rcases CFSG.LocalAnalysis.GLTheoremA.I141F.Cls.compType_uni_decomp hτ hτQ hcardF hA hord hu hue
      hJ with
    ⟨a, dd, E, hE, hEfin, τ', hτ', ha2, hτ'Q, hcardE, ⟨eM⟩⟩ |
    ⟨b, e', E, hE, hEfin, hb2, hcardE, ⟨eM⟩⟩
  · letI := hE
    have hpw : Q ^ dd = 2 ^ (labL.n * dd) := by rw [← hQdef, ← pow_mul]
    rw [hpw] at hτ'Q hcardE
    exact classicalOr360_of_quot_heldSU hJ.2.2 τ' hτ' ha2 hτ'Q hcardE ⟨eM⟩
  · letI := hE
    have hpw : Q ^ (2 * e') = 2 ^ (labL.n * (2 * e')) := by rw [← hQdef, ← pow_mul]
    rw [hpw] at hcardE
    exact classicalOr360_of_quot_statedSL hJ.2.2 hb2 hcardE ⟨eM⟩

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag in
theorem classicalOr360_symp {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥)
    (ht : labL.tag = .B ∨ labL.tag = .C) (hin : InnDiagKind S labL β) (hβp : β ^ p = 1)
    {J : Subgroup S} (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) : ClassicalOr360 ↥J := by
  classical
  obtain ⟨F, hF, hFf, r, hr, hn, hcard, h2, e, A, hαA⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.I141F.Cls.compType_symp_data hcen ht hin
  letI := hF
  letI := hFf
  obtain ⟨x, hx⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnSympRed.exists_conjAut_eq_conj h2 A
  have hMEq : MulAut.congr e β = MulAut.conj (proj r F x) := by
    rw [← hx]
    ext z
    have h1 := hαA (e.symm z)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  have hZ : Subgroup.center (StatedProj (StatedSp r F)) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e.symm z ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hz (e g)
    rw [hcen, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    simpa using congrArg e hz'
  have hpow : MulAut.conj (proj r F x) ^ p = 1 := by
    rw [← hMEq, ← map_pow, hβp, map_one]
  have hxp : x ^ p = 1 :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnSympRed.pow_eq_one_of_conj_pow_eq_one h2 hZ hpow
  have hJ' := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.isComponentOf_transport e β hJ
  rw [hMEq] at hJ'
  obtain ⟨-, hcomp⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompsCore_conj_sp_card (a6 := False)
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFourTwoFacts_holds
      (fun h => h.elim) (fun h => h.elim) (fun h => h.elim)
      hp hp2 Nat.prime_two hn hcard (by omega) hp2 (fun h => h.elim) x hxp
  obtain ⟨X, inst, hXfin, ⟨hXLie, -⟩, hfac, f, hf, hker⟩ := hcomp _ hJ'
  letI := inst
  obtain ⟨eJ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.center_quot_equiv_of_surjective
    hXLie.perfect f hf hker
  unfold CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SpFactorOver at hfac
  rcases hfac with hSL | hSU | hSp | hSp42
  · rw [hcard] at hSL
    obtain ⟨b, k, E, _, _, hb, hE, -, hφ⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.linCase_of_factor eJ hSL
    exact ClassicalOr360.of_mulEquiv (J.equivMapOfInjective e.toMonoidHom e.injective)
      (classicalOr360_of_quot_statedSL hJ'.2.2 hb hE hφ)
  · rw [hcard] at hSU
    obtain ⟨b, k, E, _, _, τ, hτ, hb, hτk, hE, -, hφ⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.uniCase_of_factor eJ hSU
    exact ClassicalOr360.of_mulEquiv (J.equivMapOfInjective e.toMonoidHom e.injective)
      (classicalOr360_of_quot_heldSU hJ'.2.2 τ hτ hb hτk hE hφ)
  · obtain ⟨-, -, s, hs2, hne, ⟨eX⟩⟩ := hSp
    have hne' : ¬(s = 2 ∧ Nat.card F = 2) := fun h => hne (by rw [h.1, h.2])
    have hchar : CharP F 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hcard
    obtain ⟨eXZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sp
      (s := s) hs2 hne' hchar eX
    exact ClassicalOr360.of_mulEquiv (J.equivMapOfInjective e.toMonoidHom e.injective)
      (classicalOr360_of_quot_statedSp hs2 hcard hne' (eJ.trans eXZ))
  · obtain ⟨-, -, hK2, ⟨eX⟩⟩ := hSp42
    exact ClassicalOr360.of_mulEquiv (J.equivMapOfInjective e.toMonoidHom e.injective)
      (classicalOr360_of_quot_sp42 hK2 eX eJ)

open CFSG.LocalAnalysis.GLTheoremA.Y10GInnOrthModel in
theorem classicalOr360_orth {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥) (hF : FamOrth labL)
    (hin : InnDiagKind S labL β) (hβp : β ^ p = 1) {J : Subgroup S}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) : ClassicalOr360 ↥J := by
  obtain ⟨hmodel, a, rfl⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnOrthMark.innDiagKind_orth_data hcen hF hin
  have hap : a ^ p = 1 := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.pow_eq_one_of_conj_pow_eq_one
    hcen hβp
  obtain ⟨t, ht, hG⟩ : ∃ t : StatedLieTag, (t = .POmegaPlus ∨ t = .POmegaMinus) ∧
      StatedClassicalModel S t labL.rank 2 (canonLabel labL).n := by
    rcases hmodel with hG | hG
    · exact ⟨_, Or.inl rfl, hG⟩
    · exact ⟨_, Or.inr rfl, hG⟩
  obtain ⟨X, inst, -, hXLie, hfac, -, g, hg, hker⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_lieFactor_of_component_conj_omega_card
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.omegaFactorField_holds
      hp hp2 (Or.inr ht) hG hp2 a hap J hJ
  letI := inst
  obtain ⟨eJ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.center_quot_equiv_of_surjective
    hXLie.perfect g hg hker
  unfold CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthFactorOver at hfac
  rcases hfac with hSL | hSU | hSp | hOm
  · obtain ⟨b, k, E, _, _, hb, hE, -, hφ⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.linCase_of_factor eJ hSL
    exact classicalOr360_of_quot_statedSL hJ.2.2 hb hE hφ
  · obtain ⟨b, k, E, _, _, τ, hτ, hb, hτk, hE, -, hφ⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.uniCase_of_factor eJ hSU
    exact classicalOr360_of_quot_heldSU hJ.2.2 τ hτ hb hτk hE hφ
  · obtain ⟨K', _, _, hK'card, hK'ring, s, hs2, hne, ⟨eX⟩⟩ := hSp
    haveI : Finite K' := Finite.of_fintype K'
    have hchar : CharP K' 2 := ringChar.of_eq hK'ring
    have hne' : ¬(s = 2 ∧ Nat.card K' = 2) := fun h => hne (by rw [h.1, h.2])
    obtain ⟨eXZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sp
      (s := s) hs2 hne' hchar eX
    exact classicalOr360_of_quot_statedSp hs2 hK'card hne' (eJ.trans eXZ)
  · obtain ⟨K', _, _, V, _, _, _, Q, hK'card, _, hQ, hd, hT, ⟨eX⟩⟩ := hOm
    obtain ⟨s, hs⟩ :=
      exists_statedClassicalModel_quotCenter_orthDerived hK'card hQ hd hT eX
    rcases hs with hplus | hminus
    · exact classicalOr360_of_model (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eJ.symm hplus)
    · exact classicalOr360_of_model (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
        (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eJ.symm hminus)

end Families

section F4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType.RecipeExcLang
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw
open CFSG.LocalAnalysis.GLTheoremA.CanonTriL
open scoped MatrixGroups commutatorElement


theorem classicalOr360_f4_class_nonA {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.F4 L p₀) (hch : ringChar L = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Fin Tag.F4.rank → Lˣ} (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus)
    (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit Tag.F4 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hqs : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ClassicalOr360 ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  have hp2' : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  rcases f4_nonA_casesP2 hp hp2' S hpL hTp h1 i hnonA with ⟨v, hroots, -, -⟩ |
      ⟨v, J, hJ, hroots, -, -⟩
  · by_cases hQ : 3 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
    · obtain ⟨K', hfin, hne, g, hg, hker⟩ := exists_spCover_of_spRange S hT i hinner (m := 2) le_rfl
        (fun K' hfin hcardK' => by
          haveI := hfin
          obtain ⟨k, hk⟩ := card_subfield_eq_two_pow hch K'
          have h3 : 3 ≤ Nat.card ↥K' := hcardK' ▸ hQ
          have h4 : 4 ≤ Nat.card ↥K' := by
            rw [hk] at h3 ⊢
            rcases Nat.lt_or_ge k 2 with hk2 | hk2
            · interval_cases k <;> omega
            · calc 4 = 2 ^ 2 := by norm_num
                _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
          haveI : CharP ↥K' 2 := ringChar.of_eq (by rw [ringChar_subfield' K', hch])
          refine ⟨fun h => by omega, ?_⟩
          obtain ⟨Ψ, hΨker, hΨrange⟩ := spRange_f4_B2 h4
          rw [CFSG.RankThree.Chevalley.subsystemGroup_eq_iSup_rootSubgroup (τ := Tag.F4)
            (J := f4LeviB2) ↥K'] at hΨrange
          obtain ⟨Ψ', h', hr'⟩ := spRange_rootSpan_smul v (fun α hα => hα.1) hΨker hΨrange
          refine ⟨Ψ', h', ?_⟩
          rw [hr']
          show _ = rootSpan Tag.F4 ↥K' (componentRoots (rootCharHom a) i)
          rw [hroots])
      haveI := hfin
      obtain ⟨k, hk⟩ := card_subfield_eq_two_pow hch K'
      exact classicalOr360_of_spCover le_rfl hne hk g hg hker
    · obtain ⟨K', hfin, hK2, ⟨eR⟩⟩ :=
        exists_sp42_equiv_rationalComponent S hT i v hroots hinner (not_le.1 hQ) hqs
      haveI := hfin
      let eZ := QuotientGroup.congr
        (Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
        (Subgroup.center ↥(commutator (StatedSp 2 ↥K'))) eR.symm
        (Subgroup.map_center_eq eR.symm)
      exact classicalOr360_of_quot_sp42 hK2 (MulEquiv.refl _) eZ
  · obtain ⟨K', hfin, hne, g, hg, hker⟩ := exists_spCover_of_spRange S hT i hinner (m := 3)
      (by norm_num) (fun K' hfin hcardK' => by
        haveI := hfin
        obtain ⟨k, hk⟩ := card_subfield_eq_two_pow hch K'
        have hk0 : 0 < k := by
          rcases Nat.eq_zero_or_pos k with h0 | h0
          · have : 1 < Nat.card ↥K' := Finite.one_lt_card
            rw [hk, h0] at this
            norm_num at this
          · exact h0
        refine ⟨fun h => by omega, ?_⟩
        obtain ⟨Ψ, hΨker, hΨrange⟩ := spRange_f4_levi hJ hk0 hk
        rw [CFSG.RankThree.Chevalley.subsystemGroup_eq_iSup_rootSubgroup (τ := Tag.F4)
          (J := J) ↥K'] at hΨrange
        obtain ⟨Ψ', h', hr'⟩ := spRange_rootSpan_smul v (fun α hα => hα.1) hΨker hΨrange
        refine ⟨Ψ', h', ?_⟩
        rw [hr']
        show _ = rootSpan Tag.F4 ↥K' (componentRoots (rootCharHom a) i)
        rw [hroots])
    haveI := hfin
    obtain ⟨k, hk⟩ := card_subfield_eq_two_pow hch K'
    exact classicalOr360_of_spCover (by norm_num) hne hk g hg hker

theorem classicalOr360_adjointF4 {K : Type} [Field K] [Finite K] (hK2 : ringChar K = 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {β : MulAut ↥(adjointGroup .F4 K)} (hβmem : β ∈ innAutDerived ↥(adjointGroup .F4 K))
    (hβp : β ^ p = 1) (hβ1 : β ≠ 1) {J : Subgroup ↥(adjointGroup .F4 K)}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) : ClassicalOr360 ↥J := by
  classical
  obtain ⟨h, hh, hβh, hp1, hh1⟩ := exists_inndiag_of_mem_innAutDerived_F4 β hβmem hβp hβ1
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hcardK⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcardK
  have hpℓ : p ≠ ringChar K := by rw [hK2]; exact hp2
  have hpK : ¬ p ∣ Nat.card K := fun h' =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow (hK ▸ h')))
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ f.pos hp hp2 hpℓ
  have hp₀K : ¬ p₀ ∣ Nat.card K := fun hd =>
    hp₀ℓ ((Nat.prime_dvd_prime_iff_eq hp₀ hℓ).1 (hp₀.dvd_of_dvd_pow (hK ▸ hd)))
  have hq₀' : 5 ≤ p₀ ∨ 4 ≤ Nat.card K := by rw [hK]; exact hq₀
  have hmon : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt .F4 p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) hp hp2
  have hperf : commutator ↥(adjointGroup .F4 K) = ⊤ := single_edge_perfect .F4 K (by simp)
  obtain ⟨S, a, ι, _hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime (τ := .F4) (Or.inr (Or.inl rfl)) hp hpK hp₀ hp₀K hq₀'
      hmon hperf β h (baseChange_mem_adjointGroup_of_mem_inndiag hh) hβh hp1 hh1
  have hℓL : ringChar (AlgebraicClosure K) = ringChar K := ringChar_algebraicClosure K
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne hp (by rw [hℓL]; exact hpℓ.symm)
  have hsmall : Tag.F4 = .G2 → 5 ≤ p ∨ 4 ≤ S.D.q := fun h => absurd h (by decide)
  have hTame := langSetup_hTame_of_prime S hp hpL hsmall hT hap h1
  obtain ⟨i, hqs, hJR⟩ := components_of_langSetup S hp ι hinj hrange β hconj hT hap h1 hTame hJ
  let eJ : ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  have hch : ringChar (AlgebraicClosure K) = 2 := by rw [hℓL, hK2]
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · obtain ⟨ν, f', -, -, -, hmodel⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.RationalModel.rationalComponent_typeA_model S hp hT hap h1 i hA
        hqs
    rw [hch] at hmodel
    refine ClassicalOr360.of_mulEquiv eJ ?_
    rcases hmodel with hM | hM
    · exact classicalOr360_of_model (Or.inl rfl) hM
    · exact classicalOr360_of_model (Or.inr (Or.inl rfl)) hM
  · by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · exact ClassicalOr360.of_mulEquiv eJ
        (classicalOr360_f4_class_nonA S hch hp hp2 hT hap h1 i hA hinner hqs)
    · have hp2' : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
      rcases f4_nonA_casesP hp hp2' S hpL hTp h1 i hA with ⟨hr, hn⟩ | ⟨_, _, -, -, hr, hn⟩
      · exact (hinner (twistInner_of_shape S hT i 2 8 hr hn (by omega) (by omega) (by omega)
          (by omega))).elim
      · exact (hinner (twistInner_of_shape S hT i 3 18 hr hn (by omega) (by omega) (by omega)
          (by omega))).elim

theorem classicalOr360_F4 {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥)
    (hin : CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind S labL β) (hβp : β ^ p = 1)
    (hβ1 : β ≠ 1) (ht : labL.tag = .F4) {J : Subgroup S}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) : ClassicalOr360 ↥J := by
  classical
  have hS : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel S (· = labL) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hin
  have hβmem : β ∈ innAutDerived S := mem_innAutDerived_of_innDiagKind_exc hcen (Or.inl ht) hin
  have hM := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel hS
  obtain ⟨t, r, n⟩ := labL
  simp only at ht
  subst ht
  have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .F4 0 2 n := hM
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ :=
    CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLM
  have hZ : Subgroup.center ↥(adjointGroup .F4 K) = ⊥ := center_adjointGroup_eq_bot
  let ψ : S ≃* ↥(adjointGroup .F4 K) :=
    (CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans
      (e₀.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot))
  have hK2 : ringChar K = 2 := by
    haveI := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
    exact ringChar.eq K 2
  have hβ'mem : MulAut.congr ψ β ∈ innAutDerived _ := (mem_innAutDerived_congr ψ).2 hβmem
  have hβ'p : (MulAut.congr ψ β) ^ p = 1 := by rw [← map_pow, hβp, map_one]
  have hβ'1 : MulAut.congr ψ β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr ψ).injective (by rw [h, map_one]))
  exact ClassicalOr360.of_mulEquiv (J.equivMapOfInjective ψ.toMonoidHom ψ.injective)
    (classicalOr360_adjointF4 hK2 hp hp2 hβ'mem hβ'p hβ'1 (isComponentOf_transport ψ β hJ))

end F4

end CFSG.LocalAnalysis.GLTheoremA.S265C.DynO

end
