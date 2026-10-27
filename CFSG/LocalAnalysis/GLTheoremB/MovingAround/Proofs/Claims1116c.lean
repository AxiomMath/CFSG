module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1116b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.CrossCharOdd
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporLie
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenShape
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SporFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporJ4
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Final
import CFSG.GH74.Uniqueness.SU.KI8C
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24LeafShape
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCheck

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1116c

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple PSimple PQuot catalogIs onLie ambiguousChev)
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Aut

theorem le_of_sq_dvd {p N m : ℕ} (hp : p.Prime) (hN : N ≠ 0) (h : p ^ 2 ∣ N)
    (hall : ∀ q ∈ N.primeFactorsList, q ^ 2 ∣ N → q ≤ m) : p ≤ m :=
  hall p ((Nat.mem_primeFactorsList hN).2 ⟨hp, (dvd_pow_self p two_ne_zero).trans h⟩) h

theorem p_eq_of_card_eq {q' : TauCeti.PrimePower} {r k : ℕ} (hr : r.Prime) (h : q'.card = r ^ k) :
    q'.p = r := by
  have h1 : q'.p ∣ r ^ k := by
    rw [← h, TauCeti.PrimePower.card_def]
    exact dvd_pow_self q'.p q'.exponent_pos.ne'
  exact (Nat.prime_dvd_prime_iff_eq q'.prime_p hr).1 (q'.prime_p.dvd_of_dvd_pow h1)

theorem card_mulAut_alt {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6) :
    Nat.card (MulAut (alternatingGroup (Fin n))) = n.factorial := by
  rw [← Nat.card_congr (Equiv.ofBijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6)), Nat.card_perm,
    Nat.card_fin]

theorem pRank_aut_le_one {p : ℕ} (hp : p.Prime) {K T : Type} [Group K] [Finite K] [Group T]
    (hperf : commutator K = ⊤) (e : K ⧸ Subgroup.center K ≃* T) {N : ℕ}
    (hN : Nat.card (MulAut T) ∣ N) (hpN : ¬ p ^ 2 ∣ N) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsPerfect K := ⟨hperf⟩
  haveI : Finite (MulAut K) := MulEquiv.finite_left
  set ψ : MulAut K →* MulAut T :=
    (MulAut.congr e).toMonoidHom.comp
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K) with hψ
  have hψinj : Function.Injective ψ := (MulAut.congr e).injective.comp
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective K)
  refine InputsSeitz.pRank_top_le_of_forall hp fun A hA => ?_
  have hdvd : Nat.card A ∣ N := by
    rw [← Subgroup.card_map_of_injective hψinj]
    exact (Subgroup.card_subgroup_dvd_card _).trans hN
  by_contra hlt
  push Not at hlt
  rw [GL83.PiGen.card_eq_pow_pRank hA] at hdvd
  exact hpN ((pow_dvd_pow p hlt).trans hdvd)

theorem card_mulAut_L27 {T : Type} [Group T] {q' : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.A 1 q').Valid} (h7 : q'.card = 7)
    (e : T ≃* (TauCeti.CFSGIndex.lie ⟨.A 1 q', hv⟩).Group) : Nat.card (MulAut T) = 336 := by
  haveI : Fact q'.p.Prime := ⟨q'.prime_p⟩
  have hF : Nat.card (GaloisField q'.p q'.exponent) = 7 := by
    rw [GaloisField.card _ _ q'.exponent_pos.ne', ← TauCeti.PrimePower.card_def, h7]
  let f : T ≃* CFSG.GH74.GLS.IVK.L2 (GaloisField q'.p q'.exponent) :=
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q' hv)).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
        (GaloisField q'.p q'.exponent))
  have hT : Nat.card T = 168 :=
    Prop1116Design.card_statedProj_two_seven ⟨_, inferInstance, inferInstance, hF, ⟨f⟩⟩
  haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [hT]; norm_num)
  rw [CFSG.GH74.Uniqueness.SU.K.KI8.card_aut_eq ⟨by rw [hF]; decide, by rw [hF]; norm_num⟩ f
    (by norm_num) hF, hT]

end Aut

section Seitz

open GL83.CompFam

@[expose] def Input23_10FaithThree : Prop :=
  ∀ (q : ℕ), q.Prime → q ≠ 2 → q ≠ 3 →
    ∀ (Y : Type) [Group Y] [Finite Y], GLAPPrimeCore 3 Y = ⊥ →
      ∀ (K B : Subgroup Y), IsComponentOf K ⊤ → IsElemAbelian 3 B →
        B ≤ Subgroup.normalizer (K : Set Y) → B ⊓ Subgroup.centralizer (K : Set Y) = ⊥ →
        3 < Nat.card B → Nat.card B ≤ 3 ^ 3 → IsLieChar (· = q) ↥K → Lemma1314.IsGMinusOne 3 B K

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ}

theorem iSup_gLBConj_eq {A K : Subgroup Y} (hA : A ≤ Subgroup.normalizer (K : Set Y)) :
    (⨆ g ∈ A, GLBConj g K) = K := by
  apply le_antisymm
  · exact iSup₂_le fun g hg => (gLBConj_eq_of_mem_normalizer (hA hg)).le
  · exact le_iSup₂_of_le (f := fun g (_ : g ∈ A) => GLBConj g K) 1 (one_mem _) (gLBConj_one K).ge

theorem isGMinusOne_of_faithful (hp : p.Prime) {K A : Subgroup Y} (hA : IsElemAbelian p A)
    (hAN : A ≤ Subgroup.normalizer (K : Set Y))
    (hcard : p * Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set Y)) < Nat.card A)
    (hres : ∀ B₁ : Subgroup Y, IsElemAbelian p B₁ → B₁ ≤ Subgroup.normalizer (K : Set Y) →
      B₁ ⊓ Subgroup.centralizer (K : Set Y) = ⊥ → p < Nat.card B₁ → Lemma1314.IsGMinusOne p B₁ K) :
    Lemma1314.IsGMinusOne p A K :=
  InputsSeitz.isGMinusOne_of_faithful_le hp hA hAN hcard fun B₁ hB₁ hB₁N hfaith hB₁card _ =>
    hres B₁ hB₁ hB₁N hfaith hB₁card

theorem exc5_of_i2310Exc5 {K : Subgroup Y} (h : Lemma1314.I2310Exc5 K) :
    Claims1116.Exc5 (↥K ⧸ Subgroup.center ↥K) := by
  rcases h with ⟨idx, h, e⟩ | ⟨idx, h, e⟩ | ⟨idx, h, e⟩
  · exact ⟨idx, Or.inl h, e⟩
  · exact ⟨idx, Or.inr (Or.inr h), e⟩
  · exact ⟨idx, Or.inr (Or.inl h), e⟩

section Cert


theorem rankOne_or_lieChar (hp : p.Prime) (hp2 : p ≠ 2) {r : ℕ} (hrp : r ≠ p) {K : Subgroup Y}
    (hperf : commutator ↥K = ⊤) (hchev : IsChevSimple r (↥K ⧸ Subgroup.center ↥K))
    (hexc : ¬ (r = 2 ∧ (p = 3 ∨ (p = 5 ∧ Claims1116.Exc5 (↥K ⧸ Subgroup.center ↥K))))) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) ≤ 1 ∨
      ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ (p = 3 → q ≠ 2) ∧ IsLieChar (· = q) ↥K ∧
        (p = 5 → ¬ Lemma1314.I2310Exc5 K) := by
  have hnoexc : p = 5 → ¬ Lemma1314.I2310Exc5 K := fun hp5 hx => by
    have h5 := exc5_of_i2310Exc5 hx
    by_cases hr2 : r = 2
    · exact hexc ⟨hr2, Or.inr ⟨hp5, h5⟩⟩
    · exact CrossCharOdd.input3_3_Exc5_holds _ h5 r hr2 hchev
  have hp1 : 2 ≤ p := hp.two_le
  rcases hchev with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | lie d =>
      have hdr : d.1.characteristic = r := hi
      refine Or.inr ⟨r, hdr ▸ TauCeti.LieTypeIndex.characteristic_prime d.1, hrp,
        fun h3 h2 => hexc ⟨h2, Or.inl h3⟩, ⟨d, ⟨e⟩, hdr⟩, hnoexc⟩
    | cyclic _ _ => exact hi.elim
    | alternating _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
  · cases i with
    | alternating n hn =>
      left
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩
      · refine pRank_aut_le_one hp hperf e (N := 120)
          (by
            show Nat.card (MulAut (alternatingGroup (Fin 5))) ∣ 120
            rw [card_mulAut_alt (by norm_num) (by norm_num)]
            decide) fun h => ?_
        have := le_of_sq_dvd (m := 2) hp (by norm_num) h
          (by simp only [Nat.primeFactorsList_ofNat]; decide)
        omega
      · have hp3 : p ≠ 3 := by
          rcases hr with rfl | rfl
          · exact fun h => hexc ⟨rfl, Or.inl h⟩
          · exact fun h => hrp h.symm
        refine pRank_aut_le_one hp hperf e InputsSeitz.card_mulAut_alt6_dvd fun h => ?_
        have := le_of_sq_dvd (m := 3) hp (by norm_num) h
          (by simp only [Nat.primeFactorsList_ofNat]; decide)
        omega
      · have hp3 : p ≠ 3 := fun h => hexc ⟨hr, Or.inl h⟩
        refine pRank_aut_le_one hp hperf e (N := 40320)
          (by
            show Nat.card (MulAut (alternatingGroup (Fin 8))) ∣ 40320
            rw [card_mulAut_alt (by norm_num) (by norm_num)]
            decide) fun h => ?_
        have := le_of_sq_dvd (m := 3) hp (by norm_num) h
          (by simp only [Nat.primeFactorsList_ofNat]; decide)
        omega
    | lie d =>
      obtain ⟨d1, hv⟩ := d
      cases d1 with
      | A k q' =>
        rcases k with _ | _ | k
        · simp [ambiguousChev] at hi
        · have hi' : (q'.card = 7 ∧ r = 2) ∨ (q'.card = 8 ∧ r = 3) := by
            simpa [ambiguousChev] using hi
          rcases hi' with ⟨h7, hr⟩ | ⟨h8, hr⟩
          · have hp3 : p ≠ 3 := fun h => hexc ⟨hr, Or.inl h⟩
            have hq7 : q'.p = 7 := p_eq_of_card_eq (k := 1) (by norm_num) (by rw [h7]; norm_num)
            by_cases hp7 : p = 7
            · left
              subst hp7
              exact pRank_aut_le_one hp hperf e
                (dvd_of_eq (card_mulAut_L27 (q' := q') (hv := hv) h7 (MulEquiv.refl _)))
                (by norm_num)
            · exact Or.inr ⟨q'.p, q'.prime_p, by rw [hq7]; exact Ne.symm hp7,
                fun h => absurd h hp3, ⟨_, ⟨e⟩, TauCeti.LieTypeIndex.characteristic_A _ _⟩, hnoexc⟩
          · have hp3 : p ≠ 3 := fun h => hrp (hr.trans h.symm)
            have hq2 : q'.p = 2 := p_eq_of_card_eq (k := 3) Nat.prime_two (by rw [h8]; norm_num)
            exact Or.inr ⟨q'.p, q'.prime_p, by rw [hq2]; omega, fun h => absurd h hp3,
              ⟨_, ⟨e⟩, TauCeti.LieTypeIndex.characteristic_A _ _⟩, hnoexc⟩
        · simp [ambiguousChev] at hi
      | twistedA k q' =>
        rcases k with _ | _ | _ | _ | k
        · simp [ambiguousChev] at hi
        · simp [ambiguousChev] at hi
        · have hi' : q'.card = 3 ∧ r = 2 := by simpa [ambiguousChev] using hi
          have hp3 : p ≠ 3 := fun h => hexc ⟨hi'.2, Or.inl h⟩
          have hq3 : q'.p = 3 :=
            p_eq_of_card_eq (k := 1) Nat.prime_three (by rw [hi'.1]; norm_num)
          exact Or.inr ⟨q'.p, q'.prime_p, by rw [hq3]; exact Ne.symm hp3, fun h => absurd h hp3,
            ⟨_, ⟨e⟩, TauCeti.LieTypeIndex.characteristic_twistedA _ _⟩, hnoexc⟩
        · have hi' : q'.card = 2 ∧ r = 3 := by simpa [ambiguousChev] using hi
          have hp3 : p ≠ 3 := fun h => hrp (hi'.2.trans h.symm)
          have hq2 : q'.p = 2 :=
            p_eq_of_card_eq (k := 1) Nat.prime_two (by rw [hi'.1]; norm_num)
          exact Or.inr ⟨q'.p, q'.prime_p, by rw [hq2]; omega, fun h => absurd h hp3,
            ⟨_, ⟨e⟩, TauCeti.LieTypeIndex.characteristic_twistedA _ _⟩, hnoexc⟩
        · simp [ambiguousChev] at hi
      | _ => simp [ambiguousChev] at hi
    | cyclic _ _ => exact hi.elim
    | sporadic _ => exact hi.elim

theorem claims1116_input23_10_of_faith (h5 : InputsSeitz.Input23_10Faith)
    (h3 : Input23_10FaithThree) : Claims1116.Input23_10 := by
  intro G _ _ p r hp hp2 hrp X J E hJ hEX hE hE3 hchev hexc
  haveI : Fact p.Prime := ⟨hp⟩
  have hK : IsComponentOf (barX p X J) ⊤ := hJ.2.2.1
  have hcore : GLAPPrimeCore p (↥X ⧸ GLAPPrimeCore p ↥X) = ⊥ := CFSG.pPrimeCore_quotient_eq_bot hp
  have ec := Claims1116.barX_centerQuotEquiv hp hJ
  have hchevK : IsChevSimple r (↥(barX p X J) ⧸ Subgroup.center ↥(barX p X J)) :=
    Claims1116.isChevSimple_congr ec hchev
  have hexcK : ¬ (r = 2 ∧ (p = 3 ∨ (p = 5 ∧
      Claims1116.Exc5 (↥(barX p X J) ⧸ Subgroup.center ↥(barX p X J))))) := by
    rintro ⟨h2, h3' | ⟨h5', hx⟩⟩
    · exact hexc ⟨h2, Or.inl h3'⟩
    · exact hexc ⟨h2, Or.inr ⟨h5', Claims1116.exc5_congr ec.symm hx⟩⟩
  set K := barX p X J with hKdef
  set A := barX p X E ⊓ Subgroup.normalizer (K : Set (↥X ⧸ GLAPPrimeCore p ↥X)) with hAdef
  have hAel : IsElemAbelian p A := elem_mono (isElemAbelian_barX hE) inf_le_left
  have hAN : A ≤ Subgroup.normalizer (K : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := inf_le_right
  have hA3 : Nat.card A ≤ p ^ 3 := by
    refine (Subgroup.card_le_of_le inf_le_left).trans ?_
    rw [Claims1116.card_barX_of_isPGroup hp (CFSG.Open.IsElemAbelian.isPGroup hE) hEX]
    exact hE3
  have key : Nat.card A ≤
        p * Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set (↥X ⧸ GLAPPrimeCore p ↥X))) ∨
      Lemma1314.IsGMinusOne p A K := by
    rcases rankOne_or_lieChar hp hp2 hrp hK.2.2.1 hchevK hexcK with
      h1 | ⟨q, hq, hqp, hq32, hlie, hq5⟩
    · left
      have hstab : stab A K = A := inf_eq_left.2 hAN
      have hst := card_stab_le hAel K
      rw [hstab] at hst
      calc Nat.card A ≤ p ^ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) * Nat.card (cen A K) := hst
        _ ≤ p ^ 1 * Nat.card (cen A K) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp.pos h1)
        _ = p * Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set (↥X ⧸ GLAPPrimeCore p ↥X))) := by
          rw [pow_one]; rfl
    · by_cases hsmall : Nat.card A ≤
          p * Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set (↥X ⧸ GLAPPrimeCore p ↥X)))
      · exact Or.inl hsmall
      · push Not at hsmall
        refine Or.inr (InputsSeitz.isGMinusOne_of_faithful_le hp hAel hAN hsmall
          fun B₁ hB₁ hB₁N hfaith hB₁card hB₁le => ?_)
        by_cases hp3 : p = 3
        · subst hp3
          exact h3 q hq (hq32 rfl) hqp _ hcore K B₁ hK hB₁ hB₁N hfaith hB₁card (hB₁le.trans hA3) hlie
        · have hp5 : 5 ≤ p := by
            have h2 := hp.two_le
            by_contra hlt
            have h4 : p = 4 := by omega
            subst h4
            exact absurd hp (by decide)
          exact h5 p q hp hp5 hq hqp _ hcore K B₁ hK hB₁ hB₁N hfaith hB₁card (hB₁le.trans hA3) hlie hq5
  rcases key with hsmall | hG
  · refine le_iSup₂_of_le (A ⊓ Subgroup.centralizer (K : Set (↥X ⧸ GLAPPrimeCore p ↥X)))
      ⟨inf_le_left, hsmall⟩ ?_
    intro x hx
    exact ⟨hx, Subgroup.mem_centralizer_iff.2 fun f hf =>
      (Subgroup.mem_centralizer_iff.1 hf.2 x hx).symm⟩
  · unfold Lemma1314.IsGMinusOne Lemma1314.IsGClass Lemma1314.GammaPrimeOf at hG
    rw [iSup_gLBConj_eq hAN] at hG
    refine hG.le.trans (iSup₂_le fun A' hA' => ?_)
    obtain ⟨hA'A, hr'⟩ := hA'
    have hA'el : IsElemAbelian p A' := elem_mono hAel hA'A
    have hcard : Nat.card A ≤ p * Nat.card A' := by
      rw [GL83.PiGen.card_eq_pow_pRank hAel, GL83.PiGen.card_eq_pow_pRank hA'el]
      calc p ^ CFSG.Open.pRank p A ≤ p ^ (CFSG.Open.pRank p A' + 1) :=
            Nat.pow_le_pow_right hp.pos (by omega)
        _ = p * p ^ CFSG.Open.pRank p A' := by ring
    exact le_iSup₂_of_le A' ⟨hA'A, hcard⟩ (le_of_eq (inf_comm _ _))

end Cert

end Seitz

section L33

@[expose] def pp3 : TauCeti.PrimePower := ⟨3, 1, Nat.prime_three, Nat.one_pos⟩

theorem valid_A_two_pp3 : (TauCeti.LieTypeIndex.A 2 pp3).Valid := by
  simp [pp3]

theorem isChevSimple_three_of_isLpType {T : Type} [Group T] (h : IsLpType 3 3 T) :
    IsChevSimple 3 T := by
  obtain ⟨F, hF, hFin, hc, ⟨f⟩⟩ := h
  haveI : Fact (3 : ℕ).Prime := ⟨Nat.prime_three⟩
  haveI : Fact pp3.p.Prime := ⟨pp3.prime_p⟩
  have hc' : Nat.card F = 3 ^ 1 := by rw [hc]; norm_num
  let eK := CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F 3 3 1 (by norm_num) hc'
  let eC := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 pp3 valid_A_two_pp3
  refine Or.inl ⟨.lie ⟨.A 2 pp3, valid_A_two_pp3⟩, ?_, ⟨(f.trans eK).trans eC.symm⟩⟩
  show (TauCeti.LieTypeIndex.A 2 pp3).characteristic = 3
  rw [TauCeti.LieTypeIndex.characteristic_A]
  rfl

@[expose] def InputL33DownThree : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 13 Y = ⊥ →
    IsChevSimple 3 (Y ⧸ Subgroup.center Y) →
    ∀ β : MulAut Y, β ^ 13 = 1 → β ≠ 1 → ∀ I : Subgroup Y, GLAPComponent 13 (fixSubgroup β) I →
      IsLpType 3 3 (PSimple 13 I) → IsLpType 3 (3 ^ 13) Y ∨ Prop1116Design.IsLieOverField 3 Y

section Cert


theorem inputL33Down_of_three (h : InputL33DownThree) : Claims1116b.InputL33Down := by
  intro Y _ _ hq hO q hq' hq2 hq13 hchev β hβ hβ1 I hI hL33
  have hβo : orderOf β = 13 := orderOf_eq_prime hβ hβ1
  have hKhat : CFSG.LocalAnalysis.GLTheoremA.IsKHat Y := by
    refine ⟨hq, ?_⟩
    rcases hchev with ⟨i, -, ⟨e⟩⟩ | ⟨i, -, ⟨e⟩⟩
    · exact ⟨i, ⟨e⟩⟩
    · exact ⟨i, ⟨e⟩⟩
  have hpump : Lemma1314.PumpupVia 13 (barOf 13 I) Y β :=
    ⟨hβo, I, by rw [PumpDefChar.fixSub_eq_fixSubgroup]; exact hI, ⟨MulEquiv.refl _⟩⟩
  have hdown := (Inputs1315.input14_4_1_holds 13 q (by norm_num) (by norm_num) hq' Y hKhat hO hchev
    (barOf 13 I) β hpump).1
  have h3 : IsChevSimple 3 (PSimple 13 I) := isChevSimple_three_of_isLpType hL33
  have hq3 : q = 3 := by
    by_contra hne
    rcases CrossCharOdd.input3_3_OddChar_holds (PSimple 13 I) q 3 hdown h3 hne with h2 | h2
    · exact hq2 h2
    · norm_num at h2
  subst hq3
  exact h Y hq hO hchev β hβ hβ1 I hI hL33

end Cert

end L33

section Spor

theorem sporOrd_eq_sporOrder (s : TauCeti.SporadicName) :
    CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s =
      CFSG.ComponentClassification.GSThmB.QPUSpor.sporOrder s := by
  cases s <;> rfl

theorem sporOrd_bounds (s : TauCeti.SporadicName) :
    7920 ≤ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s ∧
      CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s ≠ 504 ∧
      CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s ≠ 25920 := by
  cases s <;> decide

theorem card_alt (n : ℕ) (hn : 2 ≤ n) : Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]

@[expose] def SporDownCase (s : TauCeti.SporadicName) (p : ℕ) (T : Type) [Group T] : Prop :=
  (p = 3 ∧ (s = .M23 ∨ s = .HS) ∧ IsLpType 2 5 T) ∨
    (p = 3 ∧ (s = .M24 ∨ s = .He) ∧ IsLpType 2 7 T) ∨
    (p = 5 ∧ s = .Suz ∧ IsLpType 2 9 T) ∨ (p = 13 ∧ s = .M ∧ IsLpType 3 3 T)

@[expose] def SporDownRow (s : TauCeti.SporadicName) (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ∀ x : S, orderOf x = p → ∀ I : Subgroup S,
      GLAPComponent p (Subgroup.centralizer ({x} : Set S)) I →
      ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → IsChevSimple q (PSimple p I) →
        SporDownCase s p (PSimple p I)


@[expose] def SporDownResidual : Prop :=
  SporDownRow .M24 3 ∧ SporDownRow .J2 3 ∧ SporDownRow .Ru 3 ∧ SporDownRow .Co1 3 ∧
    SporDownRow .B 3 ∧ SporDownRow .M 3 ∧ SporDownRow .Fi23 5 ∧ SporDownRow .Fi24Prime 5 ∧
    SporDownRow .B 5 ∧ SporDownRow .M 5 ∧ SporDownRow .Co1 7 ∧ SporDownRow .Fi24Prime 7 ∧
    SporDownRow .B 7 ∧ SporDownRow .M 11 ∧ SporDownRow .M 13

end Spor

section Rows

@[expose] def DownTypeOK (s : TauCeti.SporadicName) (p : ℕ) (T : Type) [Group T] : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → IsChevSimple q T → SporDownCase s p T

theorem sporDownCase_of_mulEquiv {s : TauCeti.SporadicName} {p : ℕ} {T T' : Type} [Group T]
    [Group T'] (e : T ≃* T') (h : SporDownCase s p T) : SporDownCase s p T' := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨h1, h2, Claims1116b.isLpType_congr e.symm h3⟩
  · exact Or.inr (Or.inl ⟨h1, h2, Claims1116b.isLpType_congr e.symm h3⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, Claims1116b.isLpType_congr e.symm h3⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, Claims1116b.isLpType_congr e.symm h3⟩))

theorem downTypeOK_of_mulEquiv {s : TauCeti.SporadicName} {p : ℕ} {T T' : Type} [Group T]
    [Group T'] (e : T ≃* T') (h : DownTypeOK s p T) : DownTypeOK s p T' := fun q hq hq2 hqp hc =>
  sporDownCase_of_mulEquiv e (h q hq hq2 hqp (Claims1116.isChevSimple_congr e.symm hc))

theorem downTypeOK_of_not_chev {s : TauCeti.SporadicName} {p : ℕ} {T : Type} [Group T]
    (h : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → ¬ IsChevSimple q T) : DownTypeOK s p T :=
  fun q hq hq2 hqp hc => (h q hq hq2 hqp hc).elim

@[expose] def DownCompOK (s : TauCeti.SporadicName) (p : ℕ) {Q : Type} [Group Q] (k : Q) : Prop :=
  ∀ I : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) I →
    DownTypeOK s p (PSimple p I)

theorem downCompOK_of_mulEquiv {s : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime) {Q Q' : Type}
    [Group Q] [Group Q'] [Finite Q'] (σ : Q ≃* Q') {k : Q} (h : DownCompOK s p k) :
    DownCompOK s p (σ k) := by
  intro I hI
  have hI' := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv hp σ.symm hI
  rw [CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_mulEquiv,
    MulEquiv.symm_apply_apply] at hI'
  exact downTypeOK_of_mulEquiv (CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv p
    (I.equivMapOfInjective σ.symm.toMonoidHom σ.symm.injective)).symm (h _ hI')

theorem downCompOK_of_no_comp {s : TauCeti.SporadicName} {p : ℕ} {Q : Type} [Group Q] {k : Q}
    (h : ∀ I : Subgroup Q, ¬ GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) I) :
    DownCompOK s p k := fun I hI => (h I hI).elim

theorem downCompOK_of_centShape {s : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime) {Q : Type}
    [Group Q] [Finite Q] {Good : ∀ (T : Type) [Group T], Prop}
    (h : CFSG.HardMathSupport.Dickson.I271.CentShape p Good Q)
    (hG : ∀ (T : Type) [Group T], Good T → DownTypeOK s p T) {k : Q} (hk : orderOf k = p) :
    DownCompOK s p k := by
  have hk1 : k ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hk; exact hp.one_lt.ne' hk.symm
  intro I hI
  rcases h k hk1 (by rw [← hk]; exact pow_orderOf_eq_one k) with hc | ⟨J, -, huniq, hg⟩
  · exact (CFSG.HardMathSupport.Dickson.I271.no_glaPComponent_of_pConstrainedShape hp hc hI).elim
  · rw [huniq I hI]
    exact hG _ hg

theorem sporDownRow_of_model {s : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q]
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (h : Finite Q → ∀ k : Q, orderOf k = p → DownCompOK s p k) : SporDownRow s p := by
  intro S _ _ _ ⟨e⟩ x hx I hI
  let φ : S ≃* Q := e.trans b.symm
  haveI : Finite Q := Finite.of_equiv S φ.toEquiv
  have hk : orderOf (φ x) = p := by rw [MulEquiv.orderOf_eq, hx]
  have := downCompOK_of_mulEquiv hp φ.symm (h inferInstance _ hk)
  rw [MulEquiv.symm_apply_apply] at this
  exact this I hI

theorem sporDownRow_of_model' {s : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q]
    [Finite Q] (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (h : ∀ k : Q, orderOf k = p → DownCompOK s p k) : SporDownRow s p :=
  sporDownRow_of_model hp b fun _ k hk => h k hk

theorem sporDownRow_of_centShape {s : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime) {Q : Type}
    [Group Q] (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) {Good : ∀ (T : Type) [Group T], Prop}
    (h : CFSG.HardMathSupport.Dickson.I271.CentShape p Good Q)
    (hG : ∀ (T : Type) [Group T], Good T → DownTypeOK s p T) : SporDownRow s p :=
  sporDownRow_of_model hp b fun hfin _ hk => by
    haveI := hfin
    exact downCompOK_of_centShape hp h hG hk

theorem isChevSimple_five_of_A5 {T : Type} [Group T] (e : T ≃* ↥(alternatingGroup (Fin 5))) :
    IsChevSimple 5 T := by
  have h5 : 5 ≤ 5 := le_rfl
  exact Or.inr ⟨TauCeti.CFSGIndex.alternating 5 h5, Or.inl ⟨rfl, Or.inr rfl⟩, ⟨e⟩⟩

theorem isChevSimple_three_of_A6 {T : Type} [Group T] (e : T ≃* ↥(alternatingGroup (Fin 6))) :
    IsChevSimple 3 T := by
  have h6 : 5 ≤ 6 := by norm_num
  exact Or.inr ⟨TauCeti.CFSGIndex.alternating 6 h6, Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩), ⟨e⟩⟩

theorem sporDownRow_of_noComp {s : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime) {H : Type}
    [Group H] (b : H ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hno : ∀ x : H, orderOf x = p → ∀ I : Subgroup H,
      GLAPComponent p (Subgroup.centralizer ({x} : Set H)) I → False) : SporDownRow s p :=
  sporDownRow_of_model hp b fun _ x hx => downCompOK_of_no_comp fun I hI => hno x hx I hI

theorem sporDownRow_three_of_perm {s : TauCeti.SporadicName} {n : ℕ}
    {P : Subgroup (Equiv.Perm (Fin n))} (b : ↥P ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hsmall : ∀ x ∈ P, orderOf x = 3 →
      Nat.card ↥(Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ P) < 60) :
    SporDownRow s 3 := by
  refine sporDownRow_of_noComp Nat.prime_three b fun x hx I hI => ?_
  refine CFSG.LocalAnalysis.GLTheoremA.KDSpor.false_of_glaPComponent_of_solvable Nat.prime_three
    (CFSG.GroupTheory.groups_order_below_sixty_solvable ?_) hI
  have hmapc := CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype P x
  rw [← Subgroup.card_map_of_injective P.subtype_injective, hmapc]
  exact hsmall _ x.2 (by rw [Subgroup.orderOf_coe]; exact hx)

section Cert


theorem downTypeOK_of_chevP {s : TauCeti.SporadicName} {p : ℕ} (hp2 : p ≠ 2) {T : Type} [Group T]
    (h : IsChevSimple p T) : DownTypeOK s p T :=
  downTypeOK_of_not_chev fun q _ hq2 hqp hc => by
    rcases CrossCharOdd.input3_3_OddChar_holds T q p hc h hqp with h' | h'
    · exact hq2 h'
    · exact hp2 h'

theorem downTypeOK_of_leafType {s : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {T : Type} [Group T] (h : CFSG.HardMathSupport.Dickson.I271.LeafType p T) :
    DownTypeOK s p T := by
  rcases h with ⟨hc, -, -⟩ | ⟨n, hn, hn6, hpn, ⟨f⟩⟩
  · exact downTypeOK_of_chevP hp2 hc
  · refine downTypeOK_of_not_chev fun q _ hq2 hqp hc => ?_
    rcases Prop1116Design.alt_chev_cases AltFacts4.inputAltNotLie_holds hq2 hn ⟨f⟩ hc with
      ⟨rfl, rfl⟩ | ⟨rfl, -⟩
    · exact hqp ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hpn).symm
    · exact hn6 rfl

theorem downCompOK_of_centShapeSplit {s : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : Type} [Group Q] [Finite Q] (h : CFSG.HardMathSupport.Dickson.I271.CentShapeSplit p Q)
    {k : Q} (hk : orderOf k = p) : DownCompOK s p k := by
  have hk1 : k ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hk; exact hp.one_lt.ne' hk.symm
  intro I hI
  rcases h k hk1 (by rw [← hk]; exact pow_orderOf_eq_one k) with hc | ⟨J, -, huniq, hg⟩
  · exact (CFSG.HardMathSupport.Dickson.I271.no_glaPComponent_of_pConstrainedShape hp hc hI).elim
  · rw [huniq I hI]
    rcases hg with hl | ⟨⟨h3, ⟨f⟩⟩, -⟩
    · exact downTypeOK_of_leafType hp hp2 hl
    · subst h3
      exact downTypeOK_of_chevP (by norm_num) (isChevSimple_three_of_A6 f)

theorem downCompOK_of_centShapeRk' {s : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime) {Q : Type}
    [Group Q] [Finite Q] {Good Rk : ∀ (T : Type) [Group T], Prop}
    (h : CFSG.HardMathSupport.Dickson.I271.CentShapeRk' p Good Rk Q)
    (hG : ∀ (T : Type) [Group T], Good T → DownTypeOK s p T) {k : Q} (hk : orderOf k = p) :
    DownCompOK s p k := by
  have hk1 : k ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hk; exact hp.one_lt.ne' hk.symm
  intro I hI
  rcases h k hk1 (by rw [← hk]; exact pow_orderOf_eq_one k) with hno | ⟨J, -, huniq, hg, -⟩
  · exact (hno I hI).elim
  · rw [huniq I hI]
    exact hG _ hg

theorem downCompOK_of_centShapeMulti {s : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime) {Q : Type}
    [Group Q] [Finite Q] {Good Rk : ∀ (T : Type) [Group T], Prop}
    (h : CFSG.HardMathSupport.Dickson.I271.CentShapeMulti p Good Rk Q)
    (hG : ∀ (T : Type) [Group T], Good T → DownTypeOK s p T) {k : Q} (hk : orderOf k = p) :
    DownCompOK s p k := by
  have hk1 : k ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hk; exact hp.one_lt.ne' hk.symm
  intro I hI
  rcases h.1 k hk1 (by rw [← hk]; exact pow_orderOf_eq_one k) with hc | ⟨L, -, -, hall⟩
  · exact (CFSG.HardMathSupport.Dickson.I271.no_glaPComponent_of_pConstrainedShape hp hc hI).elim
  · exact hG _ (hall I hI).1

theorem downTypeOK_of_goodSpor_nil {s : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {T : Type} [Group T] (h : CFSG.HardMathSupport.Dickson.I271.GoodSpor p [] T) :
    DownTypeOK s p T := by
  rcases h with hl | ⟨h3, ⟨f⟩⟩ | ⟨S, hS, -⟩
  · exact downTypeOK_of_leafType hp hp2 hl
  · subst h3
    exact downTypeOK_of_chevP (by norm_num) (isChevSimple_three_of_A6 f)
  · exact absurd hS (List.not_mem_nil)

theorem not_isChevSimple_of_card_bound {p : ℕ} {T : Type} [Group T] [Finite T] {N : ℕ}
    (hT : Nat.card T = N) (hN0 : 0 < N) (hNlt : N < 2 ^ 200)
    (hN : ∀ q ∈ N.primeFactorsList, q ≠ 2 → q ≠ p → ∀ k < 200, q ^ k ∣ N → q ^ (3 * k) ≤ N)
    (h3 : p ≠ 3 → N ≠ 360 ∧ N ≠ 504 ∧ N ≠ 25920) (h5 : p ≠ 5 → N ≠ 60) :
    ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → ¬ IsChevSimple q T := by
  intro q hq hq2 hqp
  have h3' : q = 3 → q ^ (N.factorization q) * (N / q ^ (N.factorization q)) ≠ 360 ∧
      q ^ (N.factorization q) * (N / q ^ (N.factorization q)) ≠ 504 ∧
      q ^ (N.factorization q) * (N / q ^ (N.factorization q)) ≠ 25920 := by
    rintro rfl
    rw [Nat.ordProj_mul_ordCompl_eq_self]
    exact h3 (fun h => hqp h.symm)
  have h5' : q = 5 → q ^ (N.factorization q) * (N / q ^ (N.factorization q)) ≠ 60 := by
    rintro rfl
    rw [Nat.ordProj_mul_ordCompl_eq_self]
    exact h5 (fun h => hqp h.symm)
  refine CFSG.LocalAnalysis.GLTheoremA.I1416QRows.not_isChevSimple_of_card
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds hq hq2
    (hT.trans (Nat.ordProj_mul_ordCompl_eq_self N q).symm) (Nat.not_dvd_ordCompl hq hN0.ne') ?_
    h3' h5'
  set a := N.factorization q
  have hqa : q ^ a ∣ N := Nat.ordProj_dvd N q
  have hpos : 0 < q ^ a := pow_pos hq.pos a
  have hm : q ^ a * (N / q ^ a) = N := Nat.ordProj_mul_ordCompl_eq_self N q
  by_cases hqN : q ∣ N
  · have hmem : q ∈ N.primeFactorsList := (Nat.mem_primeFactorsList hN0.ne').2 ⟨hq, hqN⟩
    have ha : a < 200 := by
      by_contra hge
      push Not at hge
      have h1 : 2 ^ 200 ≤ q ^ a :=
        (Nat.pow_le_pow_left hq.two_le 200).trans (Nat.pow_le_pow_right hq.pos hge)
      have h2 : q ^ a ≤ N := Nat.le_of_dvd hN0 hqa
      omega
    have hk := hN q hmem hq2 hqp a ha hqa
    have : q ^ a * q ^ (2 * a) ≤ q ^ a * (N / q ^ a) := by
      rw [hm, ← pow_add]
      calc q ^ (a + 2 * a) = q ^ (3 * a) := by ring_nf
        _ ≤ N := hk
    exact Nat.le_of_mul_le_mul_left this hpos
  · have ha : a = 0 := Nat.factorization_eq_zero_of_not_dvd hqN
    simp only [ha, mul_zero, pow_zero, Nat.div_one]
    exact hN0

theorem downTypeOK_suz_five_of_card_360 {T : Type} [Group T] [Finite T] (hc : Nat.card T = 360) :
    DownTypeOK .Suz 5 T := by
  intro q _ _ _ hC
  rcases hC with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | lie d =>
      exact (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieOrderFormula_ne_360 d.2
        ((CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds d T ⟨e⟩).symm.trans
          hc)).elim
    | _ => exact hi.elim
  · cases i with
    | lie d =>
      exact (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieOrderFormula_ne_360 d.2
        ((CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds d T ⟨e⟩).symm.trans
          hc)).elim
    | alternating n hn5 =>
      have hcn : Nat.card T = n.factorial / 2 :=
        (Nat.card_congr e.toEquiv).trans (card_alt n (by omega))
      have hn6 : n = 6 := by
        rw [hc] at hcn
        rcases Nat.lt_or_ge n 7 with h | h
        · interval_cases n <;> simp_all [Nat.factorial]
        · have h7 : Nat.factorial 7 ∣ n.factorial := Nat.factorial_dvd_factorial h
          have : 2520 ≤ n.factorial / 2 := by
            have := Nat.le_of_dvd (Nat.factorial_pos n) h7
            simp [Nat.factorial] at this
            omega
          omega
      subst hn6
      refine Or.inr (Or.inr (Or.inl ⟨rfl, rfl, ?_⟩))
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hK : Nat.card (GaloisField 3 2) = 9 := by
        rw [GaloisField.card 3 2 (by norm_num)]
        norm_num
      obtain ⟨f⟩ :=
        CFSG.Open.StatedAPI.nonempty_mulEquiv_alternating_six_of_statedProj hK (MulEquiv.refl _)
      exact ⟨GaloisField 3 2, inferInstance, inferInstance, hK, ⟨e.trans f.symm⟩⟩
    | _ => exact hi.elim

end Cert

theorem card_zmod_five : Nat.card (ZMod 5) = 5 := by
  rw [Nat.card_eq_fintype_card, ZMod.card]

theorem isLpType_two_five_of_A5 {T : Type} [Group T]
    (e : T ≃* ↥(alternatingGroup (Fin 5))) :
    IsLpType 2 5 T := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨g⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five (ZMod 5)
    (Or.inr card_zmod_five)
  exact ⟨ZMod 5, inferInstance, inferInstance, card_zmod_five, ⟨e.trans g.symm⟩⟩

theorem downCompOK_three_of_card_dvd_360 {s : TauCeti.SporadicName}
    (hs : s = .M23 ∨ s = .HS)
    {Q : Type} [Group Q] [Finite Q] {k : Q} (hk3 : orderOf k = 3)
    (hk : Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ 360) : DownCompOK s 3 k := by
  intro I hI
  obtain ⟨hs', hnab⟩ := CFSG.LocalAnalysis.GLTheoremA.KDSpor.pSimple_simple_nonab Nat.prime_three hI
  haveI := hs'
  have h3 : 3 * Nat.card (PSimple 3 I) ∣ 360 :=
    (CFSG.LocalAnalysis.GLTheoremA.I1416Rows.three_mul_card_pSimple_dvd_cent hk3 hI.1).trans hk
  have hd : Nat.card (PSimple 3 I) ∣ 3000 :=
    (Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3)
      (h3.trans (by norm_num : 360 ∣ 3 * 120))).trans (by norm_num)
  obtain ⟨fA⟩ := CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    (CFSG.LocalAnalysis.GLTheoremA.KDSpor.card_eq_sixty_of_dvd_3000 hnab hd)
  exact fun _ _ _ _ _ => Or.inl ⟨rfl, hs, isLpType_two_five_of_A5 fA⟩

section Records

variable {n p : ℕ} {P R : Subgroup (Equiv.Perm (Fin n))}

theorem downCompOK_of_centralizer_eq {s : TauCeti.SporadicName} {Q : Type} [Group Q] {k k' : Q}
    (hc : Subgroup.centralizer ({k} : Set Q) = Subgroup.centralizer ({k'} : Set Q))
    (h : DownCompOK s p k) : DownCompOK s p k' := by
  intro I hI
  rw [← hc] at hI
  exact h I hI

theorem downCompOK_of_lines {s : TauCeti.SporadicName} (hp : p.Prime)
    {Q : Subgroup (Equiv.Perm (Fin n))}
    (hQP : Q ≤ P) (hQ : Nat.card Q = p ^ (Nat.card P).factorization p) {ι : Type*}
    (line : ι → Equiv.Perm (Fin n))
    (hlines : ∀ H : Subgroup (Equiv.Perm (Fin n)), H ≤ Q → Nat.card H = p →
      ∃ j, H = Subgroup.zpowers (line j))
    (hmem : ∀ j, line j ∈ P) (hline : ∀ j, DownCompOK s p (⟨line j, hmem j⟩ : ↥P)) :
    ∀ k : ↥P, orderOf k = p → DownCompOK s p k := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro k hk
  have hko : orderOf (k : Equiv.Perm (Fin n)) = p := by rw [Subgroup.orderOf_coe]; exact hk
  obtain ⟨g, hgP, hgQ⟩ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T.exists_conj_mem_of_full hQP hQ k.2 hko
  set t := g⁻¹ * (k : Equiv.Perm (Fin n)) * g with htdef
  have hto : orderOf t = p := by
    have := (MulAut.conj g⁻¹ : Equiv.Perm (Fin n) ≃* Equiv.Perm (Fin n)).orderOf_eq k
    simpa [MulAut.conj_apply, htdef, hko] using this
  obtain ⟨j, hj⟩ := hlines (Subgroup.zpowers t) ((Subgroup.zpowers_le).2 hgQ)
    (by rw [Nat.card_zpowers, hto])
  have htP : t ∈ P := P.mul_mem (P.mul_mem (P.inv_mem hgP) k.2) hgP
  have ht : DownCompOK s p (⟨t, htP⟩ : ↥P) :=
    downCompOK_of_centralizer_eq
      (CFSG.HardMathSupport.Solomon.Coordinator.centralizer_singleton_eq_of_zpowers
        (CFSG.LocalAnalysis.GLTheoremA.KDSpor.zpowers_subtype_eq hj)).symm (hline j)
  have hk' : MulAut.conj (⟨g, hgP⟩ : ↥P) (⟨t, htP⟩ : ↥P) = k := by
    apply Subtype.ext
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, htdef]
    group
  rw [← hk']
  exact downCompOK_of_mulEquiv hp _ ht

theorem downCompOK_of_pgroup_record {s : TauCeti.SporadicName} (hp : p.Prime) (hPR : P ≤ R)
    {x : Equiv.Perm (Fin n)} (hxP : x ∈ P) {C A : Subgroup (Equiv.Perm (Fin n))}
    (hC : C = Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ R) (hAC : A ≤ C)
    (hAn : (A.subgroupOf C).Normal) (hAP : A ≤ P) (hAp : IsPGroup p ↥A)
    (hAc : Subgroup.centralizer (A : Set (Equiv.Perm (Fin n))) ⊓ C ≤ A) :
    DownCompOK s p (⟨x, hxP⟩ : ↥P) := by
  refine downCompOK_of_no_comp fun I hI =>
    CFSG.HardMathSupport.Dickson.I271.no_glaPComponent_of_pConstrainedShape hp ?_ hI
  refine CFSG.HardMathSupport.Dickson.I271.pConstrainedShape_of_map_injective P.subtype
    P.subtype_injective ?_
  rw [CFSG.HardMathSupport.Dickson.I271.map_centralizer_subtype']
  have hCP : Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ P ≤ C := by
    rw [hC]
    exact inf_le_inf_left _ hPR
  refine CFSG.HardMathSupport.Dickson.I271.pConstrainedShape_of_normal_pgroup
    (fun a ha => ⟨(hC ▸ hAC ha : a ∈ _ ⊓ R).1, hAP ha⟩) ⟨fun a ha g => ?_⟩ hAp
    ((inf_le_inf_left _ hCP).trans hAc)
  rw [Subgroup.mem_subgroupOf] at ha ⊢
  have := hAn.conj_mem ⟨a, hAC ha⟩ (Subgroup.mem_subgroupOf.2 ha) ⟨g, hCP g.2⟩
  exact Subgroup.mem_subgroupOf.1 this

theorem pSimple_equiv_of_normal_record (hp : p.Prime) (hPR : P ≤ R) {x : Equiv.Perm (Fin n)}
    (hxP : x ∈ P) {C D : Subgroup (Equiv.Perm (Fin n))}
    (hC : C = Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ R) (hDC : D ≤ C)
    (hDn : (D.subgroupOf C).Normal)
    (hDs : IsSimpleGroup ↥D) (hDnab : ∃ g ∈ D, ∃ h ∈ D, g * h ≠ h * g) (hDP : D ≤ P)
    (hDcent : Subgroup.centralizer (D : Set (Equiv.Perm (Fin n))) ⊓ C = Subgroup.zpowers x)
    (hxo : orderOf x = p)
    (hcore : GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ P) = ⊥)
    (hpD : p ∣ Nat.card ↥D) (I : Subgroup ↥P)
    (hI : GLAPComponent p (Subgroup.centralizer ({(⟨x, hxP⟩ : ↥P)} : Set ↥P)) I) :
    Nonempty (PSimple p I ≃* ↥D) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set k : ↥P := ⟨x, hxP⟩ with hk
  set Cq : Subgroup ↥P := Subgroup.centralizer ({k} : Set ↥P) with hCq
  set L : Subgroup ↥P := D.subgroupOf P with hL
  let eL : ↥L ≃* ↥D := Subgroup.subgroupOfEquivOfLe hDP
  haveI hLs : IsSimpleGroup ↥L := (MulEquiv.isSimpleGroup_congr eL).2 hDs
  have hLnab : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨g, hg, h, hh, hgh⟩ := hDnab
    refine ⟨eL.symm ⟨g, hg⟩, eL.symm ⟨h, hh⟩, fun he => hgh ?_⟩
    have := congrArg (fun z => ((eL z : ↥D) : Equiv.Perm (Fin n))) he
    simpa using this
  have hLq : CFSG.Open.IsQuasisimple ↥L :=
    CFSG.HardMathSupport.Dickson.I271.isQuasisimpleOpen_of_simple_nonab hLnab
  have hxcent : x ∈ Subgroup.centralizer (D : Set (Equiv.Perm (Fin n))) := by
    have : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
    rw [← hDcent] at this
    exact this.1
  have hgC : ∀ g : ↥P, g ∈ Cq → (g : Equiv.Perm (Fin n)) ∈ C := by
    intro g hg
    rw [hC]
    refine Subgroup.mem_inf.2 ⟨?_, hPR g.2⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    exact congrArg Subtype.val hg
  have hLC : L ≤ Cq := by
    intro l hl
    rw [hCq, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 hxcent _ (Subgroup.mem_subgroupOf.1 hl))
  have hLn : ∀ g ∈ Cq, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    intro g hg l hl
    rw [hL, Subgroup.mem_subgroupOf] at hl ⊢
    have h2 := hDn.conj_mem ⟨(l : Equiv.Perm (Fin n)), hDC hl⟩ (Subgroup.mem_subgroupOf.2 hl)
      ⟨(g : Equiv.Perm (Fin n)), hgC g hg⟩
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  have hcoreQ : GLAPPrimeCore p ↥Cq = ⊥ := by
    let e1 : ↥Cq ≃* ↥(Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ P) :=
      (Cq.equivMapOfInjective P.subtype P.subtype_injective).trans
        (MulEquiv.subgroupCongr (CFSG.HardMathSupport.Dickson.I271.map_centralizer_subtype' P k))
    have h0 := (CFSG.HardMathSupport.Dickson.I271.glaPPrimeCoreOf_eq_bot_iff_glaPPrimeCore p _).1
      hcore
    rw [← glaPPrimeCore_map_iso p e1.symm, h0, Subgroup.map_bot]
  have hcent : IsPGroup p ↥(Cq ⊓ Subgroup.centralizer (L : Set ↥P)) := by
    intro c
    refine ⟨1, ?_⟩
    have hcD : ((c : ↥P) : Equiv.Perm (Fin n)) ∈
        Subgroup.centralizer (D : Set (Equiv.Perm (Fin n))) ⊓ C := by
      refine ⟨Subgroup.mem_centralizer_iff.2 fun d hd => ?_, hgC _ c.2.1⟩
      have h := Subgroup.mem_centralizer_iff.1 c.2.2 ⟨d, hDP hd⟩ (Subgroup.mem_subgroupOf.2 hd)
      exact congrArg Subtype.val h
    rw [hDcent] at hcD
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hcD
    apply Subtype.ext; apply Subtype.ext
    simp only [Subgroup.coe_pow, pow_one, Subgroup.coe_one]
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hxo,
      pow_orderOf_eq_one, one_zpow]
  have hcoreL : GLAPPrimeCore p ↥L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore p ↥L) with h | h
    · exact h
    · exfalso
      have hcop := GL83.PiGen.coprime_card_glaPPrimeCore hp ↥L
      rw [h, Subgroup.card_top, Nat.card_congr eL.toEquiv] at hcop
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop hpD
  have hZL : Subgroup.center ↥L = ⊥ :=
    CFSG.HardMathSupport.Dickson.I271.center_eq_bot_of_simple_nonab hLnab
  have hIL : I = L :=
    CFSG.HardMathSupport.Dickson.I271.eq_of_glaPComponent_of_normal_quasisimple hp hLC hLn hLq
      hcoreQ hcent hI
  subst hIL
  exact ⟨(CFSG.HardMathSupport.Dickson.I271.pSimpleEquivSelf _ hcoreL hZL).trans eL⟩

theorem downCompOK_of_normal_record {s : TauCeti.SporadicName} (hp : p.Prime) (hPR : P ≤ R)
    {x : Equiv.Perm (Fin n)} (hxP : x ∈ P) {C D : Subgroup (Equiv.Perm (Fin n))}
    (hC : C = Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ R) (hDC : D ≤ C)
    (hDn : (D.subgroupOf C).Normal)
    (hDs : IsSimpleGroup ↥D) (hDnab : ∃ g ∈ D, ∃ h ∈ D, g * h ≠ h * g) (hDP : D ≤ P)
    (hDcent : Subgroup.centralizer (D : Set (Equiv.Perm (Fin n))) ⊓ C = Subgroup.zpowers x)
    (hxo : orderOf x = p)
    (hcore : GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ P) = ⊥)
    (hpD : p ∣ Nat.card ↥D) (hT : DownTypeOK s p ↥D) : DownCompOK s p (⟨x, hxP⟩ : ↥P) :=
  fun I hI => by
    obtain ⟨e⟩ := pSimple_equiv_of_normal_record hp hPR hxP hC hDC hDn hDs hDnab hDP hDcent hxo
      hcore hpD I hI
    exact downTypeOK_of_mulEquiv e.symm hT

theorem downCompOK_of_derived_record {s : TauCeti.SporadicName} (hp : p.Prime) (hPR : P ≤ R)
    {x : Equiv.Perm (Fin n)} (hxP : x ∈ P) {C D : Subgroup (Equiv.Perm (Fin n))}
    (hC : C = Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ R) (hD : D = ⁅C, C⁆)
    (hDs : IsSimpleGroup ↥D) (hDnab : ∃ g ∈ D, ∃ h ∈ D, g * h ≠ h * g) (hDP : D ≤ P)
    (hDcent : Subgroup.centralizer (D : Set (Equiv.Perm (Fin n))) ⊓ C = Subgroup.zpowers x)
    (hxo : orderOf x = p)
    (hcore : GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ P) = ⊥)
    (hpD : p ∣ Nat.card ↥D) (hT : DownTypeOK s p ↥D) : DownCompOK s p (⟨x, hxP⟩ : ↥P) := by
  have hDC : D ≤ C := by
    rw [hD, Subgroup.commutator_le]
    intro a ha c hc
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem ha hc) (C.inv_mem ha)) (C.inv_mem hc)
  have hDn : (D.subgroupOf C).Normal := by
    refine ⟨fun l hl g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hl ⊢
    have h2 : ⁅(g : Equiv.Perm (Fin n)), (l : Equiv.Perm (Fin n))⁆ ∈ D := by
      rw [hD]
      exact Subgroup.commutator_mem_commutator g.2 (hDC hl)
    have h3 : ((g * l * g⁻¹ : ↥C) : Equiv.Perm (Fin n)) =
        ⁅(g : Equiv.Perm (Fin n)), (l : Equiv.Perm (Fin n))⁆ * l := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]; group
    rw [h3]
    exact D.mul_mem h2 hl
  exact downCompOK_of_normal_record hp hPR hxP hC hDC hDn hDs hDnab hDP hDcent hxo hcore hpD hT

theorem downCompOK_conj {s : TauCeti.SporadicName} (hp : p.Prime)
    (hR : ∀ r ∈ R, ∀ q ∈ P, r * q * r⁻¹ ∈ P) {r y : Equiv.Perm (Fin n)} (hr : r ∈ R) (hyP : y ∈ P)
    (h : DownCompOK s p (⟨y, hyP⟩ : ↥P)) : DownCompOK s p (⟨r * y * r⁻¹, hR r hr y hyP⟩ : ↥P) :=
  downCompOK_of_mulEquiv hp (CFSG.LocalAnalysis.GLTheoremA.KDSpor.conjP hR hr) h

theorem downCompOK_of_shapeRkAt {s : TauCeti.SporadicName} (hp : p.Prime) {Q : Type} [Group Q]
    [Finite Q] {Good Rk : ∀ (T : Type) [Group T], Prop} {k : Q}
    (h : CFSG.HardMathSupport.Dickson.I271.ShapeRkAt p Good Rk k)
    (hG : ∀ (T : Type) [Group T], Good T → DownTypeOK s p T) : DownCompOK s p k := by
  intro I hI
  rcases h with hc | ⟨J, -, huniq, hg, -⟩
  · exact (CFSG.HardMathSupport.Dickson.I271.no_glaPComponent_of_pConstrainedShape hp hc hI).elim
  · rw [huniq I hI]
    exact hG _ hg

end Records

section Main



theorem not_isChevSimple_of_isSporType
    {X : Type} [Group X] {s : TauCeti.SporadicName}
    (hs : IsSporType s X) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : ¬ IsChevSimple q X := by
  obtain ⟨es⟩ := hs
  have hcard : Nat.card X = CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s :=
    (Nat.card_congr es.toEquiv).trans
      (CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds s)
  obtain ⟨hb1, hb2, hb3⟩ := sporOrd_bounds s
  haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  rintro (⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩)
  · cases i with
    | lie d =>
      have hdq : d.1.characteristic = q := hi
      obtain ⟨t, n, p', f, hX, hpp', -⟩ := AltFacts4.exists_blueprint_tagged d e
      have hp' : p' = q := hpp'.trans hdq
      subst hp'
      have h1 := CFSG.ComponentClassification.HarrisLit.T1.SporRow.oddLieOrder_of_lieModel hq hq2 hX
      rw [hcard, sporOrd_eq_sporOrder] at h1
      exact CFSG.ComponentClassification.HarrisLit.T1.SporRow.not_oddLieOrder_sporOrder s h1
    | cyclic _ _ => exact hi.elim
    | alternating _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
  · cases i with
    | alternating n hn =>
      have hn56 : n = 5 ∨ n = 6 := by
        rcases hi with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hq2
      have hc : Nat.card X = n.factorial / 2 :=
        (Nat.card_congr e.toEquiv).trans (card_alt n (by omega))
      rw [hcard] at hc
      rcases hn56 with rfl | rfl
      · rw [hc] at hb1
        exact absurd hb1 (by decide)
      · rw [hc] at hb1
        exact absurd hb1 (by decide)
    | lie d =>
      obtain ⟨d, hv⟩ := d
      have hc : Nat.card X = CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula d :=
        CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨d, hv⟩ X ⟨e⟩
      rw [hcard] at hc
      have key : CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula d = 504 ∨
          CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula d = 25920 := by
        cases d with
        | A r q' =>
          rcases r with _ | _ | r
          · simp [ambiguousChev] at hi
          · have hi' : (q'.card = 7 ∧ q = 2) ∨ (q'.card = 8 ∧ q = 3) := by
              simpa [ambiguousChev] using hi
            rcases hi' with ⟨-, h2⟩ | ⟨h8, -⟩
            · exact absurd h2 hq2
            · left
              simp only [CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula]
              rw [h8]
              norm_num [CFSG.Open.orderA]
          · simp [ambiguousChev] at hi
        | twistedA r q' =>
          rcases r with _ | _ | _ | _ | r
          · simp [ambiguousChev] at hi
          · simp [ambiguousChev] at hi
          · have hi' : q'.card = 3 ∧ q = 2 := by simpa [ambiguousChev] using hi
            exact absurd hi'.2 hq2
          · have hi' : q'.card = 2 ∧ q = 3 := by simpa [ambiguousChev] using hi
            right
            simp only [CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula]
            rw [hi'.1]
            decide
          · simp [ambiguousChev] at hi
        | _ => simp [ambiguousChev] at hi
      rcases key with h | h
      · rw [h] at hc
        exact hb2 hc
      · rw [h] at hc
        exact hb3 hc
    | cyclic _ _ => exact hi.elim
    | sporadic _ => exact hi.elim

theorem inputSporDownChev_of_rows
    (hrow : ∀ (s : TauCeti.SporadicName) (p : ℕ), p.Prime → p ≠ 2 →
      p ^ 2 ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s → SporDownRow s p) :
    Claims1116b.InputSporDownChev := by
  intro S _ _ hS hnc p hp hp2 s hs α hα I hI q hq hq2 hqp hchev
  haveI := hS
  haveI : Fact p.Prime := ⟨hp⟩
  have hα1 : α ≠ 1 := by
    rintro rfl
    rw [Claims1116b.fixSubgroup_one_eq_top] at hI
    obtain ⟨f⟩ := CFSG.LocalAnalysis.GLTheoremA.chevQ_pSimple_top_equiv hp hnc hI
    exact not_isChevSimple_of_isSporType (Claims1116.isSporType_congr f.symm hs) hq hq2 hchev
  refine ⟨hα1, ?_⟩
  obtain ⟨x, rfl, hxp⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow hp hp2
    (Claims1116b.center_eq_bot_of_simple hnc)
    (CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds S hS hnc s hs) α hα
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hα1 (map_one _)
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  rw [CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup_conj] at hI
  have hcard : Nat.card S = CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s :=
    (Nat.card_congr hs.some.toEquiv).trans
      (CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds s)
  by_cases h2 : p ^ 2 ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s
  · exact hrow s p hp hp2 h2 S hS hs x hxo I hI q hq hq2 hqp hchev
  · exact (CFSG.HardMathSupport.Solomon.Coordinator.no_glaPComponent_of_exact hp hxo
      (by rw [hcard]; exact h2) hI).elim


theorem sporDownRow_of_leafShape
    {s : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : CFSG.HardMathSupport.Dickson.I271.LeafShape s p) : SporDownRow s p := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
  exact sporDownRow_of_centShape hp b h fun T _ hT => downTypeOK_of_leafType hp hp2 hT

theorem sporDownRow_Co3_three
    : SporDownRow .Co3 3 :=
  sporDownRow_of_leafShape Nat.prime_three (by norm_num)
    CFSG.HardMathSupport.Dickson.I271.leafShape_Co3

theorem sporDownRow_Co2_three
    : SporDownRow .Co2 3 :=
  sporDownRow_of_leafShape Nat.prime_three (by norm_num)
    CFSG.HardMathSupport.Dickson.I271.leafShape_Co2

theorem sporDownRow_Th_three
    : SporDownRow .Th 3 :=
  sporDownRow_of_leafShape Nat.prime_three (by norm_num)
    CFSG.HardMathSupport.Dickson.I271.leafShape_Th

theorem sporDownRow_Fi22_three
    : SporDownRow .Fi22 3 :=
  sporDownRow_of_leafShape Nat.prime_three (by norm_num)
    CFSG.HardMathSupport.Dickson.I271.leafShape_Fi22

theorem sporDownRow_Fi23_three
    : SporDownRow .Fi23 3 :=
  sporDownRow_of_leafShape Nat.prime_three (by norm_num)
    (HardMathSupport.Dickson.I271.TabFi23.leafShape_Fi23_of
        HardMathSupport.Dickson.I271.TabFi23.pConstrained_t3_two)

theorem sporDownRow_Fi24Prime_three
    : SporDownRow .Fi24Prime 3 :=
  sporDownRow_of_leafShape Nat.prime_three (by norm_num)
    CFSG.HardMathSupport.Dickson.I271.leafShape_Fi24_three

theorem sporDownRow_HN_three
    : SporDownRow .HN 3 :=
  sporDownRow_of_leafShape Nat.prime_three (by norm_num)
    CFSG.HardMathSupport.Dickson.I271.leafShape_HN



open CFSG.LocalAnalysis.GLTheoremA.KDSpor (false_of_glaPComponent_of_solvable
  false_of_glaPComponent_of_pConstrained isSolvable_of_card_two_mul isSolvable_of_card_eq
  no_comp_of_conj)


theorem downCompOK_five_of_card_dvd_3000
    {s : TauCeti.SporadicName} {Q : Type} [Group Q] [Finite Q]
    {k : Q} (hk : Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ 3000) : DownCompOK s 5 k := by
  intro I hI
  obtain ⟨hs, hnab⟩ := CFSG.LocalAnalysis.GLTheoremA.KDSpor.pSimple_simple_nonab Nat.prime_five hI
  haveI := hs
  have hd : Nat.card (PSimple 5 I) ∣ 3000 :=
    ((CFSG.LocalAnalysis.GLTheoremA.KDL227Rows.card_pSimple_dvd 5 I).trans
      (Subgroup.card_dvd_of_le hI.1)).trans hk
  obtain ⟨fA⟩ := CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    (CFSG.LocalAnalysis.GLTheoremA.KDSpor.card_eq_sixty_of_dvd_3000 hnab hd)
  exact downTypeOK_of_chevP (by norm_num) (isChevSimple_five_of_A5 fA)

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem sporDownRow_M11_three
    : SporDownRow .M11 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  exact sporDownRow_three_of_perm b fun x hx h3 =>
    CFSG.LocalAnalysis.GLTheoremA.KDSpor.check_card_lt m11S3Data rep_m11A rep_m11B
      Certificates.certificate13511.1 (by decide) x hx h3

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem sporDownRow_M12_three
    : SporDownRow .M12 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  exact sporDownRow_three_of_perm b fun x hx h3 =>
    CFSG.LocalAnalysis.GLTheoremA.KDSpor.check_card_lt m12S3Data rep_m12A rep_m12B
      Certificates.certificate13511.2.1 (by decide) x hx h3

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem sporDownRow_M22_three
    : SporDownRow .M22 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  exact sporDownRow_three_of_perm b fun x hx h3 =>
    CFSG.LocalAnalysis.GLTheoremA.KDSpor.check_card_lt m22S3Data rep_m22A rep_m22B
      Certificates.certificate13511.2.2.1 (by decide) x hx h3

theorem sporDownRow_McL_three
    : SporDownRow .McL 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .McL
  have hsh := CFSG.HardMathSupport.Dickson.I271.mcl_constrainedShape_three
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.oPrimeCoreTrivialAt_McL
  exact sporDownRow_of_centShape (Good := fun _ _ => False) Nat.prime_three b
    (fun k hk1 hk3 => Or.inl (hsh k hk1 hk3)) fun _ _ h => h.elim

theorem sporDownRow_Ly_five
    : SporDownRow .Ly 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Ly
  exact sporDownRow_of_centShape (Good := fun _ _ => False) Nat.prime_five b
    (fun k hk1 hk5 => Or.inl (CFSG.HardMathSupport.Dickson.I271.pConstrainedShape_Ly_five _
      ⟨MulEquiv.refl _⟩ (orderOf_eq_prime hk5 hk1))) fun _ _ h => h.elim

theorem sporDownRow_McL_five
    : SporDownRow .McL 5 := by
  have hc : Nat.card CFSG.Blueprint.NativeSporadic.McL = 898128000 := CFSG.Sporadic.McL.card_McL
  haveI : Finite CFSG.Blueprint.NativeSporadic.McL :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have b : CFSG.Blueprint.NativeSporadic.McL ≃* (TauCeti.CFSGIndex.sporadic .McL).Group :=
    (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .McL).some
  obtain ⟨x₁, x₂, -, -, c₁, c₂, -, hall⟩ :=
    CFSG.Sporadic.Recognition.McLAS.mcl_two_classes_order_five_of_certificate
  have hrow := @sporDownRow_of_model' .McL 5 Nat.prime_five CFSG.Blueprint.NativeSporadic.McL _ _ b
  refine hrow fun x hx => downCompOK_of_no_comp fun I hI => ?_
  refine false_of_glaPComponent_of_solvable Nat.prime_five ?_ hI
  rcases hall x hx with h | h
  · have : Nat.card (Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.McL)) = 750 := by
      rw [CFSG.Sporadic.Recognition.LyonsSims.card_centralizer_eq_of_isConj h, c₁]
    exact isSolvable_of_card_two_mul (p := 3) (q := 5) (a := 1) (b := 3) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by rw [this]; norm_num)
  · have : Nat.card (Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.McL)) = 25 := by
      rw [CFSG.Sporadic.Recognition.LyonsSims.card_centralizer_eq_of_isConj h, c₂]
    exact isSolvable_of_card_eq (p := 5) (q := 2) (a := 2) (b := 0) (by norm_num) (by norm_num)
      (by norm_num) (by rw [this]; norm_num)

set_option maxRecDepth 100000 in
theorem sporDownRow_ON_seven
    : SporDownRow .ONan 7 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  refine sporDownRow_of_noComp (by norm_num) (CFSG.ONSchreier.onEquivPv.symm.trans b)
    fun x hx I hI => ?_
  refine false_of_glaPComponent_of_solvable (by norm_num) ?_ hI
  rcases
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.KF148ONA7.card_centralizer_seven_Pv
      hx with h | h
  · exact isSolvable_of_card_eq (p := 2) (q := 7) (a := 2) (b := 3) (by norm_num) (by norm_num)
      (by norm_num) (by rw [h]; norm_num)
  · exact isSolvable_of_card_eq (p := 7) (q := 2) (a := 2) (b := 0) (by norm_num) (by norm_num)
      (by norm_num) (by rw [h]; norm_num)

theorem sporDownRow_ON_three
    : SporDownRow .ONan 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .ONan
  exact sporDownRow_of_centShape Nat.prime_three b
    (CFSG.HardMathSupport.Dickson.I271.CentShape.of_centShapeRk
      CFSG.HardMathSupport.Dickson.I271.onThree_centShapeRk)
    fun _ _ h => downTypeOK_of_chevP (by norm_num) (isChevSimple_three_of_A6 h.2.some)

set_option maxRecDepth 20000 in
theorem sporDownRow_Th_five
    : SporDownRow .Th 5 := by
  have hfin : Finite ↥CFSG.Sporadic.Th.J := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.finite_J
  have e : CFSG.Blueprint.NativeSporadic.Th ≃* ↥CFSG.Sporadic.Th.J := CFSG.Sporadic.Th.thEquivJ
  have b : ↥CFSG.Sporadic.Th.J ≃* (TauCeti.CFSGIndex.sporadic .Th).Group :=
    e.symm.trans (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Th).some
  have hcard := CFSG.HardMathSupport.Dickson.Sec6.I1431.card_centralizer_c5
  have hrow := @sporDownRow_of_model' .Th 5 Nat.prime_five ↥CFSG.Sporadic.Th.J _ hfin b
  refine hrow fun k hk => ?_
  obtain ⟨m, hm⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_c5 hk
  refine downCompOK_five_of_card_dvd_3000 ?_
  have hck := @CFSG.LocalAnalysis.GLTheoremA.KDSpor.card_centralizer_conj_eq ↥CFSG.Sporadic.Th.J _
    hfin m k
  rw [hck, hm, hcard]

set_option maxRecDepth 100000 in
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
  CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.HardMathSupport.Timmesfeld.Tables.Census in
theorem sporDownRow_J4_eleven
    : SporDownRow .J4 11 := by
  have b : ↥J ≃* (TauCeti.CFSGIndex.sporadic .J4).Group :=
    (seedEquiv j4Facts.mat).symm.trans
      (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .J4).some
  have hrow := @sporDownRow_of_model' .J4 11 (by norm_num) ↥J _ inferInstance b
  refine hrow fun x hx => downCompOK_of_no_comp fun I hI => ?_
  obtain ⟨h, hh⟩ := exists_conj_mem_of_orderOf Q11 card_Q11 not_eleven_pow_four_dvd_card_J hx
  refine no_comp_of_conj (by norm_num) h x (fun I hI => ?_) I hI
  set u := h⁻¹ * x * h with hu
  have huo : orderOf u = 11 := by
    have := orderOf_conj_eq' h⁻¹ x
    rw [inv_inv] at this
    rw [hu, this, hx]
  by_cases hz : u ∈ Subgroup.zpowers qz
  · have hzp : Subgroup.zpowers u = Subgroup.zpowers qz :=
      Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hz)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, huo, orderOf_qz])
    rw [centralizer_singleton_eq_of_zpowers hzp] at hI
    refine false_of_glaPComponent_of_pConstrained (by norm_num) ?_ hI
    have hQC : Q11 ≤ Subgroup.centralizer ({qz} : Set ↥J) := fun q hq =>
      Subgroup.mem_centralizer_singleton_iff.2 (qz_commute_of_mem hq)
    refine ⟨Q11, hQC, fun g hg q hq => ?_, IsPGroup.of_card card_Q11,
      inf_le_right.trans centralizer_Q11_le⟩
    exact (Subgroup.mem_normalizer_iff.1 (centralizer_qz_le_normalizer_J4 hg) q).1 hq
  · obtain ⟨h121, h242⟩ := card_centralizer_noncentral_le hh hz
    refine false_of_glaPComponent_of_solvable (by norm_num) ?_ hI
    obtain ⟨k, hk⟩ := h121
    have hk2 : k = 1 ∨ k = 2 := by
      have : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · rw [h0, mul_zero] at hk; exact absurd hk Nat.card_pos.ne'
        · exact h0
      omega
    haveI := Fintype.ofFinite ↥(Subgroup.centralizer ({u} : Set ↥J))
    refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      (p := 11) (q := 2) (a := 2) (b := k - 1) (by norm_num) (by norm_num) (by norm_num) ?_
    rw [Fintype.card_eq_nat_card, hk]
    rcases hk2 with rfl | rfl <;> norm_num

set_option maxRecDepth 100000 in
open CFSG.Open CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSeven
  CFSG.LocalAnalysis.GLTheoremA.I1416Rows in
theorem downCompOK_seven_ThJ
    (k : J) (hk : orderOf k = 7) : DownCompOK .Th 7 k := by
  have hp7 : Nat.Prime 7 := by norm_num
  haveI : Fact (Nat.Prime 7) := ⟨hp7⟩
  haveI : Finite J :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  have hz : DownCompOK .Th 7 (slpJ a b prog7 24 * slpJ a b prog7 25 ^ 6) := by
    intro I hI
    obtain ⟨hs, hnab⟩ := CFSG.LocalAnalysis.GLTheoremA.KDSpor.pSimple_simple_nonab hp7 hI
    haveI := hs
    have hd : 7 * Nat.card (PSimple 7 I) ∣ 1176 :=
      card_centralizer_z7 ▸ prime_mul_card_pSimple_dvd_cent hp7 orderOf_z7 hI.1
    have hd168 : Nat.card (PSimple 7 I) ∣ 168 :=
      Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 7) (hd.trans (by norm_num))
    have hc := card_eq_168_of_dvd hnab hd168
    exact downTypeOK_of_not_chev (not_isChevSimple_of_card_bound hc (by norm_num) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide))
  obtain ⟨h7x, h7y, hcomm, hx1, hpow⟩ := thSeven_pair
  obtain ⟨c, hc⟩ := exists_conj_eq_of_pair (z := slpJ a b prog7 24 * slpJ a b prog7 25 ^ 6)
    (matJ_injective (by simp only [matJ_mul]; exact hcomm)) h7x h7y hx1 hpow
    (by rw [CFSG.Sporadic.Th.Max3.natCard_J,
      show (90745943887872000 : ℕ) = 7 ^ 2 * 1851958038528000 by norm_num,
      factorization_pow_mul Nat.prime_seven 2 _ (by norm_num)])
    (fun i j hi hj hij => by
      obtain ⟨m, hm⟩ := thSeven_conj hi hj hij
      refine ⟨m, matJ_injective ?_⟩
      simp only [matJ_mul, matJ_pow] at hm ⊢
      exact hm) hk
  have := downCompOK_of_mulEquiv hp7 (MulAut.conj c⁻¹) hz
  rw [MulAut.conj_apply, ← hc, show c⁻¹ * (c * k * c⁻¹) * c⁻¹⁻¹ = k by group] at this
  exact this

set_option maxRecDepth 20000 in
theorem sporDownRow_Th_seven
    : SporDownRow .Th 7 := by
  have hfin : Finite ↥CFSG.Sporadic.Th.J := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.finite_J
  have e : CFSG.Blueprint.NativeSporadic.Th ≃* ↥CFSG.Sporadic.Th.J := CFSG.Sporadic.Th.thEquivJ
  have b : ↥CFSG.Sporadic.Th.J ≃* (TauCeti.CFSGIndex.sporadic .Th).Group :=
    e.symm.trans (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Th).some
  have hrow := @sporDownRow_of_model' .Th 7 (by norm_num) ↥CFSG.Sporadic.Th.J _ hfin b
  exact hrow downCompOK_seven_ThJ



theorem sporDownRow_J3_three
    : SporDownRow .J3 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .J3
  exact sporDownRow_of_model Nat.prime_three b fun hfin _ hk => by
    haveI := hfin
    exact downCompOK_of_centShapeSplit Nat.prime_three (by norm_num)
      CFSG.HardMathSupport.Dickson.I271.centShapeSplit_J3 hk

theorem sporDownRow_Suz_three
    : SporDownRow .Suz 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Suz
  exact sporDownRow_of_model Nat.prime_three b fun hfin _ hk => by
    haveI := hfin
    exact downCompOK_of_centShapeSplit Nat.prime_three (by norm_num)
      CFSG.HardMathSupport.Dickson.I271.centShapeSplit_Suz hk

theorem sporDownRow_HN_five
    : SporDownRow .HN 5 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .HN
  exact sporDownRow_of_model Nat.prime_five b fun hfin _ hk => by
    haveI := hfin
    exact downCompOK_of_centShapeRk' Nat.prime_five
      (CFSG.HardMathSupport.Dickson.I271.hn5_centShapeRk'_HN
        CFSG.HardMathSupport.Dickson.I271.hnFiveMoved_holds)
      (fun _ _ h => downTypeOK_of_goodSpor_nil Nat.prime_five (by norm_num) h) hk

theorem sporDownRow_J4_three
    : SporDownRow .J4 3 := by
  obtain ⟨hfin, -, -, ⟨b⟩⟩ :=
    CFSG.Sporadic.J4.j4_model CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hM : Nat.card CFSG.Blueprint.NativeSporadic.M22 = 443520 := CFSG.Sporadic.Mathieu.card_M22
  haveI : Finite CFSG.Blueprint.NativeSporadic.M22 :=
    Nat.finite_of_card_ne_zero (by rw [hM]; norm_num)
  have hrow := @sporDownRow_of_model' .J4 3 Nat.prime_three ↥CFSG.Sporadic.J4.J _ hfin b
  refine hrow fun x hx I hI => ?_
  obtain ⟨e⟩ := CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.pSimple_of_glaPComponent_three
    Nat.prime_three hx hI
  exact downTypeOK_of_mulEquiv e.symm (downTypeOK_of_not_chev fun q _ _ _ =>
    CFSG.LocalAnalysis.GLTheoremA.I1416Rows.not_isChevSimple_M22
      CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds hM q)

theorem sporDownRow_three_of_check
    {s : TauCeti.SporadicName} (hs : s = .M23 ∨ s = .HS)
    (D : CFSG.HardMathSupport.Solomon.Coordinator.B3S3.Data)
    (hD : CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check D = true)
    {A B : Equiv.Perm (Fin D.n)}
    (hA : CFSG.Monster.B.Co2.Rep D.n D.A A) (hB : CFSG.Monster.B.Co2.Rep D.n D.B B)
    (b : ↥(Subgroup.closure {A, B}) ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hsmall : ∀ c < D.cases.size, D.cases[c]!.card ∣ 360) : SporDownRow s 3 := by
  obtain ⟨-, hcls⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check_card_order_sound D hA hB hD
  refine sporDownRow_of_model' Nat.prime_three b fun x hx => ?_
  have hx3 : orderOf (x : Equiv.Perm (Fin D.n)) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨c, hc, hcc⟩ := hcls x x.2 hx3
  refine downCompOK_three_of_card_dvd_360 hs hx ?_
  have hmapc := CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype
    (Subgroup.closure {A, B}) x
  have hcc' : Nat.card (Subgroup.centralizer ({x} : Set ↥(Subgroup.closure {A, B}))) =
      Nat.card ↥(Subgroup.centralizer ({(x : Equiv.Perm (Fin D.n))} : Set (Equiv.Perm (Fin D.n))) ⊓
        Subgroup.closure {A, B}) := by
    rw [← hmapc, Subgroup.card_map_of_injective (Subgroup.closure {A, B}).subtype_injective]
  rw [hcc', hcc]
  exact hsmall c hc

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem sporDownRow_M23_three
    : SporDownRow .M23 3 :=
  sporDownRow_three_of_check (Or.inl rfl) m23S3Data Certificates.certificate13511.2.2.2
    rep_m23A rep_m23B (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .M23).some
    (by decide +kernel)

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem sporDownRow_HS_three
    : SporDownRow .HS 3 := by
  have h := Certificates.certificate13514
  obtain ⟨hvA, hvB⟩ := check_valid h
  have e : CFSG.Blueprint.NativeSporadic.HS ≃* ↥CFSG.Sporadic.Schreier.hsP :=
    CFSG.Sporadic.Schreier.hsPermEquiv
  exact sporDownRow_three_of_check (Or.inr rfl) hsS3Data h (CFSG.RankThree.Native.rep_of_validA hvA)
    (CFSG.RankThree.Native.rep_of_validA hvB)
    (e.symm.trans (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .HS).some)
    (by decide +kernel)

theorem sporDownRow_Fi22_five
    : SporDownRow .Fi22 5 := by
  intro S _ _ _ hS x hx I hI
  obtain ⟨f⟩ := SporFacts.input14_21_holds S hS x hx
  have hL : Nat.card ↥(GLAPLayer 5 (Subgroup.centralizer ({x} : Set S))) = 60 := by
    rw [Nat.card_congr f.toEquiv, card_alt 5 (by norm_num)]
    rfl
  have hIL : I ≤ GLAPLayer 5 (Subgroup.centralizer ({x} : Set S)) := le_sSup hI
  obtain ⟨hs, hnab⟩ := CFSG.LocalAnalysis.GLTheoremA.KDSpor.pSimple_simple_nonab Nat.prime_five hI
  haveI := hs
  have hd : Nat.card (PSimple 5 I) ∣ 3000 :=
    ((CFSG.LocalAnalysis.GLTheoremA.KDL227Rows.card_pSimple_dvd 5 I).trans
      ((Subgroup.card_dvd_of_le hIL).trans (by rw [hL]; norm_num)))
  obtain ⟨fA⟩ := CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    (CFSG.LocalAnalysis.GLTheoremA.KDSpor.card_eq_sixty_of_dvd_3000 hnab hd)
  exact downTypeOK_of_chevP (by norm_num) (isChevSimple_five_of_A5 fA)



theorem downTypeOK_of_goodSpor
    {s : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {names : List TauCeti.SporadicName} {T : Type} [Group T]
    (h : CFSG.HardMathSupport.Dickson.I271.GoodSpor p names T) : DownTypeOK s p T := by
  rcases h with hl | ⟨h3, ⟨f⟩⟩ | ⟨S, -, ⟨f⟩⟩
  · exact downTypeOK_of_leafType hp hp2 hl
  · subst h3
    exact downTypeOK_of_chevP (by norm_num) (isChevSimple_three_of_A6 f)
  · exact downTypeOK_of_not_chev fun q hq hq2 _ => not_isChevSimple_of_isSporType ⟨f⟩ hq hq2

theorem sporDownRow_Ly_three
    : SporDownRow .Ly 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Ly
  exact sporDownRow_of_centShape Nat.prime_three b
    (CFSG.HardMathSupport.Dickson.I271.CentShape.of_centShapeRk
      (CFSG.HardMathSupport.Dickson.I271.tabLy_centShapeRk
        CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
        CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group))
    fun _ _ h => downTypeOK_of_goodSpor Nat.prime_three (by norm_num) h

theorem sporDownRow_M_seven
    : SporDownRow .M 7 := by
  intro S _ _ hS hs x hx I hI
  haveI := hS
  have hsh := CFSG.HardMathSupport.Dickson.I271.simpleCentShapeRk'_M_of_gmat (p := 7) (by norm_num)
    (fun _ _ _ _ e h => CFSG.HardMathSupport.Dickson.I271.GoodSpor.of_equiv e h)
    (fun _ _ _ _ e h => CFSG.HardMathSupport.Dickson.I271.RkSpor.of_equiv e h)
    (CFSG.HardMathSupport.Dickson.I271.TabMSeven.mSevenShapeGmat
      CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds)
  have hS' := hsh S
    (hs.some.trans (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .M).some.symm)
  exact downCompOK_of_centShapeRk' (by norm_num) hS'
    (fun _ _ h => downTypeOK_of_goodSpor (by norm_num) (by norm_num) h) hx I hI

theorem sporDownRow_Co1_five
    : SporDownRow .Co1 5 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Co1
  exact sporDownRow_of_model Nat.prime_five b fun hfin _ hk => by
    haveI := hfin
    exact downCompOK_of_centShapeMulti Nat.prime_five
      (CFSG.HardMathSupport.Dickson.I271.TabCo1.centShapeMulti_Co1_five
        CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds)
      (fun _ _ h => downTypeOK_of_goodSpor Nat.prime_five (by norm_num) h) hk

theorem sporDownRow_He_three
    : SporDownRow .He 3 := by
  intro S _ _ hS hs x hx I hI
  haveI := hS
  have hcard : Nat.card S = CFSG.HardMathSupport.Solomon.Coordinator.sporOrd .He :=
    (Nat.card_congr hs.some.toEquiv).trans
      (CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds .He)
  have hnc : ∃ a b : S, a * b ≠ b * a :=
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by
      rw [hcard, show CFSG.HardMathSupport.Solomon.Coordinator.sporOrd .He = 4030387200 from rfl]
      norm_num)
  have hcen : Subgroup.center S = ⊥ := Claims1116b.center_eq_bot_of_simple hnc
  let eT : ↥(⊤ : Subgroup S) ≃* S := Subgroup.topEquiv
  haveI : IsSimpleGroup ↥(⊤ : Subgroup S) := eT.isSimpleGroup
  have hncT : ∃ a b : ↥(⊤ : Subgroup S), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨eT.symm a, eT.symm b, fun h => hab (by simpa using congrArg eT h)⟩
  have hq : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup S) :=
    CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_isQuasisimple_of_simple hncT
  have hZ : Subgroup.center ↥(⊤ : Subgroup S) = ⊥ := Claims1116b.center_eq_bot_of_simple hncT
  have hsp : IsSporType .He (↥(⊤ : Subgroup S) ⧸ Subgroup.center ↥(⊤ : Subgroup S)) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientBot.trans (eT.trans hs.some))⟩
  have hx1 : ∃ q ∈ (⊤ : Subgroup S), x * q ≠ q * x := by
    by_contra h
    push Not at h
    have hxc : x ∈ Subgroup.center S :=
      Subgroup.mem_center_iff.2 fun g => (h g (Subgroup.mem_top g)).symm
    rw [hcen, Subgroup.mem_bot] at hxc
    rw [hxc, orderOf_one] at hx
    norm_num at hx
  have hxN : x ∈ Subgroup.normalizer ((⊤ : Subgroup S) : Set S) :=
    Subgroup.mem_normalizer_iff.2 fun h => by simp
  have hI' : GLAPComponent 3 ((⊤ : Subgroup S) ⊓ Subgroup.centralizer ({x} : Set S)) I := by
    rw [top_inf_eq]
    exact hI
  rcases SporFacts.inputHeCent_holds S ⊤ hq hsp x hxN hx hx1 I hI' with h7 | h7
  · exact fun _ _ _ _ _ => Or.inr (Or.inl ⟨rfl, Or.inr rfl, h7⟩)
  · refine downTypeOK_of_not_chev fun q _ hq2 _ hc => ?_
    rcases Prop1116Design.alt_chev_cases AltFacts4.inputAltNotLie_holds hq2 (by norm_num) h7 hc with
      ⟨h, -⟩ | ⟨h, -⟩ <;> omega


section RowJ2

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.PartOne CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore

theorem sporDownRow_J2_five
    : SporDownRow .J2 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hQP, -, -, hQcard, -⟩, ⟨hlinesSet, -⟩, hrec, hgood, hbad⟩ :=
    R3E_J2_full_five_centralizer_structure
  have hM := j2_autModel
  have e : CFSG.Blueprint.NativeSporadic.J2 ≃* ↥j2P := j2PermEquiv
  have hfin : Finite ↥j2P := inferInstance
  have b : ↥j2P ≃* (TauCeti.CFSGIndex.sporadic .J2).Group :=
    e.symm.trans (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .J2).some
  have hlineQ : ∀ i, Subgroup.zpowers (j2FiveLine i) ≤ j2FiveQ ∧
      Nat.card (Subgroup.zpowers (j2FiveLine i)) = 5 := by
    intro i
    have h : Subgroup.zpowers (j2FiveLine i) ∈
        {H : Subgroup (Equiv.Perm (Fin 315)) | H ≤ j2FiveQ ∧ Nat.card H = 5} := by
      rw [hlinesSet]; exact ⟨i, rfl⟩
    exact h
  have hmem : ∀ i, j2FiveLine i ∈ j2P :=
    fun i => hQP ((hlineQ i).1 (Subgroup.mem_zpowers _))
  have hline : ∀ i, DownCompOK .J2 5 (⟨j2FiveLine i, hmem i⟩ : ↥j2P) := by
    intro i
    obtain ⟨hCeq, hQC, hQeq, -⟩ := hrec i
    have hC : j2FiveC i =
        Subgroup.centralizer ({j2FiveLine i} : Set (Equiv.Perm (Fin 315))) ⊓ j2R := by
      rw [hCeq, inf_comm]
    by_cases hg : i.val = 0 ∨ i.val = 1 ∨ i.val = 4
    · obtain ⟨-, hnorm⟩ := hgood i hg
      exact downCompOK_of_pgroup_record Nat.prime_five hM.le (hmem i) hC hQC hnorm hQP
        j2FiveQ_isPGroup (le_of_eq hQeq)
    · have hbad' : i.val = 2 ∨ i.val = 3 ∨ i.val = 5 := by
        have := i.2
        omega
      obtain ⟨-, hDP, hDs, hDnab, hDcard, hDn, hDcent, -⟩ := hbad i hbad'
      obtain ⟨-, hDC, -⟩ := (j2Five_record i).2.2 hbad'
      have hDfin : Finite ↥(j2FiveD i) := Finite.of_injective (Subgroup.inclusion hDP)
        (Subgroup.inclusion_injective hDP)
      refine downCompOK_of_normal_record Nat.prime_five hM.le (hmem i) hC hDC hDn hDs hDnab hDP
        hDcent (orderOf_j2FiveLine i) ?_ (by rw [hDcard]; norm_num)
        (downTypeOK_of_chevP (by norm_num) (isChevSimple_five_of_A5
          (@CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty _ _
            hDfin hDs hDcard).some))
      exact gLAPPrimeCoreOf_inf_eq_bot_of_ambient Nat.prime_five hM.le hM.conj_mem
        (gLAPPrimeCoreOf_j2FiveC_eq_bot i)
  have hrow := @sporDownRow_of_model' .J2 5 Nat.prime_five ↥j2P _ hfin b
  exact hrow (downCompOK_of_lines Nat.prime_five hQP
      (by rw [hQcard, factorization_card_j2P_five]; norm_num) j2FiveLine
      (fun H hHQ hHc => by
        have hm : H ∈ {H : Subgroup (Equiv.Perm (Fin 315)) | H ≤ j2FiveQ ∧ Nat.card H = 5} :=
          ⟨hHQ, hHc⟩
        rw [hlinesSet] at hm
        obtain ⟨j, hj⟩ := hm
        exact ⟨j, hj.symm⟩) hmem hline)

end RowJ2

section RowCo3

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.Native CFSG.Sporadic.Schreier.Co3

theorem sporDownRow_Co3_five
    : SporDownRow .Co3 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlinesSet, -⟩, htrans, hrec0, hrec25, hC0, -, hDs, hDnab, hDcard,
    hDcent, -, hC25, -, hAC, hAn, hAcard, -, -, hAc⟩ := R3E_Co3_full_five_centralizer_structures
  have e : CFSG.Blueprint.NativeSporadic.Co3 ≃* ↥co3P := co3PermEquiv
  have hfin : Finite ↥co3P := inferInstance
  have b : ↥co3P ≃* (TauCeti.CFSGIndex.sporadic .Co3).Group :=
    e.symm.trans (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Co3).some
  have hlines := lines_of_eq hlinesSet
  have hlineQ : ∀ j, Subgroup.zpowers (co3FiveLine j) ≤ co3FiveQ ∧
      Nat.card (Subgroup.zpowers (co3FiveLine j)) = 5 := by
    intro j
    have h : Subgroup.zpowers (co3FiveLine j) ∈
        {H : Subgroup (Equiv.Perm (Fin 276)) | H ≤ co3FiveQ ∧ Nat.card H = 5} := by
      rw [hlinesSet]; exact ⟨j, rfl⟩
    exact h
  have hmem : ∀ j, co3FiveLine j ∈ co3P :=
    fun j => hQP ((hlineQ j).1 (Subgroup.mem_zpowers _))
  have hord : ∀ j, orderOf (co3FiveLine j) = 5 := fun j => by
    rw [← Nat.card_zpowers]; exact (hlineQ j).2
  have hnorm : ∀ r ∈ co3P, ∀ q ∈ co3P, r * q * r⁻¹ ∈ co3P :=
    fun r hr q hq => co3P.mul_mem (co3P.mul_mem hr hq) (co3P.inv_mem hr)
  have hL0 : DownCompOK .Co3 5 (⟨co3FiveLine 0, hmem 0⟩ : ↥co3P) := by
    have hD : co3FiveD = ⁅co3FiveC0, co3FiveC0⁆ := rfl
    have hDC : co3FiveD ≤ co3FiveC0 := by
      rw [hD, Subgroup.commutator_le]
      intro a ha c hc
      rw [commutatorElement_def]
      exact co3FiveC0.mul_mem (co3FiveC0.mul_mem (co3FiveC0.mul_mem ha hc)
        (co3FiveC0.inv_mem ha)) (co3FiveC0.inv_mem hc)
    have hDP : co3FiveD ≤ co3P := fun d hd => (hC0 ▸ hDC hd : d ∈ _ ⊓ co3P).2
    have hDfin : Finite ↥co3FiveD := Finite.of_injective (Subgroup.inclusion hDP)
      (Subgroup.inclusion_injective hDP)
    exact downCompOK_of_derived_record (C := co3FiveC0) (D := co3FiveD) Nat.prime_five le_rfl
      (hmem 0) hC0 hD hDs hDnab hDP hDcent (hord 0)
      (gLAPPrimeCoreOf_co3FiveRecord_eq_bot 0 (Or.inl rfl)) (by rw [hDcard]; norm_num)
      (downTypeOK_of_chevP (by norm_num) (isChevSimple_five_of_A5
          (@CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty _ _
          hDfin hDs hDcard).some))
  have hL25 : DownCompOK .Co3 5 (⟨co3FiveLine 25, hmem 25⟩ : ↥co3P) := by
    have hAP : co3FiveA ≤ co3P := fun a ha => (hC25 ▸ hAC ha : a ∈ _ ⊓ co3P).2
    exact downCompOK_of_pgroup_record Nat.prime_five le_rfl (hmem 25) hC25 hAC hAn hAP
      (IsPGroup.of_card (n := 3) (by rw [hAcard]; norm_num)) hAc
  have hline : ∀ j, DownCompOK .Co3 5 (⟨co3FiveLine j, hmem j⟩ : ↥co3P) := by
    intro j
    obtain ⟨hjP, hjconj⟩ := htrans j
    have hr : DownCompOK .Co3 5 (⟨co3FiveLine (co3FiveRecordOf j), hmem _⟩ : ↥co3P) := by
      by_cases h : (j : ℕ) = 25
      · rw [(hrec25 j).2 h]; exact hL25
      · rw [(hrec0 j).2 h]; exact hL0
    have h := downCompOK_conj Nat.prime_five hnorm hjP (hmem _) hr
    have heq : (⟨co3FiveTransporter j * co3FiveLine (co3FiveRecordOf j) *
        (co3FiveTransporter j)⁻¹, hnorm _ hjP _ (hmem _)⟩ : ↥co3P) =
        ⟨co3FiveLine j, hmem j⟩ := Subtype.ext hjconj
    rw [heq] at h
    exact h
  have hrow := @sporDownRow_of_model' .Co3 5 Nat.prime_five ↥co3P _ hfin b
  exact hrow (downCompOK_of_lines Nat.prime_five hQP
      (card_eq_of_sylow_subgroupOf hQP hQsyl) co3FiveLine hlines hmem hline)

end RowCo3

section RowHe

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.PartOne CFSG.Sporadic.HeldB

theorem sporDownRow_He_five
    : SporDownRow .He 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlinesSet, -⟩, htrans, hrec, ⟨hC0, -⟩,
    ⟨hDs, hDnab, hDcard, hDP, hDcent, -⟩⟩ := R3E_He_full_five_centralizer_structures
  have hM := heAutModel
  have e : CFSG.Blueprint.NativeSporadic.He ≃* ↥heP := heEquivP
  have hfin : Finite ↥heP := inferInstance
  have b : ↥heP ≃* (TauCeti.CFSGIndex.sporadic .He).Group :=
    e.symm.trans (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .He).some
  have hlines := lines_of_eq hlinesSet
  have hlineQ : ∀ j, Subgroup.zpowers (heFiveLine j) ≤ heFiveQ ∧
      Nat.card (Subgroup.zpowers (heFiveLine j)) = 5 := by
    intro j
    have h : Subgroup.zpowers (heFiveLine j) ∈
        {H : Subgroup (Equiv.Perm (Fin 8330)) | H ≤ heFiveQ ∧ Nat.card H = 5} := by
      rw [hlinesSet]; exact ⟨j, rfl⟩
    exact h
  have hmem : ∀ j, heFiveLine j ∈ heP :=
    fun j => hQP ((hlineQ j).1 (Subgroup.mem_zpowers _))
  have hord : ∀ j, orderOf (heFiveLine j) = 5 := fun j => by
    rw [← Nat.card_zpowers]; exact (hlineQ j).2
  have hL0 : DownCompOK .He 5 (⟨heFiveLine 0, hmem 0⟩ : ↥heP) := by
    have hDfin : Finite ↥heFiveD0 := Finite.of_injective (Subgroup.inclusion hDP)
      (Subgroup.inclusion_injective hDP)
    exact downCompOK_of_derived_record (C := heFiveC0) (D := heFiveD0) Nat.prime_five hM.le
      (hmem 0) hC0 rfl hDs hDnab hDP hDcent (hord 0)
      (gLAPPrimeCoreOf_inf_eq_bot_of_ambient Nat.prime_five hM.le hM.conj_mem
        gLAPPrimeCoreOf_heFiveRecord_eq_bot) (by rw [hDcard]; norm_num)
      (downTypeOK_of_chevP (by norm_num) (isChevSimple_five_of_A5
          (@CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty _ _
          hDfin hDs hDcard).some))
  have hline : ∀ j, DownCompOK .He 5 (⟨heFiveLine j, hmem j⟩ : ↥heP) := by
    intro j
    obtain ⟨hjR, hjconj⟩ := htrans j
    have hr : DownCompOK .He 5 (⟨heFiveLine (heFiveRecordOf j), hmem _⟩ : ↥heP) := by
      rw [hrec j]; exact hL0
    have h := downCompOK_conj Nat.prime_five hM.conj_mem hjR (hmem _) hr
    have heq : (⟨heFiveTransporter j * heFiveLine (heFiveRecordOf j) *
        (heFiveTransporter j)⁻¹, hM.conj_mem _ hjR _ (hmem _)⟩ : ↥heP) =
        ⟨heFiveLine j, hmem j⟩ := Subtype.ext hjconj
    rw [heq] at h
    exact h
  have hrow := @sporDownRow_of_model' .He 5 Nat.prime_five ↥heP _ hfin b
  exact hrow (downCompOK_of_lines Nat.prime_five hQP
      (card_eq_of_sylow_subgroupOf hQP hQsyl) heFiveLine hlines hmem hline)

end RowHe

section RowCo2

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.Native CFSG.Sporadic.Co2Cert

theorem sporDownRow_Co2_five
    : SporDownRow .Co2 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlinesSet, -⟩, htrans, hrec0, hC0, -, hAC, hAn, hAcard, -, -,
    hAc, hC1, -, hDs, hDnab, hDcard, hDcent, hDcard5⟩ := R3E_Co2_full_five_centralizer_structures
  have e : CFSG.Blueprint.NativeSporadic.Co2 ≃* ↥co2P := co2PermEquiv
  have hfin : Finite ↥co2P := inferInstance
  have b : ↥co2P ≃* (TauCeti.CFSGIndex.sporadic .Co2).Group :=
    e.symm.trans (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Co2).some
  have hlines := lines_of_eq hlinesSet
  have hlineQ : ∀ j, Subgroup.zpowers (co2FiveLine j) ≤ co2FiveQ ∧
      Nat.card (Subgroup.zpowers (co2FiveLine j)) = 5 := by
    intro j
    have h : Subgroup.zpowers (co2FiveLine j) ∈
        {H : Subgroup (Equiv.Perm (Fin 2300)) | H ≤ co2FiveQ ∧ Nat.card H = 5} := by
      rw [hlinesSet]; exact ⟨j, rfl⟩
    exact h
  have hmem : ∀ j, co2FiveLine j ∈ co2P :=
    fun j => hQP ((hlineQ j).1 (Subgroup.mem_zpowers _))
  have hord : ∀ j, orderOf (co2FiveLine j) = 5 := fun j => by
    rw [← Nat.card_zpowers]; exact (hlineQ j).2
  have hnorm : ∀ r ∈ co2P, ∀ q ∈ co2P, r * q * r⁻¹ ∈ co2P :=
    fun r hr q hq => co2P.mul_mem (co2P.mul_mem hr hq) (co2P.inv_mem hr)
  have hL0 : DownCompOK .Co2 5 (⟨co2FiveLine 0, hmem 0⟩ : ↥co2P) := by
    have hAP : co2FiveA ≤ co2P := fun a ha => (hC0 ▸ hAC ha : a ∈ _ ⊓ co2P).2
    exact downCompOK_of_pgroup_record Nat.prime_five le_rfl (hmem 0) hC0 hAC hAn hAP
      (IsPGroup.of_card (n := 3) (by rw [hAcard]; norm_num)) hAc
  have hL1 : DownCompOK .Co2 5 (⟨co2FiveLine 1, hmem 1⟩ : ↥co2P) := by
    have hD : co2FiveD = ⁅co2FiveC1, co2FiveC1⁆ := rfl
    have hDC : co2FiveD ≤ co2FiveC1 := by
      rw [hD, Subgroup.commutator_le]
      intro a ha c hc
      rw [commutatorElement_def]
      exact co2FiveC1.mul_mem (co2FiveC1.mul_mem (co2FiveC1.mul_mem ha hc)
        (co2FiveC1.inv_mem ha)) (co2FiveC1.inv_mem hc)
    have hDP : co2FiveD ≤ co2P := fun d hd => (hC1 ▸ hDC hd : d ∈ _ ⊓ co2P).2
    have hDfin : Finite ↥co2FiveD := Finite.of_injective (Subgroup.inclusion hDP)
      (Subgroup.inclusion_injective hDP)
    have hcore : GLAPPrimeCoreOf 5
        (Subgroup.centralizer ({co2FiveLine 1} : Set (Equiv.Perm (Fin 2300))) ⊓ co2P) = ⊥ := by
      rw [← hC1]
      exact gLAPPrimeCoreOf_eq_bot_of_record_derived Nat.prime_five hDs hDnab
        (by rw [← hD, hDcard]; norm_num)
        (IsPGroup.of_card (n := 1) (by rw [pow_one, ← hD]; exact hDcard5))
    exact downCompOK_of_derived_record (C := co2FiveC1) (D := co2FiveD) Nat.prime_five le_rfl
      (hmem 1) hC1 hD hDs hDnab hDP hDcent (hord 1) hcore (by rw [hDcard]; norm_num)
      (downTypeOK_of_chevP (by norm_num) (isChevSimple_five_of_A5
          (@CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty _ _
          hDfin hDs hDcard).some))
  have hline : ∀ j, DownCompOK .Co2 5 (⟨co2FiveLine j, hmem j⟩ : ↥co2P) := by
    intro j
    obtain ⟨hjP, hjconj⟩ := htrans j
    have hr : DownCompOK .Co2 5
        (⟨co2FiveLine (co2FiveRepLine (co2FiveRecordOf j)), hmem _⟩ : ↥co2P) := by
      by_cases h : (j : ℕ) = 0
      · rw [(hrec0 j).2 h]; exact hL0
      · have h1 : co2FiveRecordOf j = 1 := by
          simp only [co2FiveRecordOf, h, if_false]
        rw [h1]; exact hL1
    have h := downCompOK_conj Nat.prime_five hnorm hjP (hmem _) hr
    have heq : (⟨co2FiveTransporter j * co2FiveLine (co2FiveRepLine (co2FiveRecordOf j)) *
        (co2FiveTransporter j)⁻¹, hnorm _ hjP _ (hmem _)⟩ : ↥co2P) =
        ⟨co2FiveLine j, hmem j⟩ := Subtype.ext hjconj
    rw [heq] at h
    exact h
  have hrow := @sporDownRow_of_model' .Co2 5 Nat.prime_five ↥co2P _ hfin b
  exact hrow (downCompOK_of_lines Nat.prime_five hQP
      (card_eq_of_sylow_subgroupOf hQP hQsyl) co2FiveLine hlines hmem hline)

end RowCo2

section RowHe7

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.PartOne CFSG.Sporadic.HeldB

theorem sporDownRow_He_seven
    : SporDownRow .He 7 := by
  have hp7 : Nat.Prime 7 := by norm_num
  haveI : Fact (Nat.Prime 7) := ⟨hp7⟩
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlinesSet, -⟩, htrans, hrecmem, -, ⟨hC0, -⟩, ⟨hC1, -⟩, ⟨hC2, -⟩,
    ⟨hA0C, hA0n, hA0P, hA0card, -, -, hA0c⟩, ⟨hDs, hDnab, hDcard, hDP, hDcent, -⟩,
    ⟨hA2C, hA2n, hA2P, hA2card, -, hA2c⟩⟩ := R3E_He_full_seven_centralizer_structures
  have hM := heAutModel
  have e : CFSG.Blueprint.NativeSporadic.He ≃* ↥heP := heEquivP
  have hfin : Finite ↥heP := inferInstance
  have b : ↥heP ≃* (TauCeti.CFSGIndex.sporadic .He).Group :=
    e.symm.trans (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .He).some
  have hlines := lines_of_eq hlinesSet
  have hlineQ : ∀ j, Subgroup.zpowers (heSevenLine j) ≤ heSevenQ ∧
      Nat.card (Subgroup.zpowers (heSevenLine j)) = 7 := by
    intro j
    have h : Subgroup.zpowers (heSevenLine j) ∈
        {H : Subgroup (Equiv.Perm (Fin 8330)) | H ≤ heSevenQ ∧ Nat.card H = 7} := by
      rw [hlinesSet]; exact ⟨j, rfl⟩
    exact h
  have hmem : ∀ j, heSevenLine j ∈ heP :=
    fun j => hQP ((hlineQ j).1 (Subgroup.mem_zpowers _))
  have hord : ∀ j, orderOf (heSevenLine j) = 7 := fun j => by
    rw [← Nat.card_zpowers]; exact (hlineQ j).2
  have hL0 : DownCompOK .He 7 (⟨heSevenLine 0, hmem 0⟩ : ↥heP) :=
    downCompOK_of_pgroup_record hp7 hM.le (hmem 0) hC0 hA0C hA0n hA0P
      (IsPGroup.of_card (n := 3) (by rw [hA0card]; norm_num)) hA0c
  have hL2 : DownCompOK .He 7 (⟨heSevenLine 2, hmem 2⟩ : ↥heP) :=
    downCompOK_of_pgroup_record hp7 hM.le (hmem 2) hC2 hA2C hA2n hA2P
      (IsPGroup.of_card (n := 2) (by rw [hA2card]; norm_num)) hA2c
  have hL1 : DownCompOK .He 7 (⟨heSevenLine 1, hmem 1⟩ : ↥heP) := by
    have hDfin : Finite ↥heSevenD1 := Finite.of_injective (Subgroup.inclusion hDP)
      (Subgroup.inclusion_injective hDP)
    haveI := hDfin
    have hT : DownTypeOK .He 7 ↥heSevenD1 := downTypeOK_of_not_chev
      (not_isChevSimple_of_card_bound hDcard (by norm_num) (by norm_num)
        (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide))
    exact downCompOK_of_derived_record (C := heSevenC1) (D := heSevenD1) hp7 hM.le
      (hmem 1) hC1 rfl hDs hDnab hDP hDcent (hord 1)
      (gLAPPrimeCoreOf_inf_eq_bot_of_ambient hp7 hM.le hM.conj_mem
        (gLAPPrimeCoreOf_heSevenRecord_eq_bot 1 (Or.inr (Or.inl rfl))))
      (by rw [hDcard]; norm_num) hT
  have hline : ∀ j, DownCompOK .He 7 (⟨heSevenLine j, hmem j⟩ : ↥heP) := by
    intro j
    obtain ⟨hjR, hjconj⟩ := htrans j
    have hr : DownCompOK .He 7 (⟨heSevenLine (heSevenRecordOf j), hmem _⟩ : ↥heP) := by
      have h := hrecmem j
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h | h
      · have : heSevenRecordOf j = 0 := Fin.ext h
        rw [this]; exact hL0
      · have : heSevenRecordOf j = 1 := Fin.ext h
        rw [this]; exact hL1
      · have : heSevenRecordOf j = 2 := Fin.ext h
        rw [this]; exact hL2
    have h := downCompOK_conj hp7 hM.conj_mem hjR (hmem _) hr
    have heq : (⟨heSevenTransporter j * heSevenLine (heSevenRecordOf j) *
        (heSevenTransporter j)⁻¹, hM.conj_mem _ hjR _ (hmem _)⟩ : ↥heP) =
        ⟨heSevenLine j, hmem j⟩ := Subtype.ext hjconj
    rw [heq] at h
    exact h
  have hrow := @sporDownRow_of_model' .He 7 hp7 ↥heP _ hfin b
  exact hrow (downCompOK_of_lines hp7 hQP
      (card_eq_of_sylow_subgroupOf hQP hQsyl) heSevenLine hlines hmem hline)

end RowHe7

section RowSuz

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.Native CFSG.Sporadic.SuzOddCore

theorem sporDownRow_Suz_five
    : SporDownRow .Suz 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hQP, -, -, -, hQsyl⟩, ⟨hlinesSet, -⟩, hrec, hgood, hbad⟩ :=
    R3E_Suz_full_five_centralizer_structures
  have hR : ∀ r ∈ suzT, ∀ q ∈ suzM, r * q * r⁻¹ ∈ suzM := fun r hr q hq =>
    suzT_conj_mem_suzM hr hq
  have e : CFSG.Blueprint.NativeSporadic.Suz ≃* ↥suzM := suzEquivM
  have hfin : Finite ↥suzM := inferInstance
  have b : ↥suzM ≃* (TauCeti.CFSGIndex.sporadic .Suz).Group :=
    e.symm.trans (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Suz).some
  have hlines := lines_of_eq hlinesSet
  have hlineQ : ∀ i, Subgroup.zpowers (suzFiveLine i) ≤ suzFiveQ ∧
      Nat.card (Subgroup.zpowers (suzFiveLine i)) = 5 := by
    intro i
    have h : Subgroup.zpowers (suzFiveLine i) ∈
        {H : Subgroup (Equiv.Perm (Fin 1782)) | H ≤ suzFiveQ ∧ Nat.card H = 5} := by
      rw [hlinesSet]; exact ⟨i, rfl⟩
    exact h
  have hmem : ∀ i, suzFiveLine i ∈ suzM :=
    fun i => hQP ((hlineQ i).1 (Subgroup.mem_zpowers _))
  have hord : ∀ i, orderOf (suzFiveLine i) = 5 := fun i => by
    rw [← Nat.card_zpowers]; exact (hlineQ i).2
  have hline : ∀ i, DownCompOK .Suz 5 (⟨suzFiveLine i, hmem i⟩ : ↥suzM) := by
    intro i
    obtain ⟨hCeq, hDs, hDnab, hDM⟩ := hrec i
    have hD : (⁅suzFiveC i, suzFiveC i⁆ : Subgroup (Equiv.Perm (Fin 1782))) = suzFiveD i := rfl
    by_cases hg : i.val = 0 ∨ i.val = 3 ∨ i.val = 4
    · obtain ⟨-, hDcard, hcentEq, hcard5⟩ := hgood i hg
      have hDC : suzFiveD i ≤ suzFiveC i := hD ▸ commutator_self_le' _
      have hDn : ((suzFiveD i).subgroupOf (suzFiveC i)).Normal := by
        refine ⟨fun n hn g => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        have h := commutator_self_conj_mem g.2 (hD ▸ hn)
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact hD ▸ h
      have hcore : GLAPPrimeCoreOf 5
          (Subgroup.centralizer ({suzFiveLine i} : Set (Equiv.Perm (Fin 1782))) ⊓ suzT) = ⊥ := by
        rw [← hCeq]
        exact gLAPPrimeCoreOf_eq_bot_of_record_derived Nat.prime_five hDs hDnab
          (by rw [hD, hDcard]; norm_num)
          (IsPGroup.of_card (n := 1) (by rw [pow_one, hD, hcentEq]; exact hcard5))
      have hDfin : Finite ↥(suzFiveD i) := Finite.of_injective (Subgroup.inclusion hDM)
        (Subgroup.inclusion_injective hDM)
      exact downCompOK_of_normal_record Nat.prime_five suzM_le_suzT (hmem i) hCeq hDC hDn hDs hDnab
        hDM hcentEq (hord i)
        (gLAPPrimeCoreOf_inf_eq_bot_of_ambient Nat.prime_five suzM_le_suzT hR hcore)
        (by rw [hDcard]; norm_num) (downTypeOK_suz_five_of_card_360 hDcard)
    · have hb' : i.val = 1 ∨ i.val = 2 ∨ i.val = 5 := by
        have := i.2
        omega
      obtain ⟨hCcard, -, -⟩ := hbad i hb'
      refine downCompOK_five_of_card_dvd_3000 ?_
      have hmapc := CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype suzM
        (⟨suzFiveLine i, hmem i⟩ : ↥suzM)
      have hcc : Nat.card (Subgroup.centralizer ({(⟨suzFiveLine i, hmem i⟩ : ↥suzM)} : Set ↥suzM)) =
          Nat.card ↥(Subgroup.centralizer ({suzFiveLine i} : Set (Equiv.Perm (Fin 1782))) ⊓
            suzM) := by
        rw [← hmapc, Subgroup.card_map_of_injective suzM.subtype_injective]
      rw [hcc]
      have hle : Subgroup.centralizer ({suzFiveLine i} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM ≤
          suzFiveC i := by
        rw [hCeq]
        exact inf_le_inf_left _ suzM_le_suzT
      exact (Subgroup.card_dvd_of_le hle).trans (by rw [hCcard]; norm_num)
  have hrow := @sporDownRow_of_model' .Suz 5 Nat.prime_five ↥suzM _ hfin b
  exact hrow (downCompOK_of_lines Nat.prime_five hQP
      (card_eq_of_sylow_subgroupOf hQP hQsyl) suzFiveLine hlines hmem hline)

end RowSuz

section RowRu
open CFSG.RankThree.PartOne CFSG.Sporadic.RuSchreier in
theorem sporDownRow_Ru_five
    : SporDownRow .Ru 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlinesSet, -⟩, htrans, hrecmem, ⟨hrec0, hrec1⟩, ⟨hC0, hC0c⟩,
    ⟨hC1, hC1c⟩, ⟨hAC, hAn, -, hAcard, -, -, hAc⟩,
    ⟨hDs, ⟨g1, hg1, h1, hh1, hgh⟩, hDcard, hDP, hDcent, -⟩⟩ :=
    R3E_Ru_full_five_centralizer_structures
  have hc : Nat.card ↥ruP = 145926144000 := card_ruP'
  have hfin : Finite ↥ruP := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have e : CFSG.Blueprint.NativeSporadic.Ru ≃* ↥ruP := ruEquivP
  have b : ↥ruP ≃* (TauCeti.CFSGIndex.sporadic .Ru).Group :=
    e.symm.trans (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Ru).some
  have hlines := CFSG.HardMathSupport.Solomon.Coordinator.lines_of_eq hlinesSet
  have hmemQ : ∀ j, ruFiveLine j ∈ ruFiveQ := by
    intro j
    have h : Subgroup.zpowers (ruFiveLine j) ∈
        {H : Subgroup (Equiv.Perm (Fin 4060)) | H ≤ ruFiveQ ∧ Nat.card H = 5} := by
      rw [hlinesSet]; exact ⟨j, rfl⟩
    exact h.1 (Subgroup.mem_zpowers _)
  have hmem : ∀ j, ruFiveLine j ∈ ruP := fun j => hQP (hmemQ j)
  have hL0 : DownCompOK .Ru 5 (⟨ruFiveLine 0, hmem 0⟩ : ↥ruP) := by
    refine downCompOK_of_shapeRkAt (Good := fun _ _ => False) (Rk := fun _ _ => True) Nat.prime_five
      (Or.inl ?_) fun _ _ h => h.elim
    refine CFSG.HardMathSupport.Dickson.I271.pConstrainedShape_of_map_injective ruP.subtype
      ruP.subtype_injective ?_
    rw [CFSG.HardMathSupport.Dickson.I271.map_centralizer_subtype']
    show CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PConstrainedShape 5
      (Subgroup.centralizer {ruFiveLine 0} ⊓ ruP)
    rw [← hC0]
    exact CFSG.HardMathSupport.Dickson.I271.pConstrainedShape_of_normal_pgroup hAC hAn
      (IsPGroup.of_card (n := 3) (by rw [hAcard]; norm_num)) hAc
  have hL1 : DownCompOK .Ru 5 (⟨ruFiveLine 1, hmem 1⟩ : ↥ruP) := by
    have hDC : ruFiveD1 ≤ ruFiveC1 := by
      show ⁅ruFiveC1, ruFiveC1⁆ ≤ ruFiveC1
      rw [Subgroup.commutator_le]
      intro a ha c hc
      rw [commutatorElement_def]
      exact ruFiveC1.mul_mem (ruFiveC1.mul_mem (ruFiveC1.mul_mem ha hc) (ruFiveC1.inv_mem ha))
        (ruFiveC1.inv_mem hc)
    have hDfin : Finite ↥ruFiveD1 := Finite.of_injective (Subgroup.inclusion hDP)
      (Subgroup.inclusion_injective hDP)
    obtain ⟨fA⟩ :=
      @CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
        ↥ruFiveD1 _ hDfin hDs
      hDcard
    refine downCompOK_of_shapeRkAt (Good := fun T _ => DownTypeOK .Ru 5 T) (Rk := fun _ _ => True)
      Nat.prime_five ?_ fun _ _ h => h
    refine CFSG.HardMathSupport.Dickson.I271.shapeRkAt_of_subgroup_data (P := ruP)
      (L := ruFiveD1) Nat.prime_five
      (fun T T' _ _ e h => downTypeOK_of_mulEquiv e h)
      (fun _ _ _ _ _ h => h) ⟨ruFiveLine 1, hmem 1⟩ (hC1 ▸ hDC) ?_ hDs
      ⟨⟨g1, hg1⟩, ⟨h1, hh1⟩, fun h => hgh (congrArg Subtype.val h)⟩ (by rw [hDcard]; norm_num)
      (k := 1) ?_ ?_ trivial
    · intro g hg l hl
      rw [← hC1] at hg
      have h2 : ⁅g, l⁆ ∈ ruFiveD1 := Subgroup.commutator_mem_commutator hg (hDC hl)
      have h3 : g * l * g⁻¹ = ⁅g, l⁆ * l := by
        rw [commutatorElement_def]; group
      rw [h3]
      exact ruFiveD1.mul_mem h2 hl
    · show Nat.card ↥(Subgroup.centralizer {ruFiveLine 1} ⊓ ruP) = Nat.card ↥ruFiveD1 * 5 ^ 1
      rw [← hC1, hC1c, hDcard]; norm_num
    · exact downTypeOK_of_chevP (by norm_num) (isChevSimple_five_of_A5 fA)
  have hline : ∀ j, DownCompOK .Ru 5 (⟨ruFiveLine j, hmem j⟩ : ↥ruP) := by
    intro j
    obtain ⟨hjP, hjconj⟩ := htrans j
    have hr : DownCompOK .Ru 5 (⟨ruFiveLine (ruFiveRecordOf j), hmem _⟩ : ↥ruP) := by
      have h := hrecmem j
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · have : ruFiveRecordOf j = 0 := Fin.ext h
        rw [this]; exact hL0
      · have : ruFiveRecordOf j = 1 := Fin.ext h
        rw [this]; exact hL1
    have hk' : MulAut.conj (⟨ruFiveTransporter j, hjP⟩ : ↥ruP)
        (⟨ruFiveLine (ruFiveRecordOf j), hmem _⟩ : ↥ruP) = ⟨ruFiveLine j, hmem j⟩ := by
      apply Subtype.ext
      simp [MulAut.conj_apply, hjconj]
    rw [← hk']
    exact @downCompOK_of_mulEquiv .Ru 5 Nat.prime_five ↥ruP ↥ruP _ _ hfin _ _ hr
  have hrow := @sporDownRow_of_model' .Ru 5 Nat.prime_five ↥ruP _ hfin b
  exact hrow (downCompOK_of_lines Nat.prime_five hQP
      (CFSG.HardMathSupport.Solomon.Coordinator.card_eq_of_sylow_subgroupOf hQP hQsyl) ruFiveLine
      hlines hmem hline)

end RowRu

section RowHS
open CFSG.RankThree.Native CFSG.RankThree.PartOne in
theorem sporDownRow_HS_five
    : SporDownRow .HS 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlinesSet, -⟩, htrans, hrecmem, -, ⟨hC0, -⟩, ⟨hC2, -⟩,
    ⟨hC23, -⟩, ⟨hA0C, hA0n, hA0P, hA0card, -, -, hA0c⟩,
    ⟨hA23C, hA23n, hA23P, hA23card, -, -, hA23c⟩,
    ⟨hDs, hDnab, hDcard, hDP, hDcent, -⟩⟩ := R3E_HS_full_five_centralizer_structures
  have hM := hs_autModel
  have hfin : Finite ↥hs100P := inferInstance
  have e : CFSG.Blueprint.NativeSporadic.HS ≃* ↥hs100P := hs100Equiv
  have b : ↥hs100P ≃* (TauCeti.CFSGIndex.sporadic .HS).Group :=
    e.symm.trans (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .HS).some
  have hlines := CFSG.HardMathSupport.Solomon.Coordinator.lines_of_eq hlinesSet
  have hlineQ : ∀ j, Subgroup.zpowers (hs100FiveLine j) ≤ hs100FiveQ ∧
      Nat.card (Subgroup.zpowers (hs100FiveLine j)) = 5 := by
    intro j
    have h : Subgroup.zpowers (hs100FiveLine j) ∈
        {H : Subgroup (Equiv.Perm (Fin 100)) | H ≤ hs100FiveQ ∧ Nat.card H = 5} := by
      rw [hlinesSet]; exact ⟨j, rfl⟩
    exact h
  have hmem : ∀ j, hs100FiveLine j ∈ hs100P :=
    fun j => hQP ((hlineQ j).1 (Subgroup.mem_zpowers _))
  have hord : ∀ j, orderOf (hs100FiveLine j) = 5 := fun j => by
    rw [← Nat.card_zpowers]; exact (hlineQ j).2
  have hL0 : DownCompOK .HS 5 (⟨hs100FiveLine 0, hmem 0⟩ : ↥hs100P) :=
    downCompOK_of_pgroup_record Nat.prime_five hM.le (hmem 0) hC0 hA0C hA0n hA0P
      (IsPGroup.of_card (n := 2) (by rw [hA0card]; norm_num)) hA0c
  have hL23 : DownCompOK .HS 5 (⟨hs100FiveLine 23, hmem 23⟩ : ↥hs100P) :=
    downCompOK_of_pgroup_record Nat.prime_five hM.le (hmem 23) hC23 hA23C hA23n hA23P
      (IsPGroup.of_card (n := 3) (by rw [hA23card]; norm_num)) hA23c
  have hL2 : DownCompOK .HS 5 (⟨hs100FiveLine 2, hmem 2⟩ : ↥hs100P) := by
    have hDfin : Finite ↥hs100FiveD2 := Finite.of_injective (Subgroup.inclusion hDP)
      (Subgroup.inclusion_injective hDP)
    refine downCompOK_of_derived_record (C := hs100FiveC2) (D := hs100FiveD2) Nat.prime_five hM.le
      (hmem 2) hC2 rfl hDs hDnab hDP hDcent
      (hord 2) ?_ (by rw [hDcard]; norm_num)
        (downTypeOK_of_chevP (by norm_num) (isChevSimple_five_of_A5
          (@CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty _ _
          hDfin hDs hDcard).some))
    exact CFSG.HardMathSupport.Solomon.Coordinator.gLAPPrimeCoreOf_inf_eq_bot_of_ambient
      Nat.prime_five hM.le hM.conj_mem
      (CFSG.HardMathSupport.Solomon.Coordinator.gLAPPrimeCoreOf_hs100FiveRecord_eq_bot 2
        (Or.inr (Or.inl rfl)))
  have hline : ∀ j, DownCompOK .HS 5 (⟨hs100FiveLine j, hmem j⟩ : ↥hs100P) := by
    intro j
    obtain ⟨hjR, hjconj⟩ := htrans j
    have hr : DownCompOK .HS 5 (⟨hs100FiveLine (hs100FiveRecordOf j), hmem _⟩ : ↥hs100P) := by
      have h := hrecmem j
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h | h
      · have : hs100FiveRecordOf j = 0 := Fin.ext h
        rw [this]; exact hL0
      · have : hs100FiveRecordOf j = 2 := Fin.ext h
        rw [this]; exact hL2
      · have : hs100FiveRecordOf j = 23 := Fin.ext h
        rw [this]; exact hL23
    have h := downCompOK_conj Nat.prime_five hM.conj_mem hjR (hmem _) hr
    have heq : (⟨hs100FiveTransporter j * hs100FiveLine (hs100FiveRecordOf j) *
        (hs100FiveTransporter j)⁻¹, hM.conj_mem _ hjR _ (hmem _)⟩ : ↥hs100P) =
        ⟨hs100FiveLine j, hmem j⟩ := Subtype.ext hjconj
    rw [heq] at h
    exact h
  have hrow := @sporDownRow_of_model' .HS 5 Nat.prime_five ↥hs100P _ hfin b
  exact hrow (downCompOK_of_lines Nat.prime_five hQP
      (CFSG.HardMathSupport.Solomon.Coordinator.card_eq_of_sylow_subgroupOf hQP hQsyl)
      hs100FiveLine hlines hmem hline)

end RowHS


theorem inputSporDownChev_of_residual
    (h : SporDownResidual) : Claims1116b.InputSporDownChev := by
  obtain ⟨hM24_3, hJ2_3, hRu_3, hCo1_3, hB_3, hM_3, hFi23_5, hFi24_5, hB_5, hM_5, hCo1_7, hFi24_7,
    hB_7, hM_11, hM_13⟩ := h
  refine inputSporDownChev_of_rows fun s p hp hp2 hdvd => ?_
  have hdvd' : p ^ 2 ∣ Nat.card (TauCeti.CFSGIndex.sporadic s).Group := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds s]
    exact hdvd
  rcases CFSG.HardMathSupport.Solomon.Coordinator.sporadicP2Table_holds s p hp hp2 hdvd' with
    h1 | h1
  · rcases h1 with ⟨rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, rfl⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl
      exacts [sporDownRow_J3_three, sporDownRow_McL_three, sporDownRow_Suz_three,
        sporDownRow_ON_three, sporDownRow_Co3_three, sporDownRow_Co2_three, hCo1_3,
        sporDownRow_Fi22_three, sporDownRow_Fi23_three, sporDownRow_Fi24Prime_three,
        sporDownRow_HN_three, sporDownRow_Ly_three, sporDownRow_Th_three, hB_3, hM_3]
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl
      exacts [sporDownRow_Co1_five, sporDownRow_HN_five, sporDownRow_Ly_five, hB_5, hM_5]
    · exact sporDownRow_M_seven
  · rcases h1 with ⟨rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, rfl⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [sporDownRow_M11_three, sporDownRow_M12_three, sporDownRow_M22_three,
        sporDownRow_M23_three, hM24_3, hJ2_3, sporDownRow_J4_three, sporDownRow_HS_three, hRu_3,
        sporDownRow_He_three]
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [sporDownRow_J2_five, sporDownRow_HS_five, sporDownRow_McL_five, sporDownRow_Suz_five,
        sporDownRow_He_five, sporDownRow_Ru_five, sporDownRow_Co2_five, sporDownRow_Co3_five,
        sporDownRow_Fi22_five, hFi23_5, hFi24_5, sporDownRow_Th_five]
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [sporDownRow_He_seven, sporDownRow_ON_seven, hCo1_7, hFi24_7, sporDownRow_Th_seven,
        hB_7]
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      exacts [sporDownRow_J4_eleven, hM_11]
    · exact hM_13

end Main

end Rows

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1116c

end
