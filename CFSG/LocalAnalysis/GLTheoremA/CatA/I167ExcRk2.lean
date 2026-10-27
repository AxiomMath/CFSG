module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcPump
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcRankMain
import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CTrans
import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.I107GChev
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycSL
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellG2
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycOrth
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyEvenOrthogonal
import CFSG.RankThree.GF2n.Stroth80.GriessOrthSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem exists_elemAbelian_nine_of_isLnA {S : Type} [Group S] {n : ℕ} (hn : 5 ≤ n)
    (h : catalogIs S (isLnA n 2)) : ∃ E : Subgroup S, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie dl =>
    obtain ⟨d, hv⟩ := dl
    cases d with
    | A r q =>
      simp [isLnA, onLie, isLnEps, isAltN] at hi
      rcases hi with ⟨hrn, hq2⟩ | ⟨hn3, hr2, -⟩
      · have hr3 : 3 ≤ r := by omega
        have hmodel : CFSG.Models.LieModel S .PSL (r + 1) q.p q.exponent :=
          CFSG.Models.lieModel_A r q hv e
        have hclass : StatedClassicalModel S .PSL (r + 1) q.p q.exponent := by
          rcases hmodel.2 with hc | ⟨-, d', hnames, -⟩
          · exact hc
          · exfalso
            cases d' <;> simp [CFSG.Models.NamesTag] at hnames
        obtain ⟨-, K, hK, hKfin, hKcard, ⟨eModel⟩⟩ := hclass
        letI : Field K := hK
        letI : Finite K := hKfin
        have hK2 : Nat.card K = 2 := hKcard.trans hq2
        haveI : CharP K 2 :=
          CFSG.QuasithinUnique.Setup.Family.charP_two_of_card (f := 1) (by simpa using hK2)
        have ePSL : Matrix.ProjectiveSpecialLinearGroup (Fin (r + 1)) K ≃* S :=
          (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (r + 1) K).trans eModel.symm
        exact CFSG.AGLEmbedding.BlockCyc.hasE9_psl_of_three_le (m := r) hr3 (F := K) ePSL
      · omega
    | _ =>
      exfalso
      simp [isLnA, onLie, isLnEps, isAltN] at hi
      try omega
  | cyclic _ _ =>
    exfalso
    simp [isLnA, onLie, isLnEps, isAltN] at hi
  | alternating _ _ =>
    exfalso
    simp [isLnA, onLie, isLnEps, isAltN] at hi
    omega
  | sporadic _ =>
    exfalso
    simp [isLnA, onLie, isLnEps, isAltN] at hi

theorem exists_elemAbelian_nine_of_isOmMA {S : Type} [Group S] {n : ℕ} (hn : 6 ≤ n)
    (h : catalogIs S (isOmMA n 2)) : ∃ E : Subgroup S, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie dl =>
    obtain ⟨d, hv⟩ := dl
    cases d with
    | twistedD rank q =>
      simp [isOmMA, isOmM, onLie, isLnEps] at hi
      obtain ⟨hrn, hq2⟩ := hi
      have hmodel : CFSG.Models.LieModel S .POmegaMinus rank q.p q.exponent :=
        CFSG.Models.lieModel_twistedD rank q hv e
      have hclass : StatedClassicalModel S .POmegaMinus rank q.p q.exponent := by
        rcases hmodel.2 with hc | ⟨-, d', hnames, -⟩
        · exact hc
        · exfalso
          cases d' <;> simp [CFSG.Models.NamesTag] at hnames
      have hqp : q.p = 2 := by
        have hdvd : q.p ∣ 2 := by
          rw [← hq2]
          exact dvd_pow_self q.p q.exponent_pos.ne'
        exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 hdvd
      have hqe : q.exponent = 1 := by
        have h := hq2
        rw [hqp] at h
        exact Nat.pow_right_injective (a := 2) (by norm_num) (by simpa using h)
      have hclass' : StatedClassicalModel S .POmegaMinus rank 2 1 := by
        simpa [hqp, hqe] using hclass
      exact CFSG.AGLEmbedding.BlockCyc.hasE9_of_model_pomegaMinus hclass'
    | twistedA rank q =>
      exfalso
      simp [isOmMA, isOmM, onLie, isLnEps] at hi
      omega
    | _ =>
      exfalso
      simp [isOmMA, isOmM, onLie, isLnEps] at hi
  | cyclic _ _ =>
    exfalso
    simp [isOmMA, isOmM, onLie, isLnEps] at hi
  | alternating _ _ =>
    exfalso
    simp [isOmMA, isOmM, onLie, isLnEps] at hi
  | sporadic _ =>
    exfalso
    simp [isOmMA, isOmM, onLie, isLnEps] at hi

private theorem exists_elemAbelian_sq_of_isOmPA_aux1 {q : TauCeti.PrimePower} {k : ℕ}
    (h : q.p ^ q.exponent = 2 ^ k) : q.p = 2 ∧ q.exponent = k := by
  have hp2 : q.p = 2 := by
    have hdvd : q.p ∣ 2 ^ k := by
      rw [← h]
      exact dvd_pow_self q.p q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow hdvd)
  have hexp : q.exponent = k := by
    rw [hp2] at h
    exact Nat.pow_right_injective (a := 2) (by norm_num) h
  exact ⟨hp2, hexp⟩

private theorem exists_elemAbelian_sq_of_isOmPA_aux2 {S : Type} [Group S] {p k r : ℕ}
    {q : TauCeti.PrimePower} (hp : p.Prime) (hpk : p ∣ 2 ^ k + 1)
    (hv : (TauCeti.LieTypeIndex.D r q).Valid) (hr3 : 3 ≤ r)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.D r q, hv⟩).Group)
    (hq2k : q.p ^ q.exponent = 2 ^ k) :
    ∃ E : Subgroup S, IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  obtain ⟨hqp, hqk⟩ := exists_elemAbelian_sq_of_isOmPA_aux1 hq2k
  have hmodel : CFSG.Models.LieModel S .POmegaPlus r q.p q.exponent :=
    CFSG.Models.lieModel_D r q hv e
  have hclass : StatedClassicalModel S .POmegaPlus r q.p q.exponent := by
    rcases hmodel.2 with hc | ⟨-, d', hnames, -⟩
    · exact hc
    · exfalso
      cases d' <;> simp [CFSG.Models.NamesTag] at hnames
  obtain ⟨-, K, hK, hKfin, hKcard, ⟨eModel⟩⟩ := hclass
  letI : Field K := hK
  letI : Finite K := hKfin
  have hKcard' : Nat.card K = 2 ^ k := by rw [hKcard, hqp, hqk]
  have hpk' : p ∣ Nat.card K + 1 := by rw [hKcard']; exact hpk
  obtain ⟨-, E, hE, hEcard⟩ :=
    CFSG.QuasithinUnique.Setup.Family.even_orthogonal_plus (f := k) hKcard' hp
      hpk' (n := r) (by omega)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CFSG.IsElementaryAbelian p ↥E := hE
  have hdvd : p ^ 2 ∣ Nat.card E := by
    rw [hEcard]
    exact pow_dvd_pow p (Nat.mul_le_mul_left 2 (Nat.div_pos (by omega) (by norm_num)))
  obtain ⟨E', -, hE'el, hE'card⟩ :=
    CFSG.RankThree.PartOne.CTP.exists_elementaryAbelian_sq_le (p := p) (A := E) hdvd
  have hE'ab : IsElemAbelian p E' := CFSG.Open.isElemAbelian_of_isElementaryAbelian
  refine ⟨E'.map eModel.symm.toMonoidHom, CFSG.Open.IsElemAbelian.map hE'ab _, ?_⟩
  rw [Subgroup.card_map_of_injective eModel.symm.injective, hE'card]

private theorem exists_elemAbelian_sq_of_isOmPA_aux3 {S : Type} [Group S] {p k : ℕ}
    {K : Type} [Field K] [Finite K] (hp : p.Prime) (hpk : p ∣ 2 ^ k + 1)
    (hk1 : k = 1) (hKcard : Nat.card K = 2 ^ k)
    (eModel : S ≃* StatedProj (StatedSL 4 K)) :
    ∃ E : Subgroup S, IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  have hp3 : p = 3 := by
    have h3 : p ∣ 3 := by simpa [hk1] using hpk
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
  have hK2 : Nat.card K = 2 := by simpa [hk1] using hKcard
  haveI : CharP K 2 :=
    CFSG.QuasithinUnique.Setup.Family.charP_two_of_card (f := 1) hK2
  have ePSL : Matrix.ProjectiveSpecialLinearGroup (Fin 4) K ≃* S :=
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 K).trans eModel.symm
  have h9 := CFSG.AGLEmbedding.BlockCyc.hasE9_psl_of_three_le (m := 3) (by norm_num) (F := K) ePSL
  simpa [hp3, CFSG.AGLEmbedding.BlockCyc.HasE9] using h9

private theorem exists_elemAbelian_sq_of_isOmPA_aux4 {S : Type} [Group S] {p k : ℕ}
    {K : Type} [Field K] [Finite K] (hp : p.Prime) (hpk : p ∣ 2 ^ k + 1)
    (hk : 1 ≤ k) (hk1 : k ≠ 1) (hKcard : Nat.card K = 2 ^ k)
    (eModel : S ≃* StatedProj (StatedSL 4 K)) :
    ∃ E : Subgroup S, IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  have hk2 : 2 ≤ k := by omega
  haveI : CharP K 2 :=
    CFSG.QuasithinUnique.Setup.Family.charP_two_of_card (f := k) hKcard
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  have hpk' : p ∣ Nat.card K + 1 := by rw [hKcard]; exact hpk
  obtain ⟨hC, E, hE, hEcard⟩ :=
    CFSG.QuasithinUnique.Setup.Family.even_orthogonal_plus (f := k) hKcard hp
      hpk' (n := 3) (by norm_num)
  have hEcard' : Nat.card E = p ^ 2 := by simpa using hEcard
  have hΩbot : (StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf
      (StatedOmega (StatedQuadPlus 3 K)) = ⊥ := by
    rw [Subgroup.subgroupOf_eq_bot, disjoint_iff]
    simpa [inf_comm] using hC
  have hSLbot : (StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K) = ⊥ := by
    rw [← CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars 4 K,
      ← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center,
      CFSG.LocalAnalysis.ComponentInitial.LinearCover.scalars_four_eq_bot,
      Subgroup.map_bot]
  let eΩ : StatedProj (StatedOmega (StatedQuadPlus 3 K)) ≃* StatedSL 4 K :=
    ((QuotientGroup.quotientMulEquivOfEq hΩbot).trans QuotientGroup.quotientBot).trans
      (CFSG.RankThree.GF2n.Stroth80.nonempty_statedOmega_quadPlus_three_mulEquiv hK4).some
  let eSL : StatedSL 4 K ≃* StatedProj (StatedSL 4 K) :=
    ((QuotientGroup.quotientMulEquivOfEq hSLbot).trans QuotientGroup.quotientBot).symm
  have eAll : StatedProj (StatedOmega (StatedQuadPlus 3 K)) ≃* S :=
    (eΩ.trans eSL).trans eModel.symm
  have hEab : IsElemAbelian p E := CFSG.Open.isElemAbelian_of_isElementaryAbelian
  refine ⟨E.map eAll.toMonoidHom, CFSG.Open.IsElemAbelian.map hEab _, ?_⟩
  rw [Subgroup.card_map_of_injective eAll.injective, hEcard']

private theorem exists_elemAbelian_sq_of_isOmPA_aux5 {S : Type} [Group S] {p k rank : ℕ}
    {q : TauCeti.PrimePower} (hp : p.Prime) (hpk : p ∣ 2 ^ k + 1) (hk : 1 ≤ k)
    (hv : (TauCeti.LieTypeIndex.A rank q).Valid)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.A rank q, hv⟩).Group)
    (hrn : rank + 1 = 4) (hq2k : q.p ^ q.exponent = 2 ^ k) :
    ∃ E : Subgroup S, IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  obtain ⟨hqp, hqk⟩ := exists_elemAbelian_sq_of_isOmPA_aux1 hq2k
  have hrank3 : rank = 3 := by omega
  subst rank
  have hmodel : CFSG.Models.LieModel S .PSL 4 q.p q.exponent :=
    CFSG.Models.lieModel_A 3 q hv e
  have hclass : StatedClassicalModel S .PSL 4 q.p q.exponent := by
    rcases hmodel.2 with hc | ⟨-, d', hnames, -⟩
    · exact hc
    · exfalso
      cases d' <;> simp [CFSG.Models.NamesTag] at hnames
  obtain ⟨-, K, hK, hKfin, hKcard, ⟨eModel⟩⟩ := hclass
  letI : Field K := hK
  letI : Finite K := hKfin
  have hKcard' : Nat.card K = 2 ^ k := by rw [hKcard, hqp, hqk]
  by_cases hk1 : k = 1
  · exact exists_elemAbelian_sq_of_isOmPA_aux3 hp hpk hk1 hKcard' eModel
  · exact exists_elemAbelian_sq_of_isOmPA_aux4 hp hpk hk hk1 hKcard' eModel

private theorem exists_elemAbelian_sq_of_isOmPA_aux6 {S : Type} [Group S] {p k degree : ℕ}
    {hdeg : 5 ≤ degree} (hp : p.Prime) (hpk : p ∣ 2 ^ k + 1)
    (e : S ≃* (TauCeti.CFSGIndex.alternating degree hdeg).Group)
    (h2k : 2 ^ k = 2) (hdeg8 : degree = 8) :
    ∃ E : Subgroup S, IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  have hp3 : p = 3 := by
    have h3 : p ∣ 3 := by
      rw [h2k] at hpk
      simpa using hpk
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
  have hE9 : CFSG.AGLEmbedding.BlockCyc.HasE9 S :=
    CFSG.AGLEmbedding.BlockCyc.hasE9_of_mulEquiv e.symm
      (CFSG.AGLEmbedding.BlockCyc.hasE9_alternatingGroup
        (N := degree) (by omega : 6 ≤ degree))
  simpa [hp3, CFSG.AGLEmbedding.BlockCyc.HasE9] using hE9

theorem exists_elemAbelian_sq_of_isOmPA {S : Type} [Group S] {p n k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 3 ≤ n) (hk : 1 ≤ k) (hpk : p ∣ 2 ^ k + 1) (h : catalogIs S (isOmPA n (2 ^ k))) :
    ∃ E : Subgroup S, IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie dl =>
    obtain ⟨d, hv⟩ := dl
    cases d with
    | D r q =>
      simp [isOmPA, isOmP, onLie, isLnEps, isAltN] at hi
      rcases hi with ⟨hrn, hq2k⟩ | hbad
      · exact exists_elemAbelian_sq_of_isOmPA_aux2 hp hpk hv (by omega) e hq2k
      · exfalso
        rcases hbad with ⟨-, hln⟩
        simp [isLnA, onLie, isLnEps, isAltN] at hln
    | A rank q =>
      simp [isOmPA, isOmP, onLie, isLnEps, isAltN] at hi
      obtain ⟨hn3, hln⟩ := hi
      simp [isLnA, onLie, isLnEps, isAltN] at hln
      obtain ⟨hrn, hq2k⟩ := hln
      exact exists_elemAbelian_sq_of_isOmPA_aux5 hp hpk hk hv e (by omega) hq2k
    | _ =>
      exfalso
      rcases hi with hP | ⟨-, hln⟩
      · unfold isOmP at hP
        simp [onLie] at hP
      · simp [isLnA, onLie, isLnEps, isAltN] at hln
  | cyclic _ _ =>
    exfalso
    rcases hi with hP | ⟨-, hln⟩
    · unfold isOmP at hP
      simp [onLie] at hP
    · simp [isLnA, onLie, isLnEps, isAltN] at hln
  | alternating _ _ =>
    rcases hi with hP | ⟨hn3, hln⟩
    · exfalso
      unfold isOmP at hP
      simp [onLie] at hP
    · simp [isLnA, onLie, isLnEps, isAltN] at hln
      exact exists_elemAbelian_sq_of_isOmPA_aux6 hp hpk e hln.1 hln.2
  | sporadic _ =>
    exfalso
    rcases hi with hP | ⟨-, hln⟩
    · unfold isOmP at hP
      simp [onLie] at hP
    · simp [isLnA, onLie, isLnEps, isAltN] at hln

theorem exists_elemAbelian_sq_of_type167J {p : ℕ} {J : Subgroup Ω} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : Type167J p J) : ∃ E : Subgroup (PSimple p J), IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  rcases h with ⟨rfl, n, -, hn, hJ⟩ | ⟨rfl, n, -, hn, hJ⟩ | ⟨n, k, -, hn, -, hk, hpk, hJ⟩
  · exact exists_elemAbelian_nine_of_isLnA hn hJ
  · exact exists_elemAbelian_nine_of_isOmMA hn hJ
  · exact exists_elemAbelian_sq_of_isOmPA hp hp2 hn hk hpk hJ

section Certs


private theorem card_elemAbelian_le_sq_of_rk2_aux1 {S : Type} [Group S] [Finite S] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {d : TauCeti.LieTypeIndex} {hv : d.Valid}
    (hi : ExcRk2Idx (.lie ⟨d, hv⟩))
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨d, hv⟩).Group)
    (hp5 : 5 ≤ p) {F : Subgroup S} (hF : IsElemAbelian p F) : Nat.card F ≤ p ^ 2 := by
  cases d with
  | G2 q =>
    have hq : q.p = 2 := by
      simpa [ExcRk2Idx, onLie] using (hi : ExcRk2Idx (.lie ⟨.G2 q, hv⟩))
    exact CFSG.LieType.SeitzGeneration.RankLE2.of_mulEquiv e.symm
      (CFSG.HardMathSupport.Curtis.Coordinator.rankLE2_cat_G2 q hv hq hp hp2) F hF
  | trialityD4 q =>
    have hq : q.p = 2 := by
      simpa [ExcRk2Idx, onLie] using (hi : ExcRk2Idx (.lie ⟨.trialityD4 q, hv⟩))
    exact CFSG.LieType.SeitzGeneration.RankLE2.of_mulEquiv e.symm
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_cat_trialityD4 q hv hp hp5
        (by rw [hq]; exact hp2)) F hF
  | reeF4 m =>
    exact CFSG.LieType.SeitzGeneration.RankLE2.of_mulEquiv e.symm
      (CFSG.LieType.SeitzGeneration.rankLE2_cat_reeF4_five hv hp hp5) F hF
  | _ =>
    exfalso
    simp [ExcRk2Idx, onLie] at hi

theorem card_elemAbelian_le_sq_of_rk2 {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : catalogIs S ExcRk2Idx) {F : Subgroup S} (hF : IsElemAbelian p F) : Nat.card F ≤ p ^ 2 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie dl =>
    obtain ⟨d, hv⟩ := dl
    have hd : CFSG.HardMathSupport.Dickson.Sec6.FamG2 d ∨
        CFSG.HardMathSupport.Dickson.Sec6.FamTriD4 d ∨
        CFSG.HardMathSupport.Dickson.Sec6.FamReeF4 d := by
      cases d with
      | G2 q => exact Or.inl trivial
      | trialityD4 q => exact Or.inr (Or.inl trivial)
      | reeF4 m => exact Or.inr (Or.inr trivial)
      | _ => exact hi.elim
    have hchar : d.characteristic = 2 := by
      cases d with
      | G2 q => simpa [ExcRk2Idx, onLie] using (hi : ExcRk2Idx (.lie ⟨.G2 q, hv⟩))
      | trialityD4 q => simpa [ExcRk2Idx, onLie] using (hi : ExcRk2Idx (.lie ⟨.trialityD4 q, hv⟩))
      | reeF4 m => simp
      | _ => exact hi.elim
    have hct : CFSG.HardMathSupport.Solomon.Coordinator.IsCharTwoLieIndex d := by
      cases d with
      | G2 q => simpa [ExcRk2Idx, onLie, CFSG.HardMathSupport.Solomon.Coordinator.IsCharTwoLieIndex]
          using (hi : ExcRk2Idx (.lie ⟨.G2 q, hv⟩))
      | trialityD4 q => simpa [ExcRk2Idx, onLie, CFSG.HardMathSupport.Solomon.Coordinator.IsCharTwoLieIndex]
          using (hi : ExcRk2Idx (.lie ⟨.trialityD4 q, hv⟩))
      | reeF4 m => trivial
      | _ => exact hi.elim
    have hp35 : p = 3 ∨ 5 ≤ p := by
      have h2 : 2 ≤ p := hp.two_le
      have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
      omega
    rcases hp35 with rfl | hp5
    · exact (CFSG.LocalAnalysis.GLTheoremA.K1419E.l3u3Rank_exc ⟨d, hv⟩ hd hct e).2 F hF
    · exact card_elemAbelian_le_sq_of_rk2_aux1 hp hp2 hi e hp5 hF
  | cyclic _ _ =>
    exfalso
    simp [ExcRk2Idx, onLie] at hi
  | alternating _ _ =>
    exfalso
    simp [ExcRk2Idx, onLie] at hi
  | sporadic _ =>
    exfalso
    simp [ExcRk2Idx, onLie] at hi

private theorem inducesInnerMod_of_rk2_aux2 {S : Type} [Group S] {p : ℕ}
    (h : catalogIs S ExcRk2Idx) : IsChevSimple 2 S := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie dl =>
    obtain ⟨d, hv⟩ := dl
    cases d with
    | G2 q =>
      have hq : q.p = 2 := by
        simpa [ExcRk2Idx, onLie] using (hi : ExcRk2Idx (.lie ⟨.G2 q, hv⟩))
      exact Or.inl ⟨.lie ⟨.G2 q, hv⟩,
        by simpa [onLie, TauCeti.LieTypeIndex.characteristic_G2] using hq, ⟨e⟩⟩
    | trialityD4 q =>
      have hq : q.p = 2 := by
        simpa [ExcRk2Idx, onLie] using (hi : ExcRk2Idx (.lie ⟨.trialityD4 q, hv⟩))
      exact Or.inl ⟨.lie ⟨.trialityD4 q, hv⟩,
        by simpa [onLie, TauCeti.LieTypeIndex.characteristic_trialityD4] using hq, ⟨e⟩⟩
    | reeF4 m =>
      exact Or.inl ⟨.lie ⟨.reeF4 m, hv⟩,
        by simpa [onLie] using TauCeti.LieTypeIndex.characteristic_reeF4 m, ⟨e⟩⟩
    | _ =>
      exfalso
      simp [ExcRk2Idx, onLie] at hi
  | cyclic _ _ =>
    exfalso
    simp [ExcRk2Idx, onLie] at hi
  | alternating _ _ =>
    exfalso
    simp [ExcRk2Idx, onLie] at hi
  | sporadic _ =>
    exfalso
    simp [ExcRk2Idx, onLie] at hi

private theorem inducesInnerMod_of_rk2_aux3 {d : TauCeti.LieTypeIndex} {hv : d.Valid}
    (hi : ExcRk2Idx (.lie ⟨d, hv⟩)) :
    CFSG.LocalAnalysis.GLTheoremA.K1419E.ExcIdx d ∧
      (CFSG.HardMathSupport.Dickson.Sec6.FamG2 d ∨
        CFSG.HardMathSupport.Dickson.Sec6.FamTriD4 d ∨
        CFSG.HardMathSupport.Dickson.Sec6.FamReeF4 d) := by
  have hfam : CFSG.HardMathSupport.Dickson.Sec6.FamG2 d ∨
      CFSG.HardMathSupport.Dickson.Sec6.FamTriD4 d ∨
      CFSG.HardMathSupport.Dickson.Sec6.FamReeF4 d := by
    cases d with
    | G2 q => exact Or.inl trivial
    | trialityD4 q => exact Or.inr (Or.inl trivial)
    | reeF4 m => exact Or.inr (Or.inr trivial)
    | _ =>
      exfalso
      simp [ExcRk2Idx, onLie] at hi
  have hd : CFSG.LocalAnalysis.GLTheoremA.K1419E.ExcIdx d := by
    cases d with
    | G2 q => exact Or.inl trivial
    | trialityD4 q => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl trivial))))))
    | reeF4 m => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr trivial))))))
    | _ =>
      exfalso
      simp [ExcRk2Idx, onLie] at hi
  exact ⟨hd, hfam⟩

private theorem inducesInnerMod_of_rk2_aux4 {d : TauCeti.LieTypeIndex} {hv : d.Valid}
    (hi : ExcRk2Idx (.lie ⟨d, hv⟩)) :
    CFSG.HardMathSupport.Solomon.Coordinator.IsCharTwoLieIndex d ∧
      d.characteristic = 2 := by
  have hchar : d.characteristic = 2 := by
    cases d with
    | G2 q =>
      have hq : q.p = 2 := by
        simpa [ExcRk2Idx, onLie] using (hi : ExcRk2Idx (.lie ⟨.G2 q, hv⟩))
      simpa [TauCeti.LieTypeIndex.characteristic_G2] using hq
    | trialityD4 q =>
      have hq : q.p = 2 := by
        simpa [ExcRk2Idx, onLie] using (hi : ExcRk2Idx (.lie ⟨.trialityD4 q, hv⟩))
      simpa [TauCeti.LieTypeIndex.characteristic_trialityD4] using hq
    | reeF4 m => exact TauCeti.LieTypeIndex.characteristic_reeF4 m
    | _ =>
      exfalso
      simp [ExcRk2Idx, onLie] at hi
  have hct : CFSG.HardMathSupport.Solomon.Coordinator.IsCharTwoLieIndex d := by
    cases d with
    | G2 q => simpa [ExcRk2Idx, onLie, CFSG.HardMathSupport.Solomon.Coordinator.IsCharTwoLieIndex]
        using (hi : ExcRk2Idx (.lie ⟨.G2 q, hv⟩))
    | trialityD4 q => simpa [ExcRk2Idx, onLie,
        CFSG.HardMathSupport.Solomon.Coordinator.IsCharTwoLieIndex]
        using (hi : ExcRk2Idx (.lie ⟨.trialityD4 q, hv⟩))
    | reeF4 m => trivial
    | _ =>
      exfalso
      simp [ExcRk2Idx, onLie] at hi
  exact ⟨hct, hchar⟩

theorem inducesInnerMod_of_rk2 {p : ℕ} {X : Subgroup Ω} {x : Ω} (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : CFSG.Open.IsQuasisimple ↥X) (h : catalogIs (PSimple p X) ExcRk2Idx)
    (hinn : InnDiagOn p (Subgroup.zpowers x) X) : InducesInnerMod p X x := by
  have hcat : catalogIs (PSimple p X) ExcRk2Idx := h
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie dl =>
    obtain ⟨d, hv⟩ := dl
    obtain ⟨hd, hfam⟩ := inducesInnerMod_of_rk2_aux3 hi
    obtain ⟨hct, hchar⟩ := inducesInnerMod_of_rk2_aux4 hi
    haveI : Nontrivial (TauCeti.CFSGIndex.lie ⟨d, hv⟩).Group :=
      (CFSG.Assembly.lie_finite_simple ⟨d, hv⟩).2.toNontrivial
    have hnt : Nontrivial (PSimple p X) := e.symm.injective.nontrivial
    have hXq : CFSG.Open.IsQuasisimple (PQuot p X) :=
      CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp
        (glaPComponent_self_of_nontrivial hX hnt)
    obtain ⟨labL, -, hkind⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.I141F.innDiagKind_chevAut
        (hinn.1 (Subgroup.mem_zpowers x)) hXq hinn
    have hsimple : IsSimpleGroup (PSimple p X) :=
      e.isSimpleGroup_congr.mpr (CFSG.Assembly.lie_finite_simple ⟨d, hv⟩).2
    have hnab : ∃ a b : PSimple p X, a * b ≠ b * a :=
      CFSG.LocalAnalysis.GLTheoremA.chevTwoNonabelian_holds (S := PSimple p X) hsimple
        (inducesInnerMod_of_rk2_aux2 (p := p) hcat)
    have hβ : chevAut p X ⟨x, hinn.1 (Subgroup.mem_zpowers x)⟩ ∈
        CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived (PSimple p X) :=
      CFSG.LocalAnalysis.GLTheoremA.K1419E.mem_innAutDerived_of_exc hsimple hnab
        (d := ⟨d, hv⟩) hd hchar e hkind
    have hinner : chevAut p X ⟨x, hinn.1 (Subgroup.mem_zpowers x)⟩ ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p X) :=
      (CFSG.LocalAnalysis.GLTheoremA.K1419E.l3u3Rank_exc ⟨d, hv⟩ hfam hct e).1 hβ
    exact (chevAut_mem_inner_iff hp (glaPComponent_self_of_nontrivial hX hnt)
      (hinn.1 (Subgroup.mem_zpowers x))).1 hinner
  | cyclic _ _ =>
    exfalso
    simp [ExcRk2Idx, onLie] at hi
  | alternating _ _ =>
    exfalso
    simp [ExcRk2Idx, onLie] at hi
  | sporadic _ =>
    exfalso
    simp [ExcRk2Idx, onLie] at hi


theorem false_of_exc_rk2 {p : ℕ} {B X D J : Subgroup Ω} {x : Ω} (H : ExcHyp p B X D J x)
    (hr : catalogIs (PSimple p X) ExcRk2Idx) : False := by
  have hZ := center_pQuot_eq_bot_of_type167J H.hp H.hp2 H.hJ H.htype
  haveI : Nontrivial (PSimple p X) := nontrivial_pSimple_of_innDiagOn H.hinn
  obtain ⟨s, hs1, hsp, hsc⟩ := exists_fixed_element H.hp H.hX inferInstance H.hJX H.hxN H.hxp H.hxX H.hxJ
    (inducesInnerMod_of_rk2 H.hp H.hp2 H.hX hr H.hinn)
  obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_sq_of_type167J H.hp H.hp2 H.htype
  obtain ⟨F, hF, hFc⟩ := exists_elemAbelian_pumpup H.hp H.hJX hZ hs1 hsp hsc hE
  have h2 := card_elemAbelian_le_sq_of_rk2 H.hp H.hp2 hr hF
  rw [hFc, hEc] at h2
  have hp0 : 0 < p ^ 2 := pow_pos H.hp.pos 2
  have hp2' := H.hp.two_le
  nlinarith

end Certs

end CFSG.LocalAnalysis.GLTheoremA.I167

end
