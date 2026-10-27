module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcPump
public import CFSG.Assembly.E6FourCentHolds
public import CFSG.Assembly.E6FourFieldRigid
public import CFSG.LocalAnalysis.GLTheoremA.CatA.CentQ
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnExc
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPRed
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172V2
import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
import CFSG.LocalAnalysis.GLTheoremA.CatA.LieOrderGrid
import CFSG.LocalAnalysis.StandardType.GGExclNoIso
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreSix
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF1

import CFSG.Assembly.E6FourNeighbourAut
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZComm
import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma83
import CFSG.HardMathSupport.Solomon.Coordinator.L5Conj
import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcFieldGen
import CFSG.LieType.SeitzGeneration.HeisTorusU87Arith
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09I133Small
import CFSG.Sporadic.Co2Smith.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly
open scoped Pointwise

variable {Ω : Type} [Group Ω] [Finite Ω]

@[expose] def ExcE6SubIdx : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedD r q => r = 4 ∧ q.card = 4 | .A r q => r = 5 ∧ q.card = 4 | _ => False

theorem type167J_case_c_of_ne_three {p : ℕ} {J : Subgroup Ω} (h : Type167J p J) (hp3 : p ≠ 3) :
    ∃ n k : ℕ, Odd n ∧ 3 ≤ n ∧ 1 ≤ k ∧ p ∣ 2 ^ k + 1 ∧ catalogIs (PSimple p J) (isOmPA n (2 ^ k)) := by
  rcases h with ⟨h3, -⟩ | ⟨h3, -⟩ | ⟨n, k, hn, hn3, -, hk, hpk, hJ⟩
  · exact absurd h3 hp3
  · exact absurd h3 hp3
  · exact ⟨n, k, hn, hn3, hk, hpk, hJ⟩

section Certs

private theorem e6_fieldRel_aux2 {p n k : ℕ} {S : Type} [Group S]
    (h : catalogIs S (isOmP n (2 ^ k))) :
    CFSG.Blueprint.LieModel S .POmegaPlus n 2 k := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic c hc => exact absurd hi (by simp [isOmP, onLie])
  | alternating a ha => exact absurd hi (by simp [isOmP, onLie])
  | sporadic s => exact absurd hi (by simp [isOmP, onLie])
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | D r q =>
      simp only [isOmP, onLie] at hi
      obtain ⟨hr, hqc⟩ := hi
      have hpow : q.p ^ q.exponent = 2 ^ k := by
        rw [← TauCeti.PrimePower.card_def, hqc]
      have hkpos : k ≠ 0 := by
        intro hk
        subst hk
        rw [pow_zero] at hpow
        exact (Nat.one_lt_pow q.exponent_pos.ne' q.prime_p.one_lt).ne' hpow
      obtain ⟨hq2, hqe⟩ := Nat.Prime.pow_inj' q.prime_p Nat.prime_two
        (Nat.ne_of_gt q.exponent_pos) hkpos hpow
      have hm := CFSG.Models.lieModel_D r q hv e
      rw [hr, hq2, hqe] at hm
      exact CFSG.Models.LieModel.toBlueprint (by simp [CFSG.Blueprint.classicalTags]) hm
    | _ => exact absurd hi (by simp [isOmP, onLie])

private theorem e6_fieldRel_aux5 {p k : ℕ} {S : Type} [Group S]
    (h : catalogIs S (isLnA 4 (2 ^ k))) :
    CFSG.Blueprint.LieModel S .PSL 4 2 k := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic c hc => exact absurd hi (by simp [isLnA, isLnEps, onLie, isAltN])
  | sporadic s => exact absurd hi (by simp [isLnA, isLnEps, onLie, isAltN])
  | alternating a ha =>
    rw [isLnA] at hi
    rcases hi with h2a | h2b | h2c | h2d | h2e
    · exact absurd h2a (by simp [onLie])
    · exact absurd h2b.1 (by omega)
    · exact absurd h2c.1 (by omega)
    · exact absurd h2d.1 (by omega)
    · obtain ⟨-, hq2', h8⟩ := h2e
      have hk : k = 1 := by
        rw [← pow_one 2] at hq2'
        exact Nat.pow_right_injective le_rfl hq2'
      subst hk
      cases h8
      exact CFSG.StandardType.ChevTwo.lieModel_psl_four_two_of_alternating_eight e
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | A r q =>
      rw [isLnA] at hi
      rcases hi with h2a | h2b | h2c | h2d | h2e
      · simp only [onLie, isLnEps] at h2a
        obtain ⟨hr, hqc⟩ := h2a
        have hr3 : r = 3 := by omega
        subst hr3
        have hpow : q.p ^ q.exponent = 2 ^ k := by
          rw [← TauCeti.PrimePower.card_def, hqc]
        have hkpos : k ≠ 0 := by
          intro hk
          subst hk
          rw [pow_zero] at hpow
          exact (Nat.one_lt_pow q.exponent_pos.ne' q.prime_p.one_lt).ne' hpow
        obtain ⟨hq2, hqe⟩ := Nat.Prime.pow_inj' q.prime_p Nat.prime_two
          (Nat.ne_of_gt q.exponent_pos) hkpos hpow
        have hm := CFSG.Models.lieModel_A 3 q hv e
        rw [hq2, hqe] at hm
        exact CFSG.Models.LieModel.toBlueprint (by simp [CFSG.Blueprint.classicalTags]) hm
      · exact absurd h2b.1 (by omega)
      · exact absurd h2c.1 (by omega)
      · exact absurd h2d.1 (by omega)
      · exact absurd h2e.2.2 (by simp [isAltN])
    | _ => exact absurd hi (by simp [isLnA, isLnEps, onLie, isAltN])

private theorem e6_fieldRel_aux7 {q : TauCeti.PrimePower} {S : Type} [Group S] {labK : GLALabel}
    {hv : (TauCeti.LieTypeIndex.E6 q).Valid} (hq2 : q.p = 2)
    (hKlabel : Y10F.HasLabel S (· = labK))
    (hdE6 : (TauCeti.LieTypeIndex.E6 q).characteristic = 2)
    (e : S ⧸ Subgroup.center S ≃* (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group) :
    (canonLabel labK).n = q.exponent := by
  have h2n := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.two_pow_canonLabel_n_of_lie
    CFSG.StandardType.ggLabelRigidInput_holds hKlabel ⟨.E6 q, hv⟩ hdE6 e
  have hfield : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize (TauCeti.LieTypeIndex.E6 q) =
      2 ^ q.exponent := by
    show q.card = 2 ^ q.exponent
    rw [TauCeti.PrimePower.card_def, hq2]
  exact Nat.pow_right_injective le_rfl (h2n.trans hfield)

private theorem e6_fieldRel_aux8 {p n k : ℕ} {X J : Subgroup Ω} {x : Ω}
    (hp : p.Prime) (hp2 : p ≠ 2) (hxN : x ∈ Subgroup.normalizer (X : Set Ω)) (hxp : x ^ p = 1)
    (hq : CFSG.Open.IsQuasisimple (PQuot p X)) (hne : chevAut p X ⟨x, hxN⟩ ≠ 1)
    (hJx : GLAPComponent p (X ⊓ cx x) J)
    (hJ : catalogIs (PSimple p J) (isOmPA n (2 ^ k))) {q : TauCeti.PrimePower}
    {hvE : (TauCeti.LieTypeIndex.E6 q).Valid}
    (hdE6 : (TauCeti.LieTypeIndex.E6 q).characteristic = 2)
    (eE : PSimple p X ≃* (TauCeti.CFSGIndex.lie ⟨.E6 q, hvE⟩).Group) :
    ∃ labJ : GLALabel, Y10F.HasLabel ↥(chevTransfer p X J) (· = labJ) ∧
      (canonLabel labJ).n = k := by
  have hap : IsPGroup p (Subgroup.zpowers x) := isPGroup_zpowers_of_pow_eq_one hxp
  have hJ' : GLAPComponent p
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (chevAut p X ⟨x, hxN⟩))
      (chevTransfer p X J) :=
    CFSG.LocalAnalysis.GLTheoremA.glaPComponent_chevTransfer hp hxN hap hJx
  have hJ'q : CFSG.Open.IsQuasisimple ↥(chevTransfer p X J) :=
    exc_transfer_isQuasisimple (d := ⟨.E6 q, hvE⟩) hp hp2 hq.2
      (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq)
      hdE6 eE hxN hxp hne hJx
  obtain ⟨eP⟩ := CFSG.LocalAnalysis.GLTheoremA.nonempty_pSimple_equiv_chevTransfer hp hxN hap hJx
  have hJ'cat : catalogIs (PSimple p (chevTransfer p X J)) (isOmPA n (2 ^ k)) :=
    (CFSG.LocalAnalysis.GLTheoremA.catalogIs_congr eP).1 hJ
  obtain ⟨iJ, hiJ, ⟨eJ'⟩⟩ := hJ'cat
  rcases hiJ with h1 | ⟨-, h2⟩
  · exact exc_label_of_lieModel (p := p) hp hJ' hJ'q (e6_fieldRel_aux2 (p := p) ⟨iJ, h1, ⟨eJ'⟩⟩)
  · exact exc_label_of_lieModel (p := p) hp hJ' hJ'q (e6_fieldRel_aux5 (p := p) ⟨iJ, h2, ⟨eJ'⟩⟩)

theorem e6_fieldRel {p : ℕ} {B X D J : Subgroup Ω} {x : Ω} (H : ExcHyp p B X D J x) {n k : ℕ} (hn : 3 ≤ n) (hk : 1 ≤ k)
    (hJ : catalogIs (PSimple p J) (isOmPA n (2 ^ k))) (hE6 : catalogIs (PSimple p X) ExcE6Idx) :
    catalogIs (PSimple p X) (ExcE6OverIdx k) := by
  obtain ⟨iE, hiE, ⟨eE⟩⟩ := hE6
  cases iE with
  | cyclic c hc => exact absurd hiE (by simp [ExcE6Idx, onLie])
  | alternating a ha => exact absurd hiE (by simp [ExcE6Idx, onLie])
  | sporadic s => exact absurd hiE (by simp [ExcE6Idx, onLie])
  | lie idx =>
    obtain ⟨dE, hvE⟩ := idx
    cases dE with
    | E6 q =>
      have hq2 : q.p = 2 := hiE
      have hdE6 : (TauCeti.LieTypeIndex.E6 q).characteristic = 2 :=
        (TauCeti.LieTypeIndex.characteristic_E6 q).trans hq2
      have hAll : Y10F.HasLabel (PQuot p X) (fun _ => True) := CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial) H.hinn.2
      have hq : CFSG.Open.IsQuasisimple (PQuot p X) := Y10F.hasLabel_isQuasisimple hAll
      have hcen : Subgroup.center (PSimple p X) = ⊥ := Y10F.center_centerQuot_eq_bot hq
      have hyN : x ∈ Subgroup.normalizer (X : Set Ω) := H.hxN
      have hne : chevAut p X ⟨x, hyN⟩ ≠ 1 := fun h1 =>
        exc3_not_centMod H ((I141F.chevAut_eq_one_iff_of_quasisimple hq hyN).1 h1)
      have hap : IsPGroup p (Subgroup.zpowers x) := isPGroup_zpowers_of_pow_eq_one H.hxp
      have hJx : GLAPComponent p (X ⊓ cx x) J := glaPComponent_inf_cx_of_eq_sup H.hDx H.hJ
      obtain ⟨labK, -, hinK⟩ :=
        CFSG.LocalAnalysis.GLTheoremA.I141F.innDiagKind_chevAut hyN hq H.hinn
      have hKlabel : Y10F.HasLabel (PSimple p X) (· = labK) :=
        CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hinK
      have hJ' : GLAPComponent p (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (chevAut p X ⟨x, hyN⟩)) (chevTransfer p X J) := CFSG.LocalAnalysis.GLTheoremA.glaPComponent_chevTransfer H.hp hyN hap hJx
      obtain ⟨labJ, hlabJ, hJn⟩ :=
        e6_fieldRel_aux8 H.hp H.hp2 hyN H.hxp hq hne hJx hJ hdE6 eE
      have hdvd := CFSG.LocalAnalysis.GLTheoremA.Y10GField.inn_of_families
        (CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.innDiagLin_of_labelDict
          CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.linLabelDict_holds)
        CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.innDiagUni_holds
        CFSG.LocalAnalysis.GLTheoremA.Y10GField.innDiagSymp_holds
        CFSG.LocalAnalysis.GLTheoremA.Y10GField.innDiagOrth_holds
        CFSG.LocalAnalysis.GLTheoremA.Y10GField.innDiagExc_holds
        (PSimple p X) p (chevAut p X ⟨x, hyN⟩) (chevTransfer p X J) labK labJ
        H.hp H.hp2 hcen hinK (CFSG.LocalAnalysis.GLTheoremA.chevAut_pow_eq_one p X hyN H.hxp)
        hlabJ hJ'
      have hφ : (PSimple p X) ⧸ Subgroup.center (PSimple p X) ≃*
          (TauCeti.CFSGIndex.lie ⟨.E6 q, hvE⟩).Group :=
        (CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).trans eE
      have hKn := e6_fieldRel_aux7 hq2 hKlabel hdE6 hφ
      rw [hKn, hJn] at hdvd
      exact ⟨.lie ⟨.E6 q, hvE⟩, ⟨hq2, hdvd⟩, ⟨eE⟩⟩
    | _ => exact absurd hiE (by simp [ExcE6Idx, onLie])

private theorem e6_four_of_halfSplit_aux1 (k : ℕ) : ¬ 7 ∣ 2 ^ k + 1 := by
  intro h
  have hz : ((2 : ZMod 7) ^ k + 1 = 0) := by
    have h1 : ((2 ^ k + 1 : ℕ) : ZMod 7) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
    push_cast at h1
    exact h1
  have hpow : (2 : ZMod 7) ^ k = (2 : ZMod 7) ^ (k % 3) := by
    conv_lhs => rw [← Nat.div_add_mod k 3]
    rw [pow_add, pow_mul, show (2 : ZMod 7) ^ 3 = 1 by decide, one_pow, one_mul]
  rw [hpow] at hz
  have hk3 : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases k % 3 <;> exact absurd hz (by decide)

private theorem e6_four_of_halfSplit_aux2 {p e k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (he : e ∣ k) (hpk : p ∣ 2 ^ k + 1) {c : Prop}
    (h : LargeEvenHalfSplit16 p ⟨.E6, 0, e⟩ c) : p = 5 ∧ c ∧ e = 2 := by
  unfold LargeEvenHalfSplit16 LargeEvenSplit16 at h
  rcases h with h | h | h | h | h | h
  · rcases h with h | h | h | h
    · obtain ⟨-, hdvd⟩ := h
      exfalso
      obtain ⟨j, rfl⟩ := he
      have hdd : 2 ^ e - 1 ∣ 2 ^ (e * j) - 1 := by
        rw [pow_mul]
        exact Nat.sub_one_dvd_pow_sub_one (2 ^ e) j
      have hp2' : p ∣ 2 := by
        have hd := Nat.dvd_sub hpk (hdvd.trans hdd)
        have heq : 2 ^ (e * j) + 1 - (2 ^ (e * j) - 1) = 2 := by
          have hpos : 1 ≤ 2 ^ (e * j) := Nat.one_le_two_pow
          omega
        rwa [heq] at hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hp2')
    · exact absurd h (by simp [LargeEvenUntwisted])
    · exact absurd h (by simp)
    · exact absurd h.2 hp3
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · obtain ⟨ht, hn, hc, hp5⟩ := h
    rcases ht with ht | ht
    · exact absurd ht (by simp)
    · exact ⟨hp5, hc, hn⟩
  · exact absurd h (by simp)
  · obtain ⟨-, -, hp7⟩ := h
    subst hp7
    exact absurd hpk (e6_four_of_halfSplit_aux1 k)

private theorem e6_four_of_halfSplit_aux3 {k : ℕ} {S : Type} [Group S]
    (h : catalogIs S (ExcE6OverIdx k)) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid)
      (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group),
      q.p = 2 ∧ q.exponent ∣ k ∧ CFSG.Blueprint.LieModel S .E6 0 2 q.exponent := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | E6 q =>
      simp only [ExcE6OverIdx, onLie] at hi
      obtain ⟨hqp, hqdvd⟩ := hi
      exact ⟨q, hv, e, hqp, hqdvd,
        Or.inr (Or.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags],
          ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
          CFSG.StandardType.ChevTwo.untwistedChevalleyModel_of_bridge
            CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv hqp e⟩)⟩
    | _ => simp [ExcE6OverIdx, onLie] at hi
  | _ => simp [ExcE6OverIdx, onLie] at hi

private theorem e6_four_of_halfSplit_aux4 {e : ℕ} (he : 1 ≤ e) :
    CFSG.SeitzReduction.F4Pilot.evenLieOrder .E6 0 e ≠ 6048 := by
  change CFSG.Open.orderE6 (2 ^ e) ≠ 6048
  intro h
  have hq : IsPrimePow (2 ^ e) := ⟨2, e, Nat.prime_iff.mp Nat.prime_two, he, rfl⟩
  have h36 : 2 ^ 36 ≤ CFSG.Open.orderE6 (2 ^ e) := by
    rcases CFSG.LocalAnalysis.GLTheoremA.LieGrid.orderE6_mul (q := 2 ^ e) hq with h1 | h0
    · exact h1.2
    · exact absurd h0 (by positivity)
  rw [h] at h36
  norm_num at h36

private theorem e6_four_of_halfSplit_aux5 {X : Type} [Group X] {e : ℕ}
    (hL : CFSG.Blueprint.LieModel X .E6 0 2 e) {lab : LargeEvenLabel}
    (hlam : LargeEvenInLambda2 lab) (hM : CFSG.StandardType.MarkedModel lab X) :
    CFSG.StandardType.markChar lab = 2 := by
  obtain ⟨t, r, n⟩ := lab
  by_contra hc
  have hb2 : t = .B2der ∨ t = .G2der := by
    cases t <;> simp_all [CFSG.StandardType.markChar]
  have hcard := CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hL
  rcases hb2 with hb | hg
  · subst t
    have h360 := CFSG.StandardType.ggMarkedModel_card_b2der rfl hM
    rw [h360] at hcard
    exact CFSG.StandardType.ClNonsplit.evenLieOrder_ne_three_sixty_of_admissible
      (CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hL) hcard.symm
  · subst t
    have h6048 : Nat.card X = 6048 := by
      dsimp only [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
        CFSG.StandardType.markRank, CFSG.StandardType.markChar, CFSG.StandardType.markDeg] at hM
      rcases hM with ⟨-, -, K, _, _, hK, ⟨eK⟩⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
      · rw [Nat.card_congr eK.toEquiv,
          CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_three le_rfl hK
            (by norm_num)]
        decide
      · exact absurd hn (by norm_num)
      · exact absurd hn (by norm_num)
      · exact absurd hn (by norm_num)
    rw [h6048] at hcard
    exact e6_four_of_halfSplit_aux4
      (CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hL).2.1 hcard.symm

private theorem e6_four_of_halfSplit_aux6 {e : ℕ} {X : Subgroup Ω} {lab : GLALabel}
    (hL : CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .E6 0 2 e)
    (hlab : LabelOf X lab) : lab = ⟨.E6, 0, e⟩ := by
  obtain ⟨t, r, n⟩ := lab
  have hH : Y10F.HasLabel ↥X (· = ⟨t, r, n⟩) :=
    (Y10F.labelOf_iff_hasLabel X ⟨t, r, n⟩).1 hlab
  have hlam : LargeEvenInLambda2 ⟨t, r, n⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.lambda2_of_hasLabel hH
  have hM : CFSG.StandardType.MarkedModel ⟨t, r, n⟩ (↥X ⧸ Subgroup.center ↥X) :=
    CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel hH
  have hchar := e6_four_of_halfSplit_aux5 hL hlam hM
  obtain ⟨ht, hn⟩ := CFSG.StandardType.NbrInnerMore.eq_of_markedModel_E6
    (CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hL).2.1 hL hlam hchar hM
  dsimp only at ht hn
  subst t
  have hr : r = 0 := by
    have h2 := hlam
    simp only [LargeEvenInLambda2] at h2
    exact h2.2
  subst n
  subst r
  rfl

theorem e6_four_of_halfSplit {p : ℕ} {B X D J : Subgroup Ω} {x : Ω} (H : ExcHyp p B X D J x) (hp3 : p ≠ 3) {k : ℕ}
    (hpk : p ∣ 2 ^ k + 1) (hE6 : catalogIs (PSimple p X) (ExcE6OverIdx k)) :
    p = 5 ∧ Subgroup.center ↥X = ⊥ ∧ catalogIs (PSimple p X) ExcE6FourIdx ∧ LabelOf X ⟨.E6, 0, 2⟩ := by
  obtain ⟨lab, hlab, hhs⟩ := H.hhs
  obtain ⟨q, hv, e, hqp, hqdvd, hLM⟩ := e6_four_of_halfSplit_aux3 hE6
  haveI : Nontrivial (PSimple p X) :=
    (CFSG.LieType.Catalog.lieModel_finite_simple (PSimple p X) .E6 0 2 q.exponent hLM).2.1
  obtain ⟨eZX⟩ := CFSG.LocalAnalysis.GLTheoremA.S265.SF.nonempty_centerQuot_equiv_pSimple
    (p := p) H.hX
  have hLM' : CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .E6 0 2 q.exponent :=
    CFSG.Blueprint.LieModel.of_mulEquiv eZX.symm hLM
  have hlab_eq : lab = ⟨.E6, 0, q.exponent⟩ := e6_four_of_halfSplit_aux6 hLM' hlab
  subst hlab_eq
  obtain ⟨hp5, hcen, he2⟩ := e6_four_of_halfSplit_aux2 H.hp H.hp2 hp3 hqdvd hpk hhs
  refine ⟨hp5, hcen, ?_, ?_⟩
  · refine ⟨.lie ⟨.E6 q, hv⟩, ?_, ⟨e⟩⟩
    rw [show ExcE6FourIdx (.lie ⟨.E6 q, hv⟩) = (q.card = 4) from rfl]
    rw [TauCeti.PrimePower.card_def, hqp, he2]
    norm_num
  · rw [he2] at hlab
    exact hlab

private theorem e6_four_sylow_data_aux1 {S : Type} [Group S]
    (hZ : Subgroup.center S = ⊥) : Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro h
    have := congrArg (fun φ : MulAut S => φ h) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

private theorem e6_four_sylow_data_aux2 {S B : Type} [Group S] [Group B]
    (hZ : Subgroup.center S = ⊥) (α : B →* MulAut S)
    (hle : α.range ≤ (MulAut.conj : S →* MulAut S).range) :
    ∃ β : B →* S, ∀ b, MulAut.conj (β b) = α b := by
  have hinj := e6_four_sylow_data_aux1 hZ
  refine ⟨(MonoidHom.ofInjective hinj).symm.toMonoidHom.comp
    (α.codRestrict _ fun b => hle ⟨b, rfl⟩), fun b => ?_⟩
  change MulAut.conj ((MonoidHom.ofInjective hinj).symm (α.codRestrict _ _ b)) = α b
  rw [MonoidHom.apply_ofInjective_symm]
  rfl

private theorem e6_four_sylow_data_auxmark {X : Subgroup Ω} (hL : LabelOf X ⟨.E6, 0, 2⟩) :
    CFSG.Assembly.E6FourMark ↥X := by
  refine CFSG.Assembly.standardTypeRecognitionMarking_mono ?_ hL
  rintro lab R _ I F θ (rfl : lab = ⟨.E6, 0, 2⟩)
  exact ⟨rfl, rfl⟩

private theorem e6_four_sylow_data_aux3 {B X : Subgroup Ω}
    (hmark : CFSG.Assembly.E6FourMark ↥X) (hZ : Subgroup.center ↥X = ⊥)
    (hB : CFSG.Open.IsElemAbelian 5 B) (hBN : B ≤ Subgroup.normalizer (X : Set Ω)) :
    ∃ β : B →* ↥X, ∀ (b : B) (j : ↥X),
      (b : Ω) * (j : Ω) * (b : Ω)⁻¹ =
        ((β b : ↥X) : Ω) * (j : Ω) * ((β b : ↥X) : Ω)⁻¹ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : IsMulCommutative B := hB.1
  let α : B →* MulAut ↥X :=
    (Subgroup.normalizerMonoidHom (H := X)).comp (Subgroup.inclusion hBN)
  have hα : ∀ (b : B) (j : ↥X),
      (((α b) j : ↥X) : Ω) = (b : Ω) * (j : Ω) * (b : Ω)⁻¹ := fun _ _ => rfl
  have hb5 : ∀ b : B, b ^ 5 = 1 := fun b => Subtype.ext (by simpa using hB.2 b b.2)
  obtain ⟨β, hβ⟩ := e6_four_sylow_data_aux2 hZ α (by
    rintro _ ⟨b, rfl⟩
    exact (CFSG.Assembly.e6FourOutInner_holds ↥X hmark hZ).1 (α b)
      (by rw [← map_pow, hb5, map_one]))
  exact ⟨β, fun b j => by rw [← hα, ← hβ]; rfl⟩

private theorem e6_four_sylow_data_aux4 {B X : Subgroup Ω}
    (hB : CFSG.Open.IsElemAbelian 5 B)
    (hSC : ∀ g ∈ X ⊔ B, g ∈ Subgroup.centralizer (B : Set Ω) → orderOf g = 5 → g ∈ B)
    {β : B →* ↥X}
    (hβc : ∀ (b : B) (j : ↥X), (b : Ω) * (j : Ω) * (b : Ω)⁻¹ =
      ((β b : ↥X) : Ω) * (j : Ω) * ((β b : ↥X) : Ω)⁻¹) :
    (∀ b : B, ((β b : ↥X) : Ω) ∈ B) ∧
      (∀ b : B, ((β b : ↥X) : Ω) ∈ Subgroup.centralizer (B : Set Ω)) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : IsMulCommutative B := hB.1
  have hβcomm : ∀ b b' : B, (β b) * (β b') = (β b') * (β b) := fun b b' => by
    rw [← map_mul, ← map_mul, mul_comm']
  have hβcent : ∀ b : B, ((β b : ↥X) : Ω) ∈ Subgroup.centralizer (B : Set Ω) := by
    intro b
    rw [Subgroup.mem_centralizer_iff]
    intro b' hb'
    have hconj : (b' : Ω) * ((β b : ↥X) : Ω) * (b' : Ω)⁻¹ = ((β b : ↥X) : Ω) := by
      have hc := congrArg (fun z : ↥X => (z : Ω)) (hβcomm b ⟨b', hb'⟩)
      rw [Subgroup.coe_mul, Subgroup.coe_mul] at hc
      rw [hβc ⟨b', hb'⟩ (β b), ← hc]
      group
    exact mul_inv_eq_iff_eq_mul.1 hconj
  refine ⟨?_, hβcent⟩
  intro b
  by_cases hb1 : β b = 1
  · rw [hb1]; simp
  · refine hSC _ (Subgroup.mem_sup_left (β b).2) (hβcent b) (orderOf_eq_prime ?_ ?_)
    · have hb5 : b ^ 5 = 1 := Subtype.ext (by simpa using hB.2 b b.2)
      rw [← Subgroup.coe_pow]
      rw [show (β b) ^ 5 = 1 by rw [← map_pow, hb5, map_one]]
      rfl
    · exact fun h => hb1 (Subtype.ext h)

private theorem e6_four_sylow_data_aux5 {B X : Subgroup Ω} {β : B →* ↥X}
    (hβc : ∀ (b : B) (j : ↥X), (b : Ω) * (j : Ω) * (b : Ω)⁻¹ =
      ((β b : ↥X) : Ω) * (j : Ω) * ((β b : ↥X) : Ω)⁻¹) :
    ∀ b : B, ((b : Ω) * ((β b : ↥X) : Ω)⁻¹) ∈ cs X := by
  intro b
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hmem : ((β b : ↥X) : Ω)⁻¹ * y * ((β b : ↥X) : Ω) ∈ X :=
    X.mul_mem (X.mul_mem (X.inv_mem (β b).2) hy) (β b).2
  have h := hβc b ⟨((β b : ↥X) : Ω)⁻¹ * y * ((β b : ↥X) : Ω), hmem⟩
  have hb : (b : Ω) * (((β b : ↥X) : Ω)⁻¹ * y * ((β b : ↥X) : Ω)) * (b : Ω)⁻¹ = y := by
    rw [h]; group
  have hb' : ((β b : ↥X) : Ω)⁻¹ * y * ((β b : ↥X) : Ω) = (b : Ω)⁻¹ * y * (b : Ω) := by
    calc ((β b : ↥X) : Ω)⁻¹ * y * ((β b : ↥X) : Ω)
        = (b : Ω)⁻¹ * ((b : Ω) * (((β b : ↥X) : Ω)⁻¹ * y * ((β b : ↥X) : Ω)) *
            (b : Ω)⁻¹) * (b : Ω) := by group
      _ = (b : Ω)⁻¹ * y * (b : Ω) := by rw [hb]
  calc y * ((b : Ω) * ((β b : ↥X) : Ω)⁻¹)
      = (b : Ω) * ((b : Ω)⁻¹ * y * (b : Ω)) * ((β b : ↥X) : Ω)⁻¹ := by group
    _ = (b : Ω) * (((β b : ↥X) : Ω)⁻¹ * y * ((β b : ↥X) : Ω)) *
          ((β b : ↥X) : Ω)⁻¹ := by rw [hb']
    _ = ((b : Ω) * ((β b : ↥X) : Ω)⁻¹) * y := by group

private theorem e6_four_sylow_data_aux6 {B X : Subgroup Ω} {x : Ω}
    (hx : x ∈ B) {β : B →* ↥X}
    (hβc : ∀ (b : B) (j : ↥X), (b : Ω) * (j : Ω) * (b : Ω)⁻¹ =
      ((β b : ↥X) : Ω) * (j : Ω) * ((β b : ↥X) : Ω)⁻¹) (hxX : x ∉ cs X) :
    ((β ⟨x, hx⟩ : ↥X) : Ω) ∉ cs X := by
  intro ha
  apply hxX
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hcomm := (Subgroup.mem_centralizer_iff.1 ha) y hy
  have ha' : ((β ⟨x, hx⟩ : ↥X) : Ω) * y * ((β ⟨x, hx⟩ : ↥X) : Ω)⁻¹ = y := by
    calc ((β ⟨x, hx⟩ : ↥X) : Ω) * y * ((β ⟨x, hx⟩ : ↥X) : Ω)⁻¹
        = (y * ((β ⟨x, hx⟩ : ↥X) : Ω)) * ((β ⟨x, hx⟩ : ↥X) : Ω)⁻¹ := by rw [hcomm]
      _ = y := by group
  have h1 : (x : Ω) * y * (x : Ω)⁻¹ = y := by
    rw [hβc ⟨x, hx⟩ ⟨y, hy⟩, ha']
  exact (mul_inv_eq_iff_eq_mul.1 h1).symm

private theorem e6_four_sylow_data_aux7a {X : Subgroup Ω}
    (hmark : CFSG.Assembly.E6FourMark ↥X) (hZ : Subgroup.center ↥X = ⊥) :
    ∃ E U : Subgroup Ω, E ≤ X ∧ U ≤ X ∧ CFSG.Open.IsElemAbelian 5 E ∧
      Nat.card E = 5 ^ 4 ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set Ω) := by
  obtain ⟨E₀, U₀, hE₀el, hE₀card, hU₀ne, hU₀2, hE₀U₀⟩ :=
    CFSG.Assembly.e6FourTwoLocalFive_holds ↥X hmark hZ
  refine ⟨E₀.map X.subtype, U₀.map X.subtype, Subgroup.map_subtype_le E₀,
    Subgroup.map_subtype_le U₀, hE₀el.map X.subtype, ?_, ?_, hU₀2.map X.subtype, ?_⟩
  · rw [Subgroup.card_subtype X E₀, hE₀card]
  · intro h
    exact hU₀ne ((Subgroup.map_eq_bot_iff_of_injective (f := X.subtype) U₀
      X.subtype_injective).mp h)
  · calc E₀.map X.subtype = E₀.map X.subtype := rfl
      _ ≤ (Subgroup.normalizer (U₀ : Set ↥X)).map X.subtype := Subgroup.map_mono hE₀U₀
      _ ≤ Subgroup.normalizer (U₀.map X.subtype) := Subgroup.le_normalizer_map X.subtype

private theorem e6_four_sylow_data_aux7b {B X E U : Subgroup Ω}
    (hB : CFSG.Open.IsElemAbelian 5 B) (hZ : Subgroup.center ↥X = ⊥)
    (hcardC : Nat.card ↥(B ⊓ cs X) = 5) (hEel : CFSG.Open.IsElemAbelian 5 E)
    (hEcard : Nat.card E = 5 ^ 4) (hEX : E ≤ X)
    (hEUN : E ≤ Subgroup.normalizer (U : Set Ω)) (hUX : U ≤ X) (hU : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) :
    ∃ J : Subgroup Ω, J ≤ X ⊔ B ∧ CFSG.Open.IsElemAbelian 5 J ∧ Nat.card J = 5 ^ 5 ∧
      J ≤ Subgroup.normalizer (U : Set Ω) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let C : Subgroup Ω := B ⊓ cs X
  have hCel : CFSG.Open.IsElemAbelian 5 C := hB.mono inf_le_left
  have hcommEC : ∀ e ∈ E, ∀ c ∈ C, e * c = c * e := by
    intro e he c hc
    exact Subgroup.mem_centralizer_iff.1 hc.2 e (hEX he)
  have hcentCE : C ≤ Subgroup.centralizer (E : Set Ω) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact hcommEC e he c hc
  have hnormCE : C ≤ Subgroup.normalizer (E : Set Ω) :=
    hcentCE.trans (Subgroup.centralizer_le_normalizer (E : Set Ω))
  have hdisj : Disjoint E C := by
    refine disjoint_iff.mpr ?_
    refine le_bot_iff.mp ?_
    calc E ⊓ C ≤ X ⊓ cs X := inf_le_inf hEX inf_le_right
      _ = ⊥ := CFSG.LocalAnalysis.GLTheoremA.inf_centralizer_eq_bot_of_center le_rfl hZ
  have hcardEC : Nat.card ↥(E ⊔ C) = 5 ^ 5 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E C hnormCE hdisj,
      hEcard, hcardC]
    norm_num
  have hECel : CFSG.Open.IsElemAbelian 5 (E ⊔ C) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hEel hCel hcommEC
  have hCUN : C ≤ Subgroup.normalizer (U : Set Ω) := by
    have hCU : C ≤ Subgroup.centralizer (U : Set Ω) := by
      intro c hc
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact Subgroup.mem_centralizer_iff.1 hc.2 u (hUX hu)
    exact hCU.trans (Subgroup.centralizer_le_normalizer (U : Set Ω))
  exact ⟨E ⊔ C, sup_le (hEX.trans le_sup_left) (inf_le_left.trans le_sup_right), hECel, hcardEC,
    sup_le hEUN hCUN⟩

private theorem e6_four_sylow_data_aux8 {B X J U : Subgroup Ω}
    (hJK : J ≤ X ⊔ B) (hUK : U ≤ X ⊔ B) (hJel : CFSG.Open.IsElemAbelian 5 J)
    (hJcard : Nat.card J = 5 ^ 5) (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hJN : J ≤ Subgroup.normalizer (U : Set Ω)) :
    5 ≤ GLATwoLocalRank 5 ↥(X ⊔ B) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let K : Subgroup Ω := X ⊔ B
  have hU'ne : U.subgroupOf K ≠ ⊥ := by
    intro h
    apply hU
    rw [eq_bot_iff]
    intro u hu
    have h1 : (⟨u, hUK hu⟩ : K) ∈ U.subgroupOf K := hu
    rw [h] at h1
    exact congrArg Subtype.val (Subgroup.mem_bot.mp h1)
  have hU'2 : IsPGroup 2 (U.subgroupOf K) := hU2.comap_subtype
  have hJel' : CFSG.Open.IsElemAbelian 5 (J.subgroupOf K) := hJel.subgroupOf K
  have hJcard' : Nat.card ↥(J.subgroupOf K) = 5 ^ 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJK).toEquiv, hJcard]
  have hJN' : J.subgroupOf K ≤ Subgroup.normalizer (U.subgroupOf K : Set ↥K) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hUK]
    exact Subgroup.subgroupOf_mono K hJN
  have hbound := GL83.PiGen.card_le_pow_twoLocalRank (X := ↥K)
    hJel' hU'2 hU'ne hJN'
  rw [hJcard'] at hbound
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 5)).1 hbound

private theorem e6_four_sylow_data_aux9a {B X D J : Subgroup Ω} {x : Ω}
    (H : ExcHyp 5 B X D J x) (hZ : Subgroup.center ↥X = ⊥) (hL : LabelOf X ⟨.E6, 0, 2⟩) :
    B = (B ⊓ cs X) ⊔ (B ⊓ X) ∧ Nat.card B = 5 * Nat.card ↥(B ⊓ X) := by
  have hmark := e6_four_sylow_data_auxmark hL
  obtain ⟨β, hβc⟩ := e6_four_sylow_data_aux3 hmark hZ H.hB H.hBN
  obtain ⟨hβmem, _⟩ := e6_four_sylow_data_aux4 H.hB H.hSC hβc
  have hquot := e6_four_sylow_data_aux5 hβc
  let C : Subgroup Ω := B ⊓ cs X
  have hquotC : ∀ b : B, ((b : Ω) * ((β b : ↥X) : Ω)⁻¹) ∈ C :=
    fun b => ⟨B.mul_mem b.2 (B.inv_mem (hβmem b)), hquot b⟩
  have hBsplit : B = C ⊔ (B ⊓ X) := by
    apply le_antisymm
    · intro b hb
      let bB : B := ⟨b, hb⟩
      have h1 : (b : Ω) * ((β bB : ↥X) : Ω)⁻¹ ∈ C := hquotC bB
      have h2 : ((β bB : ↥X) : Ω) ∈ B ⊓ X := ⟨hβmem bB, (β bB).2⟩
      have h3 := Subgroup.mul_mem_sup h1 h2
      rwa [show ((b : Ω) * ((β bB : ↥X) : Ω)⁻¹) * ((β bB : ↥X) : Ω) = b from by group] at h3
    · exact sup_le inf_le_left inf_le_left
  have hdisjC : Disjoint C (B ⊓ X) := by
    refine disjoint_iff.mpr ?_
    refine le_bot_iff.mp ?_
    calc C ⊓ (B ⊓ X) ≤ (cs X) ⊓ X := inf_le_inf inf_le_right inf_le_right
      _ = ⊥ := by
        rw [inf_comm]
        exact CFSG.LocalAnalysis.GLTheoremA.inf_centralizer_eq_bot_of_center le_rfl hZ
  have hnormCBX : (B ⊓ X) ≤ Subgroup.normalizer (C : Set Ω) := by
    have hcent : (B ⊓ X) ≤ Subgroup.centralizer (C : Set Ω) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact H.hB.comm hc.1 hb.1
    exact hcent.trans (Subgroup.centralizer_le_normalizer (C : Set Ω))
  have hcardB_eq : Nat.card B = 5 * Nat.card ↥(B ⊓ X) := by
    calc Nat.card B = Nat.card ↥(C ⊔ (B ⊓ X)) :=
          congrArg (fun H : Subgroup Ω => Nat.card ↥H) hBsplit
      _ = Nat.card C * Nat.card ↥(B ⊓ X) :=
          CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer C (B ⊓ X)
            hnormCBX hdisjC
      _ = 5 * Nat.card ↥(B ⊓ X) := by rw [H.hcard]
  exact ⟨hBsplit, hcardB_eq⟩

private theorem e6_four_sylow_data_aux9b {B X : Subgroup Ω}
    (hmark : CFSG.Assembly.E6FourMark ↥X) (hZ : Subgroup.center ↥X = ⊥)
    (hB : CFSG.Open.IsElemAbelian 5 B) :
    Nat.card ↥(B ⊓ X) ≤ 5 ^ 4 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hBXel : CFSG.Open.IsElemAbelian 5 (B ⊓ X) := hB.mono inf_le_left
  have hsub : IsPGroup 5 ((B ⊓ X).subgroupOf X) := hBXel.isPGroup.comap_subtype
  obtain ⟨P, hP⟩ := hsub.exists_le_sylow
  have hPcard : Nat.card P = 5 ^ 4 := CFSG.Assembly.e6FourSylowFive_holds ↥X hmark hZ P
  have h1 : Nat.card ((B ⊓ X).subgroupOf X) ≤ Nat.card P := Subgroup.card_le_of_le hP
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, hPcard] at h1

private theorem e6_four_sylow_data_aux10 {B X D J : Subgroup Ω} {x : Ω}
    (H : ExcHyp 5 B X D J x) (hZ : Subgroup.center ↥X = ⊥) (hL : LabelOf X ⟨.E6, 0, 2⟩) :
    5 ^ 5 ≤ Nat.card B := by
  have hmark := e6_four_sylow_data_auxmark hL
  obtain ⟨E, U, hEX, hUX, hEel, hEcard, hU, hU2, hEUN⟩ :=
    e6_four_sylow_data_aux7a hmark hZ
  obtain ⟨J', hJ'K, hJ'el, hJ'card, hJ'N⟩ :=
    e6_four_sylow_data_aux7b (B := B) (X := X) (E := E) (U := U)
      H.hB hZ H.hcard hEel hEcard hEX hEUN hUX hU hU2
  have hrank : 5 ≤ CFSG.Open.pRank 5 B :=
    (e6_four_sylow_data_aux8 hJ'K (hUX.trans le_sup_left) hJ'el hJ'card hU hU2 hJ'N).trans H.hrank
  obtain ⟨E', hE'B, hE'el, hE'card⟩ := CFSG.SectionRank.exists_pRank (p := 5) (by norm_num) B
  calc 5 ^ 5 ≤ 5 ^ CFSG.Open.pRank 5 B := Nat.pow_le_pow_right (by norm_num) hrank
    _ = Nat.card E' := hE'card.symm
    _ ≤ Nat.card B := Subgroup.card_le_of_le hE'B

private theorem e6_four_sylow_data_aux11 {B X D J : Subgroup Ω} {x : Ω}
    (H : ExcHyp 5 B X D J x) (hZ : Subgroup.center ↥X = ⊥) (hL : LabelOf X ⟨.E6, 0, 2⟩) :
    Nat.card ↥(B ⊓ X) = 5 ^ 4 := by
  obtain ⟨_, hcardB_eq⟩ := e6_four_sylow_data_aux9a H hZ hL
  have hle : Nat.card ↥(B ⊓ X) ≤ 5 ^ 4 :=
    e6_four_sylow_data_aux9b (e6_four_sylow_data_auxmark hL) hZ H.hB
  have hge : 5 ^ 4 ≤ Nat.card ↥(B ⊓ X) := by
    have h1 : 5 * 5 ^ 4 ≤ 5 * Nat.card ↥(B ⊓ X) := by
      calc 5 * 5 ^ 4 = 5 ^ 5 := by norm_num
        _ ≤ Nat.card B := e6_four_sylow_data_aux10 H hZ hL
        _ = 5 * Nat.card ↥(B ⊓ X) := hcardB_eq
    exact Nat.le_of_mul_le_mul_left h1 (by norm_num)
  exact le_antisymm hle hge

private theorem e6_four_sylow_data_auxCa {B X : Subgroup Ω} {a : Ω} (haX : a ∈ X) :
    (B ⊓ cs X) ≤ Subgroup.normalizer (Subgroup.zpowers a : Set Ω) := by
  have hcs : (B ⊓ cs X) ≤ Subgroup.centralizer (Subgroup.zpowers a : Set Ω) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have hca : Commute a c := Subgroup.mem_centralizer_iff.1 hc.2 a haX
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    exact (hca.zpow_left n).eq
  exact hcs.trans (Subgroup.centralizer_le_normalizer (Subgroup.zpowers a : Set Ω))

private theorem e6_four_sylow_data_auxDecomp {C A : Subgroup Ω}
    (hCa : C ≤ Subgroup.normalizer (A : Set Ω)) {z : Ω} (hz : z ∈ C ⊔ A) :
    ∃ c ∈ C, ∃ t ∈ A, z = c * t := by
  have hz' : z ∈ (C : Set Ω) * (A : Set Ω) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right C A hCa]
    exact hz
  rw [Set.mem_mul] at hz'
  obtain ⟨c, hc, t, ht, hct⟩ := hz'
  exact ⟨c, hc, t, ht, hct.symm⟩

private theorem e6_four_sylow_data_aux12a {B X D J : Subgroup Ω} {x : Ω}
    (H : ExcHyp 5 B X D J x) (hZ : Subgroup.center ↥X = ⊥) (hL : LabelOf X ⟨.E6, 0, 2⟩) :
    ∃ a : Ω, a ∈ B ⊓ X ∧ a ∉ cs X ∧ D = (B ⊓ cs X) ⊔ Subgroup.zpowers a := by
  have hmark := e6_four_sylow_data_auxmark hL
  obtain ⟨β, hβc⟩ := e6_four_sylow_data_aux3 hmark hZ H.hB H.hBN
  obtain ⟨hβmem, _⟩ := e6_four_sylow_data_aux4 H.hB H.hSC hβc
  have hquot := e6_four_sylow_data_aux5 hβc
  have hβx := e6_four_sylow_data_aux6 H.hxB hβc H.hxX
  let a : Ω := (β ⟨x, H.hxB⟩ : ↥X)
  have haX : a ∈ X := (β ⟨x, H.hxB⟩).2
  have hquotC : ∀ b : B, ((b : Ω) * ((β b : ↥X) : Ω)⁻¹) ∈ B ⊓ cs X :=
    fun b => ⟨B.mul_mem b.2 (B.inv_mem (hβmem b)), hquot b⟩
  have hxq : (x : Ω) * a⁻¹ ∈ B ⊓ cs X := hquotC ⟨x, H.hxB⟩
  have hDsup : D = (B ⊓ cs X) ⊔ Subgroup.zpowers a := by
    rw [H.hDx]
    apply le_antisymm
    · apply sup_le le_sup_left
      rw [Subgroup.zpowers_le]
      rw [← show ((x : Ω) * a⁻¹) * a = x from by group]
      exact Subgroup.mul_mem_sup hxq (Subgroup.mem_zpowers a)
    · apply sup_le le_sup_left
      rw [Subgroup.zpowers_le]
      have ha : a = ((x : Ω) * a⁻¹)⁻¹ * x := by group
      rw [ha]
      exact Subgroup.mul_mem_sup ((B ⊓ cs X).inv_mem hxq) (Subgroup.mem_zpowers x)
  exact ⟨a, ⟨hβmem ⟨x, H.hxB⟩, haX⟩, hβx, hDsup⟩

private theorem e6_four_sylow_data_aux12b {B X D : Subgroup Ω} {a : Ω}
    (hZ : Subgroup.center ↥X = ⊥)
    (hDsup : D = (B ⊓ cs X) ⊔ Subgroup.zpowers a) (haX : a ∈ X) :
    X ⊓ D = Subgroup.zpowers a := by
  have hCa := e6_four_sylow_data_auxCa (B := B) haX
  have hXC : X ⊓ (B ⊓ cs X) = ⊥ := by
    refine le_bot_iff.mp ?_
    calc X ⊓ (B ⊓ cs X) ≤ X ⊓ cs X := inf_le_inf le_rfl inf_le_right
      _ = ⊥ := CFSG.LocalAnalysis.GLTheoremA.inf_centralizer_eq_bot_of_center le_rfl hZ
  rw [hDsup]
  apply le_antisymm
  · intro z hz
    obtain ⟨c, hc, t, ht, hzt⟩ := e6_four_sylow_data_auxDecomp hCa hz.2
    have htX : t ∈ X := Subgroup.zpowers_le.2 haX ht
    have hcX : c ∈ X := by
      have : c = z * t⁻¹ := by rw [hzt]; group
      rw [this]
      exact X.mul_mem hz.1 (X.inv_mem htX)
    have hcbot : c ∈ (⊥ : Subgroup Ω) := by
      rw [← hXC]
      exact ⟨hcX, hc⟩
    have hc1 : c = 1 := Subgroup.mem_bot.mp hcbot
    rw [hzt, hc1, one_mul]
    exact ht
  · intro z hz
    exact ⟨Subgroup.zpowers_le.2 haX hz, Subgroup.mem_sup_right hz⟩

private theorem e6_four_sylow_data_aux12c {B X D J : Subgroup Ω} {a : Ω}
    (hDJ : D = B ⊓ cs J) (hXD : X ⊓ D = Subgroup.zpowers a) :
    (B ⊓ X) ⊓ cs J = Subgroup.zpowers a := by
  have h1 : (B ⊓ X) ⊓ cs J = X ⊓ D := by
    rw [hDJ]
    ext z
    simp only [Subgroup.mem_inf]
    tauto
  rw [h1, hXD]

private theorem e6_four_sylow_data_aux12d {B X D : Subgroup Ω} {a : Ω}
    (hDsup : D = (B ⊓ cs X) ⊔ Subgroup.zpowers a) (haX : a ∈ X) :
    X ⊓ cs D = X ⊓ cx a := by
  have hCa := e6_four_sylow_data_auxCa (B := B) haX
  apply le_antisymm
  · intro y hy
    refine ⟨hy.1, ?_⟩
    change y ∈ Subgroup.centralizer ({a} : Set Ω)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    have haD : a ∈ D := by
      rw [hDsup]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
    exact Subgroup.mem_centralizer_iff.1 hy.2 a haD
  · intro y hy
    refine ⟨hy.1, ?_⟩
    change y ∈ Subgroup.centralizer (D : Set Ω)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨c, hc, t, ht, hzt⟩ := e6_four_sylow_data_auxDecomp hCa (hDsup ▸ hz)
    have hyc : c * y = y * c := (Subgroup.mem_centralizer_iff.1 hc.2 y hy.1).symm
    have hya : Commute y a :=
      (Subgroup.mem_centralizer_iff.1 hy.2 a (Set.mem_singleton_iff.mp rfl)).symm
    have hyt : t * y = y * t := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
      exact (hya.zpow_right n).eq.symm
    calc z * y = (c * t) * y := by rw [hzt]
      _ = c * (t * y) := by group
      _ = c * (y * t) := by rw [hyt]
      _ = (c * y) * t := by group
      _ = (y * c) * t := by rw [hyc]
      _ = y * (c * t) := by group
      _ = y * z := by rw [hzt]

theorem e6_four_sylow_data {p : ℕ} {B X D J : Subgroup Ω} {x : Ω} (H : ExcHyp p B X D J x) (hp5 : p = 5)
    (hZ : Subgroup.center ↥X = ⊥) (hE : catalogIs (PSimple p X) ExcE6FourIdx) (hL : LabelOf X ⟨.E6, 0, 2⟩) :
    ∃ a ∈ B ⊓ X, a ∉ cs X ∧ GLAPComponent p (X ⊓ cx a) J ∧ Nat.card ↥(B ⊓ X) = p ^ 4 ∧
      (B ⊓ X) ⊓ cs J = Subgroup.zpowers a := by
  subst hp5
  obtain ⟨a, haBX, haX', hDsup⟩ := e6_four_sylow_data_aux12a H hZ hL
  have hXD := e6_four_sylow_data_aux12b hZ hDsup haBX.2
  have hDcs := e6_four_sylow_data_aux12d hDsup haBX.2
  exact ⟨a, haBX, haX', by rw [← hDcs]; exact H.hJ, e6_four_sylow_data_aux11 H hZ hL,
    e6_four_sylow_data_aux12c H.hDJ hXD⟩

private lemma e6_four_normalizes_aux1 {G : Type} [Group G] [Finite G] {g : G} {C : Subgroup G}
    (hord : orderOf g = 5) (hN : g ∉ Subgroup.normalizer (C : Set G)) :
    Function.Injective (fun i : Fin 5 => GLBConj (g ^ (i : ℕ)) C) := by
  have hHcard : Nat.card ↥(Subgroup.zpowers g) = 5 := by
    rw [Nat.card_zpowers, hord]
  haveI : Fact (Nat.card ↥(Subgroup.zpowers g)).Prime := by
    rw [hHcard]; exact ⟨by norm_num⟩
  let NH : Subgroup ↥(Subgroup.zpowers g) :=
    (Subgroup.normalizer (C : Set G)).comap (Subgroup.zpowers g).subtype
  have hNHtop : NH ≠ ⊤ := by
    intro h
    apply hN
    have hg : (⟨g, Subgroup.mem_zpowers g⟩ : ↥(Subgroup.zpowers g)) ∈ NH := by
      rw [h]; exact Subgroup.mem_top _
    exact hg
  have hNH : NH = ⊥ := (NH.eq_bot_or_eq_top_of_prime_card).resolve_right hNHtop
  have hnotmem : ∀ d : ℕ, 0 < d → d < 5 → g ^ d ∉ Subgroup.normalizer (C : Set G) := by
    intro d hd0 hd5 hmem
    have hmem' : (⟨g ^ d, Subgroup.npow_mem_zpowers g d⟩ : ↥(Subgroup.zpowers g)) ∈ NH := hmem
    rw [hNH, Subgroup.mem_bot] at hmem'
    have h1 : g ^ d = 1 := congrArg Subtype.val hmem'
    have hdvd : orderOf g ∣ d := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at hdvd
    have := Nat.le_of_dvd hd0 hdvd
    omega
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hd0 : 0 < (j : ℕ) - (i : ℕ) := by omega
    have hd5 : (j : ℕ) - (i : ℕ) < 5 := by omega
    have hm : (g ^ (j : ℕ)) * (g ^ (i : ℕ))⁻¹ ∈ Subgroup.normalizer (C : Set G) := by
      rw [← CFSG.HardMathSupport.Timmesfeld.Balance.Alt.gLBConj_eq_iff_mem_normalizer]
      exact hij
    rw [← pow_sub (g) (show (i:ℕ) ≤ (j:ℕ) by omega)] at hm
    exact hnotmem _ hd0 hd5 hm
  · have hd0 : 0 < (i : ℕ) - (j : ℕ) := by omega
    have hd5 : (i : ℕ) - (j : ℕ) < 5 := by omega
    have hm : (g ^ (i : ℕ)) * (g ^ (j : ℕ))⁻¹ ∈ Subgroup.normalizer (C : Set G) := by
      rw [← CFSG.HardMathSupport.Timmesfeld.Balance.Alt.gLBConj_eq_iff_mem_normalizer]
      exact hij.symm
    rw [← pow_sub (g) (show (j:ℕ) ≤ (i:ℕ) by omega)] at hm
    exact hnotmem _ hd0 hd5 hm

private lemma e6_four_normalizes_aux2 {p : ℕ} (hp : p.Prime) {Y J : Subgroup Ω}
    (hJ : GLAPComponent p Y J) (hZ : Subgroup.center (PQuot p J) = ⊥) :
    ∃ e ∈ barX p Y J, orderOf e = p ∧ ∃ c ∈ barX p Y J, e * c ≠ c * e := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hZc : Subgroup.center ↥(barX p Y J) = ⊥ := by
    have he := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.barXEquiv hp hJ.2.1
    rw [← Subgroup.map_center_eq he, hZ, Subgroup.map_bot]
  have hdvd : p ∣ Nat.card ↥(barX p Y J) :=
    CFSG.LocalAnalysis.GLTheoremA.S12.dvd_card_barX_of_component hp hJ
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' (G := ↥(barX p Y J)) p hdvd
  refine ⟨(e : PQuot p Y), e.2, (Subgroup.orderOf_coe e).trans he, ?_⟩
  by_contra hcon
  push Not at hcon
  have hemem : e ∈ Subgroup.center ↥(barX p Y J) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcon (g : PQuot p Y) g.2).symm
  rw [hZc, Subgroup.mem_bot] at hemem
  have h1 : orderOf e = 1 := by rw [hemem, orderOf_one]
  rw [he] at h1
  exact hp.one_lt.ne' h1

private lemma e6_four_normalizes_aux3 {p : ℕ} (hp : p.Prime) {Y J : Subgroup Ω}
    (hJ : GLAPComponent p Y J) (hZ : Subgroup.center (PQuot p J) = ⊥)
    (g : PQuot p Y) :
    ∀ i : Fin 5, ∃ e ∈ GLBConj (g ^ (i : ℕ)) (barX p Y J), orderOf e = p ∧
      ∃ c ∈ GLBConj (g ^ (i : ℕ)) (barX p Y J), e * c ≠ c * e := by
  obtain ⟨e0, he0, ho0, c0, hc0, hnc0⟩ := e6_four_normalizes_aux2 hp hJ hZ
  intro i
  let h : PQuot p Y := g ^ (i : ℕ)
  refine ⟨h⁻¹ * e0 * h, ?_, ?_, h⁻¹ * c0 * h, ?_, ?_⟩
  · rw [mem_gLBConj]
    rw [show h * (h⁻¹ * e0 * h) * h⁻¹ = e0 by group]
    exact he0
  · have hsem : SemiconjBy h⁻¹ e0 (h⁻¹ * e0 * h) := by
      unfold SemiconjBy; group
    exact (SemiconjBy.orderOf_eq h⁻¹ hsem).symm.trans ho0
  · rw [mem_gLBConj]
    rw [show h * (h⁻¹ * c0 * h) * h⁻¹ = c0 by group]
    exact hc0
  · intro heq
    apply hnc0
    have h1 := congrArg (fun z => h * z * h⁻¹) heq
    have h2 : h * ((h⁻¹ * e0 * h) * (h⁻¹ * c0 * h)) * h⁻¹ = e0 * c0 := by group
    have h3 : h * ((h⁻¹ * c0 * h) * (h⁻¹ * e0 * h)) * h⁻¹ = c0 * e0 := by group
    rwa [h2, h3] at h1

private lemma e6_four_normalizes_aux4 {p : ℕ} (hp : p.Prime) {Y J : Subgroup Ω}
    (hJ : GLAPComponent p Y J) (hZ : Subgroup.center (PQuot p J) = ⊥)
    {g : PQuot p Y} (hgord : orderOf g = 5)
    (hN : g ∉ Subgroup.normalizer (barX p Y J : Set (PQuot p Y))) :
    5 ≤ CFSG.Open.pRank p (⊤ : Subgroup (PQuot p Y)) := by
  classical
  let C : Fin 5 → Subgroup (PQuot p Y) := fun i => GLBConj (g ^ (i : ℕ)) (barX p Y J)
  have hCisComp : ∀ i : Fin 5, CFSG.IsComponent (C i) := fun i =>
    (CFSG.isComponent_iff_open (C i)).2
      (CFSG.HardMathSupport.Solomon.Coordinator.i25_isComponentOf_gLBConj hJ.2.2.1
        (by rw [Subgroup.mem_normalizer_iff]; intro y; simp))
  have hinj : Function.Injective C := e6_four_normalizes_aux1 hgord hN
  have hexists := e6_four_normalizes_aux3 hp hJ hZ g
  let S : Finset (Subgroup (PQuot p Y)) := Finset.univ.image C
  have hScard : S.card = 5 := by
    change (Finset.univ.image C).card = 5
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hS : ∀ K ∈ S, CFSG.IsComponent K ∧
      ∃ e ∈ K, orderOf e = p ∧ ∃ c ∈ K, e * c ≠ c * e := by
    intro K hK
    change K ∈ Finset.univ.image C at hK
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hK
    exact ⟨hCisComp i, hexists i⟩
  have hrank := CFSG.LocalAnalysis.RankThreeUC.AGL81C.card_le_pRank_of_components hp S hS
  rw [hScard] at hrank
  have h' : 5 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥(⊤ : Subgroup (PQuot p Y))) := by
    rwa [CFSG.SectionRank.pRank_eq_open_pRank_top p ↥(⊤ : Subgroup (PQuot p Y))] at hrank
  rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (⊤ : Subgroup (PQuot p Y))] at h'

private lemma e6_four_normalizes_aux5 {p : ℕ} (hp : p.Prime) {Y J : Subgroup Ω}
    (hJ : GLAPComponent p Y J) (hZ : Subgroup.center (PQuot p J) = ⊥)
    {g : PQuot p Y} (hgord : orderOf g = 5)
    (hN : g ∉ Subgroup.normalizer (barX p Y J : Set (PQuot p Y))) :
    ∃ E : Subgroup Ω, E ≤ Y ∧ IsElemAbelian p E ∧ p ^ 5 ≤ Nat.card E := by
  obtain ⟨E', -, hE'ab, hE'card⟩ :=
    CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup (PQuot p Y))
  have hE'cards : p ^ 5 ≤ Nat.card ↥E' := by
    rw [hE'card]
    exact Nat.pow_le_pow_right hp.pos (e6_four_normalizes_aux4 hp hJ hZ hgord hN)
  obtain ⟨E, hEY, hEab, hEcard⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S8.L83.lift_elemAbelian hp hE'ab hE'card
  refine ⟨E, hEY, hEab, ?_⟩
  rw [hEcard, ← hE'card]
  exact hE'cards

private lemma e6_four_normalizes_aux6 {p : ℕ} {B X D J : Subgroup Ω} {x : Ω}
    (H : ExcHyp p B X D J x) (hp5 : p = 5) (hZ : Subgroup.center ↥X = ⊥)
    (hE : catalogIs (PSimple p X) ExcE6FourIdx) (hL : LabelOf X ⟨.E6, 0, 2⟩)
    {b : Ω} (hb : b ∈ B ⊓ X) (hbN : b ∉ Subgroup.normalizer (J : Set Ω)) :
    ∃ E : Subgroup Ω, E ≤ X ∧ IsElemAbelian p E ∧ 5 ^ 5 ≤ Nat.card E := by
  obtain ⟨a, haA, haX, haJ, hA, hAJ⟩ := e6_four_sylow_data H hp5 hZ hE hL
  haveI : Fact p.Prime := ⟨H.hp⟩
  set Y : Subgroup Ω := X ⊓ cx a with hYdef
  have haJY : GLAPComponent p Y J := by rw [hYdef]; exact haJ
  have hYleX : Y ≤ X := by rw [hYdef]; exact inf_le_left
  have hbX : b ∈ X := hb.2
  have hbB : b ∈ B := hb.1
  have haB : a ∈ B := haA.1
  have hba : b * a = a * b :=
    congrArg Subtype.val (H.hB.1.is_comm.comm (⟨b, hbB⟩ : ↥B) (⟨a, haB⟩ : ↥B))
  have hbY : b ∈ Y := by
    rw [hYdef]
    exact Subgroup.mem_inf.mpr ⟨hbX, Subgroup.mem_centralizer_singleton_iff.2 hba⟩
  have hbp : b ^ p = 1 := H.hB.2 b hbB
  let g : PQuot p Y := QuotientGroup.mk' (GLAPPrimeCore p ↥Y) ⟨b, hbY⟩
  have hbp' : (⟨b, hbY⟩ : ↥Y) ^ p = 1 := Subtype.ext (by simpa using hbp)
  have hgp : g ^ p = 1 := by
    change (QuotientGroup.mk' (GLAPPrimeCore p ↥Y) ⟨b, hbY⟩) ^ p = 1
    rw [← map_pow, hbp', map_one]
  have hbN' : g ∉ Subgroup.normalizer (barX p Y J : Set (PQuot p Y)) := by
    intro hmem
    have heq : GLBConj g (barX p Y J) = barX p Y J :=
      (mem_normalizer_iff_gLBConj_eq (g := g) (H := barX p Y J)).1 hmem
    have hne := CFSG.HardMathSupport.Solomon.Coordinator.barX_gLBConj_ne haJY hbY hbN
    rw [CFSG.HardMathSupport.Timmesfeld.Balance.Alt.barX_gLBConj p hbY J] at hne
    exact hne heq
  have hg1 : g ≠ 1 := fun h => hbN' (h ▸ Subgroup.one_mem _)
  have hgord5 : orderOf g = 5 := by
    have := orderOf_eq_prime hgp hg1
    rw [this, hp5]
  have hZJ : Subgroup.center (PQuot p J) = ⊥ :=
    center_pQuot_eq_bot_of_type167J H.hp H.hp2 haJY H.htype
  obtain ⟨E, hEY, hEab, hEcard⟩ := e6_four_normalizes_aux5 H.hp haJY hZJ hgord5 hbN'
  exact ⟨E, hEY.trans hYleX, hEab, by rwa [hp5] at hEcard⟩

theorem e6_four_normalizes {p : ℕ} {B X D J : Subgroup Ω} {x : Ω} (H : ExcHyp p B X D J x) (hp5 : p = 5)
    (hZ : Subgroup.center ↥X = ⊥) (hE : catalogIs (PSimple p X) ExcE6FourIdx) (hL : LabelOf X ⟨.E6, 0, 2⟩) :
    B ⊓ X ≤ Subgroup.normalizer (J : Set Ω) := by
  intro b hb
  by_contra hbN
  obtain ⟨E, hEX, hEab, hEcard5⟩ := e6_four_normalizes_aux6 H hp5 hZ hE hL hb hbN
  have hEp : IsPGroup p ↥E := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hEab.2 (x : Ω) x.2⟩
  have hEpsub : IsPGroup p ↥(E.subgroupOf X) :=
    hEp.comap_of_injective X.subtype X.subtype_injective
  have hEpsub5 : IsPGroup 5 ↥(E.subgroupOf X) := by rwa [hp5] at hEpsub
  obtain ⟨P, hEP⟩ := hEpsub5.exists_le_sylow
  have hMark : CFSG.Assembly.E6FourMark ↥X := by
    refine CFSG.Assembly.standardTypeRecognitionMarking_mono ?_ hL
    intro lab R _ I F θ hlab
    rw [hlab]
    exact ⟨rfl, rfl⟩
  have hPcard : Nat.card P = 5 ^ 4 := CFSG.Assembly.e6FourSylowFive_holds ↥X hMark hZ P
  have hsubcard : Nat.card ↥(E.subgroupOf X) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv
  have hle : Nat.card E ≤ 5 ^ 4 := by
    have h2 : Nat.card ↥(E.subgroupOf X) ≤ Nat.card ↥P :=
      Finite.card_le_of_embedding
        ⟨fun z : ↥(E.subgroupOf X) => (⟨z.1, hEP z.2⟩ : ↥P), by
          intro a b hab
          apply Subtype.ext
          exact congrArg (fun w : ↥P => (w : ↥X)) hab⟩
    calc Nat.card E = Nat.card ↥(E.subgroupOf X) := hsubcard.symm
      _ ≤ Nat.card ↥P := h2
      _ = 5 ^ 4 := hPcard
  have hcontra : (5 : ℕ) ^ 5 ≤ 5 ^ 4 := le_trans hEcard5 hle
  norm_num at hcontra

open TauCeti

private theorem e6_four_subcomp_aux1 {S : Type} [Group S]
    (h : CFSG.Blueprint.LieModel S .POmegaMinus 4 2 2) : catalogIs S ExcE6SubIdx := by
  have hS : StatedClassicalModel S .POmegaMinus 4 2 2 :=
    h.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  obtain ⟨K, hfield, hfinite, hK, b, c, hirr, ⟨θ⟩⟩ := hS.2
  let _ := hfield
  let _ := hfinite
  let q : PrimePower := ⟨2, 2, Nat.prime_two, by norm_num⟩
  have hv : (LieTypeIndex.twistedD 4 q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨by norm_num, not_false⟩
  obtain ⟨b₀, c₀, hirr₀, ⟨eT⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid 4 q hv
  obtain ⟨φ⟩ := CFSG.ClassicalModels.nonempty_ringEquiv_validIndex_fixedField ⟨.twistedD 4 q, hv⟩ K (by
    simp [ValidLieTypeIndex.fieldOrder, q, hK])
  have _ : Finite ↥(ValidLieTypeIndex.fixedField ⟨.twistedD 4 q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  obtain ⟨e2⟩ := CFSG.Blueprint.EvenSource.nonempty_statedOmegaMinus_equiv (n := 4) (by norm_num)
    (CFSG.ClassicalInvolution.Upgrade.irreducible_map φ hirr) hirr₀
  let e1 := CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
    (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp (n := 4) (b := b) (c := c) φ rfl rfl))
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  refine ⟨.lie ⟨.twistedD 4 q, hv⟩, ?_, ⟨((θ.trans e1).trans e2).trans eT.symm⟩⟩
  simp only [ExcE6SubIdx, onLie]
  norm_num [q, PrimePower.card_def]

private theorem e6_four_subcomp_aux2 {S : Type} [Group S]
    (h : CFSG.Blueprint.LieModel S .PSL 6 2 2) : catalogIs S ExcE6SubIdx := by
  have hS : StatedClassicalModel S .PSL 6 2 2 :=
    h.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  obtain ⟨K, hfield, hfinite, hK, e⟩ := hS.2
  let _ := hfield
  let _ := hfinite
  obtain ⟨e⟩ := e
  have hp : Nat.Prime 2 := Nat.prime_two
  let _ : Fact (Nat.Prime 2) := ⟨hp⟩
  let q : PrimePower := ⟨2, 2, hp, by norm_num⟩
  have hdup : ¬ (LieTypeIndex.A 5 q).IsDuplicateRepresentative := by
    rw [LieTypeIndex.isDuplicateRepresentative_iff]
    simp only [PrimePower.card_def, q]
    rintro (⟨hr1, -⟩ | ⟨hr2, -⟩ | ⟨hr3, hq⟩)
    · omega
    · omega
    · norm_num at hq
  have hv : (LieTypeIndex.A 5 q).Valid :=
    CFSG.ClassicalModels.linearCatalog_index_valid 6 2 2 hS.1 hdup
  let eK := CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 6 2 2 (by norm_num) hK
  have hdim : 5 + 1 = 6 := by norm_num
  have eC := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 5 q hv
  have eC' : (ValidLieTypeIndex.Group ⟨LieTypeIndex.A 5 q, hv⟩) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 6) (GaloisField 2 2) := by
    rw [hdim] at eC
    exact eC
  refine ⟨.lie ⟨LieTypeIndex.A 5 q, hv⟩, ?_, ⟨(e.trans eK).trans eC'.symm⟩⟩
  simp only [ExcE6SubIdx, onLie]
  norm_num [q, PrimePower.card_def]

private theorem e6_four_subcomp_aux3 {p : ℕ} {B X J : Subgroup Ω} {a : Ω}
    (hB : IsElemAbelian p B) (hX : CFSG.Open.IsQuasisimple ↥X) (hL : LabelOf X ⟨.E6, 0, 2⟩)
    (haA : a ∈ B ⊓ X) (haX : a ∉ cs X) (haJ : GLAPComponent p (X ⊓ cx a) J) (hp5 : p = 5) :
    CFSG.Open.IsQuasisimple ↥J := by
  subst p
  have ha1 : a ≠ 1 := fun h => haX (by rw [h]; exact Subgroup.one_mem _)
  have hK : IsChev2 X :=
    CFSG.Assembly.standardTypeRecognitionMarking_mono (fun _ _ _ _ _ _ _ => trivial) hL
  have hord : orderOf a = 5 := by
    refine orderOf_eq_prime ?_ ha1
    simpa using hB.2 a haA.1
  exact centQuasiAt_holds Ω X a 5 Nat.prime_five (by norm_num) hK hX haA.2
    ⟨5, Nat.prime_five, by norm_num, hord⟩ J haJ

private theorem e6_four_subcomp_aux4 {p : ℕ} {X J : Subgroup Ω} {a : Ω} (haX : a ∈ X)
    (haJ : GLAPComponent p (X ⊓ cx a) J) (hJX : J ≤ X) (hqJ : CFSG.Open.IsQuasisimple ↥J) :
    CFSG.Open.IsComponentOf (J.subgroupOf X) (Subgroup.centralizer ({⟨a, haX⟩} : Set ↥X)) := by
  have hcent : Subgroup.centralizer ({(⟨a, haX⟩ : ↥X)} : Set ↥X) = (X ⊓ cx a).subgroupOf X := by
    ext z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hz; exact ⟨z.2, by simpa using congrArg Subtype.val hz⟩
    · rintro ⟨-, hz⟩; exact Subtype.ext (by simpa using hz)
  rw [hcent]
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact Subgroup.mem_subgroupOf.mpr (haJ.1 (Subgroup.mem_subgroupOf.mp hz))
  · exact CFSG.Open.IsSubnormal.comap X.subtype haJ.2.1
  · exact (CFSG.Open.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hJX)).2 hqJ

private theorem e6_four_subcomp_aux5 {B X J : Subgroup Ω}
    (hN : B ⊓ X ≤ Subgroup.normalizer (J : Set Ω)) :
    (B ⊓ X).subgroupOf X ≤ Subgroup.normalizer ((J.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
  intro u hu
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  have hu' : (u : Ω) ∈ B ⊓ X := hu
  have hiff := Subgroup.mem_normalizer_iff.mp (hN hu') (h : Ω)
  constructor
  · intro hh
    show ((u * h * u⁻¹ : ↥X) : Ω) ∈ J
    simpa using hiff.mp hh
  · intro hh
    exact hiff.mpr (by simpa using hh)

private theorem e6_four_subcomp_aux6 {B J X : Subgroup Ω} {a : Ω} (haX : a ∈ X) (hJX : J ≤ X)
    (hAJ : (B ⊓ X) ⊓ cs J = Subgroup.zpowers a) :
    (B ⊓ X).subgroupOf X ⊓
        Subgroup.centralizer ((J.subgroupOf X : Subgroup ↥X) : Set ↥X) =
      Subgroup.zpowers (⟨a, haX⟩ : ↥X) := by
  have hcentJ : Subgroup.centralizer ((J.subgroupOf X : Subgroup ↥X) : Set ↥X) =
      (cs J).subgroupOf X := by
    ext z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hz j hj
      exact congrArg Subtype.val (hz ⟨j, hJX hj⟩ (Subgroup.mem_subgroupOf.mpr hj))
    · intro hz j hj
      exact Subtype.ext (hz (j : Ω) (Subgroup.mem_subgroupOf.mp hj))
  rw [hcentJ]
  have hinf : (B ⊓ X).subgroupOf X ⊓ (cs J).subgroupOf X = ((B ⊓ X) ⊓ cs J).subgroupOf X := rfl
  rw [hinf, hAJ]
  ext z
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, Subtype.ext hk⟩
  · rintro ⟨k, hk⟩; exact ⟨k, Subtype.ext_iff.mp hk⟩

private theorem e6_four_subcomp_aux7 {J X : Subgroup Ω}
    (hsub : CFSG.Assembly.E6FourSubcompMark ↥(J.subgroupOf X)) :
    catalogIs (↥(J.subgroupOf X) ⧸ Subgroup.center ↥(J.subgroupOf X)) ExcE6SubIdx := by
  obtain ⟨lab, _hLam, hn, hshape, hM⟩ := CFSG.Assembly.e6Four_subcompMark_model hsub
  have hlab : lab = ⟨.twD, 4, 2⟩ ∨ lab = ⟨.A, 5, 2⟩ := by
    obtain ⟨tg, r, m⟩ := lab
    have hm : m = 2 := hn
    rcases hshape with ⟨ht, hr⟩ | ⟨ht, hr⟩
    · left; subst ht; subst hr; subst hm; rfl
    · right; subst ht; subst hr; subst hm; rfl
  rcases hlab with rfl | rfl
  · refine e6_four_subcomp_aux1 ?_
    simp only [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
      CFSG.StandardType.markRank, CFSG.StandardType.markChar, CFSG.StandardType.markDeg] at hM
    norm_num at hM
    exact hM
  · exact e6_four_subcomp_aux2 (by
      simpa only [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
        CFSG.StandardType.markRank, CFSG.StandardType.markChar, CFSG.StandardType.markDeg]
        using hM)

private theorem e6_four_subcomp_aux8 {p : ℕ} {X J : Subgroup Ω} {a : Ω}
    (h : catalogIs (↥(J.subgroupOf X) ⧸ Subgroup.center ↥(J.subgroupOf X)) ExcE6SubIdx)
    (hJX : J ≤ X) (haJ : GLAPComponent p (X ⊓ cx a) J) (hqJ : CFSG.Open.IsQuasisimple ↥J)
    (hp5 : p = 5) : catalogIs (PSimple p J) ExcE6SubIdx := by
  subst p
  obtain ⟨i, hi, ⟨e'⟩⟩ := h
  have eJ : ↥(J.subgroupOf X) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJX
  have eZ : ↥(J.subgroupOf X) ⧸ Subgroup.center ↥(J.subgroupOf X) ≃* ↥J ⧸ Subgroup.center ↥J :=
    QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)
  obtain ⟨eP⟩ := I141F.centerQuot_equiv_pSimple Nat.prime_five haJ hqJ
  exact ⟨i, hi, ⟨(eZ.trans eP).symm.trans e'⟩⟩

theorem e6_four_subcomp {p : ℕ} {B X D J : Subgroup Ω} {x : Ω} (H : ExcHyp p B X D J x) (hp5 : p = 5)
    (hZ : Subgroup.center ↥X = ⊥) (hE : catalogIs (PSimple p X) ExcE6FourIdx) (hL : LabelOf X ⟨.E6, 0, 2⟩)
    {a : Ω} (haA : a ∈ B ⊓ X) (haX : a ∉ cs X) (haJ : GLAPComponent p (X ⊓ cx a) J)
    (hA : Nat.card ↥(B ⊓ X) = p ^ 4) (hAJ : (B ⊓ X) ⊓ cs J = Subgroup.zpowers a)
    (hN : B ⊓ X ≤ Subgroup.normalizer (J : Set Ω)) : catalogIs (PSimple p J) ExcE6SubIdx := by
  have ha1 : a ≠ 1 := fun h => haX (by rw [h]; exact Subgroup.one_mem _)
  have haXmem : a ∈ X := haA.2
  have hqJ := e6_four_subcomp_aux3 H.hB H.hX hL haA haX haJ hp5
  let s : ↥X := ⟨a, haXmem⟩
  let A : Subgroup ↥X := (B ⊓ X).subgroupOf X
  have hAcard : Nat.card A = p ^ 4 := by
    rw [show Nat.card A = Nat.card ↥(B ⊓ X) from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, hA]
  have hAcard5 : Nat.card A = 5 ^ 4 := by rw [hAcard, hp5]
  have hsA : s ∈ A := by rw [Subgroup.mem_subgroupOf]; exact haA
  have hs1 : s ≠ 1 := fun h => ha1 (Subtype.ext_iff.mp h)
  have hcomp := e6_four_subcomp_aux4 haXmem haJ H.hJX hqJ
  have hAN := e6_four_subcomp_aux5 hN
  have hAC := e6_four_subcomp_aux6 haXmem H.hJX hAJ
  have hmark : CFSG.Assembly.E6FourMark ↥X := by
    refine CFSG.Assembly.standardTypeRecognitionMarking_mono ?_ hL
    rintro _ _ _ _ _ _ rfl
    exact ⟨rfl, rfl⟩
  have hcomp' : CFSG.Assembly.IsComponentOf (J.subgroupOf X)
      (Subgroup.centralizer ({s} : Set ↥X)) :=
    (CFSG.Assembly.isComponentOf_iff_open).2 hcomp
  have hsub : CFSG.Assembly.E6FourSubcompMark ↥(J.subgroupOf X) :=
    CFSG.Assembly.e6FourCentFive_holds ↥X hmark hZ A hAcard5 s hsA hs1 (J.subgroupOf X) hcomp' hAN hAC
  exact e6_four_subcomp_aux8 (e6_four_subcomp_aux7 hsub) H.hJX haJ hqJ hp5

private theorem not_catalogIs_e6Sub_of_omPA_aux1 {S : Type} [Group S] [Finite S]
    (hb : CatDistinct.OrderBridge) (hsub : catalogIs S ExcE6SubIdx) :
    padicValNat 2 (Nat.card S) = 24 ∨ padicValNat 2 (Nat.card S) = 30 := by
  obtain ⟨j, hj, ⟨e'⟩⟩ := hsub
  cases j with
  | cyclic a b => exact absurd hj (by simp [ExcE6SubIdx, onLie])
  | sporadic a => exact absurd hj (by simp [ExcE6SubIdx, onLie])
  | alternating a b => exact absurd hj (by simp [ExcE6SubIdx, onLie])
  | lie idx =>
    obtain ⟨d, hd⟩ := idx
    cases d with
    | twistedD r q =>
      simp only [ExcE6SubIdx, onLie] at hj
      obtain ⟨hr, hq⟩ := hj
      subst hr
      have hq2 : q.card = 2 ^ 2 := by rw [hq]; norm_num
      have hcat : catalogIs S (isOmMA 4 (2 ^ 2)) :=
        ⟨.lie ⟨.twistedD 4 q, hd⟩, Or.inl ⟨rfl, hq2⟩, ⟨e'⟩⟩
      obtain ⟨-, hv24⟩ := CFSG.LocalAnalysis.GLTheoremA.S172.v2_isOmMA hb (by norm_num : 1 ≤ 2) hcat
      exact Or.inl (by rw [hv24])
    | A r q =>
      simp only [ExcE6SubIdx, onLie] at hj
      obtain ⟨hr, hq⟩ := hj
      subst hr
      have hq2 : q.card = 2 ^ 2 := by rw [hq]; norm_num
      have hcat : catalogIs S (isLnA 6 (2 ^ 2)) :=
        ⟨.lie ⟨.A 5 q, hd⟩, Or.inl ⟨rfl, hq2⟩, ⟨e'⟩⟩
      obtain ⟨-, hv60⟩ := CFSG.LocalAnalysis.GLTheoremA.S172.v2_isLnA hb (by norm_num : 1 ≤ 2) hcat
      exact Or.inr (by omega)
    | _ => exact absurd hj (by simp [ExcE6SubIdx, onLie])

private theorem not_catalogIs_e6Sub_of_omPA_aux2 {n k : ℕ} (hn : Odd n) (hn3 : 3 ≤ n)
    (hpk : 5 ∣ 2 ^ k + 1) (hV : k * (n * (n - 1)) = 24 ∨ k * (n * (n - 1)) = 30) : False := by
  rcases hV with hV | hV
  · have hdvd : n * (n - 1) ∣ 24 := ⟨k, by rw [mul_comm]; exact hV.symm⟩
    have hnle : n ≤ 5 := by
      by_contra hc
      have hc6 : 6 ≤ n := by omega
      have h1 : 6 * 5 ≤ n * (n - 1) := Nat.mul_le_mul hc6 (by omega)
      have h2 := Nat.le_of_dvd (by norm_num : 0 < 24) hdvd
      omega
    interval_cases n
    · have hk4 : k = 4 := by omega
      subst hk4
      norm_num at hpk
    · obtain ⟨m, hm⟩ := hn; omega
    · omega
  · have hdvd : n * (n - 1) ∣ 30 := ⟨k, by rw [mul_comm]; exact hV.symm⟩
    have hnle : n ≤ 6 := by
      by_contra hc
      have hc7 : 7 ≤ n := by omega
      have h1 : 7 * 6 ≤ n * (n - 1) := Nat.mul_le_mul hc7 (by omega)
      have h2 := Nat.le_of_dvd (by norm_num : 0 < 30) hdvd
      omega
    interval_cases n
    · have hk5 : k = 5 := by omega
      subst hk5
      norm_num at hpk
    · obtain ⟨m, hm⟩ := hn; omega
    · omega
    · obtain ⟨m, hm⟩ := hn; omega

theorem not_catalogIs_e6Sub_of_omPA {S : Type} [Group S] [Finite S] {p n k : ℕ} (hp5 : p = 5) (hn : Odd n) (hn3 : 3 ≤ n)
    (hk : 1 ≤ k) (hpk : p ∣ 2 ^ k + 1) (h : catalogIs S (isOmPA n (2 ^ k))) : ¬ catalogIs S ExcE6SubIdx := by
  intro hsub
  subst p
  have hb : CatDistinct.OrderBridge := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
  obtain ⟨-, hv⟩ := CFSG.LocalAnalysis.GLTheoremA.S172.v2_isOmPA hb hk h
  refine not_catalogIs_e6Sub_of_omPA_aux2 hn hn3 hpk ?_
  rcases not_catalogIs_e6Sub_of_omPA_aux1 hb hsub with h | h
  · left; rw [hv] at h; exact h
  · right; rw [hv] at h; exact h

theorem false_of_exc_E6 {p : ℕ} {B X D J : Subgroup Ω} {x : Ω} (H : ExcHyp p B X D J x) (hp3 : p ≠ 3)
    (hE6 : catalogIs (PSimple p X) ExcE6Idx) : False := by
  obtain ⟨n, k, hn, hn3, hk, hpk, hJ⟩ := type167J_case_c_of_ne_three H.htype hp3
  have hE6k := e6_fieldRel H hn3 hk hJ hE6
  obtain ⟨hp5, hZ, hE4, hL⟩ := e6_four_of_halfSplit H hp3 hpk hE6k
  obtain ⟨a, haA, haX, haJ, hA, hAJ⟩ := e6_four_sylow_data H hp5 hZ hE4 hL
  have hN := e6_four_normalizes H hp5 hZ hE4 hL
  exact not_catalogIs_e6Sub_of_omPA hp5 hn hn3 hk hpk hJ
    (e6_four_subcomp H hp5 hZ hE4 hL haA haX haJ hA hAJ hN)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.I167

end
