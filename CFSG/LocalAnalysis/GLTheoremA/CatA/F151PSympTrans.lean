module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151Defs
import CFSG.Adapters.TauCetiLieModels
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open TauCeti
open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10

private theorem sympTrans_indAut_zpow {G : Type} [Group G] {p : ℕ} {L : Subgroup G} {b : G}
    (hbN : b ∈ Subgroup.normalizer (L : Set G)) (k : ℤ) :
    MI.indAut p L (b ^ k) (Subgroup.zpow_mem _ hbN k) = MI.indAut p L b hbN ^ k := by
  unfold MI.indAut
  rw [← map_zpow]
  congr 1
  exact Subtype.ext (by simp [zpow_neg, inv_zpow])

private theorem sympTrans_congr_indAut {G G' : Type} [Group G] [Group G']
    {p : ℕ} {J : Subgroup G} {J' : Subgroup G'} {b : G} {b' : G'}
    (e : PSimple p J ≃* PSimple p J')
    (hbN : b ∈ Subgroup.normalizer (J : Set G))
    (hb'N : b' ∈ Subgroup.normalizer (J' : Set G'))
    (hIso : ∀ s s' : PSimple p J, indRelS p J b s s' →
      indRelS p J' b' (e s) (e s')) :
    MulAut.congr e (MI.indAut p J b hbN) = MI.indAut p J' b' hb'N := by
  ext s
  obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (e.symm s)
  have hs : s = e (QuotientGroup.mk q) := by rw [hq, MulEquiv.apply_symm_apply]
  obtain ⟨q', hq'⟩ := MI.indRel_total hbN q
  have hrelS : indRelS p J b (QuotientGroup.mk q) (QuotientGroup.mk q') :=
    ⟨q, q', hq', rfl, rfl⟩
  obtain ⟨r, r', hr, hrq, hrq'⟩ := hIso _ _ hrelS
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, ← hq,
    MI.indAut_apply_mk hbN hq', ← hrq', ← MI.indAut_apply_mk hb'N hr, hrq, ← hs]

private theorem sympTrans_congr_indAut_zpow {G G' : Type} [Group G] [Group G']
    {p : ℕ} {J : Subgroup G} {J' : Subgroup G'} {b : G} {b' : G'}
    (e : PSimple p J ≃* PSimple p J')
    (hbN : b ∈ Subgroup.normalizer (J : Set G))
    (hb'N : b' ∈ Subgroup.normalizer (J' : Set G'))
    (hIso : ∀ s s' : PSimple p J, indRelS p J b s s' →
      indRelS p J' b' (e s) (e s')) (k : ℤ) :
    MulAut.congr e (MI.indAut p J (b ^ k) (Subgroup.zpow_mem _ hbN k)) =
      MI.indAut p J' (b' ^ k) (Subgroup.zpow_mem _ hb'N k) := by
  rw [sympTrans_indAut_zpow hbN k, sympTrans_indAut_zpow hb'N k, map_zpow,
    sympTrans_congr_indAut e hbN hb'N hIso]

private theorem sympTrans_markTransport : MarkTransport := by
  intro G G' _ _ _ _ p J J' b b' e hcomm hbN hIso hdiag'
  obtain ⟨hb'N, hmark'⟩ := hdiag'
  have hb'norm : b' ∈ Subgroup.normalizer (J' : Set G') := hb'N (Subgroup.mem_zpowers b')
  refine ⟨Subgroup.zpowers_le.2 hbN, ?_⟩
  refine lemma102_marking_transport hcomm e ?_ hmark'
  intro lab R _ I F θ hP
  intro a ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have hbk : b ^ k ∈ Subgroup.normalizer (J : Set G) := Subgroup.zpow_mem _ hbN k
  have hb'k : b' ^ k ∈ Subgroup.normalizer (J' : Set G') := Subgroup.zpow_mem _ hb'norm k
  obtain ⟨φ, hφI, hφ⟩ := hP (b' ^ k) (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b') k)
  refine ⟨φ, hφI, ?_⟩
  have h1 : φ = MulAut.congr θ (MI.indAut p J' (b' ^ k) hb'k) :=
    (MI.induces_indRel_iff hb'k θ).1 hφ
  have h2 : MulAut.congr e (MI.indAut p J (b ^ k) hbk) =
      MI.indAut p J' (b' ^ k) hb'k :=
    sympTrans_congr_indAut_zpow e hbN hb'norm hIso k
  have h3 : MulAut.congr (e.trans θ) (MI.indAut p J (b ^ k) hbk) =
      MulAut.congr θ (MI.indAut p J' (b' ^ k) hb'k) := by
    rw [← h2]
    ext y
    simp [MulAut.congr_apply]
  exact (MI.induces_indRel_iff hbk (e.trans θ)).2 (h1.trans h3.symm)

private theorem namesTag_psp_false (d : TauCeti.LieTypeIndex) (p f : ℕ) :
    ¬ CFSG.Models.NamesTag d .PSp p f := by
  cases d <;> simp [CFSG.Models.NamesTag]

private theorem shapeModelAt_symp_of_catalog {S : Type} [Group S] [Finite S] {p : ℕ}
    (hIso : ShapeModelIso) (hSymp : SympModel) (hp : p.Prime) (hp2 : p ≠ 2)
    (hcat : catalogIs S (onLie (CharTwoOf isSympIdx))) : ShapeModelAt S p := by
  obtain ⟨i, hi, ⟨e0⟩⟩ := hcat
  cases i with
  | cyclic n' hn' => exact hi.elim
  | alternating n' hn' => exact hi.elim
  | sporadic s => exact hi.elim
  | lie j =>
      obtain ⟨d, hv⟩ := j
      cases d with
      | A r q => exact absurd hi.1 (by simp [isSympIdx])
      | twistedA r q => exact absurd hi.1 (by simp [isSympIdx])
      | B r q =>
          have hq2 : q.p = 2 := by simpa using hi.2
          rcases CFSG.Models.lieModel_B r q hv (MulEquiv.refl _) with hPSp | hOdd
          · rw [hq2] at hPSp
            have hclass : StatedClassicalModel
                (ValidLieTypeIndex.Group ⟨LieTypeIndex.B r q, hv⟩) .PSp r 2 q.exponent := by
              rcases hPSp.2 with h | ⟨-, dd, hnt, -⟩
              · exact h
              · exact absurd hnt (namesTag_psp_false dd.1 2 q.exponent)
            obtain ⟨hadm, K, hKfield, hKfin, hcard, ⟨e1⟩⟩ := hclass
            letI : Field K := hKfield
            letI : Finite K := hKfin
            haveI : CharP K 2 := by
              haveI : Fintype K := Fintype.ofFinite K
              exact charP_of_card_eq_prime_pow (p := 2) (R := K)
                (by rw [← Nat.card_eq_fintype_card]; exact hcard)
            have hbot : (StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K) = ⊥ :=
              CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot
            have e2 : StatedProj (StatedSp r K) ≃* ↥(StatedSp r K) :=
              (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
            have full : S ≃* ↥(CFSG.Assembly.LargeEvenSpGroup K r) :=
              e0.trans (e1.trans e2)
            have h2r : 2 ≤ r := hadm.2.2.1
            have hne : ¬ (r = 2 ∧ Nat.card K = 2) := fun hc =>
              hadm.2.2.2 (by rw [hc.1, hcard.symm, hc.2])
            have hSympK : ShapeModelAt ↥(CFSG.Assembly.LargeEvenSpGroup K r) p :=
              hSymp r q.exponent K h2r hne hcard p hp hp2
            exact hIso sympTrans_markTransport (↥(CFSG.Assembly.LargeEvenSpGroup K r)) S
              full.symm p hSympK
          · exact absurd hq2 hOdd.1.2.2.2
      | C r q =>
          have hq2 : q.p = 2 := by simpa using hi.2
          have hC : q.p ≠ 2 := by
            have h := (LieTypeIndex.valid_iff (.C r q)).mp hv
            exact ((LieTypeIndex.inStandardRange_iff (.C r q)).mp h.1).2
          exact absurd hq2 hC
      | D r q => exact absurd hi.1 (by simp [isSympIdx])
      | twistedD r q => exact absurd hi.1 (by simp [isSympIdx])
      | E6 q => exact absurd hi.1 (by simp [isSympIdx])
      | E7 q => exact absurd hi.1 (by simp [isSympIdx])
      | E8 q => exact absurd hi.1 (by simp [isSympIdx])
      | F4 q => exact absurd hi.1 (by simp [isSympIdx])
      | G2 q => exact absurd hi.1 (by simp [isSympIdx])
      | twistedE6 q => exact absurd hi.1 (by simp [isSympIdx])
      | trialityD4 q => exact absurd hi.1 (by simp [isSympIdx])
      | suzuki m => exact absurd hi.1 (by simp [isSympIdx])
      | reeG2 m => exact absurd hi.1 (by simp [isSympIdx])
      | reeF4 m => exact absurd hi.1 (by simp [isSympIdx])
      | tits => exact absurd hi.1 (by simp [isSympIdx])

theorem sympTrans_holds : SympTrans := by
  unfold SympTrans
  intro hIso hSymp
  unfold SimpleModel
  intro S _ _ p hp hp2 hcat _
  exact shapeModelAt_symp_of_catalog hIso hSymp hp hp2 hcat

end CFSG.LocalAnalysis.GLTheoremA.F151

end
