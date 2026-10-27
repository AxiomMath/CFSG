module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151Defs
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInOrthTransMark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA

private theorem isOrthIdx_iff {idx : TauCeti.LieTypeIndex} :
    isOrthIdx idx ↔ ∃ (n : ℕ) (q : TauCeti.PrimePower),
      idx = .D n q ∨ idx = .twistedD n q := by
  cases idx <;> simp [isOrthIdx]

private theorem indAut_zpow {G : Type} [Group G] {p : ℕ} {L : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (L : Set G)) (k : ℤ)
    (hk : y ^ k ∈ Subgroup.normalizer (L : Set G)) :
    MI.indAut p L (y ^ k) hk = (MI.indAut p L y hy) ^ k := by
  unfold MI.indAut
  rw [← map_zpow]
  congr 1
  apply Subtype.ext
  simp [zpow_neg, inv_zpow']

private theorem markTransport_holds : MarkTransport := by
  intro G G' _ _ _ _ p J J' b b' e hcomm hb hpres hdiag
  obtain ⟨hzp, -, lab, hlab, hraw⟩ := hdiag
  have hb' : b' ∈ Subgroup.normalizer (J' : Set G') := hzp (Subgroup.mem_zpowers b')
  have key : MulAut.congr e (MI.indAut p J b hb) = MI.indAut p J' b' hb' := by
    refine MulEquiv.ext fun s => ?_
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (e.symm s)
    have hs : s = e (QuotientGroup.mk q) := by rw [hq, MulEquiv.apply_symm_apply]
    obtain ⟨q', hq'⟩ := MI.indRel_total (p := p) (L := J) hb q
    have h1 := MI.indAut_apply_mk hb hq'
    have h2 : indRelS p J b (QuotientGroup.mk q) (QuotientGroup.mk q') :=
      ⟨q, q', hq', rfl, rfl⟩
    obtain ⟨r, r', hrr', hr, hr'⟩ := hpres _ _ h2
    have h4 := MI.indAut_apply_mk hb' hrr'
    rw [hs]
    calc
      (MulAut.congr e (MI.indAut p J b hb)) (e (QuotientGroup.mk q))
          = e ((MI.indAut p J b hb) (QuotientGroup.mk q)) := by
            simp [MulAut.congr_apply, MulEquiv.trans_apply]
      _ = e (QuotientGroup.mk q') := by rw [h1]
      _ = QuotientGroup.mk r' := hr'.symm
      _ = (MI.indAut p J' b' hb') (QuotientGroup.mk r) := h4.symm
      _ = (MI.indAut p J' b' hb') (e (QuotientGroup.mk q)) := by rw [hr.symm]
  refine ⟨Subgroup.zpowers_le.2 hb, hcomm, lab, hlab, ?_⟩
  refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  refine ⟨hs, hna, e.trans θ, ?_⟩
  intro c hc
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  have hb'k : b' ^ k ∈ Subgroup.zpowers b' := Subgroup.zpow_mem _ (Subgroup.mem_zpowers b') k
  obtain ⟨φ, hφI, hφ⟩ := hθ (b' ^ k) hb'k
  refine ⟨φ, hφI, ?_⟩
  have hbk : b ^ k ∈ Subgroup.normalizer (J : Set G) := Subgroup.zpow_mem _ hb k
  have hb'k' : b' ^ k ∈ Subgroup.normalizer (J' : Set G') := Subgroup.zpow_mem _ hb' k
  have hkeyk : MulAut.congr e (MI.indAut p J (b ^ k) hbk) =
      MI.indAut p J' (b' ^ k) hb'k' := by
    calc
      MulAut.congr e (MI.indAut p J (b ^ k) hbk)
          = MulAut.congr e ((MI.indAut p J b hb) ^ k) := by rw [indAut_zpow hb k hbk]
      _ = (MulAut.congr e (MI.indAut p J b hb)) ^ k :=
          map_zpow (MulAut.congr e).toMonoidHom _ k
      _ = (MI.indAut p J' b' hb') ^ k := by rw [key]
      _ = MI.indAut p J' (b' ^ k) hb'k' := (indAut_zpow hb' k hb'k').symm
  have hφ' := (MI.induces_indRel_iff hb'k' θ).1 hφ
  refine (MI.induces_indRel_iff hbk (e.trans θ)).2 ?_
  rw [hφ']
  calc
    MulAut.congr θ (MI.indAut p J' (b' ^ k) hb'k')
        = MulAut.congr θ (MulAut.congr e (MI.indAut p J (b ^ k) hbk)) := by rw [hkeyk]
    _ = MulAut.congr (e.trans θ) (MI.indAut p J (b ^ k) hbk) := by
        ext r
        simp [MulAut.congr_apply, MulEquiv.trans_apply]

theorem orthModelTrans_holds : OrthModelTrans := by
  intro hIso hPlus hMinus S _ _ p hp hp2 hcat hshape
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | lie d =>
    obtain ⟨idx, hvalid⟩ := d
    simp only [onLie, CharTwoOf] at hi
    obtain ⟨horth, hchar⟩ := hi
    rw [isOrthIdx_iff] at horth
    obtain ⟨m, q, rfl | rfl⟩ := horth
    · have hq2 : q.p = 2 := by simpa using hchar
      have hm4 : 4 ≤ m := by
        have h := hvalid
        rw [TauCeti.LieTypeIndex.valid_iff] at h
        simpa [TauCeti.LieTypeIndex.inStandardRange_iff] using h.1
      have hcatD : catalogIs S (onLie fun i => ∃ q' : TauCeti.PrimePower,
          i = .D m q' ∧ q'.card = 2 ^ q.exponent) := by
        refine ⟨.lie ⟨.D m q, hvalid⟩, ⟨q, rfl, ?_⟩, ⟨e⟩⟩
        rw [TauCeti.PrimePower.card_def, hq2]
      have hLM := T171Sh.lieModel_of_catalogIs_D hcatD
      have hclass := hLM.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
      obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨eS⟩⟩ := hclass
      letI : Field K := hKfield
      letI : Finite K := hKfinite
      have hplus := hPlus m q.exponent K hm4 hKcard p hp hp2
      have eS' : S ≃* CFSG.Assembly.LargeEvenProj
          (CFSG.Assembly.LargeEvenOmega (CFSG.Assembly.LargeEvenQPlus K m)) := eS
      exact (hIso markTransport_holds) _ _ eS'.symm p hplus
    · have hq2 : q.p = 2 := by simpa using hchar
      have hm4 : 4 ≤ m := by
        have h := hvalid
        rw [TauCeti.LieTypeIndex.valid_iff] at h
        exact TauCeti.LieTypeIndex.four_le_of_twistedD_inStandardRange h.1
      have hcatD : catalogIs S (onLie fun i => ∃ q' : TauCeti.PrimePower,
          i = .twistedD m q' ∧ q'.card = 2 ^ q.exponent) := by
        refine ⟨.lie ⟨.twistedD m q, hvalid⟩, ⟨q, rfl, ?_⟩, ⟨e⟩⟩
        rw [TauCeti.PrimePower.card_def, hq2]
      have hLM := T171Sh.lieModel_of_catalogIs_twistedD hcatD
      have hclass := hLM.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
      obtain ⟨-, K, hKfield, hKfinite, hKcard, b, c, hbc, ⟨eS⟩⟩ := hclass
      letI : Field K := hKfield
      letI : Finite K := hKfinite
      have hminus := hMinus m q.exponent K hm4 hKcard b c hbc p hp hp2
      have eS' : S ≃* CFSG.Assembly.LargeEvenProj
          (CFSG.Assembly.LargeEvenOmega (CFSG.Assembly.LargeEvenQMinus (m - 1) b c)) :=
        eS.trans (CFSG.StandardType.omegaMinusProjEquiv m b c).symm
      exact (hIso markTransport_holds) _ _ eS'.symm p hminus
  | cyclic n hn => simp [onLie] at hi
  | alternating n hn => simp [onLie] at hi
  | sporadic s => simp [onLie] at hi

end CFSG.LocalAnalysis.GLTheoremA.F151

end
