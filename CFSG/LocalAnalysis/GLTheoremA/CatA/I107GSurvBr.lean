module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48LayerY
public import CFSG.LocalAnalysis.StandardType.MarkingChevalley
public import CFSG.Adapters.TauCetiExceptional.EvenD4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107G

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly TauCeti CFSG.LocalAnalysis.GLTheoremA.CatB

abbrev pp2 : PrimePower := ⟨2, 1, Nat.prime_two, Nat.one_pos⟩

theorem catalogIs_of_model {X M : Type} [Group X] [Group M] {P : CFSGIndex → Prop} (i0 : CFSGIndex) (hP0 : P i0)
    (hbr : ∀ {S : Type} [Group S], catalogIs S P → Nonempty (S ≃* M)) (e : X ≃* M) : catalogIs X P := by
  obtain ⟨f⟩ := hbr (S := i0.Group) ⟨i0, hP0, ⟨MulEquiv.refl _⟩⟩
  exact ⟨i0, hP0, ⟨e.trans f.symm⟩⟩

theorem catalogIs_isList107_of {X : Type} [Group X] {P : CFSGIndex → Prop}
    (hP : ∀ i, P i → S9.isList107 i) (h : catalogIs X P) : catalogIs X S9.isList107 := by
  obtain ⟨i, hi, e⟩ := h
  exact ⟨i, hP i hi, e⟩

theorem valid_B3 : (LieTypeIndex.B 3 pp2).Valid := by
  rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff, LieTypeIndex.isDuplicateRepresentative_iff]
  simp [pp2]

theorem valid_D4 : (LieTypeIndex.D 4 pp2).Valid := by
  rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff, LieTypeIndex.isDuplicateRepresentative_iff]
  simp [pp2]

theorem valid_twistedA4 : (LieTypeIndex.twistedA 4 pp2).Valid := by
  rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff, LieTypeIndex.isDuplicateRepresentative_iff]
  simp [pp2]

theorem valid_trialityD4 : (LieTypeIndex.trialityD4 pp2).Valid := by
  rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff, LieTypeIndex.isDuplicateRepresentative_iff]
  simp [pp2]

theorem catalogIs_sp6_recipe {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    catalogIs (LargeEvenProj (LargeEvenSpGroup K 3)) S9.isList107 := by
  obtain ⟨φ⟩ := exists_ringEquiv_zmod_two hK
  have e : LargeEvenProj (LargeEvenSpGroup K 3) ≃* CFSG.Sporadic.Co2Smith.Sp62 :=
    statedProjEquivZMod2 φ (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp φ 3)
  have hP : S9.isSp6two (CFSGIndex.lie ⟨.B 3 pp2, valid_B3⟩) := by
    show pp2.card = 2
    simp [pp2, TauCeti.PrimePower.card_def]
  exact catalogIs_isList107_of (fun i hi => Or.inl hi)
    (catalogIs_of_model (CFSGIndex.lie ⟨.B 3 pp2, valid_B3⟩) hP
      (fun {S} _ h => bridge_sp6two h) e)

theorem catalogIs_u4_recipe {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    catalogIs (LargeEvenProj (LargeEvenSUGroup (Fin 4) K 2)) S9.isList107 :=
  catalogIs_isList107_of (fun i hi => Or.inr (Or.inl hi))
    (catalogIs_u4two_of_statedProj hK (MulEquiv.refl _))

theorem catalogIs_u5_recipe {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    catalogIs (LargeEvenProj (LargeEvenSUGroup (Fin 5) K 2)) S9.isList107 := by
  have hP : S9.isU5two (CFSGIndex.lie ⟨.twistedA 4 pp2, valid_twistedA4⟩) := by
    show pp2.card = 2
    simp [pp2, TauCeti.PrimePower.card_def]
  exact catalogIs_isList107_of (fun i hi => Or.inr (Or.inr (Or.inl hi)))
    (catalogIs_of_model (CFSGIndex.lie ⟨.twistedA 4 pp2, valid_twistedA4⟩) hP
      (fun {S} _ h => bridge_u5two h)
      (CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.statedProjEquiv (hK.trans (by norm_num))))

theorem catalogIs_u3_recipe {K : Type} [Field K] [Finite K] (hK : Nat.card K = 64) :
    catalogIs (LargeEvenProj (LargeEvenSUGroup (Fin 3) K 8)) S9.isList107 :=
  catalogIs_isList107_of (fun i hi => Or.inr (Or.inr (Or.inr (Or.inl hi))))
    (CFSG.LocalAnalysis.GLTheoremA.CatB.U48.catalogIs_u3eight_of_statedProj hK (MulEquiv.refl _))

theorem catalogIs_d4_recipe {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    catalogIs (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))) S9.isList107 := by
  obtain ⟨φ⟩ := exists_ringEquiv_zmod_two hK
  have hP : S9.isD4two (CFSGIndex.lie ⟨.D 4 pp2, valid_D4⟩) := by
    show pp2.card = 2
    simp [pp2, TauCeti.PrimePower.card_def]
  have e : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)) ≃* CFSG.AGLEmbedding.Om8 :=
    statedProjEquivZMod2 φ (glCongr_statedOmega_plus φ 4)
  exact catalogIs_isList107_of (fun i hi => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hi)))))
    (catalogIs_of_model (CFSGIndex.lie ⟨.D 4 pp2, valid_D4⟩) hP
      (fun {S} _ h => bridge_d4two h) e)

theorem catalogIs_td4_recipe
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 3) :
    catalogIs (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 1))
      S9.isTD4two := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  have hc : Fintype.card K = Fintype.card (GaloisField 2 3) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, GaloisField.card 2 3 (by norm_num)]
    norm_num
  let ψ : K ≃+* GaloisField 2 3 := FiniteField.ringEquivOfCardEq hc
  let σ : K →+* K := ψ.symm.toRingHom.comp ((frobenius (GaloisField 2 3) 2).comp ψ.toRingHom)
  have hσ : ∀ c : K, σ c = c ^ 2 ^ 1 := by
    intro c
    simp [σ, frobenius_def, map_pow]
  obtain ⟨e1⟩ := CFSG.StandardType.centerQuot_twistedH_equiv K CFSG.Blueprint.Chevalley.TwistTag.D4 1 σ hσ
  have hK3 : Nat.card K = pp2.card ^ CFSG.Blueprint.Chevalley.TwistTag.D4.order := by
    rw [hK, TauCeti.PrimePower.card_def]
    rfl
  have hσ' : ∀ x : K, σ x = x ^ pp2.card := fun x => by
    rw [hσ x, TauCeti.PrimePower.card_def]
  obtain ⟨e2⟩ := CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 pp2 valid_trialityD4 rfl K hK3 σ hσ'
  have hP : S9.isTD4two (CFSGIndex.lie ⟨.trialityD4 pp2, valid_trialityD4⟩) := by
    show pp2.card = 2
    simp [pp2, TauCeti.PrimePower.card_def]
  exact ⟨CFSGIndex.lie ⟨.trialityD4 pp2, valid_trialityD4⟩, hP, ⟨e1.trans e2⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.I107G

end
