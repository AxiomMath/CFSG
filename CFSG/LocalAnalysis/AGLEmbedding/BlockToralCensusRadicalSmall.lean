module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusRadicalModels
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverSmall
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThree
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartOne.N143.Inspect613Even

public section

namespace CFSG.AGLEmbedding.ToralCensus

open Equiv CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge.Over
  CFSG.QuasithinUnique.L246C127 CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Unc25K1.Six CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

theorem RadicalSelfNormOver.of_sylow {X : Type*} [Group X] [Finite X] (T₀ : Sylow 2 X)
    (h : ∀ J : Subgroup X, Subgroup.normalizer ((T₀ : Subgroup X) : Set X) ≤ J →
      Subgroup.normalizer (pCoreOf 2 J : Set X) ≤ J) : RadicalSelfNormOver X := by
  intro T J hNJ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X T₀ T
  set φ : X ≃* X := MulAut.conj g with hφ
  have hT : (T : Subgroup X) = (T₀ : Subgroup X).map φ.toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hid : ∀ A : Subgroup X, (A.map φ.toMonoidHom).map φ.symm.toMonoidHom = A := fun A => by
    rw [Subgroup.map_map]
    simp
  have h0 := h (J.map φ.symm.toMonoidHom) (by
    rw [← hid (Subgroup.normalizer ((T₀ : Subgroup X) : Set X)),
      Subgroup.map_equiv_normalizer_eq, ← hT]
    exact Subgroup.map_mono hNJ)
  rw [pCoreOf_map_mulEquiv, ← Subgroup.map_equiv_normalizer_eq] at h0
  have h1 := Subgroup.map_mono (f := φ.toMonoidHom) h0
  have hid' : ∀ A : Subgroup X, (A.map φ.symm.toMonoidHom).map φ.toMonoidHom = A := fun A => by
    rw [Subgroup.map_map]
    simp
  rwa [hid', hid'] at h1

theorem normalizer_pCoreOf_le_of_latCert {n : ℕ} {A : Subgroup (Perm (Fin n))}
    (c : LatCert (Perm (Fin n))) (hM : Subgroup.closure {g | g ∈ c.mGens} = A)
    (hTA : Subgroup.closure {g | g ∈ c.tGens} ≤ A) (hc : c.check RN.enc = true)
    (hsz : ∀ s ∈ c.sizes, s = c.sizes.headD 0 ∨ s = 3 * c.sizes.headD 0 ∨ s = c.msize)
    (hlt : 3 * c.sizes.headD 0 < c.msize) [IsSimpleGroup ↥A]
    (hchar : ∀ Y : Subgroup ↥A, (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf A ≤ Y →
      Y = ⊤ ∨ CharTwo Y)
    (hT₀ : IsPGroup 2 ((Subgroup.closure {g | g ∈ c.tGens}).subgroupOf A))
    (J : Subgroup ↥A)
    (hNJ : Subgroup.normalizer
      (((Subgroup.closure {g | g ∈ c.tGens}).subgroupOf A : Subgroup ↥A) : Set ↥A) ≤ J) :
    Subgroup.normalizer (pCoreOf 2 J : Set ↥A) ≤ J := by
  subst hM
  set T₀ := (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf
    (Subgroup.closure {g | g ∈ c.mGens}) with hT₀def
  have hcl := c.closedOK_of_check hc
  have hszOK := c.sizesOK_of_check hc
  have hcardT : Nat.card T₀ = c.sizes.headD 0 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTA).toEquiv,
      c.card_t (rawIsEnc n) hcl hszOK]
  have hcardA : Nat.card ↥(Subgroup.closure {g | g ∈ c.mGens}) = c.msize :=
    c.card_m (rawIsEnc n) hcl hszOK
  have hmem : ∀ Y : Subgroup ↥(Subgroup.closure {g | g ∈ c.mGens}), T₀ ≤ Y →
      Nat.card Y ∈ c.sizes := fun Y hY => by
    obtain ⟨L, -, hLM, hYL, hL⟩ := c.overgroup_cases (rawIsEnc n) hc Y hY
    rw [hYL, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv]
    exact hL
  have hTJ : T₀ ≤ J := Subgroup.le_normalizer.trans hNJ
  have hJN : J ≤ Subgroup.normalizer (pCoreOf 2 J : Set _) := le_normalizer_pCoreOf 2 J
  have htop : ∀ Y : Subgroup ↥(Subgroup.closure {g | g ∈ c.mGens}), Nat.card Y = c.msize →
      Y = ⊤ := fun Y hY => Subgroup.eq_top_of_card_eq Y (by rw [hY, hcardA])
  have hpos : 0 < c.sizes.headD 0 := hcardT ▸ Nat.card_pos
  rcases hsz _ (hmem J hTJ) with hJ | hJ | hJ
  ·
    have hJT : J = T₀ := (Subgroup.eq_of_le_of_card_ge hTJ (by rw [hJ, hcardT])).symm
    have hO : pCoreOf 2 J = J := le_antisymm (pCoreOf_le 2 J)
      (le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer (hJT ▸ hT₀))
    rw [hO, hJT]
    exact hJT ▸ hNJ
  ·
    have hJne : J ≠ ⊤ := fun h => by
      rw [h, Subgroup.card_top, hcardA] at hJ
      omega
    rcases hsz _ (hmem _ (hTJ.trans hJN)) with hN | hN | hN
    · have := Subgroup.card_le_of_le hJN
      omega
    · exact (Subgroup.eq_of_le_of_card_ge hJN (by rw [hN, hJ])).ge
    · exfalso
      have hnorm : (pCoreOf 2 J).Normal := Subgroup.normalizer_eq_top_iff.1 (htop _ hN)
      rcases hnorm.eq_bot_or_eq_top with hO | hO
      · rcases hchar J hTJ with h | h
        · exact hJne h
        · have hJ1 : J ≤ ⊥ := by
            have hc' := h
            rw [CharTwo, hO, Subgroup.coe_bot, Subgroup.centralizer_singleton_one,
              inf_top_eq] at hc'
            exact hc'
          have := Subgroup.card_le_of_le hJ1
          rw [Subgroup.card_bot, hJ] at this
          omega
      · exact hJne (eq_top_iff.2 (hO ▸ pCoreOf_le 2 J))
  ·
    rw [htop J hJ]
    exact le_top

theorem radicalSelfNormOver_catalog_seven {Y : Type} [Group Y] [Finite Y]
    {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower} (hq : q.card = 7)
    (hd : d.1 = .A 1 q) (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) : RadicalSelfNormOver Y := by
  obtain ⟨dd, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨hp, hf⟩ := ParabHub.primePower_eq_of_card_eq Nat.prime_seven hq
  have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
  rw [hp, hf] at h
  obtain ⟨e₇⟩ := nonempty_equiv_sl_three_two_of_model_seven h
  have h2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  exact radicalSelfNormOver_of_model_psl (n := 3) (f := 1)
    ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩, ZMod 2, inferInstance,
      inferInstance, by rw [h2, pow_one],
      ⟨e₇.trans (Setup.Family.statedProjSL_equiv_of_card_two 3 (ZMod 2) h2).symm⟩⟩

theorem radicalSelfNormOver_alt_five :
    RadicalSelfNormOver ↥(alternatingGroup (Fin 5)) := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨T₀, hT₀⟩ := exists_sylow_of_isSylowTwoOf_top CertA5.isSylow_D
  refine RadicalSelfNormOver.of_sylow T₀ fun J hNJ => ?_
  rw [hT₀] at hNJ
  exact normalizer_pCoreOf_le_of_latCert CertA5.cert CertA5.closure_mGens CertA5.D_le
    CertA5.cert_check (by decide) (by decide)
    (fun Y hY => overgroups_charTwo CertA5.cert CertA5.cts CertA5.closure_mGens CertA5.D_le
      CertA5.cert_check CertA5.members_ok Y hY) (hT₀ ▸ T₀.isPGroup') J hNJ

theorem radicalSelfNormOver_alt_six :
    RadicalSelfNormOver ↥(alternatingGroup (Fin 6)) := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨T₀, hT₀⟩ := exists_sylow_of_isSylowTwoOf_top Even6.isSylow_D
  refine RadicalSelfNormOver.of_sylow T₀ fun J hNJ => ?_
  rw [hT₀] at hNJ
  exact normalizer_pCoreOf_le_of_latCert Even6.cert Even6.closure_mGens Even6.D_le
    Even6.cert_check (by decide) (by decide) Even6.overgroups (hT₀ ▸ T₀.isPGroup') J hNJ

theorem radicalSelfNormOver_u33
    [IsSimpleGroup ↥CFSG.GH74.KGroups.U33.QP.originalSubgroup] :
    RadicalSelfNormOver ↥CFSG.GH74.KGroups.U33.QP.originalSubgroup := by
  obtain ⟨T₀, hT₀⟩ := exists_sylow_of_isSylowTwoOf_top CertU33.isSylow_D
  refine RadicalSelfNormOver.of_sylow T₀ fun J hNJ => ?_
  rw [hT₀] at hNJ
  exact normalizer_pCoreOf_le_of_latCert CertU33.cert CertU33.closure_mGens CertU33.D_le
    CertU33.cert_check (by decide) (by decide)
    (fun Y hY => overgroups_charTwo CertU33.cert CertU33.cts CertU33.closure_mGens CertU33.D_le
      CertU33.cert_check CertU33.members_ok Y hY) (hT₀ ▸ T₀.isPGroup') J hNJ

theorem radicalSelfNormOver_catalog_u33
    {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower} (hq : q.card = 3)
    (hd : d.1 = .twistedA 2 q) (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) :
    RadicalSelfNormOver Y := by
  obtain ⟨dd, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨hp, hf⟩ := ParabHub.primePower_eq_of_card_eq Nat.prime_three hq
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  rw [hp, hf] at h
  obtain ⟨e₃⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel (Or.inl ⟨by decide, h⟩)
  have : IsSimpleGroup ↥CFSG.GH74.KGroups.U33.QP.originalSubgroup := e₃.symm.isSimpleGroup
  exact RadicalSelfNormOver.of_mulEquiv e₃.symm radicalSelfNormOver_u33

theorem radicalSelfNormOver_small
    {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hY : IsSmallTwoOrG2 Y) : RadicalSelfNormOver Y := by
  rcases hY with ⟨n, hn, ⟨e⟩⟩ | ⟨d, ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩, ⟨e⟩⟩
  · rcases hn with rfl | rfl | rfl
    · exact RadicalSelfNormOver.of_mulEquiv e.symm radicalSelfNormOver_alt_five
    · exact RadicalSelfNormOver.of_mulEquiv e.symm radicalSelfNormOver_alt_six
    · exact radicalSelfNormOver_alt_eight e
  · exact radicalSelfNormOver_catalog_seven hq hd e
  · exact radicalSelfNormOver_catalog_u33 hq hd e

end CFSG.AGLEmbedding.ToralCensus
