module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverSmall
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartOne.N143.Inspect613Even

public section

namespace CFSG.AGLEmbedding.ParabHub

open Equiv CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge.Over CFSG.QuasithinUnique.L246C127
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Unc25K1.Six

@[expose] def ThreeDvdOver (S : Type) [Group S] : Prop :=
  ∀ T J : Subgroup S, IsSylowTwoOf T ⊤ → T ≤ J → J ≠ T → 3 ∣ Nat.card J

theorem ThreeDvdOver.of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : ThreeDvdOver S) : ThreeDvdOver S' := by
  intro T J hT hTJ hne
  have hT' : IsSylowTwoOf (T.map e.symm.toMonoidHom) ⊤ := by
    have := (Setup.Layer.isSylowTwoOf_map_mulEquiv e.symm (X := T) (Y := ⊤)).2 hT
    simpa [Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective] using this
  have hne' : J.map e.symm.toMonoidHom ≠ T.map e.symm.toMonoidHom := fun h' =>
    hne (Subgroup.map_injective e.symm.injective h')
  have := h _ _ hT' (Subgroup.map_mono hTJ) hne'
  rwa [Subgroup.card_map_of_injective e.symm.injective] at this

theorem ThreeDvdOver.of_sylow {S : Type} [Group S] [Finite S] (T₀ : Subgroup S)
    (hT₀ : IsSylowTwoOf T₀ ⊤) (h : ∀ J : Subgroup S, T₀ ≤ J → J ≠ T₀ → 3 ∣ Nat.card J) :
    ThreeDvdOver S := by
  intro T J hT hTJ hne
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf' hT₀ hT
  set e : S ≃* S := MulAut.conj g with he
  have hTe : T.map e.symm.toMonoidHom = T₀ := by
    rw [← hg, map_map_symm']
  have hT₀J : T₀ ≤ J.map e.symm.toMonoidHom := by
    rw [← hTe]
    exact Subgroup.map_mono hTJ
  have hne' : J.map e.symm.toMonoidHom ≠ T₀ := fun h' =>
    hne (Subgroup.map_injective e.symm.injective (h'.trans hTe.symm))
  have := h _ hT₀J hne'
  rwa [Subgroup.card_map_of_injective e.symm.injective] at this

theorem threeDvd_of_latCert {n : ℕ} {A : Subgroup (Perm (Fin n))} (c : LatCert (Perm (Fin n)))
    (hM : Subgroup.closure {g | g ∈ c.mGens} = A) (hTA : Subgroup.closure {g | g ∈ c.tGens} ≤ A)
    (hc : c.check RN.enc = true) (hsz : ∀ s ∈ c.sizes, s = c.sizes.headD 0 ∨ 3 ∣ s)
    (Y : Subgroup ↥A) (hTY : (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf A ≤ Y)
    (hne : Y ≠ (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf A) : 3 ∣ Nat.card Y := by
  subst hM
  obtain ⟨L, hL, hLM, hYL, hmem⟩ := c.overgroup_cases (rawIsEnc n) hc Y hTY
  have hcard : Nat.card Y = Nat.card (Subgroup.closure {g | g ∈ L}) := by
    rw [hYL]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv
  rcases hsz _ hmem with h | h
  · exfalso
    apply hne
    have hT := c.card_t (rawIsEnc n) (c.closedOK_of_check hc) (c.sizesOK_of_check hc)
    have hcardT : Nat.card ((Subgroup.closure {g | g ∈ c.tGens}).subgroupOf
        (Subgroup.closure {g | g ∈ c.mGens})) = c.sizes.headD 0 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTA).toEquiv, hT]
    exact (Subgroup.eq_of_le_of_card_ge hTY (by rw [hcard, h, hcardT])).symm
  · rw [hcard]
    exact h

theorem threeDvdOver_alt_five :
    ThreeDvdOver ↥(alternatingGroup (Fin 5)) :=
  ThreeDvdOver.of_sylow _ CertA5.isSylow_D fun J hJ hne =>
    threeDvd_of_latCert CertA5.cert CertA5.closure_mGens CertA5.D_le CertA5.cert_check (by decide)
      J hJ hne

theorem threeDvdOver_alt_six :
    ThreeDvdOver ↥(alternatingGroup (Fin 6)) :=
  ThreeDvdOver.of_sylow _ Even6.isSylow_D fun J hJ hne =>
    threeDvd_of_latCert Even6.cert Even6.closure_mGens Even6.D_le Even6.cert_check (by decide)
      J hJ hne

theorem threeDvdOver_alt_eight :
    ThreeDvdOver ↥(alternatingGroup (Fin 8)) :=
  ThreeDvdOver.of_sylow _ Even8.isSylow_D fun J hJ hne =>
    threeDvd_of_latCert Even8.cert Even8.closure_mGens Even8.D_le Even8.cert_check (by decide)
      J hJ hne

theorem threeDvdOver_alt
    {S : Type} [Group S] {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 8)
    (e : S ≃* alternatingGroup (Fin n)) : ThreeDvdOver S := by
  rcases hn with rfl | rfl | rfl
  · exact ThreeDvdOver.of_mulEquiv e.symm threeDvdOver_alt_five
  · exact ThreeDvdOver.of_mulEquiv e.symm threeDvdOver_alt_six
  · exact ThreeDvdOver.of_mulEquiv e.symm threeDvdOver_alt_eight

theorem threeDvdOver_z8 :
    ThreeDvdOver ↥(Vol2Native.A312L.Seven.Z 8) :=
  ThreeDvdOver.of_sylow _ CertL32.isSylow_D fun J hJ hne =>
    threeDvd_of_latCert CertL32.cert CertL32.closure_mGens CertL32.D_le CertL32.cert_check
      (by decide) J hJ hne

theorem threeDvdOver_model_seven
    {S : Type} [Group S]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSL 2 7 1) : ThreeDvdOver S := by
  obtain ⟨e⟩ := nonempty_equiv_sl_three_two_of_model_seven h
  exact ThreeDvdOver.of_mulEquiv (e.trans Vol2Native.A312L.Seven.z8Equiv).symm threeDvdOver_z8

theorem threeDvdOver_u33 :
    ThreeDvdOver ↥CFSG.GH74.KGroups.U33.QP.originalSubgroup :=
  ThreeDvdOver.of_sylow _ CertU33.isSylow_D fun J hJ hne =>
    threeDvd_of_latCert CertU33.cert CertU33.closure_mGens CertU33.D_le CertU33.cert_check
      (by decide) J hJ hne

theorem threeDvdOver_lieModel_psu_three_three
    {K : Type} [Group K] (h : CFSG.Blueprint.LieModel K .PSU 3 3 1) : ThreeDvdOver K := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel h
  exact ThreeDvdOver.of_mulEquiv e.symm threeDvdOver_u33

theorem primePower_eq_of_card_eq {q : TauCeti.PrimePower} {ℓ : ℕ} (hℓ : ℓ.Prime)
    (h : q.card = ℓ) : q.p = ℓ ∧ q.exponent = 1 := by
  rw [TauCeti.PrimePower.card_def] at h
  exact (Nat.Prime.pow_eq_iff hℓ).1 h

theorem threeDvdOver_catalog_seven
    {Y : Type} [Group Y] {d : TauCeti.ValidLieTypeIndex}
    {q : TauCeti.PrimePower} (hq : q.card = 7) (hd : d.1 = .A 1 q)
    (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) : ThreeDvdOver Y := by
  obtain ⟨dd, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_seven hq
  have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
  rw [hp, hf] at h
  exact threeDvdOver_model_seven h

theorem threeDvdOver_catalog_psu_three_three
    {Y : Type} [Group Y] {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower}
    (hq : q.card = 3) (hd : d.1 = .twistedA 2 q)
    (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) : ThreeDvdOver Y := by
  obtain ⟨dd, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_three hq
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  rw [hp, hf] at h
  exact threeDvdOver_lieModel_psu_three_three (Or.inl ⟨by decide, h⟩)

section Small


theorem threeDvd_small {Y : Type} [Group Y] [Finite Y]
    (hY : (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 8) ∧ Nonempty (Y ≃* alternatingGroup (Fin n))) ∨
      (∃ d : TauCeti.ValidLieTypeIndex,
        ((∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
          (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) ∧
        Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group))) :
    ∀ T J : Subgroup Y, IsSylowTwoOf T ⊤ → Subgroup.normalizer (T : Set Y) ≤ J →
      J ≠ Subgroup.normalizer (T : Set Y) → 3 ∣ Nat.card J := by
  have h3 : ThreeDvdOver Y := by
    rcases hY with ⟨n, hn, ⟨e⟩⟩ | ⟨d, ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩, ⟨e⟩⟩
    · exact threeDvdOver_alt hn e
    · exact threeDvdOver_catalog_seven hq hd e
    · exact threeDvdOver_catalog_psu_three_three hq hd e
  intro T J hT hN hJ
  refine h3 T J hT (Subgroup.le_normalizer.trans hN) fun hJT => hJ ?_
  have h1 : Subgroup.normalizer (T : Set Y) ≤ T := hJT ▸ hN
  exact hJT.trans (le_antisymm Subgroup.le_normalizer h1)

end Small

end CFSG.AGLEmbedding.ParabHub
