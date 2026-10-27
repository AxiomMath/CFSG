module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSmall
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeCover
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartOne.N143.Inspect613Even

public section

namespace CFSG.AGLEmbedding.ParabPrime

open Equiv CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge.Over CFSG.QuasithinUnique.L246C127
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Unc25K1.Six
open CFSG.AGLEmbedding.ParabHub

@[expose] def PrimeOver (S : Type) [Group S] : Prop :=
  ∀ T J : Subgroup S, IsSylowTwoOf T ⊤ → T ≤ J → J ≠ T → ∀ p : ℕ, p.Prime → 5 ≤ p →
    p ∣ Nat.card J → J = ⊤

theorem PrimeOver.of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : PrimeOver S) : PrimeOver S' := by
  intro T J hT hTJ hne p hp hp5 hpJ
  have hT' : IsSylowTwoOf (T.map e.symm.toMonoidHom) ⊤ := by
    have := (Setup.Layer.isSylowTwoOf_map_mulEquiv e.symm (X := T) (Y := ⊤)).2 hT
    simpa [Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective] using this
  have hne' : J.map e.symm.toMonoidHom ≠ T.map e.symm.toMonoidHom := fun h' =>
    hne (Subgroup.map_injective e.symm.injective h')
  have hJ := h _ _ hT' (Subgroup.map_mono hTJ) hne' p hp hp5
    (by rwa [Subgroup.card_map_of_injective e.symm.injective])
  exact Subgroup.map_injective e.symm.injective
    (hJ.trans (Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective).symm)

theorem PrimeOver.of_sylow {S : Type} [Group S] [Finite S] (T₀ : Subgroup S)
    (hT₀ : IsSylowTwoOf T₀ ⊤)
    (h : ∀ J : Subgroup S, T₀ ≤ J → J ≠ T₀ → ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ Nat.card J →
      J = ⊤) : PrimeOver S := by
  intro T J hT hTJ hne p hp hp5 hpJ
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf' hT₀ hT
  set e : S ≃* S := MulAut.conj g with he
  have hTe : T.map e.symm.toMonoidHom = T₀ := by
    rw [← hg, map_map_symm']
  have hT₀J : T₀ ≤ J.map e.symm.toMonoidHom := by
    rw [← hTe]
    exact Subgroup.map_mono hTJ
  have hne' : J.map e.symm.toMonoidHom ≠ T₀ := fun h' =>
    hne (Subgroup.map_injective e.symm.injective (h'.trans hTe.symm))
  have hJ := h _ hT₀J hne' p hp hp5 (by rwa [Subgroup.card_map_of_injective e.symm.injective])
  exact Subgroup.map_injective e.symm.injective
    (hJ.trans (Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective).symm)

theorem primeOver_of_latCert {n : ℕ} {A : Subgroup (Perm (Fin n))} (c : LatCert (Perm (Fin n)))
    (hM : Subgroup.closure {g | g ∈ c.mGens} = A) (hTA : Subgroup.closure {g | g ∈ c.tGens} ≤ A)
    (hc : c.check RN.enc = true)
    (hsz : ∀ s ∈ c.sizes, s = c.sizes.headD 0 ∨ s = c.msize ∨ s ∣ 2 ^ 20 * 3 ^ 20)
    (Y : Subgroup ↥A) (hTY : (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf A ≤ Y)
    (hne : Y ≠ (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf A) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpY : p ∣ Nat.card Y) : Y = ⊤ := by
  subst hM
  obtain ⟨L, hL, hLM, hYL, hmem⟩ := c.overgroup_cases (rawIsEnc n) hc Y hTY
  have hcard : Nat.card Y = Nat.card (Subgroup.closure {g | g ∈ L}) := by
    rw [hYL]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv
  rcases hsz _ hmem with h | h | h
  · exfalso
    apply hne
    have hT := c.card_t (rawIsEnc n) (c.closedOK_of_check hc) (c.sizesOK_of_check hc)
    have hcardT : Nat.card ((Subgroup.closure {g | g ∈ c.tGens}).subgroupOf
        (Subgroup.closure {g | g ∈ c.mGens})) = c.sizes.headD 0 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTA).toEquiv, hT]
    exact (Subgroup.eq_of_le_of_card_ge hTY (by rw [hcard, h, hcardT])).symm
  · apply Subgroup.eq_top_of_card_eq
    rw [hcard, h]
    exact (c.card_m (rawIsEnc n) (c.closedOK_of_check hc) (c.sizesOK_of_check hc)).symm
  · exfalso
    rw [hcard] at hpY
    have h2 := hpY.trans h
    rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
      omega

theorem primeOver_alt_five :
    PrimeOver ↥(alternatingGroup (Fin 5)) :=
  PrimeOver.of_sylow _ CertA5.isSylow_D fun J hJ hne p hp hp5 hpJ =>
    primeOver_of_latCert CertA5.cert CertA5.closure_mGens CertA5.D_le CertA5.cert_check
      (by decide) J hJ hne hp hp5 hpJ

theorem primeOver_alt_six :
    PrimeOver ↥(alternatingGroup (Fin 6)) :=
  PrimeOver.of_sylow _ Even6.isSylow_D fun J hJ hne p hp hp5 hpJ =>
    primeOver_of_latCert Even6.cert Even6.closure_mGens Even6.D_le Even6.cert_check
      (by decide) J hJ hne hp hp5 hpJ

theorem primeOver_z8 :
    PrimeOver ↥(Vol2Native.A312L.Seven.Z 8) :=
  PrimeOver.of_sylow _ CertL32.isSylow_D fun J hJ hne p hp hp5 hpJ =>
    primeOver_of_latCert CertL32.cert CertL32.closure_mGens CertL32.D_le CertL32.cert_check
      (by decide) J hJ hne hp hp5 hpJ

theorem primeOver_u33 :
    PrimeOver ↥CFSG.GH74.KGroups.U33.QP.originalSubgroup :=
  PrimeOver.of_sylow _ CertU33.isSylow_D fun J hJ hne p hp hp5 hpJ =>
    primeOver_of_latCert CertU33.cert CertU33.closure_mGens CertU33.D_le CertU33.cert_check
      (by decide) J hJ hne hp hp5 hpJ

theorem ParabCore.of_primeOver {S : Type} [Group S] [Finite S] (h : PrimeOver S) :
    ParabCore S 2 := by
  intro T J hNJ hJ p hp hp5
  have hT : IsSylowTwoOf (T : Subgroup S) ⊤ :=
    ⟨le_top, T.isPGroup', by
      rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
      exact T.not_dvd_index⟩
  have hTJ : (T : Subgroup S) ≤ J := Subgroup.le_normalizer.trans hNJ
  have hne : J ≠ (T : Subgroup S) := by
    intro hJT
    apply hJ
    exact le_antisymm (hJT ▸ Subgroup.le_normalizer) hNJ
  refine ⟨fun hpq => ?_, fun hpJ => Or.inl (h _ _ hT hTJ hne p hp hp5 hpJ)⟩
  exfalso
  have : p ≤ 3 := Nat.le_of_dvd (by norm_num) (by simpa using hpq)
  omega

theorem primeOver_alt {S : Type}
    [Group S] {n : ℕ} (hn : n = 5 ∨ n = 6) (e : S ≃* alternatingGroup (Fin n)) : PrimeOver S := by
  rcases hn with rfl | rfl
  · exact PrimeOver.of_mulEquiv e.symm primeOver_alt_five
  · exact PrimeOver.of_mulEquiv e.symm primeOver_alt_six

theorem primeOver_model_seven
    {S : Type} [Group S]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSL 2 7 1) : PrimeOver S := by
  obtain ⟨e⟩ := nonempty_equiv_sl_three_two_of_model_seven h
  exact PrimeOver.of_mulEquiv (e.trans Vol2Native.A312L.Seven.z8Equiv).symm primeOver_z8

theorem primeOver_lieModel_psu_three_three
    {K : Type} [Group K] (h : CFSG.Blueprint.LieModel K .PSU 3 3 1) : PrimeOver K := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel h
  exact PrimeOver.of_mulEquiv e.symm primeOver_u33

theorem primeOver_catalog_seven
    {Y : Type} [Group Y] {d : TauCeti.ValidLieTypeIndex}
    {q : TauCeti.PrimePower} (hq : q.card = 7) (hd : d.1 = .A 1 q)
    (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) : PrimeOver Y := by
  obtain ⟨dd, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_seven hq
  have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
  rw [hp, hf] at h
  exact primeOver_model_seven h

theorem primeOver_catalog_psu_three_three
    {Y : Type} [Group Y] {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower}
    (hq : q.card = 3) (hd : d.1 = .twistedA 2 q)
    (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) : PrimeOver Y := by
  obtain ⟨dd, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_three hq
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  rw [hp, hf] at h
  exact primeOver_lieModel_psu_three_three (Or.inl ⟨by decide, h⟩)

section Small


theorem parabCore_small {Y : Type} [Group Y] [Finite Y]
    (hY : (∃ n : ℕ, (n = 5 ∨ n = 6) ∧ Nonempty (Y ≃* alternatingGroup (Fin n))) ∨
      (∃ d : TauCeti.ValidLieTypeIndex,
        ((∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
          (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) ∧
        Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group))) : ParabCore Y 2 := by
  refine ParabCore.of_primeOver ?_
  rcases hY with ⟨n, hn, ⟨e⟩⟩ | ⟨d, ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩, ⟨e⟩⟩
  · exact primeOver_alt hn e
  · exact primeOver_catalog_seven hq hd e
  · exact primeOver_catalog_psu_three_three hq hd e

end Small

end CFSG.AGLEmbedding.ParabPrime
