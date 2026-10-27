module

import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSmall
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartOne.N143.Inspect613Even
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverSmall

public section

namespace CFSG.HardMathSupport.Curtis.Proving

open Equiv CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge.Over
open CFSG.QuasithinUnique.Vol2Native.A312L PermLat

@[expose] def OvergroupOrder96 (S : Type) [Group S] : Prop :=
  ∀ T Y : Subgroup S, IsSylowTwoOf T ⊤ → T ≤ Y → Y ≠ ⊤ → Nat.card Y ∣ 96

theorem OvergroupOrder96.of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : OvergroupOrder96 S) : OvergroupOrder96 S' := by
  intro T Y hT hTY hY
  have hT' : IsSylowTwoOf (T.map e.symm.toMonoidHom) ⊤ := by
    have := (Setup.Layer.isSylowTwoOf_map_mulEquiv e.symm (X := T) (Y := ⊤)).2 hT
    simpa [Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective] using this
  have hY' : Y.map e.symm.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hY
    have := congrArg (Subgroup.map e.toMonoidHom) htop
    rw [Subgroup.map_map] at this
    have h1 : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id S' := by ext y; simp
    rwa [h1, Subgroup.map_id, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at this
  have hc := h _ _ hT' (Subgroup.map_mono hTY) hY'
  rw [Nat.card_congr (Subgroup.equivMapOfInjective Y e.symm.toMonoidHom e.symm.injective).toEquiv]
  exact hc

theorem OvergroupOrder96.of_sylow {S : Type} [Group S] [Finite S] (T₀ : Subgroup S)
    (hT₀ : IsSylowTwoOf T₀ ⊤)
    (h : ∀ Y : Subgroup S, T₀ ≤ Y → Y ≠ ⊤ → Nat.card Y ∣ 96) : OvergroupOrder96 S := by
  intro T Y hT hTY hY
  obtain ⟨g, hg⟩ := L246C127.exists_conj_of_isSylowTwoOf' hT₀ hT
  set e : S ≃* S := MulAut.conj g with he
  have hT₀Y : T₀ ≤ Y.map e.symm.toMonoidHom := by
    rw [← map_map_symm' e T₀, hg]
    exact Subgroup.map_mono hTY
  have hY' : Y.map e.symm.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hY
    have := congrArg (Subgroup.map e.toMonoidHom) htop
    rw [Subgroup.map_map, show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id S by
      ext y; simp, Subgroup.map_id, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
      at this
    exact this
  have hc := h _ hT₀Y hY'
  rw [Nat.card_congr (Subgroup.equivMapOfInjective Y e.symm.toMonoidHom e.symm.injective).toEquiv]
  exact hc

theorem ordBound_of_cert {n : ℕ} {A : Subgroup (Perm (Fin n))}
    (c : LatCert (Perm (Fin n))) (hM : Subgroup.closure {g | g ∈ c.mGens} = A)
    (hc : c.check RN.enc = true)
    (hsz' : ∀ s ∈ c.sizes, s = c.msize ∨ s ∣ 96)
    (hT₀ : IsSylowTwoOf ((Subgroup.closure {g | g ∈ c.tGens}).subgroupOf A) ⊤) :
    OvergroupOrder96 ↥A := by
  subst hM
  refine OvergroupOrder96.of_sylow _ hT₀ ?_
  intro Y hDY hY
  have hcl := c.closedOK_of_check hc
  have hsz := c.sizesOK_of_check hc
  obtain ⟨L, -, hLM, hYL, hcard⟩ := c.overgroup_cases (rawIsEnc n) hc Y hDY
  have hcardY : Nat.card Y = Nat.card (Subgroup.closure {g | g ∈ L}) := by
    rw [hYL]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv
  rcases hsz' _ hcard with hmz | hdvd
  · exfalso
    apply hY
    have hcM := c.card_m (rawIsEnc n) hcl hsz
    have heq : Subgroup.closure {g | g ∈ L} = Subgroup.closure {g | g ∈ c.mGens} :=
      Subgroup.eq_of_le_of_card_ge hLM (by rw [hmz, hcM])
    rw [hYL, heq, Subgroup.subgroupOf_self]
  · rw [hcardY]
    exact hdvd

theorem ordBound_alt_five :
    OvergroupOrder96 ↥(alternatingGroup (Fin 5)) :=
  ordBound_of_cert CertA5.cert CertA5.closure_mGens CertA5.cert_check (by decide)
    CertA5.isSylow_D

theorem ordBound_alt_six :
    OvergroupOrder96 ↥(alternatingGroup (Fin 6)) :=
  ordBound_of_cert CFSG.QuasithinUnique.L246C127.Even6.cert
    CFSG.QuasithinUnique.L246C127.Even6.closure_mGens
    CFSG.QuasithinUnique.L246C127.Even6.cert_check (by decide)
    CFSG.QuasithinUnique.L246C127.Even6.isSylow_D

theorem ordBound_seven :
    OvergroupOrder96 ↥(Seven.Z 8) :=
  ordBound_of_cert CertL32.cert CertL32.closure_mGens CertL32.cert_check (by decide)
    CertL32.isSylow_D

theorem ordBound_sl_three_two :
    OvergroupOrder96 (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
  OvergroupOrder96.of_mulEquiv Seven.z8Equiv.symm ordBound_seven

theorem ordBound_u33 :
    OvergroupOrder96 ↥CFSG.GH74.KGroups.U33.QP.originalSubgroup :=
  ordBound_of_cert CertU33.cert CertU33.closure_mGens CertU33.cert_check (by decide)
    CertU33.isSylow_D

theorem ordBound_psu_three_three
    {S : Type} [Group S] (h : StatedClassicalModel S .PSU 3 3 1) :
    OvergroupOrder96 S := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel (Or.inl ⟨by decide, h⟩)
  exact OvergroupOrder96.of_mulEquiv e.symm ordBound_u33

@[expose] def IsSmallFourTwo (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, (n = 5 ∨ n = 6) ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
    (∃ d : TauCeti.ValidLieTypeIndex, ((∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
        (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) ∧
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group))

theorem ordBound_isSmallFourTwo
    {Y : Type} [Group Y] (hY : IsSmallFourTwo Y) : OvergroupOrder96 Y := by
  rcases hY with ⟨n, hn, ⟨e⟩⟩ | ⟨d, ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩, ⟨e⟩⟩
  · rcases hn with rfl | rfl
    · exact OvergroupOrder96.of_mulEquiv e.symm ordBound_alt_five
    · exact OvergroupOrder96.of_mulEquiv e.symm ordBound_alt_six
  · obtain ⟨dd, hv⟩ := d
    simp only at hd
    subst hd
    obtain ⟨hp, hf⟩ := CFSG.AGLEmbedding.ParabHub.primePower_eq_of_card_eq Nat.prime_seven hq
    have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    rw [hp, hf] at h
    obtain ⟨e₇⟩ := nonempty_equiv_sl_three_two_of_model_seven h
    exact OvergroupOrder96.of_mulEquiv e₇.symm ordBound_sl_three_two
  · obtain ⟨dd, hv⟩ := d
    simp only at hd
    subst hd
    obtain ⟨hp, hf⟩ := CFSG.AGLEmbedding.ParabHub.primePower_eq_of_card_eq Nat.prime_three hq
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    rw [hp, hf] at h
    exact ordBound_psu_three_three h

end CFSG.HardMathSupport.Curtis.Proving

end
