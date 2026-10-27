module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSmall
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartOne.N143.Inspect613Even

public section

namespace CFSG.AGLEmbedding.ParabHub

open Equiv CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge.Over CFSG.QuasithinUnique.L246C127
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Unc25K1.Six

@[expose] def NineFreeOver (S : Type) [Group S] : Prop :=
  ∀ T J : Subgroup S, IsSylowTwoOf T ⊤ → T ≤ J → 9 ∣ Nat.card J → J = ⊤

theorem NineFreeOver.of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : NineFreeOver S) : NineFreeOver S' := by
  intro T J hT hTJ h9
  have hT' : IsSylowTwoOf (T.map e.symm.toMonoidHom) ⊤ := by
    have := (Setup.Layer.isSylowTwoOf_map_mulEquiv e.symm (X := T) (Y := ⊤)).2 hT
    simpa [Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective] using this
  have h9' : 9 ∣ Nat.card (J.map e.symm.toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective e.symm.injective]
  have htop := h _ _ hT' (Subgroup.map_mono hTJ) h9'
  have := congrArg (Subgroup.comap e.symm.toMonoidHom) htop
  rwa [Subgroup.comap_map_eq_self_of_injective e.symm.injective, Subgroup.comap_top] at this

theorem NineFreeOver.of_sylow {S : Type} [Group S] [Finite S] (T₀ : Subgroup S)
    (hT₀ : IsSylowTwoOf T₀ ⊤) (h : ∀ J : Subgroup S, T₀ ≤ J → 9 ∣ Nat.card J → J = ⊤) :
    NineFreeOver S := by
  intro T J hT hTJ h9
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf' hT₀ hT
  set e : S ≃* S := MulAut.conj g with he
  have hTe : T.map e.symm.toMonoidHom = T₀ := by
    rw [← hg, map_map_symm']
  have hT₀J : T₀ ≤ J.map e.symm.toMonoidHom := by
    rw [← hTe]
    exact Subgroup.map_mono hTJ
  have h9' : 9 ∣ Nat.card (J.map e.symm.toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective e.symm.injective]
  have htop := h _ hT₀J h9'
  have := congrArg (Subgroup.comap e.symm.toMonoidHom) htop
  rwa [Subgroup.comap_map_eq_self_of_injective e.symm.injective, Subgroup.comap_top] at this

theorem nineFree_of_latCert {n : ℕ} {A : Subgroup (Perm (Fin n))} (c : LatCert (Perm (Fin n)))
    (hM : Subgroup.closure {g | g ∈ c.mGens} = A) (hc : c.check RN.enc = true)
    (hsz : ∀ s ∈ c.sizes, s = c.msize ∨ ¬ 9 ∣ s) (Y : Subgroup ↥A)
    (hTY : (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf A ≤ Y) (h9 : 9 ∣ Nat.card Y) :
    Y = ⊤ := by
  subst hM
  obtain ⟨L, hL, hLM, hYL, hmem⟩ := c.overgroup_cases (rawIsEnc n) hc Y hTY
  have hcard : Nat.card Y = Nat.card (Subgroup.closure {g | g ∈ L}) := by
    rw [hYL]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv
  rcases hsz _ hmem with h | h
  · have hm := c.card_m (rawIsEnc n) (c.closedOK_of_check hc) (c.sizesOK_of_check hc)
    apply Subgroup.eq_top_of_card_eq
    rw [hcard, h, ← hm, Nat.card_congr (Equiv.Set.univ _).symm]
  · exact absurd (hcard ▸ h9) h

theorem nineFreeOver_alt_six :
    NineFreeOver ↥(alternatingGroup (Fin 6)) :=
  NineFreeOver.of_sylow _ Even6.isSylow_D fun J hJ h9 =>
    nineFree_of_latCert Even6.cert Even6.closure_mGens Even6.cert_check (by decide) J hJ h9

theorem nineFreeOver_z8 :
    NineFreeOver ↥(Vol2Native.A312L.Seven.Z 8) :=
  NineFreeOver.of_sylow _ CertL32.isSylow_D fun J hJ h9 =>
    nineFree_of_latCert CertL32.cert CertL32.closure_mGens CertL32.cert_check (by decide) J hJ h9

theorem nineFreeOver_u33 :
    NineFreeOver ↥CFSG.GH74.KGroups.U33.QP.originalSubgroup :=
  NineFreeOver.of_sylow _ CertU33.isSylow_D fun J hJ h9 =>
    nineFree_of_latCert CertU33.cert CertU33.closure_mGens CertU33.cert_check (by decide) J hJ h9

theorem nineFreeOver_catalog_seven
    {Y : Type} [Group Y] {d : TauCeti.ValidLieTypeIndex}
    {q : TauCeti.PrimePower} (hq : q.card = 7) (hd : d.1 = .A 1 q)
    (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) : NineFreeOver Y := by
  obtain ⟨dd, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_seven hq
  have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
  rw [hp, hf] at h
  obtain ⟨e'⟩ := nonempty_equiv_sl_three_two_of_model_seven h
  exact NineFreeOver.of_mulEquiv (e'.trans Vol2Native.A312L.Seven.z8Equiv).symm nineFreeOver_z8

theorem nineFreeOver_catalog_psu_three_three
    {Y : Type} [Group Y] {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower}
    (hq : q.card = 3) (hd : d.1 = .twistedA 2 q)
    (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) : NineFreeOver Y := by
  obtain ⟨dd, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_three hq
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  rw [hp, hf] at h
  obtain ⟨e'⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel (Or.inl ⟨by decide, h⟩)
  exact NineFreeOver.of_mulEquiv e'.symm nineFreeOver_u33

end CFSG.AGLEmbedding.ParabHub
