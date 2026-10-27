module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexBlockOK
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexLinear
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockPerfectCoreThreeSmall
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsPSL2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20Aux
import CFSG.RankThree.PartOne.N143.Inspect613Even
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSmall

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex

open Equiv Matrix CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.AGLEmbedding.ParabHub
open CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge.Over CFSG.QuasithinUnique.L246C127
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Unc25K1.Six
open CFSG.AGLEmbedding.ParabPrime (perfectJoin)
open CFSG.RankThree.PartOne.OutStructure (OutPNice Inn)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (flagStabilizer)

@[expose] def SolvOver (S : Type) [Group S] : Prop :=
  ∀ T J : Subgroup S, IsSylowTwoOf T ⊤ → T ≤ J → J ≠ ⊤ → Group.IsSolvable J

theorem map_ne_top_of_ne_top {S S' : Type} [Group S] [Group S'] (e : S' ≃* S)
    {J : Subgroup S'} (hne : J ≠ ⊤) : J.map e.toMonoidHom ≠ ⊤ := fun htop => hne (by
  have := congrArg (Subgroup.comap e.toMonoidHom) htop
  rwa [Subgroup.comap_map_eq_self_of_injective e.injective, Subgroup.comap_top] at this)

theorem isSolvable_of_map_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S' ≃* S)
    {J : Subgroup S'} (h : Group.IsSolvable (J.map e.toMonoidHom)) : Group.IsSolvable J := by
  haveI := h
  exact solvable_of_solvable_injective
    (f := (J.equivMapOfInjective e.toMonoidHom fun a b h => e.injective h).toMonoidHom)
    (MulEquiv.injective _)

theorem SolvOver.of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : SolvOver S) : SolvOver S' := by
  intro T J hT hTJ hne
  have hT' : IsSylowTwoOf (T.map e.symm.toMonoidHom) ⊤ := by
    have := (Setup.Layer.isSylowTwoOf_map_mulEquiv e.symm (X := T) (Y := ⊤)).2 hT
    simpa [Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective] using this
  exact isSolvable_of_map_mulEquiv e.symm
    (h _ _ hT' (Subgroup.map_mono hTJ) (map_ne_top_of_ne_top e.symm hne))

theorem SolvOver.of_sylow {S : Type} [Group S] [Finite S] (T₀ : Subgroup S)
    (hT₀ : IsSylowTwoOf T₀ ⊤) (h : ∀ J : Subgroup S, T₀ ≤ J → J ≠ ⊤ → Group.IsSolvable J) :
    SolvOver S := by
  intro T J hT hTJ hne
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf' hT₀ hT
  set e : S ≃* S := MulAut.conj g with he
  have hTe : T.map e.symm.toMonoidHom = T₀ := by
    rw [← hg, map_map_symm']
  have hT₀J : T₀ ≤ J.map e.symm.toMonoidHom := by
    rw [← hTe]
    exact Subgroup.map_mono hTJ
  exact isSolvable_of_map_mulEquiv e.symm (h _ hT₀J (map_ne_top_of_ne_top e.symm hne))

theorem solv_of_latCert {n : ℕ} {A : Subgroup (Perm (Fin n))} (c : LatCert (Perm (Fin n)))
    (hM : Subgroup.closure {g | g ∈ c.mGens} = A) (hc : c.check RN.enc = true)
    (hsz : ∀ s ∈ c.sizes, s = c.msize ∨ s ∣ 2 ^ 6 * 3 ^ 2) (Y : Subgroup ↥A)
    (hTY : (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf A ≤ Y) (hne : Y ≠ ⊤) :
    Group.IsSolvable Y := by
  subst hM
  obtain ⟨L, hL, hLM, hYL, hmem⟩ := c.overgroup_cases (rawIsEnc n) hc Y hTY
  have hcard : Nat.card Y = Nat.card (Subgroup.closure {g | g ∈ L}) := by
    rw [hYL]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv
  rcases hsz _ hmem with h | h
  · have hm := c.card_m (rawIsEnc n) (c.closedOK_of_check hc) (c.sizesOK_of_check hc)
    refine absurd ?_ hne
    apply Subgroup.eq_top_of_card_eq
    rw [hcard, h, ← hm, Nat.card_congr (Equiv.Set.univ _).symm]
  · exact KFactProofs.isSolvable_of_card_dvd_two_pow_mul_prime_pow Nat.prime_three (by norm_num)
      (hcard ▸ h)

theorem solvOver_alt_five :
    SolvOver ↥(alternatingGroup (Fin 5)) :=
  SolvOver.of_sylow _ CertA5.isSylow_D fun J hJ hne =>
    solv_of_latCert CertA5.cert CertA5.closure_mGens CertA5.cert_check (by decide) J hJ hne

theorem solvOver_alt_six :
    SolvOver ↥(alternatingGroup (Fin 6)) :=
  SolvOver.of_sylow _ Even6.isSylow_D fun J hJ hne =>
    solv_of_latCert Even6.cert Even6.closure_mGens Even6.cert_check (by decide) J hJ hne

theorem solvOver_z8 :
    SolvOver ↥(Vol2Native.A312L.Seven.Z 8) :=
  SolvOver.of_sylow _ CertL32.isSylow_D fun J hJ hne =>
    solv_of_latCert CertL32.cert CertL32.closure_mGens CertL32.cert_check (by decide) J hJ hne

theorem solvOver_u33 :
    SolvOver ↥CFSG.GH74.KGroups.U33.QP.originalSubgroup :=
  SolvOver.of_sylow _ CertU33.isSylow_D fun J hJ hne =>
    solv_of_latCert CertU33.cert CertU33.closure_mGens CertU33.cert_check (by decide) J hJ hne

theorem solvOver_catalog_seven
    {Y : Type} [Group Y] {d : TauCeti.ValidLieTypeIndex}
    {q : TauCeti.PrimePower} (hq : q.card = 7) (hd : d.1 = .A 1 q)
    (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) : SolvOver Y := by
  obtain ⟨dd, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_seven hq
  have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
  rw [hp, hf] at h
  obtain ⟨e'⟩ := nonempty_equiv_sl_three_two_of_model_seven h
  exact SolvOver.of_mulEquiv (e'.trans Vol2Native.A312L.Seven.z8Equiv).symm solvOver_z8

theorem solvOver_catalog_psu_three_three
    {Y : Type} [Group Y] {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower}
    (hq : q.card = 3) (hd : d.1 = .twistedA 2 q)
    (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) : SolvOver Y := by
  obtain ⟨dd, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_three hq
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  rw [hp, hf] at h
  obtain ⟨e'⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel (Or.inl ⟨by decide, h⟩)
  exact SolvOver.of_mulEquiv e'.symm solvOver_u33

theorem isSylowTwoOf_map_top {W X : Type*} [Group W] [Finite W] [Group X] {ρ : W →* X}
    (hρ : Function.Surjective ρ) (S : Sylow 2 W) : IsSylowTwoOf ((S : Subgroup W).map ρ) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite X := Finite.of_surjective ρ hρ
  have hS2 : ((S.mapSurjective hρ : Sylow 2 X) : Subgroup X) = (S : Subgroup W).map ρ := by
    rw [Sylow.coe_mapSurjective]
  rw [← hS2]
  refine ⟨le_top, (S.mapSurjective hρ).isPGroup', ?_⟩
  rw [show (((S.mapSurjective hρ : Sylow 2 X) : Subgroup X).subgroupOf ⊤).index =
    ((S.mapSurjective hρ : Sylow 2 X) : Subgroup X).index from Subgroup.relIndex_top_right _]
  exact (S.mapSurjective hρ).not_dvd_index

theorem isSolvable_of_solvOver {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    (hCP : CompParab L P) (hS : SolvOver (↥L ⧸ Subgroup.center ↥L)) : Group.IsSolvable P := by
  obtain ⟨hPL, T, hT, hTP⟩ := hCP.parab
  have hπ : Function.Surjective (QuotientGroup.mk' (Subgroup.center ↥L)) :=
    QuotientGroup.mk'_surjective _
  obtain ⟨S, hS'⟩ := Unc25K1.exists_sylow_of_isSylowTwoOf_top (isSylowTwoOf_subgroupOf_top hT)
  have hTb := isSylowTwoOf_map_top hπ S
  have hTP' : (S : Subgroup ↥L) ≤ P.subgroupOf L := by
    rw [hS']
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hTP ⟨x.2, Subgroup.le_normalizer hx⟩
  have hZP : Subgroup.center ↥L ≤ P.subgroupOf L := by
    intro z hz
    rw [Subgroup.mem_subgroupOf]
    refine hTP ⟨z.2, ?_⟩
    show (z : Y) ∈ Subgroup.normalizer (T : Set Y)
    rw [Subgroup.mem_normalizer_iff]
    intro t
    by_cases htL : t ∈ L
    · have h0 : t * (z : Y) = z * t :=
        congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨t, htL⟩)
      have h1 : (z : Y) * t * (z : Y)⁻¹ = t := by
        rw [← h0, mul_assoc, mul_inv_cancel, mul_one]
      rw [h1]
    · have h1 : t ∉ T := fun h => htL (hT.1 h)
      have h2 : (z : Y) * t * (z : Y)⁻¹ ∉ T := fun h => htL (by
        have ht : t = (z : Y)⁻¹ * ((z : Y) * t * (z : Y)⁻¹) * z := by group
        rw [ht]
        exact L.mul_mem (L.mul_mem (L.inv_mem z.2) (hT.1 h)) z.2)
      exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
  have hne : (P.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) ≠ ⊤ := by
    intro htop
    have hcm : ((P.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))).comap
        (QuotientGroup.mk' (Subgroup.center ↥L)) = P.subgroupOf L := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      exact sup_eq_left.2 hZP
    rw [htop, Subgroup.comap_top] at hcm
    refine hCP.ne_top (le_antisymm hPL fun x hx => ?_)
    have : (⟨x, hx⟩ : ↥L) ∈ P.subgroupOf L := hcm ▸ Subgroup.mem_top _
    exact this
  have hsolvbar := hS _ _ hTb (Subgroup.map_mono hTP') hne
  haveI := hsolvbar
  set f := (QuotientGroup.mk' (Subgroup.center ↥L)).subgroupMap (P.subgroupOf L) with hfdef
  have hcommK : ∀ a b : f.ker, a * b = b * a := by
    intro a b
    have ha : ((a : ↥(P.subgroupOf L)) : ↥L) ∈ Subgroup.center ↥L := by
      have h0 := a.2
      rw [MonoidHom.mem_ker] at h0
      have h1 : QuotientGroup.mk' (Subgroup.center ↥L) ((a : ↥(P.subgroupOf L)) : ↥L) = 1 :=
        congrArg Subtype.val h0
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subtype.ext (Subtype.ext (Subgroup.mem_center_iff.1 ha _).symm)
  haveI : Group.IsSolvable f.ker := isSolvable_of_comm hcommK
  haveI : Group.IsSolvable (P.subgroupOf L) :=
    solvable_of_ker_le_range f.ker.subtype f (by rw [Subgroup.range_subtype])
  exact solvable_of_solvable_injective
    (f := (Subgroup.subgroupOfEquivOfLe hPL).symm.toMonoidHom) (MulEquiv.injective _)

theorem outPNice_three_of_index_two {X : Type*} [Group X] (h : (Inn X).index = 2) :
    OutPNice 3 X := by
  refine ⟨⊤, ⊤, le_top, fun δ _ k hk => ?_, fun _ _ => Subgroup.mem_top _,
    fun _ _ _ => Subgroup.mem_top _, fun _ _ _ _ _ _ => Or.inl ⟨0, Subgroup.mem_top _⟩⟩
  have h2 : δ ^ 2 ∈ Inn X := h ▸ Subgroup.pow_index_mem (Inn X) δ
  obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
  have hδ : δ = ((δ ^ 2) ^ m)⁻¹ * δ ^ (3 ^ k) := by
    rw [hm, ← pow_mul, pow_succ, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hδ]
  exact (Inn X).mul_mem ((Inn X).inv_mem ((Inn X).pow_mem h2 m)) hk

theorem index_inn_of_alt_eight {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 8)) :
    (Inn X).index = 2 := by
  have hAut : Nat.card (MulAut X) = 40320 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv,
      KFactProofs.card_mulAut_alternatingGroup_eq (by norm_num) (by norm_num)]
    decide
  have hX : Nat.card X = 20160 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hc : e x ∈ Subgroup.center (alternatingGroup (Fin 8)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 : x * e.symm g * x⁻¹ = e.symm g := by
        have := congrArg (fun φ : MulAut X => φ (e.symm g)) hx
        simpa [MulAut.conj_apply] using this
      have h2 := congrArg e h1
      rw [map_mul, map_mul, map_inv, e.apply_symm_apply] at h2
      calc g * e x = e x * g * (e x)⁻¹ * e x := by rw [h2]
        _ = e x * g := by group
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hc
    exact Subgroup.mem_bot.2 (e.injective (by rw [hc, map_one]))
  have hInn : Nat.card (Inn X) = 20160 := by
    rw [← hX]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have hmul := Subgroup.card_mul_index (Inn X)
  rw [hInn, hAut] at hmul
  omega

theorem leviInnAt_alt_eight
    (hGA : GriessAllModelsStatement) {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    [L.Normal] (hCP : CompParab L P)
    (e8 : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8))
    (hrk : Open.pRank 3 (perfectJoin P) ≤ 1) : LeviInnAt P := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
    LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
      ((CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff _).2 ⟨e8⟩)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK, pow_one])
  obtain ⟨ρ, hρs, -, hρ⟩ :=
    kFactCoverLinear_of_griess hGA Y L hCP.comp hCP.odd 4 K (by norm_num) e
  obtain ⟨σ, e', I, hσs, hσ, hI, hcomap, hIne, -⟩ :=
    CFSG.AGLEmbedding.exists_comap_eq_flagStabilizer hCP.odd (by norm_num) e hρs hρ hCP.parab
  have hIne' := hIne hCP.ne_top
  have hker : σ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 4) K) := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have h1 : LocalAnalysis.ComponentInitial.LinearFlag.proj 4 K g = 1 := by
      rw [← hσ g, hg, QuotientGroup.mk_one, map_one]
    exact LocalAnalysis.ComponentInitial.LinearFlag.scalars_le_center 4 K
      (LocalAnalysis.ComponentInitial.LinearFlag.proj_eq_one_iff.1 h1)
  refine leviInnAt_of_levi_data (K := SpecialLinearGroup (Fin 4) K)
    (G := fun a : Fin 4 => GL (Fin (linBlockLen 4 I a)) K) hCP.parab.1 σ hσs hker
    (flagStabilizer 4 K I) hcomap.symm (linBlockSL K 4 I)
    (fun _ => ⊤) (linLeviHom K 4 I) (isPGroup_ker_linLeviHom (by omega))
    pi_le_range_linLeviHom commutator_range_linLeviHom_le
    (isQuasisimple_or_isSolvable_linBlockSL I) (fun _ _ => Subgroup.mem_top _)
    (fun a hq => ?_) (fun j E _ _ _ x hρx hβx => ?_) hrk
  · have hm := two_le_of_isQuasisimple_specialLinear
      (isQuasisimple_of_mulEquiv (slEquivToGLRange (K := K) (linBlockLen 4 I a)).symm hq)
    exact blockOK_gl_sl (linBlockLen 4 I a) hm
  · refine eq_one_of_scalar_of_single_block (j := j) hI hIne' x (hker hρx) fun a haj => ?_
    obtain ⟨y, hy, hyx⟩ := hβx
    rw [← hyx]
    exact Pi.mulSingle_eq_of_ne (M := fun a : Fin 4 => GL (Fin (linBlockLen 4 I a)) K) haj y

theorem fieldIndexOn_small
    (hGA : GriessAllModelsStatement) : FieldIndexOn IsSmallTwoOrG2 := by
  intro Y _ _ L P hCP hS hLn hrank h3 hrk a ha3 haN hout
  have hsol : SolvOver (↥L ⧸ Subgroup.center ↥L) →
      ∃ N : Subgroup Y, N.Normal ∧ N.index = 3 := fun hSO =>
    (BlockFieldIndex.false_of_isSolvable (isSolvable_of_solvOver hCP hSO) h3).elim
  rcases hS with ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · rcases hn with rfl | rfl | rfl
    · exact hsol (SolvOver.of_mulEquiv e.symm solvOver_alt_five)
    · exact hsol (SolvOver.of_mulEquiv e.symm solvOver_alt_six)
    · haveI := hLn
      exact fieldIndex_of_outPNice hCP (outPNice_three_of_index_two (index_inn_of_alt_eight e))
        (leviInnAt_alt_eight hGA hCP e hrk) ha3 haN hout
  · rcases hd with ⟨q, hq, hd'⟩ | ⟨q, hq, hd'⟩
    · exact hsol (solvOver_catalog_seven hq hd' e)
    · exact hsol (solvOver_catalog_psu_three_three hq hd' e)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
