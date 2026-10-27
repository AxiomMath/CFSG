module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9UnitClass2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9LemRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynTri
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.S10.CatSingle
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgInner
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnExcLabel
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgSymplectic
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgOrthogonalLie
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgUnitary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141FU9UC

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived mem_innAutDerived_congr)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)

section Bridge

variable {Γ : Type} [Group Γ] [Finite Γ]

@[expose] noncomputable def u9QuotAut (L : Type) [Group L] (δ : MulAut L) :
    MulAut (L ⧸ GLAPPrimeCore 3 L) :=
  QuotientGroup.congr _ _ δ
    (Subgroup.characteristic_iff_map_eq.mp (CFSG.pPrimeCore_characteristic (p := 3)) δ)

@[expose] noncomputable def u9TransferHom (K J : Subgroup Γ) (hJK : J ≤ K) :
    ↥J →* ↥(chevTransfer 3 K J) :=
  ((chevQuotHom 3 K).subgroupMap (J.subgroupOf K)).comp
    (Subgroup.subgroupOfEquivOfLe hJK).symm.toMonoidHom

theorem u9TransferHom_surjective {K J : Subgroup Γ} (hJK : J ≤ K) :
    Function.Surjective (u9TransferHom K J hJK) :=
  (MonoidHom.subgroupMap_surjective _ _).comp (MulEquiv.surjective _)

theorem u9_mem_stab {K J : Subgroup Γ} {a : Γ} (hJK : J ≤ K)
    (haN : a ∈ Subgroup.normalizer (K : Set Γ)) (haJ : a ∈ Subgroup.normalizer (J : Set Γ)) :
    chevAut 3 K ⟨a, haN⟩ ∈ CFSG.GroupActions.subgroupStabAut (chevTransfer 3 K J) := by
  have key : ∀ (b : Γ) (hbN : b ∈ Subgroup.normalizer (K : Set Γ))
      (_ : b ∈ Subgroup.normalizer (J : Set Γ)),
      (chevTransfer 3 K J).map (chevAut 3 K ⟨b, hbN⟩).toMonoidHom ≤ chevTransfer 3 K J := by
    intro b hbN hbJ
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    have hkJ : (k : Γ) ∈ J := Subgroup.mem_subgroupOf.1 hk
    have hbk : b * k * b⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 hbJ k).1 hkJ
    refine ⟨K.normalizerMonoidHom ⟨b, hbN⟩ k, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
    · rw [chev_coe_normalizerMonoidHom]
      exact hbk
    · exact (chevAut_chevQuotHom 3 K ⟨b, hbN⟩ k).symm
  have h1 := key a haN haJ
  have h2 := key a⁻¹ (Subgroup.inv_mem _ haN) (Subgroup.inv_mem _ haJ)
  change (chevTransfer 3 K J).map (chevAut 3 K ⟨a, haN⟩).toMonoidHom = chevTransfer 3 K J
  refine le_antisymm h1 ?_
  intro s hs
  refine ⟨chevAut 3 K ⟨a⁻¹, Subgroup.inv_mem _ haN⟩ s, h2 ⟨s, hs, rfl⟩, ?_⟩
  change chevAut 3 K ⟨a, haN⟩ (chevAut 3 K ⟨a⁻¹, Subgroup.inv_mem _ haN⟩ s) = s
  rw [← MulAut.mul_apply, ← map_mul]
  have : (⟨a, haN⟩ : ↥(Subgroup.normalizer (K : Set Γ))) * ⟨a⁻¹, Subgroup.inv_mem _ haN⟩ = 1 :=
    Subtype.ext (mul_inv_cancel a)
  rw [this, map_one, MulAut.one_apply]

theorem indAut_mem_innAutDerived_of_restrict {K J X : Subgroup Γ} {a : Γ} (hJK : J ≤ K)
    (haN : a ∈ Subgroup.normalizer (K : Set Γ)) (haJ : a ∈ Subgroup.normalizer (J : Set Γ))
    (hJ : GLAPComponent 3 X J) {Y : Subgroup (PSimple 3 K)}
    (hT : GLAPComponent 3 Y (chevTransfer 3 K J))
    (hTq : CFSG.Open.IsQuasisimple ↥(chevTransfer 3 K J))
    (hstab : chevAut 3 K ⟨a, haN⟩ ∈ CFSG.GroupActions.subgroupStabAut (chevTransfer 3 K J))
    (h : centerQuotientHom ↥(chevTransfer 3 K J)
        (CFSG.GroupActions.subgroupStabRestrict (chevTransfer 3 K J)
          ⟨chevAut 3 K ⟨a, haN⟩, hstab⟩) ∈
      innAutDerived (↥(chevTransfer 3 K J) ⧸ Subgroup.center ↥(chevTransfer 3 K J))) :
    MI.indAut 3 J a haJ ∈ innAutDerived (PSimple 3 J) := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  set T := chevTransfer 3 K J with hTdef
  set ψ := u9TransferHom K J hJK with hψdef
  have hψ : Function.Surjective ψ := u9TransferHom_surjective hJK
  have hJq := isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hTq' := isQuasisimple_pQuot_of_glaPComponent hp hT
  haveI : Nontrivial (PQuot 3 T) := isQuasisimple_nontrivial hTq'
  let ψbar := pQuotMapOfSurjective hp ψ hψ
  have hker1 : ψbar.ker ≤ Subgroup.center (PQuot 3 J) :=
    ker_pQuotMapOfSurjective_le_center hp ψ hψ hJq inferInstance
  let δ := CFSG.GroupActions.subgroupStabRestrict T ⟨chevAut 3 K ⟨a, haN⟩, hstab⟩
  let δbar := u9QuotAut ↥T δ
  let αbar := barAut 3 J ⟨a, haJ⟩
  have hc1 : ∀ g, δbar (ψbar g) = ψbar (αbar g) := by
    intro g
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective g
    have e1 : αbar (QuotientGroup.mk j) =
        QuotientGroup.mk (J.normalizerMonoidHom ⟨a, haJ⟩ j) := barAut_mk 3 J _ j
    rw [e1]
    show (QuotientGroup.mk (δ (ψ j)) : PQuot 3 T) = QuotientGroup.mk (ψ (J.normalizerMonoidHom ⟨a, haJ⟩ j))
    congr 1
  have hne : GLAPPrimeCore 3 ↥T ≠ ⊤ := by
    intro htop
    haveI : Subsingleton (PQuot 3 T) := by
      rw [show PQuot 3 T = (↥T ⧸ GLAPPrimeCore 3 ↥T) from rfl, htop]
      exact QuotientGroup.subsingleton_quotient_top
    exact not_subsingleton (PQuot 3 T) ‹_›
  have hker2 : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥T)).ker ≤ Subgroup.center ↥T := by
    rw [QuotientGroup.ker_mk']
    exact le_center_of_normal_of_isQuasisimple hTq inferInstance hne
  have hc2 : ∀ t, δbar (QuotientGroup.mk' (GLAPPrimeCore 3 ↥T) t) =
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥T) (δ t) := fun t => rfl
  haveI : Group.IsPerfect (PQuot 3 J) := ⟨hJq.1⟩
  haveI : Group.IsPerfect ↥T := ⟨hTq.1⟩
  have h2 := (CFSG.ComponentClassification.PerfectCentralQuotient.centerQuotientHom_mem_innAutDerived_iff_of_surjective
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥T)) (QuotientGroup.mk'_surjective _) hker2 hc2).2 h
  have h1 := (CFSG.ComponentClassification.PerfectCentralQuotient.centerQuotientHom_mem_innAutDerived_iff_of_surjective
    ψbar (pQuotMapOfSurjective_surjective hp ψ hψ) hker1 hc1).1 h2
  have hind : MI.indAut 3 J a haJ = (centerQuotientHom (PQuot 3 J) αbar)⁻¹ := by
    have e : (⟨a⁻¹, Subgroup.inv_mem _ haJ⟩ : ↥(Subgroup.normalizer (J : Set Γ))) =
        (⟨a, haJ⟩ : ↥(Subgroup.normalizer (J : Set Γ)))⁻¹ := rfl
    show chevAut 3 J ⟨a⁻¹, Subgroup.inv_mem _ haJ⟩ = _
    rw [e, map_inv]
    rfl
  rw [hind]
  exact inv_mem h1

theorem restrict_mem_innAutDerived_of_eq_top {S : Type} [Group S] {T : Subgroup S} (hT : T = ⊤)
    {γ : MulAut S} (hγ : γ ∈ innAutDerived S) (hs : γ ∈ CFSG.GroupActions.subgroupStabAut T) :
    centerQuotientHom ↥T (CFSG.GroupActions.subgroupStabRestrict T ⟨γ, hs⟩) ∈
      innAutDerived (↥T ⧸ Subgroup.center ↥T) := by
  subst hT
  have he : CFSG.GroupActions.subgroupStabRestrict ⊤ ⟨γ, hs⟩ =
      MulAut.congr (Subgroup.topEquiv.symm) γ := by
    ext t
    rw [CFSG.GroupActions.subgroupStabRestrict_apply, MulAut.congr_apply]
    rfl
  rw [he]
  exact CFSG.ComponentClassification.PerfectCentralQuotient.centerQuotientHom_mem_innAutDerived
    ((mem_innAutDerived_congr _).2 hγ)

theorem u9_fixSubgroup_one {S : Type} [Group S] : fixSubgroup (1 : MulAut S) = ⊤ := by
  ext s
  simp [mem_fixSubgroup]

theorem eq_bot_or_top_of_isSubnormal_of_simple {S : Type} [Group S] [IsSimpleGroup S]
    {H K : Subgroup S} (h : IsSubnormal H K) (hK : K = ⊤) : H = ⊥ ∨ H = ⊤ := by
  induction h with
  | refl H' => exact Or.inr hK
  | @step H' M K' hHM hn _ ih =>
    rcases ih hK with hM | hM
    · left
      exact le_bot_iff.1 (hM ▸ hHM)
    · subst hM
      have hnorm : H'.Normal := by
        constructor
        intro n hn' g
        have := hn.conj_mem ⟨n, Subgroup.mem_top n⟩ (Subgroup.mem_subgroupOf.2 hn')
          ⟨g, Subgroup.mem_top g⟩
        exact Subgroup.mem_subgroupOf.1 this
      haveI := hnorm
      exact IsSimpleGroup.eq_bot_or_eq_top_of_normal H'

end Bridge

section Orders

theorem u9_not_derived {S : Type} [Group S] [Finite S] (hcen : Subgroup.center S = ⊥)
    {lab : GLALabel} (hS : Y10F.HasLabel S (· = lab)) (h19 : 19 ∣ Nat.card S) :
    lab.tag ≠ .B2der ∧ lab.tag ≠ .G2der ∧ lab.tag ≠ .twF4der := by
  have hlam := CanonSubcomp.lambda2_of_hasLabel hS
  have hM := CanonSubcomp.markedModel_of_hasLabel hS
  have hZ : Nat.card (S ⧸ Subgroup.center S) = Nat.card S :=
    Nat.card_congr (CanonInn.quotCenterEquivOfBot hcen).toEquiv
  obtain ⟨t, r, n⟩ := lab
  refine ⟨?_, ?_, ?_⟩ <;> intro ht <;> simp only at ht <;> subst ht
  · obtain ⟨-, rfl, rfl⟩ := hlam
    have h360 := card_of_B2der hM
    rw [hZ] at h360
    rw [h360] at h19
    norm_num at h19
  · obtain ⟨-, rfl, rfl⟩ := hlam
    have h6048 := card_of_G2der hM
    rw [hZ] at h6048
    rw [h6048] at h19
    norm_num at h19
  · obtain ⟨-, rfl, rfl⟩ := hlam
    have hc := CanonTriL.card_of_label_char_two hcen hS rfl
    simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder] at hc
    rw [hc] at h19
    norm_num [CFSG.Open.ordTits] at h19

theorem u9_char_two {S : Type} [Group S] [Finite S] (hcen : Subgroup.center S = ⊥)
    {lab : GLALabel} (hS : Y10F.HasLabel S (· = lab)) (h19 : 19 ∣ Nat.card S)
    (d : TauCeti.ValidLieTypeIndex) (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) :
    d.1.characteristic = 2 := by
  by_contra hd
  obtain ⟨hB2, hG2, -⟩ := u9_not_derived hcen hS h19
  have hc : CFSG.StandardType.markChar lab = 2 := by
    obtain ⟨t, r, n⟩ := lab
    cases t <;> simp_all [CFSG.StandardType.markChar]
  have hM := CanonSubcomp.markedModel_of_hasLabel hS
  unfold CFSG.StandardType.MarkedModel at hM
  rw [hc] at hM
  have hX : CFSG.Blueprint.LieModel S (CFSG.StandardType.markTag lab)
      (CFSG.StandardType.markRank lab) 2 (CFSG.StandardType.markDeg lab) :=
    CFSG.Blueprint.LieModel.of_mulEquiv (CanonInn.quotCenterEquivOfBot hcen) hM
  obtain ⟨t, n, p, f, hp, hL⟩ := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.exists_lieModel_char d
  have hLX : CFSG.Models.LieModel S t n p f := CFSG.Models.LieModel.of_mulEquiv e.symm hL
  have hBX : CFSG.Blueprint.LieModel S t n p f :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models hLX
  have hpprime : p.Prime := by
    rw [hp]
    exact d.1.characteristic_prime
  have hodd : CFSG.Blueprint.OddLieType S := ⟨t, n, p, f, hpprime, by rw [hp]; exact hd,
    hBX.admissible, hBX⟩
  have hcard := CanonTriL.card_of_label_char_two hcen hS hc
  rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hX hodd with
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
  · rw [h1, h2, h3] at hcard
    rw [hcard] at h19
    revert h19
    decide

end Orders

section FieldOn

theorem u9_eq_twA_two_three {lab : GLALabel} (ht : CFSG.StandardType.markTag lab = .PSU)
    (hr : CFSG.StandardType.markRank lab = 2 + 1) (hc : CFSG.StandardType.markChar lab = 2)
    (hf : CFSG.StandardType.markDeg lab = 3) : lab = ⟨.twA, 2, 3⟩ := by
  obtain ⟨t, r, n⟩ := lab
  cases t <;> simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
    CFSG.StandardType.markChar, CFSG.StandardType.markDeg] at ht hr hc hf <;>
    (try split_ifs at ht hr hc hf) <;> simp_all

theorem not_mem_innAutDerived_of_fieldOn_u38 {Γ : Type} [Group Γ] [Finite Γ] {X J : Subgroup Γ}
    (hJ : GLAPComponent 3 X J) (hU : catalogIs (PSimple 3 J) S9.isU3eight) {a : Γ}
    (hF : S10.FieldOn 3 a J) : MI.indAut 3 J a hF.1 ∉ innAutDerived (PSimple 3 J) := by
  intro hmem
  have hp : Nat.Prime 3 := Nat.prime_three
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hJ
  obtain ⟨q, hv, hq8, ⟨e8⟩⟩ := CatB.lieIndex_isU3eight hU
  obtain ⟨hp2, he3⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 3) (by norm_num)
    (hq8.trans (by norm_num))
  have hm := CFSG.Models.lieModel_twistedA 2 q hv e8
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA 2 q
  have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q
  rw [hc, hf, hp2, he3] at hm
  have hb : CFSG.Blueprint.LieModel (PQuot 3 J ⧸ Subgroup.center (PQuot 3 J)) .PSU (2 + 1) 2 3 :=
    CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
      (by simp [CFSG.Blueprint.classicalTags]) hm
  have hM := CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hq.1 hb
  have hT := FP.fieldOn_marking_transport hp (by norm_num) hF hM
  obtain ⟨-, lab, hlam, hraw⟩ := hT
  obtain ⟨R, _, I, F, -, -, θ, ⟨ht, hr, hch, hdeg⟩, -⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  have hlab : lab = ⟨.twA, 2, 3⟩ := u9_eq_twA_two_three ht hr hch hdeg
  subst hlab
  have hnd : ¬ MI.DerivedLab (⟨.twA, 2, 3⟩ : GLALabel) := by
    rintro (h | h) <;> cases h
  have hcomm : MI.CAll ⟨.twA, 2, 3⟩
      (CFSG.StandardType.LargeEvenSimpleGuard CFSG.StandardType.GGInndiagCommEq) :=
    (MI.canonAll_iff_legacyAll hlam hnd _).2
      (CFSG.StandardType.largeEvenLabelAll_inndiagComm_unitary hlam (Or.inl rfl))
  have hinn : MI.CAll ⟨.twA, 2, 3⟩ (CFSG.StandardType.GGRawInnField 3) :=
    MI.canonRawInnAny (by norm_num) hlam
  obtain ⟨R, _, I, F, ⟨⟨hs, hna, θ, -, hPF⟩, hEq⟩, hRI⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists (hinn _ (hcomm _ hraw))
  obtain ⟨hImul, hIinv, hIconj, hFI⟩ := hRI hs hna
  have hEq' := hEq hs hna
  obtain ⟨-, f, hfF, u, huI, hord, hind⟩ := hPF (Or.inl (by decide))
  have hθ : u * f * u⁻¹ = MulAut.congr θ (MI.indAut 3 J a hF.1) :=
    (MI.induces_indRel_iff hF.1 θ).1 hind
  have hmemR : u * f * u⁻¹ ∈ innAutDerived R := by
    rw [hθ]
    exact (mem_innAutDerived_congr θ).2 hmem
  let I' : Subgroup (MulAut R) :=
    { carrier := I
      mul_mem' := fun {φ ψ} hφ hψ => hImul φ hφ ψ hψ
      one_mem' := by simpa using hIconj 1
      inv_mem' := fun {φ} hφ => hIinv φ hφ }
  have hle : CFSG.StandardType.ggInndiag R I ≤ I' := by
    refine sup_le ?_ ?_
    · rintro _ ⟨r, rfl⟩
      exact hIconj r
    · exact (Subgroup.closure_le I').2 fun φ hφ => hφ
  have hufu : u * f * u⁻¹ ∈ I := by
    have h1 : u * f * u⁻¹ ∈ CFSG.StandardType.ggInndiag R I := by
      rw [hEq']
      exact hmemR
    exact hle h1
  have hfI : f ∈ I := by
    have e : f = u⁻¹ * (u * f * u⁻¹) * u := by group
    rw [e]
    exact hImul _ (hImul _ (hIinv u huI) _ hufu) u huI
  exact hFI f hfF hord hfI

end FieldOn

section Alg

open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] def U9AlgAt (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, P d.1 → KD264Lie.fieldSize d.1 = 8 →
    ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      Subgroup.center S = ⊥ →
      KD264Lie.CompAlgAtWith S (fun β x => (∃ lab, Y10GField.InnDiagKind S lab β) ∧
        ∃ lab, Y10GField.InnDiagKind S lab x)

private theorem u9_compAlgAtWith_of_compAlgAt {S : Type} [Group S]
    {R : MulAut S → MulAut S → Prop} (h : KD264Lie.CompAlgAt S) : KD264Lie.CompAlgAtWith S R := by
  intro β hβmem hβ3 hβ1 K hK e he hKiso x hxmem hx3 hβx _ hxstab
  exact h β hβmem hβ3 hβ1 K hK e he hKiso x hxmem hx3 hβx hxstab

private theorem u9_compAlgAtWith_of_inner {S : Type} [Group S]
    {R : MulAut S → MulAut S → Prop} (h : KD264Lie.CompAlgInnerAt S)
    (hR : ∀ β x, R β x → β ∈ inner S ∧ x ∈ inner S) : KD264Lie.CompAlgAtWith S R := by
  intro β hβmem hβ3 hβ1 K hK e he hKiso x hxmem hx3 hβx hRβx hxstab
  exact h β hβmem hβ3 hβ1 K hK e he hKiso x hxmem hx3 hβx (hR β x hRβx) hxstab

theorem u9AlgAt_of_lieCompAlg {P : TauCeti.LieTypeIndex → Prop} (h : KD264Lie.LieCompAlg P) :
    U9AlgAt P := by
  intro d hd h8 S _ _ hSiso _
  obtain ⟨eS⟩ := hSiso
  exact u9_compAlgAtWith_of_compAlgAt (KD264Lie.compAlgAt_of_mulEquiv eS.symm (h d hd h8))

end Alg

section Main

theorem i141U9Fam_of_sLevel {Q : TauCeti.CFSGIndex → Prop} {P : TauCeti.LieTypeIndex → Prop}
    (hQP : ∀ i, Q i → ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ P d.1)
    (hNo : NoU38Comp P) (hAlg : U9AlgAt P) : I141F.I141U9Fam Q := by
  intro Γ _ _ K J x a hQ hx3 ha3 hxa _ hIx hIa hJ hJU _ hF
  exfalso
  have hp : Nat.Prime 3 := Nat.prime_three
  have hxN : x ∈ Subgroup.normalizer (K : Set Γ) := hIx.1 (Subgroup.mem_zpowers x)
  have haN : a ∈ Subgroup.normalizer (K : Set Γ) := hIa.1 (Subgroup.mem_zpowers a)
  have haJ : a ∈ Subgroup.normalizer (J : Set Γ) := hF.1
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hxp : IsPGroup 3 (Subgroup.zpowers x) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma33Ns.isPGroup_zpowers_of_pow_eq_one hx3
  have hlabAll : Y10F.HasLabel (PQuot 3 K) (fun _ => True) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial) hIx.2
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 K) := Y10F.hasLabel_isQuasisimple hlabAll
  have hcen : Subgroup.center (PSimple 3 K) = ⊥ := Y10F.center_centerQuot_eq_bot hq
  haveI hsimple : IsSimpleGroup (PSimple 3 K) := hq.2
  have hnc : ∃ u v : PSimple 3 K, u * v ≠ v * u :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
  obtain ⟨labL, -, hinβ⟩ := I141F.innDiagKind_chevAut hxN hq hIx
  obtain ⟨labL', -, hinγ⟩ := I141F.innDiagKind_chevAut haN hq hIa
  have hβ3 : chevAut 3 K ⟨x, hxN⟩ ^ 3 = 1 := chevAut_pow_eq_one 3 K hxN hx3
  have hγ3 : chevAut 3 K ⟨a, haN⟩ ^ 3 = 1 := chevAut_pow_eq_one 3 K haN ha3
  have hβγ : chevAut 3 K ⟨x, hxN⟩ * chevAut 3 K ⟨a, haN⟩ =
      chevAut 3 K ⟨a, haN⟩ * chevAut 3 K ⟨x, hxN⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hxa
  have hT : GLAPComponent 3 (fixSubgroup (chevAut 3 K ⟨x, hxN⟩)) (chevTransfer 3 K J) :=
    glaPComponent_chevTransfer hp hxN hxp hJ
  obtain ⟨eJT⟩ := nonempty_pSimple_equiv_chevTransfer hp hxN hxp hJ
  have hcardJ : Nat.card (PSimple 3 J) = 5515776 :=
    CatSingle.card_isU3eight CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds hJU
  have hcardT : Nat.card (PSimple 3 (chevTransfer 3 K J)) = 5515776 := by
    rw [← Nat.card_congr eJT.toEquiv]
    exact hcardJ
  have h19 : 19 ∣ Nat.card (PSimple 3 K) := by
    have h1 : 19 ∣ Nat.card (PSimple 3 (chevTransfer 3 K J)) := by
      rw [hcardT]
      norm_num
    have h2 : Nat.card (PSimple 3 (chevTransfer 3 K J)) ∣ Nat.card (PQuot 3 (chevTransfer 3 K J)) :=
      Subgroup.index_dvd_card _
    have h3 : Nat.card (PQuot 3 (chevTransfer 3 K J)) ∣ Nat.card ↥(chevTransfer 3 K J) :=
      Subgroup.index_dvd_card _
    have h4 : Nat.card ↥(chevTransfer 3 K J) ∣ Nat.card (PSimple 3 K) :=
      Subgroup.card_subgroup_dvd_card _
    exact h1.trans (h2.trans (h3.trans h4))
  have hlabβ : Y10F.HasLabel (PSimple 3 K) (· = labL) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hinβ
  have hlabγ : Y10F.HasLabel (PSimple 3 K) (· = labL') :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hinγ
  have hβmem : chevAut 3 K ⟨x, hxN⟩ ∈ innAutDerived (PSimple 3 K) :=
    I141F.Tri.mem_innAutDerived_of_innDiagKind_of_not_derived hcen
      (u9_not_derived hcen hlabβ h19) hinβ
  have hγmem : chevAut 3 K ⟨a, haN⟩ ∈ innAutDerived (PSimple 3 K) :=
    I141F.Tri.mem_innAutDerived_of_innDiagKind_of_not_derived hcen
      (u9_not_derived hcen hlabγ h19) hinγ
  obtain ⟨i, hi, ⟨eS⟩⟩ := hQ
  obtain ⟨d, rfl, hPd⟩ := hQP i hi
  have hchar : d.1.characteristic = 2 := u9_char_two hcen hlabβ h19 d eS
  have hstab := u9_mem_stab hJK haN haJ
  have hnot := not_mem_innAutDerived_of_fieldOn_u38 hJ hJU hF
  have hpil : CFSG.HardMathSupport.Solomon.Coordinator.PerfectInLayer (chevAut 3 K ⟨x, hxN⟩) := by
    by_cases hβ1 : chevAut 3 K ⟨x, hxN⟩ = 1
    · rw [hβ1]
      exact CFSG.HardMathSupport.Solomon.Coordinator.perfectInLayer_one hnc
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent
        (PSimple 3 K) hsimple hnc d ⟨eS⟩ 3 hp (by decide) (by rw [hchar]; decide) _ hβ3 hβ1
  have hTle : chevTransfer 3 K J ≤ GLALayer (fixSubgroup (chevAut 3 K ⟨x, hxN⟩)) :=
    hpil _ hT.1 (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hT)
  have hTc : IsComponentOf (chevTransfer 3 K J) (fixSubgroup (chevAut 3 K ⟨x, hxN⟩)) :=
    (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hT hTle).1
  obtain ⟨eTZ⟩ := I141F.centerQuot_equiv_pSimple hp hT hTc.2.2
  by_cases hβ1 : chevAut 3 K ⟨x, hxN⟩ = 1
  ·
    have hsub : IsSubnormal (chevTransfer 3 K J) ⊤ := by
      have h := hTc.2.1
      rwa [hβ1, u9_fixSubgroup_one] at h
    have hTtop : chevTransfer 3 K J = ⊤ := by
      rcases eq_bot_or_top_of_isSubnormal_of_simple hsub rfl with h | h
      · exfalso
        haveI := isQuasisimple_nontrivial hTc.2.2
        have : Nontrivial ↥(chevTransfer 3 K J) := inferInstance
        rw [h] at this
        exact not_nontrivial _ this
      · exact h
    exact hnot (indAut_mem_innAutDerived_of_restrict hJK haN haJ hJ hT hTc.2.2 hstab
      (restrict_mem_innAutDerived_of_eq_top hTtop hγmem hstab))
  · by_cases h8 : KD264Lie.fieldSize d.1 = 8
    ·
      have hCA := hAlg d hPd h8 (PSimple 3 K) ⟨eS⟩ hcen
      obtain ⟨q8, hv8, hq8, ⟨e8⟩⟩ := CatB.lieIndex_isU3eight hJU
      have hres := hCA _ hβmem hβ3 hβ1 _ hTc ⟨.twistedA 2 q8, hv8⟩ ⟨q8, Or.inr rfl, hq8⟩
        ⟨eTZ.trans (eJT.symm.trans e8)⟩ _ hγmem hγ3 hβγ ⟨⟨labL, hinβ⟩, ⟨labL', hinγ⟩⟩ hstab
      exact hnot (indAut_mem_innAutDerived_of_restrict hJK haN haJ hJ hT hTc.2.2 hstab hres)
    ·
      exact hNo d hPd hchar h8 (PSimple 3 K) ⟨eS⟩ hcen labL _ hinβ hβmem hβ3 hβ1 _ hTc
        (by rw [Nat.card_congr eTZ.toEquiv]; exact hcardT)

theorem i141U9Fam_unit : I141F.I141U9Fam I141F.u9FamUnit := by
  refine i141U9Fam_of_sLevel (P := u9UnitIdx) ?_ noU38Comp_unit (u9AlgAt_of_lieCompAlg ?_)
  · intro i hi
    cases i with
    | lie d =>
      refine ⟨d, rfl, ?_⟩
      obtain ⟨dd, hv⟩ := d
      cases dd <;> first | exact hi | exact hi.elim
    | _ => exact hi.elim
  · intro d hd h8
    obtain ⟨dd, hv⟩ := d
    cases dd with
    | twistedA r q => exact KD264Lie.lieCompAlg_unitary ⟨.twistedA r q, hv⟩ trivial h8
    | _ => exact hd.elim

open CFSG.ComponentClassification.OuterAutomorphisms (inner)

private theorem u9_isQuasisimple_of_hasLabel {S : Type} [Group S] {P : GLALabel → Prop}
    (h : Y10F.HasLabel S P) : CFSG.IsQuasisimple S := by
  have hq : CFSG.Open.IsQuasisimple S := Y10F.hasLabel_isQuasisimple h
  exact ⟨Group.isPerfect_def.mpr hq.1, hq.2,
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian S hq⟩

private theorem u9_labL_symp {d : TauCeti.ValidLieTypeIndex}
    (hd : (∃ r q, d.1 = .B r q) ∨ ∃ r q, d.1 = .C r q) (hchar : d.1.characteristic = 2)
    {S : Type} [Group S] [Finite S] (eS : S ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hcen : Subgroup.center S = ⊥) {labL : GLALabel} (hlL : Y10F.HasLabel S (· = labL)) :
    (labL.tag = .B ∨ labL.tag = .C) ∧ KD264Lie.fieldSize d.1 = 2 ^ labL.n := by
  have hSq := u9_isQuasisimple_of_hasLabel hlL
  let eZ : S ≃* S ⧸ Subgroup.center S :=
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm
  obtain ⟨dd, hv⟩ := d
  obtain ⟨r, q, e, hp, hm⟩ : ∃ (r : ℕ) (q : TauCeti.PrimePower), (dd = .B r q ∨ dd = .C r q) ∧
      q.p = 2 ∧ StatedClassicalModel S .PSp r 2 q.exponent := by
    rcases hd with ⟨r, q, rfl⟩ | ⟨r, q, rfl⟩
    · have hp : q.p = 2 := by simpa using hchar
      refine ⟨r, q, Or.inl rfl, hp, ?_⟩
      have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
      rcases (show r = 2 ∨ 3 ≤ r by simp only at hr; omega) with rfl | hr3
      · have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv eS
        rwa [hp] at h
      · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp hr3 eS
        rwa [hp] at h
    · have hp : q.p = 2 := by simpa using hchar
      refine ⟨r, q, Or.inr rfl, hp, ?_⟩
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv eS
      rwa [hp] at h
  have hne : (r, 2 ^ q.exponent) ≠ (2, 2) := hm.1.2.2.2
  have hne' : ¬(r = 2 ∧ q.exponent = 1) := by
    rintro ⟨rfl, he1⟩
    exact hne (by simp [he1])
  have hl₀ := Y10F.hasLabel_of_statedClassicalModel_PSp hSq
    (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eZ hm)
  have hc := Y10GInnExcLabel.canonLabel_eq_of_hasLabel CFSG.StandardType.ggLabelRigidInput_holds
    hlL hl₀
  have hfs : KD264Lie.fieldSize dd = 2 ^ q.exponent := by
    rcases e with rfl | rfl <;>
    · show q.card = 2 ^ q.exponent
      rw [TauCeti.PrimePower.card_def, hp]
  rw [hfs]
  obtain ⟨t, k, n⟩ := labL
  cases t <;> simp only [canonLabel] at hc <;> (try split_ifs at hc) <;> simp_all

private theorem u9_labL_orth {d : TauCeti.ValidLieTypeIndex}
    (hd : (∃ r q, d.1 = .D r q) ∨ ∃ r q, d.1 = .twistedD r q) (hchar : d.1.characteristic = 2)
    {S : Type} [Group S] [Finite S] (eS : S ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hcen : Subgroup.center S = ⊥) {labL : GLALabel} (hlL : Y10F.HasLabel S (· = labL)) :
    Y10GField.FamOrth labL ∧ KD264Lie.fieldSize d.1 = 2 ^ (canonLabel labL).n := by
  have hSq := u9_isQuasisimple_of_hasLabel hlL
  let eZ : S ≃* S ⧸ Subgroup.center S :=
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm
  obtain ⟨dd, hv⟩ := d
  rcases hd with ⟨r, q, rfl⟩ | ⟨r, q, rfl⟩
  · have hp : q.p = 2 := by simpa using hchar
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv eS
    rw [hp] at hm
    have hr4 : 4 ≤ r := hm.1.2.2
    have hl₀ := Y10F.hasLabel_of_statedClassicalModel_POmegaPlus hSq
      (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eZ hm)
    have hc := Y10GInnExcLabel.canonLabel_eq_of_hasLabel CFSG.StandardType.ggLabelRigidInput_holds
      hlL hl₀
    have hc' : canonLabel labL = ⟨.D, r, q.exponent⟩ := by
      rw [hc]
      simp [canonLabel, show r ≠ 3 by omega]
    have hL : labL = ⟨.D, r, q.exponent⟩ := by
      obtain ⟨t, k, n⟩ := labL
      cases t <;> simp only [canonLabel] at hc' <;> (try split_ifs at hc') <;> simp_all
    refine ⟨?_, ?_⟩
    · rw [hL]
      exact Or.inl ⟨rfl, by show r ≠ 3; omega⟩
    · rw [hc']
      show q.card = 2 ^ q.exponent
      rw [TauCeti.PrimePower.card_def, hp]
  · have hp : q.p = 2 := by simpa using hchar
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv eS
    rw [hp] at hm
    have hr4 : 4 ≤ r := hm.1.2.2
    have hl₀ := Y10F.hasLabel_of_statedClassicalModel_POmegaMinus hSq
      (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eZ hm)
    have hc := Y10GInnExcLabel.canonLabel_eq_of_hasLabel CFSG.StandardType.ggLabelRigidInput_holds
      hlL hl₀
    have hc' : canonLabel labL = ⟨.twD, r, q.exponent⟩ := by
      rw [hc]
      simp [canonLabel, show r ≠ 3 by omega, show r ≠ 2 by omega]
    have hL : labL = ⟨.twD, r, q.exponent⟩ := by
      obtain ⟨t, k, n⟩ := labL
      cases t <;> simp only [canonLabel] at hc' <;> (try split_ifs at hc') <;> simp_all
    refine ⟨?_, ?_⟩
    · rw [hL]
      exact Or.inr ⟨rfl, by show r ≠ 2; omega, by show r ≠ 3; omega⟩
    · rw [hc']
      show q.card = 2 ^ q.exponent
      rw [TauCeti.PrimePower.card_def, hp]

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag in
private theorem u9_noU38_symp {S : Type} [Group S] [Finite S] (hcen : Subgroup.center S = ⊥)
    {labL : GLALabel} (ht : labL.tag = .B ∨ labL.tag = .C) (hn3 : labL.n ≠ 3) {β : MulAut S}
    (hin : Y10GField.InnDiagKind S labL β) (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) {T : Subgroup S}
    (hT : IsComponentOf T (fixSubgroup β)) : Nat.card (↥T ⧸ Subgroup.center ↥T) ≠ 5515776 := by
  classical
  obtain ⟨F, _, _, r, hr, hcard, e, A, hαA⟩ := CanonTriL.innDiagKind_symp_data_BC hcen ht hin
  have hn1 : 1 ≤ labL.n := by
    rcases Nat.eq_zero_or_pos labL.n with h0 | h0
    · have : 1 < Nat.card F := Finite.one_lt_card
      rw [hcard, h0, pow_zero] at this
      omega
    · exact h0
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := Fintype.ofFinite F
  haveI : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := labL.n) (by rw [Fintype.card_eq_nat_card, hcard])
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  obtain ⟨x, hx⟩ := Y10GInnSympRed.exists_conjAut_eq_conj h2 A
  have hMEq : MulAut.congr e β = MulAut.conj (proj r F x) := by
    rw [← hx]
    ext z
    have h1 := hαA (e.symm z)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  have hZ : Subgroup.center (StatedProj (StatedSp r F)) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e.symm z ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hz (e g)
    rw [hcen, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    simpa using congrArg e hz'
  have hpow : MulAut.conj (proj r F x) ^ 3 = 1 := by
    rw [← hMEq, ← map_pow, hβ3, map_one]
  have hx3 : x ^ 3 = 1 := Y10GInnSympRed.pow_eq_one_of_conj_pow_eq_one h2 hZ hpow
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hβ1
    apply (MulAut.congr e).injective
    rw [hMEq, map_one, map_one, map_one]
  have hT' : IsComponentOf (T.map (e : S →* StatedProj (StatedSp r F)))
      (fixSubgroup (MulAut.conj (proj r F x))) := by
    rw [← hMEq, u9_fixSubgroup_congr]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hT
  rw [← u9_card_centerQuotient_map e T]
  exact u9_sp_comp_card_ne hcard hn1 hn3 (by omega) x hx3 hx1 _ hT'

private theorem u9_noU38_orth {S : Type} [Group S] [Finite S] (hcen : Subgroup.center S = ⊥)
    {labL : GLALabel} (hFam : Y10GField.FamOrth labL) (hn3 : (canonLabel labL).n ≠ 3)
    {β : MulAut S} (hin : Y10GField.InnDiagKind S labL β) (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1)
    {T : Subgroup S} (hT : IsComponentOf T (fixSubgroup β)) :
    Nat.card (↥T ⧸ Subgroup.center ↥T) ≠ 5515776 := by
  obtain ⟨hmodel, a, rfl⟩ := Y10GInnOrthMark.innDiagKind_orth_data hcen hFam hin
  have ha3 : a ^ 3 = 1 :=
    CFSG.mulAutConj_injective_of_center_eq_bot hcen (by rw [map_pow, hβ3, map_one])
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hβ1 (map_one _)
  rcases hmodel with hG | hG
  · exact u9_orth_comp_card_ne (Or.inl rfl) hG hn3 a ha3 ha1 T hT
  · exact u9_orth_comp_card_ne (Or.inr rfl) hG hn3 a ha3 ha1 T hT

theorem noU38Comp_class : NoU38Comp u9ClassIdx := by
  intro d hP hchar h8 S _ _ hSiso hcen labL β hin _ hβ3 hβ1 T hT hN
  obtain ⟨eS⟩ := hSiso
  have hlL : Y10F.HasLabel S (· = labL) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hin
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | B r q =>
    obtain ⟨ht, hf⟩ := u9_labL_symp (d := ⟨.B r q, hv⟩) (Or.inl ⟨r, q, rfl⟩) hchar eS hcen hlL
    exact u9_noU38_symp hcen ht (fun h3 => h8 (by rw [hf, h3]; norm_num)) hin hβ3 hβ1 hT hN
  | C r q =>
    obtain ⟨ht, hf⟩ := u9_labL_symp (d := ⟨.C r q, hv⟩) (Or.inr ⟨r, q, rfl⟩) hchar eS hcen hlL
    exact u9_noU38_symp hcen ht (fun h3 => h8 (by rw [hf, h3]; norm_num)) hin hβ3 hβ1 hT hN
  | D r q =>
    obtain ⟨hF, hf⟩ := u9_labL_orth (d := ⟨.D r q, hv⟩) (Or.inl ⟨r, q, rfl⟩) hchar eS hcen hlL
    exact u9_noU38_orth hcen hF (fun h3 => h8 (by rw [hf, h3]; norm_num)) hin hβ3 hβ1 hT hN
  | twistedD r q =>
    obtain ⟨hF, hf⟩ := u9_labL_orth (d := ⟨.twistedD r q, hv⟩) (Or.inr ⟨r, q, rfl⟩) hchar eS
      hcen hlL
    exact u9_noU38_orth hcen hF (fun h3 => h8 (by rw [hf, h3]; norm_num)) hin hβ3 hβ1 hT hN
  | _ => exact hP.elim

private theorem u9_mem_inner_orth {d : TauCeti.ValidLieTypeIndex}
    (hd : (∃ r q, d.1 = .D r q) ∨ ∃ r q, d.1 = .twistedD r q) (hchar : d.1.characteristic = 2)
    {S : Type} [Group S] [Finite S] (eS : S ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hcen : Subgroup.center S = ⊥) {lab : GLALabel} {β : MulAut S}
    (hin : Y10GField.InnDiagKind S lab β) : β ∈ inner S := by
  have hlL : Y10F.HasLabel S (· = lab) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hin
  obtain ⟨hF, -⟩ := u9_labL_orth hd hchar eS hcen hlL
  obtain ⟨-, a, ha⟩ := Y10GInnOrthMark.innDiagKind_orth_data hcen hF hin
  exact ⟨a, ha⟩

theorem u9AlgAt_class : U9AlgAt u9ClassIdx := by
  intro d hP h8 S _ _ hSiso hcen
  obtain ⟨eS⟩ := hSiso
  obtain ⟨dd, hv⟩ := d
  have hq8 : ∀ q : TauCeti.PrimePower, q.card = 8 → q.p = 2 ∧ q.p ^ q.exponent = 8 := by
    intro q hq
    have h8' : q.p ^ q.exponent = 2 ^ 3 :=
      (TauCeti.PrimePower.card_def q).symm.trans (hq.trans (by norm_num))
    obtain ⟨hp2, -⟩ := Nat.Prime.pow_inj' q.prime_p Nat.prime_two q.exponent_pos.ne'
      (by norm_num) h8'
    exact ⟨hp2, h8'.trans (by norm_num)⟩
  cases dd with
  | B r q =>
    exact u9_compAlgAtWith_of_compAlgAt (KD264Lie.compAlgAt_of_mulEquiv eS.symm
      (KD264Lie.lieCompAlg_symplectic ⟨.B r q, hv⟩ (Or.inr (hq8 q h8).1) h8))
  | C r q =>
    exact u9_compAlgAtWith_of_compAlgAt (KD264Lie.compAlgAt_of_mulEquiv eS.symm
      (KD264Lie.lieCompAlg_symplectic ⟨.C r q, hv⟩ trivial h8))
  | D r q =>
    obtain ⟨hp2, h8'⟩ := hq8 q h8
    have hSC := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv
      (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.D r q, hv⟩).Group)
    refine u9_compAlgAtWith_of_inner (KD264Lie.compAlgInnerAt_of_mulEquiv eS.symm
      (KD264Lie.compAlgInnerAt_of_statedClassicalModel_eight (Or.inr (Or.inl rfl)) hSC h8')) ?_
    rintro β x ⟨⟨lab, hβ⟩, ⟨lab', hx⟩⟩
    have hchar : (TauCeti.LieTypeIndex.D r q).characteristic = 2 := by simpa using hp2
    exact ⟨u9_mem_inner_orth (d := ⟨.D r q, hv⟩) (Or.inl ⟨r, q, rfl⟩) hchar eS hcen hβ,
      u9_mem_inner_orth (d := ⟨.D r q, hv⟩) (Or.inl ⟨r, q, rfl⟩) hchar eS hcen hx⟩
  | twistedD r q =>
    obtain ⟨hp2, h8'⟩ := hq8 q h8
    have hSC := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv
      (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group)
    refine u9_compAlgAtWith_of_inner (KD264Lie.compAlgInnerAt_of_mulEquiv eS.symm
      (KD264Lie.compAlgInnerAt_of_statedClassicalModel_eight (Or.inr (Or.inr rfl)) hSC h8')) ?_
    rintro β x ⟨⟨lab, hβ⟩, ⟨lab', hx⟩⟩
    have hchar : (TauCeti.LieTypeIndex.twistedD r q).characteristic = 2 := by simpa using hp2
    exact ⟨u9_mem_inner_orth (d := ⟨.twistedD r q, hv⟩) (Or.inr ⟨r, q, rfl⟩) hchar eS hcen hβ,
      u9_mem_inner_orth (d := ⟨.twistedD r q, hv⟩) (Or.inr ⟨r, q, rfl⟩) hchar eS hcen hx⟩
  | _ => exact hP.elim

theorem i141U9Fam_class : I141F.I141U9Fam I141F.u9FamClass := by
  refine i141U9Fam_of_sLevel (P := u9ClassIdx) ?_ noU38Comp_class u9AlgAt_class
  intro i hi
  cases i with
  | lie d =>
    refine ⟨d, rfl, ?_⟩
    obtain ⟨dd, hv⟩ := d
    cases dd <;> first | exact hi | exact hi.elim
  | _ => exact hi.elim

end Main

end CFSG.LocalAnalysis.GLTheoremA.I141FU9UC

end
