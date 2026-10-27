module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeData
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs
import CFSG.GroupTheory.Fitting.CharacteristicPOvergroup
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.LThreeParabolic
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.LThreeParabolicAut
import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic
import CFSG.LocalAnalysis.AGLEmbedding.SubnormalFStarP
import CFSG.LocalAnalysis.ComponentInitial.ParabolicLocalCharacteristicTransfer
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81JOneSolvPrimes
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.Adapters.QiuzhenLegacy.FeitThompson.Gorenstein.RelativeZJ

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)
open CFSG.GH74.GLS.Stage2.Signalizer (IsMaxParabolicP)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

section Helpers

omit [Finite G] in
private theorem isQuasisimple_of_isTwoPrimeComponent_self {I : Subgroup G}
    (h : IsTwoPrimeComponent I I) : CFSG.IsQuasisimple (↥I ⧸ CFSG.pCore 2 ↥I) := by
  have h1 := h.component.2.2
  have htop : barM I I = ⊤ := by
    unfold barM
    rw [Subgroup.subgroupOf_self, Subgroup.map_top, QuotientGroup.range_mk']
  rw [htop] at h1
  exact CFSG.Quasithin.A3.isQuasisimple_iff_open.2
    (CFSG.Open.IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm h1)

private theorem isMaxParabolicP_map_of_injective_comp {A A' : Type} [Group A] [Group A']
    [Finite A] [Finite A'] {p : ℕ} [Fact p.Prime] (f : A →* A') {K P : Subgroup A}
    (hf : Function.Injective (f.comp K.subtype)) (h : IsMaxParabolicP p K P) :
    IsMaxParabolicP p (K.map f) (P.map f) := by
  have hPK : P ≤ K := h.1.1
  have hrange : (f.comp K.subtype).range = K.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let e : ↥K ≃* ↥(K.map f) := (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)
  have he : ∀ x : ↥K, ((e x : ↥(K.map f)) : A') = f x := fun x => rfl
  have h1 := (CFSG.LocalAnalysis.AGL81I.Section3.isMaxParabolicP_subgroupOf_iff hPK).1 h
  have h2 := (CFSG.LocalAnalysis.AGL81I.Section3.isMaxParabolicP_of_mulEquiv e
    (P.subgroupOf K)).1 h1
  have hmap : (P.subgroupOf K).map e.toMonoidHom = (P.map f).subgroupOf (K.map f) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, (he y).symm⟩
    · intro hx
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hx)
      refine ⟨⟨z, hPK hz⟩, hz, Subtype.ext ?_⟩
      rw [MulEquiv.coe_toMonoidHom, he]
      exact hzx
  rw [hmap] at h2
  exact (CFSG.LocalAnalysis.AGL81I.Section3.isMaxParabolicP_subgroupOf_iff
    (Subgroup.map_mono hPK)).2 h2

variable {S : Type} [Group S] {K : Subgroup S} [K.Normal]

private theorem eq_one_of_mk_centralizer_eq_one (hZ : center ↥K = ⊥) {a : S} (ha : a ∈ K)
    (h1 : QuotientGroup.mk' (centralizer (K : Set S)) a = 1) : a = 1 := by
  have hac : a ∈ centralizer (K : Set S) := (QuotientGroup.eq_one_iff a).1 h1
  have hz : (⟨a, ha⟩ : ↥K) ∈ center ↥K :=
    Subgroup.mem_center_iff.2 fun k => Subtype.ext (mem_centralizer_iff.1 hac k k.2)
  rw [hZ, Subgroup.mem_bot] at hz
  exact congrArg Subtype.val hz

private theorem centralizer_map_mk_centralizer_eq_bot (hZ : center ↥K = ⊥) :
    centralizer ((K.map (QuotientGroup.mk' (centralizer (K : Set S))) :
      Subgroup (S ⧸ centralizer (K : Set S))) : Set (S ⧸ centralizer (K : Set S))) = ⊥ := by
  refine eq_bot_iff.2 fun a ha => ?_
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (centralizer (K : Set S)) a
  rw [Subgroup.mem_bot]
  refine (QuotientGroup.eq_one_iff s).2 (mem_centralizer_iff.2 fun k hk => ?_)
  have hcomm := mem_centralizer_iff.1 ha _ ⟨k, hk, rfl⟩
  have hcK : (s * k)⁻¹ * (k * s) ∈ K := by
    have h' : (s * k)⁻¹ * (k * s) = k⁻¹ * (s⁻¹ * k * s⁻¹⁻¹) := by group
    rw [h']
    exact K.mul_mem (K.inv_mem hk) ((inferInstance : K.Normal).conj_mem k hk s⁻¹)
  have hc1 : QuotientGroup.mk' (centralizer (K : Set S)) ((s * k)⁻¹ * (k * s)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, hcomm, inv_mul_cancel]
  exact (inv_mul_eq_one.1 (eq_one_of_mk_centralizer_eq_one hZ hcK hc1)).symm

end Helpers

theorem subgroupOf_le_ker_of_isCharacteristicP_range {B : Subgroup G} {T : Type*} [Group T]
    (f : ↥B →* T) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hf : CFSG.IsCharacteristicP p ↥f.range)
    {I : Subgroup G} (hIB : I ≤ B) (hI : IsSubnormal I B)
    (hshape : IsTwoPrimeComponent I I ∨ IsSymThreeOrSUThreeTwo (↥I ⧸ CFSG.pCore 2 ↥I)) :
    I.subgroupOf B ≤ f.ker := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hC : CFSG.IsCharacteristicP p (↥B ⧸ f.ker) :=
    CFSG.LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv
      (QuotientGroup.quotientKerEquivRange f).symm hf
  have hV : (I.subgroupOf B).IsSubnormal := (IsSubnormal.iff_subgroupOf hIB).1 hI
  let eI : ↥(I.subgroupOf B) ≃* ↥I := Subgroup.subgroupOfEquivOfLe hIB
  rcases hshape with hq | hb
  · have hq' : CFSG.IsQuasisimple (↥(I.subgroupOf B) ⧸ CFSG.pCore 2 ↥(I.subgroupOf B)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (QuotientGroup.congr _ _ eI.symm (CFSG.pCore_map_iso 2 eI.symm))
        (isQuasisimple_of_isTwoPrimeComponent_self hq)
    exact CFSG.AGLEmbedding.le_of_isQuasisimple_quotient_pCore_two hp hp2 hC hV hq'
  · have hcop : Nat.Coprime p (Nat.card (I.subgroupOf B)) := by
      rw [Nat.card_congr eI.toEquiv]
      refine hp.coprime_iff_not_dvd.2 fun hd => ?_
      rcases CFSG.LocalAnalysis.RankThreeTheoremC.prime_eq_of_dvd_card_of_symThree hb hp hd with
        h | h <;> omega
    have hmap : (I.subgroupOf B).map (QuotientGroup.mk' f.ker) = ⊥ :=
      CFSG.AGLEmbedding.eq_bot_of_isSubnormal_of_coprime_of_isCharacteristicP hp hC
        (hV.map (QuotientGroup.mk'_surjective f.ker))
        (hcop.coprime_dvd_right (Subgroup.card_map_dvd _ _))
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap
    exact hmap

theorem le_of_mem_cZero_of_isCharacteristicP_range {M H L : Subgroup G}
    (hL : L ∈ weakBlockSet M H) {T : Type*} [Group T] (f : ↥(H ⊓ M) →* T) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hf : CFSG.IsCharacteristicP p ↥f.range) {X : Subgroup G}
    (hker : ∀ b : ↥(H ⊓ M), f b = 1 → (b : G) ∈ X) {I : Subgroup G} (hI : I ∈ cZero (H ⊓ L)) :
    I ≤ X := by
  have hL' : IsWeakSBlock M (pCoreOf 2 H) L := hL
  have hLM : IsSubnormal L M := hL'.subnormal
  have hI' : IsCZeroMember (H ⊓ L) I := hI
  have hIle : I ≤ H ⊓ M := hI'.le.trans (inf_le_inf le_rfl hLM.le)
  have hHLM : IsSubnormal (H ⊓ L) (H ⊓ M) := by
    have h := hLM.inf H
    rwa [inf_comm L H, inf_comm M H] at h
  have hIsn : IsSubnormal I (H ⊓ M) := hI'.subnormal.trans hHLM
  have hshape : IsTwoPrimeComponent I I ∨ IsSymThreeOrSUThreeTwo (↥I ⧸ CFSG.pCore 2 ↥I) :=
    hI'.shape.imp id And.right
  have hk := subgroupOf_le_ker_of_isCharacteristicP_range f hp hp5 hf hIle hIsn hshape
  intro x hx
  exact hker ⟨x, hIle hx⟩ (hk (Subgroup.mem_subgroupOf.2 hx))

omit [Finite G] in
theorem jOne_le_of_forall_le {H L N : Subgroup G} (h : ∀ I ∈ cZero (H ⊓ L), I ≤ N) :
    jOne H L ≤ N :=
  iSup₂_le fun I hI => (CFSG.AGLEmbedding.oUpperTwo_le_self I).trans (h I hI)

section CaseTwo

variable {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

theorem isCharacteristicP_range_of_isPConstrained [Fact p.Prime] (hQM : Q ≤ M)
    (hsyl : CFSG.ABGLocalTools.IsSylowOf p Q H) (hcon : CFSG.ABGLocalTools.IsPConstrained p ↥H) :
    CFSG.IsCharacteristicP p ↥((QuotientGroup.mk' (primeComplementCore (G := ↥H) p)).comp
      (Subgroup.inclusion (inf_le_left : H ⊓ M ≤ H))).range := by
  set π := QuotientGroup.mk' (primeComplementCore (G := ↥H) p) with hπ
  have hS : CFSG.IsCharacteristicP p (StarGroup p H) :=
    CFSG.ABGTheoremB.RelativeZJ.centralizer_pCore_quotient_le hcon
  have hrange : (π.comp (Subgroup.inclusion (inf_le_left : H ⊓ M ≤ H))).range =
      ((H ⊓ M).subgroupOf H).map π := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  rw [hrange]
  refine CFSG.RankThree.PartTwo.Sec14.isCharacteristicP_of_pCore_le _ hS ?_
  obtain ⟨T, hT⟩ := hsyl
  let T' : Sylow p (StarGroup p H) := T.mapSurjective (QuotientGroup.mk'_surjective _)
  have hT' : (T' : Subgroup (StarGroup p H)) = (T : Subgroup ↥H).map π :=
    Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective _) T
  have hTB : (T : Subgroup ↥H) ≤ (H ⊓ M).subgroupOf H := by
    intro x hx
    refine Subgroup.mem_subgroupOf.2 ⟨x.2, hQM ?_⟩
    rw [← hT]
    exact ⟨x, hx, rfl⟩
  refine (CFSG.fitting_pCore_le_sylow T').trans ?_
  rw [hT']
  exact Subgroup.map_mono hTB

private theorem exists_charP_hom_of_caseTwo (h : TwelveCtx G M p Q H)
    (hsyl : CFSG.ABGLocalTools.IsSylowOf p Q H) {d : ℕ} (h2 : TwelveThreeCaseTwo M p H d) :
    ∃ (T : Type) (_ : Group T) (f : ↥(H ⊓ M) →* T), CFSG.IsCharacteristicP p ↥f.range ∧
      ∀ b : ↥(H ⊓ M), f b = 1 → (b : G) ∈ xSub p M H := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  refine ⟨↥H ⧸ primeComplementCore (G := ↥H) p, inferInstance,
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)).comp
      (Subgroup.inclusion (inf_le_left : H ⊓ M ≤ H)),
    isCharacteristicP_range_of_isPConstrained h.Q_le_M hsyl h2.2.1.1, fun b hb => ?_⟩
  refine ⟨Subgroup.inclusion inf_le_left b, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap]
  rw [MonoidHom.comp_apply] at hb
  rw [hb]
  exact Subgroup.one_mem _

theorem jOne_le_xSub_of_caseTwo (h : TwelveCtx G M p Q H)
    (hsyl : CFSG.ABGLocalTools.IsSylowOf p Q H) {d : ℕ} (hd : d ∈ sigmaSet G M)
    (h2 : TwelveThreeCaseTwo M p H d) {L : Subgroup G} (hL : L ∈ weakBlockSet M H) :
    jOne H L ≤ xSub p M H := by
  have hp5 : 5 ≤ p := five_le_of_odd_prime_dvd_add_one h.p_prime h.p_odd
    (CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1)
    (CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd d hd.1) h2.2.1.2.2.1
  obtain ⟨T, _, f, hf, hker⟩ := exists_charP_hom_of_caseTwo h hsyl h2
  exact jOne_le_of_forall_le fun I hI =>
    le_of_mem_cZero_of_isCharacteristicP_range hL f h.p_prime hp5 hf hker hI

end CaseTwo

section CaseSix

theorem isCharacteristicP_map_mk_centralizer_of_isMaxParabolicP {S : Type} [Group S] [Finite S]
    {p : ℕ} [Fact p.Prime] {K P B : Subgroup S} [K.Normal] (e : ↥K ≃* PSL(3, ZMod p))
    (hP : IsMaxParabolicP p K P) (hPB : P ≤ B) (hBP : B ≤ normalizer (P : Set S)) :
    CFSG.IsCharacteristicP p ↥(B.map (QuotientGroup.mk' (centralizer (K : Set S)))) := by
  set ρ := QuotientGroup.mk' (centralizer (K : Set S)) with hρ
  have hZ : center ↥K = ⊥ := by
    have h1 : (center ↥K).map (e : ↥K →* PSL(3, ZMod p)) = center (PSL(3, ZMod p)) :=
      Subgroup.map_center_eq e
    rw [CFSG.GH74.GLS.Stage2.Signalizer.Odd87.CentralQuotient.center_projectiveSpecialLinear_three]
      at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h1
  have hinj : Function.Injective (ρ.comp K.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (eq_one_of_mk_centralizer_eq_one hZ x.2 hx)
  have hrange : (ρ.comp K.subtype).range = K.map ρ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eK : ↥K ≃* ↥(K.map ρ) := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  let eb : ↥(K.map ρ) ≃* PSL(3, ZMod p) := eK.symm.trans e
  have hKbn : (K.map ρ).Normal :=
    Subgroup.Normal.map inferInstance ρ (QuotientGroup.mk'_surjective _)
  have hCK : centralizer ((K.map ρ : Subgroup _) : Set (S ⧸ centralizer (K : Set S))) = ⊥ :=
    centralizer_map_mk_centralizer_eq_bot hZ
  have hPb : IsMaxParabolicP p (K.map ρ) (P.map ρ) :=
    isMaxParabolicP_map_of_injective_comp ρ hinj hP
  have hPBb : P.map ρ ≤ B.map ρ := Subgroup.map_mono hPB
  refine CFSG.isCharacteristicP_of_normal_of_centralizer_le
    (N := (P.map ρ).subgroupOf (B.map ρ)) ?_ ?_ ?_
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hPBb]
    exact (Subgroup.map_mono hBP).trans (Subgroup.le_normalizer_map ρ)
  · have hc := centralizer_pCore_le_of_isMaxParabolicP_psl_three eb hPb
    exact CFSG.LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hPBb).symm hc
  · intro y hy
    have hy1 : (y : S ⧸ centralizer (K : Set S)) = 1 := by
      refine eq_one_of_commute_isMaxParabolicP_psl_three hKbn eb hPb hCK fun z hz => ?_
      have h1 := mem_centralizer_iff.1 hy ⟨z, hPBb hz⟩ (Subgroup.mem_subgroupOf.2 hz)
      exact (congrArg Subtype.val h1).symm
    have : y = 1 := Subtype.ext hy1
    rw [this]
    exact Subgroup.one_mem _

variable {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

private theorem exists_charP_hom_of_caseSix (h : TwelveCtx G M p Q H) {d : ℕ}
    (h6 : TwelveThreeCaseSix M p H d) :
    ∃ (T : Type) (_ : Group T) (f : ↥(H ⊓ M) →* T), CFSG.IsCharacteristicP p ↥f.range ∧
      ∀ b : ↥(H ⊓ M), f b = 1 → (b : G) ∈ xSub p M H := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := ↥H) p) with hπ
  have hKn : (kStar p M H).Normal := h6.2.1.map π (QuotientGroup.mk'_surjective _)
  obtain ⟨e⟩ := h6.2.2.1.1
  have hPB : starImg p H (M ⊓ kSub p M H) ≤ ((H ⊓ M).subgroupOf H).map π := by
    refine Subgroup.map_mono fun x hx => ?_
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨x.2, hx.1⟩
  have hBP : ((H ⊓ M).subgroupOf H).map π ≤
      normalizer ((starImg p H (M ⊓ kSub p M H) : Subgroup (StarGroup p H)) :
        Set (StarGroup p H)) := by
    refine (Subgroup.map_mono ?_).trans (Subgroup.le_normalizer_map π)
    rw [Subgroup.le_normalizer_iff]
    intro b hb x hx
    rw [Subgroup.mem_subgroupOf] at hb hx ⊢
    refine ⟨?_, ?_⟩
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact M.mul_mem (M.mul_mem hb.2 hx.1) (M.inv_mem hb.2)
    · exact Subgroup.mem_subgroupOf.1 (h6.2.1.conj_mem x (Subgroup.mem_subgroupOf.2 hx.2) b)
  have hchar := isCharacteristicP_map_mk_centralizer_of_isMaxParabolicP e h6.2.2.2 hPB hBP
  set ρ := QuotientGroup.mk' (centralizer ((kStar p M H : Subgroup (StarGroup p H)) :
    Set (StarGroup p H))) with hρ
  let f : ↥(H ⊓ M) →* StarGroup p H ⧸ centralizer ((kStar p M H : Subgroup (StarGroup p H)) :
      Set (StarGroup p H)) :=
    (ρ.comp π).comp (Subgroup.inclusion (inf_le_left : H ⊓ M ≤ H))
  have hrange : f.range = (((H ⊓ M).subgroupOf H).map π).map ρ := by
    simp only [f]
    rw [MonoidHom.range_comp, Subgroup.inclusion_range, Subgroup.map_map]
  have hf : CFSG.IsCharacteristicP p ↥f.range := by
    rw [hrange]
    exact hchar
  refine ⟨_, inferInstance, f, hf, fun b hb => ?_⟩
  refine ⟨Subgroup.inclusion inf_le_left b, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap]
  exact (QuotientGroup.eq_one_iff (π (Subgroup.inclusion inf_le_left b))).1 hb

theorem jOne_le_xSub_of_caseSix (h : TwelveCtx G M p Q H) {d : ℕ} (hd : d ∈ sigmaSet G M)
    (h6 : TwelveThreeCaseSix M p H d) {L : Subgroup G} (hL : L ∈ weakBlockSet M H) :
    jOne H L ≤ xSub p M H := by
  have hp5 : 5 ≤ p := five_le_of_odd_prime_dvd_add_one h.p_prime h.p_odd
    (CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1)
    (CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd d hd.1) h6.2.2.1.2.1
  obtain ⟨T, _, f, hf, hker⟩ := exists_charP_hom_of_caseSix h h6
  exact jOne_le_of_forall_le fun I hI =>
    le_of_mem_cZero_of_isCharacteristicP_range hL f h.p_prime hp5 hf hker hI

end CaseSix

theorem exists_charP_hom_of_caseTwo_or_caseSix {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}
    {d : ℕ} (h : TwelveCtx G M p Q H) (hsyl : CFSG.ABGLocalTools.IsSylowOf p Q H)
    (_hd : d ∈ sigmaSet G M) (hcase : TwelveThreeCaseTwo M p H d ∨ TwelveThreeCaseSix M p H d) :
    ∃ (T : Type) (_ : Group T) (f : ↥(H ⊓ M) →* T), CFSG.IsCharacteristicP p ↥f.range ∧
      ∀ b : ↥(H ⊓ M), f b = 1 → (b : G) ∈ xSub p M H :=
  hcase.elim (exists_charP_hom_of_caseTwo h hsyl) (exists_charP_hom_of_caseSix h)

theorem jOne_le_xSub_of_caseTwo_or_caseSix {M : Subgroup G} {p : ℕ}
    {Q H : Subgroup G} (h : TwelveCtx G M p Q H) (hsyl : CFSG.ABGLocalTools.IsSylowOf p Q H)
    {d : ℕ} (hd : d ∈ sigmaSet G M)
    (hcase : TwelveThreeCaseTwo M p H d ∨ TwelveThreeCaseSix M p H d)
    {L : Subgroup G} (hL : L ∈ weakBlockSet M H) :
    jOne H L ≤ xSub p M H := by
  rcases hcase with h2 | h6
  · exact jOne_le_xSub_of_caseTwo h hsyl hd h2 hL
  · exact jOne_le_xSub_of_caseSix h hd h6 hL

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
