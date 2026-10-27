module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.Defs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.SectionIH
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDich
public import CFSG.ClassicalInvolution.Q3.TL4Sep2F

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace S6

structure Hyp {Y : Type} [Group Y] (Φ : Set (Subgroup Y)) : Prop extends TypeRHyp Φ where
  odd : classicalInvolutionOddCore Y = ⊥

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)}

omit [Finite Y] in
theorem Hyp.gen (h : Hyp Φ) {J : Subgroup Y} (hJ : J ∈ Φ) :
    Subgroup.closure {x : Y | x ∈ J ∧ IsPGroup 2 (Subgroup.zpowers x)} = J := by
  rcases h.hyp.omega2 J hJ with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨e⟩ := h1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp ((h.twoGroup J hJ).of_equiv e)
    rw [natCard_sl2Three] at hk
    have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 24)
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem Hyp.le_centralizer_of_not_mem (h : Hyp Φ) {J : Subgroup Y} (hJ : J ∈ Φ) {u : Y}
    (hu : IsUniqueInvolution J u) {X : Subgroup Y} (hX : X.Normal) (huX : u ∉ X) :
    J ≤ Subgroup.centralizer (X : Set Y) := by
  have hOX : oddCoreOf X = ⊥ := by
    rw [oddCoreOf, TL4.oddCore_eq_bot_of_normal h.odd hX, Subgroup.map_bot]
  rw [← h.gen hJ, Subgroup.closure_le]
  rintro x ⟨hxJ, hx2⟩
  obtain ⟨T, hT, hTJ, hxT⟩ := exists_mem_RSet_ge hJ hx2 (Subgroup.zpowers_le.mpr hxJ)
  have hTX : T ⊓ X = ⊥ := by
    by_contra hne
    exact huX (TL4.mem_of_isPGroup_of_ne_bot hu (inf_le_left.trans hTJ.1)
      (hTJ.2.1.to_le inf_le_left) hne).2
  have hc := comm613Gen_normal h.hyp hT hX hTX
  rw [hOX, le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer] at hc
  exact hc (hxT (Subgroup.mem_zpowers x))

theorem Hyp.mem_layer (h : Hyp Φ) {J : Subgroup Y} (hJ : J ∈ Φ) {u : Y}
    (hu : IsUniqueInvolution J u) (hno : ¬ TightInO2 u) : u ∈ layer Y := by
  by_contra huE
  have hEn : (layer Y).Normal := by
    have := CFSG.LocalCores.layer_characteristic (G := Y)
    infer_instance
  have hE := h.le_centralizer_of_not_mem hJ hu hEn huE
  have hF := h.le_centralizer_of_not_mem hJ hu fittingSubgroup_normal fun huF =>
    hno ⟨_, fittingSubgroup_normal, TL4.isPGroup_fittingSubgroup h.odd, huF⟩
  have hC : J ≤ Subgroup.centralizer (generalizedFitting Y : Set Y) :=
    TL4.le_centralizer_sup hF hE
  have hJF : J ≤ generalizedFitting Y := hC.trans (centralizer_generalizedFitting_le Y)
  obtain ⟨-, P, hP, hPnc⟩ := h.hyp.omega1 J hJ
  refine hPnc ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have hb := Subgroup.mem_centralizer_iff.mp (hC (hP.1 a.2)) b (hJF (hP.1 b.2))
  exact hb.symm

theorem Hyp.q8Datum (h : Hyp Φ) {J : Subgroup Y} (hJ : J ∈ Φ) {u : Y}
    (hu : IsUniqueInvolution J u) (S : Sylow 2 ↥J) : Q8TwinDatum J S u := by
  have hS := isSylow2In_map_sylow J S
  obtain ⟨e⟩ := h.sylow J hJ _ hS
  have e' : ↥(S : Subgroup J) ≃* QuaternionGroup (2 ^ (3 - 2)) :=
    ((S : Subgroup J).equivMapOfInjective J.subtype J.subtype_injective).trans e
  have hcent : J ≤ Subgroup.centralizer ({u} : Set Y) := isUniqueInvolution_le_centralizer hu
  refine ⟨⟨3, le_rfl, ⟨e'⟩⟩, ?_, orderOf_eq_prime (by rw [pow_two]; exact hu.sq)
    hu.ne_one, hcent, h.twoGroup J hJ⟩
  refine TL4.mem_of_isPGroup_of_ne_bot hu hS.1 hS.2.1 fun hbot => ?_
  obtain ⟨x, hx⟩ := exists_ne (1 : QuaternionGroup 2)
  apply hx
  have h1 : e.symm x = 1 :=
    Subtype.ext ((Subgroup.eq_bot_iff_forall _).mp hbot _ (e.symm x).2)
  rw [← e.apply_symm_apply x, h1, map_one]

theorem Hyp.hypOmegaGen_conjClass (h : Hyp Φ) {J : Subgroup Y} (hJ : J ∈ Φ) :
    HypOmegaGen (CoreAssembly.conjClass (tightCore J)) := by
  rw [show tightCore J = J from h.gen hJ]
  refine hypOmegaGen_sub h.hyp ?_ (TL4.conjInvariant_conjClass J)
  rintro _ ⟨g, rfl⟩
  exact h.hyp.conjInvariant g J hJ

theorem Hyp.thmA (h : Hyp Φ) {J : Subgroup Y} (hJ : J ∈ Φ) {u : Y} (hu : IsUniqueInvolution J u)
    (hno : ¬ TightInO2 u) {A : Subgroup Y} (hA : CFSG.IsComponent A) {x : Y} (hx : x ∈ J) :
    conjSub x A = A := by
  have hle : J ≤ Subgroup.normalizer (A : Set Y) := by
    rw [← h.gen hJ, Subgroup.closure_le]
    rintro y ⟨hyJ, hy2⟩
    have hy2' : IsPGroup 2 ↥((Subgroup.zpowers y).subgroupOf J) :=
      hy2.comap_of_injective _ (Subgroup.subtype_injective _)
    obtain ⟨S, hS⟩ := hy2'.exists_le_sylow
    have hyS : y ∈ (S : Subgroup J).map J.subtype :=
      ⟨⟨y, hyJ⟩, hS (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers y)), rfl⟩
    have hd := h.q8Datum hJ hu S
    have hq8 : Nonempty (↥(S : Subgroup J) ≃* QuaternionGroup 2) := by
      obtain ⟨e⟩ := h.sylow J hJ _ (isSylow2In_map_sylow J S)
      exact ⟨((S : Subgroup J).equivMapOfInjective J.subtype J.subtype_injective).trans e⟩
    exact mem_normalizer_iff_conjSub_eq.mpr
      (thmA_twin hd hq8 (h.hypOmegaGen_conjClass hJ) h.odd hno hA hyS)
  exact mem_normalizer_iff_conjSub_eq.mp (hle hx)

theorem Hyp.component_normal (h : Hyp Φ) (hgen : omegaGen Φ = ⊤) (hno : TL4.NoInvO2 Φ)
    {L : Subgroup Y} (hL : CFSG.IsComponent L) : L.Normal := by
  have hle : omegaGen Φ ≤ Subgroup.normalizer (L : Set Y) := by
    refine iSup₂_le fun K hK => ?_
    obtain ⟨z, hz⟩ := (h.hyp.omega1 K hK).1
    intro x hx
    exact mem_normalizer_iff_conjSub_eq.mpr (h.thmA hK hz (hno K hK z hz) hL hx)
  rw [hgen] at hle
  exact Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr hle)

theorem Hyp.exists_component (h : Hyp Φ) (hgen : omegaGen Φ = ⊤) (hno : TL4.NoInvO2 Φ)
    {J : Subgroup Y} (hJ : J ∈ Φ) {u : Y} (hu : IsUniqueInvolution J u) :
    ∃ L : Subgroup Y, CFSG.IsComponent L ∧ L.Normal ∧ u ∈ L := by
  have huE := h.mem_layer hJ hu (hno J hJ u hu)
  have hex : ∃ L : Subgroup Y, CFSG.IsComponent L ∧ ¬ ∀ x ∈ L, x * u = u * x := by
    by_contra hcon
    push Not at hcon
    have hle : layer Y ≤ Subgroup.centralizer ({u} : Set Y) :=
      sSup_le fun L hL x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hcon L hL x hx)
    have hC : u ∈ Subgroup.centralizer (layer Y : Set Y) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
    exact hno J hJ u hu ⟨_, TightA.centerLayer_normal, TightA.centerLayer_isPGroup h.odd, huE, hC⟩
  obtain ⟨L, hL, hLu⟩ := hex
  have hLn := h.component_normal hgen hno hL
  refine ⟨L, hL, hLn, ?_⟩
  by_contra huL
  exact hLu fun x hx =>
    Subgroup.mem_centralizer_iff.mp (h.le_centralizer_of_not_mem hJ hu hLn huL hu.mem) x hx

theorem Hyp.not_mem_component_of_ne (h : Hyp Φ) (hno : TL4.NoInvO2 Φ) {K : Subgroup Y}
    (hK : K ∈ Φ) {z : Y} (hz : IsUniqueInvolution K z) {L M : Subgroup Y}
    (hL : CFSG.IsComponent L) (hM : CFSG.IsComponent M) (hLM : L ≠ M) (hzL : z ∈ L) :
    z ∉ M := by
  intro hzM
  have hzZ := TightA.mem_centerLayer_of_mem_center hL hzL fun y hy =>
    comm_of_ne hL hM hLM hy hzM
  exact hno K hK z hz ⟨_, TightA.centerLayer_normal, TightA.centerLayer_isPGroup h.odd, hzZ⟩

theorem Hyp.eq_component_of_inv_mem (h : Hyp Φ) (hgen : omegaGen Φ = ⊤) (hno : TL4.NoInvO2 Φ)
    {L₀ : Subgroup Y} (hL₀ : CFSG.IsComponent L₀)
    (hmem : ∀ K ∈ Φ, ∀ z : Y, IsUniqueInvolution K z → z ∈ L₀) {M : Subgroup Y}
    (hM : CFSG.IsComponent M) : M = L₀ := by
  by_contra hML
  have hle : omegaGen Φ ≤ Subgroup.centralizer (M : Set Y) := by
    refine iSup₂_le fun K hK => ?_
    obtain ⟨z, hz⟩ := (h.hyp.omega1 K hK).1
    exact h.le_centralizer_of_not_mem hK hz (h.component_normal hgen hno hM)
      (h.not_mem_component_of_ne hno hK hz hL₀ hM (Ne.symm hML) (hmem K hK z hz))
  rw [hgen] at hle
  obtain ⟨a, b, hab⟩ := hM.1.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top (b' : Y)))) a' a'.2)

theorem Hyp.layer_eq_of_inv_mem (h : Hyp Φ) (hgen : omegaGen Φ = ⊤) (hno : TL4.NoInvO2 Φ)
    {L₀ : Subgroup Y} (hL₀ : CFSG.IsComponent L₀)
    (hmem : ∀ K ∈ Φ, ∀ z : Y, IsUniqueInvolution K z → z ∈ L₀) : layer Y = L₀ :=
  le_antisymm (sSup_le fun _ hM => (h.eq_component_of_inv_mem hgen hno hL₀ hmem hM).le)
    (le_sSup hL₀)

end S6

open S6

theorem thm3RFStar_proved : Thm3RFStar := by
  intro Y _ _ Φ K hΦ hK hO hgen htw hQ
  have h : S6.Hyp Φ := { toTypeRHyp := hΦ, odd := hO }
  have hno : TL4.NoInvO2 Φ := by
    rintro J - u hu ⟨P, hPn, hP2, huP⟩
    rw [hQ P hPn hP2] at huP
    exact hu.ne_one (Subgroup.mem_bot.mp huP)
  obtain ⟨z, hz⟩ := (hΦ.hyp.omega1 K hK).1
  obtain ⟨L₀, hL₀, hL₀n, hzL₀⟩ := h.exists_component hgen hno hK hz
  have hmem : ∀ J ∈ Φ, ∀ u : Y, IsUniqueInvolution J u → u ∈ L₀ := by
    intro J hJ u hu
    obtain ⟨g, M, ⟨-, w, hwK, hwM⟩, rfl⟩ := htw J hJ
    have hw : w = z := hwK.eq hz
    subst hw
    rw [hu.eq (hwM.conj g)]
    exact hL₀n.conj_mem w hzL₀ g
  have hlayer : layer Y = L₀ := h.layer_eq_of_inv_mem hgen hno hL₀ hmem
  have hfit : fittingSubgroup Y = ⊥ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [TL4.fittingSubgroup_eq_pCore hO]
    exact hQ _ pCore_normal pCore_isPGroup
  have hF : genFittingFStar Y = L₀ := by
    rw [CFSG.Adapters.genFittingFStar_eq_foundations, generalizedFitting.eq_sup, hfit, hlayer,
      bot_sup_eq]
  have hcl : layer Y ⊓ Subgroup.centralizer (layer Y : Set Y) = ⊥ :=
    hQ _ TightA.centerLayer_normal (TightA.centerLayer_isPGroup hO)
  have hZ : Subgroup.center ↥L₀ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxZ := TightA.mem_centerLayer_of_mem_center hL₀ x.2 fun y hy =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨y, hy⟩)
    rw [hcl] at hxZ
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hxZ))
  have hq : CFSG.Open.IsQuasisimple ↥L₀ := ((CFSG.isComponent_iff_open L₀).mp hL₀).2.2
  obtain ⟨hs, hnab⟩ := isSimpleGroup_of_quasisimple_of_center_eq_bot hq hZ
  unfold FStarSimple
  rw [hF]
  exact ⟨hs, hnab⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step
