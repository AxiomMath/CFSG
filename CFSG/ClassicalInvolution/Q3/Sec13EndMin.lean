module

public import CFSG.ClassicalInvolution.Q3.Sec13StarHyp
public import CFSG.ClassicalInvolution.Q3.TL3T39
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2Fam
public import CFSG.ClassicalInvolution.Asc77.AscS22B
public import CFSG.ClassicalInvolution.Asc77.AscT8X4
public import CFSG.ClassicalInvolution.Asc77.AscT8YA3
public import CFSG.ClassicalInvolution.AschTight.S1916Coh
public import CFSG.ClassicalInvolution.AschTight.S1916Inv
public import CFSG.ClassicalInvolution.AschTight.S19QT68
public import CFSG.ClassicalInvolution.AschTight.S19QTInv
public import CFSG.ClassicalInvolution.AschTight.S19QTSign
public import CFSG.ClassicalInvolution.AschTight.S19TF1
public import CFSG.ClassicalInvolution.Balance.CentralizedDeltaBasic
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.LargeFrameExits
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.PairInfCenter
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm1RTwin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinResF2Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711PfPerfect
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinConnFinalFrame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinConnFinalModel
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitE4Conn
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf6Q8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf8Exit
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtSylow
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPairOdd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE189a
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE189b
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEApply
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf182
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf2Base
public import CFSG.ClassicalInvolution.Q3.Q3AMDBStmt
public import CFSG.ClassicalInvolution.Q3.Q3MTShapeA
public import CFSG.ClassicalInvolution.Q3.Q3T6DCfg
public import CFSG.ClassicalInvolution.Q3.Q3T6DPart1
public import CFSG.ClassicalInvolution.Q3.Q3T6FusL3Sq
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDEnd
public import CFSG.ClassicalInvolution.Q3.Q3T8B10
public import CFSG.ClassicalInvolution.Q3.Q3TLKLink
public import CFSG.ClassicalInvolution.Q3.TL3S8Gold
public import CFSG.ClassicalInvolution.Q3.TL3S8Sd
public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrE2D
public import CFSG.ClassicalInvolution.Q3.TL4Conn26Nbr
public import CFSG.ClassicalInvolution.Q3.TL4Conn274M
public import CFSG.ClassicalInvolution.Q3.TL4D4NCCor
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7
public import CFSG.Foundations
public import CFSG.Goldschmidt.Steps.G310Core2
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.Goldschmidt75.TheoremB
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCore
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingEscape
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingInherit
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingOddQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingThreeOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Moufang.Three

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

abbrev spanQuotFam {G : Type} [Group G] (P : Set (Subgroup G)) :
    Set (Subgroup (↥(pSpan P) ⧸ classicalInvolutionOddCore ↥(pSpan P))) :=
  quotFamZ (classicalInvolutionOddCore ↥(pSpan P)) (restrictFamily P (pSpan P))

section QuotW

variable {H : Type} [Group H] [Finite H] {r : ℕ} {Ω : Set (Subgroup H)} {Z : Subgroup H}

theorem inf_eq_bot_of_odd (hZo : Odd (Nat.card Z)) {Q : Subgroup H} (hQ : IsPGroup 2 Q) :
    Z ⊓ Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
  rw [hk]
  exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hZo)

omit [Finite H] in
theorem exists_le_member_of_mem_USet (h2 : ∀ J ∈ Ω, IsPGroup 2 J) {U : Subgroup H}
    (hU : U ∈ USet Ω) : ∃ L ∈ Ω, U ≤ L ∧ U.relIndex L = 2 ∧ IsCyclic ↥U := by
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
  obtain ⟨L, hL, hRL, -, hmax⟩ := mem_RSet_iff.mp hR
  obtain rfl : L = R := hmax L le_rfl (h2 L hL) hRL
  exact ⟨L, hL, hUR, hidx, hcyc⟩

variable [Z.Normal]

local notation "πz" => QuotientGroup.mk' Z

theorem map_mem_USet_quotZ (hD : ThmDHypO r Ω) (hZK : ∀ K ∈ Ω, Z ⊓ K = ⊥) {U : Subgroup H}
    (hU : U ∈ USet Ω) : U.map πz ∈ USet (quotFamZ Z Ω) := by
  obtain ⟨L, hL, hUL, hidx, hcyc⟩ := exists_le_member_of_mem_USet hD.two hU
  refine ⟨L.map πz, TC.mem_RSet_of_isPGroup ⟨L, hL, rfl⟩ ((hD.two L hL).map _),
    Subgroup.map_mono hUL, isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective πz U), ?_⟩
  have hUZ : Z ⊓ U = ⊥ := eq_bot_iff.mpr ((inf_le_inf_left _ hUL).trans (hZK L hL).le)
  have h1 := Subgroup.relIndex_mul_card (U.map πz) (L.map πz)
  rw [inf_eq_left.mpr (Subgroup.map_mono hUL), card_map_mk_eq hUZ, card_map_mk_eq (hZK L hL)]
    at h1
  have h3 := Subgroup.relIndex_mul_card U L
  rw [inf_eq_left.mpr hUL, hidx] at h3
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h3.symm)

theorem le_of_map_le_quotZ (hD : ThmDHypO r Ω) (hZc : Z ≤ Subgroup.center H)
    (hZK : ∀ K ∈ Ω, Z ⊓ K = ⊥) {U J : Subgroup H} (hU : U ∈ USet Ω) (hJ : J ∈ Ω)
    (h : U.map πz ≤ J.map πz) : U ≤ J := by
  obtain ⟨K, hK, hUK, u, huU, hu2, -⟩ := TC.Thin.exists_of_mem_USet hD.hyp hU
  obtain ⟨j, hj, hju⟩ := h ⟨u, huU, rfl⟩
  have hc : j⁻¹ * u ∈ Z := by
    rw [← QuotientGroup.eq]
    exact hju
  have hKJ := eq_of_mem_sup_center hD.hyp hD.two hZc hZK hK hJ (hUK huU) hu2 hj hc (by group)
  exact hKJ ▸ hUK

theorem exists_lift_USet_quotZ (hD : ThmDHypO r Ω) (hZc : Z ≤ Subgroup.center H)
    (hZo : Odd (Nat.card Z)) {V : Subgroup (H ⧸ Z)} (hV : V ∈ USet (quotFamZ Z Ω))
    {S : Subgroup H} (hS2 : IsPGroup 2 S) (hVS : V ≤ S.map πz) :
    ∃ U ∈ USet Ω, U ≤ S ∧ U.map πz = V := by
  have hZK : ∀ K ∈ Ω, Z ⊓ K = ⊥ := fun K hK => inf_eq_bot_of_odd hZo (hD.two K hK)
  have hΩ' := (thmDHypO_quotZ hD hZc hZK).hyp
  obtain ⟨L', hL', hVL', v', hv'V, -, hzp'⟩ := TC.Thin.exists_of_mem_USet hΩ' hV
  obtain ⟨L, hL, rfl⟩ := hL'
  obtain ⟨u, huL, rfl⟩ := hVL' hv'V
  have hUL : Subgroup.zpowers u ≤ L := Subgroup.zpowers_le.mpr huL
  have hmap : (Subgroup.zpowers u).map πz = V := by
    rw [MonoidHom.map_zpowers, hzp']
  refine ⟨Subgroup.zpowers u, ?_, ?_, hmap⟩
  ·
    refine ⟨L, TC.mem_RSet_of_isPGroup hL (hD.two L hL), hUL, inferInstance, ?_⟩
    obtain ⟨R', hR', hVR', -, hidx⟩ := hV
    obtain ⟨L₂', hL₂', hR'L₂', -, hmax'⟩ := mem_RSet_iff.mp hR'
    obtain ⟨L₂, hL₂, rfl⟩ := hL₂'
    beta_reduce at hR'L₂' hmax'
    have hR'eq : L₂.map πz = R' := hmax' _ le_rfl ((hD.two L₂ hL₂).map _) hR'L₂'
    have hUZ : Z ⊓ Subgroup.zpowers u = ⊥ :=
      eq_bot_iff.mpr ((inf_le_inf_left _ hUL).trans (hZK L hL).le)
    have h1 := Subgroup.relIndex_mul_card V R'
    rw [inf_eq_left.mpr hVR', hidx, ← hR'eq, card_map_mk_eq (hZK L₂ hL₂), hD.card L₂ hL₂,
      ← hmap, card_map_mk_eq hUZ] at h1
    have h3 := Subgroup.relIndex_mul_card (Subgroup.zpowers u) L
    rw [inf_eq_left.mpr hUL, hD.card L hL] at h3
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h3.trans h1.symm)
  ·
    obtain ⟨s, hs, hsu⟩ := hVS hv'V
    have hc : s⁻¹ * u ∈ Z := by
      rw [← QuotientGroup.eq]
      exact hsu
    have hcomm : Commute s⁻¹ u := by
      have e := Subgroup.mem_center_iff.mp (hZc hc) s⁻¹
      calc s⁻¹ * u = s * (s⁻¹ * (s⁻¹ * u)) := by group
        _ = s * (s⁻¹ * u * s⁻¹) := by rw [e]
        _ = u * s⁻¹ := by group
    obtain ⟨k, hk⟩ := hD.two L hL ⟨u, huL⟩
    obtain ⟨m, hm⟩ := hS2 ⟨s, hs⟩
    have huk : u ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hsm : s ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hc2 : (s⁻¹ * u) ^ (2 ^ m * 2 ^ k) = 1 := by
      rw [hcomm.mul_pow, inv_pow, pow_mul s, hsm, one_pow, inv_one, one_mul, mul_comm,
        pow_mul u, huk, one_pow]
    have hc1 : s⁻¹ * u = 1 := by
      have h1 : orderOf (s⁻¹ * u) ∣ 2 ^ (m + k) := by
        rw [pow_add]
        exact orderOf_dvd_of_pow_eq_one hc2
      have h2 : orderOf (s⁻¹ * u) ∣ Nat.card Z := Subgroup.orderOf_dvd_natCard Z hc
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
        (Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hZo)) h1 h2)
    have hus : u = s := by
      calc u = s * (s⁻¹ * u) := by group
        _ = s := by rw [hc1, mul_one]
    exact Subgroup.zpowers_le.mpr (hus ▸ hs)

theorem map_mem_etaG_quotZ (hD : ThmDHypO r Ω) (hZc : Z ≤ Subgroup.center H)
    (hZo : Odd (Nat.card Z)) {η : Set (Subgroup H)} (hη : η ∈ etaG Ω) :
    (fun U : Subgroup H => U.map πz) '' η ∈ etaG (quotFamZ Z Ω) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj := QuotientGroup.mk'_surjective Z
  have hZK : ∀ K ∈ Ω, Z ⊓ K = ⊥ := fun K hK => inf_eq_bot_of_odd hZo (hD.two K hK)
  obtain ⟨S, ⟨hηsub, hηd, hηmax⟩, hinv⟩ := hη
  have hinj : ∀ {U U' : Subgroup H}, U ∈ USet Ω → U' ∈ USet Ω → U.map πz = U'.map πz →
      U = U' :=
    fun hU hU' h => eq_of_map_eq_of_mem_USet hD.hyp hD.two hZc hZK hU hU' h
  refine ⟨S.mapSurjective hsurj, ⟨?_, ?_, ?_⟩, ?_⟩
  · rintro _ ⟨U, hU, rfl⟩
    rw [Sylow.coe_mapSurjective]
    exact ⟨map_mem_USet_quotZ hD hZK (hηsub hU).1, Subgroup.map_mono (hηsub hU).2⟩
  · rintro _ ⟨U, hU, rfl⟩ _ ⟨U', hU', rfl⟩ hne J' hJ' ⟨h1, h2⟩
    obtain ⟨J, hJ, rfl⟩ := hJ'
    have hUU' : U ≠ U' := fun h => hne (by rw [h])
    exact hηd U hU U' hU' hUU' J hJ ⟨le_of_map_le_quotZ hD hZc hZK (hηsub hU).1 hJ h1,
      le_of_map_le_quotZ hD hZc hZK (hηsub hU').1 hJ h2⟩
  · intro η' hη'sub hη'd
    rw [Sylow.coe_mapSurjective] at hη'sub
    set η₀ : Set (Subgroup H) := {U | U ∈ USet Ω ∧ U ≤ S ∧ U.map πz ∈ η'}
    have himg : (fun U : Subgroup H => U.map πz) '' η₀ = η' := by
      ext V
      constructor
      · rintro ⟨U, ⟨-, -, hV⟩, rfl⟩
        exact hV
      · intro hV
        obtain ⟨U, hU, hUS, hUV⟩ :=
          exists_lift_USet_quotZ hD hZc hZo (hη'sub hV).1 S.isPGroup' (hη'sub hV).2
        exact ⟨U, ⟨hU, hUS, hUV ▸ hV⟩, hUV⟩
    have hinj₀ : Set.InjOn (fun U : Subgroup H => U.map πz) η₀ := fun U hU U' hU' h =>
      hinj hU.1 hU'.1 h
    have hinjη : Set.InjOn (fun U : Subgroup H => U.map πz) η := fun U hU U' hU' h =>
      hinj (hηsub hU).1 (hηsub hU').1 h
    rw [← himg, hinj₀.ncard_image, hinjη.ncard_image]
    refine hηmax η₀ (fun U hU => ⟨hU.1, hU.2.1⟩) ?_
    intro U hU U' hU' hne J hJ ⟨h1, h2⟩
    have hne' : U.map πz ≠ U'.map πz := fun h => hne (hinj hU.1 hU'.1 h)
    exact hη'd _ hU.2.2 _ hU'.2.2 hne' _ ⟨J, hJ, rfl⟩
      ⟨Subgroup.map_mono h1, Subgroup.map_mono h2⟩
  · intro s' hs' V hV
    rw [Sylow.coe_mapSurjective] at hs'
    obtain ⟨s, hs, rfl⟩ := hs'
    obtain ⟨U, hU, rfl⟩ := hV
    exact ⟨conjSub s U, hinv s hs U hU, TwistQ.conjSub_map s U⟩

theorem wSet_singleton_of_quotZ (hD : ThmDHypO r Ω) (hZc : Z ≤ Subgroup.center H)
    (hZo : Odd (Nat.card Z)) {W' : Subgroup (H ⧸ Z)} (hW' : WSet (quotFamZ Z Ω) = {W'}) :
    ∃ W : Subgroup H, WSet Ω = {W} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZK : ∀ K ∈ Ω, Z ⊓ K = ⊥ := fun K hK => inf_eq_bot_of_odd hZo (hD.two K hK)
  have hD' := thmDHypO_quotZ hD hZc hZK
  have hmapW : ∀ {η : Set (Subgroup H)}, η ∈ etaG Ω →
      (⨆ U ∈ η, U).map πz = ⨆ V ∈ (fun U : Subgroup H => U.map πz) '' η, V := by
    intro η _
    rw [iSup_image]
    simp only [Subgroup.map_iSup]
  have hto : ∀ {η : Set (Subgroup H)}, η ∈ etaG Ω → (⨆ U ∈ η, U).map πz = W' := by
    intro η hη
    have h1 : (⨆ U ∈ η, U).map πz ∈ WSet (quotFamZ Z Ω) :=
      ⟨_, map_mem_etaG_quotZ hD hZc hZo hη, hmapW hη⟩
    rw [hW'] at h1
    exact h1
  have hsub : ∀ {η η' : Set (Subgroup H)}, η ∈ etaG Ω → η' ∈ etaG Ω → η ⊆ η' := by
    intro η η' hη hη' U hU
    obtain ⟨S', hS', hinv'⟩ := map_mem_etaG_quotZ hD hZc hZo hη'
    have h69 := (Q3T8.Asc77.l6_9_proved _ (quotFamZ Z Ω) hD'.hyp S').2 _ hS' hinv'
    obtain ⟨S, hηS, -⟩ := id hη
    have hU' := hηS.1 hU
    have hUle : U.map πz ≤ ⨆ V ∈ (fun U : Subgroup H => U.map πz) '' η', V := by
      rw [← hmapW hη', hto hη', ← hto hη]
      exact Subgroup.map_mono (le_biSup (fun U => U) hU)
    have hmem : U.map πz ∈ (fun U : Subgroup H => U.map πz) '' η' := by
      rw [← h69.2]
      exact ⟨map_mem_USet_quotZ hD hZK hU'.1, hUle⟩
    obtain ⟨U'', hU'', hUU''⟩ := hmem
    obtain ⟨S₂, hη'S, -⟩ := hη'
    have heq := eq_of_map_eq_of_mem_USet hD.hyp hD.two hZc hZK (hη'S.1 hU'').1 hU'.1 hUU''
    rw [← heq]
    exact hU''
  obtain ⟨η₀, hη₀, hinv₀⟩ := (Q3T8.Asc77.l6_9_proved H Ω hD.hyp default).1
  have hη₀G : η₀ ∈ etaG Ω := ⟨default, hη₀, hinv₀⟩
  refine ⟨⨆ U ∈ η₀, U, ?_⟩
  ext W₁
  constructor
  · rintro ⟨η₁, hη₁, rfl⟩
    have h1 : η₁ = η₀ := le_antisymm (hsub hη₁ hη₀G) (hsub hη₀G hη₁)
    rw [h1]
    rfl
  · intro h
    rw [Set.mem_singleton_iff.mp h]
    exact ⟨η₀, hη₀G, rfl⟩

end QuotW

section Transfer

open scoped IsMulCommutative

variable {X : Type} [Group X] [Finite X]

theorem map_eq_one_of_closure_two {A : Type*} [Group A] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hA : IsPGroup p A)
    (hgen : Subgroup.closure {x : X | ∃ k : ℕ, x ^ 2 ^ k = 1} = ⊤) (φ : X →* A) (x : X) :
    φ x = 1 := by
  suffices h : (⊤ : Subgroup X) ≤ φ.ker from h (Subgroup.mem_top x)
  rw [← hgen, Subgroup.closure_le]
  rintro y ⟨k, hk⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  obtain ⟨j, hj⟩ := hA (φ y)
  have h1 : orderOf (φ y) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk, map_one])
  have hcop : Nat.Coprime (2 ^ k) (p ^ j) :=
    Nat.Coprime.pow k j ((Nat.coprime_primes Nat.prime_two hp.out).mpr (Ne.symm hp2))
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop h1 (orderOf_dvd_of_pow_eq_one hj))

theorem eq_one_of_mem_center_of_sylow {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hgen : Subgroup.closure {x : X | ∃ k : ℕ, x ^ 2 ^ k = 1} = ⊤) (T : Sylow p X)
    [IsMulCommutative ↥(T : Subgroup X)] {c : X} (hc : c ∈ Subgroup.center X)
    (hcT : c ∈ (T : Subgroup X)) : c = 1 := by
  have key : ∀ (k : ℕ) (g₀ : X), g₀⁻¹ * c ^ k * g₀ ∈ (T : Subgroup X) →
      g₀⁻¹ * c ^ k * g₀ = c ^ k := fun k g₀ _ => by
    rw [mul_assoc, ← Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hc k) g₀,
      inv_mul_cancel_left]
  have h1 := MonoidHom.transfer_eq_pow (MonoidHom.id ↥(T : Subgroup X)) c key
  have h2 : (MonoidHom.id ↥(T : Subgroup X)).transfer c = 1 :=
    map_eq_one_of_closure_two hp2 T.isPGroup' hgen _ c
  rw [h2, MonoidHom.id_apply] at h1
  have h3 : c ^ (T : Subgroup X).index = 1 := (congrArg Subtype.val h1).symm
  obtain ⟨j, hj⟩ := T.isPGroup' ⟨c, hcT⟩
  have h4 : orderOf c ∣ p ^ j :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hj)
  have hcop : Nat.Coprime (p ^ j) (T : Subgroup X).index :=
    Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr T.not_dvd_index)
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop h4 (orderOf_dvd_of_pow_eq_one h3))

theorem eq_bot_of_le_center_of_sq {R : Subgroup X} [R.Normal]
    (hgen : Subgroup.closure {x : X | ∃ k : ℕ, x ^ 2 ^ k = 1} = ⊤)
    (hR : R ≤ Subgroup.center X) (hRo : Odd (Nat.card R))
    (hsq : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ^ 2 ∣ Nat.card (X ⧸ R)) : R = ⊥ := by
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_bot]
  by_contra hr1
  have hn1 : orderOf r ≠ 1 := fun h => hr1 (orderOf_eq_one_iff.mp h)
  set p := (orderOf r).minFac
  have hp : p.Prime := Nat.minFac_prime hn1
  have : Fact p.Prime := ⟨hp⟩
  have hpn : p ∣ orderOf r := Nat.minFac_dvd _
  have hp2 : p ≠ 2 := by
    intro h2
    have h3 : 2 ∣ Nat.card R := h2 ▸ hpn.trans (Subgroup.orderOf_dvd_natCard R hr)
    exact (Nat.not_even_iff_odd.mpr hRo) (even_iff_two_dvd.mpr h3)
  set c := r ^ (orderOf r / p)
  have hc : orderOf c = p := orderOf_pow_orderOf_div (orderOf_pos r).ne' hpn
  have hcR : c ∈ R := R.pow_mem hr _
  have hcp : IsPGroup p ↥(Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc, pow_one])
  obtain ⟨T, hcT⟩ := hcp.exists_le_sylow
  set f : ↥(T : Subgroup X) →* X ⧸ R := (QuotientGroup.mk' R).comp (T : Subgroup X).subtype
  have hcyc : IsCyclic f.range := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
      (T.isPGroup'.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
    have hdvd : p ^ k ∣ Nat.card (X ⧸ R) := hk ▸ Subgroup.card_subgroup_dvd_card f.range
    have hk1 : k ≤ 1 := by
      by_contra hk1
      exact hsq p hp hp2 ((pow_dvd_pow p (by omega)).trans hdvd)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk1 with rfl | rfl
    · rw [pow_zero] at hk
      have := (Nat.card_eq_one_iff_unique.mp hk).1
      exact isCyclic_of_subsingleton
    · rw [pow_one] at hk
      exact isCyclic_of_prime_card hk
  have hker : f.rangeRestrict.ker ≤ Subgroup.center ↥(T : Subgroup X) := by
    intro x hx
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hx
    have hxR : (x : X) ∈ R := (QuotientGroup.eq_one_iff (x : X)).mp hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hR hxR) y)
  have := f.rangeRestrict.isMulCommutative_of_isCyclic_of_ker_le_center hker
  have hc1 := eq_one_of_mem_center_of_sylow hp2 hgen T (hR hcR) (hcT (Subgroup.mem_zpowers c))
  rw [hc1, orderOf_one] at hc
  exact hp.one_lt.ne hc

theorem not_sq_dvd_1344 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 2 ∣ 1344 := by
  intro h
  have hcop : Nat.Coprime (p ^ 2) (2 ^ 6) :=
    Nat.Coprime.pow 2 6 ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have h21 : p ^ 2 ∣ 21 := hcop.dvd_of_dvd_mul_left (by norm_num; exact h)
  have hle : p ^ 2 ≤ 21 := Nat.le_of_dvd (by norm_num) h21
  have hp4 : p ≤ 4 := by nlinarith
  interval_cases p
  · exact Nat.not_prime_zero hp
  · exact Nat.not_prime_one hp
  · exact hp2 rfl
  · norm_num at h21
  · norm_num at hp

omit [Finite X] in
theorem closure_two_eq_top {Λ : Set (Subgroup X)} (h2 : ∀ L ∈ Λ, IsPGroup 2 L)
    (hgen : pSpan Λ = ⊤) : Subgroup.closure {x : X | ∃ k : ℕ, x ^ 2 ^ k = 1} = ⊤ := by
  rw [eq_top_iff, ← hgen]
  refine pSpan_le fun L hL x hx => Subgroup.subset_closure ?_
  obtain ⟨k, hk⟩ := h2 L hL ⟨x, hx⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem oddCore_eq_bot_of_e8 (hgen : Subgroup.closure {x : X | ∃ k : ℕ, x ^ 2 ^ k = 1} = ⊤)
    (hR : classicalInvolutionOddCore X ≤ Subgroup.center X)
    {E : Subgroup (X ⧸ classicalInvolutionOddCore X)} (hE : E8Struct ⊤ E) :
    classicalInvolutionOddCore X = ⊥ :=
  eq_bot_of_le_center_of_sq hgen hR (QuaternionStructure.odd_natCard_oddCore X)
    fun p hp hp2 => by rw [card_e8 hE]; exact not_sq_dvd_1344 hp hp2

end Transfer

theorem e8Struct_comap_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {E : Subgroup Y}
    (hE : E8Struct (⊤ : Subgroup Y) E) : E8Struct (⊤ : Subgroup X) (E.comap e.toMonoidHom) where
  le := le_top
  normal x _ a ha := by
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hE.normal _ (Subgroup.mem_top _) _ ha
  card := by
    rw [Subgroup.comap_equiv_eq_map_symm', Subgroup.card_map_of_injective e.symm.injective,
      hE.card]
  sq a ha := e.injective (by rw [map_mul, map_one]; exact hE.sq _ ha)
  cent x _ hx := by
    refine hE.cent (e x) (Subgroup.mem_top _) fun b hb => ?_
    have hb' : e.symm b ∈ E.comap e.toMonoidHom := by
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      exact hb
    have h1 := congrArg e (hx _ hb')
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
  core Q _ hQn hQ2 := by
    rw [← Subgroup.map_le_iff_le_comap]
    refine hE.core _ le_top (fun y _ q hq => ?_) (hQ2.map _)
    obtain ⟨q', hq', rfl⟩ := hq
    obtain ⟨x, rfl⟩ := e.surjective y
    exact ⟨x * q' * x⁻¹, hQn x (Subgroup.mem_top x) q' hq', by simp⟩
  index := by
    have h1 := hE.index
    rw [Subgroup.relIndex_top_right] at h1 ⊢
    rw [Subgroup.index_comap_of_surjective _ e.surjective, h1]

section Outcome

variable {G : Type} [Group G]

@[expose] def SectionOutcome (P : Set (Subgroup G)) : Prop :=
  (∀ L ∈ P, ∀ L' ∈ P, L = L') ∨
    (∃ W : Subgroup G, WIn P (pSpan P) = {W}) ∨ (∃ E : Subgroup G, E8Struct (pSpan P) E) ∨
    Nonempty (AEIdentOn P 7 AE.e64Sets AE.e64Sub) ∨
    (∃ m : ℕ, 5 ≤ m ∧ Nonempty (AEIdent P m)) ∨
    Nonempty (AEIdentOn P 8 AE.e29Sets AE.e29Sub)

variable [Finite G]

@[expose] def SectionConcl (P : Set (Subgroup G)) : Prop :=
  ((∃ L ∈ P, ∃ L' ∈ P, ¬ ∃ x ∈ pSpan P, conjSub x L = L') ∧
      ∀ L ∈ P, ∀ L' ∈ P, (¬ ∃ x ∈ pSpan P, conjSub x L = L') → Commutes L L') ∨
    ((∀ L ∈ P, ∀ L' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L') ∧
      ThmDConcl (spanQuotFam P) ∧ SectionOutcome P)

theorem sectionOutcome_of_spanQuot {r : ℕ} {Ω : Set (Subgroup G)} (hD : ThmDHyp r Ω)
    {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (hc : ThmDConcl (spanQuotFam P)) : SectionOutcome P := by
  set X := pSpan P
  set R := classicalInvolutionOddCore ↥X
  have hLX : ∀ M ∈ P, M ≤ X := fun M hM => le_pSpan hM
  have hO := thmDHypO_restrict (r := r) hD.hyp hD.two hD.card hD.aEmpty hD.inO2 hPΩ hinv
  have hRc : R ≤ Subgroup.center ↥X := oddCore_le_center hD.hyp hD.two hD.inO2 hPΩ hinv
  have hRK : ∀ M ∈ restrictFamily P X, R ⊓ M = ⊥ := fun M hM =>
    oddCore_inf_eq_bot (hO.two M hM)
  have hmemX : ∀ M ∈ P, M.subgroupOf X ∈ restrictFamily P X := fun M hM =>
    ⟨M, hM, hLX M hM, rfl⟩
  rcases hc with hsing | ⟨W, hW⟩ | ⟨E, hE⟩ | ⟨I⟩ | ⟨m, hm, ⟨I⟩⟩ | ⟨I⟩
  ·
    refine Or.inl fun L hL L' hL' => ?_
    have h1 := hsing _ ⟨_, hmemX L hL, rfl⟩ _ ⟨_, hmemX L' hL', rfl⟩
    have h2 := TC.Thin.eq_of_map_eq hO.hyp hO.two hRc hRK (hmemX L hL) (hmemX L' hL') h1
    have h3 := Subgroup.subgroupOf_inj.mp h2
    rwa [inf_eq_left.mpr (hLX L hL), inf_eq_left.mpr (hLX L' hL')] at h3
  ·
    obtain ⟨W₀, hW₀⟩ :=
      wSet_singleton_of_quotZ hO hRc (QuaternionStructure.odd_natCard_oddCore _) hW
    exact Or.inr (Or.inl ⟨W₀.map X.subtype, by rw [WIn, hW₀, Set.image_singleton]⟩)
  ·
    have hodd : R = ⊥ := oddCore_eq_bot_of_e8 (closure_two_eq_top hO.two hO.gen) hRc hE
    let e : ↥X ≃* ↥X ⧸ R :=
      ((QuotientGroup.quotientMulEquivOfEq hodd).trans QuotientGroup.quotientBot).symm
    exact Or.inr (Or.inr (Or.inl ⟨_, (e8Struct_comap_mulEquiv e hE).map⟩))
  ·
    obtain ⟨I⟩ := I
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨AEIdentOn.ofRestrict hO.gen hLX (AEIdentOn.ofQuotZ hO hRc hRK I)⟩)))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm, ⟨AEIdent.ofSpanQuot hD hPΩ hinv I⟩⟩))))
  ·
    obtain ⟨I⟩ := I
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨AEIdentOn.ofRestrict hO.gen hLX (AEIdentOn.ofQuotZ hO hRc hRK I)⟩))))

end Outcome

variable {G : Type} [Group G] [Finite G]

namespace StarHyp

variable {Ω : Set (Subgroup G)} (h : StarHyp Ω)
include h

theorem commutes_of_not_conj {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω)
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) (hlt : Nat.card ↥(pSpan P) < Nat.card G)
    {L L' : Subgroup G} (hL : L ∈ P) (hL' : L' ∈ P) (hnc : ¬ ∃ x ∈ pSpan P, conjSub x L = L') :
    Commutes L L' :=
  comm_of_not_conj_span h.thmD (d1GenLeaf_holds 3 _ (thmDGenBelow_of_absBelow h.below)) hPΩ hlt
    hinv hL hL' hnc

theorem thmDConcl_section {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω)
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) (hlt : Nat.card ↥(pSpan P) < Nat.card G)
    (htrans : ∀ L ∈ P, ∀ L' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L') :
    ThmDConcl (spanQuotFam P) ∧ SectionOutcome P := by
  have hc := thmDConcl_spanQuot h.thmD h.below hPΩ hlt htrans hinv
  exact ⟨hc, sectionOutcome_of_spanQuot h.thmD hPΩ hinv hc⟩

theorem sectionConcl {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω)
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) (hlt : Nat.card ↥(pSpan P) < Nat.card G) :
    SectionConcl P := by
  by_cases htrans : ∀ L ∈ P, ∀ L' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L'
  · exact Or.inr ⟨htrans, h.thmDConcl_section hPΩ hinv hlt htrans⟩
  · refine Or.inl ⟨?_, fun L hL L' hL' hnc => h.commutes_of_not_conj hPΩ hinv hlt hL hL' hnc⟩
    by_contra hne
    exact htrans fun L hL L' hL' => by_contra fun h' => hne ⟨L, hL, L', hL', h'⟩

theorem conjSub_mem_centMembers {a : G} {L : Subgroup G} (hL : L ∈ Generic.centMembers Ω a)
    {x : G} (hx : x ∈ pSpan (Generic.centMembers Ω a)) :
    conjSub x L ∈ Generic.centMembers Ω a := by
  have hXC : pSpan (Generic.centMembers Ω a) ≤ Subgroup.centralizer ({a} : Set G) :=
    pSpan_le fun L hL => hL.2
  refine ⟨h.thmD.hyp.conjInvariant x L hL.1, fun y hy => ?_⟩
  rw [mem_conjSub_iff] at hy
  have e : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hXC hx) (hL.2 hy)) (Subgroup.inv_mem _ (hXC hx))

theorem card_pSpan_centMembers_lt {a : G} (ha : a ≠ 1) :
    Nat.card ↥(pSpan (Generic.centMembers Ω a)) < Nat.card G := by
  have hXC : pSpan (Generic.centMembers Ω a) ≤ Subgroup.centralizer ({a} : Set G) :=
    pSpan_le fun L hL => hL.2
  have hCt : Subgroup.centralizer ({a} : Set G) ≠ ⊤ := by
    intro htop
    apply ha
    have hzc : a ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subgroup.mem_centralizer_singleton_iff.mp (htop ▸ Subgroup.mem_top g)
    rw [h.center, Subgroup.mem_bot] at hzc
    exact hzc
  have := Subgroup.card_lt_of_lt (lt_of_le_of_lt hXC (lt_top_iff_ne_top.mpr hCt))
  rwa [Subgroup.card_top] at this

theorem sectionConcl_centMembers {a : G} (ha : a ≠ 1) :
    SectionConcl (Generic.centMembers Ω a) :=
  h.sectionConcl (fun _ hL => hL.1) (fun _ hL _ hx => h.conjSub_mem_centMembers hL hx)
    (h.card_pSpan_centMembers_lt ha)

end StarHyp

omit [Finite G] in
theorem dComp_subset_of_mem {Ω : Set (Subgroup G)} {K : Subgroup G} (hK : K ∈ Ω) :
    dComp Ω K ⊆ Ω := by
  intro J hJ
  induction hJ with
  | refl => exact hK
  | tail _ hbc _ => exact hbc.1

omit [Finite G] in
theorem le_sigmaNorm_of_mem_dComp {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    {K M : Subgroup G} (hK : K ∈ Ω) (hM : M ∈ dComp Ω K) : M ≤ sigmaNorm Ω K := by
  intro m hm N
  have hMm : ∀ {n : G}, n ∈ M → conjSub n M = M := fun hn =>
    mem_normalizer_iff_conjSub_eq.mp (Subgroup.le_normalizer hn)
  have hKM : ∀ {N : Subgroup G}, N ∈ dComp Ω M ↔ N ∈ dComp Ω K := fun {N} =>
    ⟨fun hN => Relation.ReflTransGen.trans hM hN,
      fun hN => Relation.ReflTransGen.trans (reflTransGen_dAdj_symm hK hM) hN⟩
  constructor
  · intro hN
    have h1 := Thompson.mem_dComp_conjSub hΩ (hKM.mpr hN) m
    rw [hMm hm] at h1
    exact hKM.mp h1
  · intro hN
    have h1 := Thompson.mem_dComp_conjSub hΩ (hKM.mpr hN) m⁻¹
    rw [conjSub_inv_conjSub, hMm (M.inv_mem hm)] at h1
    exact hKM.mp h1

namespace StarHyp

variable {Ω : Set (Subgroup G)} (h : StarHyp Ω)
include h

theorem conjSub_mem_dComp {K : Subgroup G} (hK : K ∈ Ω) {L : Subgroup G} (hL : L ∈ dComp Ω K)
    {x : G} (hx : x ∈ pSpan (dComp Ω K)) : conjSub x L ∈ dComp Ω K :=
  ((pSpan_le fun _ hM => le_sigmaNorm_of_mem_dComp h.thmD.hyp.conjInvariant hK hM) hx L).mp hL

theorem card_pSpan_dComp_lt (hdisc : ¬ Disconnected.DConnected Ω) {K : Subgroup G}
    (hK : K ∈ Ω) : Nat.card ↥(pSpan (dComp Ω K)) < Nat.card G := by
  have hle : pSpan (dComp Ω K) ≤ sigmaNorm Ω K :=
    pSpan_le fun _ hM => le_sigmaNorm_of_mem_dComp h.thmD.hyp.conjInvariant hK hM
  have hne : sigmaNorm Ω K ≠ ⊤ := by
    intro htop
    have hall : ∀ J ∈ Ω, J ∈ dComp Ω K := by
      intro J hJ
      obtain ⟨g, rfl⟩ := h.thmD.trans K hK J hJ
      have hg : g ∈ sigmaNorm Ω K := by
        rw [htop]
        exact Subgroup.mem_top g
      exact (hg K).mp Relation.ReflTransGen.refl
    exact hdisc fun L hL J hJ =>
      Relation.ReflTransGen.trans (reflTransGen_dAdj_symm hK (hall L hL)) (hall J hJ)
  have := Subgroup.card_lt_of_lt (lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hne))
  rwa [Subgroup.card_top] at this

theorem sectionConcl_dComp (hdisc : ¬ Disconnected.DConnected Ω) {K : Subgroup G}
    (hK : K ∈ Ω) : SectionConcl (dComp Ω K) :=
  h.sectionConcl (dComp_subset_of_mem hK) (fun _ hL _ hx => h.conjSub_mem_dComp hK hL hx)
    (h.card_pSpan_dComp_lt hdisc hK)

end StarHyp

end CFSG.ClassicalInvolution.Q3.Sec13
