module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQChev
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotUniqueFieldTorus
public import CFSG.LocalAnalysis.StandardType.MarkingChevalley
public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09Field
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQUni
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExcOrders
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotUniqueField


public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FQ

open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


section Count

theorem twisted_inf_image_card {k K : Type} [Field k] [Field K] (ι : k →+* K) (σk : k →+* k)
    (σK : K →+* K) (h : ι.comp σk = σK.comp ι) :
    Nat.card ↥(twistedFixedGroup TwistTag.E6 K σK ⊓
        (adjointGroup TwistTag.E6.tag k).map (baseChangeGL ι)) =
      Nat.card ↥(twistedFixedGroup TwistTag.E6 k σk) := by
  have hmap : (twistedFixedGroup TwistTag.E6 k σk).map (baseChangeGL ι) =
      twistedFixedGroup TwistTag.E6 K σK ⊓ (adjointGroup TwistTag.E6.tag k).map (baseChangeGL ι) := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨hyA, hyF⟩ := (mem_twistedFixedGroup_iff_twistHom _ _ _).1 hy
      have hJ : baseChangeGL ι y ∈ (adjointGroup TwistTag.E6.tag k).map (baseChangeGL ι) := ⟨y, hyA, rfl⟩
      refine ⟨(mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨?_, ?_⟩, hJ⟩
      · exact (adjointBaseChangeHom TwistTag.E6.tag ι ⟨y, hyA⟩).2
      · rw [twistHom_baseChangeGL ι h, hyF]
    · rintro x ⟨hxF, hxJ⟩
      obtain ⟨y, hyA, rfl⟩ := hxJ
      refine ⟨y, (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨hyA, ?_⟩, rfl⟩
      have := ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 hxF).2
      rw [twistHom_baseChangeGL ι h] at this
      exact baseChangeGL_injective ι this
  rw [← hmap]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ (baseChangeGL_injective ι)).toEquiv).symm


variable {K : Type} [Field K] [Finite K]

theorem twoPart_card_inf_entrywise (F : Subgroup (ModGL TwistTag.E6.tag K)) (σ' : K ≃+* K) {e : ℕ}
    (he : Nat.card (fixSubfield σ') = 2 ^ e) (he1 : 1 ≤ e) :
    twoPart (Nat.card ↥(F ⊓ entrywiseFixedGroup TwistTag.E6.tag σ')) =
      twoPart (Nat.card ↥(F ⊓ fixedFieldImage TwistTag.E6.tag σ')) := by
  set Γ := entrywiseFixedGroup TwistTag.E6.tag σ' with hΓ
  set J := fixedFieldImage TwistTag.E6.tag σ' with hJ
  have hJΓ : J ≤ Γ := fixedFieldImage_le
  set N : Subgroup ↥Γ := J.subgroupOf Γ with hN
  set A : Subgroup ↥Γ := F.subgroupOf Γ with hA
  haveI : N.Normal := fixedFieldImage_normal
  have h2 : N.relIndex A * Nat.card ↥(N ⊓ A) = Nat.card ↥A := Subgroup.relIndex_mul_card N A
  obtain ⟨-, hdq⟩ := fixedFieldImage_index_dvd_card (τ := TwistTag.E6.tag) σ'
  have hodd : Odd (N.relIndex A) := by
    refine Odd.of_dvd_nat ?_ ((Subgroup.relIndex_dvd_index_of_normal N A).trans hdq)
    rw [he]
    exact (Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one).pow
  have hAc : Nat.card ↥A = Nat.card ↥(F ⊓ Γ) := by
    rw [hA, ← Subgroup.inf_subgroupOf_right F Γ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hNA : Nat.card ↥(N ⊓ A) = Nat.card ↥(F ⊓ J) := by
    have : N ⊓ A = (J ⊓ F).subgroupOf Γ := by
      ext x
      simp only [hN, hA, Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [this]
    refine (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hJΓ)).toEquiv).trans ?_
    rw [inf_comm]
  rw [← hAc, ← h2, hNA]
  exact FP.twoPart_mul_odd hodd Nat.card_pos.ne'

end Count

section TwE6Fixed

variable {K : Type} [Field K] [Finite K]

theorem twistedFixedGroup_le_adjoint (σ : K →+* K) :
    twistedFixedGroup TwistTag.E6 K σ ≤ adjointGroup TwistTag.E6.tag K := inf_le_left

theorem twistedE6_perfect_card {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ (2 * f))
    (σ : K ≃+* K) (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) :
    ⁅twistedFixedGroup TwistTag.E6 K σ.toRingHom, twistedFixedGroup TwistTag.E6 K σ.toRingHom⁆ =
        twistedFixedGroup TwistTag.E6 K σ.toRingHom ∧
      Nat.card ↥(twistedFixedGroup TwistTag.E6 K σ.toRingHom) = CFSG.Open.ordTwistedE6 (2 ^ f) := by
  have hσσ : ∀ c, σ (σ c) = c :=
    CFSG.SeitzReduction.TwistedE6Pilot.sigma_apply_apply_of_sq_eq_one_twistedE6 hσ2
  obtain ⟨hperf, hcard⟩ :=
    CFSG.SeitzReduction.TwistedE6Pilot.fixSubgroup_graphField_perfect_card_twistedE6 hf hK σ hσ2 hσ1
  rw [CFSG.SeitzReduction.TwistedE6Pilot.fixSubgroup_graphField_eq_twistedE6 σ hσσ,
    ← CFSG.SeitzReduction.TwistedE6Pilot.twistedFixedGroup_eq_graphFixedRootGroup_twistedE6 hσσ]
    at hperf hcard
  set F := twistedFixedGroup TwistTag.E6 K σ.toRingHom with hF
  have hle : F ≤ adjointGroup TwistTag.E6.tag K := twistedFixedGroup_le_adjoint _
  have hmap : (F.subgroupOf (adjointGroup TwistTag.E6.tag K)).map (adjointGroup TwistTag.E6.tag K).subtype = F :=
    Subgroup.map_subgroupOf_eq_of_le hle
  refine ⟨?_, ?_⟩
  · conv_lhs => rw [← hmap]
    rw [← Subgroup.map_commutator, hperf, hmap]
  · rw [← hcard]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).symm

theorem center_twistedFixedGroup_E6 (σ : K ≃+* K) (hσσ : ∀ c, σ (σ c) = c) :
    Subgroup.center ↥(twistedFixedGroup TwistTag.E6 K σ.toRingHom) = ⊥ := by
  rw [CFSG.SeitzReduction.TwistedE6Pilot.twistedFixedGroup_eq_graphFixedRootGroup_twistedE6 hσσ]
  exact center_graphFixedRootGroup_eq_bot σ.surjective

end TwE6Fixed


section Frob

theorem exists_frobInvolution {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ (2 * n)) :
    ∃ σ : K ≃+* K, σ ^ 2 = 1 ∧ σ ≠ 1 ∧ ∀ c, σ c = c ^ 2 ^ n := by
  obtain ⟨φ, hφ, hφord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 2 * n) hK
  refine ⟨φ ^ n, ?_, ?_, fun c => ringAut_pow_apply_of_frobenius hφ n c⟩
  · rw [← pow_mul, show n * 2 = 2 * n by ring, ← hφord]
    exact pow_orderOf_eq_one φ
  · intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hφord] at h1
    have := Nat.le_of_dvd (by omega) h1
    omega

end Frob

section Numbers

open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.YS09Field

noncomputable def twFixS (t : TwistTag) (K : Type) [Field K] (S : (Fin t.tag.rank → ℤ) → Prop)
    (n : ℕ) (σ' : K ≃+* K) : ℕ :=
  Nat.card {g : MarkChev.GLS S K // g ∈ MarkChev.twistedH t.tag.cartan S K t.perm n ∧
    MarkChev.entrywise S K σ' (map_zero σ') (g : Module.End K (MarkChev.Space S K)) =
      (g : Module.End K (MarkChev.Space S K))}

noncomputable def twCardS (t : TwistTag) (K : Type) [Field K] (S : (Fin t.tag.rank → ℤ) → Prop)
    (n : ℕ) : ℕ :=
  Nat.card (MarkChev.twistedH t.tag.cartan S K t.perm n)

noncomputable def twCenterS (t : TwistTag) (K : Type) [Field K]
    (S : (Fin t.tag.rank → ℤ) → Prop) (n : ℕ) : ℕ :=
  Nat.card (Subgroup.center (MarkChev.twistedH t.tag.cartan S K t.perm n))

theorem fixNum_twisted (t : TwistTag) (K : Type) [Field K] (n : ℕ) (σ' : K ≃+* K) :
    fixNum (stableAct (chevAct t.tag.cartan K) (chevAct_one t.tag.cartan K)
      (chevAct_mul t.tag.cartan K) (LargeEvenTwistedH t.tag.cartan K t.perm n)
      (fun σ h hh => twisted_map_mem t.tag.cartan K t.perm n σ h hh) σ') =
      twFixS t K (LargeEvenIsRoot t.tag.cartan) n σ' := by
  rw [fixNum_stableAct]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
  rw [largeEvenTwistedH_eq, Units.ext_iff, chevAct_val]
  rfl

theorem card_twistedH (t : TwistTag) (K : Type) [Field K] (n : ℕ) :
    Nat.card (LargeEvenTwistedH t.tag.cartan K t.perm n) =
      twCardS t K (LargeEvenIsRoot t.tag.cartan) n := by
  rw [largeEvenTwistedH_eq]
  rfl

theorem card_center_twistedH (t : TwistTag) (K : Type) [Field K] (n : ℕ) :
    Nat.card (Subgroup.center (LargeEvenTwistedH t.tag.cartan K t.perm n)) =
      twCenterS t K (LargeEvenIsRoot t.tag.cartan) n := by
  rw [largeEvenTwistedH_eq]
  rfl

end Numbers


section BP

variable (K : Type) [Field K]

theorem twCardS_eq (n : ℕ) (σK : K →+* K) (hσK : ∀ c, σK c = c ^ 2 ^ n)
    (hperf : ⁅twistedFixedGroup TwistTag.E6 K σK, twistedFixedGroup TwistTag.E6 K σK⁆ =
      twistedFixedGroup TwistTag.E6 K σK) :
    twCardS TwistTag.E6 K (IsRoot TwistTag.E6.tag) n =
      Nat.card ↥(twistedFixedGroup TwistTag.E6 K σK) := by
  unfold twCardS
  rw [CFSG.StandardType.twistedH_eq_commutator K TwistTag.E6 n σK hσK, hperf]

theorem twCenterS_eq [Finite K] (n : ℕ) (σe : K ≃+* K) (hσe : ∀ c, σe c = c ^ 2 ^ n)
    (hperf : ⁅twistedFixedGroup TwistTag.E6 K σe.toRingHom,
      twistedFixedGroup TwistTag.E6 K σe.toRingHom⁆ = twistedFixedGroup TwistTag.E6 K σe.toRingHom)
    (hσσ : ∀ c, σe (σe c) = c) :
    twCenterS TwistTag.E6 K (IsRoot TwistTag.E6.tag) n = 1 := by
  unfold twCenterS
  rw [CFSG.StandardType.twistedH_eq_commutator K TwistTag.E6 n σe.toRingHom hσe, hperf,
    center_twistedFixedGroup_E6 σe hσσ]
  exact Subgroup.card_bot

theorem twFixS_eq [Finite K] (n : ℕ) (σe : K ≃+* K) (hσe : ∀ c, σe c = c ^ 2 ^ n)
    (hperf : ⁅twistedFixedGroup TwistTag.E6 K σe.toRingHom,
      twistedFixedGroup TwistTag.E6 K σe.toRingHom⁆ = twistedFixedGroup TwistTag.E6 K σe.toRingHom)
    (σ' : K ≃+* K) :
    twFixS TwistTag.E6 K (IsRoot TwistTag.E6.tag) n σ' =
      Nat.card ↥(twistedFixedGroup TwistTag.E6 K σe.toRingHom ⊓
        entrywiseFixedGroup TwistTag.E6.tag σ') := by
  unfold twFixS
  rw [CFSG.StandardType.twistedH_eq_commutator K TwistTag.E6 n σe.toRingHom hσe, hperf]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
  rw [Subgroup.mem_inf, mem_entrywiseFixedGroup]
  constructor
  · rintro ⟨hF, h⟩
    exact ⟨hF, twistedFixedGroup_le_adjoint _ hF, Units.ext h⟩
  · rintro ⟨hF, -, h⟩
    exact ⟨hF, congrArg Units.val h⟩

end BP


section Main

open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.YS09Field

@[expose] noncomputable def twRho (t : TwistTag) (K : Type) [Field K] (n : ℕ) :
    (K ≃+* K) →* MulAut ↥(LargeEvenTwistedH t.tag.cartan K t.perm n) :=
  stableAct (chevAct t.tag.cartan K) (chevAct_one t.tag.cartan K) (chevAct_mul t.tag.cartan K)
    (LargeEvenTwistedH t.tag.cartan K t.perm n)
    (fun σ h hh => twisted_map_mem t.tag.cartan K t.perm n σ h hh)

theorem stOrderBody_twE6 {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (I : Set (MulAut (LargeEvenCenterQuot
      (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n)))) :
    StOrderBody p (LargeEvenCenterQuot (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n)) I
      (LargeEvenChevFieldImage TwistTag.E6.tag.cartan K
        (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n)) := by
  have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨σe, hσ2, hσ1, hσe⟩ := exists_frobInvolution hn hK'
  have hσσ : ∀ c, σe (σe c) = c :=
    CFSG.SeitzReduction.TwistedE6Pilot.sigma_apply_apply_of_sq_eq_one_twistedE6 hσ2
  obtain ⟨hperf, hcardF⟩ := twistedE6_perfect_card hn hK' σe hσ2 hσ1
  have hσe' : ∀ c, σe.toRingHom c = c ^ 2 ^ n := hσe
  have hcardH : Nat.card ↥(LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n) =
      CFSG.Open.ordTwistedE6 (2 ^ n) := by
    rw [card_twistedH, largeEvenIsRoot_eq_isRoot, twCardS_eq K n σe.toRingHom hσe' hperf, hcardF]
  have hcenH : Nat.card (Subgroup.center ↥(LargeEvenTwistedH TwistTag.E6.tag.cartan K
      TwistTag.E6.perm n)) = 1 := by
    rw [card_center_twistedH, largeEvenIsRoot_eq_isRoot, twCenterS_eq K n σe hσe hperf hσσ]
  haveI : Finite ↥(LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hcardH]
    obtain ⟨r, hr, h⟩ := (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordTwistedE6' hn).two
    rw [h]
    exact (Nat.mul_pos (by positivity) hr.pos).ne'
  refine stOrderBody_of_action (u := 18) (v := 1) (m := 2 * n) (by omega) hK'
    (Subgroup.center (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n)) le_rfl ?_
    (twRho TwistTag.E6 K n) (fun σ => Odd (orderOf σ)) ?_ (by norm_num) one_pos ?_ ?_ hp ?_ I _ ?_
  · rw [hcenH]
    exact odd_one
  · intro σ hσ k
    exact Odd.of_dvd_nat hσ (orderOf_pow_dvd k)
  · rw [pow_one, hcardH, twoPart_of_profile (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordTwistedE6' hn)]
    exact congrArg (2 ^ ·) (by ring)
  · intro σ' hσ' e he
    obtain ⟨hdvd, hcard⟩ := card_fixedPoints_field (m := 2 * n) (by omega) hK' σ'
    have hee : e = 2 * n / orderOf σ' := Nat.pow_right_injective (le_refl 2) (he.symm.trans hcard)
    have hcop : (orderOf σ').Coprime 2 := (Nat.coprime_two_left.2 hσ').symm
    obtain ⟨j', hjj'⟩ := (Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd : orderOf σ' ∣ n)
    have hr0 : 0 < orderOf σ' := Nat.pos_of_dvd_of_pos hdvd (by omega)
    have hee' : e = 2 * j' := by
      rw [hee, hjj', ← mul_assoc, mul_comm 2 (orderOf σ'), mul_assoc, Nat.mul_div_cancel_left _ hr0]
    have hj' : 1 ≤ j' := by
      rcases Nat.eq_zero_or_pos j' with h0 | h0
      · rw [h0, mul_zero] at hjj'; omega
      · exact h0
    have hk : Nat.card (fixF σ') = (2 ^ j') ^ 2 := by
      rw [card_fixF.trans he, hee', pow_mul']
    have hk' : Nat.card (fixF σ') = 2 ^ (2 * j') := by rw [hk, ← pow_mul, mul_comm]
    have he1 : 1 ≤ e := by omega
    obtain ⟨σS, hσS2, hσS1, hσS⟩ := exists_frobInvolution (K := fixSubfield σ') hj' hk'
    have hcomm : ∀ c : fixSubfield σ', ((σS.toRingHom c : fixSubfield σ') : K) =
        σe.toRingHom c := by
      intro c
      have h1 : (σS.toRingHom c : fixSubfield σ') = c ^ 2 ^ j' := hσS c
      have h2 : c ^ 2 ^ (j' * orderOf σ') = c ^ 2 ^ j' := pow_two_pow_mul_of_odd hk hσ' c
      rw [h1, ← h2, hσe', ← SubmonoidClass.coe_pow, mul_comm j' (orderOf σ'), ← hjj']
    have h2 := twisted_inf_image_card (fixSubfield σ').subtype σS.toRingHom σe.toRingHom
      (RingHom.ext fun c => hcomm c)
    have h3 := twoPart_card_inf_entrywise (twistedFixedGroup TwistTag.E6 K σe.toRingHom) σ'
      (card_fixF.trans he) he1
    have h4 := (twistedE6_perfect_card hj' hk' σS hσS2 hσS1).2
    have h5 : fixNum (twRho TwistTag.E6 K n σ') = Nat.card ↥(twistedFixedGroup TwistTag.E6 K
        σe.toRingHom ⊓ entrywiseFixedGroup TwistTag.E6.tag σ') := by
      show fixNum (stableAct _ _ _ _ _ σ') = _
      rw [fixNum_twisted, largeEvenIsRoot_eq_isRoot, twFixS_eq K n σe hσe hperf σ']
    rw [pow_one, h5, h3]
    change twoPart (Nat.card ↥(twistedFixedGroup TwistTag.E6 K σe.toRingHom ⊓
      (adjointGroup TwistTag.E6.tag (fixSubfield σ')).map
        (baseChangeGL (fixSubfield σ').subtype))) = _
    rw [h2, h4, twoPart_of_profile (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordTwistedE6' hj'),
      hee']
    exact congrArg (2 ^ ·) (by ring)
  · intro σ
    obtain ⟨hdvd, -⟩ := card_fixedPoints_field (m := 2 * n) (by omega) hK' σ
    have hr0 : orderOf σ ≠ 0 := (Nat.pos_of_dvd_of_pos hdvd (by omega)).ne'
    obtain ⟨a, c, hc, hac⟩ := Nat.exists_eq_two_pow_mul_odd hr0
    refine ⟨2 ^ a, fun h => hp2 ?_, ?_⟩
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    · rw [orderOf_pow' _ (by positivity), hac, Nat.gcd_eq_right (Dvd.intro c rfl),
        Nat.mul_div_cancel_left c (by positivity)]
      exact hc
  · rintro f ⟨σ, hσ⟩
    refine ⟨σ, fun x => ?_⟩
    exact hσ x (twRho TwistTag.E6 K n σ x) (by
      show ((chevAct TwistTag.E6.tag.cartan K σ (x : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
        LargeEvenChevGL TwistTag.E6.tag.cartan K) : Module.End K (LargeEvenChevModule
          TwistTag.E6.tag.cartan K)) = _
      rw [chevAct_val])

end Main

end FQ

end CFSG.LocalAnalysis.GLTheoremA
