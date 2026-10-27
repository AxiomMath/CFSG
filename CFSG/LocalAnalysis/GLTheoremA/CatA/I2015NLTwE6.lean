module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLAct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRTwE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP
  CFSG.LocalAnalysis.GLTheoremA.FQ CFSG.LocalAnalysis.GLTheoremA.YS09Field CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType

local notation "twH[" n ", " K "]" =>
  LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n

section Cyclic

theorem twE6ZpowersEq {G : Type*} [Group G] [Finite G] {a b c : G} (hc : Subgroup.zpowers c = ⊤)
    (h : orderOf a = orderOf b) : Subgroup.zpowers a = Subgroup.zpowers b := by
  haveI : IsCyclic G := isCyclic_iff_exists_zpowers_eq_top.2 ⟨c, hc⟩
  exact IsCyclic.subgroup_eq_iff_card_eq.2 (by rw [Nat.card_zpowers, Nat.card_zpowers, h])

theorem twE6ApplyEqOfMemZpowers {K : Type} [Field K] {κ σ₀ : K ≃+* K}
    (h : σ₀ ∈ Subgroup.zpowers κ) {c : K} (hc : κ c = c) : σ₀ c = c := by
  have h1 : Subgroup.zpowers κ ≤ MulAction.stabilizer (K ≃+* K) c := by
    rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, RingAut.smul_def]
    exact hc
  have h2 := h1 h
  rwa [MulAction.mem_stabilizer_iff, RingAut.smul_def] at h2

end Cyclic

section Fixed

theorem twE6RhoFixed {n : ℕ} {K : Type} [Field K] (σ' : K ≃+* K)
    (x : ↥(LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n)) :
    twRho TwistTag.E6 K n σ' x = x ↔
      LargeEvenEntrywise TwistTag.E6.tag.cartan K σ' (map_zero σ')
        (((x : ↥(LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n)) :
          LargeEvenChevGL TwistTag.E6.tag.cartan K) :
            Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) =
        (((x : ↥(LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n)) :
          LargeEvenChevGL TwistTag.E6.tag.cartan K) :
            Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) := by
  constructor
  · intro h
    have h1 : chevAct TwistTag.E6.tag.cartan K σ'
        (x : LargeEvenChevGL TwistTag.E6.tag.cartan K) =
        (x : LargeEvenChevGL TwistTag.E6.tag.cartan K) := congrArg Subtype.val h
    rw [← chevAct_val]
    exact congrArg (fun y : LargeEvenChevGL TwistTag.E6.tag.cartan K =>
      (y : Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K))) h1
  · intro h
    refine Subtype.ext (Units.ext ?_)
    exact h

end Fixed

section Twisted

set_option linter.unusedSectionVars false


theorem twE6Model {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σe : K ≃+* K) (hσ2 : σe ^ 2 = 1) (hσ1 : σe ≠ 1)
    (hσe : ∀ c, σe c = c ^ 2 ^ n) (S : (Fin TwistTag.E6.tag.rank → ℤ) → Prop)
    (hS : S = IsRoot TwistTag.E6.tag) (H' : Subgroup (MarkChev.GLS S K))
    (hH' : H' = MarkChev.twistedH TwistTag.E6.tag.cartan S K TwistTag.E6.perm n) :
    ∃ e : (↥H' ⧸ Subgroup.center ↥H') ≃* ↥(graphFixedRootGroup TwistTag.E6 K σe.toRingHom),
      ∀ (σ' : K ≃+* K) (x : ↥H'),
        MarkChev.entrywise S K σ' (map_zero σ')
            (((x : ↥H') : MarkChev.GLS S K) : Module.End K (MarkChev.Space S K)) =
          (((x : ↥H') : MarkChev.GLS S K) : Module.End K (MarkChev.Space S K)) ↔
          Units.map (entrywiseHom σ'.toRingHom)
            (e (QuotientGroup.mk x) : ModGL TwistTag.E6.tag K) = e (QuotientGroup.mk x) := by
  subst hS
  have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  have hσσ : ∀ c, σe (σe c) = c :=
    CFSG.SeitzReduction.TwistedE6Pilot.sigma_apply_apply_of_sq_eq_one_twistedE6 hσ2
  obtain ⟨hperf, -⟩ := twistedE6_perfect_card hn hK' σe hσ2 hσ1
  have hHP : H' = graphFixedRootGroup TwistTag.E6 K σe.toRingHom := by
    rw [hH', twistedH_eq_commutator K TwistTag.E6 n σe.toRingHom hσe, hperf,
      CFSG.SeitzReduction.TwistedE6Pilot.twistedFixedGroup_eq_graphFixedRootGroup_twistedE6 hσσ]
  subst hHP
  have hcen : Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 K σe.toRingHom) = ⊥ := by
    have h := center_twistedFixedGroup_E6 σe hσσ
    rwa [CFSG.SeitzReduction.TwistedE6Pilot.twistedFixedGroup_eq_graphFixedRootGroup_twistedE6
      hσσ] at h
  have hinj : Function.Injective (QuotientGroup.mk'
      (Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 K σe.toRingHom))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact hcen
  let ψ := MulEquiv.ofBijective (QuotientGroup.mk'
    (Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 K σe.toRingHom)))
    ⟨hinj, QuotientGroup.mk_surjective⟩
  refine ⟨ψ.symm, fun σ' x => ?_⟩
  have hx : ψ.symm (QuotientGroup.mk x) = x := ψ.symm_apply_eq.2 rfl
  rw [hx]
  exact ⟨fun h => Units.ext h, fun h => congrArg Units.val h⟩

theorem twE6SigmaZero {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {f : MulAut (LargeEvenCenterQuot (twH[n, K]))}
    (hf : f ∈ LargeEvenChevFieldImage TwistTag.E6.tag.cartan K (twH[n, K])) (hord : orderOf f = p) :
    ∃ σ₀ : K ≃+* K, orderOf σ₀ = p ∧ p ∣ n ∧
      ∀ x : ↥(twH[n, K]), twRho TwistTag.E6 K n σ₀ x = x →
        f (QuotientGroup.mk x) = QuotientGroup.mk x := by
  obtain ⟨σ, hσ⟩ := hf
  have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨σe, hσ2, hσ1, hσe⟩ := exists_frobInvolution hn hK'
  have hσσ : ∀ c, σe (σe c) = c :=
    CFSG.SeitzReduction.TwistedE6Pilot.sigma_apply_apply_of_sq_eq_one_twistedE6 hσ2
  obtain ⟨hperf, hcardF⟩ := twistedE6_perfect_card hn hK' σe hσ2 hσ1
  have hσe' : ∀ c, σe.toRingHom c = c ^ 2 ^ n := hσe
  have hcardH : Nat.card ↥(twH[n, K]) = CFSG.Open.ordTwistedE6 (2 ^ n) := by
    rw [card_twistedH, largeEvenIsRoot_eq_isRoot, twCardS_eq K n σe.toRingHom hσe' hperf, hcardF]
  have hcenH : Nat.card (Subgroup.center ↥(twH[n, K])) = 1 := by
    rw [card_center_twistedH, largeEvenIsRoot_eq_isRoot, twCenterS_eq K n σe hσe hperf hσσ]
  haveI : Finite ↥(twH[n, K]) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hcardH]
    obtain ⟨r, hr, h⟩ := (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordTwistedE6' hn).two
    rw [h]
    exact (Nat.mul_pos (by positivity) hr.pos).ne'
  have hZo : Odd (Nat.card (Subgroup.center ↥(twH[n, K]))) := by rw [hcenH]; exact odd_one
  have hσ' : ∀ x : ↥(twH[n, K]),
      f (QuotientGroup.mk x) = QuotientGroup.mk (twRho TwistTag.E6 K n σ x) :=
    fun x => hσ x (twRho TwistTag.E6 K n σ x) (by
      show ((chevAct TwistTag.E6.tag.cartan K σ (x : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
        LargeEvenChevGL TwistTag.E6.tag.cartan K) : Module.End K (LargeEvenChevModule
          TwistTag.E6.tag.cartan K)) = _
      rw [chevAct_val])
  have hordH : twoPart (Nat.card ↥(twH[n, K])) ^ 1 = 2 ^ (2 * n * 18) := by
    rw [pow_one, hcardH,
      twoPart_of_profile (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordTwistedE6' hn)]
    exact congrArg (2 ^ ·) (by ring)
  have hfix : ∀ σ' : K ≃+* K, Odd (orderOf σ') → ∀ e : ℕ, Nat.card {x : K // σ' x = x} = 2 ^ e →
      twoPart (FP.fixNum (twRho TwistTag.E6 K n σ')) ^ 1 = 2 ^ (e * 18) := by
    intro σ' hσ' e he
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
    have h5 : FP.fixNum (twRho TwistTag.E6 K n σ') = Nat.card ↥(twistedFixedGroup TwistTag.E6 K
        σe.toRingHom ⊓ entrywiseFixedGroup TwistTag.E6.tag σ') := by
      show FP.fixNum (stableAct _ _ _ _ _ σ') = _
      rw [fixNum_twisted, largeEvenIsRoot_eq_isRoot, twFixS_eq K n σe hσe hperf σ']
    rw [pow_one, h5, h3]
    change twoPart (Nat.card ↥(twistedFixedGroup TwistTag.E6 K σe.toRingHom ⊓
      (adjointGroup TwistTag.E6.tag (fixSubfield σ')).map
        (baseChangeGL (fixSubfield σ').subtype))) = _
    rw [h2, h4, twoPart_of_profile (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordTwistedE6' hj'),
      hee']
    exact congrArg (2 ^ ·) (by ring)
  have hred : ∀ σ : K ≃+* K, ∃ m : ℕ, ¬ p ∣ m ∧ Odd (orderOf (σ ^ m)) := by
    intro σ
    obtain ⟨hdvd, -⟩ := card_fixedPoints_field (m := 2 * n) (by omega) hK' σ
    have hr0 : orderOf σ ≠ 0 := (Nat.pos_of_dvd_of_pos hdvd (by omega)).ne'
    obtain ⟨a, c, hc, hac⟩ := Nat.exists_eq_two_pow_mul_odd hr0
    refine ⟨2 ^ a, fun h => hp2 ?_, ?_⟩
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    · rw [orderOf_pow' _ (by positivity), hac, Nat.gcd_eq_right (Dvd.intro c rfl),
        Nat.mul_div_cancel_left c (by positivity)]
      exact hc
  obtain ⟨σ₀, hσ₀ord, -, hdvd, -, hfixed⟩ := fixed_of_action (m := 2 * n) (by omega) hK'
    (Subgroup.center ↥(twH[n, K])) le_rfl hZo (twRho TwistTag.E6 K n) (fun σ => Odd (orderOf σ))
    (fun σ hσ k => Odd.of_dvd_nat hσ (orderOf_pow_dvd k)) (u := 18) (v := 1) (by norm_num) one_pos
    hordH hfix hp hred f σ hσ' hord
  exact ⟨σ₀, hσ₀ord, ((Nat.coprime_primes hp Nat.prime_two).2 hp2).dvd_of_dvd_mul_left hdvd,
    hfixed⟩

end Twisted

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
