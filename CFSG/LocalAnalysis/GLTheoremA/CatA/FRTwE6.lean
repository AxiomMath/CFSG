module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRChev
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQTwE6

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FR

open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP
open CFSG.LocalAnalysis.GLTheoremA.FQ CFSG.LocalAnalysis.GLTheoremA.YS09Field CFSG.Assembly
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
open scoped commutatorElement


theorem twCore (K : Type) [Field K] [Finite K] (σe σ' : K ≃+* K) {e : ℕ}
    (he : Nat.card (fixSubfield σ') = 2 ^ e) (he1 : 1 ≤ e)
    (σS : ↥(fixSubfield σ') ≃+* ↥(fixSubfield σ'))
    (hcomm : (fixSubfield σ').subtype.comp σS.toRingHom =
      σe.toRingHom.comp (fixSubfield σ').subtype) :
    ∃ J : Subgroup (ModGL TwistTag.E6.tag K),
      J ≤ twistedFixedGroup TwistTag.E6 K σe.toRingHom ⊓ entrywiseFixedGroup TwistTag.E6.tag σ' ∧
      ⁅twistedFixedGroup TwistTag.E6 K σe.toRingHom ⊓ entrywiseFixedGroup TwistTag.E6.tag σ',
        twistedFixedGroup TwistTag.E6 K σe.toRingHom ⊓ entrywiseFixedGroup TwistTag.E6.tag σ'⁆ ≤ J ∧
      Odd (J.relIndex (twistedFixedGroup TwistTag.E6 K σe.toRingHom ⊓
        entrywiseFixedGroup TwistTag.E6.tag σ')) ∧
      Nonempty (↥J ≃* ↥(twistedFixedGroup TwistTag.E6 (fixSubfield σ') σS.toRingHom)) := by
  set F := twistedFixedGroup TwistTag.E6 K σe.toRingHom with hF
  set Γ' := entrywiseFixedGroup TwistTag.E6.tag σ' with hΓ'
  set Jc := fixedFieldImage TwistTag.E6.tag σ' with hJc
  set ι : ↥(fixSubfield σ') →+* K := (fixSubfield σ').subtype with hι
  have hmap : (twistedFixedGroup TwistTag.E6 (fixSubfield σ') σS.toRingHom).map (baseChangeGL ι) =
      F ⊓ Jc := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨hyA, hyF⟩ := (mem_twistedFixedGroup_iff_twistHom _ _ _).1 hy
      have hJ : baseChangeGL ι y ∈ Jc := ⟨y, hyA, rfl⟩
      refine ⟨(mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨?_, ?_⟩, hJ⟩
      · exact (adjointBaseChangeHom TwistTag.E6.tag ι ⟨y, hyA⟩).2
      · rw [twistHom_baseChangeGL ι hcomm, hyF]
    · rintro x ⟨hxF, hxJ⟩
      obtain ⟨y, hyA, rfl⟩ := hxJ
      refine ⟨y, (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨hyA, ?_⟩, rfl⟩
      have := ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 hxF).2
      rw [twistHom_baseChangeGL ι hcomm] at this
      exact baseChangeGL_injective ι this
  refine ⟨F ⊓ Jc, inf_le_inf_left F fixedFieldImage_le, ?_, ?_, ?_⟩
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    exact ⟨by simpa [commutatorElement_def] using F.mul_mem (F.mul_mem (F.mul_mem hx.1 hy.1) (F.inv_mem hx.1)) (F.inv_mem hy.1), commutator_entrywise_le TwistTag.E6.tag σ'
      (Subgroup.commutator_mem_commutator hx.2 hy.2)⟩
  · have h1 : (F ⊓ Jc) = Jc ⊓ (F ⊓ Γ') := by
      ext x
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨hF', hJ'⟩
        exact ⟨hJ', hF', fixedFieldImage_le hJ'⟩
      · rintro ⟨hJ', hF', -⟩
        exact ⟨hF', hJ'⟩
    rw [h1, Subgroup.inf_relIndex_right]
    obtain ⟨-, hdq⟩ := fixedFieldImage_index_dvd_card (τ := TwistTag.E6.tag) σ'
    have hodd : Odd (Jc.relIndex Γ') := by
      refine Odd.of_dvd_nat ?_ hdq
      rw [he]
      exact (Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one).pow
    haveI : (Jc.subgroupOf Γ').Normal := fixedFieldImage_normal
    have h3 : (Jc.subgroupOf Γ').relIndex ((F ⊓ Γ').subgroupOf Γ') = Jc.relIndex (F ⊓ Γ') :=
      Subgroup.relIndex_subgroupOf inf_le_right
    have h4 := Subgroup.relIndex_dvd_index_of_normal (Jc.subgroupOf Γ') ((F ⊓ Γ').subgroupOf Γ')
    rw [h3] at h4
    exact Odd.of_dvd_nat hodd h4
  · rw [← hmap]
    exact ⟨(Subgroup.equivMapOfInjective _ _ (baseChangeGL_injective ι)).symm⟩

theorem twSub (K : Type) [Field K] [Finite K] (σe σ' : K ≃+* K) {e n : ℕ}
    (he : Nat.card (fixSubfield σ') = 2 ^ e) (he1 : 1 ≤ e)
    (σS : ↥(fixSubfield σ') ≃+* ↥(fixSubfield σ'))
    (hcomm : (fixSubfield σ').subtype.comp σS.toRingHom =
      σe.toRingHom.comp (fixSubfield σ').subtype) (hσe : ∀ c, σe c = c ^ 2 ^ n)
    (hperf : ⁅twistedFixedGroup TwistTag.E6 K σe.toRingHom,
      twistedFixedGroup TwistTag.E6 K σe.toRingHom⁆ = twistedFixedGroup TwistTag.E6 K σe.toRingHom)
    (S : (Fin TwistTag.E6.tag.rank → ℤ) → Prop) (hS : S = IsRoot TwistTag.E6.tag)
    (Γ : Subgroup (MarkChev.GLS S K))
    (hΓ : ∀ g, g ∈ Γ ↔ g ∈ MarkChev.twistedH TwistTag.E6.tag.cartan S K TwistTag.E6.perm n ∧
      MarkChev.entrywise S K σ' (map_zero σ') (g : Module.End K (MarkChev.Space S K)) =
        (g : Module.End K (MarkChev.Space S K))) :
    ∃ J : Subgroup (MarkChev.GLS S K), J ≤ Γ ∧ ⁅Γ, Γ⁆ ≤ J ∧ Odd (J.relIndex Γ) ∧
      Nonempty (↥J ≃* ↥(twistedFixedGroup TwistTag.E6 (fixSubfield σ') σS.toRingHom)) := by
  subst hS
  have hΓ' : Γ = twistedFixedGroup TwistTag.E6 K σe.toRingHom ⊓
      entrywiseFixedGroup TwistTag.E6.tag σ' := by
    ext g
    rw [hΓ, twistedH_eq_commutator K TwistTag.E6 n σe.toRingHom hσe, hperf, Subgroup.mem_inf,
      mem_entrywiseFixedGroup]
    constructor
    · rintro ⟨hF, h⟩
      exact ⟨hF, twistedFixedGroup_le_adjoint _ hF, Units.ext h⟩
    · rintro ⟨hF, -, h⟩
      exact ⟨hF, congrArg Units.val h⟩
  subst hΓ'
  exact twCore K σe σ' he he1 σS hcomm

theorem twistedH_equiv (k : Type) [Field k] (σS : k ≃+* k) (n' : ℕ) (hσS' : ∀ c, σS c = c ^ 2 ^ n')
    (hperf : ⁅twistedFixedGroup TwistTag.E6 k σS.toRingHom, twistedFixedGroup TwistTag.E6 k σS.toRingHom⁆ =
      twistedFixedGroup TwistTag.E6 k σS.toRingHom) :
    Nonempty (↥(twistedFixedGroup TwistTag.E6 k σS.toRingHom) ≃*
      ↥(LargeEvenTwistedH TwistTag.E6.tag.cartan k TwistTag.E6.perm n')) := by
  have key : ∀ S : (Fin TwistTag.E6.tag.rank → ℤ) → Prop, S = IsRoot TwistTag.E6.tag →
      Nonempty (↥(twistedFixedGroup TwistTag.E6 k σS.toRingHom) ≃*
        ↥(MarkChev.twistedH TwistTag.E6.tag.cartan S k TwistTag.E6.perm n')) := by
    intro S hS
    subst hS
    exact ⟨MulEquiv.subgroupCongr (by
      rw [twistedH_eq_commutator k TwistTag.E6 n' σS.toRingHom hσS', hperf])⟩
  obtain ⟨e⟩ := key _ (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag)
  exact ⟨e.trans (MulEquiv.subgroupCongr (largeEvenTwistedH_eq TwistTag.E6.tag.cartan k
    TwistTag.E6.perm n').symm)⟩

theorem nonempty_equiv_centerQuot' {G : Type*} [Group G] (h : Subgroup.center G = ⊥) :
    Nonempty (G ≃* G ⧸ Subgroup.center G) :=
  ⟨(QuotientGroup.quotientBot).symm.trans (QuotientGroup.quotientMulEquivOfEq h.symm)⟩

theorem subBody_twE6 {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (I : Set (MulAut (LargeEvenCenterQuot
      (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n)))) :
    ∀ f ∈ LargeEvenChevFieldImage TwistTag.E6.tag.cartan K
        (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n), orderOf f = p →
      p ∣ n ∧ ∃ D : Subgroup (LargeEvenCenterQuot
          (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n)),
        SubfieldGrp f D ∧ LargeEvenRecipeTwisted (LargeEvenCartanE 6) LargeEvenRhoE6 2 (n / p)
          (fun R' _ _ _ => Nonempty (↥D ≃* R')) := by
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
  set H : Subgroup (LargeEvenChevGL TwistTag.E6.tag.cartan K) :=
    LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n with hH
  have hcen : Subgroup.center ↥H = ⊥ := Subgroup.eq_bot_of_card_eq _ hcenH
  have hZo : Odd (Nat.card (Subgroup.center ↥H)) := by rw [hcenH]; exact odd_one
  rintro f ⟨σ, hσ⟩ hord
  have hσ' : ∀ x : ↥H, f (QuotientGroup.mk x) = QuotientGroup.mk (twRho TwistTag.E6 K n σ x) :=
    fun x => hσ x (twRho TwistTag.E6 K n σ x) (by
      show ((chevAct TwistTag.E6.tag.cartan K σ (x : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
        LargeEvenChevGL TwistTag.E6.tag.cartan K) : Module.End K (LargeEvenChevModule
          TwistTag.E6.tag.cartan K)) = _
      rw [chevAct_val])
  have hordH : twoPart (Nat.card ↥H) ^ 1 = 2 ^ (2 * n * 18) := by
    rw [pow_one, hH, hcardH, twoPart_of_profile (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordTwistedE6' hn)]
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
  obtain ⟨m, hm, hσ₀ord, hgood, hσm⟩ := sigma_order (m := 2 * n) (by omega) hK'
    (Subgroup.center ↥H) le_rfl hZo (twRho TwistTag.E6 K n) (fun σ => Odd (orderOf σ))
    (fun σ hσ k => Odd.of_dvd_nat hσ (orderOf_pow_dvd k)) (u := 18) (v := 1) (by norm_num) one_pos
    hordH hfix hp hred f σ hσ' hord
  set σ₀ : K ≃+* K := σ ^ m with hσ₀
  obtain ⟨hdvd, hcard⟩ := card_fixedPoints_field (m := 2 * n) (by omega) hK' σ₀
  rw [hσ₀ord] at hdvd hcard
  have hpn : p ∣ n := ((Nat.coprime_primes hp Nat.prime_two).2 hp2).dvd_of_dvd_mul_left hdvd
  have hdiv : 2 * n / p = 2 * (n / p) := by
    obtain ⟨c, hc⟩ := hpn
    rw [hc, show 2 * (p * c) = p * (2 * c) by ring, Nat.mul_div_cancel_left _ hp.pos,
      Nat.mul_div_cancel_left _ hp.pos]
  have hj' : 1 ≤ n / p := by
    have := one_le_of_card_fixed hcard
    omega
  have hk' : Nat.card (fixSubfield σ₀) = 2 ^ (2 * (n / p)) := by
    rw [card_fixF.trans hcard, hdiv]
  have hk : Nat.card (fixSubfield σ₀) = (2 ^ (n / p)) ^ 2 := by
    rw [hk', ← pow_mul, mul_comm]
  have he1 : 1 ≤ 2 * (n / p) := by omega
  obtain ⟨σS, hσS2, hσS1, hσS⟩ := exists_frobInvolution (K := fixSubfield σ₀) hj' hk'
  have hσS' : ∀ c, σS.toRingHom c = c ^ 2 ^ (n / p) := hσS
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hcomm : (fixSubfield σ₀).subtype.comp σS.toRingHom =
      σe.toRingHom.comp (fixSubfield σ₀).subtype := by
    refine RingHom.ext fun c => ?_
    have h1 : (σS.toRingHom c : fixSubfield σ₀) = c ^ 2 ^ (n / p) := hσS c
    have h2 : c ^ 2 ^ ((n / p) * p) = c ^ 2 ^ (n / p) := pow_two_pow_mul_of_odd hk hpodd c
    have hnp : n = (n / p) * p := (Nat.div_mul_cancel hpn).symm
    show ((σS.toRingHom c : fixSubfield σ₀) : K) = σe.toRingHom (c : K)
    rw [h1, ← h2, hσe', ← SubmonoidClass.coe_pow, ← hnp]
  have hσσ' : ∀ c, σS (σS c) = c :=
    CFSG.SeitzReduction.TwistedE6Pilot.sigma_apply_apply_of_sq_eq_one_twistedE6 hσS2
  obtain ⟨hperfk, -⟩ := twistedE6_perfect_card hj' hk' σS hσS2 hσS1
  obtain ⟨J, hJΓ, hJc, hJodd, ⟨eJ⟩⟩ := twSub K σe σ₀ hk' he1 σS hcomm hσe hperf
    (LargeEvenIsRoot TwistTag.E6.tag.cartan) (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag)
    ((FP.fixSub (twRho TwistTag.E6 K n σ₀)).map H.subtype) (fun g => by
      rw [show MarkChev.twistedH TwistTag.E6.tag.cartan (LargeEvenIsRoot TwistTag.E6.tag.cartan) K
          TwistTag.E6.perm n = H from (largeEvenTwistedH_eq TwistTag.E6.tag.cartan K
          TwistTag.E6.perm n).symm]
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨x.2, ?_⟩
        have h1 : twRho TwistTag.E6 K n σ₀ x = x := FP.mem_fixSub.1 hx
        have h2 : chevAct TwistTag.E6.tag.cartan K σ₀ (x : LargeEvenChevGL TwistTag.E6.tag.cartan K) =
            (x : LargeEvenChevGL TwistTag.E6.tag.cartan K) := congrArg Subtype.val h1
        have h5 : LargeEvenEntrywise TwistTag.E6.tag.cartan K (⇑σ₀) (map_zero σ₀)
            ((x : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
              Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) =
            ((x : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
              Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) := by
          rw [← chevAct_val]
          exact congrArg (fun y : LargeEvenChevGL TwistTag.E6.tag.cartan K =>
            (y : Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K))) h2
        exact h5
      · rintro ⟨hg, hfx⟩
        refine ⟨⟨g, hg⟩, FP.mem_fixSub.2 (Subtype.ext ?_), rfl⟩
        apply Units.ext
        have h3 : ((twRho TwistTag.E6 K n σ₀ ⟨g, hg⟩ : ↥H) :
            LargeEvenChevGL TwistTag.E6.tag.cartan K) =
            chevAct TwistTag.E6.tag.cartan K σ₀ g := rfl
        show ((twRho TwistTag.E6 K n σ₀ ⟨g, hg⟩ : ↥H) :
          LargeEvenChevGL TwistTag.E6.tag.cartan K).val = g.val
        rw [h3, chevAct_val]
        exact hfx)
  obtain ⟨hDT, -, -⟩ := subfield_core (Subgroup.center ↥H) le_rfl hZo (twRho TwistTag.E6 K n σ₀)
    (f ^ m) hσm
  have hfeq := fixSub_pow_eq hp hord hm
  set C : Subgroup ↥H := FP.fixSub (twRho TwistTag.E6 K n σ₀) with hC
  set π : ↥H →* ↥H ⧸ Subgroup.center ↥H := QuotientGroup.mk' (Subgroup.center ↥H) with hπ
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, hπ, QuotientGroup.ker_mk', hcen]
  have hJH : J ≤ H := hJΓ.trans (Subgroup.map_subtype_le _)
  have hJhC : J.subgroupOf H ≤ C := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hJΓ hx
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  have hTC : FP.fixSub (f ^ m) = C.map π := by
    refine le_antisymm (fun a ha => ?_) hDT
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    refine ⟨x, FP.mem_fixSub.2 (hπinj ?_), rfl⟩
    have h1 : (f ^ m) (QuotientGroup.mk x) = QuotientGroup.mk x := FP.mem_fixSub.1 ha
    rw [hσm x] at h1
    exact h1
  have hTf : FP.fixSub f = C.map π := hfeq.symm.trans hTC
  refine ⟨hpn, (J.subgroupOf H).map π, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hTf]
    exact Subgroup.map_mono hJhC
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [hTf] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    refine ⟨⁅x, y⁆, ?_, map_commutatorElement π x y⟩
    have hc := hJc (Subgroup.commutator_mem_commutator
      (⟨x, hx, rfl⟩ : (x : LargeEvenChevGL TwistTag.E6.tag.cartan K) ∈ C.map H.subtype)
      (⟨y, hy, rfl⟩ : (y : LargeEvenChevGL TwistTag.E6.tag.cartan K) ∈ C.map H.subtype))
    show ⁅x, y⁆ ∈ J.subgroupOf H
    rw [Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def] using hc
  · rw [hTf, Subgroup.relIndex_map_map_of_injective _ _ hπinj,
      ← Subgroup.relIndex_map_map_of_injective (f := H.subtype) _ _ H.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hJH]
    exact hJodd
  · refine ⟨↥(fixSubfield σ₀), inferInstance, inferInstance, hk, ?_⟩
    have hcenk : Subgroup.center ↥(LargeEvenTwistedH TwistTag.E6.tag.cartan ↥(fixSubfield σ₀)
        TwistTag.E6.perm (n / p)) = ⊥ := by
      refine Subgroup.eq_bot_of_card_eq _ ?_
      rw [card_center_twistedH, largeEvenIsRoot_eq_isRoot,
        twCenterS_eq _ (n / p) σS hσS hperfk hσσ']
    obtain ⟨eZ⟩ := nonempty_equiv_centerQuot' hcenk
    obtain ⟨eT⟩ := twistedH_equiv ↥(fixSubfield σ₀) σS (n / p) hσS hperfk
    exact ⟨((J.subgroupOf H).equivMapOfInjective π hπinj).symm.trans
      ((Subgroup.subgroupOfEquivOfLe hJH).trans (eJ.trans (eT.trans eZ)))⟩

end FR

end CFSG.LocalAnalysis.GLTheoremA
