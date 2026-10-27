module

public import CFSG.CharacterTheory.Wreathed.PrimewisePerfectLift
public import CFSG.CharacterTheory.Wreathed.ConditionalCompatibleModelData
public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2

public noncomputable section

open scoped Classical Pointwise

namespace CFSG.Wreathed.PrimewiseLayerFieldElimination

open CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.FullCentralizerFromProjectiveModel
  CFSG.Semidihedral.ProjectiveSL2Cover CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem layer_normal_quasisimple_even
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ)
    (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    (CFSG.layer (centralizerOddCoreQuotient n S e)).Normal ∧
      CFSG.IsQuasisimple (CFSG.layer (centralizerOddCoreQuotient n S e)) ∧
      Even (Nat.card (CFSG.layer (centralizerOddCoreQuotient n S e) ⧸
        Subgroup.center (CFSG.layer (centralizerOddCoreQuotient n S e)))) := by
  have hU := wreathed_centralizer_unique_component_data hnonab n hn S e hfour
  rw [hU.layer]
  refine ⟨hU.normal, hU.quasisimple, ?_⟩
  obtain ⟨φ⟩ := hU.actual_quotient
  rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq
    (hU.center.trans hU.restriction_kernel.symm)).trans φ).toEquiv]
  exact centralizerSimpleLayer_even hnonab n hn S e hfour

theorem mul_pow_orderOf_eq_of_sq_eq_one {X : Type*} [Group X] {t a : X} (ht : t ^ 2 = 1)
    (hta : Commute t a) (hd : Odd (orderOf a)) : (t * a) ^ orderOf a = t := by
  rw [hta.mul_pow, pow_orderOf_eq_one, mul_one]
  obtain ⟨k, hk⟩ := hd
  rw [hk, pow_succ, pow_mul, ht, one_pow, one_mul]

omit [IsSimpleGroup G] in
theorem odd_orderOf_of_mem_oddCore (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {r : involutionCentralizer n S e} (hr : r ∈ centralizerOddCore n S e) : Odd (orderOf r) := by
  have h : orderOf r ∣ Nat.card (centralizerOddCore n S e) := by
    rw [show orderOf r = orderOf (⟨r, hr⟩ : centralizerOddCore n S e) from
      (Subgroup.orderOf_mk r hr).symm]
    exact orderOf_dvd_natCard _
  exact (centralizerOddCore_card_odd n S e).of_dvd_nat h

omit [Finite G] [IsSimpleGroup G] in
theorem centralInvolution_sq (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralInvolution n S e ^ 2 = 1 := by
  have h := centralizerKernelInvolution_original_order n hn S e
  rw [← h]
  exact pow_orderOf_eq_one _

theorem centralInvolution_mem
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (J : Subgroup (involutionCentralizer n S e))
    (hJM : J.map (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e)) :
    centralInvolution n S e ∈ J := by
  have hx : centralizerOddCoreMap n S e (centralInvolution n S e) ∈
      J.map (centralizerOddCoreMap n S e) := by
    rw [hJM]
    exact centralizerActualLayer_involution_mem hnonab n hn S e hfour
  obtain ⟨j, hjJ, hj⟩ := Subgroup.mem_map.mp hx
  obtain ⟨r, hr, hjr⟩ := (QuotientGroup.mk'_eq_mk' (centralizerOddCore n S e)).mp hj.symm
  have hcomm : Commute (centralInvolution n S e) r :=
    ((Subgroup.mem_center_iff.mp (centralInvolution_mem_center n S e)) r).symm
  have h := mul_pow_orderOf_eq_of_sq_eq_one (centralInvolution_sq n hn S e) hcomm
    (odd_orderOf_of_mem_oddCore n S e hr)
  rw [hjr] at h
  rw [← h]
  exact J.pow_mem hjJ _

theorem kernel_bound
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f)
    (J : Subgroup (involutionCentralizer n S e)) (hJperf : Group.IsPerfect J)
    (hJM : J.map (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e))
    (hEJ : (J ⊓ centralizerOddCore n S e).subgroupOf J ≤ Subgroup.center J) :
    (p ^ f ≠ 9 → J ⊓ centralizerOddCore n S e = ⊥) ∧
      (p ^ f = 9 → IsCyclic ↥(J ⊓ centralizerOddCore n S e) ∧
        (Nat.card ↥(J ⊓ centralizerOddCore n S e) = 1 ∨
          Nat.card ↥(J ⊓ centralizerOddCore n S e) = 3)) := by
  obtain ⟨F, hF, hFfin, hcard, -, -, theta, rho, eta, -, hdata⟩ :=
    actual_projective_model_centralizer_data hnonab n hn S e hfour p f hp hpodd hf hmodel
  let : Field F := hF
  let : Finite F := hFfin
  let : Fact p.Prime := ⟨hp⟩
  have hxJ : centralInvolution n S e ∈ J := centralInvolution_mem hnonab n hn S e hfour J hJM
  let xJ : J := ⟨centralInvolution n S e, hxJ⟩
  have hπJmem : ∀ j : J, centralizerOddCoreMap n S e j ∈
      CFSG.layer (centralizerOddCoreQuotient n S e) :=
    fun j => hJM ▸ Subgroup.mem_map_of_mem (centralizerOddCoreMap n S e) j.2
  let πJ : J →* CFSG.layer (centralizerOddCoreQuotient n S e) :=
    ((centralizerOddCoreMap n S e).comp J.subtype).codRestrict _ hπJmem
  have hπJsurj : Function.Surjective πJ := by
    intro u
    have hu : (u : centralizerOddCoreQuotient n S e) ∈ J.map (centralizerOddCoreMap n S e) := by
      rw [hJM]
      exact u.2
    obtain ⟨j, hjJ, hj⟩ := Subgroup.mem_map.mp hu
    exact ⟨⟨j, hjJ⟩, Subtype.ext hj⟩
  let ρJ : J →* Matrix.SpecialLinearGroup (Fin 2) F := eta.toMonoidHom.comp πJ
  have hρJsurj : Function.Surjective ρJ := eta.surjective.comp hπJsurj
  have hρJx : ρJ xJ = minusIdentity F := by
    have h1 : πJ xJ = centralizerActualLayerInvolution hnonab n hn S e hfour := Subtype.ext rfl
    change eta (πJ xJ) = minusIdentity F
    rw [h1]
    exact hdata.involution
  have hρJker : ∀ j : J, ρJ j = 1 ↔
      (j : involutionCentralizer n S e) ∈ centralizerOddCore n S e := by
    intro j
    change eta (πJ j) = 1 ↔ _
    rw [map_eq_one_iff _ eta.injective]
    constructor
    · intro h
      exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)
  let Zj : Subgroup J := (Subgroup.zpowers (centralInvolution n S e)).subgroupOf J
  have hZjcenter : Zj ≤ Subgroup.center J := by
    intro z hz
    have hzc : (z : involutionCentralizer n S e) ∈
        Subgroup.center (involutionCentralizer n S e) :=
      (Subgroup.zpowers_le.mpr (centralInvolution_mem_center n S e)) hz
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext ((Subgroup.mem_center_iff.mp hzc) w)
  have : Zj.Normal := Subgroup.normal_of_le_center hZjcenter
  let φ : J →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F := (nativeQuotient F).comp ρJ
  have hφx : φ xJ = 1 := by
    change nativeQuotient F (ρJ xJ) = 1
    rw [hρJx]
    exact nativeQuotient_minusIdentity F
  have hZjker : Zj ≤ φ.ker := by
    intro z hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hz' : z = xJ ^ k := Subtype.ext (by rw [SubgroupClass.coe_zpow]; exact hk.symm)
    rw [MonoidHom.mem_ker, hz', map_zpow, hφx, one_zpow]
  let φbar : J ⧸ Zj →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    QuotientGroup.lift Zj φ hZjker
  let π₀ : J ⧸ Zj →* CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSL 2 F) :=
    (CFSG.SectionRank.OddCover.pslEquiv F).toMonoidHom.comp φbar
  have hφsurj : Function.Surjective φ := (nativeQuotient_surjective F).comp hρJsurj
  have hπ₀surj : Function.Surjective π₀ := by
    intro y
    obtain ⟨w, rfl⟩ := (CFSG.SectionRank.OddCover.pslEquiv F).surjective y
    obtain ⟨j, rfl⟩ := hφsurj w
    exact ⟨(j : J ⧸ Zj), rfl⟩
  have hπ₀ker : π₀.ker = φbar.ker := by
    ext z
    simp only [π₀, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, map_eq_one_iff _ (CFSG.SectionRank.OddCover.pslEquiv F).injective]
  have hkerφ : ∀ j : J, φ j = 1 → ∃ z : J,
      (z : involutionCentralizer n S e) ∈ J ⊓ centralizerOddCore n S e ∧
      ∃ k : ℤ, j = z * xJ ^ k := by
    intro j hj
    have hmem : ρJ j ∈ (nativeQuotient F).ker := hj
    rw [nativeQuotient_ker] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine ⟨j * (xJ ^ k)⁻¹, ⟨(j * (xJ ^ k)⁻¹).2, ?_⟩, k, by group⟩
    apply (hρJker _).mp
    rw [map_mul, map_inv, map_zpow, hρJx, hk, mul_inv_cancel]
  let E := J ⊓ centralizerOddCore n S e
  let ι : E →* J ⧸ Zj := (QuotientGroup.mk' Zj).comp (Subgroup.inclusion inf_le_left)
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have h1 : Subgroup.inclusion (inf_le_left : E ≤ J) z ∈ Zj :=
      (QuotientGroup.eq_one_iff _).mp hz
    have h2 : (z : involutionCentralizer n S e) ∈ Subgroup.zpowers (centralInvolution n S e) := h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h2
    have hz2 : (z : involutionCentralizer n S e) ^ 2 = 1 := by
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        centralInvolution_sq n hn S e, one_zpow]
    have hzodd := odd_orderOf_of_mem_oddCore n S e z.2.2
    have hz1 : (z : involutionCentralizer n S e) = 1 := by
      have hdvd : orderOf (z : involutionCentralizer n S e) ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact orderOf_eq_one_iff.mp h
      · rw [h] at hzodd
        exact absurd hzodd (by decide)
    exact Subtype.ext hz1
  have hιrange : ι.range = φbar.ker := by
    ext q
    constructor
    · rintro ⟨z, rfl⟩
      rw [MonoidHom.mem_ker]
      change φ (Subgroup.inclusion inf_le_left z) = 1
      change nativeQuotient F (ρJ (Subgroup.inclusion inf_le_left z)) = 1
      rw [(hρJker _).mpr z.2.2, map_one]
    · intro hq
      obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
      have hj : φ j = 1 := hq
      obtain ⟨z, hzE, k, hjz⟩ := hkerφ j hj
      refine ⟨⟨z, hzE⟩, ?_⟩
      have hxk : ((xJ ^ k : J) : J ⧸ Zj) = 1 := by
        rw [QuotientGroup.eq_one_iff]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
      change ((Subgroup.inclusion inf_le_left ⟨(z : involutionCentralizer n S e), hzE⟩ : J) :
        J ⧸ Zj) = (j : J ⧸ Zj)
      rw [hjz, QuotientGroup.mk_mul, hxk, mul_one]
      rfl
  let eE : E ≃* φbar.ker := (MonoidHom.ofInjective hιinj).trans (MulEquiv.subgroupCongr hιrange)
  have hkercentral : π₀.ker ≤ Subgroup.center (J ⧸ Zj) := by
    rw [hπ₀ker, ← hιrange]
    rintro _ ⟨z, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    have hzc : Subgroup.inclusion (inf_le_left : E ≤ J) z ∈ Subgroup.center J :=
      hEJ (show Subgroup.inclusion inf_le_left z ∈ E.subgroupOf J from z.2)
    change (w : J ⧸ Zj) * ((Subgroup.inclusion inf_le_left z : J) : J ⧸ Zj) =
      ((Subgroup.inclusion inf_le_left z : J) : J ⧸ Zj) * (w : J ⧸ Zj)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (Subgroup.mem_center_iff.mp hzc) w]
  have hEodd : Odd (Nat.card E) :=
    (centralizerOddCore_card_odd n S e).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hkerodd : Odd (Nat.card π₀.ker) := by
    rw [hπ₀ker, ← Nat.card_congr eE.toEquiv]
    exact hEodd
  have hbound := CFSG.SectionRank.OddCover.odd_psl_two_perfect_odd_cover_kernel hpodd hcard π₀
    hπ₀surj hkercentral hkerodd
  have hcardE : Nat.card E = Nat.card π₀.ker := by
    rw [hπ₀ker]
    exact Nat.card_congr eE.toEquiv
  refine ⟨fun hne => ?_, fun h9 => ?_⟩
  · have hker1 := hbound.1 hne
    rw [hker1, Subgroup.card_bot] at hcardE
    exact Subgroup.card_eq_one.mp hcardE
  · obtain ⟨hcyc, hcard3⟩ := hbound.2 h9
    have hEcyc : IsCyclic E := by
      rw [hπ₀ker] at hcyc
      exact isCyclic_of_surjective eE.symm.toMonoidHom eE.symm.surjective
    refine ⟨hEcyc, ?_⟩
    change Nat.card E = 1 ∨ Nat.card E = 3
    have h1 : Nat.card E ≤ 3 := hcardE ▸ hcard3
    have h0 : 0 < Nat.card E := Nat.card_pos
    obtain ⟨k, hk⟩ := hEodd
    omega

theorem canonical_lift
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (hcov : ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card (centralizerOddCore n S e) →
      ∃ P : Sylow ell (centralizerOddCore n S e),
        (Subgroup.centralizer (((P : Subgroup (centralizerOddCore n S e)).map
            (centralizerOddCore n S e).subtype) : Set (involutionCentralizer n S e)) ⊓
          (CFSG.layer (centralizerOddCoreQuotient n S e)).comap (centralizerOddCoreMap n S e)).map
            (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e)) :
    let N := involutionCentralizer n S e
    let R := centralizerOddCore n S e
    let π := centralizerOddCoreMap n S e
    let M := CFSG.layer (centralizerOddCoreQuotient n S e)
    let Y := M.comap π
    let H₀ := Y ⊓ Subgroup.centralizer (R : Set N)
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    let E := J ⊓ R
    Group.IsPerfect J ∧ J.Normal ∧ J ≤ Y ∧ J.map π = M ∧ ⁅J, R⁆ = ⊥ ∧ J ⊔ R = Y ∧
      (Y : Set N) = (J : Set N) * (R : Set N) ∧ Odd (Nat.card E) ∧
      E.subgroupOf J ≤ Subgroup.center J ∧ E.subgroupOf R ≤ Subgroup.center R := by
  intro N R π M Y H₀ J E
  obtain ⟨hMnormal, hquasi, heven⟩ := layer_normal_quasisimple_even hnonab n hn S e hfour
  let : (show Subgroup (involutionCentralizer n S e ⧸ centralizerOddCore n S e) from
      CFSG.layer (centralizerOddCoreQuotient n S e)).Normal := hMnormal
  obtain ⟨h1, h2, h3, h4, -, h6, h7, h8, h9, h10, h11, -⟩ :=
    PrimewisePerfectLift.primewise_Sylow_centralizer_coverage_gives_canonical_perfect_lift
      (G := involutionCentralizer n S e) (centralizerOddCore n S e)
      (centralizerOddCore_card_odd n S e) (CFSG.layer (centralizerOddCoreQuotient n S e))
      hquasi heven hcov
  exact ⟨h1, h2, h3, h4, h6, h7, h8, h9, h10, h11⟩

theorem exists_prod_mulEquiv {X : Type*} [Group X] (J R Y : Subgroup X) [R.Normal]
    (hJR : ⁅J, R⁆ = ⊥) (hY : J ⊔ R = Y) (hE : J ⊓ R = ⊥) :
    ∃ μ : J × R ≃* Y, ∀ z : J × R, (μ z : X) = z.1 * z.2 := by
  have hJcent : J ≤ Subgroup.centralizer (R : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJR
  let μ0 : J × R →* X := J.subtype.noncommCoprod R.subtype fun j r =>
    ((Subgroup.mem_centralizer_iff.mp (hJcent j.2)) r r.2).symm
  have hμ0Y : ∀ z : J × R, μ0 z ∈ Y := fun z => hY ▸ Subgroup.mul_mem _
    (Subgroup.mem_sup_left z.1.2) (Subgroup.mem_sup_right z.2.2)
  let μ : J × R →* Y := μ0.codRestrict Y hμ0Y
  have hμinj : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have h1 : (z.1 : X) * z.2 = 1 := congrArg Subtype.val hz
    have h2 : (z.1 : X) = (z.2 : X)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : (z.1 : X) ∈ J ⊓ R := ⟨z.1.2, h2 ▸ R.inv_mem z.2.2⟩
    rw [hE, Subgroup.mem_bot] at h3
    have h4 : (z.2 : X) = 1 := by
      rw [h3, one_mul] at h1
      exact h1
    exact Prod.ext (Subtype.ext h3) (Subtype.ext h4)
  have hμsurj : Function.Surjective μ := by
    intro y
    have hy : (y : X) ∈ ((J ⊔ R : Subgroup X) : Set X) := by
      rw [hY]
      exact y.2
    rw [Subgroup.mul_normal J R] at hy
    obtain ⟨j, hj, r, hr, hjr⟩ := hy
    exact ⟨(⟨j, hj⟩, ⟨r, hr⟩), Subtype.ext hjr⟩
  exact ⟨MulEquiv.ofBijective μ ⟨hμinj, hμsurj⟩, fun z => rfl⟩

omit [Finite G] [IsSimpleGroup G] in
theorem sigma_card_eq_one_of_nine [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) (hp : p.Prime) (h9 : p ^ f = 9)
    (F : Type) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
    (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
    (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
    (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma ≃* centralizerOddCoreQuotient n S e)
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) :
    Nat.card Sigma = 1 := by
  obtain ⟨-, hf2⟩ := CFSG.SectionRank.OddCover.eq_three_of_pow_eq_nine hp h9
  have hdvd := hdata.sigma_dvd
  rw [hf2] at hdvd
  have hodd := hdata.sigma_odd
  have hle : Nat.card Sigma ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card Sigma := Nat.card_pos
  obtain ⟨k, hk⟩ := hodd
  omega

end CFSG.Wreathed.PrimewiseLayerFieldElimination
