module

public import CFSG.CharacterTheory.Wreathed.CommutingNormalOddInverted
public import CFSG.CharacterTheory.Wreathed.PrimewiseLayerFieldElimination
public import CFSG.CharacterTheory.Wreathed.OriginalStationarityCoverageCriterion
public import CFSG.CharacterTheory.Wreathed.ComponentCoverFactorizations
public import CFSG.CharacterTheory.Wreathed.ConfinedOddCoreOrderSupport
public import CFSG.CharacterTheory.Wreathed.StationaryScalarCoverage

public section

open scoped Classical Pointwise

namespace CFSG.Wreathed.ComponentCoverConfinement

open CFSG.Assembly.LowTwoRank SmallerRecognitionOriginalField
open OriginalStationarityCoverageCriterion ComponentCoverFactorizations
open CFSG.Semidihedral.Principal.PrimewiseScalar
open CFSG.Wreathed.OriginalSylowNormalizerWitness CFSG.SignalizerFunctor.Helpers

section Elements

variable {G : Type} [Group G]

theorem eq_one_of_eq_inv_of_odd {v : G} (hv : Odd (orderOf v)) (h : v = v⁻¹) : v = 1 := by
  have hsq : v ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [h]
    exact mul_inv_cancel v
  have h1 : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at hv
    exact absurd hv (by decide)

theorem commute_of_inverted_mem_normalizer {x u w : G} (hw : Odd (orderOf w))
    (hxw : x * w * x⁻¹ = w⁻¹) (hwu : w ∈ Subgroup.normalizer (Subgroup.zpowers u : Set G))
    (hxu : x * u = u * x) : w * u = u * w := by
  obtain ⟨k, hk⟩ := hw
  set w' := w ^ (k + 1) with hw'
  have hsq : w' * w' = w := by
    rw [hw', ← pow_add, show k + 1 + (k + 1) = orderOf w + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hxw' : x * w' * x⁻¹ = w'⁻¹ := by
    rw [hw', ← MulAut.conj_apply, map_pow, MulAut.conj_apply, hxw, inv_pow]
  have hw'N : w' ∈ Subgroup.normalizer (Subgroup.zpowers u : Set G) :=
    Subgroup.pow_mem _ hwu _
  have hc : w' * u * w'⁻¹ ∈ Subgroup.zpowers u :=
    (Subgroup.mem_normalizer_iff.mp hw'N u).mp (Subgroup.mem_zpowers u)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hc
  have hxc : x * (w' * u * w'⁻¹) * x⁻¹ = w' * u * w'⁻¹ := by
    rw [← hi, mul_inv_eq_iff_eq_mul]
    exact ((Commute.zpow_right (show Commute x u from hxu) i)).eq
  have hxc' : x * (w' * u * w'⁻¹) * x⁻¹ = w'⁻¹ * u * w' := by
    have hux : x * u * x⁻¹ = u := by rw [hxu, mul_inv_cancel_right]
    calc x * (w' * u * w'⁻¹) * x⁻¹ = (x * w' * x⁻¹) * (x * u * x⁻¹) * (x * w' * x⁻¹)⁻¹ := by
          group
      _ = w'⁻¹ * u * w' := by rw [hxw', hux, inv_inv]
  have heq : w'⁻¹ * u * w' = w' * u * w'⁻¹ := hxc'.symm.trans hxc
  rw [← hsq]
  calc w' * w' * u = w' * (w' * u * w'⁻¹) * w' := by group
    _ = w' * (w'⁻¹ * u * w') * w' := by rw [heq]
    _ = u * (w' * w') := by group

theorem normalizer_zpowers_le_pow (u : G) (k : ℕ) :
    Subgroup.normalizer (Subgroup.zpowers u : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers (u ^ k) : Set G) := by
  have hsub : ∀ g ∈ Subgroup.normalizer (Subgroup.zpowers u : Set G),
      ∀ h ∈ Subgroup.zpowers (u ^ k), g * h * g⁻¹ ∈ Subgroup.zpowers (u ^ k) := by
    intro g hg h hh
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp
      ((Subgroup.mem_normalizer_iff.mp hg u).mp (Subgroup.mem_zpowers u))
    have : g * (u ^ k) ^ j * g⁻¹ = ((u ^ k) ^ j) ^ i := by
      rw [← MulAut.conj_apply, map_zpow, map_pow, MulAut.conj_apply, ← hi, ← zpow_natCast,
        ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul]
      ring_nf
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.zpow_mem_zpowers _ _) _
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hsub g hg h, fun hgh => ?_⟩
  have := hsub g⁻¹ (Subgroup.inv_mem _ hg) _ hgh
  simpa [mul_assoc] using this

theorem mem_normalizer_zpowers_of_conj {g u : G} (h : g * u * g⁻¹ = u ∨ g * u * g⁻¹ = u⁻¹) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rw [MonoidHom.map_zpowers]
  change Subgroup.zpowers (g * u * g⁻¹) = _
  rcases h with h | h
  · rw [h]
  · rw [h, Subgroup.zpowers_inv]

theorem confined_of_prime_order [Finite G] (K B : Subgroup G)
    (h : ∀ v ∈ B, (orderOf v).Prime → Subgroup.normalizer (Subgroup.zpowers v : Set G) ≤ K)
    {u : G} (hu : u ∈ B) (hu1 : u ≠ 1) :
    Subgroup.normalizer (Subgroup.zpowers u : Set G) ≤ K ∧
      Subgroup.centralizer ({u} : Set G) ≤ K := by
  have hord : orderOf u ≠ 1 := fun h1 => hu1 (orderOf_eq_one_iff.mp h1)
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hord
  have hv : orderOf (u ^ (orderOf u / r)) = r :=
    orderOf_pow_orderOf_div (orderOf_pos u).ne' hrdvd
  have hle := (normalizer_zpowers_le_pow u (orderOf u / r)).trans
    (h _ (B.pow_mem hu _) (by rw [hv]; exact hr))
  exact ⟨hle, (ConfinedOddCore.centralizer_singleton_le_normalizer_zpowers u).trans hle⟩

theorem exists_inverted_centralizing_witness [Finite G] (T : Subgroup G) [IsKleinFour T]
    {x y : G} (hxT : x ∈ T) (hyT : y ∈ T) (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y)
    {r : ℕ} (hr : r.Prime) (X : Subgroup G) (hXodd : Odd (Nat.card X))
    (hTX : T ≤ Subgroup.normalizer (X : Set G))
    {u w : G} (huX : u ∈ X) (hu : orderOf u = r) (hxu : x * u = u * x)
    (hTu : T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G))
    (hwX : w ∈ X) (hw : orderOf w = r) (hxw : x * w * x⁻¹ = w⁻¹)
    (hTw : T ≤ Subgroup.normalizer (Subgroup.zpowers w : Set G)) :
    ∃ v : G, v ≠ 1 ∧ IsPGroup r (Subgroup.zpowers v) ∧ x * v * x⁻¹ = v⁻¹ ∧ v * u = u * v := by
  have : Fact r.Prime := ⟨hr⟩
  have hT2 : IsPGroup 2 T :=
    IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; norm_num)
  have hrodd : Odd r := by
    rw [← hu]
    exact hXodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard X huX)
  have hup : IsPGroup r (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  have hwp : IsPGroup r (Subgroup.zpowers w) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hw, pow_one])
  obtain ⟨Q, huQ, hTQ⟩ := StationaryScalarCoverage.exists_invariant_sylow_containing hr T X
    (Subgroup.zpowers u) hT2 hXodd hTX (Subgroup.zpowers_le.mpr huX) hup hTu
  set QG := (Q : Subgroup X).map X.subtype with hQG
  have hQGp : IsPGroup r QG := Q.isPGroup'.map X.subtype
  obtain ⟨c, hc, hwle⟩ :=
    CFSG.Semidihedral.StationaryOddLocalization.invariant_pgroup_le_fixed_conjugate_sylow
      hr T X (Subgroup.zpowers w) hT2 hTX hXodd Q hTQ (Subgroup.zpowers_le.mpr hwX) hwp hTw
  obtain ⟨q, hq, hqw⟩ := hwle (Subgroup.mem_zpowers w)
  change c * q * c⁻¹ = w at hqw
  have hcx : c * x = x * c := (Subgroup.mem_centralizer_iff.mp hc.2 x hxT).symm
  have hxq : x * q * x⁻¹ = q⁻¹ := by
    have hq' : q = c⁻¹ * w * c := by rw [← hqw]; group
    rw [hq']
    calc x * (c⁻¹ * w * c) * x⁻¹ = c⁻¹ * (x * w * x⁻¹) * c := by
          rw [show x * (c⁻¹ * w * c) * x⁻¹ = (x * c⁻¹) * w * (c * x⁻¹) by group]
          have h1 : x * c⁻¹ = c⁻¹ * x := by
            rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hcx, ← mul_assoc, inv_mul_cancel, one_mul]
          have h2 : c * x⁻¹ = x⁻¹ * c := by
            rw [mul_inv_eq_iff_eq_mul, mul_assoc, hcx, ← mul_assoc, inv_mul_cancel, one_mul]
          rw [h1, h2]
          group
      _ = (c⁻¹ * w * c)⁻¹ := by rw [hxw]; group
  have hq1 : q ≠ 1 := by
    intro h1
    rw [h1, mul_one, mul_inv_cancel] at hqw
    rw [← hqw, orderOf_one] at hw
    exact hr.one_lt.ne' hw.symm
  let _action := conjugationAction T QG hTQ
  let a : T := ⟨x, hxT⟩
  let b : T := ⟨y, hyT⟩
  have ha : a ≠ 1 := fun h => hx (congrArg (fun z : T => (z : G)) h)
  have hb : b ≠ 1 := fun h => hy (congrArg (fun z : T => (z : G)) h)
  have hab : a ≠ b := fun h => hxy (congrArg (fun z : T => (z : G)) h)
  have hF : actionCentralizer (X := QG) a ≠ ⊤ := by
    intro htop
    have hmem : (⟨q, hq⟩ : QG) ∈ actionCentralizer (X := QG) a := by
      rw [htop]
      exact Subgroup.mem_top _
    have hfix := congrArg (fun z : QG => (z : G)) ((mem_actionCentralizer (a := a)).mp hmem)
    change x * q * x⁻¹ = q at hfix
    have hqodd : Odd (orderOf q) := hXodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard X
      (Subgroup.map_subtype_le _ hq))
    exact hq1 (eq_one_of_eq_inv_of_odd hqodd (hfix.symm.trans hxq))
  obtain ⟨-, -, v, hv1, hva, -, hvcomm, -⟩ :=
    four_group_odd_p_group_centralizing_inverted_witness hr hrodd hQGp a b ha hb hab hF
  have huQG : (⟨u, huQ (Subgroup.mem_zpowers u)⟩ : QG) ∈ actionCentralizer (X := QG) a := by
    apply (mem_actionCentralizer (a := a)).mpr
    apply Subtype.ext
    change x * u * x⁻¹ = u
    rw [hxu, mul_inv_cancel_right]
  have hvu := congrArg (fun z : QG => (z : G)) (hvcomm _ huQG).eq
  exact ⟨v, fun h => hv1 (Subtype.ext h), hQGp.to_le (Subgroup.zpowers_le.mpr v.property),
    congrArg (fun z : QG => (z : G)) hva, hvu⟩

end Elements

section Setting

variable {G : Type} [Group G] [Finite G]

theorem not_sym4_center (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    ¬ Nonempty ((centralizerOddCoreQuotient n S e ⧸
      Subgroup.center (centralizerOddCoreQuotient n S e)) ≃* Equiv.Perm (Fin 4)) :=
  fun ⟨α⟩ => hfour
    ⟨(OriginalScalarSylowCoverage.originalCenterQuotientEquiv n hn S e).symm.trans α⟩

theorem stationary_intrinsic (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hst : OriginalAllPrimeStationarity n S e) {ell : ℕ} (hell : ell.Prime)
    (hdiv : ell ∣ Nat.card (centralizerOddCore n S e)) :
    ∃ P₀ : Sylow ell (centralizerOddCore n S e),
      ∃ Q : Sylow ell (CFSG.pPrimeCore 2 (Subgroup.normalizer
        ((((P₀ : Subgroup (centralizerOddCore n S e)).map (centralizerOddCore n S e).subtype).map
          (involutionCentralizer n S e).subtype : Subgroup G) : Set G))),
        ((Q : Subgroup _).map (CFSG.pPrimeCore 2 (Subgroup.normalizer
          ((((P₀ : Subgroup (centralizerOddCore n S e)).map
            (centralizerOddCore n S e).subtype).map
              (involutionCentralizer n S e).subtype : Subgroup G) : Set G))).subtype).map
          (Subgroup.normalizer
            ((((P₀ : Subgroup (centralizerOddCore n S e)).map
              (centralizerOddCore n S e).subtype).map
                (involutionCentralizer n S e).subtype : Subgroup G) : Set G)).subtype =
          ((P₀ : Subgroup (centralizerOddCore n S e)).map (centralizerOddCore n S e).subtype).map
            (involutionCentralizer n S e).subtype := by
  obtain ⟨P₀, hP₀⟩ := hst ell hell hdiv
  exact ⟨P₀, CFSG.Semidihedral.StationaryOddLocalization.stationary_sylow_to_intrinsic_core hell _
    hP₀⟩

omit [Finite G] in
theorem factorization_set (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (U : Subgroup G)
    (h : NormalizerFactorization n S e U) :
    (((CFSG.pPrimeCore 2 (Subgroup.normalizer (U : Set G))).map
      (Subgroup.normalizer (U : Set G)).subtype : Subgroup G) : Set G) *
      ((Subgroup.normalizer (U : Set G) ⊓
        Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G) :
          Subgroup G) : Set G) = (Subgroup.normalizer (U : Set G) : Set G) := by
  rw [← CFSG.Semidihedral.StationaryOddLocalization.original_oddCore_eq_twoPrimeCore]
  exact h.2.2.2.1.symm

omit [Finite G] in
theorem factorization_sup (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (U : Subgroup G)
    (h : NormalizerFactorization n S e U) :
    CFSG.oddCore (Subgroup.normalizer (U : Set G)) ⊔
      (involutionCentralizer n S e).subgroupOf (Subgroup.normalizer (U : Set G)) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨k, hk⟩ -
  have hk' : k ∈ ((Subgroup.normalizer (U : Set G) : Subgroup G) : Set G) := hk
  rw [h.2.2.2.1] at hk'
  obtain ⟨o, ⟨o', ho', rfl⟩, c, hc, hoc⟩ := hk'
  have hck : c ∈ Subgroup.normalizer (U : Set G) := hc.1
  have heq : (⟨k, hk⟩ : Subgroup.normalizer (U : Set G)) = o' * ⟨c, hck⟩ :=
    Subtype.ext hoc.symm
  rw [heq]
  exact Subgroup.mul_mem_sup ho' hc.2

omit [Finite G] in
theorem centralizer_singleton_subtype (N : Subgroup G) (yN : N) :
    Subgroup.centralizer ({yN} : Set N) =
      (Subgroup.centralizer ({(yN : G)} : Set G)).subgroupOf N := by
  ext z
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

variable [IsSimpleGroup G]

theorem exists_cycler (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    ∃ g ∈ Subgroup.normalizer (Subgroup.closure ({wreathModelHom S e (Original.x (2 ^ n)),
        wreathModelHom S e (Original.x2 (2 ^ n))} : Set G) : Set G),
      g * wreathModelHom S e (Original.x (2 ^ n)) * g⁻¹ =
          wreathModelHom S e (Original.x2 (2 ^ n)) ∧
        g * wreathModelHom S e (Original.x2 (2 ^ n)) * g⁻¹ =
          wreathModelHom S e (Original.x (2 ^ n)) * wreathModelHom S e (Original.x2 (2 ^ n)) ∧
        g * (wreathModelHom S e (Original.x (2 ^ n)) *
          wreathModelHom S e (Original.x2 (2 ^ n))) * g⁻¹ =
          wreathModelHom S e (Original.x (2 ^ n)) := by
  obtain ⟨Y, hYB, hY1, hY2, hY3⟩ := BrauerWong.exists_base_three_cycle hn S e
    (simple_wreathed_one_involution_class_and_local_S3 hnonab n hn S e).1
  have hYT : Y ∈ Subgroup.normalizer (BaseFourCentralizerStructure.modelT n S e : Set G) :=
    BaseFourCentralizerStructure.modelBase_normalizer_le_modelT_normalizer n (by omega) S e hYB
  rw [CompatibleFamilies.modelT_eq_closure S e (by omega)] at hYT
  have hxy := BrauerWong.modelHom_x_mul_x2 S e (n := n) (by omega)
  refine ⟨Y⁻¹, Subgroup.inv_mem _ hYT, ?_, ?_, ?_⟩
  · rw [inv_inv]
    exact hY1
  · rw [inv_inv, hxy]
    exact hY2
  · rw [inv_inv, hxy]
    exact hY3

theorem canonical_lift
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hcov : OriginalAllPrimeCoverage n S e) :
    ∃ J : Subgroup (involutionCentralizer n S e), J.Normal ∧ Group.IsPerfect J ∧
      J.map (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e) ∧
      (∀ j ∈ J, ∀ r ∈ centralizerOddCore n S e, Commute j r) ∧
      ∃ k : ℕ, (J ⊔ centralizerOddCore n S e).index = 2 ^ k := by
  have hp2 : p ≠ 2 := fun h => by
    rw [h] at hpodd
    exact (Nat.not_even_iff_odd.mpr hpodd) even_two
  obtain ⟨hJperf, hJnormal, -, hJM, hJR, -, -, -, -, hex, hall⟩ :=
    PrimewiseLayerFieldElimination.original_primewise_layer_coverage_eliminates_odd_field_factor
      hnonab n hn S e hfour p f hp hp2 hf hlocal hcov
  set N := involutionCentralizer n S e
  set R := centralizerOddCore n S e
  obtain ⟨J, hJperf, hJnormal, hJM, hJR⟩ : ∃ J : Subgroup N, Group.IsPerfect J ∧ J.Normal ∧
      J.map (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e) ∧
      ⁅J, R⁆ = ⊥ := ⟨_, hJperf, hJnormal, hJM, hJR⟩
  let : J.Normal := hJnormal
  refine ⟨J, hJnormal, hJperf, hJM, fun j hj r hr => ?_, ?_⟩
  · have hjc := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJR) hj
    exact (Subgroup.mem_centralizer_iff.mp hjc r hr).symm
  · obtain ⟨F, hF, hFfin, Sigma, b, hSigma, ρ, Ψ, hdata⟩ := hex
    let : Field F := hF
    let : Finite F := hFfin
    have hd1 := hall F Sigma b hSigma ρ Ψ hdata
    have hprod := ConfinedOddCore.lift_sylow_product hnonab n hn S e hfour p f hp hp2 hf hlocal
      F Sigma b hSigma ρ Ψ hdata hd1 J hJM
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let SN : Subgroup N := (centralizerSylow n hn S e : Subgroup N)
    let φ : SN →* N ⧸ (J ⊔ R) := (QuotientGroup.mk' (J ⊔ R)).comp SN.subtype
    have hφ : Function.Surjective φ := by
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (J ⊔ R) q
      obtain ⟨j, hj, s, hs, r, hr, rfl⟩ := hprod g
      refine ⟨⟨s, hs⟩, ?_⟩
      change (QuotientGroup.mk' (J ⊔ R)) s = (QuotientGroup.mk' (J ⊔ R)) (j * s * r)
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have h1 : s⁻¹ * (j * s * r) = (s⁻¹ * j * s) * r := by group
      rw [h1]
      exact (J ⊔ R).mul_mem (Subgroup.mem_sup_left ((inferInstance : J.Normal).conj_mem' j hj s))
        (Subgroup.mem_sup_right hr)
    have hpg : IsPGroup 2 (N ⧸ (J ⊔ R)) :=
      (centralizerSylow n hn S e).isPGroup'.of_surjective φ hφ
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpg
    exact ⟨k, hk⟩

theorem normalizerFactorization_of_lift
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G) (J : Subgroup (involutionCentralizer n S e))
    (hJM : J.map (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e))
    (hcomm : ∀ j ∈ J, ∀ r ∈ centralizerOddCore n S e, Commute j r)
    (W : Subgroup G)
    (hWR : W ≤ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype)
    (hW : W ≠ ⊥) : NormalizerFactorization n S e W := by
  have h3 := (component_covering_criterion_produces_actual_odd_subgroup_normalizer_factorizations
    hnonab n hn S e hfour p f hp hpodd hf hq hlocal hrec).2.2
  refine h3 (J.map (involutionCentralizer n S e).subtype) (Subgroup.map_subtype_le _) ?_ ?_ W
    hWR hW
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      (involutionCentralizer n S e).subtype_injective]
    exact hJM
  · rw [← Subgroup.map_commutator]
    have hJR : ⁅J, centralizerOddCore n S e⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro j hj
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact (hcomm j hj r hr).symm
    rw [hJR, Subgroup.map_bot]

theorem scalar_sylows
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (hst : OriginalAllPrimeStationarity n S e)
    (hfac : ∀ U : Subgroup G, U ≠ ⊥ →
      U ≤ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype →
        NormalizerFactorization n S e U)
    (yN : involutionCentralizer n S e)
    (hyN : (yN : G) = wreathModelHom S e (Original.x2 (2 ^ n)))
    (ell : ℕ) (hell : ell.Prime) (hdiv : ell ∣ Nat.card (centralizerOddCore n S e)) :
    ∃ P : Subgroup (involutionCentralizer n S e), IsSylowOf (centralizerOddCore n S e) ell P ∧
      (∀ z ∈ P, yN * z * yN⁻¹ ∈ P) ∧
      ((∀ z ∈ P, yN * z * yN⁻¹ = z) ∨ (∀ z ∈ P, yN * z * yN⁻¹ = z⁻¹)) := by
  obtain ⟨P, hTP⟩ :=
    StationaryScalarCoverage.exists_invariant_sylow_centralizerOddCore n hn S e hell
  have hscalar := (StationaryScalarCoverage.scalar_abelian_coverage_of_stationary_factorizations
    hnonab n hn S e (not_sym4_center n hn S e hfour) hell hdiv
    (stationary_intrinsic n S e hst hell hdiv)
    (fun U hU _ hUR _ => factorization_set n S e U (hfac U hU hUR)) P hTP).1
  have hyT : wreathModelHom S e (Original.x2 (2 ^ n)) ∈
      BaseFourCentralizerStructure.modelT n S e := by
    rw [CompatibleFamilies.modelT_eq_closure S e (by omega)]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hmem : ∀ z ∈ (P : Subgroup (centralizerOddCore n S e)).map
      (centralizerOddCore n S e).subtype,
      (z : G) ∈ (((P : Subgroup (centralizerOddCore n S e)).map
        (centralizerOddCore n S e).subtype).map (involutionCentralizer n S e).subtype) :=
    fun z hz => Subgroup.mem_map_of_mem (involutionCentralizer n S e).subtype hz
  refine ⟨(P : Subgroup (centralizerOddCore n S e)).map (centralizerOddCore n S e).subtype,
    ⟨P, rfl⟩, fun z hz => ?_, ?_⟩
  · have h1 := (Subgroup.mem_normalizer_iff.mp (hTP hyT) (z : G)).mp (hmem z hz)
    obtain ⟨z', hz', hz'eq⟩ := h1
    have : z' = yN * z * yN⁻¹ := Subtype.ext (by
      change (z' : G) = (yN : G) * z * (yN : G)⁻¹
      rw [hyN]
      exact hz'eq)
    rw [← this]
    exact hz'
  · rcases hscalar with h | h
    · exact Or.inl fun z hz => Subtype.ext (by
        change (yN : G) * z * (yN : G)⁻¹ = z
        rw [hyN]
        exact h z (hmem z hz))
    · exact Or.inr fun z hz => Subtype.ext (by
        change (yN : G) * z * (yN : G)⁻¹ = (z : G)⁻¹
        rw [hyN]
        exact h z (hmem z hz))

theorem inverted_factor
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (hst : OriginalAllPrimeStationarity n S e)
    (hfac : ∀ U : Subgroup G, U ≠ ⊥ →
      U ≤ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype →
        NormalizerFactorization n S e U)
    (J : Subgroup (involutionCentralizer n S e)) [J.Normal]
    (hcomm : ∀ j ∈ J, ∀ r ∈ centralizerOddCore n S e, Commute j r)
    (hidx : ∃ k : ℕ, (J ⊔ centralizerOddCore n S e).index = 2 ^ k) :
    ∃ B : Subgroup (involutionCentralizer n S e),
      (B : Set (involutionCentralizer n S e)) = {r | r ∈ centralizerOddCore n S e ∧
        wreathModelHom S e (Original.x2 (2 ^ n)) * (r : G) *
          (wreathModelHom S e (Original.x2 (2 ^ n)))⁻¹ = (r : G)⁻¹} ∧
      B ≤ centralizerOddCore n S e ∧ IsMulCommutative B ∧
      (B.subgroupOf (centralizerOddCore n S e)).Characteristic ∧
      Nat.Coprime (Nat.card B) (B.relIndex (centralizerOddCore n S e)) ∧
      (B.subgroupOf (centralizerOddCore n S e)).Normal ∧
      B ⊔ (centralizerOddCore n S e ⊓ (Subgroup.centralizer
        ({wreathModelHom S e (Original.x2 (2 ^ n))} : Set G)).subgroupOf
          (involutionCentralizer n S e)) = centralizerOddCore n S e ∧
      B ⊓ (centralizerOddCore n S e ⊓ (Subgroup.centralizer
        ({wreathModelHom S e (Original.x2 (2 ^ n))} : Set G)).subgroupOf
          (involutionCentralizer n S e)) = ⊥ ∧
      B.Normal ∧
      ∀ E : Subgroup (involutionCentralizer n S e), Odd (Nat.card E) →
        (∀ z ∈ E, wreathModelHom S e (Original.x2 (2 ^ n)) * (z : G) *
          (wreathModelHom S e (Original.x2 (2 ^ n)))⁻¹ = (z : G)⁻¹) →
        E ≤ J ⊔ B ∧ B ≤ Subgroup.centralizer (E : Set (involutionCentralizer n S e)) := by
  let yN : involutionCentralizer n S e :=
    ⟨wreathModelHom S e (Original.x2 (2 ^ n)), ConfinedOddCore.y_mem_involutionCentralizer n hn S e⟩
  have hy2 : orderOf yN = 2 := by
    rw [Subgroup.orderOf_mk]
    exact CompatibleFamilies.orderOf_x2 S e hn
  have hJR : ⁅J, centralizerOddCore n S e⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (hcomm j hj r hr).symm
  have hRodd : Odd (Nat.card (centralizerOddCore n S e)) := weakClosure_oddCore_card _
  obtain ⟨B, hBset, hBR, hBab, hBchar, hBhall, hBn, hBsup, hBinf, hBN, hBE⟩ :=
    commuting_normal_factors_control_odd_inverted_subgroups J (centralizerOddCore n S e) hJR
      (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hRodd) hRodd hidx yN hy2
      (scalar_sylows hnonab n hn S e hfour hst hfac yN rfl)
  have hC : Subgroup.centralizer ({yN} : Set (involutionCentralizer n S e)) =
      (Subgroup.centralizer ({wreathModelHom S e (Original.x2 (2 ^ n))} : Set G)).subgroupOf
        (involutionCentralizer n S e) :=
    centralizer_singleton_subtype (involutionCentralizer n S e) yN
  refine ⟨B, ?_, hBR, hBab, hBchar, hBhall, hBn, hC ▸ hBsup, hC ▸ hBinf, hBN,
    fun E hE hEinv => ?_⟩
  · rw [hBset]
    ext r
    simp only [CFSG.OddInversion.invertedSet, Set.mem_ofPred_eq]
    exact and_congr_right fun _ => ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  · exact hBE E hE fun z hz => Subtype.ext (hEinv z hz)

end Setting

end CFSG.Wreathed.ComponentCoverConfinement
