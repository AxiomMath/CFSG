module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6ConcModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6ConcOuterNat
import CFSG.LieType.SemisimpleCentralizers.HeldLangCoverLift
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6ConcOuter
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SchurFactsCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup)
open CFSG.LieType.Steinberg.Isogeny (e6IsogenyFixed range_e6IsogenyFixed)

section Quot

variable {Ω : Type} [Group Ω] {S : Subgroup Ω}

private theorem ker_chevQuotHom_le_center_twE6 (hcore : GLAPPrimeCore 3 ↥S = ⊥) :
    (chevQuotHom 3 S).ker ≤ Subgroup.center ↥S := by
  intro x hx
  refine Subgroup.mem_center_iff.2 fun s => ?_
  have hx' : pQuotHom 3 S x ∈ Subgroup.center (PQuot 3 S) := by
    rw [MonoidHom.mem_ker] at hx
    exact (QuotientGroup.eq_one_iff _).1 hx
  have hinj : Function.Injective (pQuotHom 3 S) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_pQuotHom, hcore]
  apply hinj
  rw [map_mul, map_mul]
  exact Subgroup.mem_center_iff.1 hx' (pQuotHom 3 S s)

private theorem center_le_ker_chevQuotHom_twE6 :
    Subgroup.center ↥S ≤ (chevQuotHom 3 S).ker := by
  intro z hz
  have hz' : pQuotHom 3 S z ∈ Subgroup.center (PQuot 3 S) :=
    Subgroup.mem_center_iff.2 fun y => by
      obtain ⟨s, rfl⟩ := pQuotHom_surjective 3 S y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz s]
  rw [MonoidHom.mem_ker]
  exact (QuotientGroup.eq_one_iff _).2 hz'

private theorem zmod_three_eq_one_of_pow (a : ZMod 3) (h : a ^ 3 = 1) : a = 1 := by
  revert a
  decide

end Quot


theorem exists_twistedE6Sc_mulEquiv {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (h3 : 3 ∣ ℓ ^ f + 1) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore 3 ↥S = ⊥)
    (hZ : Subgroup.center ↥S ≠ ⊥) (e : PSimple 3 S ≃* ↥(twistedE6RootGroup K σ)) :
    ∃ φ : ↥(fixedGroup K σ.toRingHom) ≃* ↥S, ∀ g : ↥(fixedGroup K σ.toRingHom),
      ((e (chevQuotHom 3 S (φ g)) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
        e6IsogenyFixed σ.toRingHom g := by
  classical
  have hσ' : ∀ c, σ.toRingHom c = c ^ (ℓ ^ f) := hσ
  have hθθ : ∀ c, σ.toRingHom (σ.toRingHom c) = c :=
    CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.theta_theta_of_card hK hσ'
  have hQ5 : 5 ≤ ℓ ^ f := by
    obtain ⟨m, hm⟩ := (hℓ.odd_of_ne_two hℓ2).pow (n := f)
    have hℓ3 : 3 ≤ ℓ := by
      have := hℓ.two_le
      omega
    have hQ3 : 3 ≤ ℓ ^ f := hℓ3.trans (Nat.le_self_pow (by omega) ℓ)
    omega
  have hk4 : 4 ≤ Nat.card K := by
    rw [hK]
    nlinarith
  haveI : Finite ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup K) := by
    have : Finite (Module.End K (Fin CFSG.LieType.Steinberg.Minuscule.e6Data.d →₀ K)) :=
      Module.finite_of_finite K
    infer_instance
  haveI : Finite ↥S := Subtype.finite
  have hrange : (e6IsogenyFixed σ.toRingHom).range = twistedE6RootGroup K σ := by
    rw [range_e6IsogenyFixed σ.toRingHom hθθ hk4]
    exact (finite_fixed_root_group_perfect TwistTag.E6 hℓ hf K hK σ.toRingHom hσ').2.2.1
  let πU : ↥(fixedGroup K σ.toRingHom) →* ↥(twistedE6RootGroup K σ) :=
    (e6IsogenyFixed σ.toRingHom).codRestrict _ fun g => by
      rw [← hrange]
      exact ⟨g, rfl⟩
  have hU : Function.Surjective πU := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨g, rfl⟩ := hy
    exact ⟨g, rfl⟩
  have hkerU : Nat.card πU.ker = 3 := by
    have h1 : πU.ker = (CFSG.LieType.Simplicity.twistedIsogeny σ.toRingHom hθθ hk4).ker := by
      rw [MonoidHom.ker_codRestrict]
      exact (MonoidHom.ker_codRestrict _ _ _).symm
    rw [h1, CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.ker_twistedIsogeny_eq_center hθθ hk4,
      (CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_center_fixedGroup hK hσ').1]
    exact Nat.gcd_eq_left h3
  let πL : ↥S →* ↥(twistedE6RootGroup K σ) := e.toMonoidHom.comp (chevQuotHom 3 S)
  have hL : Function.Surjective πL := e.surjective.comp (chevQuotHom_surjective 3 S)
  have hkerL : πL.ker = (chevQuotHom 3 S).ker := by
    ext x
    simp only [πL, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ e.injective]
  have hcL : πL.ker ≤ Subgroup.center ↥S := by
    rw [hkerL]
    exact ker_chevQuotHom_le_center_twE6 hcore
  haveI hperf' : Group.IsPerfect ↥S := Subgroup.isPerfect_iff.2 hperf
  obtain ⟨φ, hφ, hφs⟩ := CFSG.LieType.SemisimpleCentralizers.HeldLang.exists_surjective_lift πU πL
    hU hL hcL hperf' fun E _ _ π' hπ' hc =>
      CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.twistedE6_exists_section_of_central
        σ.toRingHom hQ5 hK hσ' hπ' hc
  have hcardU : Nat.card ↥(fixedGroup K σ.toRingHom) =
      Nat.card ↥(twistedE6RootGroup K σ) * Nat.card πU.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup πU.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective πU hU).toEquiv]
  have hcardL : Nat.card ↥S = Nat.card ↥(twistedE6RootGroup K σ) * Nat.card πL.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup πL.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective πL hL).toEquiv]
  have hkerL3 : 3 ≤ Nat.card πL.ker := by
    have hp3 : IsPGroup 3 (Subgroup.center ↥S) :=
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.SchurFacts.isPGroup_center_of_glaPPrimeCore_eq_bot
        Nat.prime_three hcore
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hp3
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hZ (Subgroup.eq_bot_of_card_eq _ hk)
    have hle : Subgroup.center ↥S ≤ πL.ker := by
      rw [hkerL]
      exact center_le_ker_chevQuotHom_twE6
    calc 3 = 3 ^ 1 := (pow_one 3).symm
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hk0)
      _ = Nat.card (Subgroup.center ↥S) := hk.symm
      _ ≤ Nat.card πL.ker := Subgroup.card_le_of_le hle
  have hle : Nat.card ↥(fixedGroup K σ.toRingHom) ≤ Nat.card ↥S := by
    rw [hcardU, hcardL, hkerU]
    exact Nat.mul_le_mul_left _ hkerL3
  refine ⟨MulEquiv.ofBijective φ (hφs.bijective_of_nat_card_le hle), fun g => ?_⟩
  exact congrArg Subtype.val (hφ g)

theorem card_center_eq_three {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (h3 : 3 ∣ ℓ ^ f + 1) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore 3 ↥S = ⊥)
    (hZ : Subgroup.center ↥S ≠ ⊥) (e : PSimple 3 S ≃* ↥(twistedE6RootGroup K σ)) :
    Nat.card (Subgroup.center ↥S) = 3 := by
  obtain ⟨φ, -⟩ := exists_twistedE6Sc_mulEquiv hℓ hℓ2 hf h3 hK σ hσ hperf hcore hZ e
  have hσ' : ∀ c, σ.toRingHom c = c ^ (ℓ ^ f) := hσ
  rw [← Nat.card_congr (Subgroup.centerCongr φ).toEquiv,
    (CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_center_fixedGroup hK hσ').1]
  exact Nat.gcd_eq_left h3

section LiftA

open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.LieType.Universal.Unitary (SU SUid antidiag conjTr conjEquiv)
open CFSG.ClassicalInvolution.Phan (Su)
open TwE6Conc (twE6Phi twE6Phi_apply twE6R0 leviSU leviSU_mem_leviJ rootSL2_commute_of_mem_leviJ
  fixQ rootSL2_highRoot_mem map_compSL2_fixQ compSL2 orderOf_compSL2 sub_inv_ne_zero_of_orderOf
  splitHom powHom powHom_apply pow_eq_one_of_fin orderOf_twE6R0)
open TwE6Outer (suidMap entrywise_leviSU)

private theorem five_le_pow_of_three_dvd {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (h3 : 3 ∣ ℓ ^ f + 1) : 5 ≤ ℓ ^ f ∧ ℓ ^ f ≠ 9 := by
  obtain ⟨m, hm⟩ := (hℓ.odd_of_ne_two hℓ2).pow (n := f)
  have hℓ3 : 3 ≤ ℓ := by
    have := hℓ.two_le
    omega
  have hQ3 : 3 ≤ ℓ ^ f := hℓ3.trans (Nat.le_self_pow (by omega) ℓ)
  omega

private theorem exists_lift_through_central {G E X : Type} [Group G] [Group E] [Group X]
    [Finite G] [Finite E] {π : E →* X} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E)
    (hsec : ∀ (F : Type) [Group F] [Finite F] (π' : F →* G), Function.Surjective π' →
      π'.ker ≤ Subgroup.center F → ∃ s : G →* F, ∀ g, π' (s g) = g)
    (ρ : G →* X) : ∃ τ : G →* E, ∀ g, π (τ g) = ρ g := by
  let P : Subgroup (E × G) :=
    MonoidHom.eqLocus (π.comp (MonoidHom.fst E G)) (ρ.comp (MonoidHom.snd E G))
  let q : ↥P →* G := (MonoidHom.snd E G).comp P.subtype
  have hq : Function.Surjective q := by
    intro g
    obtain ⟨x, hx⟩ := hπ (ρ g)
    exact ⟨⟨(x, g), hx⟩, rfl⟩
  have hqc : q.ker ≤ Subgroup.center ↥P := by
    intro y hy
    have h1 : (y : E × G).2 = 1 := hy
    have h2 : π (y : E × G).1 = 1 := by
      have h3 : π (y : E × G).1 = ρ (y : E × G).2 := y.2
      rw [h3, h1, map_one]
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    apply Prod.ext
    · exact Subgroup.mem_center_iff.mp (hcen h2) (w : E × G).1
    · show (w : E × G).2 * (y : E × G).2 = (y : E × G).2 * (w : E × G).2
      rw [h1, mul_one, one_mul]
  haveI : Finite ↥P := Subtype.finite
  obtain ⟨s, hs⟩ := hsec ↥P q hq hqc
  refine ⟨(MonoidHom.fst E G).comp (P.subtype.comp s), fun g => ?_⟩
  have h1 : π (s g : E × G).1 = ρ (s g : E × G).2 := (s g).2
  have h2 : (s g : E × G).2 = g := hs g
  rw [h2] at h1
  exact h1

private theorem commute_of_mem_center_of_card_three {Ω : Type} [Group Ω] {S : Subgroup Ω}
    (hS : S.Normal) (h3 : Nat.card (Subgroup.center ↥S) = 3) {b : Ω} (hb3 : b ^ 3 = 1) {z : ↥S}
    (hz : z ∈ Subgroup.center ↥S) : b * (z : Ω) = (z : Ω) * b := by
  classical
  haveI := hS
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set β : MulAut ↥S := MulAut.conjNormal b with hβ
  have hβapp : ∀ w : ↥S, ((β w : ↥S) : Ω) = b * w * b⁻¹ := fun w => MulAut.conjNormal_apply b w
  have hβc : ∀ w ∈ Subgroup.center ↥S, β w ∈ Subgroup.center ↥S := fun w hw => by
    rw [← Subgroup.map_center_eq β]
    exact Subgroup.mem_map_of_mem _ hw
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hb3, map_one]
  have hfix : β z = z := by
    by_cases hz1 : z = 1
    · rw [hz1, map_one]
    have hzZ : (⟨z, hz⟩ : Subgroup.center ↥S) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
    have htop := zpowers_eq_top_of_prime_card h3 hzZ
    have hmem : (⟨β z, hβc z hz⟩ : Subgroup.center ↥S) ∈
        Subgroup.zpowers (⟨z, hz⟩ : Subgroup.center ↥S) := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hk' : z ^ k = β z := by
      have := congrArg Subtype.val hk
      rwa [Subgroup.coe_zpow] at this
    have hpow : ∀ n : ℕ, (β ^ n) z = z ^ (k ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', MulAut.mul_apply, ih, map_zpow, ← hk', ← zpow_mul, pow_succ']
    have hz3 : z ^ 3 = 1 := by
      have h1 := pow_card_eq_one' (G := Subgroup.center ↥S) (x := ⟨z, hz⟩)
      rw [h3] at h1
      exact congrArg Subtype.val h1
    have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
    have h1 : z ^ (k ^ 3) = z ^ (1 : ℤ) := by
      rw [← hpow 3, hβ3, MulAut.one_apply, zpow_one]
    rw [zpow_eq_zpow_iff_modEq, hord] at h1
    have h2 : ((k : ZMod 3)) ^ 3 = 1 := by
      have := (ZMod.intCast_eq_intCast_iff (k ^ 3) 1 3).2 h1
      push_cast at this
      exact this
    have h5 : k ≡ 1 [ZMOD 3] := (ZMod.intCast_eq_intCast_iff k 1 3).1 (by
      push_cast
      exact zmod_three_eq_one_of_pow _ h2)
    rw [← hk']
    have h6 : z ^ k = z ^ (1 : ℤ) := by
      rw [zpow_eq_zpow_iff_modEq, hord]
      exact_mod_cast h5
    rwa [zpow_one] at h6
  have h1 := hβapp z
  rw [hfix] at h1
  calc b * (z : Ω) = b * (z : Ω) * b⁻¹ * b := by group
    _ = (z : Ω) * b := by rw [← h1]

private theorem pow_three_of_mem_center_twE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (h3 : 3 ∣ ℓ ^ f + 1) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore 3 ↥S = ⊥)
    (e : PSimple 3 S ≃* ↥(twistedE6RootGroup K σ)) {z : ↥S} (hz : z ∈ Subgroup.center ↥S) :
    z ^ 3 = 1 := by
  by_cases hZ : Subgroup.center ↥S = ⊥
  · rw [hZ, Subgroup.mem_bot] at hz
    rw [hz, one_pow]
  · haveI : Finite ↥S := Subtype.finite
    have h3Z := card_center_eq_three hℓ hℓ2 hf h3 hK σ hσ hperf hcore hZ e
    have h1 := pow_card_eq_one' (G := Subgroup.center ↥S) (x := ⟨z, hz⟩)
    rw [h3Z] at h1
    exact congrArg Subtype.val h1

private noncomputable def rootSL2Q (K : Type) [Field K] [Finite K] (ℓ f : ℕ) [Fact ℓ.Prime]
    [CharP K ℓ] :
    Matrix.SpecialLinearGroup (Fin 2) (fixQ K ℓ f) →*
      ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) :=
  ((rootSL2 TwistTag.E6.tag K e6HighestRoot).comp
    (Matrix.SpecialLinearGroup.map (fixQ K ℓ f).subtype)).codRestrict _
    fun g => rootSL2_highRoot_mem g

private theorem coe_rootSL2Q {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (g : Matrix.SpecialLinearGroup (Fin 2) (fixQ K ℓ f)) :
    ((rootSL2Q K ℓ f g : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))) :
      ModGL TwistTag.E6.tag K) =
      rootSL2 TwistTag.E6.tag K e6HighestRoot
        (Matrix.SpecialLinearGroup.map (fixQ K ℓ f).subtype g) := rfl

private theorem exists_lifts_twE6 {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f) (hℓ2 : ℓ ≠ 2) (h3 : 3 ∣ ℓ ^ f + 1)
    {ζ : K} (hζ : ζ ≠ 0) (hσζ : unitaryInvolution K ℓ f ζ = -ζ) (P : GL (Fin 6) K)
    (hP : conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin 6) (Fin 6) K) *
      (P : Matrix (Fin 6) (Fin 6) K) = antidiag 6)
    {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} (hcore : GLAPPrimeCore 3 ↥S = ⊥)
    (e : PSimple 3 S ≃* ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))) :
    ∃ (ρt : Matrix.SpecialLinearGroup (Fin 2) (fixQ K ℓ f) →* ↥S) (ιt : Su K ℓ f 6 →* ↥S),
      (∀ g, e (chevQuotHom 3 S (ρt g)) = rootSL2Q K ℓ f g) ∧
      (∀ y, e (chevQuotHom 3 S (ιt y)) = leviSU hK hf hζ hσζ P hP y) ∧
      ∀ g y, ρt g * ιt y = ιt y * ρt g := by
  classical
  obtain ⟨hQ5, hQ9⟩ := five_le_pow_of_three_dvd (Fact.out : ℓ.Prime) hℓ2 hf h3
  haveI : Finite ↥S := Subtype.finite
  haveI : Finite (fixQ K ℓ f) := Subtype.finite
  haveI : Finite (Matrix.SpecialLinearGroup (Fin 2) (fixQ K ℓ f)) := Subtype.finite
  haveI : Finite (SU (unitaryInvolution K ℓ f) 6) := Subtype.finite
  let π : ↥S →* ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) :=
    e.toMonoidHom.comp (chevQuotHom 3 S)
  have hπ : Function.Surjective π := e.surjective.comp (chevQuotHom_surjective 3 S)
  have hπc : π.ker ≤ Subgroup.center ↥S := by
    intro x hx
    apply ker_chevQuotHom_le_center_twE6 hcore
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (map_eq_one_iff _ e.injective).1 hx
  obtain ⟨ιA, hιA⟩ := exists_lift_through_central hπ hπc
    (fun F _ _ π' hπ' hc =>
      CFSG.LieType.Steinberg.CentralExt.SUClosed.su_exists_section_of_central hK (by decide)
        (by norm_num) (by omega) hπ' hc)
    ((leviSU hK hf hζ hσζ P hP).comp (conjEquiv P hP).toMonoidHom)
  let ιt : Su K ℓ f 6 →* ↥S := ιA.comp (conjEquiv P hP).symm.toMonoidHom
  have hιt : ∀ y, π (ιt y) = leviSU hK hf hζ hσζ P hP y := fun y => by
    have h1 := hιA ((conjEquiv P hP).symm y)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at h1
    exact h1
  have hcardQ : Nat.card (fixQ K ℓ f) = ℓ ^ f := CFSG.LieType.Steinberg.card_fixedSubfield hK
  obtain ⟨ρt, hρt⟩ := exists_lift_through_central hπ hπc
    (fun F _ _ π' hπ' hc =>
      CFSG.LieType.Steinberg.CentralExt.SL2Closed.sl2_exists_section_of_central
        (by rw [hcardQ]; exact hQ5) (by rw [hcardQ]; exact hQ9) hπ' hc)
    (rootSL2Q K ℓ f)
  haveI : Group.IsPerfect (Su K ℓ f 6) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_SUid
      (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK) (by norm_num)
      fun h => absurd h (by norm_num)
  refine ⟨ρt, ιt, hρt, hιt, fun g y => ?_⟩
  have key := CFSG.LieType.SemisimpleCentralizers.HeldLang.eq_of_central_displacement_hom ιt
    ((MulAut.conj (ρt g)).toMonoidHom.comp ιt) fun x => hπc (by
      have hc : rootSL2Q K ℓ f g * leviSU hK hf hζ hσζ P hP x =
          leviSU hK hf hζ hσζ P hP x * rootSL2Q K ℓ f g := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_rootSL2Q]
        exact rootSL2_commute_of_mem_leviJ _ (leviSU_mem_leviJ hK hf hζ hσζ P hP x)
      have hx : ((MulAut.conj (ρt g)).toMonoidHom.comp ιt) x = ρt g * ιt x * (ρt g)⁻¹ := rfl
      have h1 : π (ρt g) = rootSL2Q K ℓ f g := hρt g
      have h2 : π (ιt x) = leviSU hK hf hζ hσζ P hP x := hιt x
      rw [MonoidHom.mem_ker, hx, map_mul, map_inv, map_mul, map_mul, map_inv, h1, h2, hc]
      group)
  have h1 := DFunLike.congr_fun key y
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  calc ρt g * ιt y = ρt g * ιt y * (ρt g)⁻¹ * ρt g := by group
    _ = ιt y * ρt g := by rw [← h1]

private theorem comap_twE6Phi_decomp {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f) {ζ : K} (hζ : ζ ≠ 0)
    (hσζ : unitaryInvolution K ℓ f ζ = -ζ) (P : GL (Fin 6) K)
    (hP : conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin 6) (Fin 6) K) *
      (P : Matrix (Fin 6) (Fin 6) K) = antidiag 6) [Fact (Nat.Prime 3)] {c : Kˣ}
    (hc : orderOf c = 3)
    (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K))
    {m : ℕ} (φ : (Fin m → Multiplicative (ZMod 3)) →* Su K ℓ f 6) {Ω : Type} [Group Ω]
    [Finite Ω] {S : Subgroup Ω} (hcore : GLAPPrimeCore 3 ↥S = ⊥)
    (e : PSimple 3 S ≃* ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)))
    (ρt : Matrix.SpecialLinearGroup (Fin 2) (fixQ K ℓ f) →* ↥S) (ιt : Su K ℓ f 6 →* ↥S)
    (hρt : ∀ g, e (chevQuotHom 3 S (ρt g)) = rootSL2Q K ℓ f g)
    (hιt : ∀ y, e (chevQuotHom 3 S (ιt y)) = leviSU hK hf hζ hσζ P hP y)
    (hcomm : ∀ g y, ρt g * ιt y = ιt y * ρt g) :
    ∃ Λ : (Fin (m + 1) → Multiplicative (ZMod 3)) →* ↥S,
      (∀ x, Λ x = ρt (compSL2 (⟨(c : K) + ((c⁻¹ : Kˣ) : K), hct⟩ : fixQ K ℓ f)) ^
        (Multiplicative.toAdd (x 0)).val * ιt (φ fun i => x i.succ)) ∧
      ∀ s ∈ (twE6Phi hK hf hζ hσζ P hP (by norm_num) hc hct φ).range.comap
        (e.toMonoidHom.comp (chevQuotHom 3 S)), ∃ x, ∃ z ∈ Subgroup.center ↥S, s = Λ x * z := by
  classical
  set R : Matrix.SpecialLinearGroup (Fin 2) (fixQ K ℓ f) :=
    compSL2 (⟨(c : K) + ((c⁻¹ : Kˣ) : K), hct⟩ : fixQ K ℓ f) with hRdef
  have hR : rootSL2Q K ℓ f R = twE6R0 c hct := by
    apply Subtype.ext
    rw [coe_rootSL2Q, hRdef, map_compSL2_fixQ c hct]
    rfl
  have hmapinj : Function.Injective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (fixQ K ℓ f).subtype) := by
    intro A B h
    apply Subtype.ext
    ext i j
    have := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) K =>
      (M : Matrix (Fin 2) (Fin 2) K) i j) h
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] at this
    exact this
  have hRo : orderOf R = 3 := by
    rw [← orderOf_injective _ hmapinj R, hRdef, map_compSL2_fixQ c hct]
    exact orderOf_compSL2 Nat.prime_three hc (sub_inv_ne_zero_of_orderOf Nat.prime_three
      (by norm_num) hc)
  have hρRo : orderOf (ρt R) = 3 := by
    have hdvd : orderOf (ρt R) ∣ 3 := hRo ▸ orderOf_map_dvd ρt R
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
    · exfalso
      rw [orderOf_eq_one_iff] at h1
      have h2 := hρt R
      rw [h1, map_one, map_one, hR] at h2
      have h3 := orderOf_twE6R0 Nat.prime_three (by norm_num) hc hct
      rw [← h2, orderOf_one] at h3
      omega
    · exact h1
  let Λ : (Fin (m + 1) → Multiplicative (ZMod 3)) →* ↥S :=
    (MonoidHom.noncommCoprod (powHom (ρt R) hρRo) (ιt.comp φ) fun a y => by
      change ρt R ^ (Multiplicative.toAdd a).val * ιt (φ y) =
        ιt (φ y) * ρt R ^ (Multiplicative.toAdd a).val
      rw [← map_pow]
      exact hcomm _ _).comp (splitHom (Multiplicative (ZMod 3)) m)
  have hΛ : ∀ x, Λ x = ρt R ^ (Multiplicative.toAdd (x 0)).val * ιt (φ fun i => x i.succ) :=
    fun x => rfl
  refine ⟨Λ, hΛ, fun s hs => ?_⟩
  obtain ⟨x, hx⟩ := hs
  refine ⟨x, (Λ x)⁻¹ * s, ?_, by group⟩
  apply ker_chevQuotHom_le_center_twE6 hcore
  rw [MonoidHom.mem_ker]
  apply e.injective
  rw [map_one, map_mul, map_mul, map_inv, map_inv]
  have hs' : e (chevQuotHom 3 S s) = twE6Phi hK hf hζ hσζ P hP (by norm_num) hc hct φ x := hx.symm
  rw [hs', hΛ, map_mul, map_mul, map_pow, map_pow, hρt, hιt, hR, twE6Phi_apply, inv_mul_cancel]

theorem isElemAbelian_comap_twE6Phi {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f) (hℓ2 : ℓ ≠ 2) (h3 : 3 ∣ ℓ ^ f + 1)
    {ζ : K} (hζ : ζ ≠ 0) (hσζ : unitaryInvolution K ℓ f ζ = -ζ) (P : GL (Fin 6) K)
    (hP : conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin 6) (Fin 6) K) *
      (P : Matrix (Fin 6) (Fin 6) K) = antidiag 6) [Fact (Nat.Prime 3)] {c : Kˣ}
    (hc : orderOf c = 3)
    (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K))
    {m : ℕ} (φ : (Fin m → Multiplicative (ZMod 3)) →* Su K ℓ f 6) {Ω : Type} [Group Ω]
    [Finite Ω] {S : Subgroup Ω} (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore 3 ↥S = ⊥)
    (e : PSimple 3 S ≃* ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))) :
    IsElemAbelian 3 ((twE6Phi hK hf hζ hσζ P hP (by norm_num) hc hct φ).range.comap
      (e.toMonoidHom.comp (chevQuotHom 3 S))) := by
  obtain ⟨ρt, ιt, hρt, hιt, hcomm⟩ := exists_lifts_twE6 hK hf hℓ2 h3 hζ hσζ P hP hcore e
  obtain ⟨Λ, -, hdec⟩ := comap_twE6Phi_decomp hK hf hζ hσζ P hP hc hct φ hcore e ρt ιt hρt hιt
    hcomm
  have hz3 : ∀ z ∈ Subgroup.center ↥S, z ^ 3 = 1 := fun z hz =>
    pow_three_of_mem_center_twE6 (Fact.out : ℓ.Prime) hℓ2 hf h3 hK _
      (unitaryInvolution_apply K ℓ f) hperf hcore e hz
  have hcomm' : ∀ (x y : Fin (m + 1) → Multiplicative (ZMod 3)) (z w : ↥S),
      z ∈ Subgroup.center ↥S → w ∈ Subgroup.center ↥S →
        Commute (Λ x * z) (Λ y * w) := by
    intro x y z w hz hw
    have cz := Subgroup.mem_center_iff.1 hz
    have cw := Subgroup.mem_center_iff.1 hw
    have h1 : Commute (Λ x) (Λ y) := (Commute.all x y).map Λ
    have h2 : Commute (Λ x) w := cw (Λ x)
    have h3' : Commute z (Λ y) := (cz (Λ y)).symm
    have h4 : Commute z w := (cz w).symm
    exact (h1.mul_right h2).mul_left (h3'.mul_right h4)
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun s hs => ?_⟩
  · obtain ⟨x, z, hz, hxz⟩ := hdec a a.2
    obtain ⟨y, w, hw, hyw⟩ := hdec b b.2
    change (a : ↥S) * b = b * a
    rw [hxz, hyw]
    exact hcomm' x y z w hz hw
  · obtain ⟨x, z, hz, rfl⟩ := hdec s hs
    have hc' : Commute (Λ x) z := (Subgroup.mem_center_iff.1 hz (Λ x))
    rw [hc'.mul_pow, ← map_pow, pow_eq_one_of_fin x, map_one, one_mul, hz3 z hz]

theorem commute_of_mem_comap_twE6Phi {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f) (hℓ2 : ℓ ≠ 2) (h3 : 3 ∣ ℓ ^ f + 1)
    {ζ : K} (hζ : ζ ≠ 0) (hσζ : unitaryInvolution K ℓ f ζ = -ζ) (P : GL (Fin 6) K)
    (hP : conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin 6) (Fin 6) K) *
      (P : Matrix (Fin 6) (Fin 6) K) = antidiag 6) [Fact (Nat.Prime 3)] {c : Kˣ}
    (hc : orderOf c = 3)
    (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K))
    {m : ℕ} (φ : (Fin m → Multiplicative (ZMod 3)) →* Su K ℓ f 6) {Ω : Type} [Group Ω]
    [Finite Ω] {S : Subgroup Ω} (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore 3 ↥S = ⊥)
    (e : PSimple 3 S ≃* ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))) (hS : S.Normal)
    {δ : K ≃+* K} (hδζ : δ ζ = ζ)
    (hPδ : ∀ i j, δ ((P : Matrix (Fin 6) (Fin 6) K) i j) = (P : Matrix (Fin 6) (Fin 6) K) i j)
    (hδc : δ ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K))
    (hφδ : ∀ x, suidMap (unitaryInvolution K ℓ f) 6 (ringEquiv_comm_of_finite _ δ) (φ x) = φ x)
    {b : Ω} (hb3 : b ^ 3 = 1)
    (hb : ∀ g : ↥S, e (chevQuotHom 3 S ⟨b * g * b⁻¹, hS.conj_mem _ g.2 _⟩) =
      fieldActor (unitaryInvolution K ℓ f) δ (e (chevQuotHom 3 S g)))
    {s : ↥S} (hs : s ∈ (twE6Phi hK hf hζ hσζ P hP (by norm_num) hc hct φ).range.comap
      (e.toMonoidHom.comp (chevQuotHom 3 S))) : b * (s : Ω) = (s : Ω) * b := by
  classical
  haveI : Finite ↥S := Subtype.finite
  haveI := hS
  obtain ⟨hQ5, -⟩ := five_le_pow_of_three_dvd (Fact.out : ℓ.Prime) hℓ2 hf h3
  obtain ⟨ρt, ιt, hρt, hιt, hcomm⟩ := exists_lifts_twE6 hK hf hℓ2 h3 hζ hσζ P hP hcore e
  obtain ⟨Λ, hΛ, hdec⟩ := comap_twE6Phi_decomp hK hf hζ hσζ P hP hc hct φ hcore e ρt ιt hρt hιt
    hcomm
  obtain ⟨x, z, hz, rfl⟩ := hdec s hs
  have hπc : ∀ g : ↥S, e (chevQuotHom 3 S g) = 1 → g ∈ Subgroup.center ↥S := fun g hg =>
    ker_chevQuotHom_le_center_twE6 hcore (by
      rw [MonoidHom.mem_ker]
      exact (map_eq_one_iff _ e.injective).1 hg)
  set β : ↥S →* ↥S := (MulAut.conjNormal b).toMonoidHom with hβdef
  have hβapp : ∀ g : ↥S, ((β g : ↥S) : Ω) = b * g * b⁻¹ := fun g =>
    MulAut.conjNormal_apply b g
  have hπβ : ∀ g : ↥S, e (chevQuotHom 3 S (β g)) =
      fieldActor (unitaryInvolution K ℓ f) δ (e (chevQuotHom 3 S g)) := fun g => by
    have h1 : β g = ⟨b * g * b⁻¹, hS.conj_mem _ g.2 _⟩ := Subtype.ext (hβapp g)
    rw [h1]
    exact hb g
  have hcomm_of : ∀ g : ↥S, β g = g → b * (g : Ω) = (g : Ω) * b := fun g h => by
    have h1 := hβapp g
    rw [h] at h1
    calc b * (g : Ω) = b * (g : Ω) * b⁻¹ * b := by group
      _ = (g : Ω) * b := by rw [← h1]
  haveI : Group.IsPerfect (Su K ℓ f 6) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_SUid
      (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK) (by norm_num)
      fun h => absurd h (by norm_num)
  have hι : β.comp ιt =
      ιt.comp (suidMap (unitaryInvolution K ℓ f) 6 (ringEquiv_comm_of_finite _ δ)) :=
    CFSG.LieType.SemisimpleCentralizers.HeldLang.eq_of_central_displacement_hom _ _ fun y =>
      hπc _ (by
        rw [map_mul, map_mul, map_inv, map_inv, MonoidHom.comp_apply, MonoidHom.comp_apply, hπβ,
          hιt, hιt, entrywise_leviSU hK hf hζ hσζ P hP hδζ hPδ, inv_mul_cancel])
  have hbι : ∀ y, b * (ιt (φ y) : Ω) = (ιt (φ y) : Ω) * b := fun y => hcomm_of _ (by
    have h1 := DFunLike.congr_fun hι (φ y)
    simp only [MonoidHom.comp_apply] at h1
    rw [h1, hφδ])
  have hδQ : ∀ a ∈ fixQ K ℓ f, δ a ∈ fixQ K ℓ f := fun a ha => by
    have ha' : unitaryInvolution K ℓ f a = a := ha
    show unitaryInvolution K ℓ f (δ a) = δ a
    rw [← ringEquiv_comm_of_finite (unitaryInvolution K ℓ f) δ a, ha']
  let δQ : fixQ K ℓ f →+* fixQ K ℓ f := δ.toRingHom.restrict _ _ hδQ
  haveI : Finite (fixQ K ℓ f) := Subtype.finite
  have hcardQ : Nat.card (fixQ K ℓ f) = ℓ ^ f := CFSG.LieType.Steinberg.card_fixedSubfield hK
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (fixQ K ℓ f)) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card _ (by omega)
  have hψρ : ∀ g, fieldActor (unitaryInvolution K ℓ f) δ (rootSL2Q K ℓ f g) =
      rootSL2Q K ℓ f (Matrix.SpecialLinearGroup.map δQ g) := fun g => by
    apply Subtype.ext
    rw [coe_fieldActor, coe_rootSL2Q, coe_rootSL2Q,
      CFSG.RankThree.Chevalley.entrywise_rootSL2_of_field]
    congr 1
  have hρ : β.comp ρt = ρt.comp (Matrix.SpecialLinearGroup.map δQ) :=
    CFSG.LieType.SemisimpleCentralizers.HeldLang.eq_of_central_displacement_hom _ _ fun g =>
      hπc _ (by
        rw [map_mul, map_mul, map_inv, map_inv, MonoidHom.comp_apply, MonoidHom.comp_apply, hπβ,
          hρt, hρt, hψρ, inv_mul_cancel])
  set R : Matrix.SpecialLinearGroup (Fin 2) (fixQ K ℓ f) :=
    compSL2 (⟨(c : K) + ((c⁻¹ : Kˣ) : K), hct⟩ : fixQ K ℓ f) with hRdef
  have hmapcomp : ∀ t : fixQ K ℓ f,
      Matrix.SpecialLinearGroup.map δQ (compSL2 t) = compSL2 (δQ t) := by
    intro t
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [compSL2]
  have hδR : Matrix.SpecialLinearGroup.map δQ R = R := by
    rw [hRdef, hmapcomp]
    congr 1
    exact Subtype.ext hδc
  have hbρ : b * (ρt R : Ω) = (ρt R : Ω) * b := hcomm_of _ (by
    have h1 := DFunLike.congr_fun hρ R
    simp only [MonoidHom.comp_apply] at h1
    rw [h1, hδR])
  have hbz : b * (z : Ω) = (z : Ω) * b := by
    by_cases hZ : Subgroup.center ↥S = ⊥
    · rw [hZ, Subgroup.mem_bot] at hz
      rw [hz, OneMemClass.coe_one, mul_one, one_mul]
    · exact commute_of_mem_center_of_card_three hS
        (card_center_eq_three (Fact.out : ℓ.Prime) hℓ2 hf h3 hK _
          (unitaryInvolution_apply K ℓ f) hperf hcore hZ e) hb3 hz
  have hbΛ : Commute b ((Λ x : ↥S) : Ω) := by
    rw [hΛ, Subgroup.coe_mul, SubgroupClass.coe_pow]
    exact (Commute.pow_right hbρ _).mul_right (hbι _)
  rw [Subgroup.coe_mul]
  exact (hbΛ.mul_right hbz).eq

end LiftA

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc
