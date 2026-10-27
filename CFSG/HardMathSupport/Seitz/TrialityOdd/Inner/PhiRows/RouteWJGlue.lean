module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWCoreDatum
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWCommutator

set_option linter.unusedSectionVars false

public noncomputable section

open scoped MatrixGroups

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open Subgroup CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg CFSG.ClassicalInvolution.G2D4Models
  CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

theorem exists_conj_in_JTw_of_involutions
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (σ : K ≃+* K) (hσq : ∀ c, σ c = c ^ (ℓ ^ f)) (hσ3 : ∀ c, σ (σ (σ c)) = c)
    {u v : twistedGroup σ.toRingHom} (hu : u ∈ JTw σ.toRingHom) (hv : v ∈ JTw σ.toRingHom)
    (hu2 : u * u = 1) (hv2 : v * v = 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    ∃ h ∈ JTw σ.toRingHom, h * u * h⁻¹ = v := by
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ (by omega) hK3
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have hq2 : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
  have hcardF : Nat.card (fixSubfield σ) = ℓ ^ f :=
    CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube hℓ hf hK σ hσq
  have hk3 : (3 : ℕ∞) ≤ ENat.card (fixSubfield σ) := by
    rw [ENat.card_eq_coe_natCard, hcardF]
    have : 3 ≤ ℓ ^ f := by
      have h3 : 3 ≤ ℓ := by
        have := hℓ.two_le
        rcases Nat.lt_or_ge ℓ 3 with h | h
        · omega
        · exact h
      exact le_trans h3 (Nat.le_self_pow (by omega) ℓ)
    exact_mod_cast this
  have hodd : Odd (Nat.card (fixSubfield σ)) := by
    rw [hcardF]; exact (hℓ.odd_of_ne_two hℓ2).pow
  let f0 : ↥(JTw σ.toRingHom) →* ModGL TwistTag.D4.tag K :=
    (twistedIncl σ.toRingHom).comp (JTw σ.toRingHom).subtype
  have hf0 : ∀ x, f0 x ∈ trialityFieldImage σ σ := by
    intro x
    have hx : Units.map (entrywiseHom σ.toRingHom) (twistedIncl σ.toRingHom (x : _)) =
        twistedIncl σ.toRingHom (x : _) := x.2
    have hmem := twistedIncl_mem_root σ hK2 hq2 hK hσq (x : twistedGroup σ.toRingHom)
    exact (d4_mem_trialityFieldImage_self_iff σ hσ3 ⟨twistedIncl σ.toRingHom (x : _), hmem⟩).2
      (Subtype.ext (by rw [coe_fieldActor]; exact hx))
  let Θ : ↥(JTw σ.toRingHom) →* ↥(trialityFieldImage σ σ) := f0.codRestrict _ hf0
  have hΘ : Function.Injective Θ := by
    intro x y h
    have h1 : twistedIncl σ.toRingHom (x : _) = twistedIncl σ.toRingHom (y : _) :=
      congrArg (fun z : ↥(trialityFieldImage σ σ) => (z : ModGL TwistTag.D4.tag K)) h
    exact Subtype.ext (twistedIncl_injective σ.toRingHom h1)
  have hΘs : Function.Surjective Θ := by
    rintro ⟨y, hy⟩
    have hyY := d4_trialityFieldImage_self_le σ hy
    have hrange := range_twistedIncl_eq_of_card (σ := σ.toRingHom) hK2 hq2 hK hσq
    obtain ⟨x, hx⟩ : y ∈ (twistedIncl σ.toRingHom).range := by rw [hrange]; exact hyY
    have hfix : Units.map (entrywiseHom σ.toRingHom) (twistedIncl σ.toRingHom x) =
        twistedIncl σ.toRingHom x := by
      have := (d4_mem_trialityFieldImage_self_iff σ hσ3 ⟨y, hyY⟩).1 hy
      have h2 := congrArg Subtype.val this
      rw [coe_fieldActor] at h2
      rw [hx]
      exact h2
    exact ⟨⟨x, hfix⟩, Subtype.ext hx⟩
  let e : ↥(JTw σ.toRingHom) ≃* ↥(adjointGroup Tag.G2 (fixSubfield σ)) :=
    (MulEquiv.ofBijective Θ ⟨hΘ, hΘs⟩).trans (trialityFieldImageEquivG2 σ hk3)
  have hu2' : e ⟨u, hu⟩ * e ⟨u, hu⟩ = 1 := by
    rw [← map_mul]
    have : (⟨u, hu⟩ * ⟨u, hu⟩ : ↥(JTw σ.toRingHom)) = 1 := Subtype.ext hu2
    rw [this, map_one]
  have hv2' : e ⟨v, hv⟩ * e ⟨v, hv⟩ = 1 := by
    rw [← map_mul]
    have : (⟨v, hv⟩ * ⟨v, hv⟩ : ↥(JTw σ.toRingHom)) = 1 := Subtype.ext hv2
    rw [this, map_one]
  have hu1' : e ⟨u, hu⟩ ≠ 1 := fun h =>
    hu1 (congrArg Subtype.val (e.injective (h.trans (map_one e).symm)))
  have hv1' : e ⟨v, hv⟩ ≠ 1 := fun h =>
    hv1 (congrArg Subtype.val (e.injective (h.trans (map_one e).symm)))
  obtain ⟨h, hh⟩ := CFSG.ClassicalInvolution.Balance.Bootstrap.g2_involutions_conj (K := fixSubfield σ)
    hodd hu2' hv2' hu1' hv1'
  refine ⟨((e.symm h : ↥(JTw σ.toRingHom)) : twistedGroup σ.toRingHom), (e.symm h).2, ?_⟩
  have : e.symm h * ⟨u, hu⟩ * (e.symm h)⁻¹ = ⟨v, hv⟩ := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hh
  exact congrArg Subtype.val this

theorem map_conj_commutator_centralizer {G : Type*} [Group G] (h w : G) :
    (⁅Subgroup.centralizer ({w} : Set G), Subgroup.centralizer ({w} : Set G)⁆).map
        (MulAut.conj h).toMonoidHom =
      ⁅Subgroup.centralizer ({h * w * h⁻¹} : Set G),
        Subgroup.centralizer ({h * w * h⁻¹} : Set G)⁆ := by
  have hc : (Subgroup.centralizer ({w} : Set G)).map (MulAut.conj h).toMonoidHom =
      Subgroup.centralizer ({h * w * h⁻¹} : Set G) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x ∈ Subgroup.centralizer ({w} : Set G) := hx
      rw [Subgroup.mem_centralizer_iff] at hx'
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      have := hx' w rfl
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc h * w * h⁻¹ * (h * x * h⁻¹) = h * (w * x) * h⁻¹ := by group
        _ = h * (x * w) * h⁻¹ := by rw [this]
        _ = h * x * h⁻¹ * (h * w * h⁻¹) := by group
    · intro hy
      refine ⟨h⁻¹ * y * h, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
      show h⁻¹ * y * h ∈ Subgroup.centralizer ({w} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      rw [Subgroup.mem_centralizer_iff] at hy
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      have := hy (h * w * h⁻¹) rfl
      have h2 : w * (h⁻¹ * y * h) = (h⁻¹ * y * h) * w := by
        calc w * (h⁻¹ * y * h) = h⁻¹ * ((h * w * h⁻¹) * y) * h := by group
          _ = h⁻¹ * (y * (h * w * h⁻¹)) * h := by rw [this]
          _ = (h⁻¹ * y * h) * w := by group
      exact h2
  rw [Subgroup.map_commutator, hc]

theorem exists_g_for_placement
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (σ : K ≃+* K) (hσq : ∀ c, σ c = c ^ (ℓ ^ f))
    (hσ : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (w : twistedGroup σ.toRingHom) (hww : w * w = 1) (hw1 : w ≠ 1)
    (hwJ : w ∈ JTw σ.toRingHom) :
    ∃ g ∈ JTw σ.toRingHom, g * w * g⁻¹ = slLong σ.toRingHom hσ (-1) ∧
      ∀ y ∈ ⁅Subgroup.centralizer ({w} : Set (twistedGroup σ.toRingHom)),
        Subgroup.centralizer ({w} : Set (twistedGroup σ.toRingHom))⁆,
        g * y * g⁻¹ ∈ invCentGroup σ.toRingHom hσ := by
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ (by omega) hK3
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have h2K : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have hq2 : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
  have hKm : (-1 : Kˣ) ≠ 1 := by
    intro h
    apply h2K
    have := congrArg Units.val h
    simp only [Units.val_neg, Units.val_one] at this
    linear_combination -this
  have hrange := range_twistedIncl_eq_of_card (σ := σ.toRingHom) hK2 hq2 hK hσq
  have hC₀ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≤
      (twistedIncl σ.toRingHom).range := hrange.ge
  have hgF : ∀ y : twistedGroup σ.toRingHom,
      twistedIncl σ.toRingHom y ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    fun y => hrange ▸ ⟨y, rfl⟩
  have hσ3 : ∀ c, σ (σ (σ c)) = c := fun c => hσ c
  set τ := slLong σ.toRingHom hσ (-1) with hτ
  have hτJ : τ ∈ JTw σ.toRingHom := slLong_mem_JTw hσ _
  have hτ2 : τ * τ = 1 := by
    rw [hτ, ← map_mul, neg_one_mul_neg_one_SL2, map_one]
  have hτ1 : τ ≠ 1 := by
    intro h
    have h' : (-1 : SL(2, fixedField σ.toRingHom)) = 1 :=
      slLong_injective hσ (by
        calc slLong σ.toRingHom hσ (-1) = τ := rfl
          _ = 1 := h
          _ = slLong σ.toRingHom hσ 1 := (map_one _).symm)
    have h2F : (2 : fixedField σ.toRingHom) ≠ 0 := by
      intro h0
      apply h2K
      have := congrArg (fixedField σ.toRingHom).subtype h0
      rwa [map_ofNat, map_zero] at this
    exact neg_one_ne_one_SL2_of_two_ne_zero h2F h'
  obtain ⟨g, hgJ, hg⟩ := exists_conj_in_JTw_of_involutions hℓ hℓ2 hf hK σ hσq hσ3 hwJ hτJ hww hτ2
    hw1 hτ1
  have hcomm := comm_centralizer_le_invCentGroup hσ hKm hC₀ hgF
  refine ⟨g, hgJ, hg, ?_⟩
  intro y hy
  have h1 : g * y * g⁻¹ ∈ (⁅Subgroup.centralizer ({w} : Set (twistedGroup σ.toRingHom)),
      Subgroup.centralizer ({w} : Set (twistedGroup σ.toRingHom))⁆).map
        (MulAut.conj g).toMonoidHom := ⟨y, hy, rfl⟩
  rw [map_conj_commutator_centralizer, hg] at h1
  exact hcomm h1

theorem phi6Placement_of_J_data
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (σ : K ≃+* K) (hσq : ∀ c, σ c = c ^ (ℓ ^ f))
    (hσ : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (E₀ : Subgroup (twistedGroup σ.toRingHom)) (w : twistedGroup σ.toRingHom)
    (hww : w * w = 1) (hw1 : w ≠ 1) (hwJ : w ∈ JTw σ.toRingHom)
    (D : Subgroup (twistedGroup σ.toRingHom)) (hDs : IsSimpleGroup D) (hDperf : ⁅D, D⁆ = D)
    (hDc : Nat.card D = ℓ ^ f * ((ℓ ^ f) ^ 2 - 1) / 2) (hDw : ∀ x ∈ D, x * w = w * x)
    (hDJ : D ≤ JTw σ.toRingHom) (x₁ : twistedGroup σ.toRingHom) (hx₁E : x₁ ∈ E₀) (hx₁1 : x₁ ≠ 1)
    (hDx : ∀ x ∈ D, x * x₁ = x₁ * x) (c : twistedGroup σ.toRingHom) (hcE : c ∈ E₀) (hc1 : c ≠ 1)
    (hcJ : c ∈ JTw σ.toRingHom) (a b : twistedGroup σ.toRingHom)
    (haE : ∀ x ∈ E₀, a * x * a⁻¹ ∈ E₀) (hbE : ∀ x ∈ E₀, b * x * b⁻¹ ∈ E₀)
    (haC : a ∈ ⁅Subgroup.centralizer ({w} : Set (twistedGroup σ.toRingHom)),
      Subgroup.centralizer ({w} : Set (twistedGroup σ.toRingHom))⁆)
    (hbC : b ∈ ⁅Subgroup.centralizer ({w} : Set (twistedGroup σ.toRingHom)),
      Subgroup.centralizer ({w} : Set (twistedGroup σ.toRingHom))⁆)
    (hab : a * b * a⁻¹ * b⁻¹ = w) :
    Phi6Placement σ.toRingHom hσ (ℓ ^ f) E₀ w := by
  obtain ⟨g, hgJ, hg, hMconj⟩ := exists_g_for_placement hℓ hℓ2 hf hK σ hσq hσ w hww hw1 hwJ
  have hconjJ : ∀ y ∈ JTw σ.toRingHom, g * y * g⁻¹ ∈ JTw σ.toRingHom := fun y hy =>
    mul_mem (mul_mem hgJ hy) (inv_mem hgJ)
  exact ⟨g, D, x₁, c, a, b, hg, hDs, hDperf, hDc, hDw, hx₁E, hx₁1, hDx,
    fun x hx => hconjJ x (hDJ hx), hcE, hc1, hconjJ c hcJ, haE, hbE, hMconj a haC, hMconj b hbC, hab⟩

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
