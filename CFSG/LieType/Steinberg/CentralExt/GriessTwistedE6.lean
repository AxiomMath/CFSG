module

public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Three
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Center
public import CFSG.LieType.Steinberg.CentralExt.CoverTransfer
public import CFSG.LieType.Chevalley.TwistedE6EvenCover
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.LieType.Steinberg.CentralExt.GriessClassical

public section

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule

namespace CFSG.LieType.Steinberg.CentralExt.GriessExceptional

theorem lieModel_twistedE6_four {K : Type} [Field K] [Finite K] {σ : K →+* K}
    (hK : Nat.card K = 4 ^ 2) (hσq : ∀ c, σ c = c ^ 4) :
    CFSG.Blueprint.LieModel (DerivedCentralQuotient (twistedFixedGroup .E6 K σ)) .twistedE6 0 2
      2 :=
  Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, by norm_num, rfl⟩, K, inferInstance,
    inferInstance, by rw [hK]; rfl, σ, fun c => by rw [hσq]; norm_num, ⟨MulEquiv.refl _⟩⟩)

theorem twistedE6_center_derived_eq_bot {K : Type} [Field K] [Finite K] {θ : K →+* K}
    (hθ : ∀ c, θ (θ c) = c) (hK4 : 4 ≤ Nat.card K) :
    Subgroup.center ↥⁅twistedFixedGroup .E6 K θ, twistedFixedGroup .E6 K θ⁆ = ⊥ := by
  have : Group.IsPerfect (fixedGroup K θ) := fixedGroup_isPerfect_of_four_le_card θ hθ hK4
  let e : fixedGroup K θ ⧸ Subgroup.center (fixedGroup K θ) ≃*
      ↥⁅twistedFixedGroup .E6 K θ, twistedFixedGroup .E6 K θ⁆ :=
    (QuotientGroup.quotientMulEquivOfEq
      (TwistedE6Closed.ker_twistedIsogeny_eq_center hθ hK4).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        (CFSG.LieType.Simplicity.twistedIsogeny_surjective θ hθ hK4))
  have hperf : commutator (fixedGroup K θ ⧸ Subgroup.center (fixedGroup K θ)) = ⊤ := by
    have : Group.IsPerfect (fixedGroup K θ ⧸ Subgroup.center (fixedGroup K θ)) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    exact Group.IsPerfect.commutator_eq_top
  have hZ := CFSG.AGLEmbedding.center_quotient_center_eq_bot_of_commutator_eq_top hperf
  rw [eq_bot_iff]
  intro z hz
  have hz' : e.symm z ∈ Subgroup.center (fixedGroup K θ ⧸ Subgroup.center (fixedGroup K θ)) :=
    Subgroup.mem_center_iff.2 fun g => e.injective (by
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact (Subgroup.mem_center_iff.1 hz (e g)))
  rw [hZ, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hz'
  exact (Subgroup.mem_bot).2 hz'

theorem twistedE6_four_exists_section {K : Type} [Field K] [Finite K] {θ : K →+* K}
    (hK : Nat.card K = 4 ^ 2) (hθq : ∀ c, θ c = c ^ 4) {E : Type} [Group E] [Finite E]
    {π : E →* fixedGroup K θ} (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ s : fixedGroup K θ →* E, ∀ g, π (s g) = g := by
  have hθ : ∀ c, θ (θ c) = c := TwistedE6Closed.theta_theta_of_card hK hθq
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (k := 4) (by norm_num) (by rw [hK]; norm_num)
  have : Finite (Module.End K (Fin e6Data.d →₀ K)) := Module.finite_of_finite K
  have : Group.IsPerfect (fixedGroup K θ) := fixedGroup_isPerfect_of_four_le_card θ hθ hK4
  have hZA := twistedE6_center_derived_eq_bot hθ hK4
  set ψ : fixedGroup K θ →* DerivedCentralQuotient (twistedFixedGroup .E6 K θ) :=
    (QuotientGroup.mk' _).comp (CFSG.LieType.Simplicity.twistedIsogeny θ hθ hK4)
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp
    (CFSG.LieType.Simplicity.twistedIsogeny_surjective θ hθ hK4)
  have hker : ψ.ker = Subgroup.center (fixedGroup K θ) := by
    rw [← TwistedE6Closed.ker_twistedIsogeny_eq_center hθ hK4]
    ext g
    simp only [ψ, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hZA, Subgroup.mem_bot]
  exact CoprimeSplit.exists_section_of_parts (p := 2) hπ hcen
    (fun E' _ _ π' hπ' hcen' hp' => CoverTransfer.exists_section_of_isogeny_cover_trivial ψ hψ hker
      (fun P _ _ _ η hη hC h2 =>
        (CFSG.LieType.Chevalley.twisted_E6_nonprime_even_field_central_two_cover_trivial η hη hC
          h2 (f := 2) le_rfl (lieModel_twistedE6_four hK hθq)).1)
      E' π' hπ' hcen' hp')
    (fun E' _ _ π' hπ' hcen' hc' =>
      TwistedE6Closed.twistedE6_exists_section_of_coprime hθ hπ' hcen' hc')

theorem twistedE6_hopfMultiplier {K : Type} [Field K] [Finite K] {θ : K →+* K} {q : ℕ}
    (hq : 3 ≤ q) (hK : Nat.card K = q ^ 2) (hθq : ∀ c, θ c = c ^ q) :
    commutator (DerivedCentralQuotient (twistedFixedGroup .E6 K θ)) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier
        (DerivedCentralQuotient (twistedFixedGroup .E6 K θ)) ≃*
          Multiplicative (ZMod (Nat.gcd 3 (q + 1)))) := by
  have hθ : ∀ c, θ (θ c) = c := TwistedE6Closed.theta_theta_of_card hK hθq
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; nlinarith
  have : Finite (Module.End K (Fin e6Data.d →₀ K)) := Module.finite_of_finite K
  have : Group.IsPerfect (fixedGroup K θ) := fixedGroup_isPerfect_of_four_le_card θ hθ hK4
  obtain ⟨hperf, ⟨e⟩⟩ := FieldFour.hopfMultiplier_of_isogeny
    (CFSG.LieType.Simplicity.twistedIsogeny θ hθ hK4)
    (CFSG.LieType.Simplicity.twistedIsogeny_surjective θ hθ hK4)
    (TwistedE6Closed.ker_twistedIsogeny_eq_center hθ hK4) (twistedE6_center_derived_eq_bot hθ hK4)
    fun E _ _ π hπ hcen => by
      rcases (show q = 3 ∨ q = 4 ∨ 5 ≤ q by omega) with rfl | rfl | hq5
      · exact TwistedE6Closed.twistedE6_three_exists_section_of_central θ hK hθq hπ hcen
      · exact twistedE6_four_exists_section hK hθq hπ hcen
      · exact TwistedE6Closed.twistedE6_exists_section_of_central θ hq5 hK hθq hπ hcen
  obtain ⟨hcard, hcyc⟩ := TwistedE6Closed.card_center_fixedGroup hK hθq
  rw [← hcard]
  exact ⟨hperf, ⟨e.trans (zmodCyclicMulEquiv hcyc).symm⟩⟩

variable {X : Type} [Group X] {n p f : ℕ}

theorem twistedE6_row (hmodel : CFSG.Models.LieModel X .twistedE6 n p f) (hq : 3 ≤ p ^ f) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃*
        generic .twistedE6 n p f × exceptional .twistedE6 n p f) := by
  obtain ⟨-, hcl | ⟨-, ⟨d, hv⟩, hd, ⟨e⟩⟩⟩ := hmodel
  · exact hcl.2.elim
  · cases d with
    | twistedE6 q =>
      obtain ⟨rfl, rfl⟩ := hd
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      set K := GaloisField q.p (2 * q.exponent)
      have hK2 : Nat.card K = q.card ^ 2 := by
        rw [TauCeti.PrimePower.card_def, GaloisField.card _ _ (by have := q.exponent_pos; omega),
          ← pow_mul, mul_comm]
      have hK : Nat.card K = q.card ^ CFSG.Blueprint.Chevalley.TwistTag.E6.order := hK2
      let σ : K →+* K := iterateFrobenius K q.p q.exponent
      have hσ : ∀ x, σ x = x ^ q.card := fun x => by
        rw [TauCeti.PrimePower.card_def]
        exact iterateFrobenius_def q.p q.exponent x
      obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).twistedE6 q hv K hK σ hσ
      have hq' : 3 ≤ q.card := by
        rw [TauCeti.PrimePower.card_def]
        exact hq
      have hM := twistedE6_hopfMultiplier hq' hK2 hσ
      rw [TauCeti.PrimePower.card_def] at hM
      refine GriessClassical.of_mulEquiv (e.trans b.symm)
        (GriessClassical.of_mulEquiv_target ?_ hM)
      refine (GriessClassical.padOne _).trans (GriessClassical.toGenEx (t := .twistedE6) (n := n)
        (p := q.p) (f := q.exponent) (a₁ := Nat.gcd 3 (q.p ^ q.exponent + 1)) (a₂ := 1) (b₁ := 1)
        (b₂ := 1) rfl ?_)
      unfold exceptionalOrders
      split <;> simp_all
    | _ => simp [CFSG.Models.NamesTag] at hd

end CFSG.LieType.Steinberg.CentralExt.GriessExceptional
