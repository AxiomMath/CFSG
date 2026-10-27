module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityA2TwoFaithful

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

section Twisted

theorem map_twistedGroup_eq_graphFixedRootGroup_two
    {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    (twistedGroup σ.toRingHom).map (adjointGroup d4 K).subtype =
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
  obtain ⟨-, -, -, -, -, h1, -, -⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσ
  have hq : 2 ≤ 2 ^ f := Nat.le_self_pow (by omega) 2
  exact (commutator_twistedFixedGroup_eq_map σ.toRingHom hq hK (fun c => hσ c)).symm.trans h1

theorem outer_involution_false_of_dvd_two {f : ℕ} (hf : 1 ≤ f) (hfe : Even f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hcard : 2 ^ f + 1 ∣ Nat.card ↥(fixSub φ))
    (ζ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hζ2 : ζ ^ 2 = 1)
    (hζout : ζ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range)
    (hζfix : ∀ c ∈ fixSub φ, ζ c = c) : False := by
  classical
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  obtain ⟨-, hNF, ⟨Θ, hΘ, -, hΘker, hΘinv⟩, -, -, -, hcen, -⟩ :=
    even_triality_exact_automorphism_normal_form hf K hK σ hσ
  have hΘζ : Θ ζ ≠ 1 := fun h1 => hζout (by rw [← hΘker]; exact h1)
  obtain ⟨-, hη⟩ := (hΘinv ζ hζ2).resolve_left hΘζ
  obtain ⟨m, hm⟩ : ∃ m, f = m * 2 :=
    ⟨f / 2, (Nat.div_mul_cancel (even_iff_two_dvd.1 hfe)).symm⟩
  have hm1 : 1 ≤ m := by omega
  have hδ : ∀ c, Θ ζ c = c ^ 2 ^ (3 * m) := fun c => by
    rw [hη c]
    congr 2
    omega
  obtain ⟨⟨g, δ'⟩, hgδ, -⟩ := hNF ζ
  have hδ' : δ' = Θ ζ := (hΘ ζ g δ' hgδ).symm
  subst hδ'
  have hgδ' : ζ = MulAut.conj g * fieldActor (t := TwistTag.D4) σ (Θ ζ) := hgδ
  set φF : K ≃+* K := iterateFrobeniusEquiv K 2 1 with hφFdef
  have hφF : ∀ c, φF c = c ^ 2 := fun c => by
    rw [hφFdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def, pow_one]
  have hε : σ ^ (3 - 2) * φF ^ (f / 2) = Θ ζ := RingEquiv.ext fun c => by
    change (σ ^ 1) ((φF ^ (f / 2)) c) = Θ ζ c
    rw [pow_one, ringAut_pow_apply_of_frobenius hφF, hσ, hδ, ← pow_mul, ← pow_add]
    congr 2
    omega
  have hgp : (MulAut.conj g * fieldActor (t := TwistTag.D4) σ (σ ^ (3 - 2) * φF ^ (f / 2))) ^ 2 =
      1 := by
    rw [hε, ← hgδ']
    exact hζ2
  obtain ⟨h₀, hh₀⟩ := CFSG.RankThree.Chevalley.exists_inner_conj_triality_field_actor (p := 2)
    (r := 2) Nat.prime_two hf K hK σ hσ hcen (by norm_num) ⟨m, by omega⟩ (Or.inr rfl)
    (by norm_num) hφF g hgp
  rw [hε, ← hgδ'] at hh₀
  have hcardζ : Nat.card ↥(fixSub ζ) = (2 ^ m) ^ 12 * ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 6 - 1) *
      ((2 ^ m) ^ 8 + (2 ^ m) ^ 4 + 1) := by
    rw [← card_fixSub_conj (MulAut.conj h₀) ζ, hh₀]
    exact card_fixSub_fieldActor_two Nat.prime_two hm1 K (by rw [hK3, hm, ← mul_assoc]) σ
      (fun c => by rw [hσ c, hm]) (Θ ζ) hδ
  have hdvd := Subgroup.card_dvd_of_le (show fixSub φ ≤ fixSub ζ from fun c hc => hζfix c hc)
  rw [hcardζ] at hdvd
  have hq1 := hcard.trans hdvd
  rw [hm, pow_mul] at hq1
  have h12 := sq_add_one_dvd_twelve (Nat.one_le_pow _ _ (by norm_num)) hq1
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · obtain rfl : m = 1 := by omega
    norm_num at h12
  · have h4 : 4 ≤ 2 ^ m :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    have h16 : 16 ≤ (2 ^ m) ^ 2 :=
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left h4 2
    have := Nat.le_of_dvd (by norm_num) h12
    omega

end Twisted

section Toral

@[expose] def TrialityA2ToralTwoFold : Prop :=
  ∀ f : ℕ, 1 ≤ f → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (2 ^ f)) → (2 ^ f) % 3 = 1 →
    ∀ (s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (d : Kˣ),
      Units.map σ.toRingHom.toMonoidHom d = d → d ^ 3 = 1 → d ≠ 1 →
      (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1] →
      (∀ N : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        N ≤ fixSub (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) →
        (∀ g ∈ fixSub (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ), ∀ n ∈ N,
          g * n * g⁻¹ ∈ N) → Nat.Coprime 3 (Nat.card N) → N = ⊥) ∧
      (∀ z ∈ fixSub (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ),
        (∀ x ∈ fixSub (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ), z * x = x * z) →
          z = 1) ∧
      (∃ U₀ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        U₀ ≤ fixSub (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) ∧ IsPGroup 2 U₀ ∧
          (2 ^ f) ^ 3 ≤ Nat.card U₀) ∧
      Nat.card ↥(fixSub (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)) =
        (2 ^ f - 1) ^ 2 * (2 ^ f) ^ 3 * ((2 ^ f + 1) * ((2 ^ f) ^ 2 + 2 ^ f + 1))

theorem trialityA2CoreFreeTwoToral_of_fold (h : TrialityA2ToralTwoFold) :
    TrialityA2CoreFreeTwoToral := by
  intro f hf K _ _ hK σ hσ hq s d hd hd3 hd1 hs
  obtain ⟨hA, hcen, hU, hcard⟩ := h f hf K hK σ hσ hq s d hd hd3 hd1 hs
  refine ⟨hA, trialityFaithfulTwo_holds f hf K hK σ hσ _ hcen hU ?_⟩
  intro hfe ζ hζ2 hζout _ hζfix
  refine outer_involution_false_of_dvd_two hf hfe hK hσ _ ?_ ζ hζ2 hζout hζfix
  rw [hcard]
  exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _

end Toral

end CFSG.HardMathSupport.Timmesfeld.CrossChar
