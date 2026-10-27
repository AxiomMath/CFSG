module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviCentralizerY

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Std CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint


variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem eq_one_of_fix_omegaMinusLevi (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (β : MulAut (graphFixedRootGroup TwistTag.E6 K σ))
    (hβX : ∀ x : graphFixedRootGroup TwistTag.E6 K σ,
      (x : ModGL TwistTag.E6.tag K) ∈ shortRootTorus (algebraMap k K) → β x = x)
    (hβD : ∀ x : graphFixedRootGroup TwistTag.E6 K σ,
      (x : ModGL TwistTag.E6.tag K) ∈ omegaMinusLevi σ → β x = x)
    (n : ℕ) (hβn : β ^ 2 ^ n = 1) : β = 1 := by
  have hf : 1 ≤ f := by omega
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Finite K := finite_of_card hK
  have : CharP K 2 := charP_two_of_card hf hK
  have hσι : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c :=
    E6GraphLevi.fixed_algebraMap (sigma_eq_pow_card hk hσ)
  obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
  have hσE : ∀ c, σE c = c ^ 2 ^ f := hσ
  have hA := EvenExceptionalActorCoverage.fixedDiagonalFieldActors_E6_eq_top hf hK σE hσE
  obtain ⟨g, hg, a, -, δ, -, hβ⟩ :=
    ((Chevalley_diagonal_field_actor_data.2 TwistTag.E6 K σE).1 β).1 (hA ▸ Subgroup.mem_top β)
  let ι : graphFixedRootGroup TwistTag.E6 K σE.toRingHom → ModGL .E6 K :=
    fun x => (show ModGL .E6 K from x.1)
  let gE : ModGL .E6 K := (show ModGL .E6 K from g)
  have hβ' : ∀ x : graphFixedRootGroup TwistTag.E6 K σE.toRingHom,
      ι (β x) = gE * rootDiagUnit .E6 a * Units.map (entrywiseHom δ.toRingHom) (ι x) *
        (rootDiagUnit .E6 a)⁻¹ * gE⁻¹ := hβ
  have hgA : gE ∈ adjointGroup .E6 K := (graphFixedRootGroup_le _ _ _ hg).1
  have hgx : ∀ {x : ModGL .E6 K} (hx : x ∈ graphFixedRootGroup TwistTag.E6 K σE.toRingHom),
      β ⟨x, hx⟩ = ⟨x, hx⟩ →
      gE * (rootDiagUnit .E6 a * Units.map (entrywiseHom δ.toRingHom) x *
        (rootDiagUnit .E6 a)⁻¹) * gE⁻¹ = x := by
    intro x hx hβx
    have e := congrArg ι hβx
    rw [hβ'] at e
    have e' : gE * rootDiagUnit .E6 a * Units.map (entrywiseHom δ.toRingHom) x *
        (rootDiagUnit .E6 a)⁻¹ * gE⁻¹ = x := e
    rw [show gE * (rootDiagUnit .E6 a * Units.map (entrywiseHom δ.toRingHom) x *
        (rootDiagUnit .E6 a)⁻¹) * gE⁻¹ = gE * rootDiagUnit .E6 a *
          Units.map (entrywiseHom δ.toRingHom) x * (rootDiagUnit .E6 a)⁻¹ * gE⁻¹ by group]
    exact e'
  obtain ⟨hδ1, hm⟩ := core_Y (k := k) hf2 hk hK hσ hgA a δ
    (fun x hx => hgx (omegaMinusLevi_le_graphFixedRootGroup _ hx)
      (hβD ⟨x, omegaMinusLevi_le_graphFixedRootGroup _ hx⟩ hx))
    (Or.inr fun c => by
      have hd : rootDiagUnit Tag.E6 (d4CentralDiag (Units.map (algebraMap k K).toMonoidHom c)
          (Units.map (algebraMap k K).toMonoidHom c)) ∈ shortRootTorus (algebraMap k K) :=
        ⟨c, rfl⟩
      exact hgx (shortRootTorus_le_C0 hσι hd) (hβX ⟨_, shortRootTorus_le_C0 hσι hd⟩ hd))
  have hδ : δ = RingEquiv.refl K := RingEquiv.ext hδ1
  subst hδ
  set m := gE * rootDiagUnit .E6 a with hmdef
  have hβm : ∀ x : graphFixedRootGroup TwistTag.E6 K σE.toRingHom,
      ι (β x) = m * ι x * m⁻¹ := by
    intro x
    have e1 : Units.map (entrywiseHom (RingEquiv.refl K).toRingHom) (ι x) = ι x :=
      Units.ext (entrywise_id _)
    rw [hβ' x, e1, hmdef]
    group
  have hpow : ∀ N : ℕ, ∀ x : graphFixedRootGroup TwistTag.E6 K σE.toRingHom,
      ι ((β ^ N) x) = m ^ N * ι x * (m ^ N)⁻¹ := by
    intro N
    induction N with
    | zero =>
      intro x
      show ι x = 1 * ι x * 1⁻¹
      group
    | succ N ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, hβm, ih, pow_succ']
      group
  have hmN : m ^ Nat.card Kˣ = 1 := pow_card_units_eq_one_of_mem_d4CentralTorus hm
  have hβN : β ^ Nat.card Kˣ = 1 := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    have h := hpow (Nat.card Kˣ) x
    rw [hmN, one_mul, inv_one, mul_one] at h
    exact h
  have hodd : Nat.Coprime (2 ^ n) (Nat.card Kˣ) := by
    rw [Nat.card_units, hK]
    refine Nat.Coprime.pow_left _ ((Nat.coprime_two_left).2 ?_)
    have h4 : 2 ∣ (2 ^ f) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
    have hpos : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    obtain ⟨m', hm'⟩ := h4
    rw [Nat.odd_iff]
    omega
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hodd (orderOf_dvd_of_pow_eq_one hβn)
    (orderOf_dvd_of_pow_eq_one hβN))

end CFSG.SeitzReduction.TwistedE6Pilot
