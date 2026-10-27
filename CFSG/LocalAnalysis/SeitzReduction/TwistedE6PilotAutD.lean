module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviCentralizer

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley.E6GraphHighestRoot


section Tools

variable {K : Type} [Field K]

theorem rootDiagUnit_highDiag_pow (ν : Kˣ) (N : ℕ) :
    rootDiagUnit .E6 (EPilot.highDiag .E6 ν) ^ N = rootDiagUnit .E6 (EPilot.highDiag .E6 (ν ^ N)) := by
  induction N with
  | zero => rw [pow_zero, pow_zero, EPilot.highDiag_one, rootDiagUnit_one]
  | succ N ih =>
    rw [pow_succ, ih, ← rootDiagUnit_mul, pow_succ]
    congr 1
    rw [EPilot.highDiag, EPilot.highDiag, EPilot.highDiag, Pi.mulSingle_mul]

theorem eq_one_of_pow_two_pow_eq_one {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {ν : Kˣ} {N : ℕ} (h : ν ^ 2 ^ N = 1) : ν = 1 := by
  have : Finite K := finite_of_card hK
  have h1 : orderOf ν ∣ 2 ^ N := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf ν ∣ Nat.card Kˣ := orderOf_dvd_natCard ν
  rw [Nat.card_units, hK] at h2
  have hodd : Nat.Coprime (2 ^ N) ((2 ^ f) ^ 2 - 1) := by
    refine Nat.Coprime.pow_left _ ((Nat.coprime_two_left).2 ?_)
    have h4 : 2 ∣ (2 ^ f) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
    have hpos : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    obtain ⟨m, hm⟩ := h4
    rw [Nat.odd_iff]
    omega
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hodd h1 h2)

end Tools

section AutD

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem eq_one_of_fix_su6Levi (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (β : MulAut (graphFixedRootGroup TwistTag.E6 K σ))
    (hβX : ∀ x : graphFixedRootGroup TwistTag.E6 K σ,
      (x : ModGL TwistTag.E6.tag K) ∈ thetaTorus (algebraMap k K) → β x = x)
    (hβD : ∀ x : graphFixedRootGroup TwistTag.E6 K σ,
      (x : ModGL TwistTag.E6.tag K) ∈ su6Levi σ → β x = x)
    (n : ℕ) (hβn : β ^ 2 ^ n = 1) : β = 1 := by
  have hf : 1 ≤ f := by omega
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Finite K := finite_of_card hK
  have : CharP K 2 := charP_two_of_card hf hK
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
        (rootDiagUnit .E6 a)⁻¹ * (gE)⁻¹ := hβ
  have hgA : gE ∈ adjointGroup .E6 K := (graphFixedRootGroup_le _ _ _ hg).1
  obtain ⟨hδ1, hm⟩ := core_X hf2 hk hK hσ hgA a δ (fun x hx => by
    have e := congrArg ι (hβD ⟨x, su6Levi_le_graphFixedRootGroup _ hx⟩ hx)
    rw [hβ'] at e
    have e' : gE * rootDiagUnit .E6 a * Units.map (entrywiseHom δ.toRingHom) x *
        (rootDiagUnit .E6 a)⁻¹ * gE⁻¹ = x := e
    rw [show gE * (rootDiagUnit .E6 a * Units.map (entrywiseHom δ.toRingHom) x *
        (rootDiagUnit .E6 a)⁻¹) * gE⁻¹ = gE * rootDiagUnit .E6 a *
          Units.map (entrywiseHom δ.toRingHom) x * (rootDiagUnit .E6 a)⁻¹ * gE⁻¹ by group]
    exact e')
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
  have hq : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  obtain ⟨c₀, hc₀⟩ := F4Pilot.exists_three_le_orderOf hq
  have hc' : 3 ≤ orderOf (Units.map (algebraMap k K).toMonoidHom c₀) := by
    rw [orderOf_injective _ (Units.map_injective (algebraMap k K).injective) c₀]
    exact hc₀
  have hhW := rootDiagUnit_highDiag_mem_thetaTorus (algebraMap k K) c₀
  have hhC := thetaTorus_le_C0 hf hk hK hσ hhW
  have e := congrArg ι (hβX ⟨_, hhC⟩ hhW)
  rw [hβm] at e
  have e' : m * rootDiagUnit .E6 (EPilot.highDiag .E6 (Units.map (algebraMap k K).toMonoidHom c₀)) *
      m⁻¹ = rootDiagUnit .E6 (EPilot.highDiag .E6 (Units.map (algebraMap k K).toMonoidHom c₀)) := e
  have hmc : m * rootDiagUnit .E6 (EPilot.highDiag .E6 (Units.map (algebraMap k K).toMonoidHom c₀)) =
      rootDiagUnit .E6 (EPilot.highDiag .E6 (Units.map (algebraMap k K).toMonoidHom c₀)) * m := by
    calc _ = (m * rootDiagUnit .E6 (EPilot.highDiag .E6
          (Units.map (algebraMap k K).toMonoidHom c₀)) * m⁻¹) * m := by group
      _ = _ := by rw [e']
  obtain ⟨ν, hν⟩ := EPilot.mem_highTorusLine.1 (mem_highTorusLine_of_mem_highRootSL2 hm hc' hmc)
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
  have hX1 : pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K 1) ∈
      thetaRankOneGroup (algebraMap k K) :=
    mem_sup_left ((mem_thetaRootGroup _).2 ⟨1, rfl⟩)
  have hXC := thetaRankOneGroup_le_C0 hf hk hK hσ hX1
  have e2 := congrArg ι (congrArg (fun γ : MulAut _ => γ ⟨_, hXC⟩) hβn)
  rw [hpow, ← hν, rootDiagUnit_highDiag_pow] at e2
  have e2' : rootDiagUnit .E6 (EPilot.highDiag .E6 (ν ^ 2 ^ n)) * pinnedX .E6 K (highRoot .E6) 1 *
      (rootDiagUnit .E6 (EPilot.highDiag .E6 (ν ^ 2 ^ n)))⁻¹ = pinnedX .E6 K (highRoot .E6) 1 := by
    have h1 : algebraMap k K 1 = 1 := map_one _
    simp only [h1] at e2
    exact e2
  rw [rootDiagUnit_conj_pinnedX _ (isRoot_highRoot _), EPilot.rootChar_highDiag,
    EPilot.highRoot_highNode (Or.inl rfl), mul_one] at e2'
  have e3 := pinnedX_injective .E6 K _ e2'
  have hν2 : ν ^ 2 ^ (n + 1) = 1 := by
    refine Units.ext ?_
    rw [pow_succ, pow_mul, Units.val_one]
    exact_mod_cast e3
  have hν1 := eq_one_of_pow_two_pow_eq_one hf hK hν2
  have hm1 : m = 1 := by rw [← hν, hν1, EPilot.highDiag_one, rootDiagUnit_one]
  refine MulEquiv.ext fun x => Subtype.ext ?_
  have h := hβm x
  rw [hm1, one_mul, inv_one, mul_one] at h
  exact h

theorem eq_one_of_fix_su6Levi_conj (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (n : graphFixedRootGroup TwistTag.E6 K σ) (β : MulAut (graphFixedRootGroup TwistTag.E6 K σ))
    (hβX : ∀ x : graphFixedRootGroup TwistTag.E6 K σ, (x : ModGL TwistTag.E6.tag K) ∈
      (thetaTorus (algebraMap k K)).map (MulAut.conj (n : ModGL TwistTag.E6.tag K)).toMonoidHom →
        β x = x)
    (hβD : ∀ x : graphFixedRootGroup TwistTag.E6 K σ, (x : ModGL TwistTag.E6.tag K) ∈
      (su6Levi σ).map (MulAut.conj (n : ModGL TwistTag.E6.tag K)).toMonoidHom → β x = x)
    (m : ℕ) (hβn : β ^ 2 ^ m = 1) : β = 1 := by
  set β' := (MulAut.conj n)⁻¹ * β * ((MulAut.conj n)⁻¹)⁻¹ with hβ'def
  have hfix : ∀ x : graphFixedRootGroup TwistTag.E6 K σ,
      β (MulAut.conj n x) = MulAut.conj n x → β' x = x := by
    intro x hx
    rw [hβ'def, inv_inv, MulAut.mul_apply, MulAut.mul_apply, hx, ← MulAut.mul_apply,
      inv_mul_cancel, MulAut.one_apply]
  have hconj : ∀ {A : Subgroup (ModGL TwistTag.E6.tag K)} (x : graphFixedRootGroup TwistTag.E6 K σ),
      (x : ModGL TwistTag.E6.tag K) ∈ A →
      ((MulAut.conj n x : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) ∈
        A.map (MulAut.conj (n : ModGL TwistTag.E6.tag K)).toMonoidHom :=
    fun x hx => ⟨x, hx, rfl⟩
  have h1 : β' = 1 := eq_one_of_fix_su6Levi hf2 hk hK hσ β'
    (fun x hx => hfix x (hβX _ (hconj x hx))) (fun x hx => hfix x (hβD _ (hconj x hx))) m (by
      rw [hβ'def, conj_pow, hβn, mul_one, mul_inv_cancel])
  calc β = ((MulAut.conj n)⁻¹)⁻¹ * β' * (MulAut.conj n)⁻¹ := by rw [hβ'def]; group
    _ = 1 := by rw [h1, mul_one, inv_inv, mul_inv_cancel]

end AutD

end CFSG.SeitzReduction.TwistedE6Pilot
