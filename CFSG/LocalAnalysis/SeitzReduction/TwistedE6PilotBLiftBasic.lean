module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviCentralizer

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley.E6GraphHighestRoot
open CFSG.ComponentClassification.M12Cover.CyclicKernel
  (eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two)

section Automizer

variable {G : Type*} [Group G]

theorem mem_of_forall_fix_fix_eq_conj {L : Subgroup G} {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hLt : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X D Y : Subgroup G} (hYo : Odd (Nat.card Y))
    (hAut : ∀ β : MulAut L, (∀ x : L, (x : G) ∈ X → β x = x) → (∀ x : L, (x : G) ∈ D → β x = x) →
      ∃ y : L, (y : G) ∈ Y ∧ β = MulAut.conj y)
    {c : G} (hcX : c ∈ centralizer (X : Set G)) (hct : c ∈ centralizer ({t} : Set G))
    (hcD : c ∈ centralizer (D : Set G)) (hco : Odd (orderOf c)) : c ∈ Y := by
  have hcN : c ∈ normalizer (L : Set G) := hLt hct
  set β := L.normalizerMonoidHom ⟨c, hcN⟩ with hβ
  have hβapp : ∀ a : L, ((β a : L) : G) = c * a * c⁻¹ := fun a => by
    simp [hβ, normalizerMonoidHom_apply_apply_coe]
  have hβX : ∀ x : L, (x : G) ∈ X → β x = x := fun x hx => by
    apply Subtype.ext
    rw [hβapp, ← mem_centralizer_iff.1 hcX _ hx, mul_inv_cancel_right]
  have hβD : ∀ x : L, (x : G) ∈ D → β x = x := fun x hx => by
    apply Subtype.ext
    rw [hβapp, ← mem_centralizer_iff.1 hcD _ hx, mul_inv_cancel_right]
  obtain ⟨y, hyY, hβy⟩ := hAut β hβX hβD
  have hyt : (y : G) * t = t * y := mem_centralizer_iff.1 htC _ y.2
  have hcen : (y : G)⁻¹ * c ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := by
    refine mem_inf.2 ⟨mem_centralizer_iff.2 fun l hl => ?_, ?_⟩
    · have h1 := congrArg Subtype.val (show β ⟨l, hl⟩ = y * ⟨l, hl⟩ * y⁻¹ by
        rw [hβy, MulAut.conj_apply])
      rw [hβapp] at h1
      simp only [coe_mul, coe_inv] at h1
      calc l * ((y : G)⁻¹ * c) = (y : G)⁻¹ * ((y : G) * l * (y : G)⁻¹) * c := by group
        _ = (y : G)⁻¹ * (c * l * c⁻¹) * c := by rw [h1]
        _ = (y : G)⁻¹ * c * l := by group
    · rw [mem_centralizer_singleton_iff]
      have hct' : c * t = t * c := mem_centralizer_singleton_iff.1 hct
      have hyt' : (y : G)⁻¹ * t = t * (y : G)⁻¹ := by
        calc (y : G)⁻¹ * t = (y : G)⁻¹ * (t * y) * (y : G)⁻¹ := by group
          _ = (y : G)⁻¹ * ((y : G) * t) * (y : G)⁻¹ := by rw [hyt]
          _ = t * (y : G)⁻¹ := by group
      calc (y : G)⁻¹ * c * t = (y : G)⁻¹ * (c * t) := by group
        _ = (y : G)⁻¹ * (t * c) := by rw [hct']
        _ = ((y : G)⁻¹ * t) * c := by group
        _ = (t * (y : G)⁻¹) * c := by rw [hyt']
        _ = t * ((y : G)⁻¹ * c) := by group
  rw [hK] at hcen
  rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two ht hcen with h1 | h1
  · have hcy : c = y := by
      calc c = (y : G) * ((y : G)⁻¹ * c) := by group
        _ = y := by rw [h1, mul_one]
    rw [hcy]
    exact hyY
  · exfalso
    have hcy : c = y * t := by
      calc c = (y : G) * ((y : G)⁻¹ * c) := by group
        _ = y * t := by rw [h1]
    obtain ⟨j, hj⟩ := hco
    have hpow : c ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one _
    have htt : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
    rw [hcy, (show Commute (y : G) t from hyt).mul_pow, pow_succ t, pow_mul, htt, one_pow,
      one_mul] at hpow
    have htY : t ∈ Y := by
      have : t = ((y : G) ^ (2 * j + 1))⁻¹ := eq_inv_of_mul_eq_one_right hpow
      rw [this]
      exact Y.inv_mem (Y.pow_mem hyY _)
    have h2 := Y.orderOf_dvd_natCard htY
    rw [ht] at h2
    exact (Nat.not_even_iff_odd.2 hYo) (even_iff_two_dvd.2 h2)

variable {L : Subgroup G} {C : Type*} [Group C]

theorem forall_eq_conj_map_symm (e : L ≃* C) {A D Y : Subgroup C}
    (hAut : ∀ β : MulAut C, (∀ x ∈ A, β x = x) → (∀ x ∈ D, β x = x) →
      ∃ w ∈ Y, β = MulAut.conj w) :
    ∀ β : MulAut L, (∀ a : L, (a : G) ∈ (A.map e.symm.toMonoidHom).map L.subtype → β a = a) →
      (∀ a : L, (a : G) ∈ (D.map e.symm.toMonoidHom).map L.subtype → β a = a) →
      ∃ y : L, (y : G) ∈ (Y.map e.symm.toMonoidHom).map L.subtype ∧ β = MulAut.conj y := by
  intro β hβX hβD
  have hmem : ∀ {B : Subgroup C} {x : C}, x ∈ B →
      ((e.symm x : L) : G) ∈ (B.map e.symm.toMonoidHom).map L.subtype :=
    fun {_ x} hx => ⟨e.symm x, ⟨x, hx, rfl⟩, rfl⟩
  obtain ⟨w, hwY, hw⟩ := hAut (MulAut.congr e β)
    (fun x hx => by
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hβX _ (hmem hx),
        MulEquiv.apply_symm_apply])
    (fun x hx => by
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hβD _ (hmem hx),
        MulEquiv.apply_symm_apply])
  refine ⟨e.symm w, hmem hwY, MulEquiv.ext fun a => ?_⟩
  have h := congrArg (fun γ : MulAut C => γ (e a)) hw
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply] at h
  rw [MulAut.conj_apply]
  apply e.injective
  rw [h, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

end Automizer

section Rigidity

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem exists_eq_conj_of_fix_su6Levi (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (β : MulAut (graphFixedRootGroup TwistTag.E6 K σ))
    (hβX : ∀ x : graphFixedRootGroup TwistTag.E6 K σ,
      (x : ModGL TwistTag.E6.tag K) ∈ thetaTorus (algebraMap k K) → β x = x)
    (hβD : ∀ x : graphFixedRootGroup TwistTag.E6 K σ,
      (x : ModGL TwistTag.E6.tag K) ∈ su6Levi σ → β x = x) :
    ∃ w : graphFixedRootGroup TwistTag.E6 K σ,
      (w : ModGL TwistTag.E6.tag K) ∈ thetaTorus (algebraMap k K) ∧ β = MulAut.conj w := by
  have hf : 1 ≤ f := by omega
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Finite K := finite_of_card hK
  have : CharP K 2 := charP_two_of_card hf hK
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
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
  have hX1 : pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K 1) ∈
      thetaRankOneGroup (algebraMap k K) :=
    mem_sup_left ((mem_thetaRootGroup _).2 ⟨1, rfl⟩)
  have hXC := thetaRankOneGroup_le_C0 hf hk hK hσ hX1
  set y := β ⟨_, hXC⟩ with hydef
  have hconj : rootDiagUnit .E6 (EPilot.highDiag .E6 ν) * pinnedX .E6 K (highRoot .E6) 1 *
      (rootDiagUnit .E6 (EPilot.highDiag .E6 ν))⁻¹ = pinnedX .E6 K (highRoot .E6) ((ν : K) ^ 2) := by
    rw [rootDiagUnit_conj_pinnedX _ (isRoot_highRoot _), EPilot.rootChar_highDiag,
      EPilot.highRoot_highNode (Or.inl rfl), mul_one, zpow_two, Units.val_mul, sq]
  have hy : (y : ModGL TwistTag.E6.tag K) =
      pinnedX TwistTag.E6.tag K e6HighestRoot ((ν : K) ^ 2) := by
    have e2 := hβm ⟨_, hXC⟩
    rw [← hν] at e2
    have e3 : (y : ModGL TwistTag.E6.tag K) =
        rootDiagUnit TwistTag.E6.tag (EPilot.highDiag .E6 ν) *
          pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K 1) *
            (rootDiagUnit TwistTag.E6.tag (EPilot.highDiag .E6 ν))⁻¹ := e2
    rw [e3, map_one]
    exact hconj
  have hF : twistHom TwistTag.E6 K σE.toRingHom (y : ModGL TwistTag.E6.tag K) = y :=
    ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (graphFixedRootGroup_le _ _ _ y.2)).2
  rw [hy, twistHom_pinnedX_eq_of_charTwo h2 _ isRoot_e6HighestRoot,
    permLattice_e6HighestRoot] at hF
  have hσν2 := pinnedX_injective TwistTag.E6.tag K _ hF
  rw [map_pow] at hσν2
  have hσν : σE.toRingHom (ν : K) = ν := frobenius_inj K 2 (by
    simp only [frobenius_def]
    exact hσν2)
  obtain ⟨ν₀, hν₀⟩ := (sigma_eq_self_iff hk hσ (ν : K)).1 hσν
  have hν₀ne : ν₀ ≠ 0 := by
    intro h
    rw [h, map_zero] at hν₀
    exact ν.ne_zero hν₀.symm
  have hνu : Units.map (algebraMap k K).toMonoidHom (Units.mk0 ν₀ hν₀ne) = ν :=
    Units.ext (by simpa using hν₀)
  have hmW : m ∈ thetaTorus (algebraMap k K) := by
    rw [← hν, ← hνu]
    exact rootDiagUnit_highDiag_mem_thetaTorus _ _
  refine ⟨⟨m, thetaTorus_le_C0 hf hk hK hσ hmW⟩, hmW, MulEquiv.ext fun x => Subtype.ext ?_⟩
  rw [MulAut.conj_apply]
  exact hβm x

end Rigidity

end CFSG.SeitzReduction.TwistedE6Pilot
