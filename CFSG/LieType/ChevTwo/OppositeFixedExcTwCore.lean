module

public import CFSG.LieType.ChevTwo.OppositeFixedExcTwisted
public import CFSG.LieType.ChevTwo.OppositeFixedExcWrap

public section

namespace CFSG.LieType.ChevTwo.Semi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.EvenOddRadical CFSG.Open CFSG.LieType.BorelTits

variable {K : Type} [Field K]

section Cert


variable (σ₀ : RingAut K)

noncomputable abbrev C0 : Subgroup (ModGL TwistTag.E6.tag K) :=
  graphFixedRootGroup TwistTag.E6 K (σ₀ : K →+* K)

@[expose] noncomputable def rad0 (J : Set (Fin TwistTag.E6.foldedTag.rank)) : Subgroup ↥(C0 σ₀) :=
  (graphFixedParabolicRadical TwistTag.E6 K (σ₀ : K →+* K) J).subgroupOf (C0 σ₀)

@[expose] noncomputable def par0 (J : Set (Fin TwistTag.E6.foldedTag.rank)) : Subgroup ↥(C0 σ₀) :=
  (graphFixedParabolic TwistTag.E6 K (σ₀ : K →+* K) J).subgroupOf (C0 σ₀)

variable {σ₀}

theorem fieldAut_mem_C0 (hσ₀c : ∀ δ : RingAut K, δ * σ₀ = σ₀ * δ) (δ : RingAut K)
    {g : ModGL TwistTag.E6.tag K} (hg : g ∈ C0 σ₀) : fieldAutHom _ K δ g ∈ C0 σ₀ := by
  have hle : C0 σ₀ ≤ (C0 σ₀).comap (fieldAutHom TwistTag.E6.tag K δ).toMonoidHom := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨hxU, hxΓ⟩ := Subgroup.mem_inf.1 hx
      exact Subgroup.mem_sup_left (Subgroup.mem_inf.2
        ⟨entrywise_mem_rootSpan (σ := δ) hxU,
          fieldAut_mem_twistedFixedGroup _ σ₀ δ (hσ₀c δ) hxΓ⟩)
    · obtain ⟨hxU, hxΓ⟩ := Subgroup.mem_inf.1 hx
      exact Subgroup.mem_sup_right (Subgroup.mem_inf.2
        ⟨entrywise_mem_rootSpan (σ := δ) hxU,
          fieldAut_mem_twistedFixedGroup _ σ₀ δ (hσ₀c δ) hxΓ⟩)
  exact hle hg

theorem graphFixedParabolic_le (J : Set (Fin TwistTag.E6.foldedTag.rank))
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ graphFixedParabolic TwistTag.E6 K (σ₀ : K →+* K) J) :
    x ∈ parabolicSubgroup TwistTag.E6.tag K (TwistTag.E6.orbitUnion J) ⊓
      twistedFixedGroup TwistTag.E6 K (σ₀ : K →+* K) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hdec₀, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 K σ₀ J
  obtain ⟨qm, ⟨hq, hm, hxqm⟩, -⟩ := hdec₀ x hx
  obtain ⟨hQAP, -, -, hMAP, -⟩ := parabolic_root_radical_Levi_factors TwistTag.E6.tag K
    (TwistTag.E6.orbitUnion J)
  have hqΓ : qm.1 ∈ twistedFixedGroup TwistTag.E6 K (σ₀ : K →+* K) := (Subgroup.mem_inf.1 hq).2
  have hmΓ : qm.2 ∈ twistedFixedGroup TwistTag.E6 K (σ₀ : K →+* K) :=
    graphFixedRootGroup_le TwistTag.E6 K (σ₀ : K →+* K) (Subgroup.mem_inf.1 hm).2
  rw [hxqm]
  exact Subgroup.mem_inf.2 ⟨mul_mem (hQAP (Subgroup.mem_inf.1 hq).1)
    (hMAP (Subgroup.mem_inf.1 hm).1), mul_mem hqΓ hmΓ⟩

variable (σ₀) in
@[expose] def UniqueNormalFormTw (R : Subgroup (MulAut ↥(C0 σ₀))) : Prop :=
  ∀ α ∈ R, ∃! gδ : ↥(C0 σ₀) × RingAut K,
    ∀ h : ↥(C0 σ₀), ((α h : ↥(C0 σ₀)) : ModGL TwistTag.E6.tag K) =
      (gδ.1 : ModGL TwistTag.E6.tag K) *
        Units.map (entrywiseHom (gδ.2 : K →+* K)) (h : ModGL TwistTag.E6.tag K) *
          (gδ.1 : ModGL TwistTag.E6.tag K)⁻¹

section LiftTw

variable {R : Subgroup (MulAut ↥(C0 σ₀))} (hNF : UniqueNormalFormTw σ₀ R)

@[expose] noncomputable def liftTw (α : ↥R) : GamL TwistTag.E6.tag K :=
  ⟨((hNF α.1 α.2).choose.1 : ModGL TwistTag.E6.tag K), (hNF α.1 α.2).choose.2⟩

theorem liftTw_left_mem (α : ↥R) : (liftTw hNF α).left ∈ C0 σ₀ :=
  (hNF α.1 α.2).choose.1.2

theorem liftTw_spec (α : ↥R) (h : ↥(C0 σ₀)) :
    ((α.1 h : ↥(C0 σ₀)) : ModGL TwistTag.E6.tag K) =
      conjAct TwistTag.E6.tag K (liftTw hNF α) (h : ModGL TwistTag.E6.tag K) := by
  rw [conjAct_apply]
  exact (hNF α.1 α.2).choose_spec.1 h

theorem liftTw_unique (α : ↥R) (g : GamL TwistTag.E6.tag K) (hg : g.left ∈ C0 σ₀)
    (hspec : ∀ h : ↥(C0 σ₀), ((α.1 h : ↥(C0 σ₀)) : ModGL TwistTag.E6.tag K) =
      conjAct TwistTag.E6.tag K g (h : ModGL TwistTag.E6.tag K)) :
    liftTw hNF α = g := by
  have h : (hNF α.1 α.2).choose = ((⟨g.left, hg⟩ : ↥(C0 σ₀)), g.right) :=
    (hNF α.1 α.2).unique (hNF α.1 α.2).choose_spec.1 (fun h => by
      rw [hspec h, conjAct_apply])
  refine SemidirectProduct.ext ?_ ?_
  · exact congrArg (fun p : ↥(C0 σ₀) × RingAut K => (p.1 : ModGL TwistTag.E6.tag K)) h
  · exact congrArg (fun p : ↥(C0 σ₀) × RingAut K => p.2) h

theorem liftTw_one : liftTw hNF 1 = 1 :=
  liftTw_unique hNF 1 1 (one_mem _) fun h => by
    rw [Subgroup.coe_one, map_one, MulAut.one_apply]
    rfl

theorem liftTw_mul (hσ₀c : ∀ δ : RingAut K, δ * σ₀ = σ₀ * δ) (α β : ↥R) :
    liftTw hNF (α * β) = liftTw hNF α * liftTw hNF β := by
  refine liftTw_unique hNF _ _ ?_ fun h => ?_
  · change (liftTw hNF α).left * fieldAutHom _ K (liftTw hNF α).right (liftTw hNF β).left ∈ _
    exact mul_mem (liftTw_left_mem hNF α)
      (fieldAut_mem_C0 hσ₀c _ (liftTw_left_mem hNF β))
  · rw [Subgroup.coe_mul, MulAut.mul_apply, liftTw_spec hNF α, liftTw_spec hNF β, map_mul,
      MulAut.mul_apply]

@[expose] noncomputable def liftHomTw (hσ₀c : ∀ δ : RingAut K, δ * σ₀ = σ₀ * δ) :
    ↥R →* GamL TwistTag.E6.tag K where
  toFun := liftTw hNF
  map_one' := liftTw_one hNF
  map_mul' := liftTw_mul hNF hσ₀c

theorem liftHomTw_injective (hσ₀c : ∀ δ : RingAut K, δ * σ₀ = σ₀ * δ) :
    Function.Injective (liftHomTw hNF hσ₀c) := fun α β h => by
  refine Subtype.ext (MulEquiv.ext fun x => Subtype.ext ?_)
  rw [liftTw_spec hNF α, liftTw_spec hNF β]
  exact congrArg (fun s => conjAct TwistTag.E6.tag K s (x : ModGL TwistTag.E6.tag K)) h

end LiftTw

theorem autCentralizer_inf_rad0_eq_bot [Finite K] [CharP K 2]
    (hσ₀ : ∀ c, σ₀ (σ₀ c) = c) (hσ₀c : ∀ δ : RingAut K, δ * σ₀ = σ₀ * δ)
    (J : Set (Fin TwistTag.E6.foldedTag.rank)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R : Subgroup (MulAut ↥(C0 σ₀))} (hR : IsPGroup p R) (hNF : UniqueNormalFormTw σ₀ R)
    (hQR : ∀ α ∈ R, (rad0 σ₀ J).map α.toMonoidHom = rad0 σ₀ J)
    (hNQ : Subgroup.normalizer ((rad0 σ₀ J : Subgroup ↥(C0 σ₀)) : Set ↥(C0 σ₀)) = par0 σ₀ J)
    (hC : autCentralizer R ≤ par0 σ₀ J) :
    autCentralizer R ⊓ rad0 σ₀ J = ⊥ := by
  classical
  have hfinM : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Fact p.Prime := ⟨hp⟩
  by_contra hne
  obtain ⟨⟨w₁, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  obtain ⟨hwC, hwQ⟩ := Subgroup.mem_inf.1 hw
  have hw1' : (w₁ : ModGL TwistTag.E6.tag K) ≠ 1 := fun h => hw1 (Subtype.ext (Subtype.ext h))
  obtain ⟨-, -, -, -, -, -, hQM, hdecP, hQ₀P, hQ₀n, hL₀P, hdec₀, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 K σ₀ J
  obtain ⟨hQAP, -, -, hMAP, -⟩ := parabolic_root_radical_Levi_factors TwistTag.E6.tag K
    (TwistTag.E6.orbitUnion J)
  set A := TwistTag.E6.orbitUnion J with hA
  set F : ModGL TwistTag.E6.tag K →* ModGL TwistTag.E6.tag K :=
    twistHom TwistTag.E6 K (σ₀ : K →+* K) with hF
  set T : Subgroup (GamL TwistTag.E6.tag K) := (liftHomTw hNF hσ₀c).range with hT
  have hTcard : Nat.card T = Nat.card R :=
    (Nat.card_congr (MonoidHom.ofInjective (liftHomTw_injective hNF hσ₀c)).toEquiv).symm
  have hRodd : Nat.card R % 2 = 1 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hR
    rw [hk]
    exact Nat.odd_iff.1 ((hp.eq_two_or_odd'.resolve_left hp2).pow)
  have hTodd : ¬ 2 ∣ Nat.card T := by
    rw [hTcard]; exact Nat.two_dvd_ne_zero.2 hRodd
  have hQ₀le : ∀ x ∈ graphFixedParabolicRadical TwistTag.E6 K (σ₀ : K →+* K) J,
      x ∈ parabolicRadical TwistTag.E6.tag K A ∧
        x ∈ twistedFixedGroup TwistTag.E6 K (σ₀ : K →+* K) := fun x hx => Subgroup.mem_inf.1 hx
  have hTP : ∀ s ∈ T, s.left ∈ parabolicSubgroup TwistTag.E6.tag K A ⊓
      twistedFixedGroup TwistTag.E6 K (σ₀ : K →+* K) := by
    rintro _ ⟨α, rfl⟩
    have hmem := left_mem_normalizer (Cg := C0 σ₀)
      (Qg := graphFixedParabolicRadical TwistTag.E6 K (σ₀ : K →+* K) J)
      (fun δ h hh => fieldAut_mem_C0 hσ₀c δ hh)
      (fun δ h hh => Subgroup.mem_inf.2 ⟨fieldAut_mem_parabolicRadical δ (hQ₀le h hh).1,
        fieldAut_mem_twistedFixedGroup _ σ₀ δ (hσ₀c δ) (hQ₀le h hh).2⟩)
      (hQR α.1 α.2) (liftTw_left_mem hNF α) (liftTw_spec hNF α)
    have hmem' := hNQ ▸ hmem
    exact graphFixedParabolic_le J (Subgroup.mem_subgroupOf.1 hmem')
  obtain ⟨y₀, hy₀, hyM⟩ := exists_conj_into_complement
    (parabolicSubgroup TwistTag.E6.tag K A ⊓ twistedFixedGroup TwistTag.E6 K (σ₀ : K →+* K))
    (graphFixedParabolicRadical TwistTag.E6 K (σ₀ : K →+* K) J)
    (parabolicLevi TwistTag.E6.tag K A ⊓ twistedFixedGroup TwistTag.E6 K (σ₀ : K →+* K))
    ((isPGroup_posUnipotent 2 TwistTag.E6.tag).to_le
      (inf_le_left.trans (parabolicRadical_le_posUnipotent A)))
    (fun x hx => Subgroup.mem_inf.2 ⟨hQAP (Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩)
    (fun x hx y hy => Subgroup.mem_inf.2 ⟨
      (Subgroup.mem_normalizer_iff.1 (parabolicSubgroup_le_normalizer_parabolicRadical A
        (Subgroup.mem_inf.1 hx).1) y).1 (Subgroup.mem_inf.1 hy).1,
      mul_mem (mul_mem (Subgroup.mem_inf.1 hx).2 (Subgroup.mem_inf.1 hy).2)
        (inv_mem (Subgroup.mem_inf.1 hx).2)⟩)
    (fun δ h hh => Subgroup.mem_inf.2 ⟨fieldAut_mem_parabolicSubgroup δ (Subgroup.mem_inf.1 hh).1,
      fieldAut_mem_twistedFixedGroup _ σ₀ δ (hσ₀c δ) (Subgroup.mem_inf.1 hh).2⟩)
    (fun δ h hh => Subgroup.mem_inf.2 ⟨fieldAut_mem_parabolicLevi δ (Subgroup.mem_inf.1 hh).1,
      fieldAut_mem_twistedFixedGroup _ σ₀ δ (hσ₀c δ) (Subgroup.mem_inf.1 hh).2⟩)
    (fun δ h hh => Subgroup.mem_inf.2 ⟨fieldAut_mem_parabolicRadical δ (Subgroup.mem_inf.1 hh).1,
      fieldAut_mem_twistedFixedGroup _ σ₀ δ (hσ₀c δ) (Subgroup.mem_inf.1 hh).2⟩)
    hQM
    (fun g hg => by
      obtain ⟨qm, ⟨hq, hm, hx⟩, -⟩ := hdecP g hg
      exact ⟨qm.1, hq, qm.2, hm, hx.symm⟩)
    hTP hTodd
  set y : GamL TwistTag.E6.tag K := SemidirectProduct.inl y₀ with hy
  set S : Subgroup (GamL TwistTag.E6.tag K) := T.map (MulAut.conj y).toMonoidHom with hS
  have hSM : ∀ s ∈ S, s.left ∈ parabolicLevi TwistTag.E6.tag K A ⊓
      twistedFixedGroup TwistTag.E6 K (σ₀ : K →+* K) := by
    rintro _ ⟨s, hs, rfl⟩
    exact hyM s hs
  have hSodd : Odd (Nat.card S) := by
    rw [hS, Subgroup.card_map_of_injective (MulAut.conj y).injective, hTcard]
    exact Nat.odd_iff.2 hRodd
  have hconjy : ∀ g : ModGL TwistTag.E6.tag K, conjAct _ K y g = y₀ * g * y₀⁻¹ := fun g => by
    rw [hy, conjAct_inl, MulAut.conj_apply]
  have hconjyinv : ∀ g : ModGL TwistTag.E6.tag K, conjAct _ K y⁻¹ g = y₀⁻¹ * g * y₀ := fun g => by
    rw [map_inv, hy, conjAct_inl, ← map_inv, MulAut.conj_apply, inv_inv]
  have hu : (w₁ : ModGL TwistTag.E6.tag K) ∈ parabolicRadical TwistTag.E6.tag K A :=
    (hQ₀le _ (Subgroup.mem_subgroupOf.1 hwQ)).1
  have hy₀A : y₀ ∈ parabolicRadical TwistTag.E6.tag K A := (hQ₀le _ hy₀).1
  have hy₀P : y₀ ∈ parabolicSubgroup TwistTag.E6.tag K A := hQAP hy₀A
  have hu' : y₀ * (w₁ : ModGL TwistTag.E6.tag K) * y₀⁻¹ ∈ parabolicRadical TwistTag.E6.tag K A :=
    (Subgroup.mem_normalizer_iff.1 (parabolicSubgroup_le_normalizer_parabolicRadical A hy₀P) _).1
      hu
  have hu'1 : y₀ * (w₁ : ModGL TwistTag.E6.tag K) * y₀⁻¹ ≠ 1 := fun h => hw1' (by
    have := congrArg (fun z => y₀⁻¹ * z * y₀) h
    simpa [mul_assoc] using this)
  have hfixT : ∀ s ∈ T, conjAct TwistTag.E6.tag K s (w₁ : ModGL TwistTag.E6.tag K) = w₁ := by
    rintro _ ⟨α, rfl⟩
    change conjAct _ K (liftTw hNF α) _ = _
    rw [← liftTw_spec hNF α, hwC α.1 α.2]
  have hfix : ∀ s ∈ S, conjAct TwistTag.E6.tag K s (y₀ * (w₁ : ModGL TwistTag.E6.tag K) * y₀⁻¹) =
      y₀ * (w₁ : ModGL TwistTag.E6.tag K) * y₀⁻¹ := by
    rintro _ ⟨s, hs, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h1 : conjAct _ K y⁻¹ (y₀ * (w₁ : ModGL TwistTag.E6.tag K) * y₀⁻¹) = w₁ := by
      rw [hconjyinv]; group
    rw [conjAct_conj, h1, hfixT s hs, hconjy]
  obtain ⟨v, hvQ, hv1, hvF, hvfix⟩ := exists_fixed_mem_oppRadical_twisted σ₀ hσ₀ (S := S)
    (fun s hs => (Subgroup.mem_inf.1 (hSM s hs)).1)
    (fun s hs => ⟨((mem_twistedFixedGroup_iff_twistHom _ _ _).1
      (Subgroup.mem_inf.1 (hSM s hs)).2).2, hσ₀c _⟩) hSodd hu' hu'1 hfix
  have hvG : v ∈ adjointGroup TwistTag.E6.tag K := rootSpan_le_adjointGroup K _ hvQ
  have hvC : v ∈ C0 σ₀ := graphFixedNegUnipotent_le_graphFixedRootGroup TwistTag.E6 K
    (σ₀ : K →+* K) (Subgroup.mem_inf.2 ⟨oppRadical_le_negUnipotent A hvQ,
      (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨hvG, hvF⟩⟩)
  have hy₀C : y₀ ∈ C0 σ₀ := graphFixedParabolicRadical_le_graphFixedRootGroup TwistTag.E6 K
    (σ₀ : K →+* K) J hy₀
  have hwC' : y₀⁻¹ * v * y₀ ∈ C0 σ₀ := mul_mem (mul_mem (inv_mem hy₀C) hvC) hy₀C
  have hwfix : ∀ s ∈ T, conjAct TwistTag.E6.tag K s (y₀⁻¹ * v * y₀) = y₀⁻¹ * v * y₀ := by
    intro s hs
    have h := hvfix _ (Subgroup.mem_map_of_mem _ hs)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    rw [conjAct_conj, hconjyinv, hconjy] at h
    calc conjAct TwistTag.E6.tag K s (y₀⁻¹ * v * y₀) =
        y₀⁻¹ * (y₀ * conjAct TwistTag.E6.tag K s (y₀⁻¹ * v * y₀) * y₀⁻¹) * y₀ := by group
      _ = y₀⁻¹ * v * y₀ := by rw [h]
  have hwcent : (⟨y₀⁻¹ * v * y₀, hwC'⟩ : ↥(C0 σ₀)) ∈ autCentralizer R := by
    intro α hα
    refine Subtype.ext ?_
    rw [liftTw_spec hNF ⟨α, hα⟩]
    exact hwfix _ ⟨⟨α, hα⟩, rfl⟩
  have hwP : y₀⁻¹ * v * y₀ ∈ graphFixedParabolic TwistTag.E6 K (σ₀ : K →+* K) J :=
    Subgroup.mem_subgroupOf.1 (hC hwcent)
  have hwPA := (graphFixedParabolic_le J hwP).1
  have hvP : v ∈ parabolicSubgroup TwistTag.E6.tag K A := by
    have e : v = y₀ * (y₀⁻¹ * v * y₀) * y₀⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hy₀P hwPA) (inv_mem hy₀P)
  have h0 := Subgroup.mem_inf.2 ⟨hvP, hvQ⟩
  rw [parabolicSubgroup_inf_oppRadical] at h0
  exact hv1 (Subgroup.mem_bot.1 h0)

theorem oppositeFixed_C0 [Finite K] [CharP K 2]
    (hσ₀ : ∀ c, σ₀ (σ₀ c) = c) (hσ₀c : ∀ δ : RingAut K, δ * σ₀ = σ₀ * δ)
    (hNF : ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ R : Subgroup (MulAut ↥(C0 σ₀)), IsPGroup p R →
      UniqueNormalFormTw σ₀ R) :
    OppositeFixed ↥(C0 σ₀) := by
  classical
  have hfinM : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hσ₀' : σ₀ ^ TwistTag.E6.order = 1 := by
    show σ₀ ^ 2 = 1
    rw [pow_two]
    exact RingEquiv.ext hσ₀
  refine oppositeFixed_of_family (rad0 σ₀) (par0 σ₀) (fun J => ?_) (fun J => ?_) (fun Q hQ0 hQ2 => ?_)
    (fun J p hp hp2 R hR hQR hNQ hC => ?_)
  · have h2 : IsPGroup 2 (graphFixedParabolicRadical TwistTag.E6 K (σ₀ : K →+* K) J) :=
      (isPGroup_posUnipotent 2 TwistTag.E6.tag).to_le
        (inf_le_left.trans (parabolicRadical_le_posUnipotent _))
    exact h2.of_equiv (Subgroup.subgroupOfEquivOfLe
      (graphFixedParabolicRadical_le_graphFixedRootGroup TwistTag.E6 K (σ₀ : K →+* K) J)).symm
  · obtain ⟨-, -, -, -, -, -, -, -, hQ₀P, hQ₀n, -⟩ :=
      diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 K σ₀ J
    have hPN := (Subgroup.normal_subgroupOf_iff_le_normalizer hQ₀P).1 hQ₀n
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hx' := hPN (Subgroup.mem_subgroupOf.1 hx)
    simp only [rad0, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 hx' _
  · have hQ₀ne : Q.map (C0 σ₀).subtype ≠ ⊥ := fun h =>
      hQ0 ((Subgroup.map_eq_bot_iff_of_injective Q (C0 σ₀).subtype_injective).1 h)
    obtain ⟨g, hg, J, hP, hQJ⟩ := exists_optimal_radical_fixed TwistTag.E6 σ₀ hσ₀'
      (Subgroup.map_subtype_le Q) (hQ2.map (C0 σ₀).subtype) hQ₀ne
    refine ⟨⟨g, hg⟩, J, fun x hx => Subgroup.mem_subgroupOf.2
      (hP x x.2 (mem_normalizer_map_subtype hx)), fun q hq =>
      Subgroup.mem_subgroupOf.2 (hQJ q ⟨q, hq, rfl⟩)⟩
  · exact autCentralizer_inf_rad0_eq_bot hσ₀ hσ₀c J hp hp2 hR (hNF p hp hp2 R hR) hQR hNQ hC

end Cert

end CFSG.LieType.ChevTwo.Semi
