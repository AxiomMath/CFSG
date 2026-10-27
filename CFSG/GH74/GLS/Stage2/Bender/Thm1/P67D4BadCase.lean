module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4BypassAssemble
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4BadAux
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4HexCent
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4LongZ
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4LongGen
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusCent

public section

namespace CFSG.GH74.GLS.SP

open CFSG.GH74.BNPair

section Generic

variable {X : Type*} [Group X] {root : ℤ → Subgroup X}

theorem mem_longSub_cent {z : X}
    (h : ∀ k, IsRoot 6 k → k % 2 = 0 → ∀ x ∈ root k, z * x * z⁻¹ = x) {x : X}
    (hx : x ∈ longSub 6 root) : z * x * z⁻¹ = x := by
  unfold longSub at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, hk2, hxk⟩ := hx
    exact h k hk hk2 x hxk
  | one => simp
  | mul x y _ _ hx hy =>
    have e : z * (x * y) * z⁻¹ = (z * x * z⁻¹) * (z * y * z⁻¹) := by group
    rw [e, hx, hy]
  | inv x _ hx =>
    have e : z * x⁻¹ * z⁻¹ = (z * x * z⁻¹)⁻¹ := by group
    rw [e, hx]

end Generic

end CFSG.GH74.GLS.SP

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.LieType.Steinberg.CentralExt CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.Balance
  CFSG.GH74.GLS.Stage2.OddAut CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem exists_twistedGroup_equiv_fixed {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    ∃ e : twistedGroup σ.toRingHom ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      ∀ x : twistedGroup σ.toRingHom,
        ((e x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
          ((x : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK3
  have h2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hq : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  refine ⟨(Subgroup.equivMapOfInjective (twistedGroup σ.toRingHom) (adjointGroup d4 K).subtype
        Subtype.val_injective).trans
        (MulEquiv.subgroupCongr (TrialityClosed.map_twistedGroup_eq_graphFixedRootGroup h2 hq hK
          (σ := σ.toRingHom) hσ)), fun x => rfl⟩

theorem d4_long_a2_Y {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f))
    (ω : Kˣ) (hωσ : Units.map σ.toRingHom.toMonoidHom ω = ω) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hz : (z : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![ω, ω, 1, ω]) :
    ∃ L U₀ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      L ≤ fixSub (MulAut.conj z) ∧ CFSG.IsQuasisimple ↥L ∧
      (∀ c ∈ fixSub (MulAut.conj z), ∀ x ∈ L, c * x * c⁻¹ ∈ L) ∧
      (∀ c ∈ fixSub (MulAut.conj z), (∀ x ∈ L, c * x = x * c) →
        (c : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom ∧
        (c : ModGL TwistTag.D4.tag K) * ((xPar (rootOperatorFamily d4) ![0, 0, 1, 0] 1 :
          adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
          ((xPar (rootOperatorFamily d4) ![0, 0, 1, 0] 1 : adjointGroup d4 K) :
            ModGL TwistTag.D4.tag K) * (c : ModGL TwistTag.D4.tag K) ∧
        (c : ModGL TwistTag.D4.tag K) * ((xPar (rootOperatorFamily d4) ![1, 1, 1, 1] 1 :
          adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
          ((xPar (rootOperatorFamily d4) ![1, 1, 1, 1] 1 : adjointGroup d4 K) :
            ModGL TwistTag.D4.tag K) * (c : ModGL TwistTag.D4.tag K)) ∧
      U₀ ≤ fixSub (MulAut.conj z) ∧ IsPGroup p U₀ ∧ (p ^ f) ^ 3 ≤ Nat.card U₀ := by
  classical
  obtain ⟨e, he⟩ := exists_twistedGroup_equiv_fixed hp hp2 hf K hK σ hσ
  have hσq : ∀ c, σ.toRingHom c = c ^ (p ^ f) := hσ
  have hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c := sigma_three_of_card hK hσq
  have hωσ' : σ.toRingHom (ω : K) = ω := congrArg Units.val hωσ
  obtain ⟨zX, hzXm, hzXH, hzXl, hzXs⟩ := d4_z_facts hσ3 ω hωσ' hω3 hω1
  have hzz : e zX = z := Subtype.ext (by rw [he, hzXm, hz])
  have hLC : LongCent (d4RGD2 σ.toRingHom hσ3) zX := ⟨hzXH, hzXl, hzXs⟩
  have hgen := d4RGD2_gen hσ3
  have hq2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  have hcenX : Subgroup.center (twistedGroup σ.toRingHom) = ⊥ :=
    TrialityClosed.twistedGroup_center_eq_bot_of_card hq2 hK hσq
  have hZ := RGD2.hZ_of_center_bot (d4RGD2 σ.toRingHom hσ3) hgen hcenX
  obtain ⟨t, htH, htL, htfree⟩ := d4_t0_facts hσ3 ω hωσ' hω3 hω1
  have hfixiff : ∀ c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      c ∈ fixSub (MulAut.conj z) ↔ zX * e.symm c * zX⁻¹ = e.symm c := by
    intro c
    rw [mem_fixSub, MulAut.conj_apply, ← hzz]
    constructor
    · intro h
      apply e.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact h
    · intro h
      have := congrArg e h
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at this
      exact this
  have hcardU : Nat.card ↥(posUnipotent (g2Shape (twistedX σ.toRingHom)) ⊓
      foldFix (MulAut.conj zX)) = (p ^ f) ^ 3 := by
    rw [LongCent.card_fixed_U hLC, d4_card_long hq2 hK hσq (k := 2) (by norm_num) (by norm_num)
      (by norm_num), d4_card_long hq2 hK hσq (k := 4) (by norm_num) (by norm_num)
      (by norm_num), d4_card_long hq2 hK hσq (k := 6) (by norm_num) (by norm_num)
      (by norm_num)]
    ring
  have hcardmap : Nat.card ↥((posUnipotent (g2Shape (twistedX σ.toRingHom)) ⊓
      foldFix (MulAut.conj zX)).map e.toMonoidHom) = (p ^ f) ^ 3 := by
    rw [← hcardU]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).toEquiv).symm
  refine ⟨(longSub 6 (hexGroup (twistedX σ.toRingHom))).map e.toMonoidHom,
    (posUnipotent (g2Shape (twistedX σ.toRingHom)) ⊓ foldFix (MulAut.conj zX)).map
      e.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [hfixiff]
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact mem_longSub_cent hzXl hx
  · exact CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective) (d4_longSub_quasisimple hσ3)
  · intro c hc x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    have hcX := (hfixiff c).1 hc
    refine ⟨_, LongCent.normalizes_longSub hLC hgen hZ hcX hx₀, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, MulEquiv.apply_symm_apply]
  · intro c hc hcL
    have hcX := (hfixiff c).1 hc
    have hcom : ∀ x ∈ longSub 6 (hexGroup (twistedX σ.toRingHom)),
        e.symm c * x = x * e.symm c := by
      intro x hx
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hcL (e x) ⟨x, hx, rfl⟩
    have hcH := LongCent.centralizer_le_H hLC hgen hZ htH htL htfree hcX hcom
    have hcT : (c : ModGL TwistTag.D4.tag K) ∈ torusGroup TwistTag.D4.tag K := by
      have := d4_hHat_le_torus _ hcH
      rwa [← he, MulEquiv.apply_symm_apply] at this
    have hcF : (c : ModGL TwistTag.D4.tag K) ∈
        twistedFixedGroup TwistTag.D4 K σ.toRingHom := graphFixedRootGroup_le _ _ _ c.2
    refine ⟨Subgroup.mem_inf.2 ⟨hcT, hcF⟩, ?_, ?_⟩
    · have hx := d4X_mem_longSub hσ3 0 1
      have h2 := congrArg (fun y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =>
        (y : ModGL TwistTag.D4.tag K)) (hcL (e (d4X hσ3 0 1)) ⟨_, hx, rfl⟩)
      simp only [Subgroup.coe_mul, he] at h2
      exact h2
    · have hx := d4X_mem_longSub hσ3 2 1
      have h2 := congrArg (fun y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =>
        (y : ModGL TwistTag.D4.tag K)) (hcL (e (d4X hσ3 2 1)) ⟨_, hx, rfl⟩)
      simp only [Subgroup.coe_mul, he] at h2
      exact h2
  · rintro _ ⟨x, hx, rfl⟩
    rw [hfixiff]
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    have hx' := (Subgroup.mem_inf.1 hx).2
    exact hx'
  · have : Fact p.Prime := ⟨hp⟩
    exact IsPGroup.of_card (n := 3 * f) (by rw [hcardmap, ← pow_mul, mul_comm])
  · exact hcardmap.ge

theorem d4BadCase_thm : D4BadCase := by
  classical
  intro p f hp hp2 hp3 hf hq K _ _ hK σ hσ V Z h2 h3 v n δ hvT hv1 hv3 hvV hn hnT hδ heV hev
  have hcen : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hVe : IsElementaryAbelian 3 V := h2.2.2.1
  have he3 : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) ^ 3 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian _ heV
  have hW3 := d4_weyl_cube_of_pow_three K hK σ hσ n δ hδ hn he3
  obtain ⟨ω, hωσ, hω3, hω1, hvω⟩ :=
    d4_fixed_line hp hp2 hf hq K hK σ hσ v n δ hvT hv1 hv3 hn hnT hW3 hδ hev
  obtain ⟨L, U₀, hLF, hLqs, hLnorm, hLc, hU, hUp, hUcard⟩ :=
    d4_long_a2_Y hp hp2 hf K hK σ hσ ω hωσ hω3 hω1 v hvω
  have hCL : ∀ c ∈ fixSub (MulAut.conj v), (∀ x ∈ L, c * x = x * c) →
      (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) c = c → c ∈ Subgroup.zpowers v := by
    intro c hc hcL hec
    obtain ⟨hct, hc0, hc2⟩ := hLc c hc hcL
    exact d4_torus_cent_fixed hp hp2 hf hq K hK σ hσ ω hωσ hω3 hω1 v hvω n δ hn hW3 hδ c
      hct hc0 hc2 hec
  have hker := d4_hker_of_data hp hp2 hf K hK σ hσ hv3
    (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) L U₀ hLF hCL hU hUp hUcard
  exact false_of_inner_quasisimple_core hcen h2 h3 hv1 hvV heV L hLF hLqs hLnorm hCL hker

end CFSG.GH74.GLS.Stage2.Bender.Thm1
