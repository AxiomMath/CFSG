module

public import CFSG.LieType.SeitzGeneration.ExcPlaneModel
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Lang.AnisoE6.F4GraphFixed

public noncomputable section

namespace CFSG.HardMathSupport.Lang.AnisoE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
  CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2 CFSG.TauCetiBridge TauCeti

set_option linter.unusedSectionVars false


section Congr

variable {τ : Tag} {K₁ K₂ : Type} [Field K₁] [Field K₂]

theorem baseChangeGL_mem_adjointGroup_of_mem (f : K₁ →+* K₂) {g : ModGL τ K₁}
    (hg : g ∈ adjointGroup τ K₁) : baseChangeGL f g ∈ adjointGroup τ K₂ := by
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, c, h | h⟩ := hy
    · rw [show y = xUnit τ K₁ i c from Units.ext h, baseChangeGL_xUnit]
      exact xUnit_mem_adjointGroup _ _
    · rw [show y = yUnit τ K₁ i c from Units.ext h, baseChangeGL_yUnit]
      exact yUnit_mem_adjointGroup _ _
  | one => simpa using one_mem _
  | mul x y _ _ hx hy => simpa using mul_mem hx hy
  | inv x _ hx => simpa using inv_mem hx

@[expose] def adjointGroupCongr (e : K₁ ≃+* K₂) : adjointGroup τ K₁ ≃* adjointGroup τ K₂ :=
  MulEquiv.ofBijective
    (((baseChangeGL (τ := τ) e.toRingHom).comp (adjointGroup τ K₁).subtype).codRestrict _
      fun g => baseChangeGL_mem_adjointGroup_of_mem e.toRingHom g.2)
    ⟨fun g g' h => Subtype.ext (baseChangeGL_injective e.toRingHom (congrArg Subtype.val h)),
      fun y => by
        have hle : adjointGroup τ K₂ ≤ (adjointGroup τ K₁).map (baseChangeGL (τ := τ) e.toRingHom) := by
          refine (Subgroup.closure_le _).2 ?_
          rintro g ⟨i, c, h | h⟩
          · refine ⟨xUnit τ K₁ i (e.symm c), xUnit_mem_adjointGroup _ _, ?_⟩
            rw [baseChangeGL_xUnit, show g = xUnit τ K₂ i c from Units.ext h]
            simp
          · refine ⟨yUnit τ K₁ i (e.symm c), yUnit_mem_adjointGroup _ _, ?_⟩
            rw [baseChangeGL_yUnit, show g = yUnit τ K₂ i c from Units.ext h]
            simp
        obtain ⟨x, hx, hxy⟩ := hle y.2
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

end Congr

section Gamma

variable {K : Type} [Field K]

theorem e6_perm_perm (i : Fin TwistTag.E6.tag.rank) :
    TwistTag.E6.perm (TwistTag.E6.perm i) = i := by
  revert i
  decide

theorem twistHom_id_twistHom_id {g : ModGL TwistTag.E6.tag K} (hg : g ∈ adjointGroup TwistTag.E6.tag K) :
    twistHom TwistTag.E6 K (RingHom.id K) (twistHom TwistTag.E6 K (RingHom.id K) g) = g := by
  have hle : adjointGroup TwistTag.E6.tag K ≤
      MonoidHom.eqLocus ((twistHom TwistTag.E6 K (RingHom.id K)).comp
        (twistHom TwistTag.E6 K (RingHom.id K))) (MonoidHom.id _) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨i, c, h | h⟩
    · rw [show g = xUnit _ K i c from Units.ext h]
      change twistHom TwistTag.E6 K (RingHom.id K)
        (twistHom TwistTag.E6 K (RingHom.id K) (xUnit _ K i c)) = xUnit _ K i c
      rw [twistHom_xUnit, twistHom_xUnit, e6_perm_perm]
      rfl
    · rw [show g = yUnit _ K i c from Units.ext h]
      change twistHom TwistTag.E6 K (RingHom.id K)
        (twistHom TwistTag.E6 K (RingHom.id K) (yUnit _ K i c)) = yUnit _ K i c
      rw [twistHom_yUnit, twistHom_yUnit, e6_perm_perm]
      rfl
  exact hle hg

variable (K) in
@[expose] def graphAut : MulAut (adjointGroup TwistTag.E6.tag K) where
  toFun g := twistC TwistTag.E6 K (RingHom.id K) g
  invFun g := twistC TwistTag.E6 K (RingHom.id K) g
  left_inv g := Subtype.ext (twistHom_id_twistHom_id g.2)
  right_inv g := Subtype.ext (twistHom_id_twistHom_id g.2)
  map_mul' _ _ := map_mul _ _ _

theorem graphAut_fixed_iff (g : adjointGroup TwistTag.E6.tag K) :
    graphAut K g = g ↔
      (g : ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K) :=
  (coe_mem_twistedFixedGroup_iff TwistTag.E6 K (RingHom.id K) g).symm

end Gamma

section Cat


theorem exists_f4_fixed_in_e6_field (K : Type) [Field K] :
    ∃ (H : Subgroup (adjointGroup TwistTag.E6.tag K)) (_ : adjointGroup Tag.F4 K ≃* H)
      (γ : MulAut (adjointGroup TwistTag.E6.tag K)), ∀ g, g ∈ H ↔ γ g = g := by
  have hle := twistedFixedGroup_le_adjointGroup TwistTag.E6 K (RingHom.id K)
  refine ⟨(twistedFixedGroup TwistTag.E6 K (RingHom.id K)).subgroupOf _,
    (e6FixedF4EquivAll K).symm.trans (Subgroup.subgroupOfEquivOfLe hle).symm, graphAut K,
    fun g => ?_⟩
  rw [graphAut_fixed_iff]
  rfl

theorem exists_f4_fixed_in_e6 (q : PrimePower) (hvE : (LieTypeIndex.E6 q).Valid)
    (hvF : (LieTypeIndex.F4 q).Valid) :
    ∃ (H : Subgroup (Cat ⟨.E6 q, hvE⟩)) (_ : Cat ⟨.F4 q, hvF⟩ ≃* H)
      (γ : MulAut (Cat ⟨.E6 q, hvE⟩)), ∀ g, g ∈ H ↔ γ g = g := by
  obtain ⟨K₂, _, _, hK₂, -, ⟨eE⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hvE
  obtain ⟨K₁, _, _, hK₁, -, ⟨eF⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hvF
  haveI : Finite K₁ := Nat.finite_of_card_ne_zero (by rw [hK₁, PrimePower.card_def]; exact pow_ne_zero _ q.prime_p.ne_zero)
  haveI : Finite K₂ := Nat.finite_of_card_ne_zero (by rw [hK₂, PrimePower.card_def]; exact pow_ne_zero _ q.prime_p.ne_zero)
  haveI : Fintype K₁ := Fintype.ofFinite K₁
  haveI : Fintype K₂ := Fintype.ofFinite K₂
  have hcard : Fintype.card K₁ = Fintype.card K₂ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK₁, hK₂]
  obtain ⟨H₀, φ₀, γ₀, hγ₀⟩ := exists_f4_fixed_in_e6_field K₂
  let H : Subgroup (adjointGroup Tag.E6 K₂) := H₀
  let φ : adjointGroup Tag.F4 K₂ ≃* H := φ₀
  let γ : MulAut (adjointGroup Tag.E6 K₂) := γ₀
  have hγ : ∀ g, g ∈ H ↔ γ g = g := hγ₀
  let ψ : Cat ⟨.F4 q, hvF⟩ ≃* adjointGroup Tag.F4 K₂ :=
    eF.trans (adjointGroupCongr (FiniteField.ringEquivOfCardEq hcard))
  have key : ∀ g, g ∈ H.map eE.symm.toMonoidHom ↔ eE g ∈ H := fun g => by
    rw [Subgroup.mem_map_equiv]
    rfl
  refine ⟨H.map eE.symm.toMonoidHom, ψ.trans (φ.trans (MulEquiv.subgroupMap eE.symm H)),
    MulAut.congr eE.symm γ, fun g => ?_⟩
  rw [key, hγ]
  constructor
  · intro h
    have := congrArg eE.symm h
    simpa using this
  · intro h
    simpa using congrArg eE h

end Cat

end CFSG.HardMathSupport.Lang.AnisoE6
