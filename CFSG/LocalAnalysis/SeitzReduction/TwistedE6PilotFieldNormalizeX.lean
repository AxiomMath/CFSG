module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldNormalize
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotNeighbourParamLift
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldNormalizeBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.LieType.Chevalley.E6GraphLevi (realize unitarySL unitaryTwist)
open scoped commutatorElement

section Realize

variable {K : Type} [Field K]

@[expose] noncomputable def realizeA (h2 : (2 : K) = 0) :
    SpecialLinearGroup (Fin 6) K →* subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA :=
  (realize h2).codRestrict _ fun B => by
    rw [← E6GraphLevi.range_realize h2]
    exact ⟨B, rfl⟩

theorem realizeA_surjective (h2 : (2 : K) = 0) : Function.Surjective (realizeA h2) := by
  rintro ⟨g, hg⟩
  rw [← E6GraphLevi.range_realize h2] at hg
  obtain ⟨B, rfl⟩ := hg
  exact ⟨B, rfl⟩

theorem ker_realizeA_le_center (h2 : (2 : K) = 0) :
    (realizeA h2).ker ≤ center (SpecialLinearGroup (Fin 6) K) := by
  intro B hB
  have hB' : B ∈ (realize h2).ker := by
    rw [MonoidHom.mem_ker] at hB ⊢
    exact congrArg Subtype.val hB
  obtain ⟨l, -, hl⟩ := (E6GraphLevi.mem_ker_realize h2 B).1 hB'
  rw [mem_center_iff]
  intro A
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hl]
  exact congrFun (congrFun (Matrix.scalar_commute l (fun r' => Commute.all l r')
    (A : Matrix (Fin 6) (Fin 6) K)).symm.eq i) j

theorem exists_surjective_lift_realizeA [Finite K] (h2 : (2 : K) = 0) {E : Type*} [Group E]
    [Group.IsPerfect E] {p : E →* subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA}
    (hp : Function.Surjective p) (hpker : p.ker ≤ center E) :
    ∃ Φ₀ : SpecialLinearGroup (Fin 6) K →* E, (∀ B, p (Φ₀ B) = realizeA h2 B) ∧
      Function.Surjective Φ₀ ∧ Φ₀.ker ≤ center (SpecialLinearGroup (Fin 6) K) := by
  obtain ⟨s, hs⟩ := UnitaryPilot.exists_section_specialLinear_of_five_le (m := 6) (by norm_num)
    (Or.inr (by norm_num))
    (CFSG.LieType.Steinberg.pullbackFst_surjective (β := realizeA h2) hp)
    (CFSG.LieType.Steinberg.ker_pullbackFst_le_center hpker)
  let Φ : SpecialLinearGroup (Fin 6) K →* E :=
    ((MonoidHom.snd _ E).comp
      (CFSG.LieType.Steinberg.pullback (realizeA h2) p).subtype).comp s
  have hΦ : ∀ B, p (Φ B) = realizeA h2 B := fun B => by
    have hmem := CFSG.LieType.Steinberg.mem_pullback.1 (s B).2
    have h1 : ((s B : CFSG.LieType.Steinberg.pullback (realizeA h2) p) :
        SpecialLinearGroup (Fin 6) K × E).1 = B := hs B
    change p ((s B : CFSG.LieType.Steinberg.pullback (realizeA h2) p) :
      SpecialLinearGroup (Fin 6) K × E).2 = _
    rw [← hmem, h1]
  refine ⟨Φ, hΦ, ?_, ?_⟩
  · have hdecomp : ∀ y : E, ∃ x, y * (Φ x)⁻¹ ∈ center E := fun y => by
      obtain ⟨x, hx⟩ := realizeA_surjective h2 (p y)
      exact ⟨x, hpker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hΦ, hx, mul_inv_cancel])⟩
    have hcomm : commutator E ≤ Φ.range := by
      rw [commutator_def, Subgroup.commutator_le]
      intro y _ z _
      obtain ⟨x, hx⟩ := hdecomp y
      obtain ⟨x', hx'⟩ := hdecomp z
      have e : ⁅y, z⁆ = ⁅Φ x, Φ x'⁆ := by
        have h := CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center hx hx' (Φ x)
          (Φ x')
        rwa [inv_mul_cancel_right, inv_mul_cancel_right] at h
      rw [e, ← map_commutatorElement]
      exact ⟨_, rfl⟩
    intro y
    exact hcomm (by rw [Group.IsPerfect.commutator_eq_top]; exact mem_top y)
  · intro x hx
    have h1 : realizeA h2 x = 1 := by rw [← hΦ, MonoidHom.mem_ker.1 hx, map_one]
    exact ker_realizeA_le_center h2 h1

end Realize

section Cover

variable {K : Type} [Field K]
  {G : Type} [Group G] {L : Subgroup G}

structure FieldCoverParamX (σ : K →+* K) (h2 : (2 : K) = 0)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (t : G) (X : Subgroup G) where
  Φ : SpecialLinearGroup (Fin 6) K →* G
  range_eq : Φ.range = centralizerPerfectCore X
  ker_le : Φ.ker ≤ center (SpecialLinearGroup (Fin 6) K)
  N1 : ∀ B : SpecialLinearGroup (Fin 6) K, B ∈ unitarySL σ →
    ∀ hC : realize h2 B ∈ graphFixedRootGroup TwistTag.E6 K σ,
      Φ B = ((e.symm ⟨realize h2 B, hC⟩ : L) : G)
  N3 : ∀ B : SpecialLinearGroup (Fin 6) K, t * Φ B * t⁻¹ = Φ (unitaryTwist σ B)

variable
  {f : ℕ}

theorem realize_mem_C0_of_mem_unitarySL (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (h2 : (2 : K) = 0)
    {B : SpecialLinearGroup (Fin 6) K} (hB : B ∈ unitarySL σ) :
    realize h2 B ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (E6GraphLevi.subsystemGroup_inf_eq_map_realize hK hσ h2).2.2 ⟨B, hB, rfl⟩

theorem realize_mem_su6Levi_of_mem_unitarySL (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (h2 : (2 : K) = 0)
    {B : SpecialLinearGroup (Fin 6) K} (hB : B ∈ unitarySL σ) : realize h2 B ∈ su6Levi σ :=
  ⟨(realizeA h2 B).2, realize_mem_C0_of_mem_unitarySL hf hK hσ h2 hB⟩

theorem nonempty_fieldCoverParamX_of_proj [Finite G] (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (h2 : (2 : K) = 0) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G} {X : Subgroup G}
    (ht : t ∈ normalizer (centralizerPerfectCore X : Set G))
    (hD : ∀ y : graphFixedRootGroup TwistTag.E6 K σ, (y : ModGL TwistTag.E6.tag K) ∈ su6Levi σ →
      ((e.symm y : L) : G) ∈ centralizerPerfectCore X)
    {p : centralizerPerfectCore X →* subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA}
    (hp : Function.Surjective p) (hpker : p.ker ≤ center (centralizerPerfectCore X))
    (h1 : ∀ (y : graphFixedRootGroup TwistTag.E6 K σ) (hy : (y : ModGL TwistTag.E6.tag K) ∈ su6Levi σ),
      p ⟨((e.symm y : L) : G), hD y hy⟩ = ⟨y, hy.1⟩)
    (h3 : ∀ x, p ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, ht⟩ x) =
      a5LeviTwist (apply_apply_eq hK hσ) (p x)) :
    Nonempty (FieldCoverParamX σ h2 e t X) := by
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  have : Group.IsPerfect (centralizerPerfectCore X) :=
    Subgroup.isPerfect_iff.mpr (F4Pilot.commutator_centralizerPerfectCore X)
  have : Group.IsPerfect (SpecialLinearGroup (Fin 6) K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  have : Group.IsPerfect (unitarySL σ) := E6GraphLevi.isPerfect_unitarySL hK hσ
  obtain ⟨Φ₀, hΦ₀, hsurj, hker⟩ := exists_surjective_lift_realizeA h2 hp hpker
  let κ : unitarySL σ →* graphFixedRootGroup TwistTag.E6 K σ :=
    { toFun := fun B => ⟨realize h2 B, realize_mem_C0_of_mem_unitarySL hf hK hσ h2 B.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _) }
  let ψ₂ : unitarySL σ →* centralizerPerfectCore X :=
    (L.subtype.comp (e.symm.toMonoidHom.comp κ)).codRestrict _ fun B =>
      hD (κ B) (realize_mem_su6Levi_of_mem_unitarySL hf hK hσ h2 B.2)
  have hψ : Φ₀.comp (unitarySL σ).subtype = ψ₂ :=
    LinearPilot.eq_of_comp_eq_of_ker_le_center hpker fun B => by
      rw [MonoidHom.comp_apply, hΦ₀]
      have hp2 : p (ψ₂ B) = ⟨κ B, (realizeA h2 B).2⟩ :=
        h1 (κ B) (realize_mem_su6Levi_of_mem_unitarySL hf hK hσ h2 B.2)
      rw [hp2]
      rfl
  have hτ : ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, ht⟩).toMonoidHom.comp Φ₀ =
      Φ₀.comp (unitaryTwist σ) :=
    LinearPilot.eq_of_comp_eq_of_ker_le_center hpker fun B => by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h3, hΦ₀, hΦ₀]
      apply Subtype.ext
      exact E6GraphLevi.twistHom_realize σ h2 B
  refine ⟨⟨(centralizerPerfectCore X).subtype.comp Φ₀, ?_, ?_, fun B hB hC => ?_, fun B => ?_⟩⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hsurj, ← MonoidHom.range_eq_map,
      range_subtype]
  · intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact Subtype.ext hx
  · have h := congrArg (fun ψ : unitarySL σ →* centralizerPerfectCore X => ((ψ ⟨B, hB⟩ : _) : G)) hψ
    exact h
  · have h := congrArg (fun ψ : SpecialLinearGroup (Fin 6) K →* centralizerPerfectCore X =>
      ((ψ B : _) : G)) hτ
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.normalizerMonoidHom_apply_apply_coe] at h
    exact h

theorem nonempty_fieldCoverParamX_of_normalized [Finite G] (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (h2 : (2 : K) = 0) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G} {X : Subgroup G}
    (htX : t ∈ centralizer (X : Set G))
    (hD : ∀ y : graphFixedRootGroup TwistTag.E6 K σ, (y : ModGL TwistTag.E6.tag K) ∈ su6Levi σ →
      ((e.symm y : L) : G) ∈ centralizerPerfectCore X)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    {q : centralizerPerfectCore X →* Kc} (hq : Function.Surjective q)
    (hqker : q.ker ≤ center (centralizerPerfectCore X))
    (hqapp : ∀ y : centralizerPerfectCore X, (q y : centralizer (X : Set G) ⧸
      oddCore (centralizer (X : Set G))) = QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
        ⟨(y : G), F4Pilot.centralizerPerfectCore_le_centralizer X y.2⟩)
    (Ψ : subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ≃* Kc)
    (hΨ1 : ∀ (y : graphFixedRootGroup TwistTag.E6 K σ) (hy : (y : ModGL TwistTag.E6.tag K) ∈ su6Levi σ),
      (Ψ ⟨y, hy.1⟩ : centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))) =
        QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
          ⟨((e.symm y : L) : G), F4Pilot.centralizerPerfectCore_le_centralizer X (hD y hy)⟩)
    (hΨ3 : ∀ x, Ψ (a5LeviTwist (apply_apply_eq hK hσ) x) =
      Kc.normalizerMonoidHom ⟨_, hsN⟩ (Ψ x)) :
    Nonempty (FieldCoverParamX σ h2 e t X) := by
  have hN : t ∈ normalizer (centralizerPerfectCore X : Set G) :=
    F4Pilot.normalizer_le_normalizer_centralizerPerfectCore X
      (Subgroup.centralizer_le_normalizer _ htX)
  set p := Ψ.symm.toMonoidHom.comp q with hpdef
  refine nonempty_fieldCoverParamX_of_proj hf hK hσ h2 e hN hD (p := p)
    (Ψ.symm.surjective.comp hq) ?_ ?_ ?_
  · intro x hx
    apply hqker
    rw [MonoidHom.mem_ker] at hx ⊢
    have h1 : Ψ.symm (q x) = Ψ.symm 1 := by rw [map_one]; exact hx
    exact Ψ.symm.injective h1
  · intro y hy
    have h1 : q ⟨((e.symm y : L) : G), hD y hy⟩ = Ψ ⟨y, hy.1⟩ := Subtype.ext (by
      rw [hqapp, hΨ1 y hy])
    change Ψ.symm (q _) = _
    rw [h1, MulEquiv.symm_apply_apply]
  · intro x
    have h1 : q ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ x) =
        Kc.normalizerMonoidHom ⟨_, hsN⟩ (q x) := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hqapp, hqapp]
      have e1 : (⟨(((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ x :
          centralizerPerfectCore X) : G), F4Pilot.centralizerPerfectCore_le_centralizer X
            ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ x).2⟩ :
              centralizer (X : Set G)) =
          ⟨t, htX⟩ * ⟨(x : G), F4Pilot.centralizerPerfectCore_le_centralizer X x.2⟩ *
            ⟨t, htX⟩⁻¹ := by
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        rfl
      rw [e1, map_mul, map_mul, map_inv]
    change Ψ.symm (q _) = a5LeviTwist (apply_apply_eq hK hσ) (Ψ.symm (q x))
    rw [h1]
    apply Ψ.injective
    rw [MulEquiv.apply_symm_apply, hΨ3, MulEquiv.apply_symm_apply]

theorem exists_normalized_a5Levi_mulEquiv [Finite G] (hf : 1 ≤ f) {k : Type} [Field k]
    [Algebra k K] (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    {X : Subgroup G} (htX : t ∈ centralizer (X : Set G)) (ht2 : orderOf t = 2)
    (hDX : ∀ y : graphFixedRootGroup TwistTag.E6 K σ, (y : ModGL TwistTag.E6.tag K) ∈ su6Levi σ →
      ((e.symm y : L) : G) ∈ centralizer (X : Set G))
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hDK : ∀ (y : graphFixedRootGroup TwistTag.E6 K σ) (hy : (y : ModGL TwistTag.E6.tag K) ∈ su6Levi σ),
      QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨((e.symm y : L) : G), hDX y hy⟩ ∈ Kc)
    (hDne : ∃ (y : graphFixedRootGroup TwistTag.E6 K σ) (hy : (y : ModGL TwistTag.E6.tag K) ∈ su6Levi σ),
      QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨((e.symm y : L) : G), hDX y hy⟩ ≠ 1)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hcore : ∀ z : Kc, z ∈ perfectCore (fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩)) ↔
      ∃ (y : graphFixedRootGroup TwistTag.E6 K σ) (hy : (y : ModGL TwistTag.E6.tag K) ∈ su6Levi σ),
        (z : centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))) =
          QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨((e.symm y : L) : G), hDX y hy⟩)
    (hψ : Nonempty (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ≃* Kc))
    (hdesc : InvolutionDescent (a5LeviTwist (apply_apply_eq hK hσ))
      ((su6Levi σ).subgroupOf (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA)))
    (hext : AutExtensionComm
      ((su6Levi σ).subgroupOf (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA)).subtype
      (a5LeviTwist (apply_apply_eq hK hσ))) :
    ∃ Ψ : subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ≃* Kc,
      (∀ (y : graphFixedRootGroup TwistTag.E6 K σ) (hy : (y : ModGL TwistTag.E6.tag K) ∈ su6Levi σ),
        (Ψ ⟨y, hy.1⟩ : centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))) =
          QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨((e.symm y : L) : G), hDX y hy⟩) ∧
      ∀ x, Ψ (a5LeviTwist (apply_apply_eq hK hσ) x) = Kc.normalizerMonoidHom ⟨_, hsN⟩ (Ψ x) := by
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨ψ₀⟩ := hψ
  set LA := subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA with hLA
  set A := (su6Levi σ).subgroupOf LA with hAdef
  set π := QuotientGroup.mk' (oddCore (centralizer (X : Set G))) with hπ
  set θ := Kc.normalizerMonoidHom ⟨_, hsN⟩ with hθdef
  have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have hθθ : θ * θ = 1 := by
    have hs : π ⟨t, htX⟩ * π ⟨t, htX⟩ = 1 := by
      rw [← map_mul, show (⟨t, htX⟩ : centralizer (X : Set G)) * ⟨t, htX⟩ = 1 from
        Subtype.ext htt, map_one]
    rw [hθdef, ← map_mul, show (⟨π ⟨t, htX⟩, hsN⟩ : normalizer (Kc : Set _)) * ⟨_, hsN⟩ = 1 from
      Subtype.ext hs, map_one]
  have hyC : ∀ x : A, ((x : LA) : ModGL TwistTag.E6.tag K) ∈ graphFixedRootGroup TwistTag.E6 K σ :=
    fun x => (mem_subgroupOf.1 x.2).2
  let κ : A →* graphFixedRootGroup TwistTag.E6 K σ :=
    { toFun := fun x => ⟨((x : LA) : ModGL TwistTag.E6.tag K), hyC x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hκD : ∀ x : A, ((κ x : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) ∈
      su6Levi σ := fun x => mem_subgroupOf.1 x.2
  let ε₁ : A →* centralizer (X : Set G) :=
    (L.subtype.comp (e.symm.toMonoidHom.comp κ)).codRestrict _ fun x => hDX (κ x) (hκD x)
  let ε : A →* Kc := (π.comp ε₁).codRestrict Kc fun x => hDK (κ x) (hκD x)
  have hεapp : ∀ x : A, ((ε x : Kc) : centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))) =
      π ⟨((e.symm (κ x) : L) : G), hDX (κ x) (hκD x)⟩ := fun _ => rfl
  have hsimple : IsSimpleGroup A := by
    have := isSimpleGroup_su6Levi hf hk hK hσ
    exact (subgroupOfEquivOfLe (su6Levi_le_subsystemGroup σ)).isSimpleGroup
  have hε : Function.Injective ε := by
    rcases hsimple.eq_bot_or_eq_top_of_normal ε.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff ε).1 h
    · exfalso
      obtain ⟨y, hy, hne⟩ := hDne
      apply hne
      have hyA : (⟨⟨y, hy.1⟩, mem_subgroupOf.2 hy⟩ : A) ∈ ε.ker := h ▸ mem_top _
      have h1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hyA)
      exact h1
  have hεr : ε.range = perfectCore (fixedSubgroup θ) := by
    ext z
    rw [hcore z]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨κ x, hκD x, hεapp x⟩
    · rintro ⟨y, hy, hz⟩
      refine ⟨⟨⟨y, hy.1⟩, mem_subgroupOf.2 hy⟩, Subtype.ext ?_⟩
      rw [hz]
      rfl
  have hj₀ : A.subtype.range = perfectCore (fixedSubgroup (a5LeviTwist (apply_apply_eq hK hσ))) := by
    rw [range_subtype, perfectCore_fixedSubgroup_a5LeviTwist hf hk hK hσ]
  obtain ⟨Ψ, hΨj, hΨβ⟩ := exists_normalized_mulEquiv A.subtype_injective hj₀ hdesc hext ψ₀ hθθ hε
    hεr
  refine ⟨Ψ, fun y hy => ?_, hΨβ⟩
  have h1 := hΨj ⟨⟨y, hy.1⟩, mem_subgroupOf.2 hy⟩
  have h2 := congrArg (fun z : Kc => (z : centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))
    h1
  exact h2

theorem exists_normalized_a5Levi_mulEquiv_of_comp [Finite G] (hf : 1 ≤ f) {k : Type} [Field k]
    [Algebra k K] (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    {X : Subgroup G} (htX : t ∈ centralizer (X : Set G)) (ht2 : orderOf t = 2) {D : Subgroup G}
    (hDe : D = (((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
      e.symm.toMonoidHom).map L.subtype)
    (hDX : D ≤ centralizer (X : Set G)) (hDt : D ≤ centralizer ({t} : Set G))
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hDK : (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤ Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hDcomp : CFSG.IsComponent ((((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).subgroupOf Kc).subgroupOf
        (fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩))))
    (hψ : Nonempty (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ≃* Kc))
    (hdesc : InvolutionDescentComp (a5LeviTwist (apply_apply_eq hK hσ))
      ((su6Levi σ).subgroupOf (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA)))
    (hext : AutExtensionComm
      ((su6Levi σ).subgroupOf (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA)).subtype
      (a5LeviTwist (apply_apply_eq hK hσ))) :
    ∃ Ψ : subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ≃* Kc,
      (∀ (y : graphFixedRootGroup TwistTag.E6 K σ) (hy : (y : ModGL TwistTag.E6.tag K) ∈ su6Levi σ)
        (hyX : ((e.symm y : L) : G) ∈ centralizer (X : Set G)),
        (Ψ ⟨y, hy.1⟩ : centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))) =
          QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨((e.symm y : L) : G), hyX⟩) ∧
      ∀ x, Ψ (a5LeviTwist (apply_apply_eq hK hσ) x) = Kc.normalizerMonoidHom ⟨_, hsN⟩ (Ψ x) := by
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨ψ₀⟩ := hψ
  set LA := subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA with hLA
  set A := (su6Levi σ).subgroupOf LA with hAdef
  set π := QuotientGroup.mk' (oddCore (centralizer (X : Set G))) with hπ
  set Db := (D.subgroupOf (centralizer (X : Set G))).map π with hDbdef
  set θ := Kc.normalizerMonoidHom ⟨_, hsN⟩ with hθdef
  have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have hθθ : θ * θ = 1 := by
    have hs : π ⟨t, htX⟩ * π ⟨t, htX⟩ = 1 := by
      rw [← map_mul, show (⟨t, htX⟩ : centralizer (X : Set G)) * ⟨t, htX⟩ = 1 from
        Subtype.ext htt, map_one]
    rw [hθdef, ← map_mul, show (⟨π ⟨t, htX⟩, hsN⟩ : normalizer (Kc : Set _)) * ⟨_, hsN⟩ = 1 from
      Subtype.ext hs, map_one]
  have hyC : ∀ x : A, ((x : LA) : ModGL TwistTag.E6.tag K) ∈ graphFixedRootGroup TwistTag.E6 K σ :=
    fun x => (mem_subgroupOf.1 x.2).2
  let κ : A →* graphFixedRootGroup TwistTag.E6 K σ :=
    { toFun := fun x => ⟨((x : LA) : ModGL TwistTag.E6.tag K), hyC x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hmemD : ∀ x : A, ((e.symm (κ x) : L) : G) ∈ D := fun x => by
    rw [hDe]
    exact ⟨e.symm (κ x), ⟨κ x, mem_subgroupOf.2 (mem_subgroupOf.1 x.2), rfl⟩, rfl⟩
  let ε₁ : A →* centralizer (X : Set G) :=
    (L.subtype.comp (e.symm.toMonoidHom.comp κ)).codRestrict _ fun x => hDX (hmemD x)
  have hε₁D : ∀ x : A, π (ε₁ x) ∈ Db := fun x => ⟨ε₁ x, mem_subgroupOf.2 (hmemD x), rfl⟩
  let ε : A →* Kc := (π.comp ε₁).codRestrict Kc fun x => hDK (hε₁D x)
  have hεrange : ε.range = Db.subgroupOf Kc := by
    ext z
    rw [mem_subgroupOf]
    constructor
    · rintro ⟨x, rfl⟩
      exact hε₁D x
    · rintro ⟨⟨d, hdX⟩, hd, hdz⟩
      have hd' : d ∈ D := mem_subgroupOf.1 hd
      rw [hDe] at hd'
      obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hd'
      refine ⟨⟨⟨y, (mem_subgroupOf.1 hy).1⟩, mem_subgroupOf.2 (mem_subgroupOf.1 hy)⟩, ?_⟩
      apply Subtype.ext
      rw [← hdz]
      rfl
  have hsimple : IsSimpleGroup A := by
    have := isSimpleGroup_su6Levi hf hk hK hσ
    exact (subgroupOfEquivOfLe (su6Levi_le_subsystemGroup σ)).isSimpleGroup
  have hε : Function.Injective ε := by
    rcases hsimple.eq_bot_or_eq_top_of_normal ε.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff ε).1 h
    · exfalso
      have hbot : ε.range = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨x, rfl⟩
        exact (MonoidHom.mem_ker.1 (h ▸ mem_top x : x ∈ ε.ker)).symm ▸ one_mem _
      rw [hεrange] at hbot
      have hbot' := (Subgroup.eq_bot_iff_forall _).1 hbot
      have hsub : Subsingleton ((Db.subgroupOf Kc).subgroupOf (fixedSubgroup θ)) :=
        ⟨fun a b => by
          have ha : (a : fixedSubgroup θ) = 1 :=
            Subtype.ext (by simpa using hbot' _ (mem_subgroupOf.1 a.2))
          have hb : (b : fixedSubgroup θ) = 1 :=
            Subtype.ext (by simpa using hbot' _ (mem_subgroupOf.1 b.2))
          exact Subtype.ext (ha.trans hb.symm)⟩
      have hns := hDcomp.1.2.1.toNontrivial
      have hss : Subsingleton (((Db.subgroupOf Kc).subgroupOf (fixedSubgroup θ)) ⧸
          center ((Db.subgroupOf Kc).subgroupOf (fixedSubgroup θ))) :=
        (QuotientGroup.mk'_surjective _).subsingleton
      exact false_of_nontrivial_of_subsingleton (((Db.subgroupOf Kc).subgroupOf
        (fixedSubgroup θ)) ⧸ center ((Db.subgroupOf Kc).subgroupOf (fixedSubgroup θ)))
  have hεθ : ε.range ≤ fixedSubgroup θ := by
    rintro _ ⟨x, rfl⟩
    apply Subtype.ext
    change π ⟨t, htX⟩ * π (ε₁ x) * (π ⟨t, htX⟩)⁻¹ = π (ε₁ x)
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hc := mem_centralizer_singleton_iff.1 (hDt (hmemD x))
    change t * ((e.symm (κ x) : L) : G) * t⁻¹ = ((e.symm (κ x) : L) : G)
    rw [← hc, mul_inv_cancel_right]
  have hεC : CFSG.IsComponent (ε.range.subgroupOf (fixedSubgroup θ)) := by
    rw [hεrange]
    exact hDcomp
  have hj₀ : A.subtype.range = fixedSubgroup (a5LeviTwist (apply_apply_eq hK hσ)) := by
    rw [range_subtype, fixedSubgroup_a5LeviTwist hf hK hσ]
  have : Finite A := inferInstance
  obtain ⟨Ψ, hΨj, hΨβ⟩ := exists_normalized_mulEquiv_of_fix_eq A.subtype_injective hj₀ hdesc hext
    ψ₀ hθθ hε hεθ hεC
  refine ⟨Ψ, fun y hy hyX => ?_, hΨβ⟩
  have h1 := hΨj ⟨⟨y, hy.1⟩, mem_subgroupOf.2 hy⟩
  have h2 := congrArg (fun z : Kc => (z : centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))
    h1
  exact h2

end Cover

end CFSG.SeitzReduction.TwistedE6Pilot
