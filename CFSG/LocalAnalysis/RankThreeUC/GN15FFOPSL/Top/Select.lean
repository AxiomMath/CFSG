module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesCollapse
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SpecialLinear.NormalizerLift.Lift
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL

open scoped MatrixGroups
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LieType.SpecialLinear

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

@[expose] noncomputable def repUnits
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin m) K) W) :
    Matrix.SpecialLinearGroup (Fin m) K →* (W ≃ₗ[ZMod 2] W) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toMonoidHom.comp ρ.asGroupHom

omit [Finite K] [CharP K 2] [Finite W] in
theorem repUnits_apply
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin m) K) W)
    (g : Matrix.SpecialLinearGroup (Fin m) K) (w : W) : repUnits ρ g w = ρ g w :=
  rfl

omit [Finite K] [CharP K 2] [Finite W] in
theorem repUnits_ker_le_scalars
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin m) K) W)
    (hker : ∀ g, ρ g = 1 → g ∈ scalars m K) :
    (repUnits ρ).ker ≤ scalars m K := by
  intro g hg
  apply hker
  have h2 : (repUnits ρ g : W →ₗ[ZMod 2] W) = ρ g := by
    simp [repUnits, Representation.asGroupHom_apply]
  rw [← h2]
  show (repUnits ρ g : W →ₗ[ZMod 2] W) = LinearMap.id
  exact congrArg (fun e : W ≃ₗ[ZMod 2] W => (e : W →ₗ[ZMod 2] W)) hg

omit [Finite K] [CharP K 2] [Finite W] in
theorem le_rangeNormalizer_repUnits
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin m) K) W)
    {A : Subgroup (W ≃ₗ[ZMod 2] W)}
    (hint : ∀ a ∈ A, ∀ x, ∃ y, ∀ w, a (ρ x w) = ρ y (a w)) :
    A ≤ rangeNormalizer (repUnits ρ) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hint a ha x
    refine ⟨y, ?_⟩
    apply LinearEquiv.ext
    intro w
    simp only [LinearEquiv.mul_apply, repUnits_apply]
    rw [hy (a⁻¹ w)]
    simp
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz⟩ := hint a⁻¹ (A.inv_mem ha) y
    refine ⟨z, ?_⟩
    have hh : h = a⁻¹ * repUnits ρ y * a := by
      rw [hy]
      group
    apply LinearEquiv.ext
    intro w
    rw [hh]
    simp only [LinearEquiv.mul_apply, repUnits_apply]
    have hz' : a⁻¹ ((ρ y) (a w)) = ρ z w := by
      have h := hz (a w)
      rwa [show a⁻¹ (a w) = w by simp] at h
    exact hz'.symm

@[expose] noncomputable def unitsOf (A : Subgroup (W ≃ₗ[ZMod 2] W)) :
    Subgroup (Module.End (ZMod 2) W)ˣ :=
  A.map (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).symm.toMonoidHom

omit [Finite W] in
theorem mem_unitsOf_iff {A : Subgroup (W ≃ₗ[ZMod 2] W)}
    {a : (Module.End (ZMod 2) W)ˣ} :
    a ∈ unitsOf A ↔
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W) a :
        W ≃ₗ[ZMod 2] W) ∈ A := by
  rw [unitsOf, Subgroup.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩
    simpa using hb
  · intro ha
    exact ⟨_, ha, by simp⟩

omit [Finite K] [CharP K 2] in
theorem commute_of_mem_offender (hm : 3 ≤ m)
    {ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin m) K) W}
    (hirr : ρ.IsIrreducible)
    {A : Subgroup (W ≃ₗ[ZMod 2] W)} (hA1 : A ≠ ⊥)
    (hAel : CFSG.IsElementaryAbelian 2 ↥A)
    (hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ w, b (a w - w) = a w - w)
    (hint : ∀ a ∈ A, ∀ x, ∃ y, ∀ w, a (ρ x w) = ρ y (a w))
    (hoff : Nat.card W ≤ Nat.card ↥A * Nat.card {w : W // ∀ a ∈ A, a w = w}) :
    ∀ a ∈ A, ∀ f : W →ₗ[ZMod 2] W, (∀ g, f ∘ₗ ρ g = ρ g ∘ₗ f) →
      (a : W →ₗ[ZMod 2] W) ∘ₗ f = f ∘ₗ (a : W →ₗ[ZMod 2] W) := by
  classical
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W
  let L : Subgroup (Module.End (ZMod 2) W)ˣ := ρ.asGroupHom.range
  have hWnt : Nontrivial W :=
    ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr).1
  have : Nontrivial W := hWnt
  have hLperf : Group.IsPerfect ↥L := by
    have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin m) K) :=
      CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le hm
    exact Group.IsPerfect.range ρ.asGroupHom
  have hLnt : L ≠ ⊥ := by
    intro hbot
    have hρ : ∀ g, ρ g = 1 := by
      intro g
      have hg : ρ.asGroupHom g = 1 := by
        have hmem : ρ.asGroupHom g ∈ L := ⟨g, rfl⟩
        rwa [hbot, Subgroup.mem_bot] at hmem
      have := congrArg Units.val hg
      simpa [Representation.asGroupHom_apply] using this
    obtain ⟨-, hirr'⟩ := (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr
    have hinv : ∀ U : Submodule (ZMod 2) W,
        ∀ g, ∀ u ∈ U, (ρ g) u ∈ U := by
      intro U g u hu
      simpa only [hρ g, Module.End.one_apply] using hu
    have hsimple : ∀ U : Submodule (ZMod 2) W, U = ⊥ ∨ U = ⊤ :=
      fun U => hirr' U (hinv U)
    obtain ⟨v, hv⟩ := exists_ne (0 : W)
    have hspan : Submodule.span (ZMod 2) {v} = ⊤ := by
      rcases hsimple (Submodule.span (ZMod 2) {v}) with h | h
      · exact absurd h (by rwa [Submodule.span_singleton_eq_bot])
      · exact h
    have hAllOne : ∀ g : W ≃ₗ[ZMod 2] W, g = 1 := by
      intro g
      have hgv : g v = v := by
        have hmem : g v ∈ Submodule.span (ZMod 2) {v} := hspan ▸ Submodule.mem_top
        obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hmem
        have hd0 : d ≠ 0 := by
          intro hd0
          have hgv0 : g v = 0 := by rw [← hd, hd0, zero_smul]
          exact hv (g.injective (by simpa using hgv0))
        have hd1 : d = 1 := by
          rcases (by decide : ∀ d : ZMod 2, d = 0 ∨ d = 1) d with h | h
          · exact absurd h hd0
          · exact h
        calc g v = d • v := hd.symm
          _ = 1 • v := by simp [hd1]
          _ = v := one_smul _ _
      apply LinearEquiv.ext
      intro w
      have hw : w ∈ Submodule.span (ZMod 2) {v} := hspan ▸ Submodule.mem_top
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
      calc g w = g (c • v) := by rw [hc]
        _ = c • g v := map_smul g c v
        _ = c • v := by rw [hgv]
        _ = w := hc
    exact hA1 ((Subgroup.eq_bot_iff_forall A).mpr fun a _ => hAllOne a)
  have hAnorm : ∀ a ∈ unitsOf A, ∀ g ∈ L, a * g * a⁻¹ ∈ L := by
    intro a ha g hg
    obtain ⟨x, rfl⟩ := hg
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y, hy⟩ := hint a' ha' x
    refine ⟨y, ?_⟩
    have h1 : a' * repUnits ρ x = repUnits ρ y * a' := by
      apply LinearEquiv.ext
      intro w
      exact hy w
    apply e.injective
    change e (ρ.asGroupHom y) = e (e.symm a' * ρ.asGroupHom x * (e.symm a')⁻¹)
    rw [map_mul, map_mul, map_inv, e.apply_symm_apply a']
    change repUnits ρ y = a' * repUnits ρ x * a'⁻¹
    rw [h1]
    group
  have hA2 : ∀ a ∈ unitsOf A, a * a = 1 := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    change e.symm a' * e.symm a' = 1
    rw [← map_mul]
    have hsq : a' * a' = 1 := by
      have h := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a' ha'
      simpa [pow_two] using h
    rw [hsq, map_one]
  have hAnt : unitsOf A ≠ ⊥ := by
    intro hbot
    change A.map e.symm.toMonoidHom = ⊥ at hbot
    rw [Subgroup.map_eq_bot_iff_of_injective (f := e.symm.toMonoidHom) A
      (fun x y h => e.symm.injective h)] at hbot
    exact hA1 hbot
  have hquad' : ∀ a ∈ unitsOf A, ∀ b ∈ unitsOf A, ∀ w,
      (b : Module.End (ZMod 2) W) ((a : Module.End (ZMod 2) W) w - w) =
        (a : Module.End (ZMod 2) W) w - w := by
    intro a ha b hb w
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    exact hquad a' ha' b' hb' w
  have hfix : Nat.card {w : W // ∀ a ∈ unitsOf A,
        (a : Module.End (ZMod 2) W) w = w} =
      Nat.card {w : W // ∀ a ∈ A, (a : W ≃ₗ[ZMod 2] W) w = w} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
    constructor
    · intro hw a ha
      have hcoe : ((e.symm a : (Module.End (ZMod 2) W)ˣ) : Module.End (ZMod 2) W) =
          ((a : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) := rfl
      have h := hw (e.symm a) (Subgroup.mem_map_of_mem _ ha)
      rw [hcoe] at h
      simpa using h
    · intro hw a ha
      have hae : (e a : W ≃ₗ[ZMod 2] W) ∈ A := (mem_unitsOf_iff.mp ha)
      have hcoe : ((a : (Module.End (ZMod 2) W)ˣ) : Module.End (ZMod 2) W) =
          ((e a : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) := rfl
      rw [hcoe]
      simpa using hw (e a) hae
  have hcard : Nat.card ↥(unitsOf A) = Nat.card ↥A := by
    rw [unitsOf, Subgroup.card_map_of_injective e.symm.injective]
  have hoff' : Nat.card W ≤ Nat.card ↥(unitsOf A) *
      Nat.card {w : W // ∀ a ∈ unitsOf A, (a : Module.End (ZMod 2) W) w = w} := by
    rw [hcard, hfix]
    exact hoff
  have hLirr : (CFSG.QuasithinUnique.Setup.SL2Modules.repOfSubgroup L).IsIrreducible := by
    rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
    obtain ⟨hnt, hirr'⟩ := (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr
    refine ⟨hnt, fun U hU => hirr' U (fun g u hu => ?_)⟩
    have := hU ⟨ρ.asGroupHom g, ⟨g, rfl⟩⟩ u hu
    simpa [CFSG.QuasithinUnique.Setup.SL2Modules.repOfSubgroup_apply,
      Representation.asGroupHom_apply] using this
  have : Fact (CFSG.QuasithinUnique.Setup.SL2Modules.repOfSubgroup L).IsIrreducible :=
    ⟨hLirr⟩
  have hlin :=
    (CFSG.QuasithinUnique.Setup.SL2Modules.quadratic_offender_endomorphism_field_linearization
      (k := ZMod 2) (W := W) (L := L) (A := unitsOf A) hLperf hLnt hAnorm hA2 hAnt
      hquad' hoff').1
  intro a ha f hf
  let a' : (Module.End (ZMod 2) W)ˣ := e.symm a
  have ha' : a' ∈ unitsOf A := Subgroup.mem_map_of_mem _ ha
  have hfend : ∃ δ : CFSG.QuasithinUnique.Setup.SL2Modules.EndRing
      (CFSG.QuasithinUnique.Setup.SL2Modules.repOfSubgroup L),
      (δ : W → W) = f := by
    apply (CFSG.QuasithinUnique.Setup.SL2Modules.mem_endRing_iff
      (CFSG.QuasithinUnique.Setup.SL2Modules.repOfSubgroup L) f).mpr
    intro g v
    obtain ⟨x, hx⟩ := g.2
    have hxL : ρ.asGroupHom x ∈ L := hx.symm ▸ g.2
    have hg : g = ⟨ρ.asGroupHom x, hxL⟩ := Subtype.ext hx.symm
    rw [hg]
    have h := congrArg (fun φ : W →ₗ[ZMod 2] W => φ v) (hf x)
    simpa [CFSG.QuasithinUnique.Setup.SL2Modules.repOfSubgroup_apply,
      Representation.asGroupHom_apply, LinearMap.comp_apply] using h
  obtain ⟨δ, hδ⟩ := hfend
  have hlin' := hlin a' ha' δ
  have hδ' : CFSG.QuasithinUnique.Setup.SL2Modules.epsHom
      (CFSG.QuasithinUnique.Setup.SL2Modules.repOfSubgroup L) δ = f := by
    apply LinearMap.ext
    intro w
    have := congrFun hδ w
    simpa [CFSG.QuasithinUnique.Setup.SL2Modules.epsHom_apply] using this
  have ha'coe : (a' : Module.End (ZMod 2) W) = (a : W →ₗ[ZMod 2] W) := rfl
  rw [ha'coe, hδ'] at hlin'
  exact hlin'

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL
