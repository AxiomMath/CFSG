module

public import CFSG.LieType.SpecialLinear.Stage.Simple
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.GraphThree.Offender
public import CFSG.HardMathSupport.GuralnickMalle.InvariantSimpleCommuting
public import CFSG.LieType.Universal.SpecialLinear
public import CFSG.LieType.CurtisTits.Recognition

public section

namespace CFSG.LieType.SpecialLinear

open Matrix
open CFSG.Quasithin.SmithCurtis
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.HardMathSupport.GuralnickMalle
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

variable {F : Type} [Field F] [Fintype F] [CharP F 2]
  {E : Type} [Field E] [Fintype E] [CharP E 2] [Algebra (ZMod 2) E]
  {k : Type} [Field k] [CharP k 2] [Algebra E k] [Algebra F k]
  {D : Type} [Group D] [Finite D]
  {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Module E X]
  [IsScalarTower (ZMod 2) E X] [Finite X]

omit [Fintype E] [CharP E 2] [CharP k 2] [Algebra F k] in
theorem stage_three_false (hq : 4 ≤ Fintype.card F)
    (σ : Representation E (SpecialLinearGroup (Fin 3) F) X)
    (hsimp : IsSimpleRep (CFSG.Theory.Representation.extendScalars k σ))
    (hσ : ∃ g, σ g ≠ 1)
    (δ : Representation (ZMod 2) D X)
    (hδE : ∀ d (c : E) (x : X), δ d (c • x) = c • δ d x)
    (hD : IsPGroup 2 D) (hD2 : ∀ d, δ d * δ d = 1)
    (hcompat : ∀ d, ∃ A : GL (Fin 3) F, IsUpperGL A ∧ ∃ (τ : F ≃+* F) (ε : ℕ),
      ∀ g x, δ d (σ g x) = σ (borelStd 3 F A τ ε g) (δ d x))
    (hgraph : ∃ d, ∃ A : GL (Fin 3) F, IsUpperGL A ∧ ∃ τ : F ≃+* F,
      ∀ g x, δ d (σ g x) = σ (borelStd 3 F A τ 1 g) (δ d x))
    (hered : ∀ Z : Submodule (ZMod 2) X, (∀ d, ∀ z ∈ Z, δ d z ∈ Z) →
      IsOffenderOn δ ⊤ Z) : False := by
  classical
  have _hδE_used := hδE
  have hσsimple : IsSimpleRep σ := isSimpleRep_of_isSimpleRep_extendScalars σ hsimp
  let σb : Representation (ZMod 2) (SpecialLinearGroup (Fin 3) F) X :=
    { toFun := fun g => (σ g).restrictScalars (ZMod 2)
      map_one' := by
        rw [map_one]
        change (LinearMap.id : X →ₗ[E] X).restrictScalars (ZMod 2) =
          (LinearMap.id : X →ₗ[ZMod 2] X)
        rw [LinearMap.restrictScalars_id]
      map_mul' := by
        intro g h
        ext x
        exact congrArg (fun f : X →ₗ[E] X => f x) (map_mul σ g h) }
  let S : Set (X →ₗ[ZMod 2] X) :=
    Set.range fun c : E => c • (LinearMap.id : X →ₗ[ZMod 2] X)
  have hS : ∀ s ∈ S, ∀ g, s ∘ₗ σb g = σb g ∘ₗ s := by
    intro s hs g
    obtain ⟨c, rfl⟩ := hs
    ext x
    simp only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.comp_apply]
    exact ((σ g).map_smul c x).symm
  have hnorm : ∀ d g, ∃ g', ∀ x, δ d (σb g x) = σb g' (δ d x) := by
    intro d g
    obtain ⟨A, -, τ, ε, hd⟩ := hcompat d
    exact ⟨borelStd 3 F A τ ε g, fun x => hd g x⟩
  have hsimp' : ∀ W : Submodule (ZMod 2) X, (∀ g, ∀ w ∈ W, σb g w ∈ W) →
      (∀ s ∈ S, ∀ w ∈ W, s w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW hWS
    have hWsmul : ∀ (c : E) (w : X), w ∈ W → c • w ∈ W := by
      intro c w hw
      have h := hWS (c • (LinearMap.id : X →ₗ[ZMod 2] X)) (Set.mem_range_self c) w hw
      simpa using h
    let W_E : Submodule E X :=
      { carrier := W
        add_mem' := W.add_mem
        zero_mem' := W.zero_mem
        smul_mem' := hWsmul }
    have hW_Eσ : ∀ g, ∀ w ∈ W_E, σ g w ∈ W_E := by
      intro g w hw
      exact hW g w hw
    rcases hσsimple.2 W_E hW_Eσ with h | h
    · left
      ext x
      have hx : x ∈ W_E ↔ x ∈ (⊥ : Submodule E X) := by rw [h]
      simpa [W_E] using hx
    · right
      ext x
      have hx : x ∈ W_E ↔ x ∈ (⊤ : Submodule E X) := by rw [h]
      simpa [W_E] using hx
  obtain ⟨Z, hZne, hZinv, hZsimple, hZinvD, hZker⟩ :=
    @exists_invariant_simple_of_commuting X (SpecialLinearGroup (Fin 3) F) D
      _ _ _ _ _ _ σb δ hD S hS hnorm hsimp' hσsimple.1
  let ρZ : Representation (ZMod 2) (SpecialLinearGroup (Fin 3) F) Z :=
    restrictToSubmodule σb Z hZinv
  let δZ : Representation (ZMod 2) D Z := restrictToSubmodule δ Z hZinvD
  have hρZ_apply : ∀ (g : SpecialLinearGroup (Fin 3) F) (z : Z),
      ((ρZ g) z : X) = σ g (z : X) := fun g z => rfl
  have hδZ_apply : ∀ (d : D) (z : Z), ((δZ d) z : X) = δ d (z : X) := fun d z => rfl
  have hirr : ρZ.IsIrreducible :=
    restrictToSubmodule_isIrreducible σb Z hZinv hZne hZsimple
  have hqs : CFSG.IsQuasisimple (SpecialLinearGroup (Fin 3) F) :=
    CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 F (by norm_num)
  have hσunit : ∃ g, σ.asGroupHom g ≠ 1 := by
    obtain ⟨g, hg⟩ := hσ
    exact ⟨g, fun h => hg (by
      have := congrArg Units.val h
      simpa [Representation.asGroupHom_apply] using this)⟩
  have hker_le : σ.asGroupHom.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) F) :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hqs (φ := σ.asGroupHom) hσunit
  have hkerZ : ∀ x, ρZ x = 1 → x ∈ LinearFlag.scalars 3 F := by
    intro x hx
    have hxσ : x ∈ σ.asGroupHom.ker := by
      rw [MonoidHom.mem_ker]
      apply Units.ext
      rw [Representation.asGroupHom_apply]
      have hxσb : σb x = 1 := by
        refine hZker x ?_
        intro z hz
        have h := congrArg (fun f : Z →ₗ[ZMod 2] Z => f ⟨z, hz⟩) hx
        exact congrArg Subtype.val h
      ext y
      have h := congrArg (fun f : X →ₗ[ZMod 2] X => f y) hxσb
      simpa [σb] using h
    have hc := hker_le hxσ
    rwa [← LinearFlag.scalars_eq_center] at hc
  have hnormZ : ∀ d x, ∃ y, ∀ z : Z, δZ d (ρZ x z) = ρZ y (δZ d z) := by
    intro d x
    obtain ⟨A, -, τ, ε, hd⟩ := hcompat d
    exact ⟨borelStd 3 F A τ ε x, fun z => by
      apply Subtype.ext
      simpa only [hρZ_apply, hδZ_apply] using hd x (z : X)⟩
  have hgraphZ : ∃ d, ∃ (A : GL (Fin 3) F) (τ : F ≃+* F),
      ∀ x z, δZ d (ρZ x z) = ρZ (borelStd 3 F A τ 1 x) (δZ d z) := by
    obtain ⟨d, A, -, τ, hd⟩ := hgraph
    exact ⟨d, A, τ, fun x z => by
      apply Subtype.ext
      simpa only [hρZ_apply, hδZ_apply] using hd x (z : X)⟩
  have hD2Z : ∀ d, δZ d * δZ d = 1 := by
    intro d
    apply LinearMap.ext
    intro z
    change (δZ d) ((δZ d) z) = z
    apply Subtype.ext
    have h : δ d (δ d (z : X)) = (z : X) := by
      simpa using congrArg (fun f : X →ₗ[ZMod 2] X => f (z : X)) (hD2 d)
    simpa only [hδZ_apply] using h
  have hoff : Nat.card Z * Nat.card δZ.ker ≤
      Nat.card D * Nat.card {z : Z // ∀ d, δZ d z = z} := by
    have hoffZ := (hered Z hZinvD).2
    have hker : δZ.ker = cenOn δ ⊤ Z := by
      ext d
      rw [MonoidHom.mem_ker]
      constructor
      · intro hd
        refine ⟨Subgroup.mem_top d, fun z hz => ?_⟩
        have h := congrArg (fun f : Z →ₗ[ZMod 2] Z => f ⟨z, hz⟩) hd
        change ((δZ d) ⟨z, hz⟩ : Z) = ⟨z, hz⟩ at h
        simpa only [hδZ_apply] using congrArg (fun w : Z => (w : X)) h
      · intro hd
        apply LinearMap.ext
        intro z
        apply Subtype.ext
        change ((δZ d) z : X) = (z : X)
        have h := hd.2 (z : X) z.2
        simpa only [hδZ_apply] using h
    let fixEquiv : {z : Z // ∀ d, δZ d z = z} ≃ ↥(fixOn δ ⊤ Z) :=
      { toFun := fun z => ⟨(z.1 : X), by
          rw [mem_fixOn]
          exact ⟨z.1.2, fun d _ => by
            have h := congrArg (fun w : Z => (w : X)) (z.2 d)
            simpa only [hδZ_apply] using h⟩⟩
        invFun := fun y => ⟨⟨(y.1 : X), y.2.1⟩, fun d => by
          apply Subtype.ext
          have h := y.2.2 d (Subgroup.mem_top d)
          simpa only [hδZ_apply] using h⟩
        left_inv := fun z => by apply Subtype.ext; rfl
        right_inv := fun y => by apply Subtype.ext; rfl }
    have hfixcard : Nat.card {z : Z // ∀ d, δZ d z = z} = Nat.card (fixOn δ ⊤ Z) :=
      Nat.card_congr fixEquiv
    rw [hker, hfixcard]
    simpa [Subgroup.card_top] using hoffZ
  obtain ⟨n, -, hcard⟩ := FiniteField.card F 2
  have hn : 2 ≤ (n : ℕ) := by
    have h4 : 2 ^ 2 ≤ 2 ^ (n : ℕ) := by
      rw [← hcard]
      simpa [Nat.card_eq_fintype_card] using hq
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4
  exact CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.sl3_borel_offender_false
    (f := (n : ℕ)) hn hcard ρZ hirr hkerZ δZ hD2Z hnormZ hgraphZ hoff

end CFSG.LieType.SpecialLinear
