module

public import CFSG.LieType.SpecialLinear.SL2Swap.Final
public import CFSG.HardMathSupport.GuralnickMalle.InvariantSimpleCommuting

public section

namespace CFSG.LieType.SpecialLinear

open scoped MatrixGroups
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.HardMathSupport.GuralnickMalle

variable {F X D : Type}
  [Field F] [Fintype F] [CharP F 2]
  [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
  [Group D] [Finite D]

noncomputable def sl2PairSwapCommutingData (hq : 4 ≤ Fintype.card F)
    (ρ : Representation (ZMod 2) (SL(2, F) × SL(2, F)) X)
    (S : Set (X →ₗ[ZMod 2] X)) (hS : ∀ s ∈ S, ∀ m, s ∘ₗ ρ m = ρ m ∘ₗ s)
    (hsimp : ∀ W : Submodule (ZMod 2) X, (∀ m, ∀ w ∈ W, ρ m w ∈ W) →
      (∀ s ∈ S, ∀ w ∈ W, s w ∈ W) → W = ⊥ ∨ W = ⊤)
    (h₁ : ∃ g, ρ (g, 1) ≠ 1) (h₂ : ∃ g, ρ (1, g) ≠ 1)
    (δ : Representation (ZMod 2) D X) (hD : IsPGroup 2 D)
    (hD2 : ∀ d, δ d * δ d = 1) (hquad : ∀ a b x, δ b (δ a x - x) = δ a x - x)
    (hcompat : ∀ d, ∃ (A₁ A₂ : GL (Fin 2) F) (σ : F ≃+* F) (sw : Bool),
      ∀ m x, δ d (ρ m x) = ρ (pairAut A₁ A₂ σ sw m) (δ d x))
    (hswap : ∃ x, ∃ (A₁ A₂ : GL (Fin 2) F) (σ : F ≃+* F),
      ∀ m z, δ x (ρ m z) = ρ (pairAut A₁ A₂ σ true m) (δ x z))
    (hered : ∀ Z : Submodule (ZMod 2) X, (∀ d, ∀ z ∈ Z, δ d z ∈ Z) →
      IsOffenderOn δ ⊤ Z) :
    PLift False := by
  classical
  haveI : Nontrivial X := by
    by_contra h
    have hsub : Subsingleton X := not_nontrivial_iff_subsingleton.mp h
    obtain ⟨g, hg⟩ := h₁
    exact hg (LinearMap.ext fun x => hsub.elim (ρ (g, 1) x) x)
  have hnorm : ∀ d g, ∃ g', ∀ x, δ d (ρ g x) = ρ g' (δ d x) := by
    intro d g
    obtain ⟨A₁, A₂, τ, sw, hd⟩ := hcompat d
    exact ⟨pairAut (F := F) A₁ A₂ τ sw g, fun x => hd g x⟩
  let hsel := exists_invariant_simple_of_commuting ρ δ hD S hS hnorm hsimp
  let Z : Submodule (ZMod 2) X := Classical.choose hsel
  have hZ := Classical.choose_spec hsel
  have hZne : Z ≠ ⊥ := hZ.1
  have hZinv : ∀ g, ∀ z ∈ Z, ρ g z ∈ Z := hZ.2.1
  have hZsimple : ∀ W : Submodule (ZMod 2) X, W ≤ Z →
      (∀ g, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = Z := hZ.2.2.1
  have hZinvD : ∀ d, ∀ z ∈ Z, δ d z ∈ Z := hZ.2.2.2.1
  have hZker : ∀ g, (∀ z ∈ Z, ρ g z = z) → ρ g = 1 := hZ.2.2.2.2
  let ρ' : Representation (ZMod 2) (SL(2, F) × SL(2, F)) Z :=
    restrictToSubmodule ρ Z hZinv
  let δ' : Representation (ZMod 2) D Z := restrictToSubmodule δ Z hZinvD
  have hρ'apply : ∀ (m : SL(2, F) × SL(2, F)) (z : Z),
      ((ρ' m) z : X) = ρ m (z : X) := fun m z => restrictToSubmodule_apply ρ Z hZinv m z
  have hδ'apply : ∀ (d : D) (z : Z), ((δ' d) z : X) = δ d (z : X) :=
    fun d z => restrictToSubmodule_apply δ Z hZinvD d z
  haveI : Fact ρ'.IsIrreducible :=
    ⟨restrictToSubmodule_isIrreducible ρ Z hZinv hZne hZsimple⟩
  have hfac : ∀ m : SL(2, F) × SL(2, F), (∀ z : Z, ρ' m z = z) → ρ m = 1 := by
    intro m hm
    apply hZker m
    intro z hz
    have h := congrArg (fun w : Z => (w : X)) (hm ⟨z, hz⟩)
    simpa only [hρ'apply] using h
  have h₁' : ∃ g, ρ' (g, 1) ≠ 1 := by
    obtain ⟨g, hg⟩ := h₁
    refine ⟨g, fun h => hg (hfac (g, 1) ?_)⟩
    intro z
    simpa using congrArg (fun f => f z) h
  have h₂' : ∃ g, ρ' (1, g) ≠ 1 := by
    obtain ⟨g, hg⟩ := h₂
    refine ⟨g, fun h => hg (hfac (1, g) ?_)⟩
    intro z
    simpa using congrArg (fun f => f z) h
  have hD2' : ∀ d, δ' d * δ' d = 1 := by
    intro d
    apply LinearMap.ext
    intro z
    change (δ' d) ((δ' d) z) = z
    apply Subtype.ext
    have h : δ d (δ d (z : X)) = (z : X) := by
      simpa using congrArg (fun f : X →ₗ[ZMod 2] X => f (z : X)) (hD2 d)
    simpa only [hδ'apply] using h
  have hquad' : ∀ a b z, δ' b (δ' a z - z) = δ' a z - z := by
    intro a b z
    apply Subtype.ext
    have h : δ b (δ a (z : X) - (z : X)) = δ a (z : X) - (z : X) := hquad a b (z : X)
    simpa only [hδ'apply, Submodule.coe_sub, map_sub] using h
  have hker : δ'.ker = cenOn δ ⊤ Z := by
    ext d
    rw [MonoidHom.mem_ker]
    constructor
    · intro hd
      refine ⟨Subgroup.mem_top d, fun z hz => ?_⟩
      have h := congrArg (fun f : Z →ₗ[ZMod 2] Z => f ⟨z, hz⟩) hd
      change ((δ' d) ⟨z, hz⟩ : Z) = ⟨z, hz⟩ at h
      simpa only [hδ'apply] using congrArg (fun w : Z => (w : X)) h
    · intro hd
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      change ((δ' d) z : X) = (z : X)
      have h := hd.2 (z : X) z.2
      simpa only [hδ'apply] using h
  let fixEquiv : {z : Z // ∀ d, δ' d z = z} ≃ ↥(fixOn δ ⊤ Z) :=
    { toFun := fun z => ⟨(z.1 : X), by
        rw [mem_fixOn]
        exact ⟨z.1.2, fun d _ => by
          have h := congrArg (fun w : Z => (w : X)) (z.2 d)
          simpa only [hδ'apply] using h⟩⟩
      invFun := fun y => ⟨⟨(y.1 : X), y.2.1⟩, fun d => by
        apply Subtype.ext
        have h := y.2.2 d (Subgroup.mem_top d)
        simpa only [hδ'apply] using h⟩
      left_inv := fun z => by
        apply Subtype.ext
        rfl
      right_inv := fun y => by
        apply Subtype.ext
        rfl }
  have hfixcard : Nat.card {z : Z // ∀ d, δ' d z = z} = Nat.card (fixOn δ ⊤ Z) :=
    Nat.card_congr fixEquiv
  have hoff' : Nat.card Z * Nat.card δ'.ker ≤
      Nat.card D * Nat.card {z : Z // ∀ d, δ' d z = z} := by
    have hoff := (hered Z hZinvD).2
    rw [hker, hfixcard]
    simpa [Subgroup.card_top] using hoff
  have hcompat' : ∀ d, ∃ (A₁ A₂ : GL (Fin 2) F) (σ : F ≃+* F) (sw : Bool),
      ∀ m z, δ' d (ρ' m z) = ρ' (pairAut A₁ A₂ σ sw m) (δ' d z) := by
    intro d
    obtain ⟨A₁, A₂, τ, sw, hd⟩ := hcompat d
    refine ⟨A₁, A₂, τ, sw, ?_⟩
    intro m z
    apply Subtype.ext
    simpa only [hρ'apply, hδ'apply] using hd m (z : X)
  have hswap' : ∃ x, ∃ (A₁ A₂ : GL (Fin 2) F) (σ : F ≃+* F),
      ∀ m z, δ' x (ρ' m z) = ρ' (pairAut A₁ A₂ σ true m) (δ' x z) := by
    obtain ⟨x, A₁, A₂, τ, hx⟩ := hswap
    refine ⟨x, A₁, A₂, τ, ?_⟩
    intro m z
    apply Subtype.ext
    simpa only [hρ'apply, hδ'apply] using hx m (z : X)
  exact ⟨sl2Pair_swap_false hq ρ' h₁' h₂' δ' hD2' hquad' hoff' hcompat' hswap'⟩

theorem sl2Pair_swap_false_of_commuting (hq : 4 ≤ Fintype.card F)
    (ρ : Representation (ZMod 2) (SL(2, F) × SL(2, F)) X)
    (S : Set (X →ₗ[ZMod 2] X)) (hS : ∀ s ∈ S, ∀ m, s ∘ₗ ρ m = ρ m ∘ₗ s)
    (hsimp : ∀ W : Submodule (ZMod 2) X, (∀ m, ∀ w ∈ W, ρ m w ∈ W) →
      (∀ s ∈ S, ∀ w ∈ W, s w ∈ W) → W = ⊥ ∨ W = ⊤)
    (h₁ : ∃ g, ρ (g, 1) ≠ 1) (h₂ : ∃ g, ρ (1, g) ≠ 1)
    (δ : Representation (ZMod 2) D X) (hD : IsPGroup 2 D)
    (hD2 : ∀ d, δ d * δ d = 1) (hquad : ∀ a b x, δ b (δ a x - x) = δ a x - x)
    (hcompat : ∀ d, ∃ (A₁ A₂ : GL (Fin 2) F) (σ : F ≃+* F) (sw : Bool),
      ∀ m x, δ d (ρ m x) = ρ (pairAut A₁ A₂ σ sw m) (δ d x))
    (hswap : ∃ x, ∃ (A₁ A₂ : GL (Fin 2) F) (σ : F ≃+* F),
      ∀ m z, δ x (ρ m z) = ρ (pairAut A₁ A₂ σ true m) (δ x z))
    (hered : ∀ Z : Submodule (ZMod 2) X, (∀ d, ∀ z ∈ Z, δ d z ∈ Z) →
      IsOffenderOn δ ⊤ Z) :
    False :=
  (sl2PairSwapCommutingData hq ρ S hS hsimp h₁ h₂ δ hD hD2 hquad hcompat hswap hered).down

theorem sl2Triple_swap_false
    {E G : Type} [Field E] [Fintype E] [CharP E 2] [Algebra (ZMod 2) E] [Module E X] [Group G]
    (hq : 4 ≤ Fintype.card F)
    (σ : Representation (ZMod 2) (SL(2, F) × G × SL(2, F)) X)
    (hσE : ∀ m (c : E) x, σ m (c • x) = c • σ m x)
    (hsimp : ∀ W : Submodule E X, (∀ m, ∀ w ∈ W, σ m w ∈ W) → W = ⊥ ∨ W = ⊤)
    (h₁ : ∃ g, σ (g, 1, 1) ≠ 1) (h₃ : ∃ g, σ (1, 1, g) ≠ 1)
    (δ : Representation (ZMod 2) D X) (hD : IsPGroup 2 D)
    (hD2 : ∀ d, δ d * δ d = 1) (hquad : ∀ a b x, δ b (δ a x - x) = δ a x - x)
    (hcompat : ∀ d, ∃ (A₁ A₃ : GL (Fin 2) F) (τ : F ≃+* F) (sw : Bool) (β : G →* G),
      ∀ g₁ g₂ g₃ x, δ d (σ (g₁, g₂, g₃) x) =
        σ ((pairAut A₁ A₃ τ sw (g₁, g₃)).1, β g₂, (pairAut A₁ A₃ τ sw (g₁, g₃)).2) (δ d x))
    (hswap : ∃ x, ∃ (A₁ A₃ : GL (Fin 2) F) (τ : F ≃+* F) (β : G →* G),
      ∀ g₁ g₂ g₃ z, δ x (σ (g₁, g₂, g₃) z) =
        σ ((pairAut A₁ A₃ τ true (g₁, g₃)).1, β g₂, (pairAut A₁ A₃ τ true (g₁, g₃)).2) (δ x z))
    (hered : ∀ Z : Submodule (ZMod 2) X, (∀ d, ∀ z ∈ Z, δ d z ∈ Z) →
      IsOffenderOn δ ⊤ Z) :
    False := by
  classical
  let emb : SL(2, F) × SL(2, F) →* SL(2, F) × G × SL(2, F) :=
    { toFun := fun m => (m.1, 1, m.2)
      map_one' := rfl
      map_mul' := by
        intro a b
        ext <;> simp }
  let ρ : Representation (ZMod 2) (SL(2, F) × SL(2, F)) X := σ.comp emb
  let S : Set (X →ₗ[ZMod 2] X) :=
    Set.range (fun c : E => c • (LinearMap.id : X →ₗ[ZMod 2] X)) ∪
      Set.range (fun g : G => σ (1, g, 1))
  have hρapply : ∀ (m : SL(2, F) × SL(2, F)) (x : X),
      ρ m x = σ (m.1, 1, m.2) x := fun m x => rfl
  have hS : ∀ s ∈ S, ∀ m, s ∘ₗ ρ m = ρ m ∘ₗ s := by
    intro s hs m
    rcases hs with hs | hs
    · obtain ⟨c, rfl⟩ := hs
      ext x
      simp only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.comp_apply]
      rw [hρapply, hρapply]
      exact (hσE (m.1, 1, m.2) c x).symm
    · obtain ⟨g, rfl⟩ := hs
      ext x
      have hcomm : ((1, g, 1) : SL(2, F) × G × SL(2, F)) * (m.1, 1, m.2) =
          (m.1, 1, m.2) * ((1, g, 1) : SL(2, F) × G × SL(2, F)) := by
        refine Prod.ext ?_ ?_
        · simp
        · refine Prod.ext ?_ ?_ <;> simp
      change (σ (1, g, 1)) ((ρ m) x) = (ρ m) ((σ (1, g, 1)) x)
      rw [hρapply, hρapply]
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hcomm]
  have hsimp' : ∀ W : Submodule (ZMod 2) X, (∀ m, ∀ w ∈ W, ρ m w ∈ W) →
      (∀ s ∈ S, ∀ w ∈ W, s w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hWρ hWS
    have hWsmul : ∀ (c : E) (w : X), w ∈ W → c • w ∈ W := by
      intro c w hw
      have h := hWS (c • (LinearMap.id : X →ₗ[ZMod 2] X)) (Or.inl (Set.mem_range_self c)) w hw
      simpa using h
    let W_E : Submodule E X :=
      { carrier := W
        add_mem' := W.add_mem
        zero_mem' := W.zero_mem
        smul_mem' := hWsmul }
    have hW_Eσ : ∀ m : SL(2, F) × G × SL(2, F), ∀ w ∈ W_E, σ m w ∈ W_E := by
      intro m w hw
      obtain ⟨g₁, g₂, g₃⟩ := m
      have hm : (g₁, g₂, g₃) =
          ((g₁, 1, g₃) : SL(2, F) × G × SL(2, F)) *
            ((1, g₂, 1) : SL(2, F) × G × SL(2, F)) := by
        refine Prod.ext ?_ ?_
        · simp
        · refine Prod.ext ?_ ?_ <;> simp
      rw [hm, map_mul, Module.End.mul_apply]
      have hw' : σ (1, g₂, 1) w ∈ W :=
        hWS (σ (1, g₂, 1)) (Or.inr (Set.mem_range_self g₂)) w hw
      exact hWρ (g₁, g₃) (σ (1, g₂, 1) w) hw'
    rcases hsimp W_E hW_Eσ with h | h
    · left
      ext x
      have hx : x ∈ W_E ↔ x ∈ (⊥ : Submodule E X) := by rw [h]
      simpa [W_E] using hx
    · right
      ext x
      have hx : x ∈ W_E ↔ x ∈ (⊤ : Submodule E X) := by rw [h]
      simpa [W_E] using hx
  have h₁' : ∃ g, ρ (g, 1) ≠ 1 := by
    obtain ⟨g, hg⟩ := h₁
    refine ⟨g, fun h => hg ?_⟩
    simpa [ρ, emb] using h
  have h₃' : ∃ g, ρ (1, g) ≠ 1 := by
    obtain ⟨g, hg⟩ := h₃
    refine ⟨g, fun h => hg ?_⟩
    simpa [ρ, emb] using h
  have hcompat' : ∀ d, ∃ (A₁ A₂ : GL (Fin 2) F) (τ : F ≃+* F) (sw : Bool),
      ∀ m x, δ d (ρ m x) = ρ (pairAut A₁ A₂ τ sw m) (δ d x) := by
    intro d
    obtain ⟨A₁, A₂, τ, sw, β, hd⟩ := hcompat d
    refine ⟨A₁, A₂, τ, sw, ?_⟩
    intro m x
    simpa [ρ, emb, map_one] using hd m.1 1 m.2 x
  have hswap' : ∃ x, ∃ (A₁ A₂ : GL (Fin 2) F) (τ : F ≃+* F),
      ∀ m z, δ x (ρ m z) = ρ (pairAut A₁ A₂ τ true m) (δ x z) := by
    obtain ⟨x, A₁, A₂, τ, β, hx⟩ := hswap
    refine ⟨x, A₁, A₂, τ, ?_⟩
    intro m z
    simpa [ρ, emb, map_one] using hx m.1 1 m.2 z
  exact sl2Pair_swap_false_of_commuting hq ρ S hS hsimp' h₁' h₃' δ hD hD2 hquad hcompat' hswap' hered

end CFSG.LieType.SpecialLinear
