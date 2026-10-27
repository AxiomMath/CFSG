module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bRepInd

public section

namespace CFSG.QuasithinUnique.Setup.X7b

open scoped MonoidAlgebra TensorProduct
open CFSG.Semidihedral.Principal Representation

section Flag

variable (k G : Type) [Field k] [Monoid G]

structure FRep where
  V : Type
  [addCommGroup : AddCommGroup V]
  [module : Module k V]
  [finite : Module.Finite k V]
  ρ : Representation k G V

attribute [instance] FRep.addCommGroup FRep.module FRep.finite

variable {k G}

@[expose] def FlagTop : ∀ {V : Type} [AddCommGroup V] [Module k V], Representation k G V →
    List (FRep k G) → Prop
  | V, _, _, _, [] => Subsingleton V
  | _, _, _, ρ, Q :: L => ∃ (V' : Type) (_ : AddCommGroup V') (_ : Module k V')
      (_ : Module.Finite k V') (ρ' : Representation k G V') (ι : IntertwiningMap ρ' ρ)
      (π : IntertwiningMap ρ Q.ρ), Function.Injective ι ∧ Function.Surjective π ∧
        Function.Exact ι π ∧ FlagTop ρ' L

theorem FlagTop.mult : ∀ (L : List (FRep k G)) {V : Type} [AddCommGroup V] [Module k V]
    [Module.Finite k V] (ρ : Representation k G V), FlagTop ρ L → ∀ {E : Type} [AddCommGroup E]
    [Module k E] (σ : Representation k G E),
    repMultiplicity ρ σ = (L.map fun Q => repMultiplicity Q.ρ σ).sum
  | [], V, _, _, _, ρ, h, _, _, _, σ => by
    have h1 : Subsingleton V := h
    have : Subsingleton (Representation.asModule ρ) := inferInstanceAs (Subsingleton V)
    unfold repMultiplicity
    rw [compositionMultiplicity_of_subsingleton]
    rfl
  | Q :: L, _, _, _, _, ρ, ⟨V', _, _, _, ρ', ι, π, hι, hπ, hex, hL⟩, _, _, _, σ => by
    rw [repMultiplicity_eq_add_of_exact ι π hι hπ hex σ, FlagTop.mult L ρ' hL σ]
    simp [List.map_cons, List.sum_cons, add_comm]

theorem FlagTop.tensor : ∀ (L : List (FRep k G)) {V : Type} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V), FlagTop ρ L → ∀ (X : FRep k G),
    FlagTop (tprod ρ X.ρ) (L.map fun Q => (⟨Q.V ⊗[k] X.V, tprod Q.ρ X.ρ⟩ : FRep k G))
  | [], V, _, _, ρ, h, X => by
    have h1 : Subsingleton V := h
    show Subsingleton (V ⊗[k] X.V)
    refine subsingleton_of_forall_eq 0 fun t => ?_
    induction t using TensorProduct.inductionOn with
    | tmul m n => rw [Subsingleton.elim m 0, TensorProduct.zero_tmul]
    | add x y hx hy => rw [hx, hy, add_zero]
  | Q :: L, _, _, _, ρ, ⟨V', _, _, _, ρ', ι, π, hι, hπ, hex, hL⟩, X => by
    refine ⟨V' ⊗[k] X.V, inferInstance, inferInstance, inferInstance, tprod ρ' X.ρ,
      IntertwiningMap.rTensor X.ρ ι, IntertwiningMap.rTensor X.ρ π, ?_, ?_, ?_,
      FlagTop.tensor L ρ' hL X⟩
    · exact Module.Flat.rTensor_preserves_injective_linearMap (M := X.V) ι.toLinearMap hι
    · exact LinearMap.rTensor_surjective X.V hπ
    · exact Module.Flat.rTensor_exact X.V hex

theorem FlagTop.congr : ∀ (L : List (FRep k G)) {V V' : Type} [AddCommGroup V] [Module k V]
    [AddCommGroup V'] [Module k V'] {ρ : Representation k G V} {ρ' : Representation k G V'},
    Representation.Equiv ρ ρ' → FlagTop ρ L → FlagTop ρ' L
  | [], V, V', _, _, _, _, ρ, ρ', e, h => by
    have h1 : Subsingleton V := h
    show Subsingleton V'
    exact e.toLinearEquiv.surjective.subsingleton
  | Q :: L, _, _, _, _, _, _, ρ, ρ', e, ⟨V'', _, _, _, ρ'', ι, π, hι, hπ, hex, hL⟩ => by
    refine ⟨V'', inferInstance, inferInstance, inferInstance, ρ'',
      IntertwiningMap.comp e.toIntertwiningMap ι, IntertwiningMap.comp π e.symm.toIntertwiningMap,
      ?_, ?_, ?_, hL⟩
    · exact e.toLinearEquiv.injective.comp hι
    · exact hπ.comp e.symm.toLinearEquiv.surjective
    · intro y
      have h1 := hex (e.symm y)
      show π (e.symm y) = 0 ↔ y ∈ Set.range fun x => e (ι x)
      rw [h1]
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨x, ?_⟩
        show e (ι x) = y
        rw [hx]
        exact e.apply_symm_apply y
      · rintro ⟨x, hx⟩
        have hx' : e (ι x) = y := hx
        refine ⟨x, ?_⟩
        rw [← hx']
        exact (e.symm_apply_apply _).symm

structure Chain {V : Type} [AddCommGroup V] [Module k V] (ρ : Representation k G V) {r : ℕ}
    (Q : Fin r → FRep k G) where
  W : Fin (r + 1) → Submodule k V
  inv : ∀ (s : Fin (r + 1)) (g : G), ∀ x ∈ W s, ρ g x ∈ W s
  bot : W 0 = ⊥
  top : W (Fin.last r) = ⊤
  mono : ∀ s : Fin r, W s.castSucc ≤ W s.succ
  φ : ∀ s : Fin r, V →ₗ[k] (Q s).V
  surj : ∀ (s : Fin r) (y : (Q s).V), ∃ x ∈ W s.succ, φ s x = y
  ker : ∀ (s : Fin r) (x : V), x ∈ W s.succ → (φ s x = 0 ↔ x ∈ W s.castSucc)
  comm : ∀ (s : Fin r) (g : G) (x : V), x ∈ W s.succ → φ s (ρ g x) = (Q s).ρ g (φ s x)

theorem flagTop_of_chain : ∀ (r : ℕ) {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k G V) (Q : Fin r → FRep k G), Chain ρ Q →
    FlagTop ρ (List.ofFn Q).reverse
  | 0, V, _, _, _, ρ, Q, C => by
    have h : Subsingleton V := by
      refine subsingleton_of_forall_eq 0 fun x => ?_
      have hx : x ∈ C.W (Fin.last 0) := by rw [C.top]; trivial
      have h0 : C.W (Fin.last 0) = ⊥ := C.bot
      rw [h0] at hx
      exact (Submodule.mem_bot k).mp hx
    have hl : (List.ofFn Q).reverse = [] := by simp
    rw [hl]
    exact h
  | r + 1, V, _, _, _, ρ, Q, C => by
    have hmono : Monotone C.W := Fin.monotone_iff_le_succ.mpr C.mono
    have hcs : ∀ s : Fin r, C.W s.castSucc.succ = C.W s.succ.castSucc := fun s => by
      rw [Fin.succ_castSucc]
    let Wr : Submodule k V := C.W (Fin.last r).castSucc
    let Wsub : Subrepresentation ρ := ⟨Wr, fun g v hv => C.inv _ g v hv⟩
    have htop : C.W (Fin.last r).succ = ⊤ := by rw [Fin.succ_last]; exact C.top
    let π : IntertwiningMap ρ (Q (Fin.last r)).ρ :=
      { toLinearMap := C.φ (Fin.last r)
        isIntertwining' := fun g => by
          ext x
          exact C.comm (Fin.last r) g x (by rw [htop]; trivial) }
    let C' : Chain Wsub.toRepresentation (fun s : Fin r => Q s.castSucc) :=
      { W := fun t => (C.W t.castSucc).comap Wr.subtype
        inv := fun t g x hx => C.inv t.castSucc g x hx
        bot := by
          show (C.W (0 : Fin (r + 1)).castSucc).comap Wr.subtype = ⊥
          rw [Fin.castSucc_zero, C.bot, Submodule.comap_bot, Submodule.ker_subtype]
        top := by
          show (C.W (Fin.last r).castSucc).comap Wr.subtype = ⊤
          exact Submodule.comap_subtype_self _
        mono := fun s => by
          have h := C.mono s.castSucc
          rw [Fin.succ_castSucc] at h
          exact Submodule.comap_mono h
        φ := fun s => (C.φ s.castSucc).comp Wr.subtype
        surj := fun s y => by
          obtain ⟨x, hx, hxy⟩ := C.surj s.castSucc y
          rw [hcs] at hx
          have hxWr : x ∈ Wr :=
            hmono (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last _)) hx
          exact ⟨⟨x, hxWr⟩, hx, hxy⟩
        ker := fun s x hx => by
          have hx' : (x : V) ∈ C.W s.castSucc.succ := by rw [hcs]; exact hx
          exact C.ker s.castSucc x hx'
        comm := fun s g x hx => by
          have hx' : (x : V) ∈ C.W s.castSucc.succ := by rw [hcs]; exact hx
          exact C.comm s.castSucc g x hx' }
    have ih := flagTop_of_chain r Wsub.toRepresentation (fun s => Q s.castSucc) C'
    have hl : (List.ofFn Q).reverse =
        Q (Fin.last r) :: (List.ofFn (fun s : Fin r => Q s.castSucc)).reverse := by
      rw [List.ofFn_succ']
      simp
    rw [hl]
    refine ⟨↥Wsub.toSubmodule, inferInstance, inferInstance, inferInstance,
      Wsub.toRepresentation, subIncl ρ Wsub, π, Wsub.toSubmodule.injective_subtype, ?_, ?_, ih⟩
    · intro y
      obtain ⟨x, -, hxy⟩ := C.surj (Fin.last r) y
      exact ⟨x, hxy⟩
    · intro x
      show C.φ (Fin.last r) x = 0 ↔ x ∈ Set.range Wsub.toSubmodule.subtype
      rw [C.ker (Fin.last r) x (by rw [htop]; trivial)]
      constructor
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
      · rintro ⟨y, rfl⟩
        exact y.2

end Flag

end CFSG.QuasithinUnique.Setup.X7b
