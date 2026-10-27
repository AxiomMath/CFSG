module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDCtx
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDGalois
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDConv

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open scoped TensorProduct MonoidAlgebra

section Orb

variable {p n : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] [Algebra (ZMod p) F] [CharP F p]
  {W : Type} [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
  (σ : Representation (ZMod p) (SLm F) W)

@[expose] noncomputable def orbSub (N : Submodule (MonoidAlgebra F (SLm F))
    (repXT σ).asModule) (j : ℕ) :
    Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule :=
  ((fun N' : Submodule (MonoidAlgebra F (SLm F))
      (repXT σ).asModule => N'.map (phiMod σ).toLinearMap)^[j]) N

omit [Module.Finite (ZMod p) W] in
theorem orbSub_zero (N : Submodule (MonoidAlgebra F (SLm F))
    (repXT σ).asModule) : orbSub σ N 0 = N := rfl

omit [Module.Finite (ZMod p) W] in
theorem orbSub_succ (N : Submodule (MonoidAlgebra F (SLm F))
    (repXT σ).asModule) (j : ℕ) :
    orbSub σ N (j + 1) = (orbSub σ N j).map (phiMod σ).toLinearMap := by
  unfold orbSub
  rw [Function.iterate_succ_apply']

omit [CharP F p] in
theorem exists_atom_label (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n) (hF : Nat.card F = p ^ n)
    (hW : IsSimpleModule (MonoidAlgebra (ZMod p) (SLm F)) σ.asModule) :
    ∃ (N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule)
      (B : ℕ), IsAtom N ∧ B < p ^ n ∧
        Nonempty (↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F B).asModule) := by
  have : Nontrivial σ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra (ZMod p) (SLm F)) σ.asModule
  have : Nontrivial W := σ.asModuleEquiv.symm.toEquiv.nontrivial
  let ρ := repXT σ
  have : Nontrivial (CFSG.Theory.Representation.extendScalars F σ).asModule := inferInstance
  have : Nontrivial ρ.asModule := (xEquiv σ).symm.toEquiv.nontrivial
  have : Finite (SLm F) := inferInstance
  have : Module.Finite F (XT p F W) := Module.Finite.equiv xtEquiv
  have : Module.Finite F ρ.asModule := Module.Finite.equiv ρ.asModuleEquiv.symm
  have : Module.Finite (MonoidAlgebra F (SLm F)) ρ.asModule :=
    Module.Finite.of_restrictScalars_finite F _ _
  have : IsArtinianRing (MonoidAlgebra F (SLm F)) := IsArtinianRing.of_finite F _
  have : IsArtinian (MonoidAlgebra F (SLm F)) ρ.asModule :=
    isArtinian_of_fg_of_artinian' (R := MonoidAlgebra F (SLm F)) (M := ρ.asModule)
  have : IsAtomic (Submodule (MonoidAlgebra F (SLm F)) ρ.asModule) := inferInstance
  obtain ⟨N, hNatom, -⟩ := (IsAtomic.eq_bot_or_exists_atom_le
    (⊤ : Submodule (MonoidAlgebra F (SLm F)) ρ.asModule)).resolve_left top_ne_bot
  have hNsimple : IsSimpleModule (MonoidAlgebra F (SLm F)) ↥N := isSimpleModule_iff_isAtom.2 hNatom
  have hπsimple : IsSimpleModule (MonoidAlgebra F (SLm F))
      (Subrepresentation.ofSubmodule' N).toRepresentation.asModule :=
    haveI := hNsimple
    IsSimpleModule.congr (submoduleEquivRep N).symm
  have : Module.Finite F ↥(Subrepresentation.ofSubmodule' N).toSubmodule := inferInstance
  obtain ⟨A, hA, ⟨e⟩⟩ := (hS p n Fact.out hp2 hn F hF).2.2 ↥(Subrepresentation.ofSubmodule' N).toSubmodule
    (Subrepresentation.ofSubmodule' N).toRepresentation hπsimple
  exact ⟨N, A, hNatom, hA, ⟨((submoduleEquivRep N).trans e).trans (stEquiv F A)⟩⟩

omit [Module.Finite (ZMod p) W] in
theorem orbSub_label (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n) (hF : Nat.card F = p ^ n)
    (N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule) {B : ℕ} (hB : B < p ^ n)
    (ι : ↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F B).asModule) (j : ℕ) :
    (rot p n)^[j] B < p ^ n ∧
      Nonempty (↥(orbSub σ N j) ≃ₗ[MonoidAlgebra F (SLm F)]
        (stRep F ((rot p n)^[j] B)).asModule) := by
  induction j with
  | zero => exact ⟨hB, ⟨ι⟩⟩
  | succ j ih =>
    obtain ⟨hlt, ⟨e⟩⟩ := ih
    rw [orbSub_succ, Function.iterate_succ_apply']
    exact ⟨mix11cD_rot_lt (Nat.Prime.one_lt (Fact.out)) hn hlt, map_phi_label σ hS hp2 hn hF _ hlt e⟩

omit [Module.Finite (ZMod p) W] in
theorem submodule_phi_stable_eq_top
    (hW : IsSimpleModule (MonoidAlgebra (ZMod p) (SLm F)) σ.asModule)
    (T : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule)
    (hΦ : T.map (phiMod σ).toLinearMap ≤ T) (hT : T ≠ ⊥) : T = ⊤ := by
  let e : (repXT σ).asModule ≃ₗ[F] F ⊗[ZMod p] W := (repXT σ).asModuleEquiv.trans xtEquiv.symm
  let T' : Submodule F (F ⊗[ZMod p] W) := (T.restrictScalars F).map e.toLinearMap
  have hmem : ∀ y, e y ∈ T' ↔ y ∈ T := by
    intro y
    constructor
    · rintro ⟨y', hy', hyy⟩
      have : y' = y := e.injective hyy
      exact this ▸ hy'
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hΦ' : ∀ x ∈ T', frobTensor W x ∈ T' := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 : phiMod σ y ∈ T := hΦ (Submodule.mem_map_of_mem hy)
    have h2 : e (phiMod σ y) = frobTensor W (e y) := phiMod_apply σ y
    show frobTensor W (e y) ∈ T'
    rw [← h2]
    exact (hmem _).2 h1
  have hG' : ∀ g : SLm F, ∀ x ∈ T', (σ g).baseChange F x ∈ T' := by
    intro g x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 : (MonoidAlgebra.single g (1 : F)) • y ∈ T := T.smul_mem _ hy
    have h2 : e ((MonoidAlgebra.single g (1 : F)) • y) = (σ g).baseChange F (e y) := by
      rw [Representation.single_smul, one_smul]
      rfl
    show (σ g).baseChange F (e y) ∈ T'
    rw [← h2]
    exact (hmem _).2 h1
  rcases frobTensor_stable_eq_bot_or_top σ hW T' hΦ' hG' with h | h
  · exfalso
    apply hT
    rw [eq_bot_iff]
    intro y hy
    have : e y ∈ T' := (hmem y).2 hy
    rw [h] at this
    have h0 : e y = 0 := (Submodule.mem_bot F).1 this
    have : y = 0 := e.injective (by rw [h0, map_zero])
    simp [this]
  · rw [eq_top_iff]
    intro y _
    have : e y ∈ T' := by rw [h]; trivial
    exact (hmem y).1 this

omit [Module.Finite (ZMod p) W] in
theorem orbSub_iSup_eq_top (hW : IsSimpleModule (MonoidAlgebra (ZMod p) (SLm F)) σ.asModule)
    (N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule) (hN : N ≠ ⊥) :
    ⨆ j, orbSub σ N j = ⊤ := by
  apply submodule_phi_stable_eq_top σ hW
  · rw [Submodule.map_iSup]
    refine iSup_le fun j => ?_
    rw [← orbSub_succ]
    exact le_iSup (orbSub σ N) (j + 1)
  · intro h
    apply hN
    rw [eq_bot_iff] at h ⊢
    exact (le_iSup (orbSub σ N) 0).trans h

theorem orbit_structure (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n) (hF : Nat.card F = p ^ n)
    (hW : IsSimpleModule (MonoidAlgebra (ZMod p) (SLm F)) σ.asModule) :
    ∃ (N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule) (A : ℕ), IsAtom N ∧ A < p ^ n ∧
      Nonempty (↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F A).asModule) ∧
      (∀ j, IsSimpleModule (MonoidAlgebra F (SLm F)) ↥(orbSub σ N j)) ∧
      ⨆ j, orbSub σ N j = ⊤ ∧
      IsSemisimpleModule (MonoidAlgebra F (SLm F)) (repXT σ).asModule := by
  obtain ⟨N, A, hNatom, hA, ⟨ι⟩⟩ := exists_atom_label σ hS hp2 hn hF hW
  have hsimple : ∀ j, IsSimpleModule (MonoidAlgebra F (SLm F)) ↥(orbSub σ N j) := by
    intro j
    obtain ⟨hlt, ⟨e⟩⟩ := orbSub_label σ hS hp2 hn hF N hA ι j
    have := stRep_simple hS hp2 hn hF hlt
    exact IsSimpleModule.congr (N := (stRep F ((rot p n)^[j] A)).asModule) e
  have htop := orbSub_iSup_eq_top σ hW N hNatom.1
  refine ⟨N, A, hNatom, hA, ⟨ι⟩, hsimple, htop, ?_⟩
  apply IsSemisimpleModule.of_sSup_simples_eq_top
  rw [eq_top_iff, ← htop]
  refine iSup_le fun j => le_sSup ?_
  exact hsimple j

end Orb

end CFSG.GH74.GLS.Stage4.Rest
