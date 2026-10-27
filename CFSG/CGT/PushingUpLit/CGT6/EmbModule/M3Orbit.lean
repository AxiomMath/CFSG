module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDMain
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M3Steinberg
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDDim

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.GH74.GLS.Stage4.Rest
open scoped TensorProduct MonoidAlgebra

section Orbit

variable {n : ℕ} {F : Type} [Field F] [Finite F] [Algebra (ZMod 2) F] [CharP F 2]
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
  (σ : Representation (ZMod 2) (SLm F) W)

omit [Algebra (ZMod 2) F] [Module.Finite (ZMod 2) W] in
theorem m3_steinbergTheta (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (A : ℕ) :
    Nonempty ((steinbergRep F F A).asModule ≃ₛₗ[
      ((gaTwist (G := SLm F) (frobF 2 F) : MonoidAlgebra F (SLm F) ≃+* MonoidAlgebra F (SLm F)) :
        MonoidAlgebra F (SLm F) →+* MonoidAlgebra F (SLm F))]
      (steinbergRep F F (rot 2 n A)).asModule) := by
  obtain ⟨Θ, hbij, hs, hg⟩ := m3_twist Nat.prime_two hF hn A
  exact ⟨semilinOfFrob (steinbergRep F F A) (steinbergRep F F (rot 2 n A)) (frobF 2 F)
    (AddEquiv.ofBijective Θ hbij) (fun c x => by simpa [frobF_apply] using hs c x)
    (fun g x => hg g x)⟩

omit [Module.Finite (ZMod 2) W] in
theorem m3_map_phi_label (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule) {B : ℕ}
    (ι : ↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F B).asModule) :
    Nonempty (N.map (phiMod σ).toLinearMap ≃ₗ[MonoidAlgebra F (SLm F)]
      (stRep F (rot 2 n B)).asModule) := by
  obtain ⟨Θ⟩ := m3_steinbergTheta (F := F) hn hF B
  exact ⟨(twistTransport (R := MonoidAlgebra F (SLm F)) (gaTwist (G := SLm F) (frobF 2 F))
    (M := (repXT σ).asModule)
    (P := (steinbergRep F F B).asModule) (Q := (steinbergRep F F (rot 2 n B)).asModule)
    (phiMod σ) Θ N (ι.trans (stEquiv F B).symm)).trans (stEquiv F (rot 2 n B))⟩

omit [Algebra (ZMod 2) F] [CharP F 2] in
theorem m3_stRep_simple (hF : Nat.card F = 2 ^ n) {A : ℕ} (hA : A < 2 ^ n) :
    IsSimpleModule (MonoidAlgebra F (SLm F)) (stRep F A).asModule := by
  have := m3_simple (F := F) (L := F) Nat.prime_two hF hA
  exact IsSimpleModule.congr (N := (steinbergRep F F A).asModule) (stEquiv F A).symm

omit [CharP F 2] in
theorem m3_exists_atom_label (hF : Nat.card F = 2 ^ n)
    (hW : IsSimpleModule (MonoidAlgebra (ZMod 2) (SLm F)) σ.asModule) :
    ∃ (N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule)
      (B : ℕ), IsAtom N ∧ B < 2 ^ n ∧
        Nonempty (↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F B).asModule) := by
  have : Nontrivial σ.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra (ZMod 2) (SLm F)) σ.asModule
  have : Nontrivial W := σ.asModuleEquiv.symm.toEquiv.nontrivial
  let ρ := repXT σ
  have : Nontrivial (CFSG.Theory.Representation.extendScalars F σ).asModule := inferInstance
  have : Nontrivial ρ.asModule := (xEquiv σ).symm.toEquiv.nontrivial
  have : Finite (SLm F) := inferInstance
  have : Module.Finite F (XT 2 F W) := Module.Finite.equiv xtEquiv
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
  obtain ⟨A, hA, ⟨e⟩⟩ := m3_complete hF ↥(Subrepresentation.ofSubmodule' N).toSubmodule
    (Subrepresentation.ofSubmodule' N).toRepresentation hπsimple
  exact ⟨N, A, hNatom, hA, ⟨((submoduleEquivRep N).trans e).trans (stEquiv F A)⟩⟩

omit [Module.Finite (ZMod 2) W] in
theorem m3_orbSub_label (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule) {B : ℕ} (hB : B < 2 ^ n)
    (ι : ↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F B).asModule) (j : ℕ) :
    (rot 2 n)^[j] B < 2 ^ n ∧
      Nonempty (↥(orbSub σ N j) ≃ₗ[MonoidAlgebra F (SLm F)]
        (stRep F ((rot 2 n)^[j] B)).asModule) := by
  induction j with
  | zero => exact ⟨hB, ⟨ι⟩⟩
  | succ j ih =>
    obtain ⟨hlt, ⟨e⟩⟩ := ih
    rw [orbSub_succ, Function.iterate_succ_apply']
    exact ⟨mix11cD_rot_lt Nat.prime_two.one_lt hn hlt, m3_map_phi_label σ hn hF _ e⟩

theorem m3_orbit_structure (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (hW : IsSimpleModule (MonoidAlgebra (ZMod 2) (SLm F)) σ.asModule) :
    ∃ (N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule) (A : ℕ), IsAtom N ∧
      A < 2 ^ n ∧
      Nonempty (↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F A).asModule) ∧
      (∀ j, IsSimpleModule (MonoidAlgebra F (SLm F)) ↥(orbSub σ N j)) ∧
      ⨆ j, orbSub σ N j = ⊤ ∧
      IsSemisimpleModule (MonoidAlgebra F (SLm F)) (repXT σ).asModule := by
  obtain ⟨N, A, hNatom, hA, ⟨ι⟩⟩ := m3_exists_atom_label σ hF hW
  have hsimple : ∀ j, IsSimpleModule (MonoidAlgebra F (SLm F)) ↥(orbSub σ N j) := by
    intro j
    obtain ⟨hlt, ⟨e⟩⟩ := m3_orbSub_label σ hn hF N hA ι j
    have := m3_stRep_simple (F := F) hF hlt
    exact IsSimpleModule.congr (N := (stRep F ((rot 2 n)^[j] A)).asModule) e
  have htop := orbSub_iSup_eq_top σ hW N hNatom.1
  refine ⟨N, A, hNatom, hA, ⟨ι⟩, hsimple, htop, ?_⟩
  apply IsSemisimpleModule.of_sSup_simples_eq_top
  rw [eq_top_iff, ← htop]
  refine iSup_le fun j => le_sSup ?_
  exact hsimple j

omit [Module.Finite (ZMod 2) W] in
theorem m3_sigma_trivial_of_label_zero (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    {N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule}
    (hA : 0 < 2 ^ n) (ι : ↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F 0).asModule)
    (htop : ⨆ j, orbSub σ N j = ⊤) (g : SLm F) : σ g = 1 := by
  have hz : ∀ z : (stRep F 0).asModule, MonoidAlgebra.single g (1 : F) • z = z := fun z => by
    rw [Representation.single_smul, one_smul]
    exact stRep_zero_fixed g _
  have hfix : ∀ x : (repXT σ).asModule, MonoidAlgebra.single g (1 : F) • x = x := by
    intro x
    have hx : x ∈ ⨆ j, orbSub σ N j := by rw [htop]; trivial
    refine Submodule.iSup_induction (motive := fun x => MonoidAlgebra.single g (1 : F) • x = x)
      (orbSub σ N) hx ?_ ?_ ?_
    · intro j y hy
      obtain ⟨-, ⟨e⟩⟩ := m3_orbSub_label σ hn hF N hA ι j
      have e' : ↥(orbSub σ N j) ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F 0).asModule := by
        rw [rot_iterate_zero] at e
        exact e
      have h1 : MonoidAlgebra.single g (1 : F) • (⟨y, hy⟩ : ↥(orbSub σ N j)) = ⟨y, hy⟩ := by
        apply e'.injective
        rw [map_smul, hz]
      exact congrArg Subtype.val h1
    · simp
    · intro x y hx hy
      rw [smul_add, hx, hy]
  ext w
  have h := hfix ((repXT σ).asModuleEquiv.symm (xtEquiv (1 ⊗ₜ[ZMod 2] w)))
  rw [Representation.single_smul, one_smul] at h
  have h3 : (σ g).baseChange F (1 ⊗ₜ[ZMod 2] w) = 1 ⊗ₜ[ZMod 2] w := h
  have h5 : (1 : F) ⊗ₜ[ZMod 2] (σ g w) = 1 ⊗ₜ[ZMod 2] w := by simpa using h3
  simpa using one_tmul_injective h5

theorem m3_finrank_orbSub (hF : Nat.card F = 2 ^ n)
    {N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule} {A : ℕ} (hA : A < 2 ^ n)
    (ι : ↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F A).asModule) (j : ℕ) :
    Module.finrank F ↥(orbSub σ N j) = digitProd 2 n A := by
  have hfin : Module.finrank F (stRep F A).asModule = digitProd 2 n A := by
    rw [← m3_finrank (L := F) Nat.prime_two hF hA]
    exact (stRep F A).asModuleEquiv.finrank_eq
  induction j with
  | zero => rw [orbSub_zero, (ι.restrictScalars F).finrank_eq, hfin]
  | succ j ih => rw [orbSub_succ, finrank_map_phi, ih]

theorem m3_finrank_ge (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    {N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule} {A : ℕ} (hA : A < 2 ^ n)
    (ι : ↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F A).asModule)
    (hsimple : ∀ j, IsSimpleModule (MonoidAlgebra F (SLm F)) ↥(orbSub σ N j))
    (htop : ⨆ j, orbSub σ N j = ⊤) :
    rotPeriod 2 n A * digitProd 2 n A ≤ Module.finrank F (repXT σ).asModule := by
  classical
  have hp : 1 < 2 := Nat.one_lt_two
  let C := isotypicComponents (MonoidAlgebra F (SLm F)) (repXT σ).asModule
  have : Finite C := inferInstance
  have := Fintype.ofFinite C
  have hsemi : IsSemisimpleModule (MonoidAlgebra F (SLm F)) (repXT σ).asModule := by
    apply IsSemisimpleModule.of_sSup_simples_eq_top
    rw [eq_top_iff, ← htop]
    exact iSup_le fun j => le_sSup (hsimple j)
  have hind : iSupIndep (fun c : C => c.1) :=
    (sSupIndep_iff _).1 (sSupIndep_isotypicComponents _ _)
  have hsup : ⨆ c : C, c.1 = ⊤ := by
    rw [← sSup_eq_iSup']
    exact sSup_isotypicComponents _ _
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hsup
  let e : (DirectSum C fun c : C => ↥c.1) ≃ₗ[MonoidAlgebra F (SLm F)] (repXT σ).asModule :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap (fun c : C => c.1)) hint
  have h1 : Module.finrank F (repXT σ).asModule = ∑ c : C, Module.finrank F ↥c.1 := by
    rw [← (e.restrictScalars F).finrank_eq, Module.finrank_directSum]
  let g : Fin (rotPeriod 2 n A) → C := fun j =>
    ⟨isotypicComponent (MonoidAlgebra F (SLm F)) (repXT σ).asModule ↥(orbSub σ N j.1),
      ⟨orbSub σ N j.1, hsimple j.1, rfl⟩⟩
  have hle : ∀ j : Fin (rotPeriod 2 n A), orbSub σ N j.1 ≤ (g j).1 := fun j =>
    Submodule.le_isotypicComponent _
  have hginj : Function.Injective g := by
    intro j k hjk
    have hjk' : (g j).1 = (g k).1 := congrArg Subtype.val hjk
    have hle' : orbSub σ N j.1 ≤
        isotypicComponent (MonoidAlgebra F (SLm F)) (repXT σ).asModule ↥(orbSub σ N k.1) :=
      (hle j).trans hjk'.le
    have hiso : IsIsotypicOfType (MonoidAlgebra F (SLm F))
        ↥(isotypicComponent (MonoidAlgebra F (SLm F)) (repXT σ).asModule ↥(orbSub σ N k.1))
        ↥(orbSub σ N k.1) := IsIsotypicOfType.isotypicComponent _ _ _
    have := hsimple j.1
    obtain ⟨e'⟩ := (isIsotypicOfType_submodule_iff.mp hiso) (orbSub σ N j.1) hle'
    obtain ⟨hltj, ⟨ej⟩⟩ := m3_orbSub_label σ hn hF N hA ι j.1
    obtain ⟨hltk, ⟨ek⟩⟩ := m3_orbSub_label σ hn hF N hA ι k.1
    have e'' : (steinbergRep F F ((rot 2 n)^[j.1] A)).asModule ≃ₗ[MonoidAlgebra F (SLm F)]
        (steinbergRep F F ((rot 2 n)^[k.1] A)).asModule :=
      (stEquiv F _).trans (ej.symm.trans (e'.trans (ek.trans (stEquiv F _).symm)))
    have hlab : (rot 2 n)^[j.1] A = (rot 2 n)^[k.1] A := m3_inj hF hltj hltk ⟨e''⟩
    exact Fin.ext (Function.iterate_injOn_Iio_minimalPeriod j.2 k.2 hlab)
  have h2 : ∑ j : Fin (rotPeriod 2 n A), Module.finrank F ↥(g j).1 ≤
      ∑ c : C, Module.finrank F ↥c.1 := by
    have := Finset.sum_image (f := fun c : C => Module.finrank F ↥c.1) (s := Finset.univ) (g := g)
      (fun j _ k _ h => hginj h)
    rw [← this]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have h3 : ∀ j : Fin (rotPeriod 2 n A), digitProd 2 n A ≤ Module.finrank F ↥(g j).1 := by
    intro j
    rw [← m3_finrank_orbSub σ hF hA ι j.1]
    exact finrank_le_of_natCard_le (Nat.card_le_card_of_injective
      (Submodule.inclusion (hle j)) (Submodule.inclusion_injective (hle j)))
  calc rotPeriod 2 n A * digitProd 2 n A
      = ∑ _j : Fin (rotPeriod 2 n A), digitProd 2 n A := by simp
    _ ≤ ∑ j : Fin (rotPeriod 2 n A), Module.finrank F ↥(g j).1 :=
      Finset.sum_le_sum fun j _ => h3 j
    _ ≤ ∑ c : C, Module.finrank F ↥c.1 := h2
    _ = Module.finrank F (repXT σ).asModule := h1.symm

theorem m3_descent_data (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (hW : IsSimpleModule (MonoidAlgebra (ZMod 2) (SLm F)) σ.asModule) (hnt : ∃ g, σ g ≠ 1) :
    ∃ (N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule) (A : ℕ),
      A < 2 ^ n ∧ A ≠ 0 ∧
      Nonempty (↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F A).asModule) ∧
      (∀ j, IsSimpleModule (MonoidAlgebra F (SLm F)) ↥(orbSub σ N j)) ∧
      rotPeriod 2 n A * digitProd 2 n A ≤ Module.finrank (ZMod 2) W := by
  obtain ⟨N, A, hNatom, hA, ⟨ι⟩, hsimple, htop, -⟩ := m3_orbit_structure σ hn hF hW
  refine ⟨N, A, hA, ?_, ⟨ι⟩, hsimple, ?_⟩
  · rintro rfl
    obtain ⟨g, hg⟩ := hnt
    exact hg (m3_sigma_trivial_of_label_zero σ hn hF (by positivity) ι htop g)
  · have hX := m3_finrank_ge σ hn hF hA ι hsimple htop
    have hW1 : Module.finrank (ZMod 2) W = Module.finrank F (repXT σ).asModule := by
      let e : (repXT σ).asModule ≃ₗ[F] F ⊗[ZMod 2] W :=
        (repXT σ).asModuleEquiv.trans xtEquiv.symm
      rw [e.finrank_eq, Module.finrank_baseChange]
    rw [hW1]
    exact hX

end Orbit

end CFSG.CGT.PushingUpLit.CGT6
