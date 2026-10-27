module

public import CFSG.HardMathSupport.GuralnickMalle.InvariantSimple
public import CFSG.Quasithin.Background.A1cModuleSemisimple

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.Quasithin
open scoped MonoidAlgebra

variable {E X M D : Type*}
  [AddCommGroup X] [Module (ZMod 2) X]
  [Group M] [Group D]

@[expose] def centralizerSubmonoid (σ : Representation (ZMod 2) M X) :
    Submonoid (Module.End (ZMod 2) X) where
  carrier := {s | ∀ g, s ∘ₗ σ g = σ g ∘ₗ s}
  one_mem' := by
    intro g
    ext x
    rfl
  mul_mem' := by
    intro s t hs ht g
    ext x
    change s (t (σ g x)) = σ g (s (t x))
    rw [show t (σ g x) = σ g (t x) from congrArg (fun f => f x) (ht g)]
    rw [show s (σ g (t x)) = σ g (s (t x)) from congrArg (fun f => f (t x)) (hs g)]

section GroupAlgebra

variable [Module (MonoidAlgebra (ZMod 2) M) X]
variable [IsScalarTower (ZMod 2) (MonoidAlgebra (ZMod 2) M) X]

@[expose] noncomputable def commLinear (σ : Representation (ZMod 2) M X)
    (hsmul : ∀ (g : M) (x : X),
      (MonoidAlgebra.single g (1 : ZMod 2)) • x = σ g x)
    (s : Module.End (ZMod 2) X) (hs : ∀ g, s ∘ₗ σ g = σ g ∘ₗ s) :
    X →ₗ[MonoidAlgebra (ZMod 2) M] X where
  toFun := s
  map_add' := map_add s
  map_smul' r x := by
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add r₁ r₂ h₁ h₂ => simp [add_smul, h₁, h₂]
    | single g a =>
        change s ((MonoidAlgebra.single g a) • x) =
          (MonoidAlgebra.single g a) • s x
        rw [single_smul_eq σ hsmul g a x, single_smul_eq σ hsmul g a (s x)]
        rw [map_smul, show s (σ g x) = σ g (s x) from congrArg (fun f => f x) (hs g)]

@[simp]
theorem commLinear_apply (σ : Representation (ZMod 2) M X)
    (hsmul : ∀ (g : M) (x : X),
      (MonoidAlgebra.single g (1 : ZMod 2)) • x = σ g x)
    (s : Module.End (ZMod 2) X) (hs : ∀ g, s ∘ₗ σ g = σ g ∘ₗ s) (x : X) :
    commLinear σ hsmul s hs x = s x := rfl

end GroupAlgebra

noncomputable def commutingSelectorData [Finite X] [Finite D]
    (σ : Representation (ZMod 2) M X) (δ : Representation (ZMod 2) D X) (hD : IsPGroup 2 D)
    (S : Set (X →ₗ[ZMod 2] X)) (hS : ∀ s ∈ S, ∀ g, s ∘ₗ σ g = σ g ∘ₗ s)
    (hnorm : ∀ d g, ∃ g', ∀ x, δ d (σ g x) = σ g' (δ d x))
    (hsimp : ∀ W : Submodule (ZMod 2) X, (∀ g, ∀ w ∈ W, σ g w ∈ W) →
      (∀ s ∈ S, ∀ w ∈ W, s w ∈ W) → W = ⊥ ∨ W = ⊤)
    [Nontrivial X] :
    { Z : Submodule (ZMod 2) X // Z ≠ ⊥ ∧
      (∀ g, ∀ z ∈ Z, σ g z ∈ Z) ∧
      (∀ W : Submodule (ZMod 2) X, W ≤ Z →
        (∀ g, ∀ w ∈ W, σ g w ∈ W) → W = ⊥ ∨ W = Z) ∧
      (∀ d, ∀ z ∈ Z, δ d z ∈ Z) ∧
      (∀ g, (∀ z ∈ Z, σ g z = z) → σ g = 1) } := by
  classical
  letI : Module (MonoidAlgebra (ZMod 2) M) X :=
    Module.compHom X σ.asAlgebraHom.toRingHom
  haveI : IsScalarTower (ZMod 2) (MonoidAlgebra (ZMod 2) M) X :=
    ZMod.instIsScalarTower 2 (MonoidAlgebra (ZMod 2) M) X
  have hsmul : ∀ (g : M) (x : X),
      (MonoidAlgebra.single g (1 : ZMod 2)) • x = σ g x := by
    intro g x
    change (σ.asAlgebraHom (MonoidAlgebra.single g (1 : ZMod 2))) x = σ g x
    rw [Representation.asAlgebraHom_single]
    simp
  haveI : Finite (Submodule (MonoidAlgebra (ZMod 2) M) X) :=
    Finite.of_injective (fun W : Submodule (MonoidAlgebra (ZMod 2) M) X => (W : Set X))
      SetLike.coe_injective
  let T : Submodule (MonoidAlgebra (ZMod 2) M) X :=
    Classical.choose (IsAtomic.exists_atom (α := Submodule (MonoidAlgebra (ZMod 2) M) X))
  have hTatom : IsAtom T :=
    Classical.choose_spec (IsAtomic.exists_atom (α := Submodule (MonoidAlgebra (ZMod 2) M) X))
  have hTsimple : IsSimpleModule (MonoidAlgebra (ZMod 2) M) T :=
    (isSimpleModule_iff_isAtom).2 hTatom
  haveI : IsSimpleModule (MonoidAlgebra (ZMod 2) M) T := hTsimple
  have hTinv : ∀ g, ∀ w ∈ T, σ g w ∈ T :=
    isInvariant_of_submodule σ hsmul T
  let C : Submonoid (Module.End (ZMod 2) X) := centralizerSubmonoid σ
  have hSC : S ⊆ C := fun s hs => hS s hs
  let φ : C → (X →ₗ[MonoidAlgebra (ZMod 2) M] X) :=
    fun s => commLinear σ hsmul s.1 s.2
  have hφ_apply : ∀ (s : C) (x : X), φ s x = s.1 x := fun s x => rfl
  let I : Submodule (ZMod 2) X :=
    ⨆ s : C, (T.restrictScalars (ZMod 2)).map (s.1 : X →ₗ[ZMod 2] X)
  have hT_map_le : ∀ g,
      (T.restrictScalars (ZMod 2)).map (σ g) ≤ T.restrictScalars (ZMod 2) := by
    intro g
    rintro _ ⟨t, ht, rfl⟩
    exact hTinv g t ht
  have hT_le_I : T.restrictScalars (ZMod 2) ≤ I := by
    intro t ht
    refine Submodule.mem_iSup_of_mem (⟨1, C.one_mem⟩ : C) ?_
    simpa using ht
  have hIσ : ∀ g, I.map (σ g) ≤ I := by
    intro g
    dsimp only [I]
    rw [Submodule.map_iSup]
    refine iSup_le fun s => ?_
    have hcomm : s.1 ∘ₗ σ g = σ g ∘ₗ s.1 := s.2 g
    calc
      ((T.restrictScalars (ZMod 2)).map s.1).map (σ g)
          = (T.restrictScalars (ZMod 2)).map (σ g ∘ₗ s.1) := by
            rw [← Submodule.map_comp]
      _ = (T.restrictScalars (ZMod 2)).map (s.1 ∘ₗ σ g) := by rw [← hcomm]
      _ = ((T.restrictScalars (ZMod 2)).map (σ g)).map s.1 := by
            rw [Submodule.map_comp]
      _ ≤ (T.restrictScalars (ZMod 2)).map s.1 :=
            Submodule.map_mono (hT_map_le g)
      _ ≤ I := le_iSup (fun s : C => (T.restrictScalars (ZMod 2)).map s.1) s
  have hIS : ∀ t ∈ S, I.map t ≤ I := by
    intro t ht
    have htC : t ∈ C := hSC ht
    dsimp only [I]
    rw [Submodule.map_iSup]
    refine iSup_le fun s => ?_
    have hEq : ((T.restrictScalars (ZMod 2)).map s.1).map t =
        (T.restrictScalars (ZMod 2)).map ((⟨t, htC⟩ * s : C).1) := by
      rw [← Submodule.map_comp]
      congr 1
    rw [hEq]
    exact le_iSup (fun s : C => (T.restrictScalars (ZMod 2)).map s.1) (⟨t, htC⟩ * s)
  have hT_ne : T ≠ ⊥ :=
    Submodule.nontrivial_iff_ne_bot.mp (IsSimpleModule.nontrivial (MonoidAlgebra (ZMod 2) M) T)
  have hI_ne : I ≠ ⊥ := by
    intro hbot
    exact hT_ne (le_bot_iff.mp (hT_le_I.trans hbot.le))
  have hIinv : ∀ g, ∀ w ∈ I, σ g w ∈ I := by
    intro g w hw
    exact hIσ g (Submodule.mem_map_of_mem (f := σ g) hw)
  have hIsinv : ∀ t ∈ S, ∀ w ∈ I, t w ∈ I := by
    intro t ht w hw
    exact hIS t ht (Submodule.mem_map_of_mem (f := t) hw)
  have hI_top : I = ⊤ := by
    rcases hsimp I hIinv hIsinv with h | h
    · exact (hI_ne h).elim
    · exact h
  have hI_le_iso : I ≤ (isotypicComponent (MonoidAlgebra (ZMod 2) M) X T).restrictScalars
      (ZMod 2) := by
    refine iSup_le fun s => ?_
    have hEq : (T.map (φ s)).restrictScalars (ZMod 2) =
        (T.restrictScalars (ZMod 2)).map (s.1 : X →ₗ[ZMod 2] X) := by
      ext x
      constructor
      · intro hx
        obtain ⟨t, ht, rfl⟩ := (Submodule.mem_map).mp hx
        exact Submodule.mem_map_of_mem (f := (s.1 : X →ₗ[ZMod 2] X)) ht
      · intro hx
        obtain ⟨t, ht, rfl⟩ := (Submodule.mem_map).mp hx
        exact Submodule.mem_map_of_mem (f := φ s) ht
    change (T.restrictScalars (ZMod 2)).map (s.1 : X →ₗ[ZMod 2] X) ≤
      (isotypicComponent (MonoidAlgebra (ZMod 2) M) X T).restrictScalars (ZMod 2)
    rw [← hEq]
    intro x hx
    exact Submodule.map_le_isotypicComponent T (φ s) hx
  have hIsoComp : isotypicComponent (MonoidAlgebra (ZMod 2) M) X T = ⊤ := by
    apply Submodule.restrictScalars_injective (ZMod 2)
    exact top_unique (hI_top ▸ hI_le_iso)
  have hIsoType : IsIsotypicOfType (MonoidAlgebra (ZMod 2) M) X T :=
    IsIsotypicOfType.of_isotypicComponent_eq_top hIsoComp
  have hX2 : ∀ x : X, x + x = 0 := by
    intro x
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [← two_smul (ZMod 2) x, h2, zero_smul]
  let Ω := {ω : Submodule (MonoidAlgebra (ZMod 2) M) X //
    Nonempty (↥ω ≃ₗ[MonoidAlgebra (ZMod 2) M] ↥T)}
  have hoddΩ : Odd (Nat.card Ω) := by
    have hodd : Odd (Nat.card {ω : Submodule (MonoidAlgebra (ZMod 2) M) X //
        ω ≤ ⊤ ∧ Nonempty (↥ω ≃ₗ[MonoidAlgebra (ZMod 2) M] ↥T)}) :=
      Twist.odd_card_iso_submodules (R := MonoidAlgebra (ZMod 2) M) (M := X)
        (L := T) (N := ⊤) hX2 le_top
    let e : Ω ≃ {ω : Submodule (MonoidAlgebra (ZMod 2) M) X //
        ω ≤ ⊤ ∧ Nonempty (↥ω ≃ₗ[MonoidAlgebra (ZMod 2) M] ↥T)} :=
      { toFun := fun ω => ⟨ω.1, le_top, ω.2⟩
        invFun := fun ω => ⟨ω.1, ω.2.2⟩
        left_inv := fun ω => rfl
        right_inv := fun ω => rfl }
    rw [Nat.card_congr e]
    exact hodd
  haveI : Finite Ω :=
    Finite.of_injective (fun ω : Ω => ω.1) (fun a b h => Subtype.ext h)
  let isoData : ∀ (d : D) (ω : Ω),
      { e : mapSubmodule σ δ hsmul hnorm d ω.1 ≃ₗ[MonoidAlgebra (ZMod 2) M] T //
        True } :=
    fun d ω => by
      letI : IsSimpleModule (MonoidAlgebra (ZMod 2) M) ω.1 :=
        IsSimpleModule.congr ω.2.some
      exact ⟨Classical.choice (@hIsoType (mapSubmodule σ δ hsmul hnorm d ω.1)
        (mapSubmodule_isSimple σ δ hsmul hnorm d)), trivial⟩
  let smulΩ : D → Ω → Ω := fun d ω =>
    ⟨mapSubmodule σ δ hsmul hnorm d ω.1, ⟨(isoData d ω).1⟩⟩
  let act : MulAction D Ω :=
    { smul := smulΩ
      one_smul := fun ω => by
        apply Subtype.ext
        exact mapSubmodule_one σ δ hsmul hnorm ω.1
      mul_smul := fun d₁ d₂ ω => by
        apply Subtype.ext
        exact mapSubmodule_mul σ δ hsmul hnorm d₁ d₂ ω.1 }
  letI : MulAction D Ω := act
  have hnotdvd : ¬ 2 ∣ Nat.card Ω := by
    obtain ⟨m, hm⟩ := hoddΩ
    rintro ⟨k, hk⟩
    rw [hk] at hm
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Z : Ω := Classical.choose (hD.nonempty_fixed_point_of_prime_not_dvd_card Ω hnotdvd)
  have hZfix : Z ∈ MulAction.fixedPoints D Ω :=
    Classical.choose_spec (hD.nonempty_fixed_point_of_prime_not_dvd_card Ω hnotdvd)
  have hfix : ∀ d, d • Z = Z := (MulAction.mem_fixedPoints).1 hZfix
  let Zb : Submodule (ZMod 2) X := Z.1.restrictScalars (ZMod 2)
  have hZsimple : IsSimpleModule (MonoidAlgebra (ZMod 2) M) Z.1 :=
    IsSimpleModule.congr Z.2.some
  have hZb_ne : Zb ≠ ⊥ := by
    intro h
    have hZbot : Z.1 = ⊥ := by
      apply Submodule.restrictScalars_injective (ZMod 2)
      simpa [Zb] using h
    exact (Submodule.nontrivial_iff_ne_bot.mp
      (IsSimpleModule.nontrivial (MonoidAlgebra (ZMod 2) M) Z.1)) hZbot
  have hZinv : ∀ g, ∀ z ∈ Zb, σ g z ∈ Zb := by
    intro g z hz
    have h : σ g z ∈ Z.1 :=
      isInvariant_of_submodule σ hsmul Z.1 g z (by simpa [Zb] using hz)
    simpa [Zb] using h
  have hZb_simple : ∀ W : Submodule (ZMod 2) X, W ≤ Zb →
      (∀ g, ∀ w ∈ W, σ g w ∈ W) → W = ⊥ ∨ W = Zb := by
    intro W hWle hWinv
    let W' := submoduleOfIsInvariant σ hsmul W hWinv
    have hW'le : W' ≤ Z.1 := by
      intro x hx
      exact hWle (by simpa [W'] using hx)
    have hZatom : IsAtom Z.1 := (isSimpleModule_iff_isAtom).1 hZsimple
    rcases hZatom.le_iff.1 hW'le with h | h
    · left
      apply Submodule.ext
      intro x
      have hx' : x ∈ W' ↔ x ∈ (⊥ : Submodule (MonoidAlgebra (ZMod 2) M) X) := by
        rw [h]
      simpa [W'] using hx'
    · right
      apply Submodule.ext
      intro x
      have hx' : x ∈ W' ↔ x ∈ Z.1 := by rw [h]
      simpa [W', Zb] using hx'
  have hdZ : ∀ d, mapSubmodule σ δ hsmul hnorm d Z.1 = Z.1 :=
    fun d => congrArg Subtype.val (hfix d)
  have hZb_Dinv : ∀ d, ∀ z ∈ Zb, δ d z ∈ Zb := by
    intro d z hz
    have hmem : δ d z ∈ mapSubmodule σ δ hsmul hnorm d Z.1 := by
      rw [mem_mapSubmodule]
      exact ⟨z, by simpa [Zb] using hz, rfl⟩
    rw [hdZ d] at hmem
    simpa [Zb] using hmem
  let J : Submodule (ZMod 2) X :=
    ⨆ s : C, Zb.map (s.1 : X →ₗ[ZMod 2] X)
  have hZb_map_le : ∀ g, Zb.map (σ g) ≤ Zb := by
    intro g
    rintro _ ⟨z, hz, rfl⟩
    exact hZinv g z hz
  have hZ_le_J : Zb ≤ J := by
    intro z hz
    refine Submodule.mem_iSup_of_mem (⟨1, C.one_mem⟩ : C) ?_
    simpa using hz
  have hJ_ne : J ≠ ⊥ := by
    intro hbot
    exact hZb_ne (le_bot_iff.mp (hZ_le_J.trans hbot.le))
  have hJσ : ∀ g, J.map (σ g) ≤ J := by
    intro g
    dsimp only [J]
    rw [Submodule.map_iSup]
    refine iSup_le fun s => ?_
    have hcomm : s.1 ∘ₗ σ g = σ g ∘ₗ s.1 := s.2 g
    calc
      (Zb.map s.1).map (σ g) = Zb.map (σ g ∘ₗ s.1) := by rw [← Submodule.map_comp]
      _ = Zb.map (s.1 ∘ₗ σ g) := by rw [← hcomm]
      _ = (Zb.map (σ g)).map s.1 := by rw [Submodule.map_comp]
      _ ≤ Zb.map s.1 := Submodule.map_mono (hZb_map_le g)
      _ ≤ J := le_iSup (fun s : C => Zb.map s.1) s
  have hJS : ∀ t ∈ S, J.map t ≤ J := by
    intro t ht
    have htC : t ∈ C := hSC ht
    dsimp only [J]
    rw [Submodule.map_iSup]
    refine iSup_le fun s => ?_
    have hEq : (Zb.map s.1).map t = Zb.map ((⟨t, htC⟩ * s : C).1) := by
      rw [← Submodule.map_comp]
      congr 1
    rw [hEq]
    exact le_iSup (fun s : C => Zb.map s.1) (⟨t, htC⟩ * s)
  have hJinv : ∀ g, ∀ w ∈ J, σ g w ∈ J := by
    intro g w hw
    exact hJσ g (Submodule.mem_map_of_mem (f := σ g) hw)
  have hJsinv : ∀ t ∈ S, ∀ w ∈ J, t w ∈ J := by
    intro t ht w hw
    exact hJS t ht (Submodule.mem_map_of_mem (f := t) hw)
  have hJ_top : J = ⊤ := by
    rcases hsimp J hJinv hJsinv with h | h
    · exact (hJ_ne h).elim
    · exact h
  refine ⟨Zb, hZb_ne, hZinv, hZb_simple, hZb_Dinv, ?_⟩
  intro g hg
  ext x
  have hxJ : x ∈ J := by rw [hJ_top]; trivial
  let F : Submodule (ZMod 2) X :=
    { carrier := {x | σ g x = x}
      add_mem' := by
        intro y z hy hz
        change σ g (y + z) = y + z
        rw [map_add, hy, hz]
      zero_mem' := by
        change σ g 0 = 0
        simp
      smul_mem' := by
        intro a y hy
        change σ g (a • y) = a • y
        rw [map_smul, hy] }
  have hJ_le_fix : J ≤ F := by
    refine iSup_le fun s => ?_
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
    have hcomm : s.1 (σ g z) = σ g (s.1 z) := congrArg (fun f => f z) (s.2 g)
    change σ g (s.1 z) = s.1 z
    rw [← hcomm, hg z hz]
  have hxfix : σ g x = x := hJ_le_fix hxJ
  simpa using hxfix

theorem exists_invariant_simple_of_commuting [Finite X] [Finite D]
    (σ : Representation (ZMod 2) M X) (δ : Representation (ZMod 2) D X) (hD : IsPGroup 2 D)
    (S : Set (X →ₗ[ZMod 2] X)) (hS : ∀ s ∈ S, ∀ g, s ∘ₗ σ g = σ g ∘ₗ s)
    (hnorm : ∀ d g, ∃ g', ∀ x, δ d (σ g x) = σ g' (δ d x))
    (hsimp : ∀ W : Submodule (ZMod 2) X, (∀ g, ∀ w ∈ W, σ g w ∈ W) →
      (∀ s ∈ S, ∀ w ∈ W, s w ∈ W) → W = ⊥ ∨ W = ⊤)
    [Nontrivial X] :
    ∃ Z : Submodule (ZMod 2) X, Z ≠ ⊥ ∧
      (∀ g, ∀ z ∈ Z, σ g z ∈ Z) ∧
      (∀ W : Submodule (ZMod 2) X, W ≤ Z →
        (∀ g, ∀ w ∈ W, σ g w ∈ W) → W = ⊥ ∨ W = Z) ∧
      (∀ d, ∀ z ∈ Z, δ d z ∈ Z) ∧
      (∀ g, (∀ z ∈ Z, σ g z = z) → σ g = 1) := by
  obtain ⟨Z, hZ⟩ := commutingSelectorData σ δ hD S hS hnorm hsimp
  exact ⟨Z, hZ⟩

end CFSG.HardMathSupport.GuralnickMalle
