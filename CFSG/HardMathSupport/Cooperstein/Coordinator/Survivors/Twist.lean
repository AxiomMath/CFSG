module

public import CFSG.Quasithin.Background.SmithCurtisDatum

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors

open CFSG.Quasithin.SmithCurtis CoxeterSystem

@[expose] def FrobTwist {K : Type*} [Field K] (θ : K ≃+* K) (V : Type*) : Type _ := V

section Twist

variable {K : Type*} [Field K] (θ : K ≃+* K) {V : Type*} [AddCommGroup V] [Module K V]

instance : AddCommGroup (FrobTwist θ V) := inferInstanceAs (AddCommGroup V)

instance : Module K (FrobTwist θ V) := Module.compHom V θ.toRingHom

variable {G : Type*} [Group G]

@[expose] def twistRep (ρ : Representation K G V) : Representation K G (FrobTwist θ V) where
  toFun g :=
    { toFun := fun v => (show FrobTwist θ V from ρ g (show V from v))
      map_add' := fun v w => map_add (ρ g) _ _
      map_smul' := fun c v => by
        change ρ g (θ c • (show V from v)) = θ c • ρ g (show V from v)
        exact (ρ g).map_smul (θ c) _ }
  map_one' := by
    ext v
    exact LinearMap.congr_fun (map_one ρ) (show V from v)
  map_mul' g h := by
    ext v
    exact LinearMap.congr_fun (map_mul ρ g h) (show V from v)

theorem isSimpleRep_twistRep {ρ : Representation K G V} (hρ : IsSimpleRep ρ) :
    IsSimpleRep (twistRep θ ρ) := by
  refine ⟨?_, fun W hW => ?_⟩
  · obtain ⟨⟨x, y, h⟩⟩ := hρ.1
    exact ⟨⟨(show FrobTwist θ V from x), (show FrobTwist θ V from y), h⟩⟩
  · let W' : Submodule K V :=
      { carrier := {v | (show FrobTwist θ V from v) ∈ W}
        add_mem' := fun {a b} ha hb => W.add_mem ha hb
        zero_mem' := W.zero_mem
        smul_mem' := fun c v hv => by
          obtain ⟨c', rfl⟩ := θ.surjective c
          exact W.smul_mem c' hv }
    have h1 : ∀ g : G, ∀ w ∈ W', ρ g w ∈ W' := fun g w hw => hW g _ hw
    rcases hρ.2 W' h1 with h | h
    · left
      refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
      have : (show V from v) ∈ W' := hv
      rw [h] at this
      have h0 : (show V from v) = 0 := (Submodule.mem_bot K).1 this
      exact h0
    · right
      refine (Submodule.eq_top_iff').2 fun v => ?_
      have : (show V from v) ∈ W' := by rw [h]; trivial
      exact this

variable {B : Type*} {M : CoxeterMatrix B} {W : Type*} [Group W] {cs : CoxeterSystem M W} {p : ℕ}
  (D : CurtisDatum G cs p)

theorem fixU_twist_iff (ρ : Representation K G V) (v : V) :
    (show FrobTwist θ V from v) ∈ D.fixU (twistRep θ ρ) ↔ v ∈ D.fixU ρ := Iff.rfl

theorem heckeT_twist [Finite G] (ρ : Representation K G V) (s : B) (v : V) :
    (show V from D.heckeT (twistRep θ ρ) s (show FrobTwist θ V from v)) = D.heckeT ρ s v := by
  have := Fintype.ofFinite (D.X s)
  rw [D.heckeT_apply, D.heckeT_apply]
  rfl

@[expose] def IsTypeGen [Finite G] (ρ : Representation K G V) (y : V) (χ : G → K) (J : Finset B)
    (H' : Set G) (tor : B → Type*) (hh : ∀ s, tor s → G) : Prop :=
  y ∈ D.fixU ρ ∧ y ≠ 0 ∧ (∀ h ∈ H', ρ h y = χ h • y) ∧
    ∀ s, s ∈ J ↔ (∀ u : tor s, χ (hh s u) = 1) ∧ D.heckeT ρ s y = 0

theorem IsTypeGen.twist [Finite G] {ρ : Representation K G V} {y : V} {χ : G → K}
    {J : Finset B} {H' : Set G} {tor : B → Type*} {hh : ∀ s, tor s → G}
    (ht : IsTypeGen D ρ y χ J H' tor hh) :
    IsTypeGen D (twistRep θ ρ) (show FrobTwist θ V from y) (fun g => θ.symm (χ g)) J H' tor hh := by
  obtain ⟨h1, h2, h3, h4⟩ := ht
  refine ⟨(fixU_twist_iff θ D ρ y).2 h1, h2, fun h hh' => ?_, fun s => ?_⟩
  · change ρ h y = θ (θ.symm (χ h)) • y
    rw [RingEquiv.apply_symm_apply]
    exact h3 h hh'
  · rw [h4 s]
    refine and_congr ?_ ?_
    · refine forall_congr' fun u => ?_
      change χ (hh s u) = 1 ↔ θ.symm (χ (hh s u)) = 1
      constructor
      · intro h
        rw [h]
        exact map_one _
      · intro h
        have := congrArg θ h
        rwa [RingEquiv.apply_symm_apply, map_one] at this
    · have := heckeT_twist θ D ρ s y
      exact ⟨fun h => this.trans h, fun h => this.symm.trans h⟩

end Twist

end CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
