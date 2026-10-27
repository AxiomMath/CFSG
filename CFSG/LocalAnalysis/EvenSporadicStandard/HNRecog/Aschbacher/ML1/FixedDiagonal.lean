module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Structure

public section

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

open Module CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private theorem card_A5 : Nat.card A5 = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]
  decide

private theorem a₀_ne_one : (a₀ : A5) ≠ 1 := by
  intro h
  have h5 := orderOf_a₀
  rw [h, orderOf_one] at h5
  exact absurd h5 (by decide)

private theorem false_of_ker_fst_eq_top
    (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (hS : Swap.StdHyp σ) {v : V} (hv0 : v ≠ 0)
    (S : Subgroup (A5 × A5)) (hSv : ∀ g, g ∈ S ↔ σ g v = v) (hcardS : Nat.card S = 60)
    (hker : ((MonoidHom.fst A5 A5).comp S.subtype).ker = ⊤) : False := by
  have hmem1 : ∀ s : S, (s : A5 × A5).1 = 1 := by
    intro s
    have hs : s ∈ ((MonoidHom.fst A5 A5).comp S.subtype).ker := by rw [hker]; trivial
    rw [MonoidHom.mem_ker] at hs
    simpa using hs
  have hinj : Function.Injective (fun s : S => (s : A5 × A5).2) := by
    intro s t hst
    apply Subtype.ext
    exact Prod.ext (by rw [hmem1 s, hmem1 t]) hst
  have hsurj : Function.Surjective (fun s : S => (s : A5 × A5).2) :=
    (hinj.bijective_of_nat_card_le (by rw [card_A5, hcardS])).surjective
  have hall : ∀ y : A5, ((1 : A5), y) ∈ S := by
    intro y
    obtain ⟨s, hs⟩ := hsurj y
    have hpair : (s : A5 × A5) = ((1 : A5), y) := Prod.ext (hmem1 s) hs
    rw [← hpair]
    exact s.2
  let U : Submodule (ZMod 2) V :=
    ⨅ y : A5, LinearMap.ker ((σ (1, y) : V →ₗ[ZMod 2] V) - 1)
  have memU : ∀ u : V, u ∈ U ↔ ∀ y : A5, σ (1, y) u = u := by
    intro u
    rw [show U = (⨅ y : A5, LinearMap.ker ((σ (1, y) : V →ₗ[ZMod 2] V) - 1)) from rfl,
      Submodule.mem_iInf]
    constructor
    · rintro h y
      have := h y
      rwa [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.End.one_apply] at this
    · intro h y
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.End.one_apply]
      exact h y
  have hvU : v ∈ U := by
    rw [memU]
    intro y
    exact (hSv ((1 : A5), y)).mp (hall y)
  have hinv : ∀ g : A5 × A5, ∀ u ∈ U, σ g u ∈ U := by
    intro g u hu
    obtain ⟨x, y'⟩ := g
    rw [memU] at hu ⊢
    intro y
    calc σ (1, y) (σ (x, y') u)
        = σ ((1, y) * (x, y')) u := by rw [← LinearEquiv.mul_apply, ← map_mul]
      _ = σ (x, y * y') u := by
            rw [show ((1 : A5), y) * (x, y') = (x, y * y') by ext <;> simp]
      _ = σ ((x, y') * (1, y'⁻¹ * y * y')) u := by
            rw [show (x, y') * (1, y'⁻¹ * y * y') = (x, y * y') by
              ext <;> simp [mul_assoc]]
      _ = σ (x, y') (σ (1, y'⁻¹ * y * y') u) := by rw [map_mul, LinearEquiv.mul_apply]
      _ = σ (x, y') u := by rw [hu (y'⁻¹ * y * y')]
  have hUne : U ≠ ⊥ := by
    intro hbot
    have : v ∈ (⊥ : Submodule (ZMod 2) V) := by rw [← hbot]; exact hvU
    exact hv0 (by simpa using this)
  have hUtop : U = ⊤ := (hS.irr U hinv).resolve_left hUne
  have hsigma : σ ((1 : A5), a₀) = 1 := by
    ext u
    have hu : u ∈ U := by rw [hUtop]; trivial
    simpa using (memU u).mp hu a₀
  have hpair : ((1 : A5), a₀) = (1 : A5 × A5) :=
    hS.inj (hsigma.trans (map_one σ).symm)
  exact a₀_ne_one (congrArg Prod.snd hpair)

private theorem false_of_ker_snd_eq_top
    (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (hS : Swap.StdHyp σ) {v : V} (hv0 : v ≠ 0)
    (S : Subgroup (A5 × A5)) (hSv : ∀ g, g ∈ S ↔ σ g v = v) (hcardS : Nat.card S = 60)
    (hker : ((MonoidHom.snd A5 A5).comp S.subtype).ker = ⊤) : False := by
  have hmem2 : ∀ s : S, (s : A5 × A5).2 = 1 := by
    intro s
    have hs : s ∈ ((MonoidHom.snd A5 A5).comp S.subtype).ker := by rw [hker]; trivial
    rw [MonoidHom.mem_ker] at hs
    simpa using hs
  have hinj : Function.Injective (fun s : S => (s : A5 × A5).1) := by
    intro s t hst
    apply Subtype.ext
    exact Prod.ext hst (by rw [hmem2 s, hmem2 t])
  have hsurj : Function.Surjective (fun s : S => (s : A5 × A5).1) :=
    (hinj.bijective_of_nat_card_le (by rw [card_A5, hcardS])).surjective
  have hall : ∀ y : A5, (y, (1 : A5)) ∈ S := by
    intro y
    obtain ⟨s, hs⟩ := hsurj y
    have hpair : (s : A5 × A5) = (y, (1 : A5)) := Prod.ext hs (hmem2 s)
    rw [← hpair]
    exact s.2
  let U : Submodule (ZMod 2) V :=
    ⨅ y : A5, LinearMap.ker ((σ (y, 1) : V →ₗ[ZMod 2] V) - 1)
  have memU : ∀ u : V, u ∈ U ↔ ∀ y : A5, σ (y, 1) u = u := by
    intro u
    rw [show U = (⨅ y : A5, LinearMap.ker ((σ (y, 1) : V →ₗ[ZMod 2] V) - 1)) from rfl,
      Submodule.mem_iInf]
    constructor
    · rintro h y
      have := h y
      rwa [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.End.one_apply] at this
    · intro h y
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.End.one_apply]
      exact h y
  have hvU : v ∈ U := by
    rw [memU]
    intro y
    exact (hSv (y, (1 : A5))).mp (hall y)
  have hinv : ∀ g : A5 × A5, ∀ u ∈ U, σ g u ∈ U := by
    intro g u hu
    obtain ⟨x', y'⟩ := g
    rw [memU] at hu ⊢
    intro y
    calc σ (y, 1) (σ (x', y') u)
        = σ ((y, 1) * (x', y')) u := by rw [← LinearEquiv.mul_apply, ← map_mul]
      _ = σ (y * x', y') u := by
            rw [show ((y : A5), (1 : A5)) * (x', y') = (y * x', y') by ext <;> simp]
      _ = σ ((x', y') * (x'⁻¹ * y * x', 1)) u := by
            rw [show (x', y') * (x'⁻¹ * y * x', (1 : A5)) = (y * x', y') by
              ext <;> simp [mul_assoc]]
      _ = σ (x', y') (σ (x'⁻¹ * y * x', 1) u) := by rw [map_mul, LinearEquiv.mul_apply]
      _ = σ (x', y') u := by rw [hu (x'⁻¹ * y * x')]
  have hUne : U ≠ ⊥ := by
    intro hbot
    have : v ∈ (⊥ : Submodule (ZMod 2) V) := by rw [← hbot]; exact hvU
    exact hv0 (by simpa using this)
  have hUtop : U = ⊤ := (hS.irr U hinv).resolve_left hUne
  have hsigma : σ (a₀, (1 : A5)) = 1 := by
    ext u
    have hu : u ∈ U := by rw [hUtop]; trivial
    simpa using (memU u).mp hu a₀
  have hpair : (a₀, (1 : A5)) = (1 : A5 × A5) :=
    hS.inj (hsigma.trans (map_one σ).symm)
  exact a₀_ne_one (congrArg Prod.fst hpair)

theorem exists_fixed_graph (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (hS : Swap.StdHyp σ) (v : V) (hv0 : v ≠ 0)
    (S : Subgroup (A5 × A5)) (hSv : ∀ g, g ∈ S ↔ σ g v = v) (hSA : Nonempty (S ≃* A5)) :
    ∃ β : A5 ≃* A5, ∀ x : A5, σ (x, β x) v = v := by
  obtain ⟨e⟩ := hSA
  have hcardS : Nat.card S = 60 := by
    rw [Nat.card_congr e.toEquiv, card_A5]
  haveI : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup S := e.isSimpleGroup
  let p₁ : S →* A5 := (MonoidHom.fst A5 A5).comp S.subtype
  let p₂ : S →* A5 := (MonoidHom.snd A5 A5).comp S.subtype
  have hinj1 : Function.Injective p₁ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal p₁.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff p₁).mp h
    · exact (false_of_ker_fst_eq_top σ hS hv0 S hSv hcardS h).elim
  have hinj2 : Function.Injective p₂ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal p₂.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff p₂).mp h
    · exact (false_of_ker_snd_eq_top σ hS hv0 S hSv hcardS h).elim
  have hbij1 : Function.Bijective p₁ :=
    hinj1.bijective_of_nat_card_le (by rw [card_A5, hcardS])
  have hbij2 : Function.Bijective p₂ :=
    hinj2.bijective_of_nat_card_le (by rw [card_A5, hcardS])
  let e₁ : S ≃* A5 := MulEquiv.ofBijective p₁ hbij1
  let e₂ : S ≃* A5 := MulEquiv.ofBijective p₂ hbij2
  refine ⟨e₁.symm.trans e₂, fun x => ?_⟩
  have hfix : σ ((e₁.symm x : S) : A5 × A5) v = v :=
    (hSv ((e₁.symm x : S) : A5 × A5)).mp (e₁.symm x).2
  have hfst : ((e₁.symm x : S) : A5 × A5).1 = x :=
    MulEquiv.apply_symm_apply e₁ x
  have hsnd : ((e₁.symm x : S) : A5 × A5).2 = (e₁.symm.trans e₂) x := rfl
  have hpair : ((e₁.symm x : S) : A5 × A5) = (x, (e₁.symm.trans e₂) x) :=
    Prod.ext hfst hsnd
  rw [hpair] at hfix
  exact hfix

end CFSG.EvenSporadicStandard.HNRecog.ML1
