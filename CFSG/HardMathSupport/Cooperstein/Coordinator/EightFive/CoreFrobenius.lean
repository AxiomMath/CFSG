module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.PermLattice
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Perfect

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open Equiv Equiv.Perm CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

variable {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] {m n : ℕ}

theorem exists_functional (Y : AddSubgroup X) (hY : Y ≠ ⊤) :
    ∃ f : X →+ ZMod 2, f ≠ 0 ∧ ∀ y ∈ Y, f y = 0 := by
  let p : Submodule (ZMod 2) X := AddSubgroup.toZModSubmodule 2 Y
  have hp : p < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hY
    rw [eq_top_iff]
    intro x _
    have : x ∈ p := h ▸ Submodule.mem_top
    exact this
  obtain ⟨f, hf, hfp⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hp inferInstance
  refine ⟨f.toAddMonoidHom, fun h => hf (LinearMap.ext fun x => ?_), fun y hy => ?_⟩
  · exact DFunLike.congr_fun h x
  · have : f y ∈ p.map f := Submodule.mem_map_of_mem (show y ∈ p from hy)
    rw [hfp] at this
    exact (Submodule.mem_bot _).1 this

theorem forall_fix_of_forall_altLift (ι : Fin m ↪ Fin n) {ω : Fin n}
    (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ ω) {P : alternatingGroup (Fin n) → Prop}
    (hP : ∀ σ, P (altLift ι σ)) (h : alternatingGroup (Fin n)) (hh : (h : Perm (Fin n)) ω = ω) :
    P h := by
  obtain ⟨σ, rfl⟩ := exists_altLift_eq ι hι h hh
  exact hP σ

@[expose] noncomputable def permSum (w : Fin n → X) : (Fin n → ZMod 2) →+ X where
  toFun y := ∑ p, y p • w p
  map_zero' := by simp
  map_add' y z := by simp [add_smul, Finset.sum_add_distrib]

theorem permSum_apply (w : Fin n → X) (y : Fin n → ZMod 2) :
    permSum w y = ∑ p, y p • w p :=
  rfl

theorem permSum_pairVec (w : Fin n → X) (a b : Fin n) :
    permSum w (pairVec a b) = w a + w b := by
  classical
  rw [permSum_apply]
  simp only [pairVec_apply, add_smul, ite_smul, one_smul, zero_smul, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem add_self_eq_zero' (x : X) : x + x = 0 := by
  have h : (1 + 1 : ZMod 2) = 0 := by decide
  rw [← one_smul (ZMod 2) x, ← add_smul, h, zero_smul]

theorem coe_pairEW (a b : Fin n) : ((pairEW a b : evenWeight n) : Fin n → ZMod 2) = pairVec a b :=
  funext fun p => by rw [pairEW_apply, pairVec_apply]

omit [Module (ZMod 2) X] in
@[expose] noncomputable def heartLift (φ : (Fin n → ZMod 2) →+ X) (h1 : φ (allOnes n) = 0) :
    altHeart n →+ X :=
  QuotientAddGroup.lift (evenWeightOnes n) (φ.comp (evenWeight n).subtype) fun x hx => by
    rw [AddMonoidHom.mem_ker]
    obtain ⟨c, hc⟩ := exists_forall_eq_of_mem_evenWeightOnes hx
    rcases zmod_two_cases c with rfl | rfl
    · have : (x : Fin n → ZMod 2) = 0 := funext hc
      simp [this]
    · have : (x : Fin n → ZMod 2) = allOnes n := funext fun i => hc i
      simp [this, h1]

omit [Module (ZMod 2) X] in
theorem heartLift_mk (φ : (Fin n → ZMod 2) →+ X) (h1 : φ (allOnes n) = 0) (x : evenWeight n) :
    heartLift φ h1 (x : altHeart n) = φ x :=
  rfl

theorem exists_heartEquiv_of_fixed (hn : 5 ≤ n) (ι : Fin m ↪ Fin n) {ω : Fin n}
    (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ ω) (r : alternatingGroup (Fin n) →* AddMonoid.End X)
    (hirr : ∀ Y : AddSubgroup X, (∀ g, ∀ y ∈ Y, r g y ∈ Y) → Y = ⊥ ∨ Y = ⊤)
    (hfix : ∀ x : X, (∀ g, r g x = x) → x = 0) {v : X} (hv0 : v ≠ 0)
    (hvK : ∀ σ : alternatingGroup (Fin m), r (altLift ι σ) v = v) :
    ∃ Θ : altHeart n ≃+ X,
      ∀ (g : alternatingGroup (Fin n)) z, Θ (altAct (g : Perm (Fin n)) z) = r g (Θ z) := by
  classical
  choose gp hgp using fun p : Fin n => exists_alt_apply_eq (by omega : 3 ≤ n) ω p
  have hvfix : ∀ h : alternatingGroup (Fin n), (h : Perm (Fin n)) ω = ω → r h v = v :=
    forall_fix_of_forall_altLift ι hι (P := fun h => r h v = v) hvK
  set w : Fin n → X := fun p => r (gp p) v with hw_def
  have hw : ∀ (g : alternatingGroup (Fin n)) p, r g (w p) = w ((g : Perm (Fin n)) p) := by
    intro g p
    set q := (g : Perm (Fin n)) p
    have hh : (((gp q)⁻¹ * (g * gp p) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply, hgp]
      exact inv_apply_of_apply (hgp q)
    have h1 : g * gp p = gp q * ((gp q)⁻¹ * (g * gp p)) := by group
    change r g (r (gp p) v) = r (gp q) v
    rw [← endo_mul_apply, h1, endo_mul_apply, hvfix _ hh]
  have hφ : ∀ (g : alternatingGroup (Fin n)) y,
      permSum w (actPM (g : Perm (Fin n)) y) = r g (permSum w y) := by
    intro g y
    rw [permSum_apply, permSum_apply, map_sum]
    rw [← Equiv.sum_comp (g : Perm (Fin n))]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [actPM_apply, perm_inv_apply_apply, ZMod.map_smul, hw]
  have hone : permSum w (allOnes n) = 0 := by
    refine hfix _ fun g => ?_
    rw [← hφ, actPM_allOnes]
  set Φ := heartLift (permSum w) hone with hΦ
  have hΦeq : ∀ (g : alternatingGroup (Fin n)) z, Φ (altAct (g : Perm (Fin n)) z) = r g (Φ z) := by
    intro g z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [altAct_mk, hΦ, heartLift_mk, heartLift_mk, ← hφ]
    rfl
  have hΦ0 : ∃ z, Φ z ≠ 0 := by
    by_contra h
    push Not at h
    have hwω : w ω = v := hvfix (gp ω) (hgp ω)
    have hwb : ∀ b, w b = v := by
      intro b
      by_cases hb : b = ω
      · rw [hb, hwω]
      have h1 := h (pairEW ω b : altHeart n)
      rw [hΦ, heartLift_mk, coe_pairEW, permSum_pairVec, hwω] at h1
      have h2 := congrArg (· + v) h1
      simp only [zero_add] at h2
      rw [add_comm, ← add_assoc, add_self_eq_zero', zero_add] at h2
      exact h2
    refine hv0 (hfix v fun g => ?_)
    rw [← hwω, hw, hwb, hwω]
  have hsurj : Function.Surjective Φ := by
    rcases hirr Φ.range (fun g y hy => by
      obtain ⟨z, rfl⟩ := hy
      exact ⟨_, hΦeq g z⟩) with h | h
    · obtain ⟨z, hz⟩ := hΦ0
      exact absurd (h ▸ (⟨z, rfl⟩ : Φ z ∈ Φ.range)) (fun h' => hz ((AddSubgroup.mem_bot).1 h'))
    · intro x
      exact (show x ∈ Φ.range from h ▸ AddSubgroup.mem_top x)
  have hinj : Function.Injective Φ := by
    rcases altHeart_irreducible (by omega) Φ.ker (fun σ hσ x hx => by
      rw [AddMonoidHom.mem_ker] at hx ⊢
      rw [← altAct_mk, hΦeq ⟨σ, hσ⟩, hx, map_zero]) with h | h
    · exact (injective_iff_map_eq_zero Φ).2 fun z hz => (AddSubgroup.mem_bot).1
        (h ▸ AddMonoidHom.mem_ker.2 hz)
    · obtain ⟨z, hz⟩ := hΦ0
      exact absurd (AddMonoidHom.mem_ker.1 (h ▸ AddSubgroup.mem_top z)) hz
  exact ⟨AddEquiv.ofBijective Φ ⟨hinj, hsurj⟩, hΦeq⟩

omit [Module (ZMod 2) X] in
theorem false_of_functional (hn : 5 ≤ n) (ι : Fin m ↪ Fin n) {ω : Fin n}
    (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ ω) (r : alternatingGroup (Fin n) →* AddMonoid.End X)
    (hirr : ∀ Y : AddSubgroup X, (∀ g, ∀ y ∈ Y, r g y ∈ Y) → Y = ⊥ ∨ Y = ⊤)
    (hK0 : ∀ v : X, (∀ σ : alternatingGroup (Fin m), r (altLift ι σ) v = v) → v = 0)
    (f : X →+ ZMod 2) (hf0 : f ≠ 0)
    (hfK : ∀ (σ : alternatingGroup (Fin m)) x, f (r (altLift ι σ) x) = f x) : False := by
  classical
  choose gp hgp using fun p : Fin n => exists_alt_apply_eq (by omega : 3 ≤ n) ω p
  have hffix : ∀ h : alternatingGroup (Fin n), (h : Perm (Fin n)) ω = ω → ∀ x, f (r h x) = f x :=
    forall_fix_of_forall_altLift ι hι (P := fun h => ∀ x, f (r h x) = f x) hfK
  let ψ : X →+ (Fin n → ZMod 2) :=
    { toFun := fun x p => f (r (gp p)⁻¹ x)
      map_zero' := by funext p; simp
      map_add' := fun x y => by funext p; simp }
  have hψapp : ∀ x p, ψ x p = f (r (gp p)⁻¹ x) := fun x p => rfl
  have hψ : ∀ (g : alternatingGroup (Fin n)) x, ψ (r g x) = actPM (g : Perm (Fin n)) (ψ x) := by
    intro g x
    funext p
    set q := (g : Perm (Fin n))⁻¹ p with hq
    have hh : (((gp p)⁻¹ * g * gp q : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply, hgp]
      rw [hq, perm_apply_inv_apply]
      exact inv_apply_of_apply (hgp p)
    have h1 : (gp p)⁻¹ * g = ((gp p)⁻¹ * g * gp q) * (gp q)⁻¹ := by group
    rw [actPM_apply, hψapp, hψapp, ← endo_mul_apply, h1, endo_mul_apply, hffix _ hh]
  obtain ⟨x₀, hx₀⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push Not at h
    exact hf0 (AddMonoidHom.ext h)
  have hψ0 : ψ x₀ ≠ 0 := by
    intro h
    apply hx₀
    have := congrFun h ω
    rw [hψapp, hffix _ (by
      rw [Subgroup.coe_inv]; exact inv_apply_of_apply (hgp ω))] at this
    exact this
  have hinj : Function.Injective ψ := by
    rcases hirr ψ.ker (fun g y hy => by
      rw [AddMonoidHom.mem_ker] at hy ⊢
      rw [hψ, hy, map_zero]) with h | h
    · exact (injective_iff_map_eq_zero ψ).2 fun z hz => (AddSubgroup.mem_bot).1
        (h ▸ AddMonoidHom.mem_ker.2 hz)
    · exact absurd (AddMonoidHom.mem_ker.1 (h ▸ AddSubgroup.mem_top x₀)) hψ0
  obtain ⟨u, ⟨x₁, rfl⟩, hu0, hufix⟩ := exists_fixed_of_invariant hn (Y := ψ.range)
    (fun σ hσ y hy => by
      obtain ⟨x, rfl⟩ := hy
      exact ⟨r ⟨σ, hσ⟩ x, hψ ⟨σ, hσ⟩ x⟩)
    (fun h => hψ0 ((AddSubgroup.mem_bot).1 (h ▸ (⟨x₀, rfl⟩ : ψ x₀ ∈ ψ.range)))) ω
  have hx₁ : x₁ = 0 := hK0 x₁ fun σ => hinj (by
    rw [hψ, hufix _ (altLift_apply_of_notMem ι σ (fun h => (hι ω).1 h rfl))])
  exact hu0 (by rw [hx₁, map_zero])

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
