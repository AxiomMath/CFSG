module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDOrb

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open scoped TensorProduct MonoidAlgebra

section RotParity

theorem rot_mod_two {p : ℕ} (hp : p % 2 = 1) (n A : ℕ) (hn : 0 < n) : rot p n A % 2 = A % 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hpm : p ^ m % 2 = 1 := by rw [Nat.pow_mod, hp]; simp
  simp only [rot, Nat.succ_sub_one]
  have h1 : ((A % p ^ m) * p + A / p ^ m) % 2 = ((A % p ^ m) % 2 + (A / p ^ m) % 2) % 2 := by
    rw [Nat.add_mod, Nat.mul_mod, hp]; simp
  have h2 : A % 2 = ((A % p ^ m) % 2 + (A / p ^ m) % 2) % 2 := by
    conv_lhs => rw [← Nat.mod_add_div A (p ^ m)]
    rw [Nat.add_mod, Nat.mul_mod, hpm]; simp
  rw [h1, h2]

end RotParity

section Main

variable {p n : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] [Algebra (ZMod p) F] [CharP F p]
  {W : Type} [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
  (σ : Representation (ZMod p) (SLm F) W)

omit [Module.Finite (ZMod p) W] [CharP F p] in
theorem hasConstituent_of_label (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n)
    (hF : Nat.card F = p ^ n)
    {N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule} {A : ℕ} (hA : A < p ^ n)
    (ι : ↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F A).asModule) : HasConstituent p F σ A := by
  have hsimp := ((hS p n Fact.out hp2 hn F hF).1 A hA).1
  have hnt : Nontrivial (steinbergRep F F A).asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra F (SLm F)) _
  refine ⟨(xEquiv σ).symm.toLinearMap ∘ₗ N.subtype ∘ₗ ι.symm.toLinearMap ∘ₗ
    (stEquiv F A).toLinearMap, ?_⟩
  intro h0
  obtain ⟨x, hx⟩ := exists_ne (0 : (steinbergRep F F A).asModule)
  apply hx
  have h1 := LinearMap.congr_fun h0 x
  have hinj : Function.Injective ((xEquiv σ).symm.toLinearMap ∘ₗ N.subtype ∘ₗ ι.symm.toLinearMap ∘ₗ
      (stEquiv F A).toLinearMap) :=
    (xEquiv σ).symm.injective.comp (N.injective_subtype.comp
      (ι.symm.injective.comp (stEquiv F A).injective))
  exact hinj (by simpa using h1)

omit [Module.Finite (ZMod p) W] [Finite F] in
theorem stRep_zero_fixed (g : SLm F) (v : StM F 0) : stRep F 0 g v = v := by
  have hconst : ∀ h : SLm F, funRep F F h (monoFun F F 0 0) = monoFun F F 0 0 := by
    intro h
    ext v
    simp [funRep, monoFun]
  have key : ∀ x ∈ steinbergSub F F 0, funRep F F g x = x := by
    intro x hx
    unfold steinbergSub at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨h, rfl⟩ := hy
      show funRep F F g (funRep F F h (monoFun F F 0 0)) = funRep F F h (monoFun F F 0 0)
      rw [hconst h, hconst g]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul a x _ hx => rw [map_smul, hx]
  exact Subtype.ext (key v.1 v.2)

theorem rot_zero (p n : ℕ) : rot p n 0 = 0 := by simp [rot]

theorem rot_iterate_zero (p n j : ℕ) : (rot p n)^[j] 0 = 0 :=
  Function.iterate_fixed (rot_zero p n) j

omit [CharP F p] [Module.Finite (ZMod p) W] in
theorem one_tmul_injective : Function.Injective (fun w : W => (1 : F) ⊗ₜ[ZMod p] w) :=
  Module.FaithfullyFlat.tensorProduct_mk_injective (A := ZMod p) (B := F) W

omit [Module.Finite (ZMod p) W] in
theorem sigma_trivial_of_label_zero (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n)
    (hF : Nat.card F = p ^ n)
    {N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule}
    (hA : 0 < p ^ n) (ι : ↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F 0).asModule)
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
      obtain ⟨-, ⟨e⟩⟩ := orbSub_label σ hS hp2 hn hF N hA ι j
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
  have h := hfix ((repXT σ).asModuleEquiv.symm (xtEquiv (1 ⊗ₜ[ZMod p] w)))
  rw [Representation.single_smul, one_smul] at h
  have h3 : (σ g).baseChange F (1 ⊗ₜ[ZMod p] w) = 1 ⊗ₜ[ZMod p] w := h
  have h5 : (1 : F) ⊗ₜ[ZMod p] (σ g w) = 1 ⊗ₜ[ZMod p] w := by simpa using h3
  simpa using one_tmul_injective h5

omit [Module.Finite (ZMod p) W] in
theorem negOne_acts_on_X (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n) (hF : Nat.card F = p ^ n)
    {N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule} {A : ℕ} (hA : A < p ^ n)
    (ι : ↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F A).asModule)
    (htop : ⨆ j, orbSub σ N j = ⊤) (x : (repXT σ).asModule) :
    MonoidAlgebra.single (T2.negOne F) (1 : F) • x = ((-1 : F) ^ A) • x := by
  have hp : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have hparity : ∀ j, (rot p n)^[j] A % 2 = A % 2 := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', rot_mod_two hp n _ hn, ih]
  have hx : x ∈ ⨆ j, orbSub σ N j := by rw [htop]; trivial
  refine Submodule.iSup_induction
    (motive := fun x => MonoidAlgebra.single (T2.negOne F) (1 : F) • x = ((-1 : F) ^ A) • x)
    (orbSub σ N) hx ?_ ?_ ?_
  · intro j y hy
    obtain ⟨hlt, ⟨e⟩⟩ := orbSub_label σ hS hp2 hn hF N hA ι j
    have hneg := ((hS p n Fact.out hp2 hn F hF).1 _ hlt).2.2.1
    have h1 : MonoidAlgebra.single (T2.negOne F) (1 : F) • (⟨y, hy⟩ : ↥(orbSub σ N j)) =
        ((-1 : F) ^ A) • (⟨y, hy⟩ : ↥(orbSub σ N j)) := by
      apply e.injective
      have hF1 : e (((-1 : F) ^ A) • (⟨y, hy⟩ : ↥(orbSub σ N j))) =
          ((-1 : F) ^ A) • e ⟨y, hy⟩ := e.toLinearMap.map_smul_of_tower _ _
      rw [hF1, e.map_smul, Representation.single_smul, one_smul]
      have h2 : (stRep F ((rot p n)^[j] A)) (T2.negOne F) ((stRep F ((rot p n)^[j] A)).asModuleEquiv (e ⟨y, hy⟩)) =
          ((-1 : F) ^ ((rot p n)^[j] A)) • ((stRep F ((rot p n)^[j] A)).asModuleEquiv (e ⟨y, hy⟩)) :=
        hneg _
      rw [h2]
      have h3 : ((-1 : F) ^ ((rot p n)^[j] A)) = (-1 : F) ^ A := by
        rw [neg_one_pow_eq_pow_mod_two, hparity j, ← neg_one_pow_eq_pow_mod_two]
      rw [h3]
      rfl
    exact congrArg Subtype.val h1
  · simp
  · intro x y hx hy
    rw [smul_add, hx, hy, smul_add]

omit [Module.Finite (ZMod p) W] in
theorem sigma_negOne_eq (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n) (hF : Nat.card F = p ^ n)
    {N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule} {A : ℕ} (hA : A < p ^ n)
    (ι : ↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F A).asModule)
    (htop : ⨆ j, orbSub σ N j = ⊤) (w : W) :
    σ (T2.negOne F) w = ((-1 : ZMod p) ^ A) • w := by
  have h := negOne_acts_on_X σ hS hp2 hn hF hA ι htop
    ((repXT σ).asModuleEquiv.symm (xtEquiv (1 ⊗ₜ[ZMod p] w)))
  have h2 := congrArg (repXT σ).asModuleEquiv h
  rw [Representation.single_smul, one_smul, LinearEquiv.map_smul] at h2
  have h3 : (σ (T2.negOne F)).baseChange F (1 ⊗ₜ[ZMod p] w) =
      ((-1 : F) ^ A) • ((1 : F) ⊗ₜ[ZMod p] w) := h2
  have h4 : ((-1 : F) ^ A) • ((1 : F) ⊗ₜ[ZMod p] w) =
      (1 : F) ⊗ₜ[ZMod p] (((-1 : ZMod p) ^ A) • w) := by
    have hneg1 : algebraMap (ZMod p) F (-1) = -1 :=
      (map_neg (algebraMap (ZMod p) F) 1).trans (congrArg Neg.neg (map_one _))
    have hc : ((-1 : F) ^ A) = (((-1 : ZMod p) ^ A) • (1 : F)) := by
      rw [Algebra.smul_def, mul_one, map_pow, hneg1]
    rw [hc, smul_assoc, one_smul, TensorProduct.tmul_smul]
  have h5 : (1 : F) ⊗ₜ[ZMod p] (σ (T2.negOne F) w) = (1 : F) ⊗ₜ[ZMod p] (((-1 : ZMod p) ^ A) • w) := by
    rw [← h4, ← h3]
    simp
  exact one_tmul_injective h5

end Main

end CFSG.GH74.GLS.Stage4.Rest
