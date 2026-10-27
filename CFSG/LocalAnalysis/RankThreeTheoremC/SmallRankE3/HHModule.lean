module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.HHChar

public section

universe u v

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.HHModule

open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.HHChar

section Chars

variable (K : Type*) [Field K] (V : Type*) [Group V]

def chars : Submodule K (V → K) where
  carrier := {f | ∀ a b : V, f (a * b) = f a + f b}
  add_mem' := by
    intro f g hf hg a b
    simp only [Pi.add_apply, hf a b, hg a b]
    ring
  zero_mem' := by
    intro a b
    simp
  smul_mem' := by
    intro c f hf a b
    simp only [Pi.smul_apply, hf a b, smul_eq_mul]
    ring

variable {K V}

lemma mem_chars {f : V → K} : f ∈ chars K V ↔ ∀ a b : V, f (a * b) = f a + f b := Iff.rfl

instance instFiniteDimensionalChars [Finite V] : FiniteDimensional K (chars K V) :=
  inferInstance

lemma char_one {f : V → K} (hf : f ∈ chars K V) : f 1 = 0 := by
  have h := hf 1 1
  rw [mul_one] at h
  linear_combination -h

lemma char_inv {f : V → K} (hf : f ∈ chars K V) (v : V) : f v⁻¹ = - f v := by
  have h := hf v v⁻¹
  rw [mul_inv_cancel, char_one hf] at h
  linear_combination -h

lemma char_mul_inv {f : V → K} (hf : f ∈ chars K V) (a b : V) :
    f (a * b⁻¹) = f a - f b := by
  rw [hf, char_inv hf]
  ring

def rhoLin (σ : MulAut V) : chars K V →ₗ[K] chars K V where
  toFun f := ⟨fun v => (f : V → K) (σ⁻¹ v), fun a b => by
    beta_reduce
    rw [map_mul]
    exact f.2 _ _⟩
  map_add' f g := rfl
  map_smul' c f := rfl

@[simp] lemma rhoLin_apply (σ : MulAut V) (f : chars K V) (v : V) :
    ((rhoLin σ f : chars K V) : V → K) v = (f : V → K) (σ⁻¹ v) := by rfl

variable (K V)

def rhoEnd : MulAut V →* Module.End K (chars K V) where
  toFun := rhoLin
  map_one' := by
    ext f v
    simp
  map_mul' σ τ := by
    ext f v
    simp [mul_inv_rev]

def rho : MulAut V →* (Module.End K (chars K V))ˣ := (rhoEnd K V).toHomUnits

variable {K V}

@[simp] lemma rho_apply (σ : MulAut V) (f : chars K V) (v : V) :
    ((((rho K V σ : (Module.End K (chars K V))ˣ) : Module.End K (chars K V)) f :
      chars K V) : V → K) v = (f : V → K) (σ⁻¹ v) := by rfl

private lemma exists_add_map_ne_zero {F M : Type*} [Field F] [AddCommGroup M] [Module F M] {m : M}
    (hm : m ≠ 0) : ∃ f : M → F, (∀ x y : M, f (x + y) = f x + f y) ∧ f m ≠ 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual F M, φ m ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hm ((Module.forall_dual_apply_eq_zero_iff F m).1 hcon)
  exact ⟨φ, fun x y => map_add φ x y, hφ⟩

lemma exists_char_gen [Finite V] (hcomm : ∀ a b : V, a * b = b * a) {ℓ : ℕ} [Fact ℓ.Prime]
    (hexp : ∀ v : V, v ^ ℓ = 1) (ι : ZMod ℓ →+* K) {a : V} (ha : a ≠ 1) :
    ∃ f ∈ chars K V, f a ≠ 0 := by
  let _ : CommGroup V := { (inferInstance : Group V) with mul_comm := hcomm }
  have hnsmul : ∀ x : Additive V, ℓ • x = 0 := fun x =>
    congrArg Additive.ofMul (hexp (Additive.toMul x))
  let _ : Module (ZMod ℓ) (Additive V) := AddCommGroup.zmodModule hnsmul
  have hne : Additive.ofMul a ≠ 0 := fun h => ha (by simpa using h)
  obtain ⟨f, hfadd, hfne⟩ := exists_add_map_ne_zero (F := ZMod ℓ) (M := Additive V) hne
  refine ⟨fun v => ι (f (Additive.ofMul v)), mem_chars.2 fun x y => ?_, ?_⟩
  · simp [ofMul_mul, hfadd, map_add]
  · intro h
    exact hfne (ι.injective (by simpa using h))

variable (K V)

lemma rho_injective_gen [Finite V] (hcomm : ∀ a b : V, a * b = b * a) {ℓ : ℕ} [Fact ℓ.Prime]
    (hexp : ∀ v : V, v ^ ℓ = 1) (ι : ZMod ℓ →+* K) : Function.Injective (rho K V) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hfix : ∀ f ∈ chars K V, ∀ w : V, f (σ⁻¹ w) = f w := by
    intro f hf w
    have h := congrArg (fun u : (Module.End K (chars K V))ˣ =>
      ((u : Module.End K (chars K V)) ⟨f, hf⟩ : chars K V).1 w) hσ
    simpa using h
  ext v
  by_contra hne
  have hc : σ v * v⁻¹ ≠ 1 := fun h => hne (by simpa using mul_inv_eq_one.1 h)
  obtain ⟨f, hf, hfc⟩ := exists_char_gen hcomm hexp ι hc
  apply hfc
  rw [char_mul_inv hf]
  have h := hfix f hf (σ v)
  rw [MulAut.inv_apply_self] at h
  rw [h, sub_self]

variable {K V}

lemma rho_fix [Finite V] (hcomm : ∀ a b : V, a * b = b * a) (x : MulAut V)
    (hfix : ∀ v : V, x v = v → v = 1) (g : chars K V)
    (hg : ((rho K V x : (Module.End K (chars K V))ˣ) : Module.End K (chars K V)) g = g) :
    g = 0 := by
  let _ : CommGroup V := { (inferInstance : Group V) with mul_comm := hcomm }
  obtain ⟨f, hf⟩ := g
  have hfx : ∀ v, f (x⁻¹ v) = f v := fun v => congrFun (congrArg Subtype.val hg) v
  let θ : V →* V := MonoidHom.mk' (fun v => x⁻¹ v * v⁻¹) (by
    intro a b
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _)
  have hθ : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hu' : x⁻¹ u = u := mul_inv_eq_one.1 hu
    apply hfix u
    calc x u = x (x⁻¹ u) := by rw [hu']
      _ = u := MulAut.apply_inv_self V x u
  have hsurj := Finite.injective_iff_surjective.1 hθ
  refine Subtype.ext (funext fun c => ?_)
  obtain ⟨v, rfl⟩ := hsurj c
  show f (x⁻¹ v * v⁻¹) = 0
  rw [char_mul_inv hf, hfx, sub_self]

end Chars

section Main

theorem kl_mulAut_aux_gen {K : Type} [Field K] [IsAlgClosed K] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] {V : Type u} [Group V] [Finite V] (hcomm : ∀ a b : V, a * b = b * a)
    (hexp : ∀ v : V, v ^ ℓ = 1) {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hqp : q ≠ p) (hpℓ : p ≠ ℓ) (hqℓ : q ≠ ℓ)
    (S : Subgroup (MulAut V)) (hS : IsPGroup q S) (x : MulAut V)
    (hx : x ∈ Subgroup.normalizer (S : Set (MulAut V))) (hxp : x ^ p = 1)
    (hfix : ∀ v : V, x v = v → v = 1) : ∀ s ∈ S, x * s = s * x := by
  have hinj := rho_injective_gen K V hcomm hexp (ZMod.castHom (dvd_refl ℓ) K)
  have hfin : Finite (S.map (rho K V)) :=
    Finite.of_surjective _ ((rho K V).subgroupMap_surjective S)
  have hQ : IsPGroup q (S.map (rho K V)) :=
    hS.of_surjective ((rho K V).subgroupMap S) ((rho K V).subgroupMap_surjective S)
  have hxQ : rho K V x ∈ Subgroup.normalizer ((S.map (rho K V) : Subgroup _) : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨x * s * x⁻¹, (Subgroup.mem_normalizer_iff.1 hx s).1 hs, ?_⟩
      simp [map_mul, map_inv]
    · rintro ⟨s', hs', hs'eq⟩
      refine ⟨x⁻¹ * s' * x, ?_, ?_⟩
      · refine (Subgroup.mem_normalizer_iff.1 hx (x⁻¹ * s' * x)).2 ?_
        rwa [show x * (x⁻¹ * s' * x) * x⁻¹ = s' by group]
      · rw [map_mul, map_mul, map_inv, hs'eq]
        group
  have hxp' : (rho K V x) ^ p = 1 := by rw [← map_pow, hxp, map_one]
  have hcore := kl_core_char (K := K) (ℓ := ℓ) hp2 hq2 hqp hpℓ hqℓ
    (S.map (rho K V)) hQ (rho K V x) hxQ hxp' (fun g hg => rho_fix hcomm x hfix g hg)
  intro s hs
  apply hinj
  rw [map_mul, map_mul]
  exact hcore (rho K V s) (Subgroup.mem_map_of_mem _ hs)

theorem kl_mulAut_gen {V : Type u} [Group V] [Finite V] (hcomm : ∀ a b : V, a * b = b * a)
    {ℓ : ℕ} [Fact ℓ.Prime] (hexp : ∀ v : V, v ^ ℓ = 1) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hqp : q ≠ p) (hpℓ : p ≠ ℓ) (hqℓ : q ≠ ℓ)
    (S : Subgroup (MulAut V)) (hS : IsPGroup q S) (x : MulAut V)
    (hx : x ∈ Subgroup.normalizer (S : Set (MulAut V))) (hxp : x ^ p = 1)
    (hfix : ∀ v : V, x v = v → v = 1) : ∀ s ∈ S, x * s = s * x :=
  kl_mulAut_aux_gen (K := AlgebraicClosure (ZMod ℓ)) hcomm hexp hp2 hq2 hqp hpℓ hqℓ S hS x hx
    hxp hfix

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.HHModule
