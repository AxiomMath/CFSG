module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.FieldPart.Action

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

theorem exists_semilinear {K : Type} [Field K] (f : K →+ K) (hf : Function.Bijective f)
    (hφ : ∀ μ : K, μ ≠ 0 → ∃ φ : K, ∀ c, f (μ * c) = φ * f c) :
    ∃ (a : Kˣ) (σ : K ≃+* K), ∀ c, f c = a * σ c := by
  have h1 : f 1 ≠ 0 := by
    intro h
    have : f 1 = f 0 := by rw [h, map_zero]
    exact one_ne_zero (hf.1 this)
  set a : Kˣ := Units.mk0 (f 1) h1 with ha
  have hmul : ∀ c d : K, (a : K)⁻¹ * f (c * d) = ((a : K)⁻¹ * f c) * ((a : K)⁻¹ * f d) := by
    intro c d
    by_cases hc : c = 0
    · subst hc
      simp
    obtain ⟨φ, hφ'⟩ := hφ c hc
    have h2 : f c = φ * f 1 := by simpa using hφ' 1
    rw [hφ' d, h2]
    have hne : (a : K) ≠ 0 := a.ne_zero
    simp only [ha, Units.val_mk0]
    field_simp
  let σ₀ : K →+* K :=
    { toFun := fun c => (a : K)⁻¹ * f c
      map_one' := inv_mul_cancel₀ h1
      map_mul' := hmul
      map_zero' := by simp
      map_add' := by intro c d; simp [mul_add] }
  have hbij : Function.Bijective σ₀ := by
    constructor
    · intro c d h
      apply hf.1
      have h' : (a : K)⁻¹ * f c = (a : K)⁻¹ * f d := h
      exact mul_left_cancel₀ (inv_ne_zero a.ne_zero) h'
    · intro d
      obtain ⟨c, hc⟩ := hf.2 ((a : K) * d)
      refine ⟨c, ?_⟩
      show (a : K)⁻¹ * f c = d
      rw [hc]
      field_simp
  refine ⟨a, RingEquiv.ofBijective σ₀ hbij, fun c => ?_⟩
  show f c = (a : K) * ((a : K)⁻¹ * f c)
  field_simp

theorem semilinear_unique {K : Type} [Field K] {a a' : Kˣ} {σ σ' : K ≃+* K}
    (h : ∀ c, (a : K) * σ c = a' * σ' c) : a = a' ∧ σ = σ' := by
  have ha : a = a' := Units.ext (by simpa using h 1)
  refine ⟨ha, RingEquiv.ext fun c => ?_⟩
  have := h c
  rw [ha] at this
  exact mul_left_cancel₀ a'.ne_zero this


variable {K : Type} [Field K]

@[expose] def Semilin (β : MulAut (adjointGroup Tag.D4 K)) (a : Kˣ) (σ : K ≃+* K) : Prop :=
  ∀ c : K, β (zElt K c) = zElt K ((a : K) * σ c)

theorem Semilin.unique {β : MulAut (adjointGroup Tag.D4 K)} {a a' : Kˣ} {σ σ' : K ≃+* K}
    (h : Semilin β a σ) (h' : Semilin β a' σ') : a = a' ∧ σ = σ' :=
  semilinear_unique fun c => zElt_injective ((h c).symm.trans (h' c))

theorem Semilin.one : Semilin (1 : MulAut (adjointGroup Tag.D4 K)) 1 (RingEquiv.refl K) := by
  intro c
  simp

theorem Semilin.mul {β β' : MulAut (adjointGroup Tag.D4 K)} {a a' : Kˣ} {σ σ' : K ≃+* K}
    (h : Semilin β a σ) (h' : Semilin β' a' σ') :
    Semilin (β * β') (a * Units.map σ.toRingHom.toMonoidHom a') (σ * σ') := by
  intro c
  rw [MulAut.mul_apply, h' c, h]
  congr 1
  simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    RingEquiv.toRingHom_eq_coe, map_mul, RingEquiv.coe_toRingHom, RingAut.mul_apply, mul_assoc]

@[expose] def StabU (K : Type) [Field K] : Subgroup (MulAut (adjointGroup Tag.D4 K)) where
  carrier := {β | (UP K).map β.toMonoidHom = UP K}
  mul_mem' := by
    intro β β' hβ hβ'
    show (UP K).map (β * β').toMonoidHom = UP K
    rw [show (β * β').toMonoidHom = β.toMonoidHom.comp β'.toMonoidHom from rfl,
      ← Subgroup.map_map]
    rw [show (UP K).map β'.toMonoidHom = UP K from hβ']
    exact hβ
  one_mem' := by
    show (UP K).map (1 : MulAut (adjointGroup Tag.D4 K)).toMonoidHom = UP K
    exact Subgroup.map_id _
  inv_mem' := by
    intro β hβ
    show (UP K).map (β⁻¹).toMonoidHom = UP K
    have h : (UP K).map β.toMonoidHom = UP K := hβ
    conv_lhs => rw [← h]
    rw [Subgroup.map_map]
    show (UP K).map ((β⁻¹ * β).toMonoidHom) = UP K
    rw [inv_mul_cancel]
    exact Subgroup.map_id _

theorem mem_StabU {β : MulAut (adjointGroup Tag.D4 K)} :
    β ∈ StabU K ↔ (UP K).map β.toMonoidHom = UP K := Iff.rfl

theorem mem_UP_of_mem_StabU {β : MulAut (adjointGroup Tag.D4 K)} (hβ : β ∈ StabU K)
    {u : adjointGroup Tag.D4 K} (hu : u ∈ UP K) : β u ∈ UP K := by
  have : β u ∈ (UP K).map β.toMonoidHom := Subgroup.mem_map_of_mem _ hu
  rwa [mem_StabU.1 hβ] at this

theorem map_ZP_of_mem_StabU {β : MulAut (adjointGroup Tag.D4 K)} (hβ : β ∈ StabU K) :
    (ZP K).map β.toMonoidHom = ZP K := by
  rw [ZP, Subgroup.map_lowerCentralSeries, mem_StabU.1 hβ]

theorem exists_fun_of_mem_StabU {β : MulAut (adjointGroup Tag.D4 K)} (hβ : β ∈ StabU K) (c : K) :
    ∃ d : K, β (zElt K c) = zElt K d := by
  have h : β (zElt K c) ∈ ZP K := by
    have : β (zElt K c) ∈ (ZP K).map β.toMonoidHom := Subgroup.mem_map_of_mem _ (zElt_mem_ZP c)
    rwa [map_ZP_of_mem_StabU hβ] at this
  obtain ⟨d, hd⟩ := mem_ZP_iff.1 h
  exact ⟨d, hd⟩

theorem mem_normalizer_of_mem_StabU {β : MulAut (adjointGroup Tag.D4 K)} (hβ : β ∈ StabU K)
    {x : adjointGroup Tag.D4 K}
    (hx : x ∈ Subgroup.normalizer ((UP K : Subgroup (adjointGroup Tag.D4 K)) :
      Set (adjointGroup Tag.D4 K))) :
    β x ∈ Subgroup.normalizer ((UP K : Subgroup (adjointGroup Tag.D4 K)) :
      Set (adjointGroup Tag.D4 K)) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  have hβ' : β⁻¹ ∈ StabU K := inv_mem hβ
  intro u
  constructor
  · intro hu
    have h1 : β⁻¹ u ∈ UP K := mem_UP_of_mem_StabU hβ' hu
    have h2 := (hx (β⁻¹ u)).1 h1
    have h3 := mem_UP_of_mem_StabU hβ h2
    simpa [map_mul, map_inv] using h3
  · intro hu
    have h1 : β⁻¹ (β x * u * (β x)⁻¹) ∈ UP K := mem_UP_of_mem_StabU hβ' hu
    have h2 : x * β⁻¹ u * x⁻¹ ∈ UP K := by simpa [map_mul, map_inv] using h1
    have h3 := (hx (β⁻¹ u)).2 h2
    have h4 := mem_UP_of_mem_StabU hβ h3
    simpa using h4

theorem exists_semilin {β : MulAut (adjointGroup Tag.D4 K)} (hβ : β ∈ StabU K) :
    ∃ (a : Kˣ) (σ : K ≃+* K), Semilin β a σ := by
  choose f hf using exists_fun_of_mem_StabU hβ
  have hadd : ∀ c d, f (c + d) = f c + f d := fun c d => by
    apply zElt_injective
    rw [← hf, zElt_add, map_mul, hf, hf, zElt_add]
  let F : K →+ K := ⟨⟨f, by
    apply zElt_injective
    rw [← hf, zElt_zero, map_one]⟩, hadd⟩
  have hFinj : Function.Injective F := fun c d h => by
    have h1 : β (zElt K c) = β (zElt K d) := by rw [hf, hf]; exact congrArg (zElt K) h
    exact zElt_injective (β.injective h1)
  have hFsurj : Function.Surjective F := by
    intro d
    obtain ⟨c, hc⟩ := exists_fun_of_mem_StabU (inv_mem hβ) d
    refine ⟨c, zElt_injective ?_⟩
    show zElt K (f c) = zElt K d
    rw [← hf, ← hc]
    simp
  have hφ : ∀ μ : K, μ ≠ 0 → ∃ φ : K, ∀ c, F (μ * c) = φ * F c := by
    intro μ hμ
    set u : Kˣ := Units.mk0 μ hμ
    obtain ⟨φ, hφ⟩ := exists_scalar_of_mem_normalizer
      (mem_normalizer_of_mem_StabU hβ (hElt_mem_normalizer (K := K) u))
    refine ⟨φ, fun c => ?_⟩
    apply zElt_injective
    have h1 := congrArg β (hElt_mul_zElt u c)
    rw [map_mul, map_mul, map_inv, hf c, hf ((u : K) * c)] at h1
    have h2 := hφ (f c)
    have h3 : zElt K ((φ : K) * f c) = zElt K (f ((u : K) * c)) := h2.symm.trans h1
    exact h3.symm
  obtain ⟨a, σ, h⟩ := exists_semilinear F ⟨hFinj, hFsurj⟩ hφ
  exact ⟨a, σ, fun c => by rw [hf, show f c = F c from rfl, h]⟩

theorem semilin_conj {x : adjointGroup Tag.D4 K}
    (hx : x ∈ Subgroup.normalizer ((UP K : Subgroup (adjointGroup Tag.D4 K)) :
      Set (adjointGroup Tag.D4 K))) :
    ∃ a : Kˣ, Semilin (MulAut.conj x) a (RingEquiv.refl K) := by
  obtain ⟨μ, hμ⟩ := exists_scalar_of_mem_normalizer hx
  exact ⟨μ, fun c => by simpa using hμ c⟩

theorem conj_mem_StabU {x : adjointGroup Tag.D4 K}
    (hx : x ∈ Subgroup.normalizer ((UP K : Subgroup (adjointGroup Tag.D4 K)) :
      Set (adjointGroup Tag.D4 K))) : MulAut.conj x ∈ StabU K := by
  rw [mem_StabU]
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hx u).1 hu
  · intro hy
    refine ⟨x⁻¹ * y * x, ?_, by group⟩
    exact (Subgroup.mem_normalizer_iff.1 hx (x⁻¹ * y * x)).2 (by simpa [mul_assoc] using hy)

end CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart
