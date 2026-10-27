module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sylow
public import CFSG.LocalAnalysis.OddStandard.Seitz77Thompson
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.OddStandard.Seitz77

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

section Coordinates

variable {F : Type} [Field F]

@[expose] def uelt (a b c : F) : unipAll F := ⟨unipU F a b c, a, b, c, rfl⟩

@[expose] def coordA (g : unipAll F) : F :=
  ((g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1

@[expose] def coordB (g : unipAll F) : F :=
  ((g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2

@[expose] def coordC (g : unipAll F) : F :=
  ((g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2

theorem coe_uelt (a b c : F) :
    ((uelt a b c : unipAll F) : SpecialLinearGroup (Fin 3) F) = unipU F a b c := rfl

@[simp] theorem coordA_uelt (a b c : F) : coordA (uelt a b c) = a := by
  simp [coordA, coe_uelt, coe_unipU]

@[simp] theorem coordB_uelt (a b c : F) : coordB (uelt a b c) = b := by
  simp [coordB, coe_uelt, coe_unipU]

@[simp] theorem coordC_uelt (a b c : F) : coordC (uelt a b c) = c := by
  simp [coordC, coe_uelt, coe_unipU]

theorem exists_uelt (g : unipAll F) : ∃ a b c : F, g = uelt a b c := by
  obtain ⟨g, a, b, c, rfl⟩ := g
  exact ⟨a, b, c, rfl⟩

theorem uelt_inj {a b c a' b' c' : F} :
    (uelt a b c : unipAll F) = uelt a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' :=
  ⟨fun h => unipU_inj (congrArg Subtype.val h), fun ⟨h1, h2, h3⟩ => by rw [h1, h2, h3]⟩

theorem uelt_coords (g : unipAll F) : uelt (coordA g) (coordB g) (coordC g) = g := by
  obtain ⟨a, b, c, rfl⟩ := exists_uelt g
  simp

theorem uelt_mul (a b c a' b' c' : F) :
    (uelt a b c : unipAll F) * uelt a' b' c' = uelt (a + a') (b + b') (c + c' + a * b') :=
  Subtype.ext (unipU_mul a b c a' b' c')

@[simp] theorem uelt_zero : (uelt 0 0 0 : unipAll F) = 1 := Subtype.ext unipU_zero

theorem uelt_inv (a b c : F) : (uelt a b c : unipAll F)⁻¹ = uelt (-a) (-b) (-c + a * b) :=
  Subtype.ext (unipU_inv a b c)

theorem uelt_eq_mul (a b c : F) : (uelt a b c : unipAll F) = uelt a b 0 * uelt 0 0 c := by
  rw [uelt_mul]
  simp

theorem coordA_mul (g h : unipAll F) : coordA (g * h) = coordA g + coordA h := by
  obtain ⟨a, b, c, rfl⟩ := exists_uelt g
  obtain ⟨a', b', c', rfl⟩ := exists_uelt h
  simp [uelt_mul]

theorem coordB_mul (g h : unipAll F) : coordB (g * h) = coordB g + coordB h := by
  obtain ⟨a, b, c, rfl⟩ := exists_uelt g
  obtain ⟨a', b', c', rfl⟩ := exists_uelt h
  simp [uelt_mul]

theorem coordC_mul (g h : unipAll F) :
    coordC (g * h) = coordC g + coordC h + coordA g * coordB h := by
  obtain ⟨a, b, c, rfl⟩ := exists_uelt g
  obtain ⟨a', b', c', rfl⟩ := exists_uelt h
  simp [uelt_mul]

theorem coordA_inv (g : unipAll F) : coordA g⁻¹ = -coordA g := by
  obtain ⟨a, b, c, rfl⟩ := exists_uelt g
  simp [uelt_inv]

theorem coordB_inv (g : unipAll F) : coordB g⁻¹ = -coordB g := by
  obtain ⟨a, b, c, rfl⟩ := exists_uelt g
  simp [uelt_inv]

@[simp] theorem coordA_one : coordA (1 : unipAll F) = 0 := by
  rw [← uelt_zero, coordA_uelt]

@[simp] theorem coordB_one : coordB (1 : unipAll F) = 0 := by
  rw [← uelt_zero, coordB_uelt]

@[simp] theorem coordC_one : coordC (1 : unipAll F) = 0 := by
  rw [← uelt_zero, coordC_uelt]

theorem commute_unipAll_iff' (g h : unipAll F) :
    g * h = h * g ↔ coordA g * coordB h = coordA h * coordB g := by
  obtain ⟨a, b, c, rfl⟩ := exists_uelt g
  obtain ⟨a', b', c', rfl⟩ := exists_uelt h
  rw [uelt_mul, uelt_mul, uelt_inj]
  simp only [coordA_uelt, coordB_uelt]
  constructor
  · rintro ⟨-, -, h3⟩
    linear_combination h3
  · intro h
    refine ⟨add_comm _ _, add_comm _ _, ?_⟩
    linear_combination h

theorem commute_of_coords_eq_zero {g : unipAll F} (hA : coordA g = 0) (hB : coordB g = 0)
    (h : unipAll F) : g * h = h * g :=
  (commute_unipAll_iff' g h).2 (by rw [hA, hB, zero_mul, mul_zero])

theorem coords_eq_zero_of_commute {g : unipAll F} (hg : ∀ h : unipAll F, g * h = h * g) :
    coordA g = 0 ∧ coordB g = 0 := by
  have h1 := (commute_unipAll_iff' g (uelt 1 0 0)).1 (hg _)
  have h2 := (commute_unipAll_iff' g (uelt 0 1 0)).1 (hg _)
  simp only [coordA_uelt, coordB_uelt] at h1 h2
  exact ⟨by linear_combination h2, by linear_combination -h1⟩

theorem mem_center_unipAll (g : unipAll F) :
    g ∈ center (unipAll F) ↔ coordA g = 0 ∧ coordB g = 0 := by
  rw [Subgroup.mem_center_iff]
  exact ⟨fun h => coords_eq_zero_of_commute fun x => (h x).symm,
    fun h x => (commute_of_coords_eq_zero h.1 h.2 x).symm⟩

@[expose] def graphFun (g : unipAll F) : unipAll F :=
  uelt (coordB g) (coordA g) (coordC g + coordA g * coordB g)

theorem graphFun_uelt (a b c : F) : graphFun (uelt a b c) = uelt b a (c + a * b) := by
  simp [graphFun]

@[expose] def diagFun (σ : F ≃+* F) (l m : F) (g : unipAll F) : unipAll F :=
  uelt (l * σ (coordA g)) (m * σ (coordB g)) (l * m * σ (coordC g))

theorem diagFun_uelt (σ : F ≃+* F) (l m a b c : F) :
    diagFun σ l m (uelt a b c) = uelt (l * σ a) (m * σ b) (l * m * σ c) := by
  simp [diagFun]

theorem diagFun_mul (σ : F ≃+* F) (l m : F) (g h : unipAll F) :
    diagFun σ l m (g * h) = diagFun σ l m g * diagFun σ l m h := by
  obtain ⟨a, b, c, rfl⟩ := exists_uelt g
  obtain ⟨a', b', c', rfl⟩ := exists_uelt h
  rw [uelt_mul, diagFun_uelt, diagFun_uelt, diagFun_uelt, uelt_mul, uelt_inj]
  refine ⟨?_, ?_, ?_⟩ <;> simp only [map_add, map_mul] <;> ring

end Coordinates

section Subgroups

variable {F : Type} [Field F]

variable (F) in
@[expose] def radOne : Subgroup (unipAll F) := (unipOne F).subgroupOf (unipAll F)

variable (F) in
@[expose] def radTwo : Subgroup (unipAll F) := (unipTwo F).subgroupOf (unipAll F)

variable (F) in
@[expose] def radCenter : Subgroup (unipAll F) := (unipCenter F).subgroupOf (unipAll F)

theorem mem_radOne (g : unipAll F) : g ∈ radOne F ↔ coordB g = 0 := by
  obtain ⟨a, b, c, rfl⟩ := exists_uelt g
  rw [radOne, mem_subgroupOf, coordB_uelt]
  constructor
  · rintro ⟨a', c', h⟩
    exact (unipU_inj h).2.1.symm
  · intro hb
    exact ⟨a, c, by rw [coe_uelt, hb]⟩

theorem mem_radTwo (g : unipAll F) : g ∈ radTwo F ↔ coordA g = 0 := by
  obtain ⟨a, b, c, rfl⟩ := exists_uelt g
  rw [radTwo, mem_subgroupOf, coordA_uelt]
  constructor
  · rintro ⟨b', c', h⟩
    exact (unipU_inj h).1.symm
  · intro ha
    exact ⟨b, c, by rw [coe_uelt, ha]⟩

theorem mem_radCenter (g : unipAll F) : g ∈ radCenter F ↔ coordA g = 0 ∧ coordB g = 0 := by
  obtain ⟨a, b, c, rfl⟩ := exists_uelt g
  rw [radCenter, mem_subgroupOf, coordA_uelt, coordB_uelt]
  constructor
  · rintro ⟨c', h⟩
    exact ⟨(unipU_inj h).1.symm, (unipU_inj h).2.1.symm⟩
  · rintro ⟨ha, hb⟩
    exact ⟨c, by rw [coe_uelt, ha, hb]⟩

theorem mul_comm_of_mem_radOne {g h : unipAll F} (hg : g ∈ radOne F) (hh : h ∈ radOne F) :
    g * h = h * g :=
  (commute_unipAll_iff' g h).2 <| by
    rw [(mem_radOne g).1 hg, (mem_radOne h).1 hh, mul_zero, mul_zero]

theorem mul_comm_of_mem_radTwo {g h : unipAll F} (hg : g ∈ radTwo F) (hh : h ∈ radTwo F) :
    g * h = h * g :=
  (commute_unipAll_iff' g h).2 <| by
    rw [(mem_radTwo g).1 hg, (mem_radTwo h).1 hh, zero_mul, zero_mul]

theorem center_unipAll : center (unipAll F) = radCenter F := by
  ext g
  rw [mem_center_unipAll, mem_radCenter]

theorem radOne_inf_radTwo : radOne F ⊓ radTwo F = radCenter F := by
  ext g
  rw [Subgroup.mem_inf, mem_radOne, mem_radTwo, mem_radCenter, and_comm]

theorem radOne_sup_radTwo : radOne F ⊔ radTwo F = ⊤ := by
  refine eq_top_iff.2 fun g _ => ?_
  obtain ⟨a, b, c, rfl⟩ := exists_uelt g
  have h : (uelt a b c : unipAll F) = uelt a 0 0 * uelt 0 b (c - a * b) := by
    rw [uelt_mul, uelt_inj]
    exact ⟨by ring, by ring, by ring⟩
  rw [h]
  exact Subgroup.mul_mem_sup ((mem_radOne _).2 (by simp)) ((mem_radTwo _).2 (by simp))

theorem radOne_ne_radTwo : radOne F ≠ radTwo F := by
  intro h
  have h1 : (uelt 0 1 0 : unipAll F) ∈ radOne F := h ▸ (mem_radTwo _).2 (by simp)
  rw [mem_radOne] at h1
  simp at h1

theorem unipOne_le_unipAll : unipOne F ≤ unipAll F := fun _ ⟨a, c, h⟩ => ⟨a, 0, c, h⟩

theorem unipTwo_le_unipAll : unipTwo F ≤ unipAll F := fun _ ⟨b, c, h⟩ => ⟨0, b, c, h⟩

theorem unipCenter_le_unipAll : unipCenter F ≤ unipAll F := fun _ ⟨c, h⟩ => ⟨0, 0, c, h⟩

theorem card_unipOne : Nat.card (unipOne F) = Nat.card F ^ 2 := by
  have hbij : Function.Bijective (fun x : F × F =>
      (⟨unipU F x.1 0 x.2, mem_unipOne.2 ⟨x.1, x.2, rfl⟩⟩ : unipOne F)) := by
    refine ⟨fun x y h => ?_, ?_⟩
    · have := unipU_inj (congrArg Subtype.val h)
      exact Prod.ext this.1 this.2.2
    · rintro ⟨g, hg⟩
      obtain ⟨a, c, rfl⟩ := mem_unipOne.1 hg
      exact ⟨(a, c), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, sq]

theorem card_unipTwo : Nat.card (unipTwo F) = Nat.card F ^ 2 := by
  have hbij : Function.Bijective (fun x : F × F =>
      (⟨unipU F 0 x.1 x.2, mem_unipTwo.2 ⟨x.1, x.2, rfl⟩⟩ : unipTwo F)) := by
    refine ⟨fun x y h => ?_, ?_⟩
    · have := unipU_inj (congrArg Subtype.val h)
      exact Prod.ext this.2.1 this.2.2
    · rintro ⟨g, hg⟩
      obtain ⟨b, c, rfl⟩ := mem_unipTwo.1 hg
      exact ⟨(b, c), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, sq]

theorem card_unipCenter : Nat.card (unipCenter F) = Nat.card F := by
  have hbij : Function.Bijective (fun x : F =>
      (⟨unipU F 0 0 x, mem_unipCenter.2 ⟨x, rfl⟩⟩ : unipCenter F)) := by
    refine ⟨fun x y h => ?_, ?_⟩
    · exact (unipU_inj (congrArg Subtype.val h)).2.2
    · rintro ⟨g, hg⟩
      obtain ⟨c, rfl⟩ := mem_unipCenter.1 hg
      exact ⟨c, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]

theorem card_radOne : Nat.card (radOne F) = Nat.card F ^ 2 := by
  rw [radOne, ← card_unipOne]
  exact Nat.card_congr (subgroupOfEquivOfLe unipOne_le_unipAll).toEquiv

theorem card_radTwo : Nat.card (radTwo F) = Nat.card F ^ 2 := by
  rw [radTwo, ← card_unipTwo]
  exact Nat.card_congr (subgroupOfEquivOfLe unipTwo_le_unipAll).toEquiv

theorem card_radCenter : Nat.card (radCenter F) = Nat.card F := by
  rw [radCenter]
  exact (Nat.card_congr (subgroupOfEquivOfLe unipCenter_le_unipAll).toEquiv).trans
    card_unipCenter

end Subgroups

section Centralizers

variable {F : Type} [Field F]

theorem centralizer_radTwo {g : unipAll F} (hA : coordA g = 0) (hB : coordB g ≠ 0) :
    centralizer {g} = radTwo F := by
  ext h
  rw [Subgroup.mem_centralizer_singleton_iff, mem_radTwo]
  constructor
  · intro h1
    have h2 := (commute_unipAll_iff' h g).1 h1
    rw [hA, zero_mul] at h2
    exact (mul_eq_zero.1 h2).resolve_right hB
  · intro h1
    refine (commute_unipAll_iff' h g).2 ?_
    rw [hA, h1, zero_mul, zero_mul]

theorem centralizer_radOne {g : unipAll F} (hB : coordB g = 0) (hA : coordA g ≠ 0) :
    centralizer {g} = radOne F := by
  ext h
  rw [Subgroup.mem_centralizer_singleton_iff, mem_radOne]
  constructor
  · intro h1
    have h2 := (commute_unipAll_iff' h g).1 h1
    rw [hB, mul_zero] at h2
    exact (mul_eq_zero.1 h2.symm).resolve_left hA
  · intro h1
    refine (commute_unipAll_iff' h g).2 ?_
    rw [hB, h1, mul_zero, mul_zero]

end Centralizers

section DiagAut

variable {F : Type} [Field F]

@[expose] def diagAut (σ : F ≃+* F) (l m : Fˣ) : MulAut (unipAll F) where
  toFun := diagFun σ l m
  invFun := diagFun σ.symm (σ.symm ((l⁻¹ : Fˣ) : F)) (σ.symm ((m⁻¹ : Fˣ) : F))
  left_inv g := by
    obtain ⟨a, b, c, rfl⟩ := exists_uelt g
    have hl : σ.symm ((l⁻¹ : Fˣ) : F) * σ.symm (l : F) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hm : σ.symm ((m⁻¹ : Fˣ) : F) * σ.symm (m : F) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [diagFun_uelt, diagFun_uelt, uelt_inj]
    refine ⟨?_, ?_, ?_⟩
    · simp only [map_mul, RingEquiv.symm_apply_apply]
      calc _ = (σ.symm ((l⁻¹ : Fˣ) : F) * σ.symm (l : F)) * a := by ring
        _ = a := by rw [hl, one_mul]
    · simp only [map_mul, RingEquiv.symm_apply_apply]
      calc _ = (σ.symm ((m⁻¹ : Fˣ) : F) * σ.symm (m : F)) * b := by ring
        _ = b := by rw [hm, one_mul]
    · simp only [map_mul, RingEquiv.symm_apply_apply]
      calc _ = (σ.symm ((l⁻¹ : Fˣ) : F) * σ.symm (l : F)) *
            (σ.symm ((m⁻¹ : Fˣ) : F) * σ.symm (m : F)) * c := by ring
        _ = c := by rw [hl, hm, one_mul, one_mul]
  right_inv g := by
    obtain ⟨a, b, c, rfl⟩ := exists_uelt g
    have hl : (l : F) * (l⁻¹ : Fˣ) = 1 := Units.mul_inv l
    have hm : (m : F) * (m⁻¹ : Fˣ) = 1 := Units.mul_inv m
    rw [diagFun_uelt, diagFun_uelt, uelt_inj]
    refine ⟨?_, ?_, ?_⟩
    · simp only [map_mul, RingEquiv.apply_symm_apply]
      calc _ = ((l : F) * (l⁻¹ : Fˣ)) * a := by ring
        _ = a := by rw [hl, one_mul]
    · simp only [map_mul, RingEquiv.apply_symm_apply]
      calc _ = ((m : F) * (m⁻¹ : Fˣ)) * b := by ring
        _ = b := by rw [hm, one_mul]
    · simp only [map_mul, RingEquiv.apply_symm_apply]
      calc _ = ((l : F) * (l⁻¹ : Fˣ)) * ((m : F) * (m⁻¹ : Fˣ)) * c := by ring
        _ = c := by rw [hl, hm, one_mul, one_mul]
  map_mul' := diagFun_mul σ l m

theorem diagAut_uelt (σ : F ≃+* F) (l m : Fˣ) (a b c : F) :
    diagAut σ l m (uelt a b c) = uelt (l * σ a) (m * σ b) (l * m * σ c) :=
  diagFun_uelt σ l m a b c

@[expose] def fieldAut (σ : F ≃+* F) : MulAut (unipAll F) := diagAut σ 1 1

@[simp] theorem fieldAut_uelt (σ : F ≃+* F) (a b c : F) :
    fieldAut σ (uelt a b c) = uelt (σ a) (σ b) (σ c) := by
  simp [fieldAut, diagAut_uelt]

@[expose] def centralAut (e₁ e₂ : F →+ F) : MulAut (unipAll F) where
  toFun g := uelt (coordA g) (coordB g) (coordC g + e₁ (coordA g) + e₂ (coordB g))
  invFun g := uelt (coordA g) (coordB g) (coordC g - e₁ (coordA g) - e₂ (coordB g))
  left_inv g := by
    obtain ⟨a, b, c, rfl⟩ := exists_uelt g
    simp only [coordA_uelt, coordB_uelt, coordC_uelt, uelt_inj]
    exact ⟨trivial, trivial, by ring⟩
  right_inv g := by
    obtain ⟨a, b, c, rfl⟩ := exists_uelt g
    simp only [coordA_uelt, coordB_uelt, coordC_uelt, uelt_inj]
    exact ⟨trivial, trivial, by ring⟩
  map_mul' g h := by
    obtain ⟨a, b, c, rfl⟩ := exists_uelt g
    obtain ⟨a', b', c', rfl⟩ := exists_uelt h
    simp only [uelt_mul, coordA_uelt, coordB_uelt, coordC_uelt, uelt_inj, map_add]
    exact ⟨trivial, trivial, by ring⟩

theorem centralAut_uelt (e₁ e₂ : F →+ F) (a b c : F) :
    centralAut e₁ e₂ (uelt a b c) = uelt a b (c + e₁ a + e₂ b) := by
  simp [centralAut]

end DiagAut

section AutBasic

variable {F : Type} [Field F]

theorem exists_ringEquiv_of_additive_mul (f : F → F) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hmul : ∀ x y, f (x * y) * f 1 = f x * f y) (hinj : Function.Injective f)
    (hsurj : Function.Surjective f) : ∃ σ : F ≃+* F, ∀ x, f x = f 1 * σ x := by
  have h0 : f 0 = 0 := by
    have := hadd 0 0
    simpa using this
  have h1 : f 1 ≠ 0 := fun h => one_ne_zero (hinj (h.trans h0.symm))
  let g : F →+* F :=
    { toFun := fun x => f x / f 1
      map_one' := div_self h1
      map_mul' := fun x y => by
        have := hmul x y
        field_simp
        linear_combination this
      map_zero' := by simp [h0]
      map_add' := fun x y => by rw [hadd, add_div] }
  have hg : Function.Bijective g := by
    refine ⟨fun x y hxy => hinj ?_, fun y => ?_⟩
    · have : f x / f 1 = f y / f 1 := hxy
      exact (div_left_inj' h1).1 this
    · obtain ⟨x, hx⟩ := hsurj (y * f 1)
      exact ⟨x, by show f x / f 1 = y; rw [hx, mul_div_cancel_right₀ _ h1]⟩
  refine ⟨RingEquiv.ofBijective g hg, fun x => ?_⟩
  show f x = f 1 * (f x / f 1)
  rw [mul_div_cancel₀ _ h1]

@[expose] def autZ (α : MulAut (unipAll F)) (c : F) : F := coordC (α (uelt 0 0 c))

@[expose] def autA (α : MulAut (unipAll F)) (a b : F) : F := coordA (α (uelt a b 0))

@[expose] def autB (α : MulAut (unipAll F)) (a b : F) : F := coordB (α (uelt a b 0))

theorem aut_center_coords (α : MulAut (unipAll F)) {g : unipAll F}
    (hg : coordA g = 0 ∧ coordB g = 0) : coordA (α g) = 0 ∧ coordB (α g) = 0 := by
  refine coords_eq_zero_of_commute fun h => ?_
  obtain ⟨h', rfl⟩ := α.surjective h
  rw [← map_mul, ← map_mul, commute_of_coords_eq_zero hg.1 hg.2 h']

theorem aut_uelt_center (α : MulAut (unipAll F)) (c : F) :
    α (uelt 0 0 c) = uelt 0 0 (autZ α c) := by
  have h := aut_center_coords α (g := uelt 0 0 c) (by simp)
  have := uelt_coords (α (uelt 0 0 c))
  rw [h.1, h.2] at this
  exact this.symm

theorem autZ_add (α : MulAut (unipAll F)) (c c' : F) :
    autZ α (c + c') = autZ α c + autZ α c' := by
  have h : (uelt 0 0 (c + c') : unipAll F) = uelt 0 0 c * uelt 0 0 c' := by
    rw [uelt_mul]
    simp
  have h2 : α (uelt 0 0 (c + c')) = uelt 0 0 (autZ α c) * uelt 0 0 (autZ α c') := by
    rw [h, map_mul, aut_uelt_center, aut_uelt_center]
  rw [aut_uelt_center, uelt_mul, uelt_inj] at h2
  simpa using h2.2.2

theorem autZ_zero (α : MulAut (unipAll F)) : autZ α 0 = 0 := by
  have := autZ_add α 0 0
  simpa using this

theorem autZ_injective (α : MulAut (unipAll F)) : Function.Injective (autZ α) := by
  intro c c' h
  have h1 : α (uelt 0 0 c) = α (uelt 0 0 c') := by
    rw [aut_uelt_center, aut_uelt_center, h]
  exact (uelt_inj.1 (α.injective h1)).2.2

theorem autZ_surjective (α : MulAut (unipAll F)) : Function.Surjective (autZ α) := by
  intro y
  refine ⟨autZ α.symm y, ?_⟩
  have h1 : α.symm (uelt 0 0 y) = uelt 0 0 (autZ α.symm y) := aut_uelt_center α.symm y
  have h2 : α (uelt 0 0 (autZ α.symm y)) = uelt 0 0 y := by
    rw [← h1, MulEquiv.apply_symm_apply]
  rw [aut_uelt_center, uelt_inj] at h2
  exact h2.2.2

theorem coordA_aut_uelt (α : MulAut (unipAll F)) (a b c : F) :
    coordA (α (uelt a b c)) = autA α a b := by
  rw [uelt_eq_mul, map_mul, coordA_mul, aut_uelt_center]
  simp [autA]

theorem coordB_aut_uelt (α : MulAut (unipAll F)) (a b c : F) :
    coordB (α (uelt a b c)) = autB α a b := by
  rw [uelt_eq_mul, map_mul, coordB_mul, aut_uelt_center]
  simp [autB]

theorem autA_add (α : MulAut (unipAll F)) (a b a' b' : F) :
    autA α (a + a') (b + b') = autA α a b + autA α a' b' := by
  have h := coordA_mul (α (uelt a b 0)) (α (uelt a' b' 0))
  rw [← map_mul, uelt_mul, coordA_aut_uelt] at h
  exact h

theorem autB_add (α : MulAut (unipAll F)) (a b a' b' : F) :
    autB α (a + a') (b + b') = autB α a b + autB α a' b' := by
  have h := coordB_mul (α (uelt a b 0)) (α (uelt a' b' 0))
  rw [← map_mul, uelt_mul, coordB_aut_uelt] at h
  exact h

theorem aut_coords_eq_zero (α : MulAut (unipAll F)) {a b : F} (hA : autA α a b = 0)
    (hB : autB α a b = 0) : a = 0 ∧ b = 0 := by
  have h := aut_center_coords α.symm (g := α (uelt a b 0)) ⟨hA, hB⟩
  rw [MulEquiv.symm_apply_apply] at h
  simpa using h

@[expose] def AutData (α : MulAut (unipAll F)) (σ : F ≃+* F) (l m : Fˣ) (sw : Bool) : Prop :=
  (∀ a b c : F, (coordA (α (uelt a b c)), coordB (α (uelt a b c))) =
      if sw then ((m : F) * σ b, (l : F) * σ a) else ((l : F) * σ a, (m : F) * σ b)) ∧
    ∀ c : F, α (uelt 0 0 c) = uelt 0 0 ((l : F) * m * σ c)

variable {α : MulAut (unipAll F)} {σ σ' : F ≃+* F} {l m l' m' : Fˣ} {sw sw' : Bool}

theorem AutData.coordA_eq (h : AutData α σ l m sw) (x : unipAll F) :
    coordA (α x) = if sw then (m : F) * σ (coordB x) else (l : F) * σ (coordA x) := by
  have := h.1 (coordA x) (coordB x) (coordC x)
  rw [uelt_coords] at this
  cases sw
  · exact (Prod.ext_iff.1 this).1
  · exact (Prod.ext_iff.1 this).1

theorem AutData.coordB_eq (h : AutData α σ l m sw) (x : unipAll F) :
    coordB (α x) = if sw then (l : F) * σ (coordA x) else (m : F) * σ (coordB x) := by
  have := h.1 (coordA x) (coordB x) (coordC x)
  rw [uelt_coords] at this
  cases sw
  · exact (Prod.ext_iff.1 this).2
  · exact (Prod.ext_iff.1 this).2

theorem AutData.unique (h : AutData α σ l m sw) (h' : AutData α σ' l' m' sw') :
    σ = σ' ∧ l = l' ∧ m = m' ∧ sw = sw' := by
  have e1 := (h.1 1 0 0).symm.trans (h'.1 1 0 0)
  have e2 := (h.1 0 1 0).symm.trans (h'.1 0 1 0)
  have e3 := (h.2 1).symm.trans (h'.2 1)
  rw [uelt_inj] at e3
  simp only [map_one, mul_one, map_zero, mul_zero] at e1 e2 e3
  have hσ : σ = σ' := by
    refine RingEquiv.ext fun c => ?_
    have e4 := (h.2 c).symm.trans (h'.2 c)
    rw [uelt_inj] at e4
    refine mul_left_cancel₀ (mul_ne_zero l.ne_zero m.ne_zero) ?_
    rw [e4.2.2, ← e3.2.2]
  refine ⟨hσ, ?_⟩
  cases sw <;> cases sw'
  · simp only [Bool.false_eq_true, ite_false, Prod.mk.injEq] at e1 e2
    exact ⟨Units.ext e1.1, Units.ext e2.2, rfl⟩
  · simp only [Bool.false_eq_true, ite_false, ite_true, Prod.mk.injEq] at e1 e2
    exact absurd e1.1 l.ne_zero
  · simp only [Bool.false_eq_true, ite_false, ite_true, Prod.mk.injEq] at e1 e2
    exact absurd e1.1.symm l'.ne_zero
  · simp only [ite_true, Prod.mk.injEq] at e1 e2
    exact ⟨Units.ext e1.2, Units.ext e2.1, rfl⟩

theorem autData_one : AutData (1 : MulAut (unipAll F)) (RingEquiv.refl F) 1 1 false := by
  refine ⟨fun a b c => ?_, fun c => ?_⟩
  · simp
  · simp

theorem autData_conj (h : unipAll F) :
    AutData (MulAut.conj h) (RingEquiv.refl F) 1 1 false := by
  have hA : ∀ g : unipAll F, coordA (MulAut.conj h g) = coordA g := fun g => by
    rw [MulAut.conj_apply, coordA_mul, coordA_mul, coordA_inv]
    ring
  have hB : ∀ g : unipAll F, coordB (MulAut.conj h g) = coordB g := fun g => by
    rw [MulAut.conj_apply, coordB_mul, coordB_mul, coordB_inv]
    ring
  refine ⟨fun a b c => ?_, fun c => ?_⟩
  · simp only [hA, hB, coordA_uelt, coordB_uelt]
    simp
  · rw [MulAut.conj_apply, ← commute_of_coords_eq_zero (g := uelt 0 0 c) (by simp) (by simp) h]
    simp

open Classical in
@[expose] noncomputable def autSwap (α : MulAut (unipAll F)) : Bool :=
  decide (coordA (α (uelt 1 0 0)) = 0)

theorem autSwap_eq {α : MulAut (unipAll F)} {σ : F ≃+* F} {l m : Fˣ} {sw : Bool}
    (h : AutData α σ l m sw) : autSwap α = sw := by
  have e := h.coordA_eq (uelt 1 0 0)
  simp only [coordA_uelt, coordB_uelt, map_zero, mul_zero, map_one, mul_one] at e
  unfold autSwap
  cases sw
  · simp only [Bool.false_eq_true, ite_false] at e
    simp [e, l.ne_zero]
  · simp only [ite_true] at e
    simp [e]

theorem autSwap_eq_true_iff (α : MulAut (unipAll F)) :
    autSwap α = true ↔ coordA (α (uelt 1 0 0)) = 0 := by
  unfold autSwap
  simp

theorem autSwap_conj (h : unipAll F) : autSwap (MulAut.conj h) = false :=
  autSwap_eq (autData_conj h)

theorem AutData.map_radOne {α : MulAut (unipAll F)} {σ : F ≃+* F} {l m : Fˣ} {sw : Bool}
    (h : AutData α σ l m sw) :
    (radOne F).map α.toMonoidHom = if sw then radTwo F else radOne F := by
  ext y
  rw [Subgroup.mem_map]
  have hm : ∀ x : F, (m : F) * σ x = 0 → x = 0 := fun x hx =>
    (map_eq_zero σ).1 ((mul_eq_zero.1 hx).resolve_left m.ne_zero)
  cases sw
  · simp only [Bool.false_eq_true, ite_false, mem_radOne]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := h.coordB_eq x
      simp only [Bool.false_eq_true, ite_false] at this
      show coordB (α x) = 0
      rw [this, hx, map_zero, mul_zero]
    · intro hy
      refine ⟨α.symm y, ?_, α.apply_symm_apply y⟩
      have := h.coordB_eq (α.symm y)
      simp only [Bool.false_eq_true, ite_false, MulEquiv.apply_symm_apply] at this
      exact hm _ (this.symm.trans hy)
  · simp only [ite_true, mem_radTwo, mem_radOne]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := h.coordA_eq x
      simp only [ite_true] at this
      show coordA (α x) = 0
      rw [this, hx, map_zero, mul_zero]
    · intro hy
      refine ⟨α.symm y, ?_, α.apply_symm_apply y⟩
      have := h.coordA_eq (α.symm y)
      simp only [ite_true, MulEquiv.apply_symm_apply] at this
      exact hm _ (this.symm.trans hy)

theorem AutData.map_radTwo {α : MulAut (unipAll F)} {σ : F ≃+* F} {l m : Fˣ} {sw : Bool}
    (h : AutData α σ l m sw) :
    (radTwo F).map α.toMonoidHom = if sw then radOne F else radTwo F := by
  ext y
  rw [Subgroup.mem_map]
  have hl : ∀ x : F, (l : F) * σ x = 0 → x = 0 := fun x hx =>
    (map_eq_zero σ).1 ((mul_eq_zero.1 hx).resolve_left l.ne_zero)
  cases sw
  · simp only [Bool.false_eq_true, ite_false, mem_radTwo]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := h.coordA_eq x
      simp only [Bool.false_eq_true, ite_false] at this
      show coordA (α x) = 0
      rw [this, hx, map_zero, mul_zero]
    · intro hy
      refine ⟨α.symm y, ?_, α.apply_symm_apply y⟩
      have := h.coordA_eq (α.symm y)
      simp only [Bool.false_eq_true, ite_false, MulEquiv.apply_symm_apply] at this
      exact hl _ (this.symm.trans hy)
  · simp only [ite_true, mem_radTwo, mem_radOne]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := h.coordB_eq x
      simp only [ite_true] at this
      show coordB (α x) = 0
      rw [this, hx, map_zero, mul_zero]
    · intro hy
      refine ⟨α.symm y, ?_, α.apply_symm_apply y⟩
      have := h.coordB_eq (α.symm y)
      simp only [ite_true, MulEquiv.apply_symm_apply] at this
      exact hl _ (this.symm.trans hy)

end AutBasic

section CharTwo

variable {F : Type} [Field F] [CharP F 2]

theorem uelt_mul_self (a b c : F) : (uelt a b c : unipAll F) * uelt a b c = uelt 0 0 (a * b) := by
  rw [uelt_mul, uelt_inj]
  refine ⟨CharTwo.add_self_eq_zero a, CharTwo.add_self_eq_zero b, ?_⟩
  rw [CharTwo.add_self_eq_zero c, zero_add]

theorem graphFun_graphFun (g : unipAll F) : graphFun (graphFun g) = g := by
  obtain ⟨a, b, c, rfl⟩ := exists_uelt g
  rw [graphFun_uelt, graphFun_uelt, uelt_inj]
  refine ⟨rfl, rfl, ?_⟩
  linear_combination (a * b) * (CharTwo.two_eq_zero : (2 : F) = 0)

theorem graphFun_mul (g h : unipAll F) : graphFun (g * h) = graphFun g * graphFun h := by
  obtain ⟨a, b, c, rfl⟩ := exists_uelt g
  obtain ⟨a', b', c', rfl⟩ := exists_uelt h
  rw [uelt_mul, graphFun_uelt, graphFun_uelt, graphFun_uelt, uelt_mul, uelt_inj]
  refine ⟨rfl, rfl, ?_⟩
  linear_combination (a * b') * (CharTwo.two_eq_zero : (2 : F) = 0)

@[expose] def graphAut : MulAut (unipAll F) where
  toFun := graphFun
  invFun := graphFun
  left_inv := graphFun_graphFun
  right_inv := graphFun_graphFun
  map_mul' := graphFun_mul

theorem graphAut_uelt (a b c : F) : graphAut (uelt a b c) = uelt b a (c + a * b) :=
  graphFun_uelt a b c

theorem graphAut_graphAut (g : unipAll F) : graphAut (graphAut g) = g := graphFun_graphFun g

theorem coordA_graphAut (g : unipAll F) : coordA (graphAut g) = coordB g := by
  obtain ⟨a, b, c, rfl⟩ := exists_uelt g
  simp [graphAut_uelt]

theorem coordB_graphAut (g : unipAll F) : coordB (graphAut g) = coordA g := by
  obtain ⟨a, b, c, rfl⟩ := exists_uelt g
  simp [graphAut_uelt]

theorem graphAut_mem_radTwo_iff (g : unipAll F) : graphAut g ∈ radTwo F ↔ g ∈ radOne F := by
  rw [mem_radTwo, mem_radOne, coordA_graphAut]

theorem graphAut_mem_radOne_iff (g : unipAll F) : graphAut g ∈ radOne F ↔ g ∈ radTwo F := by
  rw [mem_radTwo, mem_radOne, coordB_graphAut]

theorem map_graphAut_radOne :
    (radOne F).map (graphAut : MulAut (unipAll F)).toMonoidHom = radTwo F := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (graphAut_mem_radTwo_iff x).2 hx
  · intro hg
    exact ⟨graphAut g, (graphAut_mem_radOne_iff g).2 hg, graphAut_graphAut g⟩

theorem sq_eq_one_iff (g : unipAll F) : g * g = 1 ↔ g ∈ radOne F ∨ g ∈ radTwo F := by
  obtain ⟨a, b, c, rfl⟩ := exists_uelt g
  rw [uelt_mul_self, ← uelt_zero, uelt_inj, mem_radOne, mem_radTwo]
  simp [mul_eq_zero, or_comm]

theorem mul_self_of_mem_radOne {g : unipAll F} (hg : g ∈ radOne F) : g * g = 1 :=
  (sq_eq_one_iff g).2 (Or.inl hg)

theorem mul_self_of_mem_radTwo {g : unipAll F} (hg : g ∈ radTwo F) : g * g = 1 :=
  (sq_eq_one_iff g).2 (Or.inr hg)

theorem le_radOne_or_le_radTwo (E : Subgroup (unipAll F)) (hsq : ∀ g ∈ E, g * g = 1) :
    E ≤ radOne F ∨ E ≤ radTwo F := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  obtain ⟨g₁, hg₁E, hg₁⟩ := IsConcreteLE.not_le_iff_exists.1 h1
  obtain ⟨g₂, hg₂E, hg₂⟩ := IsConcreteLE.not_le_iff_exists.1 h2
  have hab : ∀ g ∈ E, coordA g * coordB g = 0 := by
    intro g hg
    rcases (sq_eq_one_iff g).1 (hsq g hg) with h | h
    · rw [(mem_radOne g).1 h, mul_zero]
    · rw [(mem_radTwo g).1 h, zero_mul]
  rw [mem_radOne] at hg₁
  rw [mem_radTwo] at hg₂
  have ha₁ : coordA g₁ = 0 := (mul_eq_zero.1 (hab g₁ hg₁E)).resolve_right hg₁
  have hb₂ : coordB g₂ = 0 := (mul_eq_zero.1 (hab g₂ hg₂E)).resolve_left hg₂
  have := hab (g₁ * g₂) (E.mul_mem hg₁E hg₂E)
  rw [coordA_mul, coordB_mul, ha₁, hb₂, zero_add, add_zero] at this
  exact mul_ne_zero hg₂ hg₁ this

theorem eq_radOne_or_radTwo_of_card [Finite F] {E : Subgroup (unipAll F)}
    (hsq : ∀ g ∈ E, g * g = 1) (hcard : Nat.card E = Nat.card F ^ 2) :
    E = radOne F ∨ E = radTwo F := by
  rcases le_radOne_or_le_radTwo E hsq with h | h
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (by rw [card_radOne, hcard]))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge h (by rw [card_radTwo, hcard]))

theorem fixSubgroup_graphAut : fixSubgroup (graphAut : MulAut (unipAll F)) = radCenter F := by
  ext g
  rw [mem_fixSubgroup, mem_radCenter]
  obtain ⟨a, b, c, rfl⟩ := exists_uelt g
  rw [graphAut_uelt, uelt_inj]
  simp only [coordA_uelt, coordB_uelt]
  constructor
  · rintro ⟨h1, -, h3⟩
    have hab : a * a = 0 := by
      rw [h1] at h3
      linear_combination h3
    exact ⟨mul_self_eq_zero.1 hab, h1.trans (mul_self_eq_zero.1 hab)⟩
  · rintro ⟨rfl, rfl⟩
    simp

end CharTwo

section Cocycle

variable {F : Type} [Field F] [CharP F 2]

@[expose] def graphFieldAut (σ : F ≃+* F) : MulAut (unipAll F) := graphAut * fieldAut σ

theorem graphFieldAut_apply (σ : F ≃+* F) (g : unipAll F) :
    graphFieldAut σ g = graphAut (fieldAut σ g) := rfl

theorem graphFieldAut_uelt (σ : F ≃+* F) (a b c : F) :
    graphFieldAut σ (uelt a b c) = uelt (σ b) (σ a) (σ c + σ a * σ b) := by
  rw [graphFieldAut_apply, fieldAut_uelt, graphAut_uelt]

end Cocycle

section AutClassify

variable {F : Type} [Field F] [CharP F 2]

theorem autZ_mul (α : MulAut (unipAll F)) (a b : F) :
    autZ α (a * b) = autA α a b * autB α a b := by
  have h1 : α (uelt a b 0) * α (uelt a b 0) = uelt 0 0 (autZ α (a * b)) := by
    rw [← map_mul, uelt_mul_self, aut_uelt_center]
  rw [← uelt_coords (α (uelt a b 0)), uelt_mul_self, uelt_inj] at h1
  exact h1.2.2.symm

theorem autA_mul_autB_eq_zero_iff (α : MulAut (unipAll F)) (a b : F) :
    autA α a b * autB α a b = 0 ↔ a * b = 0 := by
  rw [← autZ_mul]
  constructor
  · intro h
    exact autZ_injective α (h.trans (autZ_zero α).symm)
  · intro h
    rw [h, autZ_zero]

theorem aut_gens_dichotomy (α : MulAut (unipAll F)) :
    (autB α 1 0 = 0 ∧ autA α 0 1 = 0) ∨ (autA α 1 0 = 0 ∧ autB α 0 1 = 0) := by
  have hx : autA α 1 0 * autB α 1 0 = 0 := (autA_mul_autB_eq_zero_iff α 1 0).2 (by simp)
  have hy : autA α 0 1 * autB α 0 1 = 0 := (autA_mul_autB_eq_zero_iff α 0 1).2 (by simp)
  have hxy : (autA α 1 0 + autA α 0 1) * (autB α 1 0 + autB α 0 1) ≠ 0 := by
    have h := autA_add α 1 0 0 1
    have h' := autB_add α 1 0 0 1
    simp only [add_zero, zero_add] at h h'
    rw [← h, ← h']
    intro h0
    have := (autA_mul_autB_eq_zero_iff α 1 1).1 h0
    simp at this
  rcases mul_eq_zero.1 hx with hx1 | hx2 <;> rcases mul_eq_zero.1 hy with hy1 | hy2
  · exfalso
    apply hxy
    rw [hx1, hy1]
    ring
  · exact Or.inr ⟨hx1, hy2⟩
  · exact Or.inl ⟨hx2, hy1⟩
  · exfalso
    apply hxy
    rw [hx2, hy2]
    ring

theorem aut_noswap_of_gens (α : MulAut (unipAll F)) (h : autB α 1 0 = 0 ∧ autA α 0 1 = 0) :
    (∀ a, autB α a 0 = 0) ∧ (∀ b, autA α 0 b = 0) := by
  obtain ⟨hx2, hy1⟩ := h
  have hx1 : autA α 1 0 ≠ 0 := fun h0 => one_ne_zero (aut_coords_eq_zero α h0 hx2).1
  have hy2 : autB α 0 1 ≠ 0 := fun h0 => one_ne_zero (aut_coords_eq_zero α hy1 h0).2
  refine ⟨fun a => ?_, fun b => ?_⟩
  · by_contra hne
    have h1 : autA α a 0 = 0 :=
      (mul_eq_zero.1 ((autA_mul_autB_eq_zero_iff α a 0).2 (mul_zero a))).resolve_right hne
    have hA := autA_add α a 0 1 0
    have hB := autB_add α a 0 1 0
    simp only [add_zero] at hA hB
    have h2 := (autA_mul_autB_eq_zero_iff α (a + 1) 0).2 (mul_zero _)
    rw [hA, hB, h1, hx2, zero_add, add_zero] at h2
    exact mul_ne_zero hx1 hne h2
  · by_contra hne
    have h1 : autB α 0 b = 0 :=
      (mul_eq_zero.1 ((autA_mul_autB_eq_zero_iff α 0 b).2 (zero_mul b))).resolve_left hne
    have hA := autA_add α 0 b 0 1
    have hB := autB_add α 0 b 0 1
    simp only [zero_add] at hA hB
    have h2 := (autA_mul_autB_eq_zero_iff α 0 (b + 1)).2 (zero_mul _)
    rw [hA, hB, h1, hy1, zero_add, add_zero] at h2
    exact mul_ne_zero hne hy2 h2

theorem aut_core_noswap (α : MulAut (unipAll F))
    (hn : (∀ a, autB α a 0 = 0) ∧ (∀ b, autA α 0 b = 0)) :
    ∃ (σ : F ≃+* F) (l m : Fˣ),
      (∀ a b c : F, coordA (α (uelt a b c)) = l * σ a ∧ coordB (α (uelt a b c)) = m * σ b) ∧
      ∀ c : F, α (uelt 0 0 c) = uelt 0 0 ((l : F) * m * σ c) := by
  obtain ⟨hn1, hn2⟩ := hn
  have hA : ∀ a b, autA α a b = autA α a 0 := fun a b => by
    have := autA_add α a 0 0 b
    simpa [hn2 b] using this
  have hB : ∀ a b, autB α a b = autB α 0 b := fun a b => by
    have := autB_add α a 0 0 b
    simpa [hn1 a] using this
  have hz : ∀ a b, autZ α (a * b) = autA α a 0 * autB α 0 b := fun a b => by
    rw [autZ_mul, hA, hB]
  have hl1 : autA α 1 0 ≠ 0 := fun h0 => one_ne_zero (aut_coords_eq_zero α h0 (hn1 1)).1
  have hm1 : autB α 0 1 ≠ 0 := fun h0 => one_ne_zero (aut_coords_eq_zero α (hn2 1) h0).2
  have hmul : ∀ x y, autZ α (x * y) * autZ α 1 = autZ α x * autZ α y := fun x y => by
    have e1 := hz x y
    have e2 := hz 1 1
    have e3 := hz x 1
    have e4 := hz 1 y
    rw [mul_one] at e3 e2
    rw [one_mul] at e4
    rw [e1, e2, e3, e4]
    ring
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_of_additive_mul (autZ α) (autZ_add α) hmul
    (autZ_injective α) (autZ_surjective α)
  have e11 : autZ α 1 = autA α 1 0 * autB α 0 1 := by
    have := hz 1 1
    rwa [mul_one] at this
  have hlam : ∀ a, autA α a 0 = autA α 1 0 * σ a := fun a => by
    have e3 := hz a 1
    rw [mul_one] at e3
    have := hσ a
    rw [e3, e11] at this
    exact mul_right_cancel₀ hm1 (by linear_combination this)
  have hmu : ∀ b, autB α 0 b = autB α 0 1 * σ b := fun b => by
    have e4 := hz 1 b
    rw [one_mul] at e4
    have := hσ b
    rw [e4, e11] at this
    exact mul_left_cancel₀ hl1 (by linear_combination this)
  refine ⟨σ, Units.mk0 _ hl1, Units.mk0 _ hm1, fun a b c => ⟨?_, ?_⟩, fun c => ?_⟩
  · rw [coordA_aut_uelt, hA, hlam]
    rfl
  · rw [coordB_aut_uelt, hB, hmu]
    rfl
  · rw [aut_uelt_center, hσ c, e11]
    rfl

theorem autA_mul_graphAut (α : MulAut (unipAll F)) (a b : F) :
    autA (α * graphAut) a b = autA α b a := by
  show coordA (α (graphAut (uelt a b 0))) = _
  rw [graphAut_uelt, coordA_aut_uelt]

theorem autB_mul_graphAut (α : MulAut (unipAll F)) (a b : F) :
    autB (α * graphAut) a b = autB α b a := by
  show coordB (α (graphAut (uelt a b 0))) = _
  rw [graphAut_uelt, coordB_aut_uelt]

theorem aut_data (α : MulAut (unipAll F)) :
    ∃ (σ : F ≃+* F) (l m : Fˣ) (sw : Bool), AutData α σ l m sw := by
  rcases aut_gens_dichotomy α with h | h
  · obtain ⟨σ, l, m, hc, hz⟩ := aut_core_noswap α (aut_noswap_of_gens α h)
    refine ⟨σ, l, m, false, fun a b c => ?_, hz⟩
    simp only [Bool.false_eq_true, ite_false]
    exact Prod.ext (hc a b c).1 (hc a b c).2
  · have h' : autB (α * graphAut) 1 0 = 0 ∧ autA (α * graphAut) 0 1 = 0 := by
      rw [autB_mul_graphAut, autA_mul_graphAut]
      exact ⟨h.2, h.1⟩
    obtain ⟨σ, l', m', hc, hz⟩ :=
      aut_core_noswap (α * graphAut) (aut_noswap_of_gens (α * graphAut) h')
    have hα : ∀ x : unipAll F,
        α x = (α * graphAut : MulAut (unipAll F)) (graphAut x) := fun x => by
      show α x = α (graphAut (graphAut x))
      rw [graphAut_graphAut]
    refine ⟨σ, m', l', true, fun a b c => ?_, fun c => ?_⟩
    · simp only [ite_true]
      rw [hα, graphAut_uelt]
      exact Prod.ext (hc b a _).1 (hc b a _).2
    · rw [hα, graphAut_uelt, hz]
      simp only [mul_zero, add_zero]
      congr 2
      ring

end AutClassify

section AutRealize

variable {F : Type} [Field F] [CharP F 2]

noncomputable def autField (α : MulAut (unipAll F)) : RingAut F := (aut_data α).choose

theorem autField_spec (α : MulAut (unipAll F)) :
    ∃ (l m : Fˣ) (sw : Bool), AutData α (autField α) l m sw :=
  (aut_data α).choose_spec

theorem autField_eq {α : MulAut (unipAll F)} {σ : F ≃+* F} {l m : Fˣ} {sw : Bool}
    (h : AutData α σ l m sw) : autField α = σ := by
  obtain ⟨l₀, m₀, sw₀, h₀⟩ := autField_spec α
  exact (h₀.unique h).1

theorem autField_eq_of_center {α : MulAut (unipAll F)} {σ : F ≃+* F} {k : F} (hk : k ≠ 0)
    (h : ∀ c, α (uelt 0 0 c) = uelt 0 0 (k * σ c)) : autField α = σ := by
  obtain ⟨l, m, sw, hd⟩ := autField_spec α
  have e1 := (hd.2 1).symm.trans (h 1)
  rw [uelt_inj] at e1
  simp only [map_one, mul_one] at e1
  refine RingEquiv.ext fun c => ?_
  have e2 := (hd.2 c).symm.trans (h c)
  rw [uelt_inj] at e2
  have := e2.2.2
  rw [e1.2.2] at this
  exact mul_left_cancel₀ hk this

theorem autSwap_mul (α β : MulAut (unipAll F)) :
    autSwap (α * β) = xor (autSwap α) (autSwap β) := by
  obtain ⟨σ₁, l₁, m₁, sw₁, h₁⟩ := aut_data α
  obtain ⟨σ₂, l₂, m₂, sw₂, h₂⟩ := aut_data β
  rw [autSwap_eq h₁, autSwap_eq h₂]
  have hA := h₁.coordA_eq (β (uelt 1 0 0))
  have hB := h₂.coordB_eq (uelt 1 0 0)
  have hA2 := h₂.coordA_eq (uelt 1 0 0)
  simp only [coordA_uelt, coordB_uelt, map_zero, mul_zero, map_one, mul_one] at hB hA2
  rw [Bool.eq_iff_iff, autSwap_eq_true_iff]
  show coordA (α (β (uelt 1 0 0))) = 0 ↔ _
  rw [hA]
  cases sw₁ <;> cases sw₂ <;> simp_all

noncomputable def autFieldHom : MulAut (unipAll F) →* RingAut F where
  toFun := autField
  map_one' := autField_eq autData_one
  map_mul' α β := by
    obtain ⟨σ₁, l₁, m₁, sw₁, h₁⟩ := aut_data α
    obtain ⟨σ₂, l₂, m₂, sw₂, h₂⟩ := aut_data β
    rw [autField_eq h₁, autField_eq h₂]
    refine autField_eq_of_center (σ := σ₁ * σ₂) (k := (l₁ * m₁ : F) * σ₁ (l₂ * m₂ : F))
      (mul_ne_zero (mul_ne_zero l₁.ne_zero m₁.ne_zero)
        ((map_ne_zero σ₁).2 (mul_ne_zero l₂.ne_zero m₂.ne_zero))) fun c => ?_
    show α (β (uelt 0 0 c)) = _
    rw [h₂.2 c, h₁.2]
    congr 1
    simp only [RingAut.mul_apply, map_mul]
    ring

theorem autField_mul (α β : MulAut (unipAll F)) :
    autField (α * β) = autField α * autField β := autFieldHom.map_mul α β

theorem autField_conj (h : unipAll F) : autField (MulAut.conj h) = 1 :=
  autField_eq (autData_conj h)

theorem map_radOne_aut (α : MulAut (unipAll F)) :
    (radOne F).map α.toMonoidHom = if autSwap α then radTwo F else radOne F := by
  obtain ⟨σ, l, m, sw, h⟩ := aut_data α
  rw [autSwap_eq h]
  exact h.map_radOne

theorem map_radTwo_aut (α : MulAut (unipAll F)) :
    (radTwo F).map α.toMonoidHom = if autSwap α then radOne F else radTwo F := by
  obtain ⟨σ, l, m, sw, h⟩ := aut_data α
  rw [autSwap_eq h]
  exact h.map_radTwo

theorem autSwap_eq_true_iff_map (α : MulAut (unipAll F)) :
    autSwap α = true ↔ (radOne F).map α.toMonoidHom = radTwo F := by
  rw [map_radOne_aut]
  cases autSwap α
  · simp only [Bool.false_eq_true, ite_false, false_iff]
    exact radOne_ne_radTwo
  · simp

end AutRealize

section Normal

variable {F : Type} [Field F] [CharP F 2]

theorem exists_central_conj_of_data_one (ρ : MulAut (unipAll F)) (σ : F ≃+* F)
    (hσ : ∀ x, σ (σ x) = x) (h : AutData ρ σ 1 1 true) (hρ : ∀ g, ρ (ρ g) = g) :
    ∃ φ : MulAut (unipAll F), ∀ g, φ (ρ g) = graphFieldAut σ (φ g) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  set γ : F → F → F := fun a b => coordC (ρ (uelt a b 0)) with hγ
  have hρ0 : ∀ a b, ρ (uelt a b 0) = uelt (σ b) (σ a) (γ a b) := by
    intro a b
    have h1 := h.1 a b 0
    simp only [ite_true, Units.val_one, one_mul, Prod.mk.injEq] at h1
    calc ρ (uelt a b 0) = uelt (coordA (ρ (uelt a b 0))) (coordB (ρ (uelt a b 0)))
          (coordC (ρ (uelt a b 0))) := (uelt_coords _).symm
      _ = uelt (σ b) (σ a) (γ a b) := by rw [h1.1, h1.2]
  have hρc : ∀ a b c, ρ (uelt a b c) = uelt (σ b) (σ a) (γ a b + σ c) := by
    intro a b c
    rw [uelt_eq_mul a b c, map_mul, hρ0 a b, h.2 c, uelt_mul, uelt_inj]
    simp
  have hadd : ∀ a b a' b', γ (a + a') (b + b') = γ a b + γ a' b' + σ b * σ a' + σ a * σ b' := by
    intro a b a' b'
    have h1 : ρ (uelt a b 0 * uelt a' b' 0) = ρ (uelt a b 0) * ρ (uelt a' b' 0) := map_mul ρ _ _
    rw [uelt_mul, hρc (a + a') (b + b') (0 + 0 + a * b'), hρ0 a b, hρ0 a' b', uelt_mul,
      uelt_inj] at h1
    have h3 := h1.2.2
    simp only [map_mul, add_zero, zero_add] at h3
    linear_combination h3 - (σ a * σ b') * h2
  have hinv : ∀ a b, γ (σ b) (σ a) + σ (γ a b) = 0 := by
    intro a b
    have h1 := hρ (uelt a b 0)
    rw [hρ0 a b, hρc (σ b) (σ a) (γ a b), uelt_inj] at h1
    exact h1.2.2
  have hγ0 : γ 0 0 = 0 := by
    have := hadd 0 0 0 0
    simp only [add_zero, map_zero, mul_zero] at this
    linear_combination -this
  let e₂ : F →+ F :=
    { toFun := fun b => γ (σ b) 0
      map_zero' := by simp [hγ0]
      map_add' := fun b b' => by
        have := hadd (σ b) 0 (σ b') 0
        simp only [add_zero, map_add, map_zero, mul_zero, zero_mul] at this ⊢
        exact this }
  refine ⟨centralAut 0 e₂, fun g => ?_⟩
  obtain ⟨a, b, c, rfl⟩ := exists_uelt g
  rw [hρc, centralAut_uelt, centralAut_uelt, graphFieldAut_uelt, uelt_inj]
  refine ⟨rfl, rfl, ?_⟩
  have hE1 := hadd a 0 0 b
  have hE2 := hinv (σ b) 0
  simp only [add_zero, zero_add, map_zero, mul_zero, hσ] at hE1 hE2
  simp only [AddMonoidHom.zero_apply, add_zero, e₂, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hσ,
    map_add]
  linear_combination hE1 + hE2 + (γ a 0 - σ (γ (σ b) 0)) * h2

theorem exists_conj_graphField_of_swap (ρ : MulAut (unipAll F)) (hρ : ∀ g, ρ (ρ g) = g)
    (hsw : autSwap ρ = true) :
    (∀ x, autField ρ (autField ρ x) = x) ∧
      ∃ β : MulAut (unipAll F), ∀ g, β (ρ g) = graphFieldAut (autField ρ) (β g) := by
  obtain ⟨σ, l, m, sw, h⟩ := aut_data ρ
  have hs : sw = true := (autSwap_eq h).symm.trans hsw
  subst hs
  rw [autField_eq h]
  have hml : (m : F) * σ l = 1 := by
    have e := h.coordA_eq (ρ (uelt 1 0 0))
    have e2 := h.coordB_eq (uelt 1 0 0)
    simp only [ite_true] at e e2
    rw [hρ, e2] at e
    simpa using e.symm
  have hσσ : ∀ a, σ (σ a) = a := by
    intro a
    have e := h.coordA_eq (ρ (uelt a 0 0))
    have e2 := h.coordB_eq (uelt a 0 0)
    simp only [ite_true] at e e2
    rw [hρ, e2] at e
    simp only [coordA_uelt, map_mul] at e
    linear_combination (-(σ (σ a))) * hml - e
  refine ⟨hσσ, ?_⟩
  let D : MulAut (unipAll F) := diagAut (RingEquiv.refl F) 1 l⁻¹
  have hD : ∀ a b c, D (uelt a b c) = uelt a ((l : F)⁻¹ * b) ((l : F)⁻¹ * c) := by
    intro a b c
    simp [D, diagAut_uelt]
  have hDi : ∀ a b c, D.symm (uelt a b c) = uelt a ((l : F) * b) ((l : F) * c) := by
    intro a b c
    rw [MulEquiv.symm_apply_eq, hD]
    simp [l.ne_zero]
  let ρ' : MulAut (unipAll F) := D * ρ * D⁻¹
  have hρ'c : ∀ x, ρ' x = D (ρ (D.symm x)) := fun x => rfl
  have hdata : AutData ρ' σ 1 1 true := by
    refine ⟨fun a b c => ?_, fun c => ?_⟩
    · obtain ⟨y, hy⟩ : ∃ y, y = ρ (uelt a ((l : F) * b) ((l : F) * c)) := ⟨_, rfl⟩
      have e := h.1 a ((l : F) * b) ((l : F) * c)
      rw [← hy] at e
      simp only [ite_true, Prod.mk.injEq] at e
      rw [hρ'c, hDi, ← hy]
      obtain ⟨y1, y2, y3, rfl⟩ := exists_uelt y
      simp only [coordA_uelt, coordB_uelt] at e
      rw [hD]
      simp only [coordA_uelt, coordB_uelt, ite_true, Units.val_one, one_mul, Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · rw [e.1, map_mul]
        linear_combination (σ b) * hml
      · rw [e.2]
        field_simp [l.ne_zero]
    · rw [hρ'c, hDi]
      simp only [mul_zero]
      rw [h.2 ((l : F) * c), hD]
      simp only [mul_zero, Units.val_one, one_mul, uelt_inj, map_mul]
      refine ⟨trivial, trivial, ?_⟩
      field_simp [l.ne_zero]
      linear_combination (σ c) * hml
  have hρ'inv : ∀ g, ρ' (ρ' g) = g := by
    intro g
    rw [hρ'c, hρ'c, D.symm_apply_apply, hρ, D.apply_symm_apply]
  obtain ⟨φ, hφ⟩ := exists_central_conj_of_data_one ρ' σ hσσ hdata hρ'inv
  refine ⟨φ * D, fun g => ?_⟩
  have := hφ (D g)
  rw [hρ'c, D.symm_apply_apply] at this
  exact this

end Normal

section Twisted

variable {F : Type} [Field F] [CharP F 2] [Finite F]

theorem exists_add_twisted_eq (σ : F ≃+* F) (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x)
    (k : F) (hk : k * σ k = 1) (a : F) (ha : k * σ a = a) : ∃ x, a = x + k * σ x := by
  have hk0 : k ≠ 0 := left_ne_zero_of_mul_eq_one hk
  obtain ⟨y, hy0, hy⟩ : ∃ y : F, y ≠ 0 ∧ σ y = k * y := by
    by_cases h1 : k = 1
    · exact ⟨1, one_ne_zero, by simp [h1]⟩
    · refine ⟨1 + σ k, fun h0 => h1 ?_, ?_⟩
      · have h2 : σ k = 1 := by
          linear_combination h0 - (CharTwo.two_eq_zero : (2 : F) = 0)
        have := congrArg σ h2
        rwa [hσ, map_one] at this
      · rw [map_add, map_one, hσ]
        linear_combination (-1 : F) * hk
  have hfix : σ (y * a) = y * a := by
    rw [map_mul, hy]
    linear_combination y * ha
  obtain ⟨d, hd⟩ := exists_add_map_eq σ hσ hne (y * a) hfix
  have hσy : σ y ≠ 0 := fun h => hy0 ((map_eq_zero σ).1 h)
  refine ⟨d / y, ?_⟩
  rw [map_div₀, hy]
  field_simp
  linear_combination hd

end Twisted

section GaloisComm

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem ringAut_mul_comm (σ τ : RingAut F) : σ * τ = τ * σ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let toGal : RingAut F → (F ≃ₐ[ZMod 2] F) := fun f =>
    AlgEquiv.ofRingEquiv (f := f) fun r =>
      RingHom.congr_fun (RingHom.ext_zmod ((f : F →+* F).comp (algebraMap (ZMod 2) F))
        (algebraMap (ZMod 2) F)) r
  have hcomm : toGal σ * toGal τ = toGal τ * toGal σ :=
    (IsCyclic.isMulCommutative (α := F ≃ₐ[ZMod 2] F)).is_comm.comm _ _
  ext x
  exact AlgEquiv.congr_fun hcomm x

end GaloisComm

end CFSG.OddStandard.Seitz77
